// BMS → additive patterns of resemblance（加算ありの類似パターン）への翻訳。
// ブラウザ（globalThis.Bms2apor）と node（module.exports）の両方で使う。
//
// 流れ: 行列 → Buchholz の項（2 行以下）→ 可算な項の有限集合（パターンのノード）
//       → 大小・和・≤₁ を読んでパターンを書く。
(function (root) {
'use strict';

// ---------------------------------------------------------------- BMS
// 文字列 → 列のリスト。無効文字は捨て、列の高さは最大の列に合わせて 0 を詰める。
function parseBms(s) {
  const clean = s.replace(/[^(),0-9]/g, '');
  const cols = [];
  const re = /\(([^()]*)\)/g;
  let m;
  while ((m = re.exec(clean)) !== null) cols.push(m[1].split(',').map(x => x === '' ? 0 : parseInt(x, 10)));
  const h = cols.reduce((acc, c) => Math.max(acc, c.length), 0);
  return cols.map(c => c.concat(new Array(h - c.length).fill(0)));
}

// 末尾の全零行を落とす（全部 0 なら 1 行にする）
function strip(M) {
  if (!M.length) return M;
  let h = M[0].length;
  while (h > 1 && M.every(c => c[h - 1] === 0)) h--;
  return M.map(c => c.slice(0, h));
}

const bmsToString = M => M.map(c => '(' + c.join(',') + ')').join('');

// ---------------------------------------------------------------- Buchholz の項
// 0 | { nu, a }（D_nu a）| 主項の配列（和、大きい順）
const D = (nu, a) => ({ nu, a });
const isArr = t => Array.isArray(t);
const isObj = t => t !== 0 && !Array.isArray(t);
const comps = t => t === 0 ? [] : (isArr(t) ? t : [t]);
const mkSum = cs => cs.length === 0 ? 0 : (cs.length === 1 ? cs[0] : cs);
const ONE = D(0, 0);

function cmp(s, t) {
  const a = comps(s), b = comps(t);
  for (let i = 0; i < Math.min(a.length, b.length); i++) {
    const c = cmpP(a[i], b[i]);
    if (c) return c;
  }
  return Math.sign(a.length - b.length);
}
function cmpP(p, q) { return p.nu !== q.nu ? Math.sign(p.nu - q.nu) : cmp(p.a, q.a); }
const beq = (s, t) => cmp(s, t) === 0;

// 順序数の和（後ろの項より小さい末尾は消える）
function add(s, t) {
  const a = comps(s).slice(), b = comps(t);
  if (!b.length) return mkSum(a);
  while (a.length && cmpP(a[a.length - 1], b[0]) < 0) a.pop();
  return mkSum(a.concat(b));
}
const sumAll = ts => ts.reduce((acc, t) => add(acc, t), 0);
const keyOf = t => JSON.stringify(t);
const norm = t => sumAll(comps(t).map(p => D(p.nu, norm(p.a))));

// 段が mu より高い先頭の成分と、それ以外の末尾の成分に分ける
function split(t, mu) {
  const cs = comps(t);
  let i = 0;
  while (i < cs.length && cs[i].nu > mu) i++;
  return [cs.slice(0, i), cs.slice(i)];
}

// ---------------------------------------------------------------- ペア数列 → Buchholz の項
// p進大好きbot の対応（naruyoko の Trans）。koteitan/bms-vs-taranovskys-c の bms2tc.js から移した。
function pget(M, i, j) { return (j < 0 || j >= M.length) ? 0 : M[j][i]; }

function findParent(M, i, j, k) {
  if (k === undefined) k = 0;
  if (j < 0 || j >= M.length) return -1;
  if (i === 0) {
    for (let j0 = j - 1; j0 >= k; j0--) if (pget(M, 0, j0) < pget(M, 0, j)) return j0;
    return -1;
  }
  let j0 = findParent(M, 0, j, k);
  while (j0 >= k) {
    if (pget(M, 1, j0) < pget(M, 1, j)) return j0;
    j0 = findParent(M, 0, j0, k);
  }
  return -1;
}
const isParent = (M, i, j, k) => k >= 0 && k < M.length && k === findParent(M, i, j, k);
function findAncestors(M, i, j) {
  if (j < 0 || j >= M.length) return [];
  const acc = [j];
  for (let j0 = j; ;) {
    const j1 = findParent(M, i, j0);
    if (j1 < 0) return acc;
    acc.push(j1);
    j0 = j1;
  }
}
function isAncestor(M, i, j, k) {
  if (k < 0 || k >= M.length) return false;
  for (let j0 = j; ;) {
    if (k === j0) return true;
    const j1 = findParent(M, i, j0, k);
    if (j1 === -1) return false;
    j0 = j1;
  }
}
const pred = M => M.length === 1 ? M : M.slice(0, -1);
const derp = M => M.slice(1);
const incrFirst = (M, i) => M.map(c => [c[0] + i, c[1]]);
const isZeroPair = M => M.length === 1 && pget(M, 1, 0) === 0;
const isPrincipalPair = M => !isZeroPair(M) && isAncestor(M, 0, M.length - 1, 0);
const slice = (M, j0, j1) => M.slice(Math.max(j0, 0), Math.max(j1, 0));
function ppair(M) {
  const r = [];
  for (let j1 = M.length - 1; j1 >= 0;) {
    const ans = findAncestors(M, 0, j1);
    const j0 = ans[ans.length - 1];
    r.unshift(slice(M, j0, j1 + 1));
    j1 = j0 - 1;
  }
  return r;
}
const isAdmitted = (M, j) => !(j > M.length || (isParent(M, 1, j, j - 1) && isParent(M, 1, j + 1, j)));
function adm(M, j) {
  for (; j >= 0; j--) if (isAdmitted(M, j)) return j;
  return -1;
}
function idxSum(Q) {
  const r = [0];
  let j = 0;
  for (const q of Q) { j += q.length; r.push(j); }
  return r;
}
function trMax(M) {
  for (let j = 0; j < M.length; j++) if (!isParent(M, 1, j + 1, j)) return j;
  return M.length - 1;
}
const br = M => ppair(slice(M, trMax(M) + 1, M.length));
const firstNodes = M => idxSum(br(M)).map(x => x + trMax(M) + 1);
const joints = M => firstNodes(M).slice(0, -1).map(e => findParent(M, 0, e));
function jjSeq(j0, j1) {
  const r = [];
  for (let t = j0; t <= j1; t++) r.push([t, t]);
  return r;
}
const equalPair = (M, N) => M.length === N.length && M.every((c, i) => c[0] === N[i][0] && c[1] === N[i][1]);

function red(M) {
  if (isZeroPair(M)) return [[0, 0]];
  if (isPrincipalPair(M)) {
    const j1 = M.length - 1;
    if (pget(M, 0, 0) === 0 && pget(M, 1, 0) === 0) {
      const j1p = trMax(M);
      if (j1p === j1) return jjSeq(0, j1);
      const brs = br(M), fn = firstNodes(M), jn = joints(M);
      let r = jjSeq(0, j1p);
      for (let J = 0; J < brs.length; J++) {
        const bJ = brs[J];
        const nJ = pget(bJ, 1, 0) === 0 ? -1 : findParent(M, 1, fn[J]);
        const NJ = [[jn[J] + 1, nJ + 1]].concat(derp(bJ));
        r = r.concat(incrFirst(red(NJ), jn[J] - nJ));
      }
      return r;
    }
    const M10 = pget(M, 1, 0);
    if (M10 === 0) return red(incrFirst(M, -pget(M, 0, 0)));
    const N = red(jjSeq(0, M10 - 1).concat(incrFirst(M, M10)));
    if (M10 <= N.length - 1 && isPrincipalPair(slice(N, M10, N.length)))
      return incrFirst(slice(N, M10, N.length), -pget(N, 0, M10) + pget(N, 1, M10));
    return M;
  }
  let acc = [];
  for (const e of ppair(M)) acc = acc.concat(red(e));
  return acc;
}
const isReduced = M => equalPair(red(M), M);

const plusRaw = (a, b) => mkSum(comps(a).concat(comps(b)));
function replaceMark(t, c, cc) {
  if (isArr(t)) {
    if (t.length === 0) return null;
    const tt = replaceMark(t[t.length - 1], c, cc);
    return tt === null ? null : t.slice(0, -1).concat([tt]);
  }
  if (isObj(t)) {
    if (beq(t, c)) return cc;
    const tt = replaceMark(t.a, c, cc);
    return tt === null ? null : D(t.nu, tt);
  }
  return null;
}
const nextMarked = t => isArr(t) ? (t.length ? t[t.length - 1] : null) : (isObj(t) ? t.a : null);
function isMarked(t, c) {
  for (; t !== null; t = nextMarked(t)) if (beq(t, c)) return true;
  return false;
}

function makeTrans() {
  const tyM = new Map(), trM = new Map(), mkM = new Map();
  let calls = 0;
  const key = M => M.map(c => c[0] + ',' + c[1]).join(';');
  const dOf = (M, j) => D(pget(M, 1, j), 0);
  const tick = () => { if (++calls > 2000000) throw new Error('too many steps'); };

  function transType(M) {
    const k = key(M);
    if (tyM.has(k)) return tyM.get(k);
    tick();
    const j1 = M.length - 1;
    let r;
    if (isReduced(M)) {
      if (j1 === 0) r = -1;
      else if (isPrincipalPair(M)) {
        if (trans(pred(M)) === 0) r = 0;
        else {
          const j0 = findParent(M, 0, j1);
          if (pget(M, 1, j1) === 0) r = isAdmitted(M, j0) ? 1 : 2;
          else if (pget(M, 1, j0) >= pget(M, 1, j1)) r = isAdmitted(M, j0) ? 3 : 4;
          else r = j0 + 1 < j1 ? 5 : 6;
        }
      } else r = -2;
    } else r = -3;
    tyM.set(k, r);
    return r;
  }

  function c1c2(M, ty) {
    const j1 = M.length - 1;
    const j0 = findParent(M, 0, j1);
    const c1 = mark(pred(M), adm(M, j0));
    const v = isObj(c1) ? c1.nu : 0;
    const t2 = isObj(c1) ? c1.a : 0;
    const Pt2 = comps(t2);
    let c2;
    if (ty === 1 || ty === 3 || ty === 5) c2 = D(v, plusRaw(t2, dOf(M, j1)));
    else if (ty === 2 || ty === 4) {
      if (t2 === 0) c2 = D(v, D(pget(M, 1, j0), dOf(M, j1)));
      else {
        const last = Pt2[Pt2.length - 1];
        let t3, t4;
        if (isObj(last) && last.nu === pget(M, 1, j0)) {
          t3 = mkSum(Pt2.slice(0, -1));
          t4 = last.a;
        } else { t3 = t2; t4 = t2; }
        c2 = D(v, plusRaw(t3, D(pget(M, 1, j0), plusRaw(t4, dOf(M, j1)))));
      }
    } else c2 = D(v, dOf(M, j1));
    return [c1, c2];
  }

  function trans(M) {
    const k = key(M);
    if (trM.has(k)) return trM.get(k);
    tick();
    const ty = transType(M);
    let r;
    if (ty === -3) r = trans(red(M));
    else if (ty === -2) {
      r = 0;
      ppair(M).forEach((e, i) => { r = i === 0 ? trans(e) : plusRaw(r, equalPair(e, [[0, 0]]) ? ONE : trans(e)); });
    } else if (ty === -1) r = (pget(M, 0, 0) === 0 && pget(M, 1, 0) === 0) ? 0 : D(pget(M, 1, 0), 0);
    else if (ty === 0) r = D(0, dOf(M, M.length - 1));
    else {
      const [c1, c2] = c1c2(M, ty);
      const rr = replaceMark(trans(pred(M)), c1, c2);
      r = rr === null ? 0 : rr;
    }
    trM.set(k, r);
    return r;
  }

  function mark(M, m) {
    const k = key(M) + '#' + m;
    if (mkM.has(k)) return mkM.get(k);
    tick();
    const j1 = M.length - 1;
    const ty = transType(M);
    let r;
    if (ty === -3) r = mark(red(M), m);
    else if (ty === -2) {
      const PM = ppair(M);
      const last = PM[PM.length - 1];
      r = equalPair(last, [[0, 0]]) ? ONE : mark(last, m - (j1 - last.length + 1));
    } else if (ty === -1) r = (pget(M, 0, 0) === 0 && pget(M, 1, 0) === 0) ? 0 : D(pget(M, 1, 0), 0);
    else if (ty === 0) r = m === 0 ? D(0, dOf(M, j1)) : dOf(M, j1);
    else {
      const [c1, c2] = c1c2(M, ty);
      if (m < j1) {
        const c0 = mark(pred(M), m);
        if (isMarked(c0, c1)) { const rr = replaceMark(c0, c1, c2); r = rr === null ? 0 : rr; }
        else r = dOf(M, j1);
      } else r = dOf(M, j1);
    }
    mkM.set(k, r);
    return r;
  }
  return trans;
}

// 行列（2 行以下、1 行なら 2 行目を 0 とみなす）→ 項。Trans は列の和 (0,0)(0,0) の値を
// 1 + 1 と読むので、根の個数だけの 1 を足した形になる。
function bmsToTerm(M) {
  const P = M.map(c => [c[0], c.length > 1 ? c[1] : 0]);
  return norm(makeTrans()(P));
}

// ---------------------------------------------------------------- パターンのノード
// 段 0 の主項 D_0(b) の log（b の末尾に段 0 の成分があるとき）
function log0(p) {
  const [big, small] = split(p.a, 0);
  if (!big.length) return mkSum(small);
  if (!small.length) return p;
  return add(D(0, mkSum(big)), mkSum(small));
}

// 可算な主項 p は p.a = base + own と分けて持つ。行列から直接得た項は base = 0, own = p.a。
// 点の円の中に作る点は、作った場所で base と own を記録し、中身は own だけから計算する。
function makeCtx() {
  const info = new Map();      // key → { base, own }
  const memo = new Map();      // key → { J, prefix, inner }
  const conflicts = [];
  function record(p, base, own) {
    const k = keyOf(p);
    const old = info.get(k);
    if (!old) info.set(k, { base, own });
    else if (cmp(old.own, own) !== 0) conflicts.push(k);
    return p;
  }
  const baseOwn = p => info.get(keyOf(p)) || { base: 0, own: p.a };

  // 点 p = D_0(a) の中で段を 1 つ下げる。
  //   段 1 の主項 D_1(β): β の末尾が段 2 以上なら、β の中身の最後の点。そうでなければ可算な点 D_0(a + L(β))。
  //   段 k ≥ 2 の主項 D_k(β): D_{k-1}(L(β))。
  function lowerIn(p) {
    const a = p.a;
    const L = t => sumAll(comps(t).map(Lp));
    function Lp(q) {
      if (q.nu === 0) return q;
      if (q.nu === 1) {
        const [qbig, qsmall] = split(q.a, 1);
        if (!qbig.length) { const own = L(q.a); return record(D(0, add(a, own)), a, own); }
        const c = content(p, mkSum(qbig)).last;
        if (!qsmall.length) return c;
        // D_1(B + η) = D_1(B)·ω^η なので、B の中身の点 c から ω^{c + L(η)}
        const own = L(mkSum(qsmall));
        return record(D(0, add(c.a, own)), c.a, own);
      }
      return D(q.nu - 1, L(q.a));
    }
    return { L, Lp };
  }

  // 点 p の円の中に、段 2 以上の成分の和 B に対応する兄弟の点を並べる。
  // 段 2 の成分 q は 1 つずつ（own = L(q)）、続く段 3 以上の成分 G はまとめて（own = D_1(L(G))）。
  // 次の兄弟は、前の兄弟とその中で最後に作った点の位置の後ろに置く。
  function content(p, B) {
    const { L } = lowerIn(p);
    const groups = [];
    let open = false;
    for (const c of comps(B)) {
      if (c.nu === 2) { groups.push([c]); open = false; }
      else if (open) groups[groups.length - 1].push(c);
      else { groups.push([c]); open = true; }
    }
    let X = 0, last = null;
    for (const G of groups) {
      const lg = L(sumAll(G));
      const zo = G.length === 1 && G[0].nu === 2 ? lg : D(1, lg);
      const zb = add(p.a, X);
      const z = record(D(0, add(zb, zo)), zb, zo);
      X = add(add(X, zo), reach(z).inner);
      last = z;
    }
    return { last, X };
  }

  // 可算な主項 p について
  //   J: p から ≤₁ で届く上限を p + J と書いたときの J
  //   prefix: p の前に置く点（バー演算に当たる。無ければ null）
  //   inner: p の円の中で最後に作った点の、p.a から見た位置
  //   R: p から ≤₁ で直接届く上限（届かなければ p）
  function reach(p) {
    const k = keyOf(p);
    if (memo.has(k)) return memo.get(k);
    let r = { R: p, prefix: null, inner: 0 };
    memo.set(k, r);
    if (p.a !== 0) {
      const { base, own } = baseOwn(p);
      const oc = comps(own);
      const prefix = () => { const o = mkSum(oc.slice(0, -1)); return record(D(0, add(base, o)), base, o); };
      const [, small] = split(p.a, 0);
      if (small.length) {
        // p = ω^γ（ε でない）: γ の最後の項の指数まで
        r = { R: add(p, log0(small[small.length - 1])), prefix: prefix(), inner: 0 };
      } else {
        const [, o1] = split(own, 1);
        const { L } = lowerIn(p);
        if (o1.length) {
          const q = o1[o1.length - 1];
          const [qbig, qsmall] = split(q.a, 1);
          if (!qsmall.length && qbig.length) {
            // 最後の成分が段 1 で潰れている D_1(B): B の中身を円の中に並べる
            const c = content(p, mkSum(qbig));
            r = { R: c.last, prefix: prefix(), inner: c.X };
          } else {
            // 最後の成分が段 1 で潰れていない: log の像を p に足していく。
            // 途中の和が p より大きい主項になったら、その点から届く上限まで飛ぶ（≤₁ で極小な点の数え上げ）。
            let ics, inner = 0;
            if (qbig.length) {
              const c = content(p, mkSum(qbig));
              ics = [c.last].concat(comps(L(mkSum(qsmall))));
              inner = c.X;
            } else {
              ics = [p].concat(comps(L(q.a)));
            }
            let R = p;
            for (const c of ics) {
              const Rn = add(R, c);
              R = (cmpP(c, p) > 0 && comps(Rn).length === 1) ? lhFull(c) : Rn;
            }
            r = { R, prefix: prefix(), inner };
          }
        } else {
          const c = content(p, own);
          r = { R: c.last, prefix: null, inner: c.X };
        }
      }
    }
    memo.set(k, r);
    return r;
  }

  // p から ≤₁ で推移的に届く最大の上限
  const fullMemo = new Map();
  function lhFull(p) {
    const k = keyOf(p);
    if (fullMemo.has(k)) return fullMemo.get(k);
    fullMemo.set(k, p);
    let e = reach(p).R;
    for (const c of comps(e)) {
      if (cmpP(c, p) > 0) {
        const f = lhFull(c);
        if (cmp(f, e) > 0) e = f;
      }
    }
    fullMemo.set(k, e);
    return e;
  }
  return { reach, lhFull, conflicts };
}

// 項 t を含み、パターンとして必要なノードの集合を作る
function closure(t) {
  const ctx = makeCtx();
  const nodes = new Map();
  const reachOf = new Map();
  const queue = [];
  const put = x => { const k = keyOf(x); if (!nodes.has(k)) { nodes.set(k, x); queue.push(x); } };
  put(0);
  if (t !== 0) put(ONE);
  put(t);
  while (queue.length) {
    const x = queue.shift();
    const cs = comps(x);
    if (cs.length >= 2) {
      for (let i = 1; i <= cs.length; i++) put(mkSum(cs.slice(0, i)));
      cs.forEach(put);
      continue;
    }
    if (cs.length === 0) continue;
    const p = cs[0];
    if (p.nu !== 0) throw new Error('uncountable node');
    const r = ctx.reach(p);
    if (r.prefix !== null) put(r.prefix);
    if (cmp(r.R, p) > 0) { reachOf.set(keyOf(p), r.R); put(r.R); }
  }
  const list = [...nodes.values()].sort(cmp);
  const index = new Map(list.map((x, i) => [keyOf(x), i]));
  const less1 = list.map((x, i) => {
    const r = reachOf.get(keyOf(x));
    return r === undefined ? i : index.get(keyOf(r));
  });
  for (let changed = true; changed;) {
    changed = false;
    for (let i = 0; i < list.length; i++) {
      for (let j = i + 1; j <= less1[i]; j++) {
        if (less1[j] > less1[i]) { less1[i] = less1[j]; changed = true; }
      }
    }
  }
  return { list, index, less1, point: index.get(keyOf(t)) };
}

// ---------------------------------------------------------------- 表示
// 主ノードに 0, a, b, …（0 以外は小さい順）、和はその名前を + でつなぐ。≤₁ の円は "(左端 … 右端)"。
function patternToString(P) {
  const names = [];
  let next = 0;
  const letter = k => {
    let s = '';
    for (k++; k > 0; k = Math.floor(k / 26)) { k--; s = String.fromCharCode(97 + (k % 26)) + s; }
    return s;
  };
  P.list.forEach((x, i) => {
    const cs = comps(x);
    if (cs.length === 0) names[i] = '0';
    else if (cs.length === 1) names[i] = letter(next++);
    else names[i] = cs.map(c => names[P.index.get(keyOf(c))]).join('+');
  });
  const opens = P.list.map(() => 0), closes = P.list.map(() => 0);
  P.list.forEach((x, i) => { if (P.less1[i] > i) { opens[i]++; closes[P.less1[i]]++; } });
  const toks = P.list.map((x, i) => '('.repeat(opens[i]) + names[i] + ')'.repeat(closes[i]));
  return { text: toks.join(' '), point: names[P.point] };
}

// 数値形式（ローカル検証用）: N P と、各ノードの less1 K 成分…
function patternToNumeric(P) {
  const parts = [P.list.length, P.point];
  P.list.forEach((x, i) => {
    parts.push(P.less1[i]);
    const cs = comps(x);
    const d = cs.length >= 2 ? cs.map(c => P.index.get(keyOf(c))) : [];
    parts.push(d.length, ...d);
  });
  return parts.join(' ');
}

function translate(s) {
  const M = strip(parseBms(s));
  const bms = bmsToString(M);
  if (!M.length) return { pattern: '0', point: '0', rows: 0, bms };
  const rows = M[0].length;
  if (rows > 2) return { pattern: null, rows, bms, error: '3 rows and more: not supported yet' };
  try {
    // Trans は列 (0,0) だけの行列を 0 と読むので、値は 1 + (Trans の値)
    const P = closure(add(ONE, bmsToTerm(M)));
    const out = patternToString(P);
    return { pattern: out.text, point: out.point, rows, bms };
  } catch (e) {
    return { pattern: null, rows, bms, error: 'translation failed (' + e.message + ')' };
  }
}

const api = { parseBms, strip, bmsToString, D, comps, cmp, add, norm, split, bmsToTerm,
  log0, makeCtx, closure, patternToString, patternToNumeric, translate };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.Bms2apor = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
