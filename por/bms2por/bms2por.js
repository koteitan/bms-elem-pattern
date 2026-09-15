// BMS → pure patterns of resemblance（加算なしの類似パターン）への翻訳。
// ブラウザ（globalThis.Bms2por）と node（module.exports）の両方で使う。
//
// 行列の列をそのままパターンのノードにし、k 行目の祖先関係を ≤_{k+1} として読む。
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

// 末尾の全零行を取り除く（全部 0 なら 1 行にする）
function strip(M) {
  if (!M.length) return M;
  let h = M[0].length;
  while (h > 1 && M.every(c => c[h - 1] === 0)) h--;
  return M.map(c => c.slice(0, h));
}

const bmsToString = M => M.map(c => '(' + c.join(',') + ')').join('');

// par[k][i]: 列 i の k 行目の親（無ければ -1）。
// 候補は k = 0 なら左のすべての列、k ≥ 1 なら (k-1) 行目の祖先。k 行目の値が小さい候補のうち最も右のもの（BM4）。
function parents(M) {
  const rows = M.length ? M[0].length : 0;
  const par = [];
  for (let k = 0; k < rows; k++) {
    par.push(M.map((col, i) => {
      if (k === 0) {
        for (let j = i - 1; j >= 0; j--) if (M[j][0] < col[0]) return j;
        return -1;
      }
      for (let j = par[k - 1][i]; j >= 0; j = par[k - 1][j]) if (M[j][k] < col[k]) return j;
      return -1;
    }));
  }
  return par;
}

// ---------------------------------------------------------------- 表示
// ノード名 a, b, …, z, aa, ab, …
function letter(k) {
  let s = '';
  for (k++; k > 0; k = Math.floor(k / 26)) { k--; s = String.fromCharCode(97 + (k % 26)) + s; }
  return s;
}

// 各ノードを「名前(≤_1 での直前の点,≤_2 での直前の点,…)」と書く。直前の点が無い段から先は書かない
// （≤_{k+1} ⊆ ≤_k なので、≤_k で無ければ ≤_{k+1} でも無い）。点は最後のノード。
function translate(s) {
  const M = strip(parseBms(s));
  const bms = bmsToString(M);
  if (!M.length) return { pattern: null, bms, error: 'no columns' };
  const rows = M[0].length;
  if (rows > 3) return { pattern: null, rows, bms, error: '4 rows and more: not supported' };
  const par = parents(M);
  const names = M.map((c, i) => letter(i));
  const toks = M.map((c, i) => {
    const ps = [];
    for (let k = 0; k < rows && par[k][i] >= 0; k++) ps.push(names[par[k][i]]);
    return ps.length ? names[i] + '(' + ps.join(',') + ')' : names[i];
  });
  return { pattern: toks.join(' '), point: names[M.length - 1], rows, bms };
}

const api = { parseBms, strip, bmsToString, parents, letter, translate };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.Bms2por = api;
})(typeof globalThis !== 'undefined' ? globalThis : this);
