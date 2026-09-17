[← Back](README.md) | [English](en/05-arrays-labels.md) | [Japanese](05-arrays-labels.md)

# 配列、展開、安定ラベル

前提: [01 順序数と ω₁](01-ordinals.md)

このノートは BM4 の組合せの部分をまとめる。Lean のコードは [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) からコピーしたもので、証明の細部は同じリポジトリの study ノート（study/07-stable-labels.md）にある。

## 1. 配列

$`r`$ 行、長さ $`\ell`$ の **配列** $`A`$ は、列 $`A_0, \dots, A_{\ell - 1}`$ の並びで、各列は自然数の $`r`$ 組である。列 $`A_i`$ の行 $`k`$ の成分を $`A_i[k]`$ と書く。配列は列を並べて $`(0,0)(1,1)(2,2)`$ のように書く。

## 2. 親と祖先

**定義（$`k`$-親）.** 列 $`i`$ の行 $`k`$ での **候補** を、$`k = 0`$ なら $`j \lt i`$ のすべての列、$`k \ge 1`$ なら列 $`i`$ の $`(k-1)`$-祖先とする。候補 $`j`$ のうち $`A_j[k] \lt A_i[k]`$ となる最大の $`j`$ を、列 $`i`$ の **$`k`$-親** と呼ぶ。

**定義（$`k`$-祖先）.** $`k`$-親を 1 回以上たどって届く列を、列 $`i`$ の **$`k`$-祖先** と呼び、$`j \prec_k i`$ と書く。$`j \preceq_k i`$ は $`j = i`$ または $`j \prec_k i`$ を表す。

**例.** $`(0,0)(1,1)(2,2)`$ では、列 2 の 0-親は列 1（値 $`1 \lt 2`$）、1-親も列 1 である。すべての $`j \lt i`$ について $`j \prec_0 i`$ かつ $`j \prec_1 i`$ である。

## 3. 展開

$`c = \ell - 1`$ を最後の列とする。

**列 $`c`$ がどの行 $`k \lt r`$ にも親を持たないとき.** $`A[N]`$ は $`A`$ から最後の列を取り除いたものである。

**親を持つとき.** 次のように置く。

| 記号 | 意味 |
|---|---|
| $`m_0`$ | 列 $`c`$ が親を持つ最大の行 |
| $`p`$ | 列 $`c`$ の $`m_0`$-親 |
| $`s = c - p`$ | 悪い部分の長さ |
| $`G = A_0 \cdots A_{p-1}`$ | 良い部分 |

$`A[N] = G\, B_0\, B_1 \cdots B_N`$ で、コピー $`B_q`$ の第 $`j`$ 列（$`j \lt s`$）は次のとおりである。

```math
(B_q)_j[k] = \begin{cases} A_{p+j}[k] + q \cdot (A_c[k] - A_p[k]) & k \lt m_0 \text{ かつ } p \preceq_k p + j \text{ のとき} \cr A_{p+j}[k] & \text{それ以外} \end{cases}
```

**例 1.** $`(0,0)(1,1)[N]`$：$`c = 1`$、$`m_0 = 1`$、$`p = 0`$、$`s = 1`$。行 0 に $`q \cdot (1 - 0)`$ を足すので

```math
(0,0)(1,1)[N] = (0,0)(1,0)(2,0) \cdots (N,0)
```

**例 2.** $`(0,0)(1,1)(2,2)[2]`$：$`c = 2`$、$`m_0 = 1`$、$`p = 1`$、$`s = 1`$、$`G = (0,0)`$。$`B_q = (1 + q, 1)`$ なので

```math
(0,0)(1,1)(2,2)[2] = (0,0)(1,1)(2,1)(3,1)
```

## 4. 標準列

**定義.** $`r`$ 行の配列

```math
S^r_n = \underbrace{(0,\dots,0)}_{r}\,\underbrace{(1,\dots,1)}_{r} \cdots \underbrace{(n,\dots,n)}_{r}
```

から展開を有限回して得られる配列を、$`r`$ 行の **標準列** と呼ぶ。$`r = 1`$ が原始数列、$`r = 2`$ がペア数列、$`r = 3`$ がトリオ数列である。BM4 の初期列 $`E_r`$ は $`S^r_1`$ である。

## 5. ラベルの体系

**定義.** 行数 $`r`$ の **ラベルの体系** とは、整列順序 $`(\mathrm{Lab}, \lt)`$ と、$`\mathrm{Lab}`$ 上の関係 $`\lhd_0, \dots, \lhd_{r-1}`$ で、次を満たすものをいう。

1. **狭義.** $`a \lhd_k b \Rightarrow a \lt b`$
2. **推移.** $`a \lhd_k b \wedge b \lhd_k c \Rightarrow a \lhd_k c`$
3. **有限反映.** $`n \lt r`$、$`\alpha \lhd_n \beta`$、$`X \subseteq \alpha`$ は有限、$`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ のとき、$`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ で次の (a)〜(d) を満たすものがある

```math
\max X \lt y'_0 \qquad \text{(a)}
```

```math
\forall x \in X\ \forall i \lt s\ \forall k \lt r\ \bigl(x \lhd_k y_i \Rightarrow x \lhd_k y'_i\bigr) \qquad \text{(b)}
```

```math
\forall i, j \lt s\ \forall k \lt r\ \bigl(y_i \lhd_k y_j \Rightarrow y'_i \lhd_k y'_j\bigr) \qquad \text{(c)}
```

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lhd_m \beta \Rightarrow y'_i \lhd_m \alpha\bigr) \qquad \text{(d)}
```

**読み方.** $`[\alpha, \beta)`$ にある有限個のラベルを、関係を保ったまま $`\alpha`$ の下へ写せる。(d) は、上端 $`\beta`$ との関係を、上端 $`\alpha`$ との関係に写すことを言っている。

## 6. 安定ラベルと高さ

**定義（安定ラベル）.** 長さ $`\ell`$ の配列 $`A`$ の **安定ラベル** とは、写像 $`f : \{0, \dots, \ell - 1\} \to \mathrm{Lab}`$ で次を満たすものである。

1. $`i \lt j \Rightarrow f(i) \lt f(j)`$
2. $`k \lt r`$ で $`j \prec_k i \Rightarrow f(j) \lhd_k f(i)`$

**定義（高さ）.** $`\mathrm{ht}(f) = f(\ell - 1)`$。

## 7. 命題 19.1（高さの下降）

**命題（DH）.** 安定ラベル $`f`$ を持つ空でない配列 $`A`$ と $`N \in \mathbb{N}`$ について、$`A[N]`$ が空でなければ、$`A[N]`$ は安定ラベル $`g`$ で $`\mathrm{ht}(g) \lt \mathrm{ht}(f)`$ となるものを持つ。

**証明の筋.** 親が無いときは $`f`$ を制限すればよい。親があるときは、$`G\, B_0 \cdots B_q`$ のラベルを $`q`$ について順に作る。

1. $`\alpha = f(p)`$、$`\beta = f(c)`$、$`y_i = f(p + i)`$ と置く。$`p \prec_{m_0} c`$ なので $`\alpha \lhd_{m_0} \beta`$
2. $`X`$ を $`B_q`$ より前のラベルの集合として、有限反映を $`n = m_0`$ で使い、$`y'`$ を得る
3. $`B_q`$ のラベルを $`y`$ から $`y'`$ に取り替え、新しい $`B_{q+1}`$ に $`y`$ を貼る

最後のコピー $`B_N`$ のラベルは $`y_0, \dots, y_{s-1}`$ なので、$`\mathrm{ht}(g) = f(c - 1) \lt f(c)`$ である。祖先関係が保たれることの確認には、配列の組合せについてのコピー補題を使う。

有限反映が呼ばれるのは $`n = m_0 \lt r`$ の場合だけである。

## 8. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| 標準列 | [08](08-termination.md) |
| ラベルの体系 | [06](06-finite-reflection.md) で満たすことを示す |
| 命題 19.1 | [08](08-termination.md) |

## 9. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 配列 | `Arr` | [`Bm4/Defs.lean`](../../lean/Bm4/Defs.lean) |
| 候補、親 | `cand`, `parentRel`, `parent` | 同上 |
| 祖先 | `anc`, `ancEq` | 同上 |
| 親の有無、$`m_0`$、$`p`$ | `LastHasParent`, `m₀`, `badRoot` | 同上 |
| 展開、展開列 | `dropLast`, `tildeCol`, `expand`, `seq` | 同上 |
| ラベルの体系 | `LabelSystem` | [`Bm4/Label.lean`](../../lean/Bm4/Label.lean) |
| 安定ラベル、高さ | `Stable`, `ht` | 同上 |
| 命題 19.1 | `descent` | 同上 |
| $`S^r_n`$、標準列 | `stair`, `Std` | [`Pattern/Main.lean`](../../lean/Pattern/Main.lean) |
