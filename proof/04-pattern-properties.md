[← Back](README.md)

# R_N の性質 P1〜P7

前提: [01 順序数と ω₁](01-ordinals.md)、[02 構造と初等部分構造](02-elementary-substructure.md)、[03 R_N](03-patterns.md)

[06 有限反映](06-finite-reflection.md) は、$`\mathcal{R}_N`$ の次の 7 つの性質だけを使う。どれも初等部分構造の定義から出る。P2、P4 の $`j = 2`$ の場合、P6、P7 では $`N \ge 2`$ とする。

| | 性質 |
|---|---|
| P1 | $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ |
| P2 | $`a \le_1 b \le_1 c \wedge a \le_2 c \Rightarrow a \le_2 b`$ |
| P3 | $`y \le \alpha`$、$`\alpha`$ が後続で閉じ、$`\forall v \in [y, \alpha)\ y \le_1 v`$ $`\Rightarrow y \le_1 \alpha`$ |
| P4 | $`y \lt \alpha`$、$`S \subseteq [y, \alpha)`$ が $`\alpha`$ で非有界、$`\forall v \in S\ y \le_j v`$ $`\Rightarrow y \le_j \alpha`$（$`j \le 2`$） |
| P5 | $`\alpha \lt_1 \beta \Rightarrow \alpha`$ は後続で閉じる |
| P6 | $`y \lt_2 \beta \Rightarrow \beta`$ は後続で閉じる |
| P7 | $`\alpha \lt_2 \beta \Rightarrow \forall z \lt \alpha\ \exists u\ (z \lt u \lt \alpha \wedge u \le_1 \alpha)`$ |

$`S`$ が $`\alpha`$ で **非有界** とは、どの $`z \lt \alpha`$ に対しても $`z \lt v`$ となる $`v \in S`$ があることをいう。

## P1：≤₁ は ≤ に沿って閉じる

**命題.** $`a \le b \le c`$ かつ $`a \le_1 c`$ なら、$`a \le_1 b`$ である。

**証明.** $`a`$ 未満のパラメータを持つ $`\Sigma_1`$ 論理式 $`\varphi`$ を取る。

- $`b \models \varphi`$ なら、上へ保存で $`c \models \varphi`$、$`a \le_1 c`$ から $`a \models \varphi`$
- $`a \models \varphi`$ なら、上へ保存で $`b \models \varphi`$

$`\square`$

**意味.** $`\{c : a \le_1 c\}`$ は、$`a`$ から始まる区間である。[03](03-patterns.md) §4 の $`\{\omega, \omega + 1\}`$ がその例である。

## P2：≤₂ は ≤₁ に沿って閉じる

**命題.** $`a \le_1 b`$、$`b \le_1 c`$、$`a \le_2 c`$ なら、$`a \le_2 b`$ である。

**証明.** $`\Sigma_1`$ 論理式の一致は $`a \le_1 b`$ から出る。$`a`$ 未満のパラメータ $`\vec p`$ を持つ $`\Sigma_2`$ 論理式 $`\varphi = \exists \vec x\ \forall \vec z\ \psi`$ を取る。

- $`b \models \varphi`$ とする。証人 $`\vec x \lt b`$ について $`b \models \forall \vec z\ \psi(\vec p, \vec x, \vec z)`$。これは $`b`$ 未満のパラメータを持つ $`\Pi_1`$ 論理式なので、$`b \le_1 c`$ から $`c`$ でも真。よって $`c \models \varphi`$、$`a \le_2 c`$ から $`a \models \varphi`$
- $`a \models \varphi`$ とする。証人 $`\vec x \lt a`$ について $`a \models \forall \vec z\ \psi(\vec p, \vec x, \vec z)`$。$`a \le_1 b`$ から $`b`$ でも真なので、$`b \models \varphi`$

$`\square`$

**注意.** $`\le_2`$ は $`\le`$ に沿っては閉じていない。Wilken によれば $`\upsilon_\omega \lt_2 \upsilon_\omega \cdot 2`$ で、$`\upsilon_\omega`$ の最小の $`\lt_2`$-後者は $`\upsilon_\omega \cdot 2`$ なので、$`\upsilon_\omega \le_2 \upsilon_\omega + 1`$ ではない。

## P3：≤₁ の連続性

**命題.** $`y \le \alpha`$、$`\alpha`$ は後続で閉じ、すべての $`v \in [y, \alpha)`$ で $`y \le_1 v`$ とする。このとき $`y \le_1 \alpha`$ である。

**証明.** $`y = \alpha`$ なら反射律。$`y \lt \alpha`$ とし、$`y`$ 未満のパラメータを持つ $`\Sigma_1`$ 論理式 $`\varphi`$ を取る。

- $`\alpha \models \varphi`$ とする。証人 $`x_0, \dots, x_{b-1} \lt \alpha`$ の上界 $`z \lt \alpha`$ を取る（[01](01-ordinals.md) §2.1）。$`v = \max(y, z + 1)`$ は後続で閉じることから $`\alpha`$ 未満で、証人はすべて $`v`$ 未満なので $`v \models \varphi`$。$`y \le_1 v`$ から $`y \models \varphi`$
- $`y \models \varphi`$ なら、上へ保存で $`\alpha \models \varphi`$

$`\square`$

## P4：非有界な集合での連続性（段 1、2）

**命題.** $`j \in \{1, 2\}`$、$`y \lt \alpha`$ とする。$`S \subseteq [y, \alpha)`$ が $`\alpha`$ で非有界で、すべての $`v \in S`$ で $`y \le_j v`$ なら、$`y \le_j \alpha`$ である。

**証明.** $`j = 1`$ は P3 の証明と同じで、$`v`$ を $`S`$ から取ればよい。$`j = 2`$ とし、$`y`$ 未満のパラメータ $`\vec p`$ を持つ $`\Sigma_2`$ 論理式 $`\varphi = \exists \vec x\ \forall \vec z\ \psi`$ を取る。$`\Sigma_1`$ 論理式の一致は $`j = 1`$ の場合から出ている。

- $`\alpha \models \varphi`$ とする。証人 $`\vec x \lt \alpha`$ より大きい $`v \in S`$ を取る。$`\Pi_1`$ 論理式 $`\forall \vec z\ \psi(\vec p, \vec x, \vec z)`$ は下へ保存されるので $`v`$ で真、よって $`v \models \varphi`$。$`y \le_2 v`$ から $`y \models \varphi`$
- $`y \models \varphi`$ とする。証人 $`\vec x \lt y`$ について $`y \models \forall \vec z\ \psi`$。もし $`\alpha \models \exists \vec z\ \neg \psi(\vec p, \vec x, \vec z)`$ なら、その証人より大きい $`v \in S`$ を取ると $`v \models \exists \vec z\ \neg \psi`$。$`y \le_1 v`$ から $`y \models \exists \vec z\ \neg \psi`$ となり矛盾。よって $`\alpha \models \varphi`$

$`\square`$

**なぜ段 3 では同じ議論ができないか.** $`\Sigma_3`$ 論理式 $`\exists \vec x\ \forall \vec z\ \exists \vec w\ \psi`$ では、1 つめの向きで「$`\alpha`$ で真な $`\forall \vec z\ \exists \vec w\ \psi`$ が $`v`$ でも真」が要る。しかし $`\vec z \lt v`$ に対する証人 $`\vec w`$ が $`v`$ 以上にあるかもしれず、$`v`$ へ下ろせない。

## P5：<₁ の下端は後続で閉じる

**命題.** $`\alpha \lt_1 \beta`$ なら、$`\alpha`$ は後続で閉じる。

**証明.** $`\alpha = z + 1`$ とする。パラメータ $`z`$ を持つ $`\Sigma_1`$ 論理式 $`\exists x\ (z \lt x)`$ は、$`\beta`$ で真（$`x = \alpha`$）、$`\alpha`$ で偽である。$`\alpha \le_1 \beta`$ に反する。$`\square`$

例：$`3 \lt_1 \beta`$ となる $`\beta`$ は無い。

## P6：<₂ の上端は後続で閉じる

**命題.** $`y \lt_2 \beta`$ なら、$`\beta`$ は後続で閉じる。

**証明.** $`\beta = z + 1`$ とする。$`\Sigma_2`$ 論理式 $`\sigma = \exists x\ \forall w\ (w \le x)`$（最大元がある）は $`\beta`$ で真（$`x = z`$）。$`y \le_2 \beta`$ から $`y \models \sigma`$ なので、$`x_0 \lt y`$ で、$`y`$ 未満のすべての $`w`$ が $`w \le x_0`$ となるものがある。一方 $`y \lt_1 \beta`$ なので、P5 から $`y`$ は後続で閉じ、$`x_0 + 1 \lt y`$ となって矛盾する。$`\square`$

P5 は下端について、P6 は上端について言っている。

## P7：<₂ の下端では ≤₁-前者が非有界

**命題.** $`\alpha \lt_2 \beta`$ なら、どの $`z \lt \alpha`$ に対しても、$`z \lt u \lt \alpha`$ かつ $`u \le_1 \alpha`$ となる $`u`$ がある。

**証明.** パラメータ $`z`$ を持つ $`\Sigma_2`$ 論理式

```math
\varphi(z) = \exists u\ \bigl(z \lt u \wedge \forall w\ (u \le w \Rightarrow u \le_1 w)\bigr)
```

を考える。

1. $`\beta`$ で真：$`u = \alpha`$ とする。$`\alpha \le_1 \beta`$ なので、P1 から $`[\alpha, \beta)`$ のすべての $`w`$ で $`\alpha \le_1 w`$
2. $`\alpha \le_2 \beta`$ から $`\alpha \models \varphi(z)`$。証人 $`u \in (z, \alpha)`$ は、すべての $`w \in [u, \alpha)`$ で $`u \le_1 w`$
3. P5 から $`\alpha`$ は後続で閉じるので、P3 から $`u \le_1 \alpha`$

$`\square`$

## 証明での使われ方

| 性質 | 使う場所 |
|---|---|
| P1、P3、P5 | [06](06-finite-reflection.md) の $`n = 1`$ と $`n = 2`$ |
| P2、P4、P6、P7 | [06](06-finite-reflection.md) の $`n = 2`$ |

## Lean での対応

Lean の段の番号は 1 つずれている（`lev N 0` が $`\le_1`$）。

| 性質 | Lean | ファイル |
|---|---|---|
| P1 | `lev0_of_le` | [`Pattern/Basic.lean`](../lean/Pattern/Basic.lean) |
| P2 | `lev1_of_lev0` | 同上 |
| P3 | `lev0_of_forall` | 同上 |
| P4 | `elem_cofinal` | 同上 |
| P5 | `succ_lt_of_lab0` | 同上 |
| P6 | `succ_lt_of_lab1_top` | 同上 |
| P7 | `exists_lev0_below` | 同上 |
