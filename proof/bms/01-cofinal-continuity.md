[← Back](README.md) | [English](en/01-cofinal-continuity.md) | [Japanese](01-cofinal-continuity.md)

# P4′ と P2′：すべての段での連続性と閉じ方

前提: [pss 02 構造と初等部分構造](../pss/02-elementary-substructure.md)、[pss 03 R_N](../pss/03-patterns.md)、[pss 04 R_N の性質 P1〜P7](../pss/04-pattern-properties.md)

## 1. 何が要るか

3 行までの有限反映は、[pss 04](../pss/04-pattern-properties.md) の P2（$`\le_2`$ は $`\le_1`$ に沿って閉じる）と P4（非有界な集合での連続性、段 1、2）を使った。すべての段の有限反映には、この 2 つをすべての段に広げたものが要る。

P4 は、段 3 ではそのままの形では示せない（[pss 04](../pss/04-pattern-properties.md) の P4 の後の注意）。このノートでは、$`S`$ の元 $`v`$ に条件 $`v \le_{j-2} \alpha`$ を足すと、どの段でも成り立つことを示す。

**記法.** $`\le_0`$ と $`\le_{-1}`$ は $`\le`$ と読む。したがって $`j \le 2`$ のとき、$`v \lt \alpha`$ なら条件 $`v \le_{j-2} \alpha`$ は自動的に成り立つ。

論理式は [pss 02](../pss/02-elementary-substructure.md) §5 の形 $`\exists \vec x_1\ \neg\, \exists \vec x_2\ \neg \cdots`$ で考え、$`\le_j`$ は「ブロックが $`j`$ 個以下の論理式の真偽が一致する」ことで判定する。

## 2. P4′：非有界な集合での連続性

**命題（P4′）.** $`1 \le j \le N`$、$`y \lt \alpha`$ とする。$`S \subseteq [y, \alpha)`$ が $`\alpha`$ で非有界で、すべての $`v \in S`$ で

```math
y \le_j v \wedge v \le_{j-2} \alpha
```

なら、$`y \le_j \alpha`$ である。

$`j = 1, 2`$ では後ろの条件は自動的に成り立つので、これは P4 と同じである。

**証明.** $`y`$ 未満のパラメータ $`\vec p`$ を持ち、ブロックが $`j`$ 個以下の論理式 $`\varphi`$ を取り、$`y \models \varphi \iff \alpha \models \varphi`$ を示す。ブロックが 0 個なら量化子なしなので、真偽は $`\vec p`$ の原子図式で決まり、一致する。

**ブロックが 1 個のとき.** $`\varphi = \exists \vec x\ \psi`$（$`\psi`$ は量化子なし）と書く。

- $`y \models \varphi`$ なら、上へ保存で $`\alpha \models \varphi`$
- $`\alpha \models \varphi`$ とする。証人 $`\vec x \lt \alpha`$ のすべてより大きい $`v \in S`$ を取ると $`v \models \varphi`$。$`y \le_j v`$ から $`y \models \varphi`$

**ブロックが 2 個以上のとき.** $`\varphi = \exists \vec x\ \neg\, \exists \vec z\ \neg\, \chi`$ と書く。$`\chi`$ のブロックは $`j - 2`$ 個以下である。

$`y \models \varphi`$ とし、証人を $`\vec x \lt y`$ とする。つまり $`y \models \neg\, \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$ である。$`\alpha \models \varphi`$ を示すため、$`\alpha \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$ と仮定して矛盾を導く。

1. 証人 $`\vec z \lt \alpha`$ のすべてより大きい $`v \in S`$ を取る。$`\vec p, \vec x \lt y \le v`$ なので、パラメータはすべて $`v`$ 未満
2. $`\chi`$ のブロックは $`j - 2`$ 個以下なので、$`v \le_{j-2} \alpha`$ から $`v \models \neg\, \chi(\vec p, \vec x, \vec z)`$
3. よって $`v \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$。これはブロックが $`j - 1`$ 個以下なので、$`y \le_j v`$ から $`y`$ でも真
4. $`\vec x`$ の選び方に反する

$`\alpha \models \varphi`$ とし、証人を $`\vec x \lt \alpha`$ とする。$`\vec x`$ のすべてより大きい $`v \in S`$ を取り、$`v \models \varphi`$ を示す。

1. $`v \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$ と仮定し、証人を $`\vec z \lt v`$ とする
2. $`v \le_{j-2} \alpha`$ から $`\alpha \models \neg\, \chi(\vec p, \vec x, \vec z)`$ となり、$`\vec x`$ の選び方に反する
3. よって $`\vec x`$ は $`v`$ での証人になり、$`v \models \varphi`$。$`y \le_j v`$ から $`y \models \varphi`$

$`\square`$

**なぜ条件が効くか.** [pss 04](../pss/04-pattern-properties.md) で見たとおり、条件が無いと、$`\alpha`$ で真な内側の論理式を $`v`$ へ下ろすときに、証人が $`v`$ 以上にあるかもしれない。条件 $`v \le_{j-2} \alpha`$ があると、内側の $`\chi`$ の真偽が $`v`$ と $`\alpha`$ で一致するので、証人を下ろす必要が無い。

## 3. P2′：≤ₘ₊₁ は ≤ₘ に沿って閉じる

**命題（P2′）.** $`1 \le m \lt N`$ とする。$`a \le b \le c`$、$`a \le_m b`$、$`b \le_m c`$、$`a \le_{m+1} c`$ なら、$`a \le_{m+1} b`$ である。

$`m = 1`$ が P2 である。$`m = 0`$ と読めば P1 になる。

**証明.** $`a`$ 未満のパラメータ $`\vec p`$ を持ち、ブロックが $`m + 1`$ 個以下の論理式を取る。ブロックが 0 個なら明らかなので、$`\varphi = \exists \vec x\ \neg\, \psi`$ と書く。$`\psi`$ のブロックは $`m`$ 個以下である。

- $`a \models \varphi`$ とし、証人を $`\vec x \lt a`$ とする。$`a \models \neg\, \psi(\vec p, \vec x)`$ で、$`a \le_m b`$ から $`b \models \neg\, \psi(\vec p, \vec x)`$。よって $`b \models \varphi`$
- $`b \models \varphi`$ とし、証人を $`\vec x \lt b`$ とする。$`b \models \neg\, \psi(\vec p, \vec x)`$ で、$`b \le_m c`$ から $`c \models \neg\, \psi(\vec p, \vec x)`$。よって $`c \models \varphi`$ で、$`a \le_{m+1} c`$ から $`a \models \varphi`$

$`\square`$

## 4. 系：上端に結ばれた点の間

**系.** $`1 \le m \le N`$ とする。$`u \le s \le \gamma`$、$`u \le_m \gamma`$、$`s \le_{m-1} \gamma`$ なら、$`u \le_m s`$ である。

**証明.** $`m`$ についての帰納法。

- $`m = 1`$：P1 そのもの
- $`m + 1`$：$`u \le_{m+1} \gamma`$ から $`u \le_m \gamma`$、$`s \le_m \gamma`$ から $`s \le_{m-1} \gamma`$。帰納法の仮定から $`u \le_m s`$。P2′ を $`a = u`$、$`b = s`$、$`c = \gamma`$ で使うと $`u \le_{m+1} s`$

$`\square`$

**読み方.** $`\gamma`$ に $`\le_m`$ で結ばれた $`u`$ は、$`\gamma`$ に $`\le_{m-1}`$ で結ばれた $`s \ge u`$ のすべてと $`\le_m`$ で結ばれる。

## 5. 証明での使われ方

| 性質 | 使う場所 |
|---|---|
| P4′ | [02](02-phi.md) の補題 A、[05](05-finite-reflection.md) の (d) |
| §4 の系 | [02](02-phi.md) の補題 B、[05](05-finite-reflection.md) の「β で真」 |

## 6. Lean での対応

Lean の段の番号は 1 つずれている（`lev N 0` が $`\le_1`$）。`Elem R j a b` は、ブロックが $`j`$ 個以下の論理式の真偽が一致することである。

| 性質 | Lean | ファイル |
|---|---|---|
| P4′ | `elem_cofinal_gen` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| P2′ | `elem_of_elem_top`, `lev_of_lev_top` | 同上 |
| §4 の系 | `lev_below_top` | 同上 |
| P1、P4（段 1、2） | `lev0_of_le`, `elem_cofinal` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
