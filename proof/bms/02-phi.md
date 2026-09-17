[← Back](README.md) | [English](en/02-phi.md) | [Japanese](02-phi.md)

# 論理式 Φₘ：上端との結びつきを中から言う

前提: [pss 04 R_N の性質 P1〜P7](../pss/04-pattern-properties.md)、[01 P4′ と P2′](01-cofinal-continuity.md)

## 1. 何が要るか

有限反映の (d) は「$`y_i \lt_{m+1} \beta`$ なら $`y'_i \lt_{m+1} \alpha`$」である。$`y'_i`$ は $`\alpha`$ で真な文の証人として得るので、「$`u \le_{m+1} \alpha`$」を $`\alpha`$ の中の論理式で言い表したい。しかし右辺の $`\alpha`$ は構造そのもので、構造の中の元ではないので、そのままでは論理式にならない。

このノートの $`\Phi_m`$ がその代わりになる。[pss 04](../pss/04-pattern-properties.md) の P7 の証明で使った $`\forall w\ (u \le w \Rightarrow u \le_1 w)`$ が $`\Phi_1`$ である。

## 2. 定義

**定義.** 構造 $`(\gamma; \le, \le_1, \dots, \le_N)`$ の中で、1 変数の論理式 $`\Phi_m(u)`$ を次で定める。

```math
\Phi_0(u) = \top
```

```math
\Phi_1(u) = \forall w\ \bigl(u \le w \Rightarrow u \le_1 w\bigr)
```

```math
\Phi_{m+2}(u) = \forall z\ \exists s\ \bigl(z \lt s \wedge u \le_{m+2} s \wedge \Phi_m(s)\bigr)
```

量化子の範囲は $`\gamma`$ 未満である。$`\gamma \models \Phi_m(u)`$ を「$`\gamma`$ で $`\Phi_m(u)`$」と書く。

**量化子の数.** $`m \ge 1`$ なら $`\Phi_m`$ は $`\Pi_m`$ 論理式である。

- $`\Phi_1`$：$`\forall w`$ の後ろは量化子なし
- $`\Phi_2`$：$`\exists s\ (z \lt s \wedge u \le_2 s)`$ は $`\Sigma_1`$、$`\forall z`$ を付けて $`\Pi_2`$
- $`\Phi_{m+2}`$（$`m \ge 1`$）：$`\Phi_m`$ が $`\Pi_m`$ なので $`\exists s\ (\cdots \wedge \Phi_m(s))`$ は $`\Sigma_{m+1}`$、$`\forall z`$ を付けて $`\Pi_{m+2}`$

Lean の論理式の形（ブロックの列）で書けることは [03](03-block-form.md) で示す。

**定義（前者が非有界）.** $`1 \le i \le N`$ について

```math
\mathrm{Cof}_i(\gamma) \iff \forall z \lt \gamma\ \exists s\ \bigl(z \lt s \lt \gamma \wedge s \le_i \gamma\bigr)
```

と置く。$`\gamma`$ の $`\le_i`$-前者が $`\gamma`$ で非有界であることをいう。$`i \le i'`$ なら $`\mathrm{Cof}_{i'}(\gamma) \Rightarrow \mathrm{Cof}_i(\gamma)`$ である。

## 3. 補題 A：Φₘ から ≤ₘ へ

**補題 A.** $`\gamma`$ は後続で閉じ、$`1 \le m \le N`$、$`u \lt \gamma`$ とする。$`\gamma`$ で $`\Phi_m(u)`$ なら、$`u \le_m \gamma`$ である。

**証明.** $`m`$ についての帰納法。

**$`m = 1`$ のとき.** すべての $`w \in [u, \gamma)`$ で $`u \le_1 w`$ である。P3 から $`u \le_1 \gamma`$。

**$`m \ge 2`$ のとき.** $`S`$ を、次を満たす $`s`$ 全体とする。

```math
u \lt s \lt \gamma, \qquad u \le_m s, \qquad \gamma \models \Phi_{m-2}(s)
```

1. $`S`$ は $`\gamma`$ で非有界：$`z \lt \gamma`$ に対し、$`\Phi_m(u)`$ を $`\max(z, u)`$ で使えば、$`z`$ より大きい $`s \in S`$ がある
2. $`m \ge 3`$ なら、帰納法の仮定から、すべての $`s \in S`$ で $`s \le_{m-2} \gamma`$。$`m = 2`$ なら、この条件は自動的に成り立つ
3. P4′（[01](01-cofinal-continuity.md)）を $`j = m`$ で使うと $`u \le_m \gamma`$

$`\square`$

## 4. 補題 B：≤ₘ から Φₘ へ

**補題 B.** $`1 \le m \le N`$、$`u \lt \gamma`$、$`u \le_m \gamma`$ とし、$`1 \le i \le m - 1`$ のすべてで $`\mathrm{Cof}_i(\gamma)`$ とする。このとき $`\gamma`$ で $`\Phi_m(u)`$ である。

**証明.** $`m`$ についての帰納法。

**$`m = 1`$ のとき.** $`w \in [u, \gamma)`$ なら、$`u \le w \le \gamma`$ と $`u \le_1 \gamma`$ から、P1 で $`u \le_1 w`$。

**$`m \ge 2`$ のとき.** $`z \lt \gamma`$ を取る。$`\mathrm{Cof}_{m-1}(\gamma)`$ から、$`\max(z, u) \lt s \lt \gamma`$ で $`s \le_{m-1} \gamma`$ となる $`s`$ がある。この $`s`$ が $`z`$ に対する証人であることを示す。

1. $`u \le s \le \gamma`$、$`u \le_m \gamma`$、$`s \le_{m-1} \gamma`$ なので、[01](01-cofinal-continuity.md) §4 の系から $`u \le_m s`$
2. $`m \ge 3`$ なら、$`s \le_{m-2} \gamma`$ と、$`i \le m - 3`$ の $`\mathrm{Cof}_i(\gamma)`$ から、帰納法の仮定で $`\gamma \models \Phi_{m-2}(s)`$。$`m = 2`$ なら $`\Phi_0`$ は真

$`\square`$

## 5. まとめ

$`\gamma`$ が後続で閉じ、$`i \lt m`$ のすべてで $`\mathrm{Cof}_i(\gamma)`$ なら、$`u \lt \gamma`$ について

```math
\gamma \models \Phi_m(u) \iff u \le_m \gamma
```

である。$`m = 1`$ では $`\mathrm{Cof}`$ の条件は無く、これは P1 と P3 の言い換えである。

## 6. 証明での使われ方

| 補題 | 使う場所 |
|---|---|
| 補題 A | [04](04-cofinal-predecessors.md) の段階 C、E、[05](05-finite-reflection.md) の「β で真」 |
| 補題 B | [04](04-cofinal-predecessors.md) の段階 A、D、[05](05-finite-reflection.md) の「α で (d)」 |

## 7. Lean での対応

Lean の `Phi N γ m u` は、論理式ではなく、$`\gamma`$ で評価した $`\Phi_m(u)`$ の意味を直接書いた命題である。論理式として書けることは [03](03-block-form.md) の `tn_sig` で示す。`Cof N j γ` は $`\mathrm{Cof}_{j+1}(\gamma)`$ である。

| 概念 | Lean | ファイル |
|---|---|---|
| $`\Phi_m`$ | `Phi` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| $`\mathrm{Cof}_i`$ | `Cof`, `Cof.mono` | 同上 |
| 補題 A | `lev_of_phi` | 同上 |
| 補題 B | `phi_of_lev` | 同上 |
| P3 | `lev0_of_forall` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
