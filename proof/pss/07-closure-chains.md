[← Back](README.md) | [English](en/07-closure-chains.md) | [Japanese](07-closure-chains.md)

# ω₁ の中の閉包と、すべての段で結ばれた鎖

前提: [01 順序数と ω₁](01-ordinals.md)、[02 構造と初等部分構造](02-elementary-substructure.md)、[03 R_N](03-patterns.md)

## 1. 何が要るか

$`S^r_n`$ の $`n + 1`$ 個の列にラベルを貼るには、順序数 $`c_0 \lt c_1 \lt \cdots \lt c_n`$ で、どの 2 つも $`\le_1, \dots, \le_r`$ のすべてで結ばれているものが要る（[08](08-termination.md)）。このノートでは、そういう鎖がどの長さでも存在することを示す。

## 2. 閉包の 1 段

**論理式の番号づけ.** [02](02-elementary-substructure.md) §5 の形の論理式は、原子図式の個数 $`n`$、原子図式の集合 $`D`$、ブロックの長さの列、パラメータの個数 $`k`$ の組で決まる。原子図式は有限種類なので、論理式全体は可算である。

**パラメータの番号づけ.** $`0 \lt \gamma \lt \omega_1`$ なら、全射 $`e : \mathbb{N} \to \gamma`$ がある（[01](01-ordinals.md) 事実 4）。$`\gamma`$ 未満の順序数の有限列は、自然数の有限列 $`(t_0, \dots, t_{k-1})`$ で $`(e(t_0), \dots, e(t_{k-1}))`$ と表せる。

**定義（next）.** 論理式と、パラメータの番号の組ごとに、次の値を考える。

- 論理式が $`\omega_1`$ で真なら、最初のブロックの証人 $`x_0, \dots, x_{b-1}`$ を 1 つ選び、$`\max_i (x_i + 1)`$ を取る
- 偽なら $`0`$ とする

これら全体の上限と $`\gamma`$ の大きいほうに $`1`$ を足したものを $`\mathrm{next}(\gamma)`$ とする。

**補題.** $`\gamma \lt \omega_1`$ なら $`\gamma \lt \mathrm{next}(\gamma) \lt \omega_1`$ である。

**証明.** 各値は $`\omega_1`$ 未満（証人が $`\omega_1`$ 未満で、事実 2）。組は可算個なので、事実 3 から上限も $`\omega_1`$ 未満。最後に事実 2 を使う。$`\square`$

**補題（証人は next の下にある）.** パラメータがすべて $`\gamma`$ 未満の論理式 $`\mathrm{Sig}([b_1, b_2, \dots, b_r], \vec p)`$ が $`\omega_1`$ で真なら、$`x_0, \dots, x_{b_1 - 1} \lt \mathrm{next}(\gamma)`$ で、$`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ が $`\omega_1`$ で偽となるものがある。

**証明.** パラメータを番号で表し、定義で選んだ証人を取る。$`\square`$

## 3. λ(γ)

**定義.**

```math
\lambda(\gamma) = \sup_{t \lt \omega} \mathrm{next}^t(\gamma)
```

$`\gamma \lt \omega_1`$ なら、事実 3 から $`\gamma \lt \lambda(\gamma) \lt \omega_1`$ である。

**補題.** $`\lambda(\gamma)`$ 未満の有限個の順序数は、ある $`t`$ についてすべて $`\mathrm{next}^t(\gamma)`$ 未満である。

**証明.** 各順序数について $`t`$ が取れ、$`\mathrm{next}^t(\gamma)`$ は $`t`$ について増加するので、その最大をとればよい。$`\square`$

**定理.** $`\gamma \lt \omega_1`$ とする。パラメータがすべて $`\lambda(\gamma)`$ 未満のどの論理式も、$`\lambda(\gamma)`$ と $`\omega_1`$ で真偽が一致する。

**証明.** ブロックの数についての帰納法で示す。

**ブロックが無いとき.** 真偽は原子図式だけで決まり、構造によらない。

**ブロック $`[b_1, b_2, \dots, b_r]`$ のとき.**

- $`\lambda(\gamma)`$ で真とする。証人 $`\vec x \lt \lambda(\gamma)`$ で、$`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ が $`\lambda(\gamma)`$ で偽。パラメータ $`\vec p\,\vec x`$ は $`\lambda(\gamma)`$ 未満なので、帰納法の仮定から $`\omega_1`$ でも偽。$`\vec x \lt \omega_1`$ なので $`\omega_1`$ で真
- $`\omega_1`$ で真とする。パラメータは $`\mathrm{next}^t(\gamma)`$ 未満にとれる。§2 の補題から、$`\vec x \lt \mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$ で、$`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ が $`\omega_1`$ で偽。帰納法の仮定から $`\lambda(\gamma)`$ でも偽なので、$`\lambda(\gamma)`$ で真

$`\square`$

これは Löwenheim–Skolem–Tarski の議論を、初期切片の形で行ったものである。

## 4. 鎖

**系.** $`\gamma, \delta \lt \omega_1`$、$`\lambda(\gamma) \lt \lambda(\delta)`$ なら、すべての $`j \le N`$ で $`\lambda(\gamma) \lt_j \lambda(\delta)`$ である。

**証明.** パラメータが $`\lambda(\gamma)`$ 未満の論理式は、§3 の定理から $`\lambda(\gamma)`$ と $`\omega_1`$ で一致し、$`\lambda(\delta)`$ と $`\omega_1`$ でも一致する。$`\square`$

**鎖.** $`\Lambda_0 = \lambda(0)`$、$`\Lambda_{t+1} = \lambda(\Lambda_t)`$ と置くと、$`\Lambda_t \lt \lambda(\Lambda_t) = \Lambda_{t+1}`$ なので増加列である。系から、どの 2 つもすべての段で結ばれている。$`c_i = \Lambda_{i+1}`$ とすれば、どの長さの鎖も得られる。

## 5. ラベルの大きさについて

この構成で得られる順序数は $`\omega_1`$ 未満だが、どこにあるかは分からない。

- $`\mathcal{R}_2`$ では、有限の $`\le_2`$ 鎖は $`\psi_0(\Omega_\omega)`$ 未満にいくらでも長く取れることが、Wilken によって示されている（[03](03-patterns.md) §5）
- $`\mathcal{R}_3`$ では、最小の $`\lt_3`$ の組が $`\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2 + 2}`$ であることまで分かっている

これらは形式化していない。

## 6. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| どの長さの鎖もある | [08](08-termination.md) 初期列のラベル |

## 7. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 論理式の組 | `Form` | [`Pattern/Chain.lean`](../../lean/Pattern/Chain.lean) |
| パラメータの番号づけ | `params`, `exists_params` | 同上 |
| 証人の高さ | `witHeight`, `witHeight_lt` | 同上 |
| $`\mathrm{next}`$ | `next`, `lt_next`, `next_lt` | 同上 |
| 証人は next の下 | `wit_below` | 同上 |
| $`\mathrm{next}^t`$、$`\lambda`$ | `tower`, `lam`, `tower_le_lam`, `lam_lt`, `lt_lam` | 同上 |
| 有限個は途中の段の下 | `exists_tower` | 同上 |
| §3 の定理 | `lam_elem` | 同上 |
| §4 の系 | `lab_lam` | 同上 |
| 鎖 | `lamChain`, `lamChain_lt`, `lamChain_strictMono`, `exists_chain` | 同上 |
