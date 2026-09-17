[← Back](README.md)

# ϑᵢ と υ の対応表

前提: [01](01-theta.md)、[02](02-upsilon.md)、[03](03-examples.md)

根拠の列の意味は次のとおり。

| 根拠 | 意味 |
|---|---|
| W | Wilken の論文にある値 |
| 計算 | 定義から計算した。[03](03-examples.md) の該当する節を書く |
| 概略 | 定義からの概略だけで、細部は確かめていない |

Buchholz の $`\psi`$（$`\Omega_0 = 1`$、$`\nu \le \omega`$ の $`\psi_\nu`$）の列は、Wilken の論文には無い。
小さい値は $`\psi`$ の定義から計算し、SVO、LVO、$`\psi_0(\Omega_n)`$、$`\psi_0(\Omega_\omega)`$ はよく知られた値を書いた。この列の計算はノートには書いていない。

## 1. ϑ₀（τ = 1）

| ϑ の項 | 値 | 別の書き方 | Buchholz の $`\psi`$ | 根拠 |
|---|---|---|---|---|
| $`\vartheta_0(0)`$ | $`1`$ | $`\varphi(0, 0)`$ | $`\psi_0(0)`$ | W |
| $`\vartheta_0(1)`$ | $`\omega`$ | $`\varphi(0, 1)`$ | $`\psi_0(1)`$ | W |
| $`\vartheta_0(2)`$ | $`\omega^2`$ | | $`\psi_0(2)`$ | 計算 §2 |
| $`\vartheta_0(\omega)`$ | $`\omega^\omega`$ | | $`\psi_0(\omega)`$ | 計算 §2 |
| $`\vartheta_0(\varepsilon_0)`$ | $`\varepsilon_0 \cdot \omega`$ | $`\omega^{\varepsilon_0+1}`$ | $`\psi_0(\Omega + 1)`$ | W |
| $`\vartheta_0(\Omega)`$ | $`\varepsilon_0`$ | $`\varphi(1, 0)`$ | $`\psi_0(\Omega)`$ | W |
| $`\vartheta_0(\Omega + 1)`$ | $`\varepsilon_1`$ | $`\varphi(1, 1)`$ | $`\psi_0(\Omega \cdot 2)`$ | 計算 §4.2 |
| $`\vartheta_0(\Omega + \varepsilon_0)`$ | $`\varepsilon_{\varepsilon_0}`$ | $`\varphi(1, \varepsilon_0)`$ | $`\psi_0(\Omega \cdot \varepsilon_0)`$ | W |
| $`\vartheta_0(\Omega \cdot 2)`$ | $`\zeta_0`$ | $`\varphi(2, 0)`$ | $`\psi_0(\Omega^2)`$ | W |
| $`\vartheta_0(\Omega \cdot 3)`$ | $`\varphi(3, 0)`$ | | $`\psi_0(\Omega^3)`$ | 概略 §4.5 |
| $`\vartheta_0(\Omega \cdot \omega)`$ | $`\varphi(\omega, 0)`$ | | $`\psi_0(\Omega^\omega)`$ | 概略 §4.5 |
| $`\vartheta_0(\Omega^2)`$ | $`\Gamma_0`$ | $`\varphi(1, 0, 0)`$ | $`\psi_0(\Omega^\Omega)`$ | W |
| $`\vartheta_0(\Omega^\omega)`$ | SVO | | $`\psi_0(\Omega^{\Omega^\omega})`$ | 概略 §4.6 |
| $`\vartheta_0(\Omega^\Omega)`$ | LVO | | $`\psi_0(\Omega^{\Omega^\Omega})`$ | 概略 §4.6 |
| $`\vartheta_0(\varepsilon_{\Omega+1})`$ | BHO | $`\lvert \mathrm{ID}_1 \rvert`$ | $`\psi_0(\Omega_2)`$ | W |
| $`\vartheta_0(\vartheta_1(\vartheta_2(\vartheta_3(0))))`$ | $`\lvert \mathrm{ID}_2 \rvert`$ | | $`\psi_0(\Omega_3)`$ | W |
| $`\vartheta_0(\vartheta_1(\cdots \vartheta_{n+1}(0) \cdots))`$ | $`\lvert \mathrm{ID}_n \rvert`$ | | $`\psi_0(\Omega_{n+1})`$ | W |
| 上の行の $`n \to \omega`$ の上限 | $`\upsilon_1`$ | $`\lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert`$ | $`\psi_0(\Omega_\omega)`$ | W |

SVO は小 Veblen 順序数、LVO は大 Veblen 順序数、BHO は Bachmann–Howard 順序数である。

**R₂ での意味（Wilken）.**

| 順序数 | $`\mathcal{R}_2`$ での意味 |
|---|---|
| $`\varepsilon_0 \cdot \omega = \vartheta_0(\varepsilon_0)`$ | $`\lt_2`$-後者を持つ最小の順序数 |
| $`\vartheta_0(\vartheta_1(\cdots \vartheta_{n+1}(0) \cdots))`$ | $`n + 2`$ 個の順序数からなる各点最小の $`\lt_2`$ 鎖の、最小の $`\le_1`$-前者 |
| $`\upsilon_1`$ | $`\le_1`$-最小。$`\mathcal{R}_2`$ のコア全体 |

## 2. ϑ₁、ϑ₂

| ϑ の項 | 値 | 根拠 |
|---|---|---|
| $`\vartheta_1(0)`$ | $`\Omega`$ | 計算 §3 |
| $`\vartheta_1(1)`$ | $`\Omega \cdot \omega`$ | 計算 §3 |
| $`\vartheta_1(\omega)`$ | $`\Omega \cdot \omega^\omega`$ | 計算 §3 |
| $`\vartheta_1(\vartheta_1(0))`$ | $`\Omega^2`$ | W |
| $`\vartheta_1(\vartheta_1(1))`$ | $`\Omega^\omega`$ | 計算 §3 |
| $`\vartheta_1(\vartheta_1(\vartheta_1(0)))`$ | $`\Omega^\Omega`$ | 計算 §3 |
| $`\vartheta_2(0)`$ | $`\Omega_2`$ | W |
| $`\vartheta_1(\vartheta_2(0))`$ | $`\varepsilon_{\Omega+1}`$ | W |

## 3. 相対化した ϑ^τ

右端の列は、同じ順序数の、相対化しない $`T`$ での項である。$`\upsilon_1`$ 以上の可算順序数は $`T`$ に項を持たない。

| τ | ϑ^τ の項 | 値 | $`T`$ での項 | 根拠 |
|---|---|---|---|---|
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(0)`$ | $`\varepsilon_0`$ | $`\vartheta_0(\Omega)`$ | 計算 §5.1 |
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(1)`$ | $`\varepsilon_0 \cdot \omega`$ | $`\vartheta_0(\varepsilon_0)`$ | 計算 §5.1 |
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(\Omega)`$ | $`\varepsilon_1`$ | $`\vartheta_0(\Omega + 1)`$ | 計算 §5.1 |
| BHO | $`\vartheta^{\mathrm{BHO}}(\Omega^2)`$ | $`\Gamma_{\mathrm{BHO}+1}`$ | $`\vartheta_0(\Omega^2 + \mathrm{BHO})`$ | W |
| $`\Gamma_{\mathrm{BHO}+1}`$ | $`\vartheta^{\Gamma_{\mathrm{BHO}+1}}(\Omega)`$ | $`\varepsilon_{\Gamma_{\mathrm{BHO}+1}+1}`$ | $`\vartheta_0(\Omega + \Gamma_{\mathrm{BHO}+1})`$ | W |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(0)`$ | $`\upsilon_1`$ | 無い | 計算 §6.2 |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(1)`$ | $`\upsilon_1 \cdot \omega`$ | 無い | 計算 §6.2 |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(\Omega)`$ | $`\varepsilon_{\upsilon_1+1}`$ | 無い | 計算 §6.2 |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(\Omega^2)`$ | $`\Gamma_{\upsilon_1+1}`$ | 無い | 計算 §6.2 |
| $`\upsilon_1`$ | 上限 $`\sup_n \vartheta^{\upsilon_1}(\vartheta_1(\cdots \vartheta_n(0) \cdots))`$ | $`\upsilon_2`$ | 無い | 定義 |

## 4. υ

$`\lambda`$ は極限順序数、$`3 \le n \lt \omega`$ である。$`\mathcal{R}_2`$ と $`\mathcal{R}_3`$ の列は Wilken の結果（[02](02-upsilon.md) §3、§4）。

| $`\upsilon_\iota`$ | 定義 | 大きさ | $`\mathcal{R}_2`$ | $`\mathcal{R}_3`$ |
|---|---|---|---|---|
| $`\upsilon_0`$ | $`0`$ | $`0`$ | | |
| $`\upsilon_1`$ | $`T \cap \Omega`$ | $`\psi_0(\Omega_\omega)`$ | $`\le_1`$-最小。$`\lt_2`$-後者は無い | |
| $`\upsilon_2`$ | $`T^{\upsilon_1} \cap \Omega`$ | 可算、ε 数 | $`\upsilon_1 \lt_1 \upsilon_2`$。最小の $`\lt_2`$-後者は $`\upsilon_2 + \upsilon_1`$ | |
| $`\upsilon_n`$ | $`T^{\upsilon_{n-1}} \cap \Omega`$ | 可算、ε 数 | $`\upsilon_2 \lt_2 \cdots \lt_2 \upsilon_n`$。最小の $`\lt_2`$-後者は $`\upsilon_n + \upsilon_{n-1}`$ | |
| $`\upsilon_\omega`$ | $`\sup_n \upsilon_n`$ | 可算、ε 数 | 最初の無限 $`\lt_2`$ 鎖の上限。最小の $`\lt_2`$-後者は $`\upsilon_\omega \cdot 2`$ | |
| $`\upsilon_{\lambda+1}`$ | $`T^{\upsilon_\lambda} \cap \Omega`$ | | $`\lt_2`$-後者は無い。最大の $`\lt_1`$-前者は $`\upsilon_\lambda`$ | |
| $`\upsilon_{\lambda+2}`$ | $`T^{\upsilon_{\lambda+1}} \cap \Omega`$ | | 最小の $`\lt_2`$-後者は $`\upsilon_{\lambda+2} + \upsilon_{\lambda+1}`$ | |
| $`\upsilon_{\omega^2}`$ | $`\sup_{\iota \lt \omega^2} \upsilon_\iota`$ | 可算、ε 数 | | 最小の $`\lt_3`$ の組の下端 |
| $`\upsilon_{\omega^2+2}`$ | $`T^{\upsilon_{\omega^2+1}} \cap \Omega`$ | 可算、ε 数 | | 最小の $`\lt_3`$ の組の上端。この始切片の上で $`\mathcal{R}_2`$ と $`\mathcal{R}_3`$ の関係は一致 |
| $`\upsilon_{\omega_1}`$ | $`\sup_{\iota \lt \omega_1} \upsilon_\iota`$ | $`\omega_1`$ | | |

「可算、ε 数」は [02](02-upsilon.md) §2 の 3、4 による。$`\upsilon_2`$ 以降を Buchholz の $`\psi`$ で書いた式は、Wilken の論文には無く、ここでも確かめていない。

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021) 103001. https://doi.org/10.1016/j.apal.2021.103001
- G. Wilken, Pure Σ2-Elementarity beyond the Core, arXiv 版 v1. https://arxiv.org/abs/1710.01870v1
- T. J. Carlson and G. Wilken, Tracking chains of Σ2-elementarity, Annals of Pure and Applied Logic 163 (2012) 23–67. https://doi.org/10.1016/j.apal.2011.08.003
- W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207.
