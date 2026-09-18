[← Back](README.md)

# ϑᵢ と υ の対応表

前提: [01](01-theta.md)、[02](02-upsilon.md)、[03](03-examples.md)

Buchholz の $`\psi`$（$`\Omega_0 = 1`$、$`\nu \le \omega`$ の $`\psi_\nu`$）の列は、Wilken の論文には無い。
小さい値は $`\psi`$ の定義から計算し、SVO、LVO、$`\psi_0(\Omega_n)`$、$`\psi_0(\Omega_\omega)`$ はよく知られた値を書いた。この列の計算はノートには書いていない。

§1〜§3 の表は値の小さい順、§4 の表は添字の順に並べてある。

「全部 ϑ で書いた項」の列は、略記をすべて展開したものである。使う書き換えは次のとおり。

```math
1 = \vartheta_0(0), \quad \omega = \vartheta_0(\vartheta_0(0)), \quad \Omega = \vartheta_1(0), \quad \varepsilon_0 = \vartheta_0(\vartheta_1(0)), \quad \Omega_2 = \vartheta_2(0)
```

自然数 $`k`$ は $`\vartheta_0(0)`$ を $`k`$ 個足したものである。

## 1. ϑ₀（τ = 1）

| ϑ の項 | 全部 ϑ で書いた項 | 値 | Buchholz の $`\psi`$ |
|---|---|---|---|
| $`\vartheta_0(0)`$ | $`\vartheta_0(0)`$ | $`1`$ | $`\psi_0(0)`$ |
| $`\vartheta_0(1)`$ | $`\vartheta_0(\vartheta_0(0))`$ | $`\omega`$ | $`\psi_0(1)`$ |
| $`\vartheta_0(2)`$ | $`\vartheta_0(\vartheta_0(0) + \vartheta_0(0))`$ | $`\omega^2`$ | $`\psi_0(2)`$ |
| $`\vartheta_0(\omega)`$ | $`\vartheta_0(\vartheta_0(\vartheta_0(0)))`$ | $`\omega^\omega`$ | $`\psi_0(\omega)`$ |
| $`\vartheta_0(\Omega)`$ | $`\vartheta_0(\vartheta_1(0))`$ | $`\varepsilon_0`$ | $`\psi_0(\Omega)`$ |
| $`\vartheta_0(\varepsilon_0)`$ | $`\vartheta_0(\vartheta_0(\vartheta_1(0)))`$ | $`\varepsilon_0 \cdot \omega`$ | $`\psi_0(\Omega + 1)`$ |
| $`\vartheta_0(\varepsilon_0 + 1)`$ | $`\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(0))`$ | $`\varepsilon_0 \cdot \omega^2`$ | $`\psi_0(\Omega + 2)`$ |
| $`\vartheta_0(\varepsilon_0 + k)`$ | $`\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(0) + \cdots + \vartheta_0(0))`$ | $`\varepsilon_0 \cdot \omega^{k+1}`$ | $`\psi_0(\Omega + k + 1)`$ |
| $`\vartheta_0(\varepsilon_0 + \omega)`$ | $`\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(\vartheta_0(0)))`$ | $`\varepsilon_0 \cdot \omega^\omega`$ | $`\psi_0(\Omega + \omega)`$ |
| $`\vartheta_0(\varepsilon_0 \cdot 2)`$ | $`\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(\vartheta_1(0)))`$ | $`\varepsilon_0^2`$ | $`\psi_0(\Omega + \varepsilon_0)`$ |
| $`\vartheta_0(\varepsilon_0 \cdot \omega)`$ | $`\vartheta_0(\vartheta_0(\vartheta_0(\vartheta_1(0))))`$ | $`\varepsilon_0^\omega`$ | $`\psi_0(\Omega + \varepsilon_0 \cdot \omega)`$ |
| $`\vartheta_0(\varepsilon_0^2)`$ | $`\vartheta_0(\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(\vartheta_1(0))))`$ | $`\varepsilon_0^{\varepsilon_0}`$ | $`\psi_0(\Omega + \varepsilon_0^2)`$ |
| $`\vartheta_0(\varepsilon_0^{\varepsilon_0})`$ | $`\vartheta_0(\vartheta_0(\vartheta_0(\vartheta_0(\vartheta_1(0)) + \vartheta_0(\vartheta_1(0)))))`$ | $`\omega^{\varepsilon_0^{\varepsilon_0}}`$ | $`\psi_0(\Omega + \varepsilon_0^{\varepsilon_0})`$ |
| $`\vartheta_0(\Omega + 1)`$ | $`\vartheta_0(\vartheta_1(0) + \vartheta_0(0))`$ | $`\varepsilon_1`$ | $`\psi_0(\Omega \cdot 2)`$ |
| $`\vartheta_0(\Omega + \varepsilon_0)`$ | $`\vartheta_0(\vartheta_1(0) + \vartheta_0(\vartheta_1(0)))`$ | $`\varepsilon_{\varepsilon_0}`$ | $`\psi_0(\Omega \cdot \varepsilon_0)`$ |
| $`\vartheta_0(\Omega \cdot 2)`$ | $`\vartheta_0(\vartheta_1(0) + \vartheta_1(0))`$ | $`\zeta_0`$ | $`\psi_0(\Omega^2)`$ |
| $`\vartheta_0(\Omega \cdot 3)`$ | $`\vartheta_0(\vartheta_1(0) + \vartheta_1(0) + \vartheta_1(0))`$ | $`\varphi(3, 0)`$ | $`\psi_0(\Omega^3)`$ |
| $`\vartheta_0(\Omega \cdot \omega)`$ | $`\vartheta_0(\vartheta_1(\vartheta_0(0)))`$ | $`\varphi(\omega, 0)`$ | $`\psi_0(\Omega^\omega)`$ |
| $`\vartheta_0(\Omega^2)`$ | $`\vartheta_0(\vartheta_1(\vartheta_1(0)))`$ | $`\Gamma_0`$ | $`\psi_0(\Omega^\Omega)`$ |
| $`\vartheta_0(\Omega^\omega)`$ | $`\vartheta_0(\vartheta_1(\vartheta_1(\vartheta_0(0))))`$ | SVO | $`\psi_0(\Omega^{\Omega^\omega})`$ |
| $`\vartheta_0(\Omega^\Omega)`$ | $`\vartheta_0(\vartheta_1(\vartheta_1(\vartheta_1(0))))`$ | LVO | $`\psi_0(\Omega^{\Omega^\Omega})`$ |
| $`\vartheta_0(\varepsilon_{\Omega+1})`$ | $`\vartheta_0(\vartheta_1(\vartheta_2(0)))`$ | BHO | $`\psi_0(\Omega_2)`$ |
| $`\vartheta_0(\vartheta_1(\vartheta_2(\vartheta_3(0))))`$ | 同じ | $`\lvert \mathrm{ID}_2 \rvert`$ | $`\psi_0(\Omega_3)`$ |
| $`\vartheta_0(\vartheta_1(\cdots \vartheta_{n+1}(0) \cdots))`$ | 同じ | $`\lvert \mathrm{ID}_n \rvert`$ | $`\psi_0(\Omega_{n+1})`$ |
| 上の行の $`n \to \omega`$ の上限 | 無い | $`\upsilon_1`$ | $`\psi_0(\Omega_\omega)`$ |

SVO は小 Veblen 順序数、LVO は大 Veblen 順序数、BHO は Bachmann–Howard 順序数である。

- $`\varphi(3, 0)`$、$`\varphi(\omega, 0)`$、SVO、LVO の行は、定義からの概略だけで確かめた（[03](03-examples.md) §4.5、§4.6）。ほかの行は Wilken の論文にある値か、[03](03-examples.md) の計算である

- $`\varepsilon_0 = \omega^{\varepsilon_0}`$ なので $`\varepsilon_0^\alpha = \omega^{\varepsilon_0 \cdot \alpha}`$ である。これで 2 列目と 3 列目が同じ順序数になる
- $`\varepsilon_0`$ と $`\varepsilon_1`$ の間の加法的主要数は、すべて $`\vartheta_0(\eta)`$（$`\varepsilon_0 \le \eta \lt \varepsilon_1`$）で名前が付く。$`\varepsilon_1`$ 自身は $`\Delta = 0`$ の段では名前が付かず、$`\vartheta_0(\Omega + 1)`$ になる。その間の順序数は、表の値の有限和（Cantor 標準形）で全部書ける
- Buchholz では $`\psi_0(\Omega + \alpha) = \omega^{\varepsilon_0 + \alpha}`$（$`\alpha \ge 1`$ で、$`\alpha`$ が hull に入るとき）

## 2. ϑ₁、ϑ₂

$`\vartheta_1 = \vartheta^\Omega`$ なので、この表は §1 を $`\tau = \Omega`$ に相対化したものと同じ形になる。$`\Omega_2`$ が §1 の $`\Omega`$ の役をする。

| ϑ の項 | 全部 ϑ で書いた項 | 値 |
|---|---|---|
| $`\vartheta_1(0)`$ | $`\vartheta_1(0)`$ | $`\Omega`$ |
| $`\vartheta_1(1)`$ | $`\vartheta_1(\vartheta_0(0))`$ | $`\Omega \cdot \omega`$ |
| $`\vartheta_1(2)`$ | $`\vartheta_1(\vartheta_0(0) + \vartheta_0(0))`$ | $`\Omega \cdot \omega^2`$ |
| $`\vartheta_1(\omega)`$ | $`\vartheta_1(\vartheta_0(\vartheta_0(0)))`$ | $`\Omega \cdot \omega^\omega`$ |
| $`\vartheta_1(\Omega)`$ | $`\vartheta_1(\vartheta_1(0))`$ | $`\Omega^2`$ |
| $`\vartheta_1(\Omega \cdot 2)`$ | $`\vartheta_1(\vartheta_1(0) + \vartheta_1(0))`$ | $`\Omega^3`$ |
| $`\vartheta_1(\Omega \cdot \omega)`$ | $`\vartheta_1(\vartheta_1(\vartheta_0(0)))`$ | $`\Omega^\omega`$ |
| $`\vartheta_1(\Omega^2)`$ | $`\vartheta_1(\vartheta_1(\vartheta_1(0)))`$ | $`\Omega^\Omega`$ |
| $`\vartheta_1(\Omega^\Omega)`$ | $`\vartheta_1(\vartheta_1(\vartheta_1(\vartheta_1(0))))`$ | $`\Omega^{\Omega^\Omega}`$ |
| $`\vartheta_1(\Omega_2)`$ | $`\vartheta_1(\vartheta_2(0))`$ | $`\varepsilon_{\Omega+1}`$ |
| $`\vartheta_1(\varepsilon_{\Omega+1})`$ | $`\vartheta_1(\vartheta_1(\vartheta_2(0)))`$ | $`\varepsilon_{\Omega+1} \cdot \omega`$ |
| $`\vartheta_1(\varepsilon_{\Omega+1} \cdot \omega)`$ | $`\vartheta_1(\vartheta_1(\vartheta_1(\vartheta_2(0))))`$ | $`\varepsilon_{\Omega+1}^\omega`$ |
| $`\vartheta_1(\Omega_2 + 1)`$ | $`\vartheta_1(\vartheta_2(0) + \vartheta_0(0))`$ | $`\varepsilon_{\Omega+2}`$ |
| $`\vartheta_1(\Omega_2 + \Omega)`$ | $`\vartheta_1(\vartheta_2(0) + \vartheta_1(0))`$ | $`\varepsilon_{\Omega \cdot 2}`$ |
| $`\vartheta_1(\Omega_2 \cdot 2)`$ | $`\vartheta_1(\vartheta_2(0) + \vartheta_2(0))`$ | $`\varphi(2, \Omega+1)`$ |
| $`\vartheta_1(\Omega_2^2)`$ | $`\vartheta_1(\vartheta_2(\vartheta_2(0)))`$ | $`\Gamma_{\Omega+1}`$ |
| $`\vartheta_1(\varepsilon_{\Omega_2+1})`$ | $`\vartheta_1(\vartheta_2(\vartheta_3(0)))`$ | $`\Omega`$ の上の BHO |
| $`\vartheta_2(0)`$ | $`\vartheta_2(0)`$ | $`\Omega_2`$ |
| $`\vartheta_2(1)`$ | $`\vartheta_2(\vartheta_0(0))`$ | $`\Omega_2 \cdot \omega`$ |
| $`\vartheta_2(\Omega_2)`$ | $`\vartheta_2(\vartheta_2(0))`$ | $`\Omega_2^2`$ |
| $`\vartheta_2(\Omega_3)`$ | $`\vartheta_2(\vartheta_3(0))`$ | $`\varepsilon_{\Omega_2+1}`$ |
| $`\vartheta_3(0)`$ | $`\vartheta_3(0)`$ | $`\Omega_3`$ |

- $`\Omega`$ は ε 数、ζ 数、Γ 数のどれでもある。よって $`\Omega`$ より大きい最小の ε 数は $`\varepsilon_{\Omega+1}`$、最小の ζ 数は $`\varphi(2, \Omega+1)`$、最小の Γ 数は $`\Gamma_{\Omega+1}`$ である
- 「$`\Omega`$ の上の BHO」は、§1 の $`\vartheta_0(\vartheta_1(\vartheta_2(0))) = \mathrm{BHO}`$ を 1 段上げたものである。$`\vartheta_1 = \vartheta^\Omega`$ なので、BHO の作り方を $`\Omega`$ の上でやり直した順序数になり、$`\Omega`$ と $`\Omega_2`$ の間にある。決まった名前は無い
- $`\Omega = \omega^\Omega`$ なので $`\Omega^\alpha = \omega^{\Omega \cdot \alpha}`$ である。たとえば $`\Omega^3 = \omega^{\Omega \cdot 3}`$、$`\Omega^{\Omega^\Omega} = \omega^{\Omega^\Omega}`$

## 3. 相対化した ϑ^τ

右端の列は、同じ順序数の、相対化しない $`T`$ での項である。$`\upsilon_1`$ 以上の可算順序数は $`T`$ に項を持たない。

| τ | ϑ^τ の項 | 値 | $`T`$ での項 |
|---|---|---|---|
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(0)`$ | $`\varepsilon_0`$ | $`\vartheta_0(\Omega)`$ |
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(1)`$ | $`\varepsilon_0 \cdot \omega`$ | $`\vartheta_0(\varepsilon_0)`$ |
| $`\varepsilon_0`$ | $`\vartheta^{\varepsilon_0}(\Omega)`$ | $`\varepsilon_1`$ | $`\vartheta_0(\Omega + 1)`$ |
| BHO | $`\vartheta^{\mathrm{BHO}}(\Omega^2)`$ | $`\Gamma_{\mathrm{BHO}+1}`$ | $`\vartheta_0(\Omega^2 + \mathrm{BHO})`$ |
| $`\Gamma_{\mathrm{BHO}+1}`$ | $`\vartheta^{\Gamma_{\mathrm{BHO}+1}}(\Omega)`$ | $`\varepsilon_{\Gamma_{\mathrm{BHO}+1}+1}`$ | $`\vartheta_0(\Omega + \Gamma_{\mathrm{BHO}+1})`$ |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(0)`$ | $`\upsilon_1`$ | 無い |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(1)`$ | $`\upsilon_1 \cdot \omega`$ | 無い |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(\Omega)`$ | $`\varepsilon_{\upsilon_1+1}`$ | 無い |
| $`\upsilon_1`$ | $`\vartheta^{\upsilon_1}(\Omega^2)`$ | $`\Gamma_{\upsilon_1+1}`$ | 無い |
| $`\upsilon_1`$ | 上限 $`\sup_n \vartheta^{\upsilon_1}(\vartheta_1(\cdots \vartheta_n(0) \cdots))`$ | $`\upsilon_2`$ | 無い |

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
