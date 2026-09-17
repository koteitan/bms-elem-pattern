[← Back](../README.md)

# Wilken の順序数表記：ϑᵢ、T^τ、υ

Wilken は、$`\mathcal{R}_2`$ と $`\mathcal{R}_3`$ の関係 $`\le_1, \le_2, \le_3`$ を、順序数表記 $`T^\tau`$ と、つぶし関数 $`\vartheta_i`$ と、それをくり返して作る列 $`\upsilon_\iota`$ で書いている。
このフォルダは、その定義、小さい計算例、ほかの表記との対応表をまとめたものである。停止性の証明（[proof/](../proof/)）には使っていない。

## ノート

| ノート | 内容 |
|---|---|
| [01 ϑᵢ と T^τ の定義](01-theta.md) | 有限の段での定義、極限、基本性質 |
| [02 υ の定義](02-upsilon.md) | 定義、基本性質、R₂ と R₃ での役割 |
| [03 ϑᵢ と υ の計算例](03-examples.md) | ϑ₀、ϑ₁ の値、相対化、υ₁、υ₂ |
| [04 ϑᵢ と υ の対応表](04-table.md) | Veblen 関数、Buchholz の ψ、R₂ と R₃ での意味 |

## 要点

$`\tau \in \mathrm{E} \cup \{1\}`$ とし、$`\Omega_0 = \tau`$、$`\Omega_1, \Omega_2, \dots`$ を非可算正則基数とする。

$`T^\tau`$ は次を満たす最小の集合である。$`\vartheta^\tau = \vartheta_0`$ は $`\tau`$ に相対化した関数である。

```math
\tau \subseteq T^\tau, \qquad \xi, \eta \in T^\tau \Rightarrow \xi + \eta \in T^\tau, \qquad \xi \in T^\tau \cap \Omega_{i+2} \Rightarrow \vartheta_i(\xi) \in T^\tau
```

$`\vartheta_i(\alpha)`$ は、$`[\Omega_i, \Omega_{i+1})`$ の中で、次の 2 つを満たす最小の順序数である。「それ未満から、足し算と、上の段の関数と、引数が $`\alpha`$ 未満の $`\vartheta_i`$ で作っても、$`\Omega_{i+1}`$ 未満では越えられない」「$`\alpha`$ 自身は作れる」（[01](01-theta.md) §3）。

```math
\vartheta_i(0) = \Omega_i, \qquad \vartheta_i(1 + \alpha) = \bar\omega^{\Omega_i + \alpha} \quad (\alpha \lt \Omega_{i+1})
```

```math
\tau^\infty = T^\tau \cap \Omega_1 = \sup_{n \lt \omega} \vartheta_0(\vartheta_1(\cdots \vartheta_n(0) \cdots))
```

```math
\upsilon_0 = 0, \qquad \upsilon_{\xi+1} = \upsilon_\xi^\infty, \qquad \upsilon_\lambda = \sup_{\iota \lt \lambda} \upsilon_\iota
```

主な値：

| 項 | 値 |
|---|---|
| $`\vartheta_0(0)`$ | $`1`$ |
| $`\vartheta_0(1)`$ | $`\omega`$ |
| $`\vartheta_0(\varepsilon_0)`$ | $`\varepsilon_0 \cdot \omega`$ |
| $`\vartheta_0(\Omega)`$ | $`\varepsilon_0 = \psi_0(\Omega)`$ |
| $`\vartheta_0(\Omega \cdot 2)`$ | $`\zeta_0 = \psi_0(\Omega^2)`$ |
| $`\vartheta_0(\Omega^2)`$ | $`\Gamma_0 = \psi_0(\Omega^\Omega)`$ |
| $`\vartheta_0(\varepsilon_{\Omega+1})`$ | Bachmann–Howard 順序数 $`= \psi_0(\Omega_2)`$ |
| $`\upsilon_1`$ | $`\psi_0(\Omega_\omega)`$ |
| $`\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2+2}`$ | $`\mathcal{R}_3`$ で最小の $`\lt_3`$ の組 |

右の $`\psi_0`$ は Buchholz の $`\psi`$ である。

## 注意

- $`\upsilon_\iota`$ は、$`\iota \lt \omega_1`$ なら可算である。非可算基数 $`\Omega_\iota`$ とは違う（[02](02-upsilon.md) §2）
- $`\Omega^2 = \Omega \cdot \Omega`$ と $`\Omega_2`$ は違う
- Wilken の $`\vartheta_0`$ と Buchholz の $`\psi_0`$ は別の関数である。たとえば $`\vartheta_0(\Omega^2) = \Gamma_0`$ だが $`\psi_0(\Omega^2) = \zeta_0`$

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021) 103001. https://doi.org/10.1016/j.apal.2021.103001 , arXiv 版 https://arxiv.org/abs/1710.01870
- G. Wilken, Ordinal arithmetic based on Skolem hulling, Annals of Pure and Applied Logic 145 (2007) 130–161.
- T. J. Carlson and G. Wilken, Tracking chains of Σ2-elementarity, Annals of Pure and Applied Logic 163 (2012) 23–67. https://doi.org/10.1016/j.apal.2011.08.003
- G. Wilken, Tracking chains revisited. https://arxiv.org/abs/1611.04348
- W. Buchholz, A new system of proof-theoretic ordinal functions, Annals of Pure and Applied Logic 32 (1986) 195–207.
