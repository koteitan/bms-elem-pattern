[← Back](README.md)

# υ の定義

前提: [01 ϑᵢ と T^τ の定義](01-theta.md)

## 1. 定義

$`\tau \in \mathrm{E}_1`$ について、$`\Omega_{\gt \tau}`$ を、$`\Omega_0 = \tau`$ としたときの $`\Omega_1`$ とする。$`\tau`$ が可算なら $`\Omega_{\gt \tau} = \aleph_1`$ である。

**定義（Wilken 2021 の定義 1.5）.** 順序数の列 $`(\upsilon_\iota)_{\iota \in \mathrm{Ord}}`$ を次で定める。

```math
\upsilon_0 = 0, \qquad \upsilon_{\xi+1} = \upsilon_\xi^\infty = T^{\upsilon_\xi} \cap \Omega_{\gt \upsilon_\xi}, \qquad \upsilon_\lambda = \sup_{\iota \lt \lambda} \upsilon_\iota
```

最後の式の $`\lambda`$ は極限順序数である。$`\upsilon_0 = 0`$ は $`\mathrm{E}_1`$ に入らないので、$`T^0 = T^1`$ と約束する。

**読み方.**

- $`\upsilon_1 = 1^\infty`$ は、相対化しない表記系 $`T`$ で名前が付く可算順序数の全体である
- $`\upsilon_{\xi+1}`$ は、次の表記系 $`T^{\upsilon_\xi}`$ で名前が付く可算順序数の全体である
  - $`\upsilon_\xi`$ 未満の順序数は、すべて定数として使える
  - $`\vartheta_0`$ は $`\upsilon_\xi`$ から数え始める（$`\vartheta^{\upsilon_\xi}(0) = \upsilon_\xi`$）
- $`\upsilon_{\xi+1}`$ 自身は $`T^{\upsilon_\xi}`$ で名前が付かない。そこで次の段では、$`\upsilon_{\xi+1}`$ 未満をすべて定数にして、同じことをくり返す

## 2. 基本性質

次の 1〜5 は、定義と [01](01-theta.md) の性質から出る。論文にそのままの形では書かれていない。

**1. 狭義増加.** $`\tau \lt \tau^\infty`$ である。$`\tau = 1`$ なら $`\omega = \vartheta_0(1) \in T \cap \Omega`$ から。$`\tau \in \mathrm{E}`$ なら、[01](01-theta.md) §5 (2) から $`\vartheta^\tau(1) = \bar\omega^\tau = \omega^{\tau+1} = \tau \cdot \omega`$ で、これが $`\tau^\infty`$ 未満にあるから。

**2. 連続.** 定義から、極限では上限を取る。

**3. ε 数.** $`\xi \ge 1`$ なら $`\upsilon_\xi \in \mathrm{E}`$ である。

- 後続の段 $`\tau^\infty`$：$`\eta \lt \tau^\infty`$ なら $`\vartheta^\tau(\Omega + \eta)`$ も $`\tau^\infty`$ 未満にあり、[01](01-theta.md) §5 (4)(5) から $`\eta`$ より大きい ε 数である。よって $`\tau^\infty`$ は ε 数の上限なので、ε 数
- 極限の段：ε 数の上限なので、ε 数

したがって、どの段でも $`T^{\upsilon_\xi}`$ の定義に必要な $`\upsilon_\xi \in \mathrm{E}_1`$ が成り立つ。

**4. 可算.** $`\xi \lt \omega_1`$ なら $`\upsilon_\xi \lt \omega_1`$ である。$`\tau`$ が可算なら、$`T^\tau`$ は可算個の定数から可算個の関数で作るので可算集合で、$`\tau^\infty = T^\tau \cap \Omega_1`$ は可算順序数になる。極限の段は、可算個の可算順序数の上限である。

**5. 列の上限.** $`\upsilon_{\omega_1} = \omega_1`$ である。長さ $`\omega_1`$ の狭義増加列で、各項が可算だからである。

**6. 最初の値（1 節）.** 次が成り立つ。

```math
\upsilon_1 = 1^\infty = \lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert = \lvert \mathrm{KP}\ell_0 \rvert = \lvert \mathrm{ID}_{\lt\omega} \rvert = \psi_0(\Omega_\omega)
```

右端は Buchholz の $`\psi`$ である。$`\upsilon_2`$ 以降を Buchholz の $`\psi`$ で書いた式は、Wilken の論文には無く、ここでも確かめていない。

**Ωᵢ との違い.** 添字の意味が違う。

- $`\Omega_\iota`$ の添字は、非可算正則基数の番号である
- $`\upsilon_\iota`$ の添字は、「定数を増やして可算部分を取る」操作を何回くり返したかである

たとえば、4 と 5 から次が成り立つ。

```math
\upsilon_{\omega^2+2} \lt \omega_1 = \Omega_1 \lt \Omega_{\omega^2+2}
```

## 3. R₂ での役割

$`\mathcal{R}_2 = (\mathrm{Ord}; \le, \le_1, \le_2)`$ とする。添字の集合を次で置く。

```math
I = \{\iota \in \mathrm{Ord} : \iota \gt 1 \wedge \forall \lambda \in \mathrm{Lim}\ (\iota \ne \lambda + 1)\}
```

$`\mathrm{Lim}`$ は極限順序数の全体である。$`\iota \mathbin{\dot{-}} 1`$ は、$`\iota = \iota_0 + 1`$ なら $`\iota_0`$、そうでなければ $`\iota`$ とする。

**定理（Wilken 2021 の定理 1.8）.**

1. $`(\upsilon_\iota)_{\iota \gt 0}`$ は $`\lt_1`$ 鎖である。$`(\upsilon_\iota)_{\iota \in I}`$ は極大の $`\lt_2`$ 鎖で、どの $`\iota`$ についても、$`\upsilon_\iota`$ の $`\lt_2`$-前者の全体は $`(\upsilon_\xi)_{\xi \in I \cap \iota}`$ である
2. $`\iota \notin I`$（$`\iota \gt 0`$）なら、$`\upsilon_\iota`$ は $`\lt_2`$-後者を持たない。また $`\upsilon_{\iota \mathbin{\dot{-}} 1} \lt \alpha \lt \upsilon_\iota`$ で $`\alpha \lt_1 \upsilon_\iota`$ となる $`\alpha`$ は無い
3. $`\iota \in I`$ なら、$`\upsilon_\iota`$ は、$`\upsilon_\iota`$ より大きい $`\upsilon_{\iota \mathbin{\dot{-}} 1}`$ の倍数すべての $`\lt_2`$-前者である
4. $`\lambda`$ が極限のとき、$`\upsilon_\lambda`$ の形の順序数の全体は、長さが極限の $`\lt_2`$ 鎖の上限の全体である

**例（定理 1.8 の後の説明）.** 最小の $`\lt_2`$-後者は次のとおり。$`\lambda`$ は極限順序数である。

| 順序数 | 最小の $`\lt_2`$-後者 |
|---|---|
| $`\upsilon_1`$ | 無い |
| $`\upsilon_2`$ | $`\upsilon_2 + \upsilon_1`$ |
| $`\upsilon_3`$ | $`\upsilon_3 + \upsilon_2`$ |
| $`\upsilon_\lambda`$ | $`\upsilon_\lambda \cdot 2`$ |
| $`\upsilon_{\lambda+1}`$ | 無い |
| $`\upsilon_{\lambda+2}`$ | $`\upsilon_{\lambda+2} + \upsilon_{\lambda+1}`$ |

ほかに次が分かっている。

- $`\upsilon_1`$ は $`\le_1`$-最小である。つまり $`\alpha \lt_1 \upsilon_1`$ となる $`\alpha`$ は無い
- $`\upsilon_{\lambda+1}`$ の最大の $`\lt_1`$-前者は $`\upsilon_\lambda`$ である
- $`\upsilon_\omega`$ は、$`\mathcal{R}_2`$ の最初の無限 $`\lt_2`$ 鎖の上限である（2021 の 3 節）。また、自分の $`\lt_2`$-前者の真の上限になっている最小の順序数である（arXiv 版 v1 の 4 節）
- $`\mathcal{R}_2`$ のコア（すべての有限パターンの各点最小の実現の和集合）は $`\upsilon_1`$ である

## 4. R₃ での役割

$`\mathcal{R}_3 = (\mathrm{Ord}; \le, \le_1, \le_2, \le_3)`$ とする。次は Wilken, "Pure Σ2-elementarity beyond the core" の arXiv 版 v1 の 4 節にある。

1. 始切片 $`\upsilon_{\omega^2+2}`$ の上で、$`\mathcal{R}_2`$ と $`\mathcal{R}_3`$ の $`\le_1`$、$`\le_2`$ は一致する
2. $`\alpha \lt_3 \beta`$ なら、$`\alpha`$ は自分の $`\lt_2`$-前者の真の上限である（補題 4.2）
3. $`\mathcal{R}_3`$ で最小の $`\lt_3`$ の組は、次である（定理 4.3）

```math
\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2+2}
```

この組は、3 行の BMS の $`(0,0,0)(1,1,1)`$ のラベルに使える（[pss 08](../proof/pss/08-termination.md) §6）。

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021) 103001. https://doi.org/10.1016/j.apal.2021.103001 （定義 1.5、定理 1.8、2 節、3 節）
- G. Wilken, Pure Σ2-Elementarity beyond the Core, arXiv 版 v1. https://arxiv.org/abs/1710.01870v1 （4 節）
- T. J. Carlson and G. Wilken, Tracking chains of Σ2-elementarity, Annals of Pure and Applied Logic 163 (2012) 23–67. https://doi.org/10.1016/j.apal.2011.08.003
