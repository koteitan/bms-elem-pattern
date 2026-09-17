[← Back](README.md)

# ϑᵢ と υ の計算例

前提: [01 ϑᵢ と T^τ の定義](01-theta.md)、[02 υ の定義](02-upsilon.md)

特に書かない限り $`\tau = 1`$ とする。$`\Omega = \Omega_1`$ である。「(2)」「(5)」などは [01](01-theta.md) §5 の番号である。

## 1. ω̄ の値

$`\bar\omega^\xi`$ は、ε 数でない加法的主要数の $`\xi`$ 番目である（[01](01-theta.md) §1）。

| $`\xi`$ | $`\bar\omega^\xi`$ |
|---|---|
| $`0`$ | $`1`$ |
| $`1`$ | $`\omega`$ |
| $`2`$ | $`\omega^2`$ |
| $`\omega`$ | $`\omega^\omega`$ |
| $`\varepsilon_0`$ | $`\omega^{\varepsilon_0+1} = \varepsilon_0 \cdot \omega`$ |
| $`\varepsilon_0 + 1`$ | $`\omega^{\varepsilon_0+2} = \varepsilon_0 \cdot \omega^2`$ |
| $`\varepsilon_0 + \omega`$ | $`\omega^{\varepsilon_0+\omega}`$ |
| $`\Omega`$ | $`\omega^{\Omega+1} = \Omega \cdot \omega`$ |
| $`\Omega \cdot 2`$ | $`\omega^{\Omega \cdot 2} = \Omega^2`$ |

$`\xi = \varepsilon_0`$ のとき：$`\omega^0, \omega^1, \dots`$ と数えると、$`\varepsilon_0`$ 番目の候補 $`\omega^{\varepsilon_0} = \varepsilon_0`$ は ε 数なので飛ばす。次の $`\omega^{\varepsilon_0+1}`$ が $`\varepsilon_0`$ 番目になる。

## 2. ϑ₀ の値（Δ = 0）

(2) から $`\vartheta_0(0) = \Omega_0 = 1`$、$`\vartheta_0(1 + \alpha) = \bar\omega^{1+\alpha}`$ である。

| 引数 | 計算 | 値 |
|---|---|---|
| $`0`$ | $`\Omega_0`$ | $`1`$ |
| $`1`$ | $`\bar\omega^1`$ | $`\omega`$ |
| $`2`$ | $`\bar\omega^2`$ | $`\omega^2`$ |
| $`\omega`$ | $`\bar\omega^{1+\omega} = \bar\omega^\omega`$ | $`\omega^\omega`$ |
| $`\varepsilon_0`$ | $`\bar\omega^{\varepsilon_0}`$ | $`\varepsilon_0 \cdot \omega`$ |
| $`\varepsilon_0 + 1`$ | $`\bar\omega^{\varepsilon_0+1}`$ | $`\varepsilon_0 \cdot \omega^2`$ |

**定義から ϑ₀(ε₀) を確かめる.** $`n = 2`$ の定義 2.1 で、$`C = C^2_0(\varepsilon_0, \xi)`$ を考える。$`\varepsilon_0 \lt \theta^2_1`$ なので、補題 2.15 から $`\vartheta_0(\varepsilon_0) = \vartheta^2_0(\varepsilon_0)`$ である。

1. $`\vartheta_1`$ の値と、それを含む和は $`\Omega`$ 以上である。$`\vartheta_0`$ の引数は $`\varepsilon_0`$ 未満に限るので、これらは $`\vartheta_0`$ に入らない。よって $`C \cap \Omega`$ は、$`\xi`$ と $`0`$ から、足し算と、$`\eta \lt \varepsilon_0`$ についての $`\eta \mapsto \vartheta_0(\eta)`$ で作れるものの全体である
2. $`\eta \lt \varepsilon_0`$ なら $`\vartheta_0(\eta) \lt \varepsilon_0`$ である。よって $`\xi \le \varepsilon_0`$ なら $`\varepsilon_0 \notin C`$ で、条件「$`\alpha = \varepsilon_0 \in C`$」を満たさない。したがって $`\xi \gt \varepsilon_0`$
3. $`\xi \gt \varepsilon_0`$ で $`C \cap \Omega \subseteq \xi`$ なら、$`\varepsilon_0 \cdot k \lt \xi`$ がすべての $`k`$ で成り立つので、$`\xi \ge \varepsilon_0 \cdot \omega`$
4. $`\xi = \varepsilon_0 \cdot \omega`$ は足し算と $`\eta \mapsto \vartheta_0(\eta)`$（$`\eta \lt \varepsilon_0`$）で閉じているので、条件を満たす

よって $`\vartheta_0(\varepsilon_0) = \varepsilon_0 \cdot \omega`$。$`\square`$

**注意.** $`\varepsilon_0 \cdot \omega`$ は、$`\mathcal{R}_2`$ で $`\lt_2`$-後者を持つ最小の順序数である（Wilken 2021 の 3 節）。

## 3. ϑ₁、ϑ₂ の値

(2) から $`\vartheta_1(0) = \Omega`$、$`\alpha \lt \Omega_2`$ について $`\vartheta_1(1 + \alpha) = \bar\omega^{\Omega+\alpha}`$、$`\vartheta_2(0) = \Omega_2`$ である。

次の表は、値の順ではなく、引数の順に並べてある。

| 項 | 計算 | 値 |
|---|---|---|
| $`\vartheta_1(0)`$ | $`\Omega_1`$ | $`\Omega`$ |
| $`\vartheta_1(1)`$ | $`\bar\omega^\Omega`$ | $`\Omega \cdot \omega`$ |
| $`\vartheta_1(2)`$ | $`\bar\omega^{\Omega+1}`$ | $`\Omega \cdot \omega^2`$ |
| $`\vartheta_1(\omega)`$ | $`\bar\omega^{\Omega+\omega}`$ | $`\Omega \cdot \omega^\omega`$ |
| $`\vartheta_1(\Omega)`$ | $`\bar\omega^{\Omega+\Omega}`$ | $`\Omega^2`$ |
| $`\vartheta_1(\Omega \cdot \omega)`$ | $`\bar\omega^{\Omega+\Omega \cdot \omega} = \bar\omega^{\Omega \cdot \omega}`$ | $`\Omega^\omega`$ |
| $`\vartheta_1(\Omega^2)`$ | $`\bar\omega^{\Omega+\Omega^2} = \bar\omega^{\Omega^2}`$ | $`\Omega^\Omega`$ |
| $`\vartheta_2(0)`$ | $`\Omega_2`$ | $`\Omega_2`$ |
| $`\vartheta_1(\Omega_2)`$ | (4)(5)(6) | $`\varepsilon_{\Omega+1}`$ |

- $`\Omega`$ は ε 数なので、$`\bar\omega^\Omega = \omega^{\Omega+1} = \Omega \cdot \omega`$
- $`\Omega^2 = \omega^\Omega \cdot \omega^\Omega = \omega^{\Omega \cdot 2}`$、$`\Omega^\omega = \omega^{\Omega \cdot \omega}`$、$`\Omega^\Omega = \omega^{\Omega^2}`$
- 最後の行：(6) から $`\vartheta_1 = \vartheta^{\Omega_1}`$。引数 $`\Omega_2`$ は段 $`\Omega_2`$ の最初なので、(4)(5) から値は $`\Omega_1`$ より大きい最小の ε 数 $`\varepsilon_{\Omega+1}`$

項で書くと、$`\Omega \cdot \omega = \vartheta_1(1)`$、$`\Omega^2 = \vartheta_1(\vartheta_1(0))`$、$`\Omega^\omega = \vartheta_1(\vartheta_1(1))`$、$`\Omega^\Omega = \vartheta_1(\vartheta_1(\vartheta_1(0)))`$、$`\varepsilon_{\Omega+1} = \vartheta_1(\vartheta_2(0))`$ である。

## 4. ϑ₀ の値（Δ > 0）

### 4.1 ϑ₀(Ω) = ε₀

$`n = 2`$ の定義 2.1 で、$`C = C^2_0(\Omega, \xi)`$ を考える。$`\Omega \lt \theta^2_1`$ なので $`\vartheta_0(\Omega) = \vartheta^2_0(\Omega)`$ である。

1. $`0 \in \Omega_0 = \{0\}`$ なので $`0 \in C`$、$`\Omega = \vartheta_1(0) \in C`$。条件「$`\alpha = \Omega \in C`$」は、どの $`\xi`$ でも成り立つ
2. $`\vartheta_1`$ の値と、それを含む和は $`\Omega`$ 以上なので、$`\vartheta_0`$ の引数に使えない。よって $`C \cap \Omega`$ は、$`\xi`$ と $`0`$ から、足し算と $`\eta \mapsto \vartheta_0(\eta)`$（$`\eta \lt \Omega`$）で作れるものの全体である
3. §2 から $`\eta \lt \varepsilon_0`$ なら $`\vartheta_0(\eta) \lt \varepsilon_0`$。よって $`\xi = \varepsilon_0`$ なら $`C \cap \Omega = \varepsilon_0`$
4. $`\xi \lt \varepsilon_0`$ なら、$`C`$ は $`1, \omega, \omega^\omega, \omega^{\omega^\omega}, \dots`$ を含み、これは $`\varepsilon_0`$ で非有界なので $`C \cap \Omega \not\subseteq \xi`$

よって $`\vartheta_0(\Omega) = \varepsilon_0`$。$`\square`$

### 4.2 ϑ₀(Ω + 1) = ε₁

(5) で、$`\{\varepsilon_\alpha : \alpha \lt \varepsilon_\alpha\}`$ の 1 番目（0 番目は $`\varepsilon_0`$）なので $`\varepsilon_1`$ である。

定義からも確かめられる。$`C = C(\Omega + 1, \xi)`$ は $`\vartheta_0(\Omega) = \varepsilon_0`$ を含み、$`C \cap \Omega`$ は $`\varepsilon_0`$ から足し算と $`\bar\omega`$ で作れるものを含む。これは $`\varepsilon_0 \cdot \omega, \omega^{\varepsilon_0 \cdot \omega}, \dots`$ で、$`\varepsilon_1`$ で非有界。$`\xi = \varepsilon_1`$ で初めて閉じる。

### 4.3 ϑ₀(Ω + ε₀) = ε_{ε₀}

Wilken の例である。

1. $`\varepsilon_0 = \vartheta_0(\Omega) \in C`$ なので $`\Omega + \varepsilon_0 \in C`$
2. 引数が $`\Omega + \varepsilon_0`$ 未満の $`\vartheta_0`$ は、$`\eta \mapsto \bar\omega^\eta`$ と、$`\eta \lt \varepsilon_0`$ についての $`\vartheta_0(\Omega + \eta) = \varepsilon_\eta`$ である（(5)。$`\zeta_0`$ 未満に ε の不動点は無い）
3. $`0`$ からこれらで作れるものの全体は $`\varepsilon_{\varepsilon_0}`$ である

§2 の $`\vartheta_0(\varepsilon_0) = \varepsilon_0 \cdot \omega`$ と比べると、引数に $`\Omega`$ があるかどうかで値の大きさがまったく違う。

### 4.4 ϑ₀(Ω·2) = φ(2, 0) = ζ₀

Wilken の例である。

1. $`\Omega \cdot 2 = \Omega + \Omega \in C`$
2. 引数が $`\Omega \cdot 2`$ 未満の $`\vartheta_0`$ は、$`\eta \mapsto \bar\omega^\eta`$ と $`\eta \mapsto \vartheta_0(\Omega + \eta)`$ である。後者は、$`\zeta_0`$ 未満では $`\varepsilon_\eta`$ である
3. $`0`$ から、足し算、$`\bar\omega`$、$`\eta \mapsto \varepsilon_\eta`$ で作れるものの全体は $`\varphi(2, 0) = \zeta_0`$ である

### 4.5 ϑ₀(Ω·3) = φ(3, 0)、ϑ₀(Ω·ω) = φ(ω, 0)（概略）

Wilken の論文には書かれていない。(8) を使った概略である。

1. $`\eta \lt \varphi(3, 0)`$ について $`\vartheta_0(\Omega \cdot 2 + \eta) = \varphi(2, \eta)`$ を、$`\eta`$ についての帰納法で示す
   - (8) の $`\theta`$ は、$`\eta \mapsto \bar\omega^\eta`$ と $`\eta \mapsto \varepsilon_\eta`$ で閉じているので、ε の不動点（$`\varphi(2, \cdot)`$ の値）である
   - $`\nu \lt \eta`$ について $`\varphi(2, \nu) = \vartheta_0(\Omega \cdot 2 + \nu) \lt \theta`$ である
   - これらを満たす最小のものは $`\varphi(2, \eta)`$ で、$`\eta \lt \varphi(3, 0)`$ なので $`\eta \lt \varphi(2, \eta)`$ も成り立つ
2. $`\vartheta_0(\Omega \cdot 3)`$ は、$`0`$ から足し算、$`\bar\omega`$、$`\varphi(1, \cdot)`$、$`\varphi(2, \cdot)`$ で作れるものの全体なので $`\varphi(3, 0)`$
3. 同じように $`\vartheta_0(\Omega \cdot k + \eta) = \varphi(k, \eta)`$（$`1 \le k \lt \omega`$、$`\eta \lt \varphi(k+1, 0)`$）で、$`\vartheta_0(\Omega \cdot \omega) = \varphi(\omega, 0)`$

### 4.6 ϑ₀(Ω²) = Γ₀、ϑ₀(Ω^ω)、ϑ₀(Ω^Ω)

$`\vartheta_0(\Omega^2) = \Gamma_0`$ は Wilken の例である。残りの 2 つは Wilken の論文には書かれていない。概略を書く。

- $`\Omega^2`$ 未満の引数は $`\Omega \cdot \alpha + \eta`$（$`\alpha, \eta \lt \Omega`$）の形である。$`\vartheta_0(\Omega \cdot \alpha + \eta)`$ は 2 変数の Veblen 関数 $`\varphi(\alpha, \eta)`$ の役をする。$`0`$ からこれで作れるものの全体は $`\Gamma_0`$
- $`\Omega^\omega`$ 未満の引数は $`\Omega^k \cdot \alpha_k + \cdots + \Omega \cdot \alpha_1 + \alpha_0`$ の形で、有限変数の Veblen 関数 $`\varphi(\alpha_k, \dots, \alpha_1, \alpha_0)`$ の役をする。作れるものの全体は小 Veblen 順序数（SVO）
- $`\Omega^\Omega`$ 未満の引数は、$`\Omega^\gamma`$（$`\gamma \lt \Omega`$）を位置の番号とする、0 でない成分が有限個の超限変数 Veblen 関数の役をする。作れるものの全体は大 Veblen 順序数（LVO）

### 4.7 ϑ₀(ε_{Ω+1}) = BHO と ID_n

Wilken の例である。

```math
\vartheta_0(\varepsilon_{\Omega+1}) = \vartheta_0(\vartheta_1(\vartheta_2(0))) = \mathrm{BHO}
```

```math
\lvert \mathrm{ID}_n \rvert = \vartheta_0(\vartheta_1(\cdots \vartheta_{n+1}(0) \cdots)) \qquad (0 \lt n \lt \omega)
```

BHO は Bachmann–Howard 順序数、$`\mathrm{ID}_n`$ は $`n`$ 回くり返した帰納的定義の理論である。

## 5. 相対化した ϑ^τ

### 5.1 τ = ε₀

$`\Omega_0 = \varepsilon_0`$ なので、$`\varepsilon_0`$ 未満の順序数はすべて定数になる。

| 項 | 計算 | 値 | $`T`$ での項 |
|---|---|---|---|
| $`\vartheta^{\varepsilon_0}(0)`$ | $`\Omega_0`$ | $`\varepsilon_0`$ | $`\vartheta_0(\Omega)`$ |
| $`\vartheta^{\varepsilon_0}(1)`$ | $`\bar\omega^{\varepsilon_0}`$ | $`\varepsilon_0 \cdot \omega`$ | $`\vartheta_0(\varepsilon_0)`$ |
| $`\vartheta^{\varepsilon_0}(2)`$ | $`\bar\omega^{\varepsilon_0+1}`$ | $`\varepsilon_0 \cdot \omega^2`$ | $`\vartheta_0(\varepsilon_0 + 1)`$ |
| $`\vartheta^{\varepsilon_0}(\Omega)`$ | (5) | $`\varepsilon_1`$ | $`\vartheta_0(\Omega + 1)`$ |

(5) の行：$`\{\varepsilon_\alpha : \varepsilon_0 \lt \varepsilon_\alpha,\ \alpha \lt \varepsilon_\alpha\}`$ の最小の元は $`\varepsilon_1`$ である。

同じ順序数に、$`T^{\varepsilon_0}`$ の項と $`T`$ の項の両方がある。

### 5.2 τ = BHO（Wilken の例）

Wilken 2021 の定義 2.32 の後の例である。

```math
\alpha = \mathrm{BHO} = \vartheta_0(\vartheta_1(\vartheta_2(0)))
```

```math
\beta = \Gamma_{\alpha+1} = \vartheta^\alpha(\Omega^2) = \vartheta_0(\Omega^2 + \alpha)
```

```math
\gamma = \varepsilon_{\beta+1} = \vartheta^\beta(\Omega) = \vartheta_0(\Omega + \beta)
```

- $`\beta`$ は、$`\alpha`$ より大きい最小の Γ 数である。$`\Gamma_\alpha = \alpha`$ なので $`\Gamma_{\alpha+1}`$ になる
- $`\gamma`$ は、$`\beta`$ より大きい最小の ε 数である

## 6. υ の計算

### 6.1 υ₁

[01](01-theta.md) の定理 2.18 から、$`\upsilon_1 = 1^\infty = \sup_n \vartheta_0(\vartheta_1(\cdots \vartheta_n(0) \cdots))`$ である。

| $`n`$ | 項 | 値 |
|---|---|---|
| $`0`$ | $`\vartheta_0(0)`$ | $`1`$ |
| $`1`$ | $`\vartheta_0(\vartheta_1(0)) = \vartheta_0(\Omega)`$ | $`\varepsilon_0`$ |
| $`2`$ | $`\vartheta_0(\vartheta_1(\vartheta_2(0))) = \vartheta_0(\varepsilon_{\Omega+1})`$ | $`\mathrm{BHO}`$ |
| $`3`$ | $`\vartheta_0(\vartheta_1(\vartheta_2(\vartheta_3(0))))`$ | $`\lvert \mathrm{ID}_2 \rvert`$ |
| $`n \ge 2`$ | $`\vartheta_0(\vartheta_1(\cdots \vartheta_n(0) \cdots))`$ | $`\lvert \mathrm{ID}_{n-1} \rvert`$ |

上限は $`\upsilon_1 = \lvert \Pi^1_1\text{-}\mathrm{CA}_0 \rvert = \psi_0(\Omega_\omega)`$ である。

$`T \cap \Omega = \upsilon_1`$ なので、$`\upsilon_1`$ 以上の可算順序数は $`T`$ に項を持たない。

### 6.2 υ₂

$`\tau = \upsilon_1`$ とする。[02](02-upsilon.md) §2 の 3 から $`\upsilon_1 \in \mathrm{E}`$ である。

| 項 | 値 | 理由 |
|---|---|---|
| $`\vartheta^{\upsilon_1}(0)`$ | $`\upsilon_1`$ | (2) |
| $`\vartheta^{\upsilon_1}(1)`$ | $`\upsilon_1 \cdot \omega`$ | (2) |
| $`\vartheta^{\upsilon_1}(2)`$ | $`\upsilon_1 \cdot \omega^2`$ | (2) |
| $`\vartheta^{\upsilon_1}(\Omega)`$ | $`\varepsilon_{\upsilon_1+1}`$ | (5) |
| $`\vartheta^{\upsilon_1}(\Omega^2)`$ | $`\Gamma_{\upsilon_1+1}`$ | §5.2 と同じ |
| $`\vartheta^{\upsilon_1}(\varepsilon_{\Omega+1})`$ | Bachmann–Howard 順序数を $`\upsilon_1`$ の上で作り直したもの | 名前は無い |

- (5) の行：$`\varepsilon_{\upsilon_1} = \upsilon_1`$ は $`\upsilon_1`$ より大きくないので、最小の元は $`\varepsilon_{\upsilon_1+1}`$
- $`\Omega^2`$ の行：$`\upsilon_1`$ は $`\eta \mapsto \vartheta_0(\Omega^2 + \eta)`$ で閉じているので、$`\Gamma_{\upsilon_1} = \upsilon_1`$。よって $`\upsilon_1`$ より大きい最小の Γ 数は $`\Gamma_{\upsilon_1+1}`$

これらはどれも $`\upsilon_1`$ 以上なので、$`T`$ の項を持たない（§6.1）。

$`\upsilon_2`$ は次の上限である。

```math
\upsilon_2 = \sup_n \vartheta^{\upsilon_1}(\vartheta_1(\cdots \vartheta_n(0) \cdots)) = \sup\{\upsilon_1,\ \varepsilon_{\upsilon_1+1},\ \vartheta^{\upsilon_1}(\varepsilon_{\Omega+1}),\ \dots\}
```

$`\mathcal{R}_2`$ では $`\upsilon_1 \lt_1 \upsilon_2`$ で、$`\upsilon_2`$ の最小の $`\lt_2`$-後者は $`\upsilon_2 + \upsilon_1`$ である（[02](02-upsilon.md) §3）。

### 6.3 υ_ω と υ_{ω+1}

```math
\upsilon_\omega = \sup_{n \lt \omega} \upsilon_n, \qquad \upsilon_{\omega+1} = T^{\upsilon_\omega} \cap \Omega, \qquad \vartheta^{\upsilon_\omega}(0) = \upsilon_\omega
```

$`\mathcal{R}_2`$ では次が成り立つ（[02](02-upsilon.md) §3）。

- $`\upsilon_2 \lt_2 \upsilon_3 \lt_2 \cdots \lt_2 \upsilon_\omega \lt_2 \upsilon_{\omega+1}`$
- $`\upsilon_\omega`$ の最小の $`\lt_2`$-後者は $`\upsilon_\omega \cdot 2`$
- $`\upsilon_{\omega+1}`$ は $`\lt_2`$-後者を持たない。最大の $`\lt_1`$-前者は $`\upsilon_\omega`$

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021) 103001. https://doi.org/10.1016/j.apal.2021.103001 （1 節の例、定義 2.32 の後の例、3 節）
- G. Wilken, Pure Σ2-Elementarity beyond the Core, arXiv 版 v1. https://arxiv.org/abs/1710.01870v1
