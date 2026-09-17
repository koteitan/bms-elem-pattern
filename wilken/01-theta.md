[← Back](README.md)

# ϑᵢ と T^τ の定義

出典は G. Wilken, "Pure Σ2-elementarity beyond the core" (2021) の 1 節と 2.1 節である。そこでは Wilken, "Ordinal arithmetic based on Skolem hulling" (2007) の 3 節の定義がまとめてある。以下の番号（定義 2.1 など）は 2021 年の論文のものである。

## 1. 記号

| 記号 | 意味 |
|---|---|
| $`\mathrm{P}`$ | 加法的主要数 $`\{\omega^\eta : \eta \in \mathrm{Ord}\}`$ |
| $`\mathrm{E}`$ | ε 数 $`\{\eta : \omega^\eta = \eta\}`$ |
| $`\mathrm{E}_1`$ | $`\mathrm{E} \cup \{1\}`$ |
| $`\mathrm{E}_{\gt \tau}`$ | $`\tau`$ より大きい ε 数 |
| $`\bar\omega^\xi`$ | ε 数でない加法的主要数を、小さい順に 0 番から数えたときの $`\xi`$ 番目 |

$`\bar\omega^\xi`$ は、数えると次のようになる。

- $`\xi = \varepsilon + k`$（$`\varepsilon \in \mathrm{E}`$、$`k \lt \omega`$）のとき、$`\bar\omega^\xi = \omega^{\xi+1}`$
- それ以外のとき、$`\bar\omega^\xi = \omega^\xi`$

たとえば $`\omega^{\varepsilon_0} = \varepsilon_0`$ は ε 数なので飛ばされ、$`\bar\omega^{\varepsilon_0} = \omega^{\varepsilon_0+1}`$ になる。
これは Wilken, "Tracking chains revisited" 2.4 節の式 (1) を $`\tau = 1`$ で読んだものと同じである。

順序数は、それより小さい順序数の集合とみなす。

## 2. 設定

$`\tau \in \mathrm{E}_1`$ を 1 つ固定する。$`\tau = 1`$ が相対化しない場合である。

- $`\Omega_0 = \tau`$
- $`\Omega_1`$ は、$`\mathrm{Card}(\tau)`$ と $`\aleph_0`$ より大きい最小の正則基数。$`\tau`$ が可算なら $`\Omega_1 = \aleph_1`$
- $`i \ge 1`$ について、$`\Omega_{i+1}`$ は $`\Omega_i`$ より大きい最小の正則基数

$`\Omega_0 = \tau`$ は集合としては $`\tau`$ 未満の順序数全体である。添字のない $`\Omega`$ は $`\Omega_1`$ を表す。

**注意.** $`\Omega^2 = \Omega \cdot \Omega`$ と $`\Omega_2`$ は違う。$`\Omega^2 \lt \Omega_2`$ である。

## 3. 有限の段 n での定義

段 $`m`$ の関数 $`\vartheta_m`$ を定義するには、それより上の段の関数 $`\vartheta_k`$（$`k \gt m`$）が先に要る。関数は無限個あるので、まず上限 $`n`$ を決めて上から順に定義し（この節）、あとで $`n \to \omega`$ の極限を取る（§4）。

**定義（定義 2.1）.** $`0 \lt n \lt \omega`$ とする。$`m = n-1, n-2, \dots, 0`$ の順に、$`\alpha \lt \Omega_{m+2}`$ についての再帰で、集合 $`C^n_m(\alpha, \beta)`$（$`\beta \lt \Omega_{m+1}`$）と順序数 $`\vartheta^n_m(\alpha)`$ を同時に定める。

$`C^n_m(\alpha, \beta)`$ は、次の 4 つを満たす最小の集合である。

1. $`\Omega_m \cup \beta \subseteq C^n_m(\alpha, \beta)`$
2. $`\xi, \eta \in C^n_m(\alpha, \beta) \Rightarrow \xi + \eta \in C^n_m(\alpha, \beta)`$
3. $`m \lt k \lt n`$ かつ $`\xi \in C^n_m(\alpha, \beta) \cap \Omega_{k+2}`$ $`\Rightarrow \vartheta^n_k(\xi) \in C^n_m(\alpha, \beta)`$
4. $`\xi \in C^n_m(\alpha, \beta) \cap \alpha \Rightarrow \vartheta^n_m(\xi) \in C^n_m(\alpha, \beta)`$

これを使って次のように置く。

```math
\vartheta^n_m(\alpha) = \min\bigl(\{\xi \lt \Omega_{m+1} : C^n_m(\alpha, \xi) \cap \Omega_{m+1} \subseteq \xi \wedge \alpha \in C^n_m(\alpha, \xi)\} \cup \{\Omega_{m+1}\}\bigr)
```

**読み方.**

- $`C^n_m(\alpha, \beta)`$ は、$`\Omega_m`$ 未満と $`\beta`$ 未満の順序数から、足し算、上の段の関数、引数が $`\alpha`$ 未満の $`\vartheta^n_m`$ で作れるもの全体である
- $`\vartheta^n_m(\alpha)`$ は、次の 2 つを満たす最小の $`\xi \lt \Omega_{m+1}`$ である
  - $`\xi`$ 未満から作っても、$`\Omega_{m+1}`$ 未満では $`\xi`$ を越えない
  - 引数 $`\alpha`$ 自身は作れる
- 3 の $`\vartheta^n_k`$（$`k \gt m`$）は、段の高い順に定義するので、すでに決まっている
- $`\vartheta^n_m(0) = \Omega_m`$ である

**定義（定義 2.5）.** $`m \lt n`$ について

```math
T^n_m = C^n_m(\Omega_{m+2}, 0) = \bigcup_{\alpha \lt \Omega_{m+2}} C^n_m(\alpha, 0)
```

と置く。

**定理（定理 2.13）.** $`m \lt n`$ のとき、$`T^n_m \cap \Omega_{m+1}`$ は順序数である。これを $`\theta^n_m`$ と書く。

## 4. n → ω の極限

**補題（補題 2.15）.** $`m \lt n`$、$`\alpha \lt \theta^n_{m+1}`$ なら $`\vartheta^n_m(\alpha) = \vartheta^{n+1}_m(\alpha)`$ である。また $`\theta^n_m \lt \theta^{n+1}_m`$ である。ここで $`\theta^n_n = \theta^n_{n-1}`$ と置く。

つまり、$`n`$ を大きくしても、すでに決まった値は変わらない。

**定義（定義 2.17）.** $`m \lt \omega`$ について次のように置く。

```math
\theta_m = \sup_{n \gt m} \theta^n_m
```

```math
\vartheta_m : \theta_{m+1} \to \Omega_{m+1}, \qquad \vartheta_m(\alpha) = \vartheta^n_m(\alpha)
```

右辺の $`n`$ は、$`\alpha \lt \theta^n_{m+1}`$ となるように大きく取る。補題 2.15 から、どの $`n`$ を取っても値は同じである。

$`T_m`$ は、次を満たす最小の集合である。

1. $`\Omega_m \subseteq T_m`$
2. $`\xi, \eta \in T_m \Rightarrow \xi + \eta \in T_m`$
3. $`k \ge m`$ かつ $`\xi \in T_m \cap \Omega_{k+2}`$ $`\Rightarrow \vartheta_k(\xi) \in T_m`$

**定義（規約 2.20、定義 1.3）.**

```math
T^\tau = T_0, \qquad \vartheta^\tau = \vartheta_0, \qquad \tau^\infty = T^\tau \cap \Omega_1
```

$`\tau = 1`$ のときは上付きの $`\tau`$ を省き、$`T`$、$`\vartheta_0`$ と書く。

まとめると、$`T^\tau`$ は次を満たす最小の集合である。

```math
\tau \subseteq T^\tau, \qquad \xi, \eta \in T^\tau \Rightarrow \xi + \eta \in T^\tau, \qquad \xi \in T^\tau \cap \Omega_{i+2} \Rightarrow \vartheta_i(\xi) \in T^\tau \quad (i \lt \omega)
```

**定理（定理 2.18）.** $`T_m = \bigcup_{n \gt m} T^n_m`$ で、

```math
T_m \cap \Omega_{m+1} = \theta_m = \sup_{n \ge m} \vartheta_m(\vartheta_{m+1}(\cdots \vartheta_n(0) \cdots))
```

特に次が成り立つ。

```math
\tau^\infty = \sup_{n \lt \omega} \vartheta_0(\vartheta_1(\cdots \vartheta_n(0) \cdots))
```

## 5. 基本性質

**(1) 単射と値の範囲（補題 1.4、補題 2.26）.** $`\vartheta_m`$ を $`T^\tau \cap \Omega_{m+2}`$ に制限したものは単射で、値は $`\mathrm{P} \cap [\Omega_m, \Omega_{m+1})`$ に入る。

**(2) 小さい引数（補題 1.2）.** $`\vartheta_m(0) = \Omega_m`$ である。$`\alpha \lt \Omega_{m+1}`$ なら次が成り立つ。

```math
\vartheta_m(1 + \alpha) = \bar\omega^{\Omega_m + \alpha}
```

**(3) 引数の分け方（規約 2.28）.** $`\vartheta^\tau(\Delta + \eta)`$ と書いたら、$`\Delta`$ は $`\Omega_1`$ の倍数（0 でもよい）、$`\eta \lt \Omega_1`$ とする。Wilken は $`\Delta`$ を不動点の段と呼ぶ。

**(4) ε 数になる条件（補題 2.29）.** $`\alpha = \vartheta^\tau(\Delta + \eta) \in T^\tau`$ について、次が成り立つ。

```math
\alpha \in \mathrm{E}_{\gt \tau} \iff \Delta \gt 0
```

**(5) Ω の段（1 節の説明）.** $`\xi \lt \Omega`$ について、$`\xi \mapsto \vartheta^\tau(\Omega + \xi)`$ は次の集合を小さい順に並べたものである。

```math
\{\varepsilon_\alpha : \tau \lt \varepsilon_\alpha,\ \alpha \lt \varepsilon_\alpha \lt \Omega\}
```

$`\varepsilon_\alpha = \alpha`$ となる不動点は飛ばす。一般に、$`\Delta`$ が $`\Omega`$ の倍数で $`\xi \lt \Omega`$ なら $`\xi \lt \vartheta^\tau(\Delta + \xi)`$ である。

**(6) 上の段は相対化の一種（1 節）.** $`\vartheta_i = \vartheta^{\Omega_i}`$ である。右辺は、$`\Omega_i`$ に相対化した $`\vartheta_0`$ である。

**(7) 比較（定義 2.23、補題 2.26）.** $`\alpha \in T^\tau`$ の項の部分項のうち、次を満たすものの最大を $`\alpha^{*m}`$ と書く。無ければ $`0`$ とする。

- $`\vartheta_k`$（$`k \lt m`$）の内側にない
- $`[\Omega_m, \Omega_{m+1})`$ に入る加法的主要数である

$`\alpha, \gamma \in T^\tau \cap \Omega_{m+2}`$ について $`\alpha^{*m} \lt \vartheta_m(\alpha)`$ で、次が成り立つ。

```math
\vartheta_m(\alpha) \lt \vartheta_m(\gamma) \iff \bigl(\alpha \lt \gamma \wedge \alpha^{*m} \lt \vartheta_m(\gamma)\bigr) \vee \vartheta_m(\alpha) \le \gamma^{*m}
```

**(8) 値の言い換え（注意 2.27 の後）.** $`\vartheta^\tau(\xi)`$ は、次を満たす最小の $`\theta`$ である。

- $`\theta \gt \xi^{*0}`$
- $`\theta`$ は $`\tau`$ 未満の定数を含み、足し算で閉じている
- $`\zeta \lt \xi`$ かつ $`\zeta^{*0} \lt \theta`$ なら $`\vartheta^\tau(\zeta) \lt \theta`$

[03](03-examples.md) の計算は、主に (2)、(5)、(8) と定義 2.1 を使う。

## 出典

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021) 103001. https://doi.org/10.1016/j.apal.2021.103001 （1 節、2.1 節、2.2 節）
- G. Wilken, Ordinal arithmetic based on Skolem hulling, Annals of Pure and Applied Logic 145 (2007) 130–161.（3 節）
- G. Wilken, Tracking chains revisited. https://arxiv.org/abs/1611.04348 （2.4 節の式 (1)）
