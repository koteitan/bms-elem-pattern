[← Back](README.md) | [English](en/03-block-form.md) | [Japanese](03-block-form.md)

# 成分ごとの条件をブロックの形に書く

前提: [pss 02 構造と初等部分構造](../pss/02-elementary-substructure.md) §5、[02 論理式 Φₘ](02-phi.md)

## 1. 何が要るか

数学では、$`\Phi_m`$ が $`\Pi_m`$ 論理式であることは、量化子を数えれば分かる。Lean では論理式を構文にせず、ブロックの長さの列と原子図式の集合 $`D`$ で表す（[pss 02](../pss/02-elementary-substructure.md) §5）。

```math
\mathrm{Sig}_\gamma([b_1, \dots, b_r],\ \vec p) \iff \exists \vec x_1\ \neg\, \exists \vec x_2\ \neg \cdots \exists \vec x_r\ \neg\, \bigl(\mathrm{diag}(\vec p, \vec x_1, \dots, \vec x_r) \in D\bigr)
```

$`\le_j`$ は、この形でブロックが $`j`$ 個以下の論理式の一致として定義してある。したがって、使う文がこの形で書けて、ブロックの数が正しいことを、Lean では示す必要がある。

使う文は、$`s`$ 個の成分ごとに同じ形の条件を並べたものである。

```math
G(\vec v) \wedge \bigwedge_{i \lt s} \bigl(Q_i(\vec v) \vee \neg\, \Phi_d(v_{c+i})\bigr)
```

- $`G`$、$`Q_i`$ は量化子なしの条件
- $`G`$ は位置 $`c`$ 未満の成分だけ、$`Q_i`$ は位置 $`c + s`$ 未満の成分だけを見る
- $`\Phi_d`$ を当てる組 $`(v_c, \dots, v_{c+s-1})`$ は、位置 $`c`$ から $`c + s - 1`$ にある

問題は、$`i`$ ごとに別々の量化子が付くことである。ブロックの形では、1 つのブロックの量化子は全成分に共通でなければならない。

## 2. 成分ごとのスコーレム標準形

$`\gamma \gt 0`$ とし、量化子の範囲はすべて $`\gamma`$ 未満とする。

**補題.** 次の 2 つが成り立つ。

```math
\bigwedge_{i \lt s} \bigl(Q_i \vee \exists w\ P_i(w)\bigr) \iff \exists \vec W\ \bigwedge_{i \lt s} \bigl(Q_i \vee P_i(W_i)\bigr)
```

```math
\bigwedge_{i \lt s} \bigl(Q_i \vee \exists z\ \forall t\ P_i(z, t)\bigr) \iff \exists \vec Z\ \forall \vec S\ \bigwedge_{i \lt s} \bigl(Q_i \vee P_i(Z_i, S_i)\bigr)
```

**証明.**

- 左から右：$`Q_i`$ が成り立つ $`i`$ では $`W_i = 0`$（または $`Z_i = 0`$）、そうでない $`i`$ では証人を選ぶ。$`0 \lt \gamma`$ はここで使う
- 1 つめの右から左：$`W_i`$ が証人になる
- 2 つめの右から左：$`Q_i`$ が偽の $`i`$ と $`t \lt \gamma`$ を取る。$`\vec S`$ をすべての成分が $`t`$ の組にすると、$`i`$ 番目の連言から $`P_i(Z_i, t)`$。よって $`Z_i`$ が証人

2 つめの右から左では、$`i`$ 番目の連言が $`Z_i`$ と $`S_i`$ しか見ないことを使っている。$`\square`$

## 3. ブロックの形

**命題.** $`\gamma \gt 0`$、$`d \ge 0`$ とする。原子図式の集合 $`D_d`$ で、どの $`\vec v = (v_0, \dots, v_{c+s-1})`$ についても

```math
\mathrm{Sig}_\gamma\bigl([\underbrace{s, \dots, s}_{d}],\ \vec v\bigr) \iff G(\vec v) \wedge \bigwedge_{i \lt s} \bigl(Q_i(\vec v) \vee \neg\, \Phi_d(v_{c+i})\bigr)
```

となるものがある。右辺の $`\Phi_d`$ は $`\gamma`$ で評価する。

**証明.** $`d`$ についての帰納法。

**$`d = 0`$ のとき.** $`\Phi_0`$ は真なので、右辺は $`G \wedge \bigwedge_i Q_i`$ で、量化子なし。これを $`D_0`$ にする。

**$`d = 1`$ のとき.** 

```math
\neg\, \Phi_1(u) \iff \exists w\ \bigl(u \le w \wedge \neg\, u \le_1 w\bigr)
```

§2 の 1 つめで $`\exists \vec W`$ を前に出すと、中身は量化子なしになる。

**$`d = 2`$ のとき.**

```math
\neg\, \Phi_2(u) \iff \exists z\ \forall t\ \neg\, \bigl(z \lt t \wedge u \le_2 t\bigr)
```

§2 の 2 つめで $`\exists \vec Z\ \forall \vec S`$ を前に出すと、中身は量化子なしになる。

**$`d + 2`$ のとき（$`d \ge 1`$）.**

```math
\neg\, \Phi_{d+2}(u) \iff \exists z\ \forall t\ \Bigl(\neg\, \bigl(z \lt t \wedge u \le_{d+2} t\bigr) \vee \neg\, \Phi_d(t)\Bigr)
```

§2 の 2 つめで $`\exists \vec Z\ \forall \vec S`$ を前に出すと、中身は次になる。

```math
G \wedge \bigwedge_{i \lt s} \bigl(Q'_i \vee \neg\, \Phi_d(S_i)\bigr), \qquad Q'_i = Q_i \vee \neg\, \bigl(Z_i \lt S_i \wedge v_{c+i} \le_{d+2} S_i\bigr)
```

これは列 $`(\vec v, \vec Z, \vec S)`$ についての同じ形の条件で、組 $`\vec S`$ は位置 $`c + 2s`$ から始まる。$`G`$ は位置 $`c`$ 未満、$`Q'_i`$ は位置 $`c + 3s`$ 未満だけを見る。帰納法の仮定から、ブロック $`[s, \dots, s]`$（$`d`$ 個）で書ける。前の 2 ブロックと合わせて $`d + 2`$ 個になる。

$`\square`$

## 4. 使う文

**(1) パラメータ $`z`$ を持つ文 $`\exists u\ (z \lt u \wedge \Phi_d(u))`$.** $`s = 1`$、$`c = 1`$、$`G = \top`$、$`Q_0 = (u \le z)`$ として §3 を使い、前に $`\exists u\ \neg`$ を付ける。

```math
\exists u\ \neg\, \bigl(u \le z \vee \neg\, \Phi_d(u)\bigr) \iff \exists u\ \bigl(z \lt u \wedge \Phi_d(u)\bigr)
```

ブロックは $`[1, 1, \dots, 1]`$（$`d + 1`$ 個）で、$`\Sigma_{d+1}`$ 文である。

**(2) パラメータ無しの文 $`\exists z\ \neg\, \exists u\ (z \lt u \wedge \Phi_d(u))`$.** (1) の前に $`\exists z\ \neg`$ を付ける。ブロックは $`d + 2`$ 個で、$`\Pi_{d+2}`$ 文 $`\forall z\ \exists u\ (z \lt u \wedge \Phi_d(u))`$ の否定である。

**(3) 有限反映の文.** [05](05-finite-reflection.md) の文 $`\sigma`$ は、組 $`\vec U`$、$`\vec V`$ を持つ次の形である。

```math
\exists \vec U\ \neg\, \exists \vec V\ \neg\, \Bigl(G \wedge \bigwedge_{i \lt s} \bigl(Q_i \vee \neg\, \Phi_{n-1}(V_i)\bigr)\Bigr)
```

§3 を $`d = n - 1`$ で使うと、ブロックは $`[s, s, \dots, s]`$（$`n + 1`$ 個）で、$`\Sigma_{n+1}`$ 文である。

## 5. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| (1)(2) | [04](04-cofinal-predecessors.md) の段階 B、E |
| (3) | [05](05-finite-reflection.md) |

## 6. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| 原子図式の上の条件 | `DP` | [`Pattern/General.lean`](../../lean/Pattern/General.lean) |
| 位置 $`B`$ 未満だけを見る | `Reads`, `Reads.diag_iff`, `Reads.mono`, `reads_gle`, `reads_glev` | 同上 |
| §2 | `skolem_one`, `skolem_two` | 同上 |
| §3 の $`D_d`$ | `tnMat` | 同上 |
| §3 の命題 | `tn_sig` | 同上 |
| §3 の否定の展開 | `not_phi_one`, `not_phi_two`, `not_phi_add_three` | 同上 |
| §4 (1)(2) | `exPhiMat`, `sig_exists_phi`, `sig_forall_exists_phi` | 同上 |
| §4 (3) | `reflect_gen` の中の `hsem` | 同上 |
