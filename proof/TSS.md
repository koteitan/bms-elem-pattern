# Σ₃ 初等部分構造によるトリオ数列システムの停止性の証明

[ペア数列の証明](README.md) を 3 行に広げた。
ラベルの関係には $`\mathcal{R}_2`$ の代わりに $`\mathcal{R}_3 = (\mathrm{Ord}; \le, \le_1, \le_2, \le_3)`$ の関係を使う。
Lean では $`\mathcal{R}_N`$ を一般の $`N`$ で定義し、1〜3 行（原始数列、ペア数列、トリオ数列）を 1 つの定理で扱う。

## 結論

**定理（停止性）.** $`r \le 3`$ とし、$`A`$ を $`r`$ 行の標準列、$`n : \mathbb{N} \to \mathbb{N}`$ を任意の関数とする。

```math
A_0 = A, \qquad A_{t+1} = A_t[n(t)]
```

と置くと、ある $`T`$ で $`A_T`$ は空である。

**定理（整礎性）.** $`r \le 3`$ のとき、$`r`$ 行の標準列の上の関係

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

は整礎である。

Lean の証明に `sorry` は無く、公理は `propext` / `Classical.choice` / `Quot.sound` のみ。

## 1. 標準列

```math
S^r_n = \underbrace{(0,\dots,0)}_{r}\,\underbrace{(1,\dots,1)}_{r} \cdots \underbrace{(n,\dots,n)}_{r}
```

**定義.** $`r`$ 行の標準列とは、ある $`S^r_n`$ から展開を有限回して得られる $`r`$ 行の配列のことである。$`r = 3`$ がトリオ数列である。

展開規則は BM4 である。

## 2. R_N

```math
\alpha \le_j \beta \iff (\alpha; \le, \le_1, \dots, \le_N) \preceq_{\Sigma_j} (\beta; \le, \le_1, \dots, \le_N) \qquad (1 \le j \le N)
```

```math
\alpha \lt_j \beta \iff \alpha \lt \beta \wedge \alpha \le_j \beta
```

$`\le_1, \dots, \le_N`$ は、$`\beta`$ についての帰納法で同時に定義する。

Lean では、量化子のブロックの長さの列 $`[b_1, \dots, b_r]`$ と、原子図式の集合 $`D`$ で論理式を表す。

```math
\exists x^1_1 \cdots x^1_{b_1}\ \neg\, \exists x^2_1 \cdots x^2_{b_2}\ \neg \cdots \exists x^r_1 \cdots x^r_{b_r}\ \neg\, \bigl(\mathrm{diag}(\vec p, \vec x^1, \dots, \vec x^r) \in D\bigr)
```

ブロックが $`r`$ 個のものが $`\Sigma_r`$ 文である。$`\Sigma_j`$ 初等部分構造は、ブロックが $`j`$ 個以下の文すべてが一致することとして定義する。

## 3. ラベルの関係

```math
\lhd_0 = \lt_1, \qquad \lhd_1 = \lt_2, \qquad \lhd_2 = \lt_3
```

$`\lhd_k`$ が狭義で推移的であることはすぐ分かる。残りは有限反映である。

**有限反映.** $`n \lt 3`$、$`\alpha \lhd_n \beta`$、$`X \subseteq \alpha`$ は有限、$`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ とする。このとき $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ で、次の (a)〜(d) を満たすものがある。

```math
\max X \lt y'_0 \qquad \text{(a)}
```

```math
\forall x \in X\ \forall i \lt s\ \forall k \lt 3\ \bigl(x \lhd_k y_i \Rightarrow x \lhd_k y'_i\bigr) \qquad \text{(b)}
```

```math
\forall i, j \lt s\ \forall k \lt 3\ \bigl(y_i \lhd_k y_j \Rightarrow y'_i \lhd_k y'_j\bigr) \qquad \text{(c)}
```

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lhd_m \beta \Rightarrow y'_i \lhd_m \alpha\bigr) \qquad \text{(d)}
```

$`n = 0, 1`$ はペア数列のときと同じ証明である。新しいのは $`n = 2`$ で、(d) に $`m = 1`$ の条件

```math
y_i \lt_2 \beta \Rightarrow y'_i \lt_2 \alpha
```

が加わることである。

## 4. 使う性質

$`\mathcal{R}_N`$ で次が成り立つ。どれも初等部分構造の定義だけから出る。

| | 性質 |
|---|---|
| (P1) | $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ |
| (P2) | $`a \le_1 b \le_1 c \wedge a \le_2 c \Rightarrow a \le_2 b`$ |
| (P3) | $`\alpha`$ が後続で閉じ、$`\forall v \in [y, \alpha)\ y \le_1 v`$ $`\Rightarrow y \le_1 \alpha`$ |
| (P4) | $`S \subseteq [y, \alpha)`$ が $`\alpha`$ で非有界、$`\forall v \in S\ y \le_j v`$ $`\Rightarrow y \le_j \alpha`$ （$`j \le 2`$） |
| (P5) | $`\alpha \lt_1 \beta \Rightarrow \alpha`$ は後続で閉じる |
| (P6) | $`y \lt_2 \beta \Rightarrow \beta`$ は後続で閉じる |
| (P7) | $`\alpha \lt_2 \beta \Rightarrow \{u \lt \alpha : u \le_1 \alpha\}`$ は $`\alpha`$ で非有界 |

- (P2) は、$`\Sigma_2`$ 文の証人を $`\Pi_1`$ 文として $`b`$ から $`c`$ へ運ぶ
- (P4) は、$`\Sigma_2`$ 文 $`\exists \vec x\ \forall \vec z\ \psi`$ の証人と反例を、$`S`$ の十分大きい元の中に収める
- (P6) は、$`\Sigma_2`$ 文「最大元がある」が $`\beta`$ と $`y`$ で一致することから出る
- (P7) は、$`\Sigma_2`$ 文「$`p`$ より大きい $`u`$ で、$`\forall w\ (u \le w \Rightarrow u \le_1 w)`$ となるものがある」を $`\beta`$ から $`\alpha`$ へ移し、(P3) を使う

## 5. n = 2 の有限反映

$`\alpha \lt_3 \beta`$ とする。次の $`\Sigma_3`$ 文を使う。

```math
\exists \vec u\ \forall \vec v\ \exists \vec w\ \Bigl(\mathrm{diag}(X, \vec u) = \mathrm{diag}(X, \vec y) \wedge \bigwedge_{i \lt s} \bigl(A_i \wedge C_i\bigr)\Bigr)
```

```math
A_i :\quad y_i \lt_1 \beta \Rightarrow \bigl(u_i \le v_i \Rightarrow u_i \le_1 v_i\bigr)
```

```math
C_i :\quad y_i \lt_2 \beta \Rightarrow \Bigl(u_i \le_1 v_i \Rightarrow \bigl(v_i \le w_i \wedge \neg\, v_i \le_1 w_i\bigr) \vee u_i \le_2 v_i\Bigr)
```

$`y_i \lt_1 \beta`$、$`y_i \lt_2 \beta`$ は外で決まる真偽なので、式の一部ではなく、どの連言を入れるかの選択である。

**β で真.** $`\vec u = \vec y`$ と置く。$`A_i`$ は (P1) から出る。$`C_i`$ について、$`y_i \lt_2 \beta`$ かつ $`y_i \le_1 v_i`$ で、$`y_i \le_2 v_i`$ でないとする。

1. $`w \in [v_i, \beta)`$ で $`v_i \le_1 w`$ でないものがあることを示す。無いとすると $`\forall w \in [v_i, \beta)\ v_i \le_1 w`$ である
2. $`\beta`$ は後続で閉じる（P6）ので、(P3) から $`v_i \le_1 \beta`$
3. $`y_i \le_1 v_i \le_1 \beta`$ と $`y_i \le_2 \beta`$ から、(P2) で $`y_i \le_2 v_i`$ となり、仮定に反する
4. その $`w`$ を $`w_i`$ に選べば、$`C_i`$ の左の選言が成り立つ

**α で (d).** $`\alpha \lt_3 \beta`$ により文は $`\alpha`$ でも真で、証人を $`\vec y'`$ とする。(a)(b)(c) は原子図式が同じことから出る。

- $`m = 0`$：$`y_i \lt_1 \beta`$ とする。$`t \in [y'_i, \alpha)`$ に $`\vec v = t`$ を入れると $`A_i`$ から $`y'_i \le_1 t`$。$`\alpha`$ は後続で閉じる（P5）ので、(P3) から $`y'_i \lt_1 \alpha`$
- $`m = 1`$：$`y_i \lt_2 \beta`$ とする。$`m = 0`$ の場合から $`y'_i \le_1 \alpha`$ である

  1. $`z \lt \alpha`$ を任意に取る。(P7) から、$`\max(z, y'_i) \lt t \lt \alpha`$ で $`t \le_1 \alpha`$ となる $`t`$ がある
  2. $`\vec v = t`$ を入れて $`\vec w`$ を取る。(P1) から $`y'_i \le_1 t`$ なので、$`C_i`$ のどちらかの選言が成り立つ
  3. $`t \le_1 \alpha`$ と (P1) から $`t \le_1 w_i`$ なので、左の選言は成り立たない。よって $`y'_i \le_2 t`$
  4. そういう $`t`$ は $`\alpha`$ で非有界なので、(P4) から $`y'_i \le_2 \alpha`$。すなわち $`y'_i \lt_2 \alpha`$

## 6. 初期列のラベルと停止性

$`\omega_1`$ の中の閉包で作った $`\lambda(\gamma)`$ は、ブロックの数によらずすべての文について $`\omega_1`$ と一致する。したがって

```math
\lambda(0) \lt \lambda(\lambda(0)) \lt \lambda(\lambda(\lambda(0))) \lt \cdots
```

のどの 2 つも、$`\le_1, \dots, \le_N`$ のすべてで結ばれる。これを $`S^r_n`$ のラベルとして貼る。

あとはペア数列と同じく、命題 19.1 で高さが下がることから停止性が出る。

## 7. 形式化していないこと

- **ラベルの大きさ**：Lean の証明はラベルを $`\omega_1`$ の中の閉包で作っているので、どれくらいの大きさかは示していない。$`\mathcal{R}_3`$ の中で鎖がどこに現れるかは、調べていない
- **4 行以上**
  - (d) に $`m = 2`$ の条件 $`y_i \lt_3 \beta \Rightarrow y'_i \lt_3 \alpha`$ が加わる
  - §5 の方法を使うには、(P2)(P4)(P6)(P7) を一段上げた性質が要る。(P4) は $`\Sigma_2`$ 文の証人と反例を収める議論なので、$`\Sigma_3`$ ではそのままは使えない
  - 4 行以上は扱っていない

## 8. Lean との対応

| 数学 | Lean | ファイル |
|---|---|---|
| $`\le_j`$ の定義 | `RFix`, `RN`, `lev`, `lev_iff` | [`Basic.lean`](../lean/Pattern/Basic.lean) |
| $`\lt_j`$ | `lab` | 同上 |
| 論理式、原子図式 | `Sig`, `diag`, `Elem` | 同上 |
| (P1) | `lev0_of_le` | 同上 |
| (P2) | `lev1_of_lev0` | 同上 |
| (P3) | `lev0_of_forall` | 同上 |
| (P4) | `elem_cofinal` | 同上 |
| (P5) | `succ_lt_of_lab0` | 同上 |
| (P6) | `succ_lt_of_lab1_top` | 同上 |
| (P7) | `exists_lev0_below` | 同上 |
| 有限反映 $`n = 0, 1, 2`$ | `reflect_zero`, `reflect_one`, `reflect_two` | [`Reflect.lean`](../lean/Pattern/Reflect.lean) |
| ラベルの体系 | `labelSystem` | 同上 |
| $`\lambda`$ | `next`, `lam`, `lam_elem` | [`Chain.lean`](../lean/Pattern/Chain.lean) |
| すべての段で結ばれた鎖 | `lab_lam`, `exists_chain` | 同上 |
| $`S^r_n`$、標準列 | `stair`, `Std` | [`Main.lean`](../lean/Pattern/Main.lean) |
| $`S^r_n`$ のラベル | `stable_stair` | 同上 |
| 停止性（$`r \le 3`$） | `terminates` | 同上 |
| トリオ数列、ペア数列の停止性 | `tss_terminates`, `pss_terminates` | 同上 |
| 整礎性 | `StdR_wf` | 同上 |
| 命題 19.1 | `descent` | [`Bm4/Label.lean`](../lean/Bm4/Label.lean) |
