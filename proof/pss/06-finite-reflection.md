[← Back](README.md) | [English](en/06-finite-reflection.md) | [Japanese](06-finite-reflection.md)

# 有限反映

前提: [02 構造と初等部分構造](02-elementary-substructure.md)、[03 R_N](03-patterns.md)、[04 R_N の性質 P1〜P7](04-pattern-properties.md)、[05 配列、展開、安定ラベル](05-arrays-labels.md)

## 1. 主張

$`r \le 3`$ とし、$`\mathcal{R}_r`$ の関係でラベルの関係を置く。

```math
\lhd_k = \lt_{k+1} \qquad (k \lt r)
```

$`\lhd_k`$ が狭義で推移的であることは [03](03-patterns.md) §3 から出る。このノートでは有限反映（[05](05-arrays-labels.md) §5 の (a)〜(d)）を $`n = 0, 1, 2`$ について示す。$`n = 1`$ では $`r \ge 2`$、$`n = 2`$ では $`r = 3`$ である。

以下 $`X = \{p_0, \dots, p_{k-1}\} \subseteq \alpha`$、$`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$ とする。

## 2. 原子図式が同じコピー

**補題.** $`y'_0, \dots, y'_{s-1} \lt \alpha`$ で、列 $`(p_0, \dots, p_{k-1}, y'_0, \dots, y'_{s-1})`$ の原子図式が列 $`(p_0, \dots, p_{k-1}, y_0, \dots, y_{s-1})`$ の原子図式と同じなら、$`y'`$ は増加列で、(a)(b)(c) を満たす。

**証明.**

- 増加：$`i \lt j`$ なら $`[y_j \le y_i]`$ が偽なので $`[y'_j \le y'_i]`$ も偽
- (a)：$`p_a \lt \alpha \le y_0`$ なので $`[y_0 \le p_a]`$ が偽、よって $`[y'_0 \le p_a]`$ も偽
- (b)(c)：$`x \lt_{k+1} y_i`$ などは原子式 $`\le`$ と $`\le_{k+1}`$ の真偽で決まるので、そのまま移る

$`\square`$

$`[\alpha, \beta)`$ の点を $`\alpha`$ の下へ写すことは、[02](02-elementary-substructure.md) §4.2 のコピーと同じ形である。

## 3. n = 0

$`\alpha \lt_1 \beta`$ とする。$`\Sigma_1`$ 論理式

```math
\exists u_0 \cdots \exists u_{s-1}\ \bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y)\bigr)
```

は $`\beta`$ で真（$`\vec u = \vec y`$）。$`\alpha \le_1 \beta`$ から $`\alpha`$ でも真で、その証人が §2 の $`y'`$ になる。(d) は $`m \lt 0`$ なので空である。$`\square`$

## 4. n = 1

$`\alpha \lt_2 \beta`$ とする。$`y_i \lt_1 \beta`$ となる $`i`$ についてだけ連言を入れた、次の $`\Sigma_2`$ 論理式を使う。

```math
\exists \vec u\ \forall \vec v\ \Bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i : y_i \lt_1 \beta} \bigl(u_i \le v_i \Rightarrow u_i \le_1 v_i\bigr)\Bigr)
```

**β で真.** $`\vec u = \vec y`$ とする。$`y_i \le v_i \lt \beta`$ と $`y_i \le_1 \beta`$ から、P1 で $`y_i \le_1 v_i`$。

**α で (d).** $`\alpha \le_2 \beta`$ から $`\alpha`$ でも真で、証人を $`y'`$ とする。(a)(b)(c) は §2 から出る。$`y_i \lt_1 \beta`$ とする。

1. $`t \in [y'_i, \alpha)`$ を任意に取り、$`\vec v`$ のすべての成分を $`t`$ にすると、$`y'_i \le_1 t`$
2. $`\alpha \lt_1 \beta`$ なので、P5 から $`\alpha`$ は後続で閉じる
3. P3 から $`y'_i \le_1 \alpha`$。$`y'_i \lt \alpha`$ なので $`y'_i \lt_1 \alpha`$

$`\square`$

これは Wilken の論文 "Pure Σ2-elementarity beyond the core" の補題 1.7 と同じ内容である。

## 5. n = 2

$`\alpha \lt_3 \beta`$ とする。(d) に $`m = 1`$ の条件 $`y_i \lt_2 \beta \Rightarrow y'_i \lt_2 \alpha`$ が加わる。次の $`\Sigma_3`$ 論理式を使う。

```math
\exists \vec u\ \forall \vec v\ \exists \vec w\ \Bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i \lt s} \bigl(A_i \wedge C_i\bigr)\Bigr)
```

```math
A_i :\quad y_i \lt_1 \beta \text{ のときだけ入れる：}\ \ u_i \le v_i \Rightarrow u_i \le_1 v_i
```

```math
C_i :\quad y_i \lt_2 \beta \text{ のときだけ入れる：}\ \ u_i \le_1 v_i \Rightarrow \bigl(v_i \le w_i \wedge \neg\, v_i \le_1 w_i\bigr) \vee u_i \le_2 v_i
```

$`y_i \lt_1 \beta`$、$`y_i \lt_2 \beta`$ は外で決まる真偽で、どの連言を入れるかを決めるだけである。$`A_i`$ は $`\forall v_i`$ の下の、$`C_i`$ は $`\forall v_i\ \exists w_i`$ の下の量化子なし論理式なので、全体は $`\exists \forall \exists`$ の $`\Sigma_3`$ 論理式である。

### 5.1 β で真

$`\vec u = \vec y`$ とし、$`\beta`$ 未満の $`\vec v`$ を任意に取る。$`A_i`$ は §4 と同じく P1 から出る。$`C_i`$ のための $`w_i`$ を選ぶ。

$`y_i \lt_2 \beta`$、$`y_i \le_1 v_i`$ で、$`y_i \le_2 v_i`$ でないとする（それ以外なら $`w_i = v_i`$ でよい）。

1. $`[v_i, \beta)`$ に、$`v_i \le_1 w`$ でない $`w`$ があることを示す。無いとすると、すべての $`w \in [v_i, \beta)`$ で $`v_i \le_1 w`$
2. P6 から $`\beta`$ は後続で閉じるので、P3 から $`v_i \le_1 \beta`$
3. $`y_i \le_1 v_i`$、$`v_i \le_1 \beta`$、$`y_i \le_2 \beta`$ から、P2 で $`y_i \le_2 v_i`$。仮定に反する
4. その $`w`$ を $`w_i`$ に選ぶと、$`C_i`$ の左の選言が成り立つ

### 5.2 α で (d)

$`\alpha \le_3 \beta`$ から論理式は $`\alpha`$ でも真で、証人を $`y'`$ とする。(a)(b)(c) は §2 から出る。

**$`m = 0`$.** $`y_i \lt_1 \beta`$ なら、§4 と同じく、$`\vec v`$ の成分をすべて $`t \in [y'_i, \alpha)`$ にして $`A_i`$ を使い、P5、P3 から $`y'_i \lt_1 \alpha`$。

**$`m = 1`$.** $`y_i \lt_2 \beta`$ とする。$`y_i \lt_1 \beta`$ でもあるので、$`m = 0`$ から $`y'_i \le_1 \alpha`$。

1. $`z \lt \alpha`$ を任意に取る。$`\alpha \lt_2 \beta`$ なので、P7 から $`\max(z, y'_i) \lt t \lt \alpha`$ かつ $`t \le_1 \alpha`$ となる $`t`$ がある
2. $`\vec v`$ の成分をすべて $`t`$ にして、$`\vec w \lt \alpha`$ を得る
3. P1 から $`y'_i \le_1 t`$ なので、$`C_i`$ のどちらかの選言が成り立つ
4. $`t \le_1 \alpha`$ と P1 から $`t \le_1 w_i`$ なので、左の選言は成り立たない。よって $`y'_i \le_2 t`$
5. そういう $`t`$ は $`\alpha`$ で非有界なので、P4 から $`y'_i \le_2 \alpha`$。$`y'_i \lt \alpha`$ なので $`y'_i \lt_2 \alpha`$

$`\square`$

Wilken（arXiv 版 v1 の補題 4.2）は、$`\alpha \lt_3 \beta`$ なら $`\alpha`$ が $`\lt_2`$-前者の上限であることを、同じ P2、P7 型の議論で示している。

## 6. 4 行で同じ方法が使えない理由

$`n = 3`$ では、(d) に $`m = 2`$ の条件 $`y_i \lt_3 \beta \Rightarrow y'_i \lt_3 \alpha`$ が加わる。§5 と同じ形の論理式を作るには、P2、P4、P6、P7 を一段上げた性質が要る。そのうち P4 は、[04](04-pattern-properties.md) で見たとおり $`\Sigma_3`$ ではそのまま成り立たない。4 行以上は、P4 に条件を足した P4′ と論理式 $`\Phi_m`$ を使う別の証明で示した（[bms 05](../bms/05-finite-reflection.md)）。

## 7. 証明での使われ方

| 事実 | 使う場所 |
|---|---|
| $`n = 0, 1, 2`$ の有限反映 | $`\mathcal{R}_r`$ がラベルの体系になること（[08](08-termination.md)） |

## 8. Lean での対応

| 概念 | Lean | ファイル |
|---|---|---|
| $`X`$ を列にする | `listTuple`, `listTuple_lt`, `mem_listTuple` | [`Pattern/Reflect.lean`](../../lean/Pattern/Reflect.lean) |
| 原子図式が同じ | `SameBits`, `Agree`, `agree_iff`, `lab_transfer` | 同上 |
| §2 の補題 | `copy_props` | 同上 |
| §3 | `reflect_zero` | 同上 |
| §4 | `reflect_one` | 同上 |
| §5 | `reflect_two` | 同上 |
| ラベルの体系 | `labelSystem` | 同上 |
