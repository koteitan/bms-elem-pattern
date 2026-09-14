[← Back](../README-en.md) | [English](06-finite-reflection.md) | [Japanese](../06-finite-reflection.md)

# Finite Reflection

Prerequisites: [02 Structures and elementary substructures](02-elementary-substructure.md), [03 R_N](03-patterns.md), [04 Properties P1–P7 of R_N](04-pattern-properties.md), [05 Arrays, expansion, and stable labels](05-arrays-labels.md)

## 1. Claim

Let $`r \le 3`$, and define the label relations by the relations of $`\mathcal{R}_r`$:

```math
\lhd_k = \lt_{k+1} \qquad (k \lt r) .
```

That $`\lhd_k`$ is strict and transitive follows from [03](03-patterns.md) §3. This note proves finite reflection ((a)–(d) of [05](05-arrays-labels.md) §5) for $`n = 0, 1, 2`$. For $`n = 1`$ we have $`r \ge 2`$, and for $`n = 2`$, $`r = 3`$.

Below, let $`X = \{p_0, \dots, p_{k-1}\} \subseteq \alpha`$ and $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$.

## 2. Copies with the same atomic diagram

**Lemma.** If $`y'_0, \dots, y'_{s-1} \lt \alpha`$ and the atomic diagram of $`(p_0, \dots, p_{k-1}, y'_0, \dots, y'_{s-1})`$ equals that of $`(p_0, \dots, p_{k-1}, y_0, \dots, y_{s-1})`$, then $`y'`$ is increasing and satisfies (a)(b)(c).

**Proof.**

- Increasing: for $`i \lt j`$, $`[y_j \le y_i]`$ is false, so $`[y'_j \le y'_i]`$ is false as well
- (a): $`p_a \lt \alpha \le y_0`$, so $`[y_0 \le p_a]`$ is false, hence $`[y'_0 \le p_a]`$ is false
- (b)(c): statements such as $`x \lt_{k+1} y_i`$ are determined by the truth values of the atomic formulas $`\le`$ and $`\le_{k+1}`$, so they transfer as they are

$`\square`$

Moving the points of $`[\alpha, \beta)`$ below $`\alpha`$ has the same form as the copies in [02](02-elementary-substructure.md) §4.2.

## 3. n = 0

Let $`\alpha \lt_1 \beta`$. The $`\Sigma_1`$ formula

```math
\exists u_0 \cdots \exists u_{s-1}\ \bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y)\bigr)
```

is true in $`\beta`$ ($`\vec u = \vec y`$). By $`\alpha \le_1 \beta`$ it is also true in $`\alpha`$, and its witness is the $`y'`$ of §2. (d) is vacuous since $`m \lt 0`$. $`\square`$

## 4. n = 1

Let $`\alpha \lt_2 \beta`$. Use the following $`\Sigma_2`$ formula, where the conjuncts are included only for those $`i`$ with $`y_i \lt_1 \beta`$.

```math
\exists \vec u\ \forall \vec v\ \Bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i : y_i \lt_1 \beta} \bigl(u_i \le v_i \Rightarrow u_i \le_1 v_i\bigr)\Bigr)
```

**True in β.** Put $`\vec u = \vec y`$. From $`y_i \le v_i \lt \beta`$ and $`y_i \le_1 \beta`$, P1 gives $`y_i \le_1 v_i`$.

**(d) in α.** By $`\alpha \le_2 \beta`$ the formula is also true in $`\alpha`$; let $`y'`$ be the witness. (a)(b)(c) follow from §2. Suppose $`y_i \lt_1 \beta`$.

1. Take any $`t \in [y'_i, \alpha)`$ and set all components of $`\vec v`$ to $`t`$; then $`y'_i \le_1 t`$
2. Since $`\alpha \lt_1 \beta`$, $`\alpha`$ is closed under successor by P5
3. P3 gives $`y'_i \le_1 \alpha`$. Since $`y'_i \lt \alpha`$, $`y'_i \lt_1 \alpha`$

$`\square`$

This is the same content as Lemma 1.7 of Wilken's paper "Pure Σ2-elementarity beyond the core".

## 5. n = 2

Let $`\alpha \lt_3 \beta`$. (d) gains the condition $`y_i \lt_2 \beta \Rightarrow y'_i \lt_2 \alpha`$ for $`m = 1`$. Use the following $`\Sigma_3`$ formula.

```math
\exists \vec u\ \forall \vec v\ \exists \vec w\ \Bigl(\mathrm{diag}(\vec p, \vec u) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i \lt s} \bigl(A_i \wedge C_i\bigr)\Bigr)
```

```math
A_i :\quad \text{included only if } y_i \lt_1 \beta \text{:}\ \ u_i \le v_i \Rightarrow u_i \le_1 v_i
```

```math
C_i :\quad \text{included only if } y_i \lt_2 \beta \text{:}\ \ u_i \le_1 v_i \Rightarrow \bigl(v_i \le w_i \wedge \neg\, v_i \le_1 w_i\bigr) \vee u_i \le_2 v_i
```

$`y_i \lt_1 \beta`$ and $`y_i \lt_2 \beta`$ are truth values decided outside, and they only decide which conjuncts are included. $`A_i`$ is a quantifier-free formula under $`\forall v_i`$, and $`C_i`$ under $`\forall v_i\ \exists w_i`$, so the whole is a $`\Sigma_3`$ formula of the form $`\exists \forall \exists`$.

### 5.1 True in β

Put $`\vec u = \vec y`$ and take any $`\vec v`$ below $`\beta`$. $`A_i`$ follows from P1 as in §4. We choose $`w_i`$ for $`C_i`$.

Suppose $`y_i \lt_2 \beta`$ and $`y_i \le_1 v_i`$, but $`y_i \le_2 v_i`$ fails (otherwise $`w_i = v_i`$ will do).

1. We show that $`[v_i, \beta)`$ contains $`w`$ with $`v_i \le_1 w`$ false. If not, $`v_i \le_1 w`$ for all $`w \in [v_i, \beta)`$
2. $`\beta`$ is closed under successor by P6, so P3 gives $`v_i \le_1 \beta`$
3. From $`y_i \le_1 v_i`$, $`v_i \le_1 \beta`$ and $`y_i \le_2 \beta`$, P2 gives $`y_i \le_2 v_i`$, contradicting the assumption
4. Choosing that $`w`$ as $`w_i`$ makes the left disjunct of $`C_i`$ true

### 5.2 (d) in α

By $`\alpha \le_3 \beta`$ the formula is also true in $`\alpha`$; let $`y'`$ be the witness. (a)(b)(c) follow from §2.

**$`m = 0`$.** If $`y_i \lt_1 \beta`$, then as in §4, set all components of $`\vec v`$ to $`t \in [y'_i, \alpha)`$ and use $`A_i`$; P5 and P3 give $`y'_i \lt_1 \alpha`$.

**$`m = 1`$.** Suppose $`y_i \lt_2 \beta`$. Since also $`y_i \lt_1 \beta`$, the case $`m = 0`$ gives $`y'_i \le_1 \alpha`$.

1. Take any $`z \lt \alpha`$. Since $`\alpha \lt_2 \beta`$, P7 gives $`t`$ with $`\max(z, y'_i) \lt t \lt \alpha`$ and $`t \le_1 \alpha`$
2. Set all components of $`\vec v`$ to $`t`$ and obtain $`\vec w \lt \alpha`$
3. P1 gives $`y'_i \le_1 t`$, so one of the disjuncts of $`C_i`$ holds
4. From $`t \le_1 \alpha`$ and P1 we get $`t \le_1 w_i`$, so the left disjunct fails. Hence $`y'_i \le_2 t`$
5. Such $`t`$ are unbounded in $`\alpha`$, so P4 gives $`y'_i \le_2 \alpha`$. Since $`y'_i \lt \alpha`$, $`y'_i \lt_2 \alpha`$

$`\square`$

Wilken (Lemma 4.2 of arXiv version v1) shows, by the same P2- and P7-type arguments, that if $`\alpha \lt_3 \beta`$ then $`\alpha`$ is the supremum of its $`\lt_2`$-predecessors.

## 6. Why the same method does not work for 4 rows

For $`n = 3`$, (d) gains the condition $`y_i \lt_3 \beta \Rightarrow y'_i \lt_3 \alpha`$ for $`m = 2`$. Building a formula of the same form as in §5 would require P2, P4, P6 and P7 one level higher. Of these, P4 does not hold for $`\Sigma_3`$ as it is, as seen in [04](04-pattern-properties.md). 4 or more rows are not treated.

## 7. How it is used in the proof

| Fact | Where |
|---|---|
| Finite reflection for $`n = 0, 1, 2`$ | $`\mathcal{R}_r`$ is a label system ([08](08-termination.md)) |

## 8. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Turning $`X`$ into a sequence | `listTuple`, `listTuple_lt`, `mem_listTuple` | [`Pattern/Reflect.lean`](../../lean/Pattern/Reflect.lean) |
| Same atomic diagram | `SameBits`, `Agree`, `agree_iff`, `lab_transfer` | same |
| Lemma of §2 | `copy_props` | same |
| §3 | `reflect_zero` | same |
| §4 | `reflect_one` | same |
| §5 | `reflect_two` | same |
| Label system | `labelSystem` | same |
