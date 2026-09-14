[← Back](../README-en.md) | [English](TSS.md) | [Japanese](../TSS.md)

# Termination Proof of the Trio Sequence System via Σ₃-Elementary Substructures

We extend [the proof for pair sequences](../README-en.md) to 3 rows.
The labels are related by the relations of $`\mathcal{R}_3 = (\mathrm{Ord}; \le, \le_1, \le_2, \le_3)`$ instead of $`\mathcal{R}_2`$.
In Lean, $`\mathcal{R}_N`$ is defined for general $`N`$, and 1 to 3 rows (primitive, pair and trio sequences) are treated by a single theorem.

## Result

**Theorem (termination).** Let $`r \le 3`$, let $`A`$ be a standard array with $`r`$ rows and $`n : \mathbb{N} \to \mathbb{N}`$ an arbitrary function, and put

```math
A_0 = A, \qquad A_{t+1} = A_t[n(t)] .
```

Then $`A_T`$ is empty for some $`T`$.

**Theorem (well-foundedness).** For $`r \le 3`$, the relation on standard arrays with $`r`$ rows

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

is well-founded.

The Lean proof contains no `sorry`, and the only axioms are `propext` / `Classical.choice` / `Quot.sound`.

## 1. Standard arrays

```math
S^r_n = \underbrace{(0,\dots,0)}_{r}\,\underbrace{(1,\dots,1)}_{r} \cdots \underbrace{(n,\dots,n)}_{r}
```

**Definition.** A standard array with $`r`$ rows is an array with $`r`$ rows obtained from some $`S^r_n`$ by finitely many expansions. The case $`r = 3`$ is the trio sequence system.

The expansion rule is BM4.

## 2. R_N

```math
\alpha \le_j \beta \iff (\alpha; \le, \le_1, \dots, \le_N) \preceq_{\Sigma_j} (\beta; \le, \le_1, \dots, \le_N) \qquad (1 \le j \le N)
```

```math
\alpha \lt_j \beta \iff \alpha \lt \beta \wedge \alpha \le_j \beta
```

$`\le_1, \dots, \le_N`$ are defined simultaneously by induction on $`\beta`$.

In Lean, a formula is represented by a list of quantifier block lengths $`[b_1, \dots, b_r]`$ and a set $`D`$ of atomic diagrams.

```math
\exists x^1_1 \cdots x^1_{b_1}\ \neg\, \exists x^2_1 \cdots x^2_{b_2}\ \neg \cdots \exists x^r_1 \cdots x^r_{b_r}\ \neg\, \bigl(\mathrm{diag}(\vec p, \vec x^1, \dots, \vec x^r) \in D\bigr)
```

Those with $`r`$ blocks are the $`\Sigma_r`$ sentences. A $`\Sigma_j`$-elementary substructure is defined as agreement on all sentences with at most $`j`$ blocks.

## 3. Label relations

```math
\lhd_0 = \lt_1, \qquad \lhd_1 = \lt_2, \qquad \lhd_2 = \lt_3
```

That $`\lhd_k`$ is strict and transitive is immediate. What remains is finite reflection.

**Finite reflection.** Let $`n \lt 3`$, $`\alpha \lhd_n \beta`$, $`X \subseteq \alpha`$ finite, and $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$. Then there are $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ satisfying (a)–(d) below.

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

The cases $`n = 0, 1`$ are proved as for pair sequences. What is new is $`n = 2`$, where (d) gains the condition for $`m = 1`$:

```math
y_i \lt_2 \beta \Rightarrow y'_i \lt_2 \alpha .
```

## 4. Properties used

The following hold in $`\mathcal{R}_N`$. All of them follow from the definition of elementary substructures alone.

| | Property |
|---|---|
| (P1) | $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ |
| (P2) | $`a \le_1 b \le_1 c \wedge a \le_2 c \Rightarrow a \le_2 b`$ |
| (P3) | $`\alpha`$ closed under successor, $`\forall v \in [y, \alpha)\ y \le_1 v`$ $`\Rightarrow y \le_1 \alpha`$ |
| (P4) | $`S \subseteq [y, \alpha)`$ unbounded in $`\alpha`$, $`\forall v \in S\ y \le_j v`$ $`\Rightarrow y \le_j \alpha`$ ($`j \le 2`$) |
| (P5) | $`\alpha \lt_1 \beta \Rightarrow \alpha`$ is closed under successor |
| (P6) | $`y \lt_2 \beta \Rightarrow \beta`$ is closed under successor |
| (P7) | $`\alpha \lt_2 \beta \Rightarrow \{u \lt \alpha : u \le_1 \alpha\}`$ is unbounded in $`\alpha`$ |

- (P2) carries the witness of a $`\Sigma_2`$ sentence from $`b`$ to $`c`$ as a $`\Pi_1`$ sentence
- (P4) places the witnesses and counterexamples of a $`\Sigma_2`$ sentence $`\exists \vec x\ \forall \vec z\ \psi`$ inside a sufficiently large element of $`S`$
- (P6) follows because the $`\Sigma_2`$ sentence "there is a largest element" has the same truth value in $`\beta`$ and $`y`$
- (P7) transfers the $`\Sigma_2`$ sentence "there is $`u`$ greater than $`p`$ with $`\forall w\ (u \le w \Rightarrow u \le_1 w)`$" from $`\beta`$ to $`\alpha`$ and uses (P3)

## 5. Finite reflection for n = 2

Let $`\alpha \lt_3 \beta`$. We use the following $`\Sigma_3`$ sentence.

```math
\exists \vec u\ \forall \vec v\ \exists \vec w\ \Bigl(\mathrm{diag}(X, \vec u) = \mathrm{diag}(X, \vec y) \wedge \bigwedge_{i \lt s} \bigl(A_i \wedge C_i\bigr)\Bigr)
```

```math
A_i :\quad y_i \lt_1 \beta \Rightarrow \bigl(u_i \le v_i \Rightarrow u_i \le_1 v_i\bigr)
```

```math
C_i :\quad y_i \lt_2 \beta \Rightarrow \Bigl(u_i \le_1 v_i \Rightarrow \bigl(v_i \le w_i \wedge \neg\, v_i \le_1 w_i\bigr) \vee u_i \le_2 v_i\Bigr)
```

$`y_i \lt_1 \beta`$ and $`y_i \lt_2 \beta`$ are truth values decided outside, so they are not part of the sentence; they only select which conjuncts to include.

**True in β.** Put $`\vec u = \vec y`$. $`A_i`$ follows from (P1). For $`C_i`$, suppose $`y_i \lt_2 \beta`$ and $`y_i \le_1 v_i`$ but not $`y_i \le_2 v_i`$.

1. We show that there is $`w \in [v_i, \beta)`$ with $`v_i \le_1 w`$ false. If not, $`\forall w \in [v_i, \beta)\ v_i \le_1 w`$
2. $`\beta`$ is closed under successor (P6), so (P3) gives $`v_i \le_1 \beta`$
3. From $`y_i \le_1 v_i \le_1 \beta`$ and $`y_i \le_2 \beta`$, (P2) gives $`y_i \le_2 v_i`$, contradicting the assumption
4. Choosing that $`w`$ as $`w_i`$ makes the left disjunct of $`C_i`$ true

**(d) in α.** By $`\alpha \lt_3 \beta`$ the sentence is also true in $`\alpha`$; let $`\vec y'`$ be the witness. (a)(b)(c) follow because the atomic diagrams agree.

- $`m = 0`$: suppose $`y_i \lt_1 \beta`$. For $`t \in [y'_i, \alpha)`$, putting $`\vec v = t`$ in $`A_i`$ gives $`y'_i \le_1 t`$. $`\alpha`$ is closed under successor (P5), so (P3) gives $`y'_i \lt_1 \alpha`$
- $`m = 1`$: suppose $`y_i \lt_2 \beta`$. By the case $`m = 0`$ we have $`y'_i \le_1 \alpha`$

  1. Take any $`z \lt \alpha`$. By (P7) there is $`t`$ with $`\max(z, y'_i) \lt t \lt \alpha`$ and $`t \le_1 \alpha`$
  2. Put $`\vec v = t`$ and take $`\vec w`$. By (P1), $`y'_i \le_1 t`$, so one of the disjuncts of $`C_i`$ holds
  3. From $`t \le_1 \alpha`$ and (P1) we get $`t \le_1 w_i`$, so the left disjunct fails. Hence $`y'_i \le_2 t`$
  4. Such $`t`$ are unbounded in $`\alpha`$, so (P4) gives $`y'_i \le_2 \alpha`$, that is, $`y'_i \lt_2 \alpha`$

## 6. Labels of the initial arrays and termination

The ordinal $`\lambda(\gamma)`$ built by a closure inside $`\omega_1`$ agrees with $`\omega_1`$ on all sentences, regardless of the number of blocks. Hence any two of

```math
\lambda(0) \lt \lambda(\lambda(0)) \lt \lambda(\lambda(\lambda(0))) \lt \cdots
```

are related by all of $`\le_1, \dots, \le_N`$. These are attached as the labels of $`S^r_n`$.

The rest is as for pair sequences: termination follows because Proposition 19.1 lowers the height.

## 7. What is not formalized

- **Size of the labels**: the Lean proof builds the labels by a closure inside $`\omega_1`$, so it does not show how large they are. Where chains appear in $`\mathcal{R}_3`$ has not been investigated
- **4 or more rows**
  - (d) gains the condition $`y_i \lt_3 \beta \Rightarrow y'_i \lt_3 \alpha`$ for $`m = 2`$
  - Using the method of §5 would require (P2)(P4)(P6)(P7) one level higher. (P4) is an argument placing the witnesses and counterexamples of a $`\Sigma_2`$ sentence, so it does not carry over to $`\Sigma_3`$ as it is
  - 4 or more rows are not treated

## 8. Correspondence with Lean

| Mathematics | Lean | File |
|---|---|---|
| Definition of $`\le_j`$ | `RFix`, `RN`, `lev`, `lev_iff` | [`Basic.lean`](../../lean/Pattern/Basic.lean) |
| $`\lt_j`$ | `lab` | same |
| Formulas, atomic diagrams | `Sig`, `diag`, `Elem` | same |
| (P1) | `lev0_of_le` | same |
| (P2) | `lev1_of_lev0` | same |
| (P3) | `lev0_of_forall` | same |
| (P4) | `elem_cofinal` | same |
| (P5) | `succ_lt_of_lab0` | same |
| (P6) | `succ_lt_of_lab1_top` | same |
| (P7) | `exists_lev0_below` | same |
| Finite reflection $`n = 0, 1, 2`$ | `reflect_zero`, `reflect_one`, `reflect_two` | [`Reflect.lean`](../../lean/Pattern/Reflect.lean) |
| Label system | `labelSystem` | same |
| $`\lambda`$ | `next`, `lam`, `lam_elem` | [`Chain.lean`](../../lean/Pattern/Chain.lean) |
| Chains related at every level | `lab_lam`, `exists_chain` | same |
| $`S^r_n`$, standard arrays | `stair`, `Std` | [`Main.lean`](../../lean/Pattern/Main.lean) |
| Labels of $`S^r_n`$ | `stable_stair` | same |
| Termination ($`r \le 3`$) | `terminates` | same |
| Termination of trio and pair sequences | `tss_terminates`, `pss_terminates` | same |
| Well-foundedness | `StdR_wf` | same |
| Proposition 19.1 | `descent` | [`Bm4/Label.lean`](../../lean/Bm4/Label.lean) |
