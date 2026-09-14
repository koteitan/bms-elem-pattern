[← Back](../README-en.md) | [English](05-arrays-labels.md) | [Japanese](../05-arrays-labels.md)

# Arrays, Expansion, and Stable Labels

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md)

This note summarizes the combinatorial part of BM4. The Lean code is copied from [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal), and the details of the proof are in a study note of the same repository (study/07-stable-labels.md).

## 1. Arrays

An **array** $`A`$ with $`r`$ rows and length $`\ell`$ is a sequence of columns $`A_0, \dots, A_{\ell - 1}`$, each column being an $`r`$-tuple of natural numbers. The row-$`k`$ entry of the column $`A_i`$ is written $`A_i[k]`$. Arrays are written by listing their columns, as in $`(0,0)(1,1)(2,2)`$.

## 2. Parents and ancestors

**Definition ($`k`$-parent).** The **candidates** for column $`i`$ in row $`k`$ are all columns $`j \lt i`$ if $`k = 0`$, and the $`(k-1)`$-ancestors of column $`i`$ if $`k \ge 1`$. The largest candidate $`j`$ with $`A_j[k] \lt A_i[k]`$ is the **$`k`$-parent** of column $`i`$.

**Definition ($`k`$-ancestor).** A column reached from column $`i`$ by following $`k`$-parents one or more times is a **$`k`$-ancestor** of column $`i`$, written $`j \prec_k i`$. $`j \preceq_k i`$ means $`j = i`$ or $`j \prec_k i`$.

**Example.** In $`(0,0)(1,1)(2,2)`$, the 0-parent of column 2 is column 1 (value $`1 \lt 2`$), and its 1-parent is also column 1. For all $`j \lt i`$ we have $`j \prec_0 i`$ and $`j \prec_1 i`$.

## 3. Expansion

Let $`c = \ell - 1`$ be the last column.

**If column $`c`$ has no parent in any row $`k \lt r`$.** $`A[N]`$ is $`A`$ with the last column removed.

**If it has a parent.** Put:

| Symbol | Meaning |
|---|---|
| $`m_0`$ | the largest row in which column $`c`$ has a parent |
| $`p`$ | the $`m_0`$-parent of column $`c`$ |
| $`s = c - p`$ | length of the bad part |
| $`G = A_0 \cdots A_{p-1}`$ | the good part |

$`A[N] = G\, B_0\, B_1 \cdots B_N`$, where the $`j`$-th column ($`j \lt s`$) of the copy $`B_q`$ is as follows.

```math
(B_q)_j[k] = \begin{cases} A_{p+j}[k] + q \cdot (A_c[k] - A_p[k]) & \text{if } k \lt m_0 \text{ and } p \preceq_k p + j \cr A_{p+j}[k] & \text{otherwise} \end{cases}
```

**Example 1.** $`(0,0)(1,1)[N]`$: $`c = 1`$, $`m_0 = 1`$, $`p = 0`$, $`s = 1`$. Row 0 gets $`q \cdot (1 - 0)`$ added, so

```math
(0,0)(1,1)[N] = (0,0)(1,0)(2,0) \cdots (N,0) .
```

**Example 2.** $`(0,0)(1,1)(2,2)[2]`$: $`c = 2`$, $`m_0 = 1`$, $`p = 1`$, $`s = 1`$, $`G = (0,0)`$. Since $`B_q = (1 + q, 1)`$,

```math
(0,0)(1,1)(2,2)[2] = (0,0)(1,1)(2,1)(3,1) .
```

## 4. Standard arrays

**Definition.** An array obtained by finitely many expansions from the array with $`r`$ rows

```math
S^r_n = \underbrace{(0,\dots,0)}_{r}\,\underbrace{(1,\dots,1)}_{r} \cdots \underbrace{(n,\dots,n)}_{r}
```

is a **standard array** with $`r`$ rows. $`r = 1`$ is the primitive sequence system, $`r = 2`$ the pair sequence system, and $`r = 3`$ the trio sequence system. The initial array $`E_r`$ of BM4 is $`S^r_1`$.

## 5. Label systems

**Definition.** A **label system** with $`r`$ rows is a well-order $`(\mathrm{Lab}, \lt)`$ together with relations $`\lhd_0, \dots, \lhd_{r-1}`$ on $`\mathrm{Lab}`$ satisfying the following.

1. **Strict.** $`a \lhd_k b \Rightarrow a \lt b`$
2. **Transitive.** $`a \lhd_k b \wedge b \lhd_k c \Rightarrow a \lhd_k c`$
3. **Finite reflection.** If $`n \lt r`$, $`\alpha \lhd_n \beta`$, $`X \subseteq \alpha`$ is finite, and $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$, then there are $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ satisfying (a)–(d) below

```math
\max X \lt y'_0 \qquad \text{(a)}
```

```math
\forall x \in X\ \forall i \lt s\ \forall k \lt r\ \bigl(x \lhd_k y_i \Rightarrow x \lhd_k y'_i\bigr) \qquad \text{(b)}
```

```math
\forall i, j \lt s\ \forall k \lt r\ \bigl(y_i \lhd_k y_j \Rightarrow y'_i \lhd_k y'_j\bigr) \qquad \text{(c)}
```

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lhd_m \beta \Rightarrow y'_i \lhd_m \alpha\bigr) \qquad \text{(d)}
```

**Reading.** Finitely many labels in $`[\alpha, \beta)`$ can be moved below $`\alpha`$ while preserving the relations. (d) says that the relations to the upper end $`\beta`$ are moved to relations to the upper end $`\alpha`$.

## 6. Stable labels and height

**Definition (stable label).** A **stable label** of an array $`A`$ of length $`\ell`$ is a map $`f : \{0, \dots, \ell - 1\} \to \mathrm{Lab}`$ such that:

1. $`i \lt j \Rightarrow f(i) \lt f(j)`$
2. for $`k \lt r`$, $`j \prec_k i \Rightarrow f(j) \lhd_k f(i)`$

**Definition (height).** $`\mathrm{ht}(f) = f(\ell - 1)`$.

## 7. Proposition 19.1 (descent of the height)

**Proposition (DH).** Let $`A`$ be a nonempty array with a stable label $`f`$ and $`N \in \mathbb{N}`$. If $`A[N]`$ is nonempty, then $`A[N]`$ has a stable label $`g`$ with $`\mathrm{ht}(g) \lt \mathrm{ht}(f)`$.

**Outline of the proof.** If there is no parent, restrict $`f`$. If there is a parent, build the labels of $`G\, B_0 \cdots B_q`$ step by step in $`q`$.

1. Put $`\alpha = f(p)`$, $`\beta = f(c)`$ and $`y_i = f(p + i)`$. Since $`p \prec_{m_0} c`$, $`\alpha \lhd_{m_0} \beta`$
2. Let $`X`$ be the set of labels before $`B_q`$, apply finite reflection with $`n = m_0`$, and obtain $`y'`$
3. Replace the labels of $`B_q`$ by $`y'`$ instead of $`y`$, and put $`y`$ on the new $`B_{q+1}`$

The labels of the last copy $`B_N`$ are $`y_0, \dots, y_{s-1}`$, so $`\mathrm{ht}(g) = f(c - 1) \lt f(c)`$. That the ancestor relations are respected is checked using copy lemmas about the combinatorics of arrays.

Finite reflection is only invoked with $`n = m_0 \lt r`$.

## 8. How it is used in the proof

| Fact | Where |
|---|---|
| Standard arrays | [08](08-termination.md) |
| Label systems | shown to be satisfied in [06](06-finite-reflection.md) |
| Proposition 19.1 | [08](08-termination.md) |

## 9. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Arrays | `Arr` | [`Bm4/Defs.lean`](../../lean/Bm4/Defs.lean) |
| Candidates, parents | `cand`, `parentRel`, `parent` | same |
| Ancestors | `anc`, `ancEq` | same |
| Existence of a parent, $`m_0`$, $`p`$ | `LastHasParent`, `m₀`, `badRoot` | same |
| Expansion, expansion sequences | `dropLast`, `tildeCol`, `expand`, `seq` | same |
| Label systems | `LabelSystem` | [`Bm4/Label.lean`](../../lean/Bm4/Label.lean) |
| Stable labels, height | `Stable`, `ht` | same |
| Proposition 19.1 | `descent` | same |
| $`S^r_n`$, standard arrays | `stair`, `Std` | [`Pattern/Main.lean`](../../lean/Pattern/Main.lean) |
