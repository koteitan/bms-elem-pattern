[← Back](../README-en.md) | [English](04-pattern-properties.md) | [Japanese](../04-pattern-properties.md)

# Properties P1–P7 of R_N

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md), [02 Structures and elementary substructures](02-elementary-substructure.md), [03 R_N](03-patterns.md)

[06 Finite reflection](06-finite-reflection.md) uses only the following seven properties of $`\mathcal{R}_N`$. All of them follow from the definition of elementary substructures. For P2, the case $`j = 2`$ of P4, P6 and P7, assume $`N \ge 2`$.

| | Property |
|---|---|
| P1 | $`a \le b \le c \wedge a \le_1 c \Rightarrow a \le_1 b`$ |
| P2 | $`a \le_1 b \le_1 c \wedge a \le_2 c \Rightarrow a \le_2 b`$ |
| P3 | $`y \le \alpha`$, $`\alpha`$ closed under successor, $`\forall v \in [y, \alpha)\ y \le_1 v`$ $`\Rightarrow y \le_1 \alpha`$ |
| P4 | $`y \lt \alpha`$, $`S \subseteq [y, \alpha)`$ unbounded in $`\alpha`$, $`\forall v \in S\ y \le_j v`$ $`\Rightarrow y \le_j \alpha`$ ($`j \le 2`$) |
| P5 | $`\alpha \lt_1 \beta \Rightarrow \alpha`$ is closed under successor |
| P6 | $`y \lt_2 \beta \Rightarrow \beta`$ is closed under successor |
| P7 | $`\alpha \lt_2 \beta \Rightarrow \forall z \lt \alpha\ \exists u\ (z \lt u \lt \alpha \wedge u \le_1 \alpha)`$ |

$`S`$ is **unbounded** in $`\alpha`$ if for every $`z \lt \alpha`$ there is $`v \in S`$ with $`z \lt v`$.

## P1: ≤₁ is closed along ≤

**Proposition.** If $`a \le b \le c`$ and $`a \le_1 c`$, then $`a \le_1 b`$.

**Proof.** Take a $`\Sigma_1`$ formula $`\varphi`$ with parameters below $`a`$.

- If $`b \models \varphi`$, then $`c \models \varphi`$ by upward preservation, and $`a \models \varphi`$ by $`a \le_1 c`$
- If $`a \models \varphi`$, then $`b \models \varphi`$ by upward preservation

$`\square`$

**Meaning.** $`\{c : a \le_1 c\}`$ is an interval starting at $`a`$. The set $`\{\omega, \omega + 1\}`$ in [03](03-patterns.md) §4 is an example.

## P2: ≤₂ is closed along ≤₁

**Proposition.** If $`a \le_1 b`$, $`b \le_1 c`$ and $`a \le_2 c`$, then $`a \le_2 b`$.

**Proof.** Agreement on $`\Sigma_1`$ formulas follows from $`a \le_1 b`$. Take a $`\Sigma_2`$ formula $`\varphi = \exists \vec x\ \forall \vec z\ \psi`$ with parameters $`\vec p`$ below $`a`$.

- Suppose $`b \models \varphi`$. For a witness $`\vec x \lt b`$, $`b \models \forall \vec z\ \psi(\vec p, \vec x, \vec z)`$. This is a $`\Pi_1`$ formula with parameters below $`b`$, so it is also true in $`c`$ by $`b \le_1 c`$. Hence $`c \models \varphi`$, and $`a \models \varphi`$ by $`a \le_2 c`$
- Suppose $`a \models \varphi`$. For a witness $`\vec x \lt a`$, $`a \models \forall \vec z\ \psi(\vec p, \vec x, \vec z)`$. It is also true in $`b`$ by $`a \le_1 b`$, so $`b \models \varphi`$

$`\square`$

**Remark.** $`\le_2`$ is not closed along $`\le`$. According to Wilken, $`\upsilon_\omega \lt_2 \upsilon_\omega \cdot 2`$ and the least $`\lt_2`$-successor of $`\upsilon_\omega`$ is $`\upsilon_\omega \cdot 2`$, so $`\upsilon_\omega \le_2 \upsilon_\omega + 1`$ fails.

## P3: continuity of ≤₁

**Proposition.** Let $`y \le \alpha`$, let $`\alpha`$ be closed under successor, and suppose $`y \le_1 v`$ for all $`v \in [y, \alpha)`$. Then $`y \le_1 \alpha`$.

**Proof.** If $`y = \alpha`$, use reflexivity. Let $`y \lt \alpha`$ and take a $`\Sigma_1`$ formula $`\varphi`$ with parameters below $`y`$.

- Suppose $`\alpha \models \varphi`$. Take an upper bound $`z \lt \alpha`$ of the witnesses $`x_0, \dots, x_{b-1} \lt \alpha`$ ([01](01-ordinals.md) §2.1). $`v = \max(y, z + 1)`$ is below $`\alpha`$ because $`\alpha`$ is closed under successor, and all witnesses are below $`v`$, so $`v \models \varphi`$. By $`y \le_1 v`$, $`y \models \varphi`$
- If $`y \models \varphi`$, then $`\alpha \models \varphi`$ by upward preservation

$`\square`$

## P4: continuity along unbounded sets (levels 1 and 2)

**Proposition.** Let $`j \in \{1, 2\}`$ and $`y \lt \alpha`$. If $`S \subseteq [y, \alpha)`$ is unbounded in $`\alpha`$ and $`y \le_j v`$ for all $`v \in S`$, then $`y \le_j \alpha`$.

**Proof.** The case $`j = 1`$ is the same as the proof of P3, taking $`v`$ from $`S`$. Let $`j = 2`$ and take a $`\Sigma_2`$ formula $`\varphi = \exists \vec x\ \forall \vec z\ \psi`$ with parameters $`\vec p`$ below $`y`$. Agreement on $`\Sigma_1`$ formulas follows from the case $`j = 1`$.

- Suppose $`\alpha \models \varphi`$. Take $`v \in S`$ greater than the witnesses $`\vec x \lt \alpha`$. The $`\Pi_1`$ formula $`\forall \vec z\ \psi(\vec p, \vec x, \vec z)`$ is preserved downward, so it is true in $`v`$ and $`v \models \varphi`$. By $`y \le_2 v`$, $`y \models \varphi`$
- Suppose $`y \models \varphi`$. For a witness $`\vec x \lt y`$, $`y \models \forall \vec z\ \psi`$. If $`\alpha \models \exists \vec z\ \neg \psi(\vec p, \vec x, \vec z)`$, take $`v \in S`$ greater than its witness; then $`v \models \exists \vec z\ \neg \psi`$. By $`y \le_1 v`$, $`y \models \exists \vec z\ \neg \psi`$, a contradiction. Hence $`\alpha \models \varphi`$

$`\square`$

**Why the same argument fails at level 3.** For a $`\Sigma_3`$ formula $`\exists \vec x\ \forall \vec z\ \exists \vec w\ \psi`$, the first direction needs "$`\forall \vec z\ \exists \vec w\ \psi`$ true in $`\alpha`$ is also true in $`v`$". But for $`\vec z \lt v`$ the witness $`\vec w`$ may lie at or above $`v`$, so it cannot be brought down to $`v`$.

## P5: the lower end of <₁ is closed under successor

**Proposition.** If $`\alpha \lt_1 \beta`$, then $`\alpha`$ is closed under successor.

**Proof.** Suppose $`\alpha = z + 1`$. The $`\Sigma_1`$ formula $`\exists x\ (z \lt x)`$ with parameter $`z`$ is true in $`\beta`$ ($`x = \alpha`$) and false in $`\alpha`$, contradicting $`\alpha \le_1 \beta`$. $`\square`$

Example: there is no $`\beta`$ with $`3 \lt_1 \beta`$.

## P6: the upper end of <₂ is closed under successor

**Proposition.** If $`y \lt_2 \beta`$, then $`\beta`$ is closed under successor.

**Proof.** Suppose $`\beta = z + 1`$. The $`\Sigma_2`$ formula $`\sigma = \exists x\ \forall w\ (w \le x)`$ (there is a largest element) is true in $`\beta`$ ($`x = z`$). By $`y \le_2 \beta`$, $`y \models \sigma`$, so there is $`x_0 \lt y`$ with $`w \le x_0`$ for all $`w`$ below $`y`$. On the other hand $`y \lt_1 \beta`$, so $`y`$ is closed under successor by P5, and $`x_0 + 1 \lt y`$, a contradiction. $`\square`$

P5 is about the lower end, P6 about the upper end.

## P7: at the lower end of <₂, the ≤₁-predecessors are unbounded

**Proposition.** If $`\alpha \lt_2 \beta`$, then for every $`z \lt \alpha`$ there is $`u`$ with $`z \lt u \lt \alpha`$ and $`u \le_1 \alpha`$.

**Proof.** Consider the $`\Sigma_2`$ formula with parameter $`z`$

```math
\varphi(z) = \exists u\ \bigl(z \lt u \wedge \forall w\ (u \le w \Rightarrow u \le_1 w)\bigr) .
```

1. True in $`\beta`$: take $`u = \alpha`$. Since $`\alpha \le_1 \beta`$, P1 gives $`\alpha \le_1 w`$ for all $`w \in [\alpha, \beta)`$
2. By $`\alpha \le_2 \beta`$, $`\alpha \models \varphi(z)`$. The witness $`u \in (z, \alpha)`$ satisfies $`u \le_1 w`$ for all $`w \in [u, \alpha)`$
3. $`\alpha`$ is closed under successor by P5, so P3 gives $`u \le_1 \alpha`$

$`\square`$

## How it is used in the proof

| Property | Where |
|---|---|
| P1, P3, P5 | $`n = 1`$ and $`n = 2`$ in [06](06-finite-reflection.md) |
| P2, P4, P6, P7 | $`n = 2`$ in [06](06-finite-reflection.md) |

## Correspondence with Lean

The level index in Lean is shifted by one (`lev N 0` is $`\le_1`$).

| Property | Lean | File |
|---|---|---|
| P1 | `lev0_of_le` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
| P2 | `lev1_of_lev0` | same |
| P3 | `lev0_of_forall` | same |
| P4 | `elem_cofinal` | same |
| P5 | `succ_lt_of_lab0` | same |
| P6 | `succ_lt_of_lab1_top` | same |
| P7 | `exists_lev0_below` | same |
