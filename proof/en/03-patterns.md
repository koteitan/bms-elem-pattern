[← Back](../README-en.md) | [English](03-patterns.md) | [Japanese](../03-patterns.md)

# R_N (Elementary Patterns of Resemblance)

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md), [02 Structures and elementary substructures](02-elementary-substructure.md)

## 1. Definition

**Definition (Carlson).** Let $`N \ge 1`$. The relations $`\le_1, \dots, \le_N`$ on ordinals are defined simultaneously by the following formula.

```math
\alpha \le_j \beta \iff \alpha \le \beta \wedge (\alpha; \le, \le_1, \dots, \le_N) \preceq_{\Sigma_j} (\beta; \le, \le_1, \dots, \le_N) \qquad (1 \le j \le N)
```

```math
\mathcal{R}_N = (\mathrm{Ord}; \le, \le_1, \dots, \le_N), \qquad \alpha \lt_j \beta \iff \alpha \lt \beta \wedge \alpha \le_j \beta
```

The structures $`\mathcal{R}_2`$ and $`\mathcal{R}_3`$ in Wilken's papers are the cases $`N = 2, 3`$.

**Reading.** $`\alpha \le_j \beta`$ says that the "shape" of the ordinals below $`\alpha`$ cannot be distinguished by $`\Sigma_j`$ formulas even when extended up to $`\beta`$. Here the shape consists of the order and of the relations $`\le_1, \dots, \le_N`$ themselves.

## 2. Why the definition makes sense

The right-hand side uses the relations $`\le_1, \dots, \le_N`$ that are being defined on the left. This looks circular, but the relations are determined by induction on $`\beta`$.

The relations appearing in the two structures on the right-hand side are only $`a \le_i b`$ between two elements $`a, b`$ below $`\beta`$. Since $`b \lt \beta`$, these are already determined at the earlier stage $`b`$. So at stage $`\beta`$ it suffices to decide $`\alpha \le_j \beta`$ for all $`\alpha \le \beta`$, using the relations already determined.

By this construction, the truth value of $`a \le_i b`$ is the same in every structure $`(\gamma; \ldots)`$ containing $`a, b`$, because the relations of the structures are restrictions of the global relations.

In Lean, these relations are defined by well-founded recursion on $`\beta`$, and the defining formula is extracted as a lemma. The key lemma is that "a formula evaluated below $`\beta`$ only looks at the relations between pairs below $`\beta`$".

## 3. Basic properties

**Proposition.** Let $`1 \le j \le N`$.

1. $`\alpha \le_j \alpha`$
2. If $`\alpha \le_j \beta`$ and $`\beta \le_j \gamma`$, then $`\alpha \le_j \gamma`$
3. If $`j \lt N`$ and $`\alpha \le_{j+1} \beta`$, then $`\alpha \le_j \beta`$

**Proof.** 1 is clear since the two structures are the same. 2 is the transitivity in [02](02-elementary-substructure.md) §4. 3 follows because a $`\Sigma_{j+1}`$-elementary substructure is a $`\Sigma_j`$-elementary substructure. $`\square`$

By 3, $`\alpha \lt_{j+1} \beta`$ implies $`\alpha \lt_j \beta`$.

## 4. Small examples

Below, $`N \ge 1`$ is arbitrary.

**Example 1.** For natural numbers $`n \lt m`$, $`n \le_1 m`$ fails. Likewise $`n \le_1 \omega`$ fails.

- If $`n \ge 1`$: the $`\Sigma_1`$ formula $`\exists x\ (n - 1 \lt x)`$ with parameter $`n - 1`$ is true in $`m`$ ($`x = n`$) and false in $`n`$
- If $`n = 0`$: $`\exists x\ (x \le x)`$ is true in $`m`$ and false in the empty structure $`0`$

**Example 2.** $`\omega \lt_1 \omega + 1`$.

By Example 1 and item 3 of §3, no $`\le_j`$ holds between two distinct elements below $`\omega + 1`$. So in $`(\omega; \ldots)`$ and $`(\omega + 1; \ldots)`$ the atomic formula $`x \le_j y`$ means the same as $`x = y`$. Then being a $`\Sigma_1`$-elementary substructure is the same question as for structures with $`\le`$ only, and it holds by the example in [02](02-elementary-substructure.md) §4.2.

**Example 3.** $`\omega \le_2 \omega + 1`$ fails, because the $`\Sigma_2`$ formula "there is a largest element" is true in $`\omega + 1`$ and false in $`\omega`$.

**Example 4.** $`\omega \le_1 \omega + 2`$ fails. The $`\Sigma_1`$ formula $`\exists x\ \exists y\ (x \lt y \wedge x \le_1 y)`$ is true in $`\omega + 2`$ by Example 2 ($`x = \omega`$, $`y = \omega + 1`$), and false in $`\omega`$ by Example 1.

Hence $`\{\beta : \omega \le_1 \beta\} = \{\omega, \omega + 1\}`$.

## 5. What is known from the literature

Not used in the proof. Used when discussing the size of the labels.

- The least $`\lt_2`$ pair in $`\mathcal{R}_2`$ is $`\varepsilon_0 \cdot \omega \lt_2 \varepsilon_0 \cdot (\omega + 1)`$
- Consider the sequence $`\upsilon_0 = 0`$, $`\upsilon_{\xi + 1} = \upsilon_\xi^\infty`$, $`\upsilon_\lambda = \sup_{\iota \lt \lambda} \upsilon_\iota`$. Here $`\upsilon_\xi^\infty`$ is the countable part of a relativized Buchholz-style notation system built on $`\upsilon_\xi`$, and $`\upsilon_1 = \psi_0(\Omega_\omega)`$
- In $`\mathcal{R}_2`$, for the set $`I`$ of indices $`\iota \gt 1`$ not of the form "limit + 1", $`(\upsilon_\iota)_{\iota \in I}`$ is the maximal $`\lt_2`$ chain
- $`\psi_0(\Omega_\omega)`$ is the least ordinal below which finite $`\le_2`$ chains of arbitrary length exist
- The least $`\lt_3`$ pair in $`\mathcal{R}_3`$ is $`\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2 + 2}`$
- On the initial segment $`\upsilon_{\omega^2 + 2}`$, the relations of $`\mathcal{R}_2`$ and $`\mathcal{R}_3`$ agree

Sources:

- G. Wilken, Pure Σ2-elementarity beyond the core, Annals of Pure and Applied Logic 172 (2021). https://doi.org/10.1016/j.apal.2021.103001
- G. Wilken, Tracking chains revisited. https://arxiv.org/abs/1611.04348
- G. Wilken, Pure Σ2-Elementarity beyond the Core, Section 4 of arXiv version v1. https://arxiv.org/abs/1710.01870v1

## 6. How it is used in the proof

| Fact | Where |
|---|---|
| Definition | label relations $`\lhd_k = \lt_{k+1}`$ ([06](06-finite-reflection.md)) |
| Reflexivity, transitivity, monotonicity in the level | [04](04-pattern-properties.md), [06](06-finite-reflection.md), [08](08-termination.md) |

## 7. Correspondence with Lean

In Lean, the level index is shifted by one: `lev N j a b` is $`a \le_{j+1} b`$ and `lab N j a b` is $`a \lt_{j+1} b`$.

| Concept | Lean | File |
|---|---|---|
| Recursion of the definition | `stage`, `RFix`, `RN` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
| $`\le_{j+1}`$, $`\lt_{j+1}`$ | `lev N j`, `lab N j` | same |
| Defining formula | `rel_iff`, `lev_iff` | same |
| Only pairs below $`\beta`$ matter | `sig_congr`, `stage_agree`, `elem_congr` | same |
| Items 1, 2, 3 of §3 | `lev_refl`, `lev_trans`, `lev_mono` | same |
| Transitivity and monotonicity for $`\lt`$ | `lab_trans`, `lab_mono` | same |
