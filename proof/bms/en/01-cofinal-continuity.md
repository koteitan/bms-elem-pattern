[← Back](../README-en.md) | [English](01-cofinal-continuity.md) | [Japanese](../01-cofinal-continuity.md)

# P4′ and P2′: Continuity and Closure at Every Level

Prerequisites: [pss 02 Structures and elementary substructures](../../pss/en/02-elementary-substructure.md), [pss 03 R_N](../../pss/en/03-patterns.md), [pss 04 Properties P1–P7 of R_N](../../pss/en/04-pattern-properties.md)

## 1. What we need

Finite reflection up to 3 rows used P2 ($`\le_2`$ is closed along $`\le_1`$) and P4 (continuity along an unbounded set, levels 1 and 2) of [pss 04](../../pss/en/04-pattern-properties.md). Finite reflection at every level needs both of them at every level.

P4 cannot be shown at level 3 in its original form (the remark after P4 in [pss 04](../../pss/en/04-pattern-properties.md)). In this note we show that it holds at every level once the condition $`v \le_{j-2} \alpha`$ is added for the elements $`v`$ of $`S`$.

**Notation.** Read $`\le_0`$ and $`\le_{-1}`$ as $`\le`$. So for $`j \le 2`$ the condition $`v \le_{j-2} \alpha`$ holds automatically when $`v \lt \alpha`$.

Formulas have the form $`\exists \vec x_1\ \neg\, \exists \vec x_2\ \neg \cdots`$ of [pss 02](../../pss/en/02-elementary-substructure.md) §5, and $`\le_j`$ is decided by "formulas with at most $`j`$ blocks have the same truth value".

## 2. P4′: continuity along an unbounded set

**Proposition (P4′).** Let $`1 \le j \le N`$ and $`y \lt \alpha`$. If $`S \subseteq [y, \alpha)`$ is unbounded in $`\alpha`$ and every $`v \in S`$ satisfies

```math
y \le_j v \wedge v \le_{j-2} \alpha
```

then $`y \le_j \alpha`$.

For $`j = 1, 2`$ the second condition holds automatically, so this is P4.

**Proof.** Take a formula $`\varphi`$ with parameters $`\vec p`$ below $`y`$ and at most $`j`$ blocks, and show $`y \models \varphi \iff \alpha \models \varphi`$. With 0 blocks it is quantifier-free, so its truth value is decided by the atomic diagram of $`\vec p`$ and the two sides agree.

**One block.** Write $`\varphi = \exists \vec x\ \psi`$ ($`\psi`$ quantifier-free).

- If $`y \models \varphi`$, then $`\alpha \models \varphi`$ by upward persistence
- Suppose $`\alpha \models \varphi`$. Take $`v \in S`$ above all the witnesses $`\vec x \lt \alpha`$; then $`v \models \varphi`$, and $`y \le_j v`$ gives $`y \models \varphi`$

**Two or more blocks.** Write $`\varphi = \exists \vec x\ \neg\, \exists \vec z\ \neg\, \chi`$. Then $`\chi`$ has at most $`j - 2`$ blocks.

Suppose $`y \models \varphi`$ with witness $`\vec x \lt y`$, that is, $`y \models \neg\, \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$. To show $`\alpha \models \varphi`$, assume $`\alpha \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$ and derive a contradiction.

1. Take $`v \in S`$ above all the witnesses $`\vec z \lt \alpha`$. Since $`\vec p, \vec x \lt y \le v`$, all parameters are below $`v`$
2. $`\chi`$ has at most $`j - 2`$ blocks, so $`v \le_{j-2} \alpha`$ gives $`v \models \neg\, \chi(\vec p, \vec x, \vec z)`$
3. Hence $`v \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$. This has at most $`j - 1`$ blocks, so $`y \le_j v`$ makes it true in $`y`$
4. This contradicts the choice of $`\vec x`$

Suppose $`\alpha \models \varphi`$ with witness $`\vec x \lt \alpha`$. Take $`v \in S`$ above all of $`\vec x`$ and show $`v \models \varphi`$.

1. Assume $`v \models \exists \vec z\ \neg\, \chi(\vec p, \vec x, \vec z)`$ with witness $`\vec z \lt v`$
2. $`v \le_{j-2} \alpha`$ gives $`\alpha \models \neg\, \chi(\vec p, \vec x, \vec z)`$, contradicting the choice of $`\vec x`$
3. So $`\vec x`$ is a witness in $`v`$ and $`v \models \varphi`$. $`y \le_j v`$ gives $`y \models \varphi`$

$`\square`$

**Why the condition helps.** As seen in [pss 04](../../pss/en/04-pattern-properties.md), without the condition, bringing an inner formula true in $`\alpha`$ down to $`v`$ may need witnesses at or above $`v`$. With $`v \le_{j-2} \alpha`$, the inner $`\chi`$ has the same truth value in $`v`$ and $`\alpha`$, so no witness has to be brought down.

## 3. P2′: ≤ₘ₊₁ is closed along ≤ₘ

**Proposition (P2′).** Let $`1 \le m \lt N`$. If $`a \le b \le c`$, $`a \le_m b`$, $`b \le_m c`$ and $`a \le_{m+1} c`$, then $`a \le_{m+1} b`$.

$`m = 1`$ is P2. Reading $`m = 0`$ gives P1.

**Proof.** Take a formula with parameters $`\vec p`$ below $`a`$ and at most $`m + 1`$ blocks. With 0 blocks it is clear, so write $`\varphi = \exists \vec x\ \neg\, \psi`$, where $`\psi`$ has at most $`m`$ blocks.

- Suppose $`a \models \varphi`$ with witness $`\vec x \lt a`$. Then $`a \models \neg\, \psi(\vec p, \vec x)`$, and $`a \le_m b`$ gives $`b \models \neg\, \psi(\vec p, \vec x)`$. Hence $`b \models \varphi`$
- Suppose $`b \models \varphi`$ with witness $`\vec x \lt b`$. Then $`b \models \neg\, \psi(\vec p, \vec x)`$, and $`b \le_m c`$ gives $`c \models \neg\, \psi(\vec p, \vec x)`$. Hence $`c \models \varphi`$, and $`a \le_{m+1} c`$ gives $`a \models \varphi`$

$`\square`$

## 4. Corollary: between points connected to the top

**Corollary.** Let $`1 \le m \le N`$. If $`u \le s \le \gamma`$, $`u \le_m \gamma`$ and $`s \le_{m-1} \gamma`$, then $`u \le_m s`$.

**Proof.** Induction on $`m`$.

- $`m = 1`$: this is P1
- $`m + 1`$: $`u \le_{m+1} \gamma`$ gives $`u \le_m \gamma`$, and $`s \le_m \gamma`$ gives $`s \le_{m-1} \gamma`$. By the induction hypothesis $`u \le_m s`$. P2′ with $`a = u`$, $`b = s`$, $`c = \gamma`$ gives $`u \le_{m+1} s`$

$`\square`$

**Reading.** A point $`u`$ with $`u \le_m \gamma`$ is $`\le_m`$-related to every $`s \ge u`$ with $`s \le_{m-1} \gamma`$.

## 5. Where it is used

| Property | Used in |
|---|---|
| P4′ | Lemma A of [02](02-phi.md), (d) in [05](05-finite-reflection.md) |
| Corollary of §4 | Lemma B of [02](02-phi.md), "true in β" in [05](05-finite-reflection.md) |

## 6. Lean correspondence

Lean's level numbers are shifted by one (`lev N 0` is $`\le_1`$). `Elem R j a b` means that formulas with at most $`j`$ blocks have the same truth value.

| Property | Lean | File |
|---|---|---|
| P4′ | `elem_cofinal_gen` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| P2′ | `elem_of_elem_top`, `lev_of_lev_top` | same |
| Corollary of §4 | `lev_below_top` | same |
| P1, P4 (levels 1, 2) | `lev0_of_le`, `elem_cofinal` | [`Pattern/Basic.lean`](../../../lean/Pattern/Basic.lean) |
