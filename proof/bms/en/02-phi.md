[← Back](../README-en.md) | [English](02-phi.md) | [Japanese](../02-phi.md)

# The Formulas Φₘ: Connection to the Top, Seen from Inside

Prerequisites: [pss 04 Properties P1–P7 of R_N](../../pss/en/04-pattern-properties.md), [01 P4′ and P2′](01-cofinal-continuity.md)

## 1. What we need

Condition (d) of finite reflection says "if $`y_i \lt_{m+1} \beta`$ then $`y'_i \lt_{m+1} \alpha`$". We get $`y'_i`$ as a witness of a sentence true in $`\alpha`$, so we want to express "$`u \le_{m+1} \alpha`$" by a formula inside $`\alpha`$. But the right-hand $`\alpha`$ is the structure itself, not an element of it, so this is not a formula as it stands.

The formulas $`\Phi_m`$ of this note take its place. The formula $`\forall w\ (u \le w \Rightarrow u \le_1 w)`$ used in the proof of P7 in [pss 04](../../pss/en/04-pattern-properties.md) is $`\Phi_1`$.

## 2. Definition

**Definition.** In the structure $`(\gamma; \le, \le_1, \dots, \le_N)`$, define the formulas $`\Phi_m(u)`$ in one variable by

```math
\Phi_0(u) = \top
```

```math
\Phi_1(u) = \forall w\ \bigl(u \le w \Rightarrow u \le_1 w\bigr)
```

```math
\Phi_{m+2}(u) = \forall z\ \exists s\ \bigl(z \lt s \wedge u \le_{m+2} s \wedge \Phi_m(s)\bigr)
```

Quantifiers range below $`\gamma`$. We write "$`\Phi_m(u)`$ in $`\gamma`$" for $`\gamma \models \Phi_m(u)`$.

**Counting quantifiers.** For $`m \ge 1`$, $`\Phi_m`$ is a $`\Pi_m`$ formula.

- $`\Phi_1`$: quantifier-free after $`\forall w`$
- $`\Phi_2`$: $`\exists s\ (z \lt s \wedge u \le_2 s)`$ is $`\Sigma_1`$, and adding $`\forall z`$ gives $`\Pi_2`$
- $`\Phi_{m+2}`$ ($`m \ge 1`$): $`\Phi_m`$ is $`\Pi_m`$, so $`\exists s\ (\cdots \wedge \Phi_m(s))`$ is $`\Sigma_{m+1}`$, and adding $`\forall z`$ gives $`\Pi_{m+2}`$

That they can be written in Lean's form of formulas (lists of blocks) is shown in [03](03-block-form.md).

**Definition (unbounded predecessors).** For $`1 \le i \le N`$ put

```math
\mathrm{Cof}_i(\gamma) \iff \forall z \lt \gamma\ \exists s\ \bigl(z \lt s \lt \gamma \wedge s \le_i \gamma\bigr)
```

It says that the $`\le_i`$-predecessors of $`\gamma`$ are unbounded in $`\gamma`$. If $`i \le i'`$, then $`\mathrm{Cof}_{i'}(\gamma) \Rightarrow \mathrm{Cof}_i(\gamma)`$.

## 3. Lemma A: from Φₘ to ≤ₘ

**Lemma A.** Let $`\gamma`$ be closed under successor, $`1 \le m \le N`$ and $`u \lt \gamma`$. If $`\Phi_m(u)`$ holds in $`\gamma`$, then $`u \le_m \gamma`$.

**Proof.** Induction on $`m`$.

**Case $`m = 1`$.** $`u \le_1 w`$ for all $`w \in [u, \gamma)`$. P3 gives $`u \le_1 \gamma`$.

**Case $`m \ge 2`$.** Let $`S`$ be the set of all $`s`$ with

```math
u \lt s \lt \gamma, \qquad u \le_m s, \qquad \gamma \models \Phi_{m-2}(s)
```

1. $`S`$ is unbounded in $`\gamma`$: for $`z \lt \gamma`$, apply $`\Phi_m(u)`$ to $`\max(z, u)`$ to get $`s \in S`$ above $`z`$
2. If $`m \ge 3`$, the induction hypothesis gives $`s \le_{m-2} \gamma`$ for all $`s \in S`$. If $`m = 2`$, this condition holds automatically
3. P4′ ([01](01-cofinal-continuity.md)) with $`j = m`$ gives $`u \le_m \gamma`$

$`\square`$

## 4. Lemma B: from ≤ₘ to Φₘ

**Lemma B.** Let $`1 \le m \le N`$, $`u \lt \gamma`$ and $`u \le_m \gamma`$, and assume $`\mathrm{Cof}_i(\gamma)`$ for all $`1 \le i \le m - 1`$. Then $`\Phi_m(u)`$ holds in $`\gamma`$.

**Proof.** Induction on $`m`$.

**Case $`m = 1`$.** If $`w \in [u, \gamma)`$, then $`u \le w \le \gamma`$ and $`u \le_1 \gamma`$ give $`u \le_1 w`$ by P1.

**Case $`m \ge 2`$.** Take $`z \lt \gamma`$. By $`\mathrm{Cof}_{m-1}(\gamma)`$ there is $`s`$ with $`\max(z, u) \lt s \lt \gamma`$ and $`s \le_{m-1} \gamma`$. We show that $`s`$ is a witness for $`z`$.

1. $`u \le s \le \gamma`$, $`u \le_m \gamma`$ and $`s \le_{m-1} \gamma`$, so the corollary of [01](01-cofinal-continuity.md) §4 gives $`u \le_m s`$
2. If $`m \ge 3`$, then $`s \le_{m-2} \gamma`$ and $`\mathrm{Cof}_i(\gamma)`$ for $`i \le m - 3`$ give $`\gamma \models \Phi_{m-2}(s)`$ by the induction hypothesis. If $`m = 2`$, $`\Phi_0`$ is true

$`\square`$

## 5. Summary

If $`\gamma`$ is closed under successor and $`\mathrm{Cof}_i(\gamma)`$ holds for all $`i \lt m`$, then for $`u \lt \gamma`$

```math
\gamma \models \Phi_m(u) \iff u \le_m \gamma
```

For $`m = 1`$ there is no $`\mathrm{Cof}`$ condition, and this restates P1 and P3.

## 6. Where it is used

| Lemma | Used in |
|---|---|
| Lemma A | steps C and E of [04](04-cofinal-predecessors.md), "true in β" of [05](05-finite-reflection.md) |
| Lemma B | steps A and D of [04](04-cofinal-predecessors.md), "(d) in α" of [05](05-finite-reflection.md) |

## 7. Lean correspondence

`Phi N γ m u` in Lean is not a formula but a proposition that directly states the meaning of $`\Phi_m(u)`$ evaluated in $`\gamma`$. That it is expressed by a formula is `tn_sig` of [03](03-block-form.md). `Cof N j γ` is $`\mathrm{Cof}_{j+1}(\gamma)`$.

| Concept | Lean | File |
|---|---|---|
| $`\Phi_m`$ | `Phi` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| $`\mathrm{Cof}_i`$ | `Cof`, `Cof.mono` | same |
| Lemma A | `lev_of_phi` | same |
| Lemma B | `phi_of_lev` | same |
| P3 | `lev0_of_forall` | [`Pattern/Basic.lean`](../../../lean/Pattern/Basic.lean) |
