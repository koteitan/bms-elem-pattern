[← Back](../README-en.md) | [English](04-cofinal-predecessors.md) | [Japanese](../04-cofinal-predecessors.md)

# P7′: Predecessors Are Unbounded at the Lower End

Prerequisites: [pss 04 Properties P1–P7 of R_N](../../pss/en/04-pattern-properties.md), [02 The formulas Φₘ](02-phi.md), [03 Writing coordinatewise conditions in block form](03-block-form.md)

## 1. Statement

**Proposition (P7′).** Let $`1 \le m \lt N`$ and $`\alpha \lt_{m+1} \beta`$. Then $`\mathrm{Cof}_i(\alpha)`$ holds for all $`1 \le i \le m`$:

```math
\forall z \lt \alpha\ \exists s\ \bigl(z \lt s \lt \alpha \wedge s \le_i \alpha\bigr)
```

$`m = 1`$ is P7. Finite reflection for 3 rows used only P7. Finite reflection at every level needs this proposition in order to apply Lemma B of [02](02-phi.md) in $`\alpha`$.

**Remark.** If $`\alpha \lt_j \beta`$, then $`\alpha \gt 0`$: the $`\Sigma_1`$ sentence $`\exists x\ (x \le x)`$ is true in $`\beta`$ ($`x = \alpha`$), hence true in $`\alpha`$. The lemma of [03](03-block-form.md) uses this.

## 2. Proof

Induction on $`m`$. $`m = 1`$ is P7.

Let $`m + 1 \lt N`$ and $`\alpha \lt_{m+2} \beta`$. Since $`\alpha \lt_{m+1} \beta`$, the induction hypothesis gives $`\mathrm{Cof}_i(\alpha)`$ for all $`i \le m`$. We show $`\mathrm{Cof}_{m+1}(\alpha)`$.

Facts used:

- $`\alpha \lt_1 \beta`$, so $`\alpha`$ is closed under successor by P5
- $`\alpha \lt_2 \beta`$, so $`\beta`$ is closed under successor by P6
- the following $`\tau`$ is a $`\Pi_{m+2}`$ sentence without parameters, and its negation is the $`\Sigma_{m+2}`$ sentence (2) of [03](03-block-form.md) §4

```math
\tau = \forall z\ \exists u\ \bigl(z \lt u \wedge \Phi_m(u)\bigr)
```

**Step A: τ in α.** Take $`z \lt \alpha`$. By $`\mathrm{Cof}_m(\alpha)`$ there is $`u`$ with $`z \lt u \lt \alpha`$ and $`u \le_m \alpha`$. Since $`\mathrm{Cof}_i(\alpha)`$ holds for $`i \lt m`$, Lemma B gives $`\alpha \models \Phi_m(u)`$.

**Step B: τ in β.** $`\alpha \le_{m+2} \beta`$, and $`\neg\, \tau`$ is a $`\Sigma_{m+2}`$ sentence without parameters, so it has the same truth value in $`\alpha`$ and $`\beta`$. By step A, $`\beta \models \tau`$.

**Step C: Cof_m(β).** Take $`z \lt \beta`$. By step B there is $`u`$ with $`z \lt u \lt \beta`$ and $`\beta \models \Phi_m(u)`$. $`\beta`$ is closed under successor, so Lemma A gives $`u \le_m \beta`$.

**Step D: Φ_{m+1}(α) in β.** $`\alpha \lt \beta`$ and $`\alpha \le_{m+1} \beta`$. By step C, $`\mathrm{Cof}_i(\beta)`$ holds for all $`i \le m`$, so Lemma B gives $`\beta \models \Phi_{m+1}(\alpha)`$.

**Step E: back to α.** Take $`z \lt \alpha`$. The $`\Sigma_{m+2}`$ sentence with parameter $`z`$ ((1) of [03](03-block-form.md) §4)

```math
\exists u\ \bigl(z \lt u \wedge \Phi_{m+1}(u)\bigr)
```

is true in $`\beta`$ by step D ($`u = \alpha`$). By $`\alpha \le_{m+2} \beta`$ it is true in $`\alpha`$, with a witness $`u`$ such that $`z \lt u \lt \alpha`$ and $`\alpha \models \Phi_{m+1}(u)`$. $`\alpha`$ is closed under successor, so Lemma A gives $`u \le_{m+1} \alpha`$.

$`\square`$

**Reading.** "The $`\le_{m+1}`$-predecessors of $`\alpha`$ are unbounded" cannot be said by a formula inside $`\alpha`$. So the proof goes as follows.

1. Lift "points satisfying $`\Phi_m`$ are unbounded", which can be said inside $`\alpha`$, to $`\beta`$
2. On the side of $`\beta`$, get $`\mathrm{Cof}_m(\beta)`$ and show that $`\alpha`$ itself satisfies $`\Phi_{m+1}`$ in $`\beta`$
3. Bring "there is a point above $`z`$ satisfying $`\Phi_{m+1}`$" back to $`\alpha`$

## 3. Where it is used

| Fact | Used in |
|---|---|
| P7′ | "(d) in α" of [05](05-finite-reflection.md), to take points satisfying $`\Phi_{n-1}`$ unboundedly in $`\alpha`$ |

## 4. Lean correspondence

In `cof_of_lab j h`, the hypothesis `lab N (j + 1) α β` is $`\alpha \lt_{j+2} \beta`$ and the conclusion `Cof N i α` is $`\mathrm{Cof}_{i+1}(\alpha)`$.

| Concept | Lean | File |
|---|---|---|
| $`\alpha \gt 0`$ | `pos_of_lab` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| P7′ | `cof_of_lab` | same |
| Negation of $`\tau`$, the sentence of step E | `sig_forall_exists_phi`, `sig_exists_phi` | same |
| P5, P6, P7 | `succ_lt_of_lab0`, `succ_lt_of_lab1_top`, `exists_lev0_below` | [`Pattern/Basic.lean`](../../../lean/Pattern/Basic.lean) |
