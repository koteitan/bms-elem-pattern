[← Back](../README-en.md) | [English](01-ordinals.md) | [Japanese](../01-ordinals.md)

# Ordinals and ω₁

Prerequisites: none

## 1. Ordinals and infinite descending sequences

**Definition (well-order).** A linear order $`\lt`$ on a set $`X`$ is a **well-order** if every nonempty subset of $`X`$ has a least element.

**Definition (ordinal).** An ordinal is the order type of a well-order. An ordinal $`\alpha`$ is identified with the set $`\{\beta : \beta \lt \alpha\}`$ of smaller ordinals. Below, "an element of $`\alpha`$" and "an ordinal below $`\alpha`$" mean the same thing.

| Ordinal | Smaller ordinals |
|---|---|
| $`0`$ | none |
| $`3`$ | $`0, 1, 2`$ |
| $`\omega`$ | $`0, 1, 2, \dots`$ |
| $`\omega + 1`$ | $`0, 1, 2, \dots, \omega`$ |
| $`\omega \cdot 2`$ | $`0, 1, 2, \dots, \omega, \omega + 1, \omega + 2, \dots`$ |

The class of all ordinals is also well-ordered by $`\lt`$.

**Theorem (no infinite descending sequence).** There is no sequence of ordinals $`\alpha_0 \gt \alpha_1 \gt \alpha_2 \gt \cdots`$.

**Proof.** Suppose there is one, and let $`\alpha_{t_0}`$ be the least element of $`\{\alpha_t : t \in \mathbb{N}\}`$. Then $`\alpha_{t_0 + 1}`$ is also in this set and $`\alpha_{t_0 + 1} \lt \alpha_{t_0}`$, contradicting minimality. $`\square`$

The termination proof finally reduces to this theorem ([08](08-termination.md)).

## 2. Successors and ordinals closed under successor

**Definition.** $`\alpha + 1`$ is the least ordinal greater than $`\alpha`$. An ordinal of the form $`\alpha = \beta + 1`$ is a **successor ordinal**, and an ordinal that is neither $`0`$ nor a successor ordinal is a **limit ordinal**.

**Definition (closed under successor).** An ordinal $`\alpha`$ is **closed under successor** if the following holds.

```math
\forall z \lt \alpha\ \ (z + 1 \lt \alpha)
```

Being closed under successor is the same as $`\alpha = 0`$ or $`\alpha`$ being a limit ordinal: if $`\alpha = \beta + 1`$, the condition fails at $`z = \beta`$.

| $`\alpha`$ | Closed under successor? | Reason |
|---|---|---|
| $`0`$ | yes | there is no $`z \lt 0`$ |
| $`3`$ | no | $`2 + 1 = 3`$ |
| $`\omega`$ | yes | $`n + 1 \lt \omega`$ |
| $`\omega + 1`$ | no | $`\omega + 1`$ itself |
| $`\omega \cdot 2`$ | yes | $`\omega + n + 1 \lt \omega \cdot 2`$ |

The following notes use this phrase instead of "limit", so that $`0`$ needs no separate case.

### 2.1 An upper bound for finitely many ordinals

**Lemma.** Let $`0 \lt \alpha`$ and $`x_0, \dots, x_{b-1} \lt \alpha`$. Then there is $`z \lt \alpha`$ with $`x_i \le z`$ for all $`i \lt b`$.

**Proof.** Take $`z = \max_i x_i`$ if $`b \gt 0`$, and $`z = 0`$ if $`b = 0`$. $`\square`$

If $`\alpha`$ is closed under successor, then $`z + 1 \lt \alpha`$, so below $`\alpha`$ there is an ordinal strictly greater than all $`x_i`$.

## 3. Countable ordinals and ω₁

**Definition.** A set is **countable** if it is finite or in one-to-one correspondence with the natural numbers.

**Definition (ω₁).** $`\omega_1`$ is the least ordinal such that the set of smaller ordinals is not countable. It is also written $`\Omega_1`$.

We use the following four facts.

**Fact 1.** $`\gamma \lt \omega_1`$ if and only if the set of ordinals below $`\gamma`$ is countable.

**Fact 2.** $`\omega_1`$ is closed under successor, because if the ordinals below $`\gamma`$ are countably many, so are the ordinals below $`\gamma + 1`$.

**Fact 3 (regularity).** The supremum of countably many ordinals $`\gamma_i \lt \omega_1`$ is below $`\omega_1`$, because a countable union of countable sets is countable (this uses the axiom of choice).

**Fact 4 (enumeration).** If $`0 \lt \gamma \lt \omega_1`$, there is a surjection $`e : \mathbb{N} \to \gamma`$ from the natural numbers onto the ordinals below $`\gamma`$.

By Fact 4, finite sequences of ordinals below $`\gamma`$ can be indexed by finite sequences of natural numbers. This is used in [07](07-closure-chains.md).

| Ordinal | Below $`\omega_1`$? |
|---|---|
| $`\omega`$, $`\omega^2`$, $`\varepsilon_0`$ | yes |
| $`\psi_0(\Omega_\omega)`$ (the ordinal of pair sequences) | yes |
| $`\omega_1`$ | no |

## 4. Aside: recursive ordinals and admissible ordinals

Not used in the proof, but they appear when discussing the size of the labels.

An ordinal that is the order type of a computable well-order is called a **recursive ordinal**, and the supremum of the recursive ordinals is written $`\omega_1^{\mathrm{CK}}`$. $`\omega_1^{\mathrm{CK}}`$ is the least admissible ordinal greater than $`\omega`$, and $`\omega_1^{\mathrm{CK}} \lt \omega_1`$. Hence ordinals greater than $`\omega`$ and less than $`\omega_1^{\mathrm{CK}}`$ are not admissible.

## 5. How it is used in the proof

| Fact | Where |
|---|---|
| No infinite descending sequence | [08](08-termination.md) termination |
| Closed under successor | [04](04-pattern-properties.md) P3, P5, P6 |
| Upper bound for finitely many ordinals | [04](04-pattern-properties.md) P3, P4 |
| Facts 1–4 | [07](07-closure-chains.md) closure |

## 6. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Ordinals | `Ordinal.{0}` | Mathlib |
| $`z + 1`$ | `Order.succ z` | Mathlib |
| Upper bound for finitely many ordinals | `exists_bound` | [`Pattern/Basic.lean`](../../../lean/Pattern/Basic.lean) |
| $`\omega_1`$ | `Om` | [`Pattern/Chain.lean`](../../../lean/Pattern/Chain.lean) |
| Fact 1 | `countable_Iio` | same |
| Fact 2 | `om_succ_lt` | same |
| Fact 3 | `Ordinal.iSup_lt_omega_one` | Mathlib |
| Fact 4 | `enumBelow`, `enumBelow_surj` | [`Pattern/Chain.lean`](../../../lean/Pattern/Chain.lean) |
| No infinite descending sequence | `WellFounded.has_min` | Mathlib |
