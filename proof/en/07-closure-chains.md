[← Back](../README-en.md) | [English](07-closure-chains.md) | [Japanese](../07-closure-chains.md)

# Closure inside ω₁ and Chains Related at Every Level

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md), [02 Structures and elementary substructures](02-elementary-substructure.md), [03 R_N](03-patterns.md)

## 1. What is needed

To label the $`n + 1`$ columns of $`S^r_n`$, we need ordinals $`c_0 \lt c_1 \lt \cdots \lt c_n`$ any two of which are related by all of $`\le_1, \dots, \le_r`$ ([08](08-termination.md)). This note shows that such chains exist in every length.

## 2. One step of the closure

**Indexing formulas.** A formula of the form in [02](02-elementary-substructure.md) §5 is determined by the number $`n`$ of positions of the atomic diagram, the set $`D`$ of atomic diagrams, the list of block lengths, and the number $`k`$ of parameters. Since there are finitely many atomic diagrams, the set of all formulas is countable.

**Indexing parameters.** If $`0 \lt \gamma \lt \omega_1`$, there is a surjection $`e : \mathbb{N} \to \gamma`$ ([01](01-ordinals.md) Fact 4). A finite sequence of ordinals below $`\gamma`$ can be written as $`(e(t_0), \dots, e(t_{k-1}))`$ for a finite sequence of natural numbers $`(t_0, \dots, t_{k-1})`$.

**Definition (next).** For each pair of a formula and a sequence of parameter indices, consider the following value.

- If the formula is true in $`\omega_1`$, choose a witness $`x_0, \dots, x_{b-1}`$ of its first block and take $`\max_i (x_i + 1)`$
- If it is false, take $`0`$

Let $`\mathrm{next}(\gamma)`$ be the larger of $`\gamma`$ and the supremum of all these values, plus $`1`$.

**Lemma.** If $`\gamma \lt \omega_1`$, then $`\gamma \lt \mathrm{next}(\gamma) \lt \omega_1`$.

**Proof.** Each value is below $`\omega_1`$ (the witnesses are below $`\omega_1`$, and Fact 2). There are countably many pairs, so the supremum is below $`\omega_1`$ by Fact 3. Finally use Fact 2. $`\square`$

**Lemma (witnesses lie below next).** If a formula $`\mathrm{Sig}([b_1, b_2, \dots, b_r], \vec p)`$ with all parameters below $`\gamma`$ is true in $`\omega_1`$, then there are $`x_0, \dots, x_{b_1 - 1} \lt \mathrm{next}(\gamma)`$ such that $`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ is false in $`\omega_1`$.

**Proof.** Represent the parameters by indices and take the witness chosen in the definition. $`\square`$

## 3. λ(γ)

**Definition.**

```math
\lambda(\gamma) = \sup_{t \lt \omega} \mathrm{next}^t(\gamma)
```

If $`\gamma \lt \omega_1`$, Fact 3 gives $`\gamma \lt \lambda(\gamma) \lt \omega_1`$.

**Lemma.** Finitely many ordinals below $`\lambda(\gamma)`$ are all below $`\mathrm{next}^t(\gamma)`$ for some $`t`$.

**Proof.** For each ordinal some $`t`$ works, and $`\mathrm{next}^t(\gamma)`$ is increasing in $`t`$, so take the largest. $`\square`$

**Theorem.** Let $`\gamma \lt \omega_1`$. Every formula with all parameters below $`\lambda(\gamma)`$ has the same truth value in $`\lambda(\gamma)`$ and in $`\omega_1`$.

**Proof.** By induction on the number of blocks.

**No blocks.** The truth value is determined by the atomic diagram alone and does not depend on the structure.

**Blocks $`[b_1, b_2, \dots, b_r]`$.**

- Suppose it is true in $`\lambda(\gamma)`$. There is a witness $`\vec x \lt \lambda(\gamma)`$ with $`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ false in $`\lambda(\gamma)`$. The parameters $`\vec p\,\vec x`$ are below $`\lambda(\gamma)`$, so by the induction hypothesis it is also false in $`\omega_1`$. Since $`\vec x \lt \omega_1`$, the formula is true in $`\omega_1`$
- Suppose it is true in $`\omega_1`$. The parameters can be taken below $`\mathrm{next}^t(\gamma)`$. By the lemma of §2 there is $`\vec x \lt \mathrm{next}^{t+1}(\gamma) \le \lambda(\gamma)`$ with $`\mathrm{Sig}([b_2, \dots, b_r], \vec p\,\vec x)`$ false in $`\omega_1`$. By the induction hypothesis it is also false in $`\lambda(\gamma)`$, so the formula is true in $`\lambda(\gamma)`$

$`\square`$

This is the Löwenheim–Skolem–Tarski argument carried out in the form of an initial segment.

## 4. Chains

**Corollary.** If $`\gamma, \delta \lt \omega_1`$ and $`\lambda(\gamma) \lt \lambda(\delta)`$, then $`\lambda(\gamma) \lt_j \lambda(\delta)`$ for all $`j \le N`$.

**Proof.** A formula with parameters below $`\lambda(\gamma)`$ agrees between $`\lambda(\gamma)`$ and $`\omega_1`$ by the theorem of §3, and also between $`\lambda(\delta)`$ and $`\omega_1`$. $`\square`$

**Chains.** Put $`\Lambda_0 = \lambda(0)`$ and $`\Lambda_{t+1} = \lambda(\Lambda_t)`$. Since $`\Lambda_t \lt \lambda(\Lambda_t) = \Lambda_{t+1}`$, this is an increasing sequence, and by the corollary any two of its members are related at every level. Taking $`c_i = \Lambda_{i+1}`$ gives chains of every length.

## 5. On the size of the labels

The ordinals obtained by this construction are below $`\omega_1`$, but where they lie is unknown.

- In $`\mathcal{R}_2`$, Wilken has shown that finite $`\le_2`$ chains of arbitrary length exist below $`\psi_0(\Omega_\omega)`$ ([03](03-patterns.md) §5)
- In $`\mathcal{R}_3`$, it is known that the least $`\lt_3`$ pair is $`\upsilon_{\omega^2} \lt_3 \upsilon_{\omega^2 + 2}`$

These are not formalized.

## 6. How it is used in the proof

| Fact | Where |
|---|---|
| Chains of every length exist | [08](08-termination.md) labels of the initial arrays |

## 7. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Formulas | `Form` | [`Pattern/Chain.lean`](../../lean/Pattern/Chain.lean) |
| Indexing parameters | `params`, `exists_params` | same |
| Height of witnesses | `witHeight`, `witHeight_lt` | same |
| $`\mathrm{next}`$ | `next`, `lt_next`, `next_lt` | same |
| Witnesses lie below next | `wit_below` | same |
| $`\mathrm{next}^t`$, $`\lambda`$ | `tower`, `lam`, `tower_le_lam`, `lam_lt`, `lt_lam` | same |
| Finitely many lie below some stage | `exists_tower` | same |
| Theorem of §3 | `lam_elem` | same |
| Corollary of §4 | `lab_lam` | same |
| Chains | `lamChain`, `lamChain_lt`, `lamChain_strictMono`, `exists_chain` | same |
