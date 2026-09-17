[← Back](../README-en.md) | [English](03-block-form.md) | [Japanese](../03-block-form.md)

# Writing Coordinatewise Conditions in Block Form

Prerequisites: [pss 02 Structures and elementary substructures](../../pss/en/02-elementary-substructure.md) §5, [02 The formulas Φₘ](02-phi.md)

## 1. What we need

In mathematics, that $`\Phi_m`$ is a $`\Pi_m`$ formula follows by counting quantifiers. Lean does not define formulas as syntax; it represents them by a list of block lengths and a set $`D`$ of atomic diagrams ([pss 02](../../pss/en/02-elementary-substructure.md) §5).

```math
\mathrm{Sig}_\gamma([b_1, \dots, b_r],\ \vec p) \iff \exists \vec x_1\ \neg\, \exists \vec x_2\ \neg \cdots \exists \vec x_r\ \neg\, \bigl(\mathrm{diag}(\vec p, \vec x_1, \dots, \vec x_r) \in D\bigr)
```

$`\le_j`$ is defined as agreement on formulas of this form with at most $`j`$ blocks. So in Lean we must show that the sentences we use can be written in this form, with the right number of blocks.

The sentences we use put the same kind of condition on each of $`s`$ coordinates.

```math
G(\vec v) \wedge \bigwedge_{i \lt s} \bigl(Q_i(\vec v) \vee \neg\, \Phi_d(v_{c+i})\bigr)
```

- $`G`$ and $`Q_i`$ are quantifier-free conditions
- $`G`$ reads only the entries at positions below $`c`$, and $`Q_i`$ only those below $`c + s`$
- the tuple $`(v_c, \dots, v_{c+s-1})`$ that $`\Phi_d`$ is applied to is at positions $`c`$ to $`c + s - 1`$

The problem is that each $`i`$ carries its own quantifiers, while in block form the quantifiers of one block are shared by all coordinates.

## 2. Coordinatewise Skolem normal forms

Let $`\gamma \gt 0`$; all quantifiers range below $`\gamma`$.

**Lemma.** The following hold.

```math
\bigwedge_{i \lt s} \bigl(Q_i \vee \exists w\ P_i(w)\bigr) \iff \exists \vec W\ \bigwedge_{i \lt s} \bigl(Q_i \vee P_i(W_i)\bigr)
```

```math
\bigwedge_{i \lt s} \bigl(Q_i \vee \exists z\ \forall t\ P_i(z, t)\bigr) \iff \exists \vec Z\ \forall \vec S\ \bigwedge_{i \lt s} \bigl(Q_i \vee P_i(Z_i, S_i)\bigr)
```

**Proof.**

- Left to right: for $`i`$ with $`Q_i`$ put $`W_i = 0`$ (or $`Z_i = 0`$); for the other $`i`$ choose a witness. This uses $`0 \lt \gamma`$
- Right to left in the first: $`W_i`$ is a witness
- Right to left in the second: take $`i`$ with $`Q_i`$ false and $`t \lt \gamma`$. Let $`\vec S`$ be the tuple with all entries $`t`$; the $`i`$-th conjunct gives $`P_i(Z_i, t)`$. So $`Z_i`$ is a witness

The second right-to-left direction uses that the $`i`$-th conjunct reads only $`Z_i`$ and $`S_i`$. $`\square`$

## 3. Block form

**Proposition.** Let $`\gamma \gt 0`$ and $`d \ge 0`$. There is a set $`D_d`$ of atomic diagrams such that for every $`\vec v = (v_0, \dots, v_{c+s-1})`$

```math
\mathrm{Sig}_\gamma\bigl([\underbrace{s, \dots, s}_{d}],\ \vec v\bigr) \iff G(\vec v) \wedge \bigwedge_{i \lt s} \bigl(Q_i(\vec v) \vee \neg\, \Phi_d(v_{c+i})\bigr)
```

where $`\Phi_d`$ on the right is evaluated in $`\gamma`$.

**Proof.** Induction on $`d`$.

**Case $`d = 0`$.** $`\Phi_0`$ is true, so the right side is the quantifier-free $`G \wedge \bigwedge_i Q_i`$. Take it as $`D_0`$.

**Case $`d = 1`$.**

```math
\neg\, \Phi_1(u) \iff \exists w\ \bigl(u \le w \wedge \neg\, u \le_1 w\bigr)
```

Pulling $`\exists \vec W`$ to the front by the first part of §2 leaves a quantifier-free body.

**Case $`d = 2`$.**

```math
\neg\, \Phi_2(u) \iff \exists z\ \forall t\ \neg\, \bigl(z \lt t \wedge u \le_2 t\bigr)
```

Pulling $`\exists \vec Z\ \forall \vec S`$ to the front by the second part of §2 leaves a quantifier-free body.

**Case $`d + 2`$ ($`d \ge 1`$).**

```math
\neg\, \Phi_{d+2}(u) \iff \exists z\ \forall t\ \Bigl(\neg\, \bigl(z \lt t \wedge u \le_{d+2} t\bigr) \vee \neg\, \Phi_d(t)\Bigr)
```

Pulling $`\exists \vec Z\ \forall \vec S`$ to the front by the second part of §2 leaves the body

```math
G \wedge \bigwedge_{i \lt s} \bigl(Q'_i \vee \neg\, \Phi_d(S_i)\bigr), \qquad Q'_i = Q_i \vee \neg\, \bigl(Z_i \lt S_i \wedge v_{c+i} \le_{d+2} S_i\bigr)
```

This is a condition of the same form on the sequence $`(\vec v, \vec Z, \vec S)`$, with the tuple $`\vec S`$ starting at position $`c + 2s`$. $`G`$ reads only positions below $`c`$, and $`Q'_i`$ only positions below $`c + 3s`$. By the induction hypothesis it is written with blocks $`[s, \dots, s]`$ ($`d`$ of them). Together with the two blocks in front, there are $`d + 2`$ blocks.

$`\square`$

## 4. The sentences used

**(1) The sentence $`\exists u\ (z \lt u \wedge \Phi_d(u))`$ with parameter $`z`$.** Apply §3 with $`s = 1`$, $`c = 1`$, $`G = \top`$, $`Q_0 = (u \le z)`$, and put $`\exists u\ \neg`$ in front.

```math
\exists u\ \neg\, \bigl(u \le z \vee \neg\, \Phi_d(u)\bigr) \iff \exists u\ \bigl(z \lt u \wedge \Phi_d(u)\bigr)
```

The blocks are $`[1, 1, \dots, 1]`$ ($`d + 1`$ of them), so this is a $`\Sigma_{d+1}`$ sentence.

**(2) The sentence $`\exists z\ \neg\, \exists u\ (z \lt u \wedge \Phi_d(u))`$ without parameters.** Put $`\exists z\ \neg`$ in front of (1). It has $`d + 2`$ blocks and is the negation of the $`\Pi_{d+2}`$ sentence $`\forall z\ \exists u\ (z \lt u \wedge \Phi_d(u))`$.

**(3) The sentence of finite reflection.** The sentence $`\sigma`$ of [05](05-finite-reflection.md) has tuples $`\vec U`$, $`\vec V`$ and the form

```math
\exists \vec U\ \neg\, \exists \vec V\ \neg\, \Bigl(G \wedge \bigwedge_{i \lt s} \bigl(Q_i \vee \neg\, \Phi_{n-1}(V_i)\bigr)\Bigr)
```

§3 with $`d = n - 1`$ gives blocks $`[s, s, \dots, s]`$ ($`n + 1`$ of them), so it is a $`\Sigma_{n+1}`$ sentence.

## 5. Where it is used

| Fact | Used in |
|---|---|
| (1), (2) | steps B and E of [04](04-cofinal-predecessors.md) |
| (3) | [05](05-finite-reflection.md) |

## 6. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| Conditions on atomic diagrams | `DP` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| Reads only positions below $`B`$ | `Reads`, `Reads.diag_iff`, `Reads.mono`, `reads_gle`, `reads_glev` | same |
| §2 | `skolem_one`, `skolem_two` | same |
| $`D_d`$ of §3 | `tnMat` | same |
| Proposition of §3 | `tn_sig` | same |
| Unfolding the negations in §3 | `not_phi_one`, `not_phi_two`, `not_phi_add_three` | same |
| §4 (1), (2) | `exPhiMat`, `sig_exists_phi`, `sig_forall_exists_phi` | same |
| §4 (3) | `hsem` inside `reflect_gen` | same |
