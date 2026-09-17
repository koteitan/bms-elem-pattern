[← Back](../README-en.md) | [English](05-finite-reflection.md) | [Japanese](../05-finite-reflection.md)

# Finite Reflection at Every Level

Prerequisites: [pss 05 Arrays, expansion, and stable labels](../../pss/en/05-arrays-labels.md) §5, [pss 06 Finite reflection](../../pss/en/06-finite-reflection.md) §2–§4, [01](01-cofinal-continuity.md)–[04](04-cofinal-predecessors.md)

## 1. Statement

Let $`N \ge 1`$ and define the label relations by the relations of $`\mathcal{R}_N`$:

```math
\lhd_k = \lt_{k+1} \qquad (k \lt N)
```

**Theorem (finite reflection).** Let $`n \lt N`$, $`\alpha \lhd_n \beta`$, $`X = \{p_0, \dots, p_{k-1}\} \subseteq \alpha`$ and $`\alpha \le y_0 \lt \cdots \lt y_{s-1} \lt \beta`$. Then there are $`y'_0 \lt \cdots \lt y'_{s-1} \lt \alpha`$ satisfying (a)–(d) of [pss 05](../../pss/en/05-arrays-labels.md) §5. Condition (d) is

```math
\forall i \lt s\ \forall m \lt n\ \bigl(y_i \lt_{m+1} \beta \Rightarrow y'_i \lt_{m+1} \alpha\bigr) \qquad \text{(d)}
```

- $`n = 0`$ was shown in [pss 06](../../pss/en/06-finite-reflection.md) §3
- From now on let $`n \ge 1`$, that is, $`\alpha \lt_{n+1} \beta`$
- (a), (b), (c) follow from the lemma of [pss 06](../../pss/en/06-finite-reflection.md) §2 once we take $`\vec y' \lt \alpha`$ with $`\mathrm{diag}(\vec p, \vec y') = \mathrm{diag}(\vec p, \vec y)`$

## 2. The sentence

For each $`i \lt s`$ put $`M_i = \{m \lt n : y_i \lt_{m+1} \beta\}`$. For tuples $`\vec U`$, $`\vec V`$ of length $`s`$, we use the following sentence $`\sigma`$ with parameters $`\vec p`$.

```math
\sigma = \exists \vec U\ \forall \vec V\ \Bigl(\mathrm{diag}(\vec p, \vec U) = \mathrm{diag}(\vec p, \vec y) \wedge \bigwedge_{i \lt s} \bigl(U_i \le V_i \wedge \Phi_{n-1}(V_i) \Rightarrow \bigwedge_{m \in M_i} U_i \le_{m+1} V_i\bigr)\Bigr)
```

- $`M_i`$ is a set fixed from outside; it selects which conjuncts are included and is not part of the formula
- $`\Phi_{n-1}`$ is $`\Pi_{n-1}`$ (true if $`n = 1`$), so the body of $`\bigwedge_i`$ is a $`\Sigma_{n-1}`$ formula. $`\forall \vec V`$ makes it $`\Pi_n`$, and $`\exists \vec U`$ makes it $`\Sigma_{n+1}`$
- In Lean's form it is written with blocks $`[s, s, \dots, s]`$ ($`n + 1`$ of them), as in (3) of [03](03-block-form.md) §4
- For $`n = 1`$, $`\sigma`$ is the sentence of [pss 06](../../pss/en/06-finite-reflection.md) §4

**Idea.** $`\Phi_{n-1}(V_i)`$ says from inside that $`V_i`$ is $`\le_{n-1}`$-connected to the top ([02](02-phi.md) §5). If $`U_i`$ is $`\le_{m+1}`$-related to every $`V_i \ge U_i`$ connected to the top, then P4′ connects $`U_i`$ itself to the top by $`\le_{m+1}`$.

## 3. True in β

Put $`\vec U = \vec y`$. The atomic diagrams clearly agree. Take $`\vec V \lt \beta`$ and $`i \lt s`$ with $`y_i \le V_i`$, $`\beta \models \Phi_{n-1}(V_i)`$, and $`m \in M_i`$. We show $`y_i \le_{m+1} V_i`$.

1. We show $`V_i \le_m \beta`$. If $`m = 0`$ it follows from $`V_i \lt \beta`$. If $`m \ge 1`$, then $`n \ge 2`$. Since $`\alpha \lt_2 \beta`$, $`\beta`$ is closed under successor by P6, and Lemma A gives $`V_i \le_{n-1} \beta`$. As $`m \le n - 1`$, $`V_i \le_m \beta`$
2. $`m \in M_i`$ gives $`y_i \le_{m+1} \beta`$
3. Since $`y_i \le V_i \le \beta`$, the corollary of [01](01-cofinal-continuity.md) §4 with $`u = y_i`$, $`s = V_i`$, $`\gamma = \beta`$ gives $`y_i \le_{m+1} V_i`$

$`\square`$

## 4. (d) in α

Since $`\alpha \le_{n+1} \beta`$ and $`\vec p \lt \alpha`$, $`\sigma`$ is true in $`\alpha`$ as well. Let $`\vec y'`$ be a witness.

- The agreement of atomic diagrams is required whatever $`\vec V`$ is, so $`\mathrm{diag}(\vec p, \vec y') = \mathrm{diag}(\vec p, \vec y)`$. By §1 this gives (a), (b), (c)
- We show (d). Take $`i \lt s`$ and $`m \in M_i`$. We show $`y'_i \le_{m+1} \alpha`$ by P4′ with $`j = m + 1`$

**Choosing the point v.** Take $`z \lt \alpha`$ and put $`z' = \max(z, y'_i)`$. Take $`v`$ with

```math
z' \lt v \lt \alpha, \qquad \alpha \models \Phi_{n-1}(v), \qquad n \ge 2 \Rightarrow v \le_{n-1} \alpha
```

- Case $`n = 1`$: $`v = z' + 1`$. Since $`\alpha \lt_1 \beta`$, $`\alpha`$ is closed under successor by P5, so $`v \lt \alpha`$. $`\Phi_0`$ is true
- Case $`n \ge 2`$: since $`\alpha \lt_n \beta`$, P7′ ([04](04-cofinal-predecessors.md)) gives $`\mathrm{Cof}_l(\alpha)`$ for all $`l \le n - 1`$. By $`\mathrm{Cof}_{n-1}(\alpha)`$ take $`v`$ with $`z' \lt v \lt \alpha`$ and $`v \le_{n-1} \alpha`$. Lemma B gives $`\alpha \models \Phi_{n-1}(v)`$

**v satisfies the conditions of P4′.**

1. Put the tuple with all entries $`v`$ into $`\forall \vec V`$ of $`\sigma`$. From $`y'_i \le v`$ and $`\alpha \models \Phi_{n-1}(v)`$ we get $`y'_i \le_{m+1} v`$
2. We show $`v \le_{m-1} \alpha`$. If $`m \le 1`$ it holds automatically. If $`m \ge 2`$, then $`n \ge m + 1 \ge 3`$, so $`v \le_{n-1} \alpha`$, and $`m - 1 \le n - 1`$ gives $`v \le_{m-1} \alpha`$

The set $`S`$ of all such $`v`$ is a subset of $`[y'_i, \alpha)`$ unbounded in $`\alpha`$ and satisfies the conditions of P4′. Hence $`y'_i \le_{m+1} \alpha`$, and since $`y'_i \lt \alpha`$, $`y'_i \lt_{m+1} \alpha`$.

$`\square`$

## 5. The label system

**Corollary.** For $`N \ge 1`$, the class of ordinals as $`\mathrm{Lab}`$ with $`\lhd_k = \lt_{k+1}`$ ($`k \lt N`$) is a label system with $`N`$ rows ([pss 05](../../pss/en/05-arrays-labels.md) §5).

- Strict and transitive: [pss 03](../../pss/en/03-patterns.md) §3
- Finite reflection: $`n = 0`$ by [pss 06](../../pss/en/06-finite-reflection.md) §3, $`n \ge 1`$ by §1–§4

## 6. Difference from the proof for 3 rows

The proof for $`n = 2`$ in [pss 06](../../pss/en/06-finite-reflection.md) §5 put $`\le_1`$-related points into $`\vec v`$ and split into cases on whether there is a point $`w_i`$ where $`\le_1`$ breaks. Extending that method to level 3 and above needs P4 at level 3 and above, and it stopped there ([pss 06](../../pss/en/06-finite-reflection.md) §6).

Here this is avoided in two ways.

- $`\vec V`$ carries the assumption $`\Phi_{n-1}(V_i)`$ that it is connected to the top. Truth in $`\beta`$ then follows from the corollary of [01](01-cofinal-continuity.md) alone
- On the side of $`\alpha`$, $`v`$ is taken from $`\mathrm{Cof}_{n-1}(\alpha)`$. Then $`v \le_{n-1} \alpha`$, which gives the extra condition $`v \le_{m-1} \alpha`$ of P4′

## 7. Where it is used

| Fact | Used in |
|---|---|
| The label system of §5 | passed to Proposition 19.1 in [06](06-termination.md) |

## 8. Lean correspondence

In `reflect_gen hn1 h`, the hypothesis `lab N n α β` is $`\alpha \lt_{n+1} \beta`$. In the conclusion, `SameBits` is the agreement of atomic diagrams, and the last condition is (d).

| Concept | Lean | File |
|---|---|---|
| Meaning of $`\sigma`$ in §2 | `hsem` inside `reflect_gen` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| §3 | `hβsat` inside `reflect_gen` | same |
| §4 | `reflect_gen` | same |
| Agreement with 0 blocks | `elem_zero` | same |
| $`\Sigma_i`$ agreement from $`v \le_{j} \alpha`$ ($`i \le j`$) | `elem_of_lev` | same |
| §5 | `labelSystemGen` | same |
| $`n = 0`$ | `reflect_zero` | [`Pattern/Reflect.lean`](../../../lean/Pattern/Reflect.lean) |
| Lemma of [pss 06](../../pss/en/06-finite-reflection.md) §2 | `copy_props` | same |
