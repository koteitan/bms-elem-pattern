[← Back](../README-en.md) | [English](08-termination.md) | [Japanese](../08-termination.md)

# Termination and Well-Foundedness

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md), [05 Arrays, expansion, and stable labels](05-arrays-labels.md), [06 Finite reflection](06-finite-reflection.md), [07 Closure inside ω₁ and chains](07-closure-chains.md)

## 1. The label system

Let $`r \le 3`$. Let $`\mathrm{Lab}`$ be the class of ordinals, and put $`\lhd_k = \lt_{k+1}`$ ($`k \lt r`$) using the relations of $`\mathcal{R}_r`$.

- Strict and transitive: [03](03-patterns.md) §3
- Finite reflection: [06](06-finite-reflection.md)

The case of every number of rows $`r`$ is in [bms](../../bms/README-en.md). Lean's `terminates` is proved without a bound on the number of rows, using `labelSystemGen`, which works for every number of rows.

Hence this is a label system with $`r`$ rows ([05](05-arrays-labels.md) §5).

## 2. Labels of the initial arrays

**Lemma.** $`S^r_n`$ has a stable label.

**Proof.** Take the chain $`c_0 \lt c_1 \lt \cdots \lt c_n`$ of [07](07-closure-chains.md) §4 and put $`f(i) = c_i`$.

1. If $`i \lt j`$, then $`c_i \lt c_j`$
2. If $`j \prec_k i`$, then $`j \lt i`$, so $`c_j \lt_{k+1} c_i`$, that is, $`f(j) \lhd_k f(i)`$

$`\square`$

## 3. Standard arrays have labels

**Lemma.** Every nonempty standard array has a stable label.

**Proof.** By induction on the number of expansions. The initial arrays are handled by §2. When $`A[N]`$ is obtained from $`A`$: if $`A`$ is empty, then $`A[N] = A`$ is empty as well, contradicting the assumption. If $`A`$ is nonempty, it has a stable label by the induction hypothesis, and $`A[N]`$ has one by Proposition 19.1. $`\square`$

## 4. Termination

**Theorem.** Let $`r \le 3`$, $`A`$ a standard array with $`r`$ rows, $`n : \mathbb{N} \to \mathbb{N}`$, and put $`A_0 = A`$, $`A_{t+1} = A_t[n(t)]`$. Then $`A_T`$ is empty for some $`T`$.

**Proof.** Suppose no $`A_t`$ is empty.

1. By §3, $`A_0`$ has a stable label $`f_0`$
2. If $`f_t`$ is a stable label of $`A_t`$, Proposition 19.1 gives a stable label $`f_{t+1}`$ of $`A_{t+1}`$ with $`\mathrm{ht}(f_{t+1}) \lt \mathrm{ht}(f_t)`$. Choose one for each $`t`$ by the axiom of choice to form a sequence
3. $`\mathrm{ht}(f_0) \gt \mathrm{ht}(f_1) \gt \cdots`$ is an infinite descending sequence of ordinals, contradicting [01](01-ordinals.md) §1

$`\square`$

## 5. Well-foundedness

**Theorem.** For $`r \le 3`$, the relation on standard arrays with $`r`$ rows

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

is well-founded.

**Proof.** Suppose there is an infinite descending sequence $`B_0, B_1, \dots`$ of $`R`$ ($`B_{t+1} \mathrel{R} B_t`$). Choosing $`n(t)`$ with $`B_{t+1} = B_t[n(t)]`$ gives an expansion sequence starting from $`B_0`$ none of whose terms is empty, contradicting §4. $`\square`$

## 6. Size of the labels (not formalized)

**Lower bound.** Put the height of the empty array to be $`0`$, and for a nonempty array $`A`$ define its height in the expansion tree by $`\mathrm{rank}(A) = \sup_N (\mathrm{rank}(A[N]) + 1)`$. Then

```math
\mathrm{rank}(A) \le \mathrm{ht}(f)
```

can be shown by induction on $`\mathrm{ht}(f)`$ for stable labels $`f`$: the label $`g`$ of $`A[N]`$ satisfies $`\mathrm{ht}(g) \lt \mathrm{ht}(f)`$, and by the induction hypothesis $`\mathrm{rank}(A[N]) \le \mathrm{ht}(g)`$. Hence the last label of $`S^r_n`$ must be at least the height of $`S^r_n`$ in the expansion tree.

**Upper bound.**

| Case | Range of labels |
|---|---|
| Labels built in Lean | below $`\omega_1`$; where exactly is unknown |
| Pair sequences (literature) | can be taken below $`\psi_0(\Omega_\omega)`$ |
| $`(0,0,0)(1,1,1)`$ (literature) | $`(\upsilon_{\omega^2}, \upsilon_{\omega^2 + 2})`$ can be used |
| Further trio sequences | unknown |

## 7. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Label system | `labelSystem` (up to 3 rows) | [`Pattern/Reflect.lean`](../../../lean/Pattern/Reflect.lean) |
| Label system | `labelSystemGen` (every number of rows) | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| §2 | `stable_stair` | [`Pattern/Main.lean`](../../../lean/Pattern/Main.lean) |
| §3 | `std_stable` | same |
| §4 | `terminates`, `pss_terminates`, `tss_terminates` | same |
| §5 | `StdElt`, `StdR`, `StdR_wf` | same |
