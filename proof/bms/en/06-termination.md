[← Back](../README-en.md) | [English](06-termination.md) | [Japanese](../06-termination.md)

# Termination and Well-Foundedness for Every Number of Rows

Prerequisites: [pss 05 Arrays, expansion, and stable labels](../../pss/en/05-arrays-labels.md), [pss 07 Closure inside ω₁ and chains](../../pss/en/07-closure-chains.md), [pss 08 Termination and well-foundedness](../../pss/en/08-termination.md), [05 Finite reflection at every level](05-finite-reflection.md)

## 1. The label system

Let $`r \ge 1`$ be the number of rows. Let $`\mathrm{Lab}`$ be the class of ordinals and put $`\lhd_k = \lt_{k+1}`$ ($`k \lt r`$) using the relations of $`\mathcal{R}_r`$. By [05](05-finite-reflection.md) §5 this is a label system with $`r`$ rows.

For $`r = 0`$ the finite reflection condition $`n \lt 0`$ is empty, so any strict transitive relations form a label system. Lean treats $`r = 0`$ with the same definition.

## 2. Labels of the initial arrays

**Lemma.** $`S^r_n = (0, \dots, 0)(1, \dots, 1) \cdots (n, \dots, n)`$ has a stable label.

**Proof.** The same as [pss 08](../../pss/en/08-termination.md) §2. Any two elements of the chain $`c_0 \lt c_1 \lt \cdots \lt c_n`$ of [pss 07](../../pss/en/07-closure-chains.md) §4 satisfy $`c_i \lt_j c_{i'}`$ at every level $`j \le r`$, so $`f(i) = c_i`$ works. $`\square`$

## 3. Standard arrays have labels

**Lemma.** Every nonempty standard array with $`r`$ rows has a stable label.

**Proof.** Induction on the number of expansions. The initial arrays are handled by §2 and expansions by Proposition 19.1 ([pss 05](../../pss/en/05-arrays-labels.md) §7). The same as [pss 08](../../pss/en/08-termination.md) §3. $`\square`$

## 4. Termination

**Theorem.** Let $`r`$ be any natural number, $`A`$ a standard array with $`r`$ rows and $`n : \mathbb{N} \to \mathbb{N}`$, and put

```math
A_0 = A, \qquad A_{t+1} = A_t[n(t)]
```

Then $`A_T`$ is empty for some $`T`$.

**Proof.** Suppose no $`A_t`$ is empty. By §3 and Proposition 19.1 we can choose stable labels $`f_t`$ with

```math
\mathrm{ht}(f_0) \gt \mathrm{ht}(f_1) \gt \mathrm{ht}(f_2) \gt \cdots
```

This is an infinite descending sequence of ordinals, contradicting [pss 01](../../pss/en/01-ordinals.md) §1. $`\square`$

## 5. Well-foundedness

**Theorem.** The relation on standard arrays with $`r`$ rows

```math
A \mathrel{R} B \iff B \ne \emptyset \wedge \exists n\ \bigl(A = B[n]\bigr)
```

is well-founded.

**Proof.** An infinite descending sequence for $`R`$ is an expansion sequence with no empty term, contradicting §4. $`\square`$

## 6. Relation to BM4

- The BM4 initial array $`E_r = (0, \dots, 0)(1, \dots, 1)`$ is $`S^r_1`$. So every array obtained from $`E_r`$ by expansions is a standard array with $`r`$ rows, and its expansions terminate by §4
- Only the BM4 expansion rule is treated. Agreement with other versions of the Bashicu matrix is not treated
- DH's paper proves termination by passing labels given by elementary substructures of the constructible hierarchy to the same Proposition 19.1. Here we pass the relations of $`\mathcal{R}_r`$

## 7. Size of the labels (not formalized)

- The Lean labels are built by the closure of [pss 07](../../pss/en/07-closure-chains.md), so we only know that they are below $`\omega_1`$
- The lower bound $`\mathrm{rank}(A) \le \mathrm{ht}(f)`$ of [pss 08](../../pss/en/08-termination.md) §6 holds for every number of rows
- For 4 rows and more, we have not studied where in $`\mathcal{R}_r`$ the labels can be taken

## 8. Lean correspondence

| Concept | Lean | File |
|---|---|---|
| §1 | `labelSystemGen` | [`Pattern/General.lean`](../../../lean/Pattern/General.lean) |
| $`S^r_n`$, standard arrays | `stair`, `Std` | [`Pattern/Main.lean`](../../../lean/Pattern/Main.lean) |
| §2 | `stable_stair` | same |
| §3 | `std_stable` | same |
| §4 | `terminates` | same |
| §5 | `StdElt`, `StdR`, `StdR_wf` | same |
| Chain | `lamChain`, `lab_lam` | [`Pattern/Chain.lean`](../../../lean/Pattern/Chain.lean) |
| Proposition 19.1 | `descent` | [`Bm4/Label.lean`](../../../lean/Bm4/Label.lean) |
