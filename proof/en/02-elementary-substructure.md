[← Back](../README-en.md) | [English](02-elementary-substructure.md) | [Japanese](../02-elementary-substructure.md)

# Structures and Elementary Substructures

Prerequisites: [01 Ordinals and ω₁](01-ordinals.md)

## 1. Language and structures

**Definition (language).** The language $`\mathcal{L}_N`$ used below consists only of the binary relation symbols $`\le, \le_1, \dots, \le_N`$.

**Definition (structure).** A structure for $`\mathcal{L}_N`$ is a set $`M`$ together with $`N + 1`$ binary relations on $`M`$, which are the meanings of the symbols $`\le, \le_1, \dots, \le_N`$.

**Notation.** The structure consisting of a set $`M`$ and binary relations $`P_0, P_1, \dots, P_N`$ on $`M`$ is written

```math
(M;\ P_0, P_1, \dots, P_N) .
```

The $`M`$ before the semicolon is the **universe** of the structure, the range over which the quantifiers of formulas run. After the semicolon come the relations assigned to the symbols $`\le, \le_1, \dots, \le_N`$ in this order.

When a relation is defined on a range wider than the universe, we use the relation that keeps only pairs of elements of the universe (the restriction).

**Example.** Let $`R`$ be the relation $`a \mathrel{R} b \iff b = a + 1`$. The structure $`(3;\ \le, R)`$ is as follows (as in [01](01-ordinals.md) §1, $`3`$ is the set $`\{0, 1, 2\}`$ of ordinals below $`3`$).

| Part | Contents |
|---|---|
| Universe | $`\{0, 1, 2\}`$ |
| Meaning of $`\le`$ | $`0 \le 0,\ 0 \le 1,\ 0 \le 2,\ 1 \le 1,\ 1 \le 2,\ 2 \le 2`$ |
| Meaning of $`\le_1`$ | $`0 \mathrel{R} 1,\ 1 \mathrel{R} 2`$ |

$`2 \mathrel{R} 3`$ does not appear in this structure because $`3`$ is not in the universe. It does appear in the structure $`(4;\ \le, R)`$.

All structures used from this note on have the following form. Fix binary relations $`R_1, \dots, R_N`$ on all ordinals, and for each ordinal $`\alpha`$ consider

```math
(\alpha;\ \le,\ R_1, \dots, R_N) .
```

Its universe is the set of ordinals below $`\alpha`$, and its relations are the restrictions of the global relations to $`\alpha`$.

**Definition (substructure).** If $`\alpha \le \beta`$, then $`(\alpha; \le, R_1, \dots, R_N)`$ is a **substructure** of $`(\beta; \le, R_1, \dots, R_N)`$, because the relation between two elements below $`\alpha`$ is the same in both structures.

## 2. Formulas

The atomic formulas are $`x \le y`$ and $`x \le_j y`$. $`x = y`$ can be written as $`x \le y \wedge y \le x`$, and $`x \lt y`$ as $`\neg\, y \le x`$.

A formula without quantifiers is a **quantifier-free formula**. A formula obtained from a quantifier-free formula $`\psi`$ by adding $`n`$ alternating quantifier blocks starting with $`\exists`$ is a **$`\Sigma_n`$ formula**.

```math
\exists \vec x_1\ \forall \vec x_2\ \exists \vec x_3 \cdots\ \psi
```

Those starting with $`\forall`$ are **$`\Pi_n`$ formulas**. The negation of a $`\Sigma_n`$ formula is equivalent to a $`\Pi_n`$ formula. A formula with fewer than $`n`$ blocks can also be regarded as a $`\Sigma_n`$ formula by adding empty blocks.

| Formula | Form | Meaning |
|---|---|---|
| $`\exists x\ (p \lt x)`$ | $`\Sigma_1`$ | there is an element greater than $`p`$ |
| $`\exists x\ \forall y\ (y \le x)`$ | $`\Sigma_2`$ | there is a largest element |
| $`\forall x\ \exists y\ (x \lt y)`$ | $`\Pi_2`$ | there is no largest element |
| $`\exists x\ \exists y\ (x \lt y \wedge x \le_1 y)`$ | $`\Sigma_1`$ | there are two distinct elements related by $`\le_1`$ |

## 3. Satisfaction and preservation upward and downward

$`M \models \varphi[\vec p]`$ means that $`\varphi`$ with a tuple $`\vec p`$ of elements of $`M`$ as parameters holds in $`M`$. The quantifiers range only over elements of $`M`$.

**Lemma.** Let $`M`$ be a substructure of $`M'`$ and $`\vec p`$ a tuple of elements of $`M`$.

1. A quantifier-free formula has the same truth value in $`M`$ and in $`M'`$
2. If a $`\Sigma_1`$ formula is true in $`M`$, it is true in $`M'`$ (preserved upward)
3. If a $`\Pi_1`$ formula is true in $`M'`$, it is true in $`M`$ (preserved downward)

**Proof.** 1 follows because atomic formulas have the same truth values. For 2, a witness in $`M`$ is also a witness in $`M'`$. 3 is the contrapositive of 2. $`\square`$

$`\Sigma_2`$ formulas need not be preserved in either direction. In structures with the relation $`\le`$ only, "there is a largest element" is true in $`(\omega + 1; \le)`$ and false in $`(\omega; \le)`$.

## 4. Σₙ-elementary substructures

**Definition.** If $`M`$ is a substructure of $`M'`$ and for every $`\Sigma_n`$ formula $`\varphi`$ with parameters from $`M`$

```math
M \models \varphi[\vec p] \iff M' \models \varphi[\vec p] ,
```

we write $`M \preceq_{\Sigma_n} M'`$ and say that $`M`$ is a **$`\Sigma_n`$-elementary substructure** of $`M'`$.

The following are immediate.

- If $`M \preceq_{\Sigma_{n+1}} M'`$, then $`M \preceq_{\Sigma_n} M'`$
- If $`M \subseteq M' \subseteq M''`$, $`M \preceq_{\Sigma_n} M'`$ and $`M' \preceq_{\Sigma_n} M''`$, then $`M \preceq_{\Sigma_n} M''`$
- Taking negations, the truth values of $`\Pi_n`$ formulas also agree

### 4.1 Examples (structures with ≤ only)

| Pair of structures | Result | Reason |
|---|---|---|
| $`(3; \le)`$ and $`(4; \le)`$ | not a $`\Sigma_1`$-elementary substructure | $`\exists x\ (2 \lt x)`$ is true in $`4`$ and false in $`3`$ |
| $`(\omega; \le)`$ and $`(\omega + 1; \le)`$ | a $`\Sigma_1`$-elementary substructure | the example in 4.2 |
| $`(\omega; \le)`$ and $`(\omega + 1; \le)`$ | not a $`\Sigma_2`$-elementary substructure | "there is a largest element" |

### 4.2 Σ₁-elementary substructures are determined by copies of finitely many points

**Proposition.** Suppose the language consists of finitely many relation symbols. Let $`M`$ be a substructure of $`M'`$. The following are equivalent.

1. $`M \preceq_{\Sigma_1} M'`$
2. For every finite subset $`X`$ of $`M`$ and finite subset $`Y`$ of $`M'`$, there are a finite subset $`Y'`$ of $`M`$ and a bijection $`h : X \cup Y' \to X \cup Y`$ that fixes the elements of $`X`$ and preserves the truth values of all atomic formulas

**Proof.** From 1 to 2: let $`Y = \{y_1, \dots, y_s\}`$. "The truth values of atomic formulas between $`X`$ and $`u_1, \dots, u_s`$ are those between $`X`$ and $`y_1, \dots, y_s`$" can be written as a quantifier-free formula, since there are finitely many relation symbols. The $`\Sigma_1`$ formula obtained by adding $`\exists u_1 \cdots \exists u_s`$ is true in $`M'`$, hence true in $`M`$, and its witness is $`Y'`$.

From 2 to 1: if a $`\Sigma_1`$ formula $`\exists \vec u\ \psi(\vec p, \vec u)`$ is true in $`M'`$, let $`Y`$ be the set of witnesses and $`X`$ the set of parameters, and take a copy $`Y'`$. The atomic truth values agree, so $`\psi`$ is true at $`Y'`$. Together with upward preservation this gives 1. $`\square`$

**Example.** For $`(\omega; \le)`$ and $`(\omega + 1; \le)`$: if $`Y`$ contains $`\omega`$, replacing it by a natural number larger than all natural numbers in $`X \cup Y`$ gives a copy.

This idea of copies is the prototype of finite reflection in [06](06-finite-reflection.md).

## 5. How it is written in Lean

In Lean, formulas are not defined as syntax. They are represented on the side of values, as follows.

**Atomic diagrams.** For a sequence of ordinals $`v = (v_0, v_1, \dots)`$, the **atomic diagram** of its first $`n`$ entries is defined as follows, where $`[P]`$ is the truth value of $`P`$.

```math
\mathrm{diag}_n(v)(a, b) = \bigl([v_a \le v_b],\ [v_a \le_1 v_b],\ \dots,\ [v_a \le_N v_b]\bigr) \qquad (a, b \lt n)
```

**Example.** Let $`N = 1`$ and, as an example, let the meaning $`R_1`$ of the symbol $`\le_1`$ be the following relation.

```math
a \mathrel{R_1} b \iff a = b \vee \bigl(a \text{ is a limit ordinal and } b = a + 1\bigr)
```

The atomic diagram of the first $`3`$ entries of the sequence $`v = (3,\ \omega,\ \omega + 1)`$ is the following table. Each entry is $`([v_a \le v_b],\ [v_a \mathrel{R_1} v_b])`$, where $`1`$ is true and $`0`$ is false.

| | $`b = 0`$ ($`3`$) | $`b = 1`$ ($`\omega`$) | $`b = 2`$ ($`\omega + 1`$) |
|---|---|---|---|
| $`a = 0`$ ($`3`$) | $`(1, 1)`$ | $`(1, 0)`$ | $`(1, 0)`$ |
| $`a = 1`$ ($`\omega`$) | $`(0, 0)`$ | $`(1, 1)`$ | $`(1, 1)`$ |
| $`a = 2`$ ($`\omega + 1`$) | $`(0, 0)`$ | $`(0, 0)`$ | $`(1, 1)`$ |

- The atomic diagram of the sequence $`w = (5,\ \omega \cdot 2,\ \omega \cdot 2 + 1)`$ is the same as this table
- The atomic diagram of the sequence $`u = (3,\ \omega,\ \omega + 2)`$ differs from this table, since its entry at $`(a, b) = (1, 2)`$ is $`(1, 0)`$

The truth value of a quantifier-free formula depends only on the atomic diagram of the values substituted for its variables. Since there are only finitely many atomic diagrams, a quantifier-free formula carries the same information as a **set $`D`$ of atomic diagrams**.

**Example (continued).** The quantifier-free formula $`\psi(x, y, z) = x \lt y \wedge y \mathrel{R_1} z`$ is true for $`v`$ and $`w`$ and false for $`u`$. The set $`D`$ corresponding to $`\psi`$ consists of all atomic diagrams whose $`\le`$ component at position $`(1, 0)`$ is $`0`$ and whose $`R_1`$ component at position $`(1, 2)`$ is $`1`$, because $`x \lt y`$ is $`\neg\, y \le x`$.

**Evaluation by blocks.** Given a list of quantifier block lengths $`[b_1, \dots, b_r]`$, a set $`D`$ of atomic diagrams and a sequence of parameters, define $`\mathrm{Sig}_M`$ by recursion on the number of blocks.

```math
\mathrm{Sig}_M([\,],\ v) \iff \mathrm{diag}_n(v) \in D
```

```math
\mathrm{Sig}_M([b_1, b_2, \dots, b_r],\ v) \iff \exists x_0, \dots, x_{b_1 - 1} \lt M\ \ \neg\, \mathrm{Sig}_M([b_2, \dots, b_r],\ v\,\vec x)
```

Here $`v\,\vec x`$ is the sequence with $`x_0, \dots, x_{b_1 - 1}`$ placed after the positions already assigned. $`n`$ is taken to be the number of parameters plus $`b_1 + \cdots + b_r`$. Unfolding gives the following form.

```math
\mathrm{Sig}_M([b_1, \dots, b_r],\ \vec p) \iff \exists \vec x_1\ \neg\, \exists \vec x_2\ \neg \cdots \exists \vec x_r\ \neg\, \bigl(\mathrm{diag}(\vec p, \vec x_1, \dots, \vec x_r) \in D\bigr)
```

Since $`\neg \exists = \forall \neg`$, this is a $`\Sigma_r`$ formula of the form $`\exists \vec x_1\ \forall \vec x_2\ \exists \vec x_3 \cdots`$, whose matrix is $`D`$ or its complement. Conversely, every $`\Sigma_r`$ formula can be written in this form.

**Example.** "There is a largest element" is represented with no parameters, blocks $`[1, 1]`$, and $`D = \{d :`$ the $`\le`$ component of $`d(1, 0)`$ is true$`\}`$.

```math
\mathrm{Sig}_M([1, 1],\ ()) \iff \exists x\ \neg\, \exists y\ \neg\, (y \le x) \iff \exists x\ \forall y\ (y \le x)
```

**Σⱼ-elementary substructures.** $`\mathrm{Elem}_j(\alpha, \beta)`$ is defined as: for every list with at most $`j`$ blocks, every $`D`$ and all parameters below $`\alpha`$, $`\mathrm{Sig}_\alpha`$ and $`\mathrm{Sig}_\beta`$ agree. This means the same as $`(\alpha; \ldots) \preceq_{\Sigma_j} (\beta; \ldots)`$.

## 6. How it is used in the proof

| Fact | Where |
|---|---|
| Substructures, preservation upward and downward | all properties in [04](04-pattern-properties.md) |
| Σₙ-elementary substructures | the definition in [03](03-patterns.md) |
| Characterization by copies | [06](06-finite-reflection.md) finite reflection |
| Evaluation by blocks | [07](07-closure-chains.md) induction in the closure |

## 7. Correspondence with Lean

| Concept | Lean | File |
|---|---|---|
| Atomic diagrams | `Diag`, `diag`, `bits` | [`Pattern/Basic.lean`](../../lean/Pattern/Basic.lean) |
| Concatenation $`v\,\vec x`$ | `cat` | same |
| Evaluation by blocks | `Sig`, `sig_nil`, `sig_cons` | same |
| $`\mathrm{Elem}_j`$ | `Elem` | same |
| Upward preservation of $`\Sigma_1`$ | `sig_up1` | same |
| Reading entries of atomic diagrams | `get`, `GLe`, `GLev`, `gle_diag`, `glev_diag` | same |
