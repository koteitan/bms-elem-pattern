/-
  Termination of the standard sequences with at most three rows, with labels in R_r
  (`r` = number of rows):

    ◁ₖ = <_{k+1}.

  An array with `r` rows is standard if it is reachable from some `(0,…,0)(1,…,1)⋯(n,…,n)`.
  r = 1: primitive sequences, r = 2: pair sequences, r = 3: trio sequences.
-/
import Pattern.Reflect
import Pattern.Chain

open Classical

namespace Pat

open BM4

/-- `(0,…,0)(1,…,1)⋯(n,…,n)` with `r` rows. -/
def stair (r n : ℕ) : Arr r := ⟨n + 1, fun i _ => i⟩

/-- Arrays with `r` rows reachable from some `(0,…,0)(1,…,1)⋯(n,…,n)`. -/
inductive Std (r : ℕ) : Arr r → Prop
  | init (n : ℕ) : Std r (stair r n)
  | step {A : Arr r} (N : ℕ) : Std r A → Std r (expand A N)

/-- `(0,…,0)(1,…,1)⋯(n,…,n)` is labelled by a chain related at every level. -/
theorem stable_stair {r : ℕ} (hr : r ≤ 3) (n : ℕ) :
    ∃ f, Stable (labelSystem r hr) (stair r n) f := by
  refine ⟨fun i => lamChain r (i + 1), fun i j hij _ => lamChain_strictMono (by omega),
    fun k hk i j _ h => ?_⟩
  have hij : i < j := anc_lt h
  have hlt : lamChain r (i + 1) < lamChain r (j + 1) := lamChain_strictMono (by omega)
  exact lab_lam (lamChain_lt i) (lamChain_lt j) hlt hk

/-- Every nonempty standard array carries a stable label. -/
theorem std_stable {r : ℕ} (hr : r ≤ 3) {A : Arr r} (hA : Std r A) (h0 : 0 < A.len) :
    ∃ f, Stable (labelSystem r hr) A f := by
  induction hA with
  | init n => exact stable_stair hr n
  | @step A N hA ih =>
    by_cases hlen : A.len = 0
    · rw [expand_of_len_zero hlen] at h0
      omega
    · obtain ⟨f, hf⟩ := ih (Nat.pos_of_ne_zero hlen)
      obtain ⟨g, hg, _⟩ := descent (labelSystem r hr) hf (Nat.pos_of_ne_zero hlen) N h0
      exact ⟨g, hg⟩

/-- The labels chosen along an expansion sequence with no empty term. -/
private noncomputable def chain {r : ℕ} (hr : r ≤ 3) {A : Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → Ordinal.{0}}
    (hf₀ : Stable (labelSystem r hr) A f₀) :
    ∀ t, {g : ℕ → Ordinal.{0} // Stable (labelSystem r hr) (seq A n t) g} :=
  Nat.rec ⟨f₀, hf₀⟩ fun t g =>
    ⟨_, (descent (labelSystem r hr) g.2 (hpos t) (n t) (hpos (t + 1))).choose_spec.1⟩

private theorem chain_lt {r : ℕ} (hr : r ≤ 3) {A : Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → Ordinal.{0}}
    (hf₀ : Stable (labelSystem r hr) A f₀) (t : ℕ) :
    ht (labelSystem r hr) (seq A n (t + 1)) (chain hr hpos hf₀ (t + 1)).1
      < ht (labelSystem r hr) (seq A n t) (chain hr hpos hf₀ t).1 :=
  (descent (labelSystem r hr) (chain hr hpos hf₀ t).2 (hpos t) (n t)
    (hpos (t + 1))).choose_spec.2

/-- **Termination**: for `r ≤ 3`, every expansion sequence starting from a standard array with
`r` rows reaches the empty array. -/
theorem terminates {r : ℕ} (hr : r ≤ 3) {A : Arr r} (hA : Std r A) (n : ℕ → ℕ) :
    ∃ T, (seq A n T).len = 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ t, 0 < (seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  obtain ⟨f₀, hf₀⟩ := std_stable hr hA (hpos 0)
  have hdesc := chain_lt hr hpos hf₀
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ordinal.{0})).has_min
      (Set.range fun t => ht (labelSystem r hr) (seq A n t) (chain hr hpos hf₀ t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (hdesc t₀)

/-- A standard array with `r` rows. -/
def StdElt (r : ℕ) : Type := {A : Arr r // Std r A}

/-- One-step expansion: `A R B` iff `B` is nonempty and `A = B[n]`. -/
def StdR (r : ℕ) (A B : StdElt r) : Prop := 0 < B.1.len ∧ ∃ n, A.1 = expand B.1 n

/-- **Well-foundedness** of one-step expansion on standard arrays with `r ≤ 3` rows. -/
theorem StdR_wf {r : ℕ} (hr : r ≤ 3) : WellFounded (StdR r) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun B => ?_⟩
  obtain ⟨B, hB⟩ := B
  have hstep : ∀ t, ∃ N, (B (t + 1)).1 = expand (B t).1 N := fun t => (hB t).2
  choose n hn using hstep
  have hBseq : ∀ t, (B t).1 = seq (B 0).1 n t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hn t, ih]; rfl
  obtain ⟨T, hT⟩ := terminates hr (B 0).2 n
  have hlen : 0 < (B T).1.len := (hB T).1
  rw [hBseq T, hT] at hlen
  exact absurd hlen (lt_irrefl 0)

/-- Pair sequences terminate. -/
theorem pss_terminates {A : Arr 2} (hA : Std 2 A) (n : ℕ → ℕ) : ∃ T, (seq A n T).len = 0 :=
  terminates (by omega) hA n

/-- Trio sequences terminate. -/
theorem tss_terminates {A : Arr 3} (hA : Std 3 A) (n : ℕ → ℕ) : ∃ T, (seq A n T).len = 0 :=
  terminates le_rfl hA n

end Pat
