/-
  Termination of the pair sequence system (BM4 with two rows), with labels in R2:

    ◁₀ = <₁,   ◁₁ = <₂.

  The pair sequences are the two-row arrays reachable from some `(0,0)(1,1)⋯(n,n)`.
-/
import Wilken.Reflect
import Wilken.Chain

open Classical

namespace Wilken

open BM4

/-- The pair sequence `(0,0)(1,1)⋯(n,n)`. -/
def stair (n : ℕ) : Arr 2 := ⟨n + 1, fun i _ => i⟩

/-- Pair sequences: two-row arrays reachable from some `(0,0)(1,1)⋯(n,n)`. -/
inductive PSS : Arr 2 → Prop
  | init (n : ℕ) : PSS (stair n)
  | step {A : Arr 2} (N : ℕ) : PSS A → PSS (expand A N)

/-- `(0,0)(1,1)⋯(n,n)` is labelled by a `<₂`-chain of length `n + 1`. -/
theorem stable_stair (n : ℕ) : ∃ f, Stable labelSystem (stair n) f := by
  obtain ⟨c, hc⟩ := exists_lt2_chain (n + 1)
  refine ⟨c, fun i j hij hj => (hc i j hij hj).1, fun k hk i j hj h => ?_⟩
  have hij : i < j := anc_lt h
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact lt1_of_lt2 (hc i j hij hj)
  · exact hc i j hij hj

/-- Every nonempty pair sequence carries a stable label. -/
theorem pss_stable {A : Arr 2} (hA : PSS A) (h0 : 0 < A.len) : ∃ f, Stable labelSystem A f := by
  induction hA with
  | init n => exact stable_stair n
  | @step A N hA ih =>
    by_cases hlen : A.len = 0
    · rw [expand_of_len_zero hlen] at h0
      omega
    · obtain ⟨f, hf⟩ := ih (Nat.pos_of_ne_zero hlen)
      obtain ⟨g, hg, _⟩ := descent labelSystem hf (Nat.pos_of_ne_zero hlen) N h0
      exact ⟨g, hg⟩

/-- The labels chosen along an expansion sequence with no empty term. -/
private noncomputable def chain {A : Arr 2} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → Ordinal.{0}} (hf₀ : Stable labelSystem A f₀) :
    ∀ t, {g : ℕ → Ordinal.{0} // Stable labelSystem (seq A n t) g} :=
  Nat.rec ⟨f₀, hf₀⟩ fun t g =>
    ⟨_, (descent labelSystem g.2 (hpos t) (n t) (hpos (t + 1))).choose_spec.1⟩

private theorem chain_lt {A : Arr 2} {n : ℕ → ℕ} (hpos : ∀ t, 0 < (seq A n t).len)
    {f₀ : ℕ → Ordinal.{0}} (hf₀ : Stable labelSystem A f₀) (t : ℕ) :
    ht labelSystem (seq A n (t + 1)) (chain hpos hf₀ (t + 1)).1
      < ht labelSystem (seq A n t) (chain hpos hf₀ t).1 :=
  (descent labelSystem (chain hpos hf₀ t).2 (hpos t) (n t) (hpos (t + 1))).choose_spec.2

/-- **Termination of the pair sequence system**: every expansion sequence starting from a pair
sequence reaches the empty array. -/
theorem pss_terminates {A : Arr 2} (hA : PSS A) (n : ℕ → ℕ) : ∃ T, (seq A n T).len = 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : ∀ t, 0 < (seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  obtain ⟨f₀, hf₀⟩ := pss_stable hA (hpos 0)
  have hdesc := chain_lt hpos hf₀
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ordinal.{0})).has_min
      (Set.range fun t => ht labelSystem (seq A n t) (chain hpos hf₀ t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (hdesc t₀)

/-- A pair sequence as an element. -/
def PElt : Type := {A : Arr 2 // PSS A}

/-- One-step expansion on pair sequences: `A R B` iff `B` is nonempty and `A = B[n]`. -/
def PR (A B : PElt) : Prop := 0 < B.1.len ∧ ∃ n, A.1 = expand B.1 n

/-- **Well-foundedness**: there is no infinite descending expansion sequence of pair sequences. -/
theorem PR_wf : WellFounded PR := by
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
  obtain ⟨T, hT⟩ := pss_terminates (B 0).2 n
  have hlen : 0 < (B T).1.len := (hB T).1
  rw [hBseq T, hT] at hlen
  exact absurd hlen (lt_irrefl 0)

end Wilken
