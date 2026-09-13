/-
  The structure R2 = (Ord; ≤, ≤₁, ≤₂) of pure elementary patterns of order 2.

    α ≤ᵢ β  :⟺  (α; ≤, ≤₁, ≤₂) is a Σᵢ-elementary substructure of (β; ≤, ≤₁, ≤₂)

  defined simultaneously for i = 1, 2 by recursion on β.

  Formulas are not written as syntax.  A quantifier-free formula in `n` variables is a set `D`
  of atomic diagrams of `n`-tuples, and a Σ₂ formula `∃x₀…x_{m-1} ∀y₀…y_{l-1} ψ` with parameters
  `p₀…p_{k-1}` is the statement `Sat R M k m l D p` below.  Σ₁ formulas are the case `l = 0`.
-/
import Mathlib

open Classical

namespace Wilken

/-- A pair of binary relations `(≤₁, ≤₂)` on ordinals. -/
structure RelPair where
  le1 : Ordinal.{0} → Ordinal.{0} → Prop
  le2 : Ordinal.{0} → Ordinal.{0} → Prop

/-- Atomic diagrams of `n`-tuples: for each pair of positions, the truth values of
`≤`, `≤₁`, `≤₂`. -/
abbrev Diag (n : ℕ) := Fin n → Fin n → Bool × Bool × Bool

/-- The truth values of `a ≤ b`, `a ≤₁ b`, `a ≤₂ b`. -/
noncomputable def bits (R : RelPair) (a b : Ordinal.{0}) : Bool × Bool × Bool :=
  (decide (a ≤ b), decide (R.le1 a b), decide (R.le2 a b))

/-- The atomic diagram of the first `n` entries of a tuple. -/
noncomputable def diag (R : RelPair) (n : ℕ) (v : ℕ → Ordinal.{0}) : Diag n :=
  fun a b => bits R (v a) (v b)

/-- Concatenation: the first `k` entries come from `p`, the rest from `q`. -/
def cat (k : ℕ) (p q : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0} :=
  fun i => if i < k then p i else q (i - k)

/-- The Σ₂ statement `∃ x < M ∀ y < M, diag(p, x, y) ∈ D` in the structure `(M; ≤, ≤₁, ≤₂)`,
with `k` parameters `p`, `m` existential and `l` universal variables. -/
def Sat (R : RelPair) (M : Ordinal.{0}) (k m l : ℕ) (D : Set (Diag (k + m + l)))
    (p : ℕ → Ordinal.{0}) : Prop :=
  ∃ x : ℕ → Ordinal.{0}, (∀ i < m, x i < M) ∧
    ∀ y : ℕ → Ordinal.{0}, (∀ j < l, y j < M) → diag R (k + m + l) (cat k p (cat m x y)) ∈ D

/-- `(α; ≤, ≤₁, ≤₂) ≼_{Σ₁} (β; ≤, ≤₁, ≤₂)`. -/
def Elem1 (R : RelPair) (α β : Ordinal.{0}) : Prop :=
  ∀ (k m : ℕ) (D : Set (Diag (k + m + 0))) (p : ℕ → Ordinal.{0}), (∀ i < k, p i < α) →
    (Sat R α k m 0 D p ↔ Sat R β k m 0 D p)

/-- `(α; ≤, ≤₁, ≤₂) ≼_{Σ₂} (β; ≤, ≤₁, ≤₂)`. -/
def Elem2 (R : RelPair) (α β : Ordinal.{0}) : Prop :=
  ∀ (k m l : ℕ) (D : Set (Diag (k + m + l))) (p : ℕ → Ordinal.{0}), (∀ i < k, p i < α) →
    (Sat R α k m l D p ↔ Sat R β k m l D p)

/-! ### The recursion on `β` -/

/-- The relations on pairs below `β`, read off from the values at earlier stages. -/
def stage (β : Ordinal.{0}) (IH : ∀ b : Ordinal.{0}, b < β → Ordinal.{0} → Prop × Prop) :
    RelPair :=
  ⟨fun a b => ∃ h : b < β, a ≤ b ∧ (IH b h a).1, fun a b => ∃ h : b < β, a ≤ b ∧ (IH b h a).2⟩

/-- `R2fix β α = (α ≤₁ β, α ≤₂ β)`. -/
noncomputable def R2fix : Ordinal.{0} → Ordinal.{0} → Prop × Prop :=
  (wellFounded_lt (α := Ordinal.{0})).fix (C := fun _ => Ordinal.{0} → Prop × Prop)
    (fun β IH α => (α ≤ β ∧ Elem1 (stage β IH) α β, α ≤ β ∧ Elem2 (stage β IH) α β))

/-- `a ≤₁ b`. -/
def le1 (a b : Ordinal.{0}) : Prop := (R2fix b a).1

/-- `a ≤₂ b`. -/
def le2 (a b : Ordinal.{0}) : Prop := (R2fix b a).2

/-- The relations of R2. -/
def R2 : RelPair := ⟨le1, le2⟩

/-- `a <₁ b`. -/
def lt1 (a b : Ordinal.{0}) : Prop := a < b ∧ le1 a b

/-- `a <₂ b`. -/
def lt2 (a b : Ordinal.{0}) : Prop := a < b ∧ le2 a b

theorem R2fix_eq (β : Ordinal.{0}) :
    R2fix β = fun α => (α ≤ β ∧ Elem1 (stage β fun b _ => R2fix b) α β,
      α ≤ β ∧ Elem2 (stage β fun b _ => R2fix b) α β) :=
  WellFounded.fix_eq _ _ _

theorem le1_le {a b : Ordinal.{0}} (h : le1 a b) : a ≤ b := by
  have h' := h
  unfold le1 at h'
  rw [R2fix_eq] at h'
  exact h'.1

theorem le2_le {a b : Ordinal.{0}} (h : le2 a b) : a ≤ b := by
  have h' := h
  unfold le2 at h'
  rw [R2fix_eq] at h'
  exact h'.1

/-! ### Only pairs below the top matter -/

theorem diag_congr {R R' : RelPair} {N : Ordinal.{0}} {n : ℕ} {v : ℕ → Ordinal.{0}}
    (hR : ∀ a b, a < N → b < N → (R.le1 a b ↔ R'.le1 a b) ∧ (R.le2 a b ↔ R'.le2 a b))
    (hv : ∀ i < n, v i < N) : diag R n v = diag R' n v := by
  funext a b
  have h := hR (v a) (v b) (hv a a.2) (hv b b.2)
  simp only [diag, bits, h.1, h.2]

theorem cat_lt {k m l : ℕ} {p x y : ℕ → Ordinal.{0}} {N : Ordinal.{0}}
    (hp : ∀ i < k, p i < N) (hx : ∀ i < m, x i < N) (hy : ∀ j < l, y j < N) :
    ∀ i < k + m + l, cat k p (cat m x y) i < N := by
  intro i hi
  unfold cat
  split_ifs with h1 h2
  · exact hp i h1
  · exact hx _ (by omega)
  · exact hy _ (by omega)

theorem sat_congr {R R' : RelPair} {N M : Ordinal.{0}} (hMN : M ≤ N)
    (hR : ∀ a b, a < N → b < N → (R.le1 a b ↔ R'.le1 a b) ∧ (R.le2 a b ↔ R'.le2 a b))
    {k m l : ℕ} {D : Set (Diag (k + m + l))} {p : ℕ → Ordinal.{0}} (hp : ∀ i < k, p i < N) :
    Sat R M k m l D p ↔ Sat R' M k m l D p := by
  constructor
  · rintro ⟨x, hx, hD⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    rw [← diag_congr hR (cat_lt hp (fun i hi => (hx i hi).trans_le hMN)
      (fun j hj => (hy j hj).trans_le hMN))]
    exact hD y hy
  · rintro ⟨x, hx, hD⟩
    refine ⟨x, hx, fun y hy => ?_⟩
    rw [diag_congr hR (cat_lt hp (fun i hi => (hx i hi).trans_le hMN)
      (fun j hj => (hy j hj).trans_le hMN))]
    exact hD y hy

theorem stage_agree (β : Ordinal.{0}) :
    ∀ a b, a < β → b < β →
      ((stage β fun b _ => R2fix b).le1 a b ↔ R2.le1 a b) ∧
      ((stage β fun b _ => R2fix b).le2 a b ↔ R2.le2 a b) := by
  intro a b _ hb
  constructor
  · exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hb, le1_le h, h⟩⟩
  · exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hb, le2_le h, h⟩⟩

theorem elem1_congr {α β : Ordinal.{0}} (hαβ : α ≤ β) :
    Elem1 (stage β fun b _ => R2fix b) α β ↔ Elem1 R2 α β := by
  have hR := stage_agree β
  constructor
  · intro h k m D p hp
    have hpN : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [← sat_congr hαβ hR hpN, ← sat_congr le_rfl hR hpN]
    exact h k m D p hp
  · intro h k m D p hp
    have hpN : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [sat_congr hαβ hR hpN, sat_congr le_rfl hR hpN]
    exact h k m D p hp

theorem elem2_congr {α β : Ordinal.{0}} (hαβ : α ≤ β) :
    Elem2 (stage β fun b _ => R2fix b) α β ↔ Elem2 R2 α β := by
  have hR := stage_agree β
  constructor
  · intro h k m l D p hp
    have hpN : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [← sat_congr hαβ hR hpN, ← sat_congr le_rfl hR hpN]
    exact h k m l D p hp
  · intro h k m l D p hp
    have hpN : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [sat_congr hαβ hR hpN, sat_congr le_rfl hR hpN]
    exact h k m l D p hp

/-- The defining equivalence of `≤₁`. -/
theorem le1_iff {α β : Ordinal.{0}} : le1 α β ↔ α ≤ β ∧ Elem1 R2 α β := by
  unfold le1
  rw [R2fix_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (elem1_congr h1).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (elem1_congr h1).mpr h2⟩⟩

/-- The defining equivalence of `≤₂`. -/
theorem le2_iff {α β : Ordinal.{0}} : le2 α β ↔ α ≤ β ∧ Elem2 R2 α β := by
  unfold le2
  rw [R2fix_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (elem2_congr h1).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (elem2_congr h1).mpr h2⟩⟩

/-! ### Basic properties -/

theorem le1_refl (a : Ordinal.{0}) : le1 a a :=
  le1_iff.mpr ⟨le_rfl, fun _ _ _ _ _ => Iff.rfl⟩

theorem le2_refl (a : Ordinal.{0}) : le2 a a :=
  le2_iff.mpr ⟨le_rfl, fun _ _ _ _ _ _ => Iff.rfl⟩

theorem le1_of_le2 {a b : Ordinal.{0}} (h : le2 a b) : le1 a b := by
  obtain ⟨hab, he⟩ := le2_iff.mp h
  exact le1_iff.mpr ⟨hab, fun k m D p hp => he k m 0 D p hp⟩

theorem le1_trans {a b c : Ordinal.{0}} (hab : le1 a b) (hbc : le1 b c) : le1 a c := by
  obtain ⟨h1, e1⟩ := le1_iff.mp hab
  obtain ⟨h2, e2⟩ := le1_iff.mp hbc
  refine le1_iff.mpr ⟨h1.trans h2, fun k m D p hp => ?_⟩
  exact (e1 k m D p hp).trans (e2 k m D p fun i hi => (hp i hi).trans_le h1)

theorem le2_trans {a b c : Ordinal.{0}} (hab : le2 a b) (hbc : le2 b c) : le2 a c := by
  obtain ⟨h1, e1⟩ := le2_iff.mp hab
  obtain ⟨h2, e2⟩ := le2_iff.mp hbc
  refine le2_iff.mpr ⟨h1.trans h2, fun k m l D p hp => ?_⟩
  exact (e1 k m l D p hp).trans (e2 k m l D p fun i hi => (hp i hi).trans_le h1)

theorem lt1_trans {a b c : Ordinal.{0}} (hab : lt1 a b) (hbc : lt1 b c) : lt1 a c :=
  ⟨hab.1.trans hbc.1, le1_trans hab.2 hbc.2⟩

theorem lt2_trans {a b c : Ordinal.{0}} (hab : lt2 a b) (hbc : lt2 b c) : lt2 a c :=
  ⟨hab.1.trans hbc.1, le2_trans hab.2 hbc.2⟩

theorem lt1_of_lt2 {a b : Ordinal.{0}} (h : lt2 a b) : lt1 a b := ⟨h.1, le1_of_le2 h.2⟩

/-- Σ₁ statements go up. -/
theorem sat_up {R : RelPair} {M M' : Ordinal.{0}} (h : M ≤ M') {k m : ℕ}
    {D : Set (Diag (k + m + 0))} {p : ℕ → Ordinal.{0}} :
    Sat R M k m 0 D p → Sat R M' k m 0 D p := by
  rintro ⟨x, hx, hD⟩
  exact ⟨x, fun i hi => (hx i hi).trans_le h, fun y _ => hD y (fun j hj => absurd hj (by omega))⟩

/-- `≤₁` respects `≤`: `a ≤ b ≤ c` and `a ≤₁ c` give `a ≤₁ b`. -/
theorem le1_of_le_of_le1 {a b c : Ordinal.{0}} (hab : a ≤ b) (hbc : b ≤ c) (hac : le1 a c) :
    le1 a b := by
  obtain ⟨_, e⟩ := le1_iff.mp hac
  refine le1_iff.mpr ⟨hab, fun k m D p hp => ⟨sat_up hab, fun hb => ?_⟩⟩
  exact (e k m D p hp).mpr (sat_up hbc hb)

/-- Continuity of `≤₁` at a limit: if `y ≤₁ v` for all `v ∈ [y, α)` and `α` is closed under
successor, then `y ≤₁ α`. -/
theorem le1_of_forall {y α : Ordinal.{0}} (hyα : y ≤ α)
    (hlim : ∀ z < α, Order.succ z < α) (h : ∀ v, y ≤ v → v < α → le1 y v) : le1 y α := by
  rcases hyα.lt_or_eq with hlt | rfl
  · refine le1_iff.mpr ⟨hyα, fun k m D p hp => ⟨sat_up hyα, ?_⟩⟩
    rintro ⟨x, hx, hD⟩
    set v := max y ((Finset.range m).sup fun i => Order.succ (x i)) with hv
    have hbot : (⊥ : Ordinal.{0}) < α := lt_of_le_of_lt bot_le hlt
    have hvα : v < α := by
      refine max_lt hlt ((Finset.sup_lt_iff hbot).mpr fun i hi => ?_)
      exact hlim _ (hx i (Finset.mem_range.mp hi))
    have hxv : ∀ i < m, x i < v := by
      intro i hi
      refine lt_of_lt_of_le (Order.lt_succ (x i)) (le_trans ?_ (le_max_right _ _))
      exact Finset.le_sup (f := fun i => Order.succ (x i)) (Finset.mem_range.mpr hi)
    have hsv : Sat R2 v k m 0 D p :=
      ⟨x, hxv, fun z _ => hD z (fun j hj => absurd hj (by omega))⟩
    obtain ⟨_, ev⟩ := le1_iff.mp (h v (le_max_left _ _) hvα)
    exact (ev k m D p hp).mpr hsv
  · exact le1_refl y

/-- The atomic bits of a diagram, as propositions. -/
theorem bits_eq_iff {R : RelPair} {a b c d : Ordinal.{0}} (h : bits R a b = bits R c d) :
    (a ≤ b ↔ c ≤ d) ∧ (R.le1 a b ↔ R.le1 c d) ∧ (R.le2 a b ↔ R.le2 c d) := by
  simp only [bits, Prod.mk.injEq, decide_eq_decide] at h
  exact h

/-- A `<₁`-lower end is closed under successor. -/
theorem succ_lt_of_lt1 {α β : Ordinal.{0}} (h : lt1 α β) : ∀ z < α, Order.succ z < α := by
  intro z hz
  by_contra hcon
  have hαz : α = Order.succ z :=
    le_antisymm (not_lt.mp hcon) (Order.succ_le_of_lt hz)
  obtain ⟨_, e⟩ := le1_iff.mp h.2
  let D : Set (Diag (1 + 1 + 0)) :=
    {d | (d ⟨0, by decide⟩ ⟨1, by decide⟩).1 = true ∧ (d ⟨1, by decide⟩ ⟨0, by decide⟩).1 = false}
  have hβ : Sat R2 β 1 1 0 D (fun _ => z) := by
    refine ⟨fun _ => α, fun _ _ => h.1, fun y _ => ?_⟩
    simp [D, diag, bits, cat, hz.le, not_le.mpr hz]
  obtain ⟨x, hx, hD⟩ := (e 1 1 D (fun _ => z) fun _ _ => hz).mpr hβ
  have hd := hD (fun _ => 0) (fun j hj => absurd hj (by omega))
  simp only [D, diag, bits, cat, Set.mem_setOf_eq] at hd
  have hzx : z < x 0 := by
    simp at hd
    exact hd.2
  have hx0 : x 0 < α := hx 0 (by omega)
  rw [hαz] at hx0
  exact absurd (Order.succ_le_of_lt hzx) (not_le.mpr hx0)

end Wilken
