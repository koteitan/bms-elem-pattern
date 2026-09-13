/-
  Arbitrarily long finite `<₂`-chains exist in R2.

  For every `γ < ω₁` a closure argument inside `ω₁` gives `Λ ∈ (γ, ω₁)` such that
  `(Λ; ≤, ≤₁, ≤₂)` is a Σ₂-elementary substructure of `(ω₁; ≤, ≤₁, ≤₂)`.
  Any two such ordinals are `<₂`-related.

  This file only proves existence, using `ω₁`.  Wilken shows that such chains already exist
  below the ordinal of Π¹₁-CA₀; that result is not formalized here.
-/
import Wilken.Reflect

open Classical Cardinal Ordinal

namespace Wilken

/-- `ω₁`. -/
noncomputable abbrev Om : Ordinal.{0} := ω₁

theorem om_pos : (0 : Ordinal.{0}) < Om := Ordinal.omega_pos 1

theorem om_succ_lt {a : Ordinal.{0}} (h : a < Om) : Order.succ a < Om := by
  have hl : Order.IsSuccLimit (ω₁ : Ordinal.{0}) := by
    rw [← Cardinal.ord_aleph]
    exact Cardinal.isSuccLimit_ord (by simp)
  exact hl.succ_lt h

theorem countable_Iio {γ : Ordinal.{0}} (h : γ < Om) : (Set.Iio γ).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  rw [Om, ← Cardinal.ord_aleph, Cardinal.lt_ord, Cardinal.lt_aleph_one_iff] at h
  exact h

/-! ### Tuples -/

theorem cat_congr_left {k : ℕ} {p p' q : ℕ → Ordinal.{0}} (h : ∀ i < k, p i = p' i) :
    cat k p q = cat k p' q := by
  funext i
  unfold cat
  split_ifs with hi
  · exact h i hi
  · rfl

theorem sat_param_congr {M : Ordinal.{0}} {k m l : ℕ} {D : Set (Diag (k + m + l))}
    {p p' : ℕ → Ordinal.{0}} (h : ∀ i < k, p i = p' i) :
    Sat R2 M k m l D p ↔ Sat R2 M k m l D p' := by
  have e : ∀ q, cat k p q = cat k p' q := fun q => cat_congr_left h
  simp only [Sat, e]

theorem cat_assoc_lt {k m l : ℕ} {p x y z : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < k + m + l) :
    cat (k + m) (cat k p x) (cat l y z) i = cat k p (cat m x y) i := by
  unfold cat
  split_ifs <;> first | rfl | (congr 1; omega)

/-! ### Enumerating the ordinals below a countable ordinal -/

/-- An enumeration of the ordinals below `γ` (onto when `0 < γ < ω₁`). -/
noncomputable def enumBelow (γ : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : (Set.Iio γ).Countable ∧ (Set.Iio γ).Nonempty then
    Classical.choose (h.1.exists_eq_range h.2)
  else fun _ => 0

theorem enumBelow_surj {γ : Ordinal.{0}} (hγ : γ < Om) {a : Ordinal.{0}} (ha : a < γ) :
    ∃ t, enumBelow γ t = a := by
  have h : (Set.Iio γ).Countable ∧ (Set.Iio γ).Nonempty := ⟨countable_Iio hγ, ⟨a, ha⟩⟩
  have hs := Classical.choose_spec (h.1.exists_eq_range h.2)
  have hmem : a ∈ Set.Iio γ := ha
  rw [hs] at hmem
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, by simp only [enumBelow, dif_pos h]; exact ht⟩

/-- Parameters below `γ`, coded by a list of indices. -/
noncomputable def params (γ : Ordinal.{0}) (l : List ℕ) : ℕ → Ordinal.{0} :=
  fun i => enumBelow γ (l.getD i 0)

theorem exists_params {γ : Ordinal.{0}} (hγ : γ < Om) {k : ℕ} {p : ℕ → Ordinal.{0}}
    (hp : ∀ i < k, p i < γ) : ∃ l : List ℕ, ∀ i < k, params γ l i = p i := by
  choose t ht using fun i (hi : i < k) => enumBelow_surj hγ (hp i hi)
  refine ⟨(List.range k).map fun i => if h : i < k then t i h else 0, fun i hi => ?_⟩
  unfold params
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [hi, ht]

/-! ### Closure under witnesses -/

/-- A Σ₂ formula: numbers of parameters, existential and universal variables, and the matrix. -/
abbrev Form : Type := Σ k : ℕ, Σ m : ℕ, Σ l : ℕ, Set (Diag (k + m + l))

/-- The height of the chosen witness of a true Σ₂ statement in `ω₁` (`0` if it is false). -/
noncomputable def witHeight (φ : Form) (p : ℕ → Ordinal.{0}) : Ordinal.{0} :=
  if h : Sat R2 Om φ.1 φ.2.1 φ.2.2.1 φ.2.2.2 p then
    (Finset.range φ.2.1).sup fun i => Order.succ (Classical.choose h i)
  else 0

theorem witHeight_lt (φ : Form) (p : ℕ → Ordinal.{0}) : witHeight φ p < Om := by
  unfold witHeight
  split_ifs with h
  · refine (Finset.sup_lt_iff (lt_of_le_of_lt bot_le om_pos)).mpr fun i hi => ?_
    exact om_succ_lt ((Classical.choose_spec h).1 i (Finset.mem_range.mp hi))
  · exact om_pos

/-- One closure step. -/
noncomputable def next (γ : Ordinal.{0}) : Ordinal.{0} :=
  Order.succ (max γ (⨆ q : Form × List ℕ, witHeight q.1 (params γ q.2)))

theorem lt_next (γ : Ordinal.{0}) : γ < next γ :=
  lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)

theorem next_lt {γ : Ordinal.{0}} (h : γ < Om) : next γ < Om :=
  om_succ_lt (max_lt h (Ordinal.iSup_lt_omega_one fun _ => witHeight_lt _ _))

/-- A true Σ₂ statement in `ω₁` with parameters below `γ` has a witness below `next γ`. -/
theorem wit_below {γ : Ordinal.{0}} (hγ : γ < Om) {k m l : ℕ} {D : Set (Diag (k + m + l))}
    {p : ℕ → Ordinal.{0}} (hp : ∀ i < k, p i < γ) (h : Sat R2 Om k m l D p) :
    ∃ x : ℕ → Ordinal.{0}, (∀ i < m, x i < next γ) ∧
      ∀ y : ℕ → Ordinal.{0}, (∀ j < l, y j < Om) →
        diag R2 (k + m + l) (cat k p (cat m x y)) ∈ D := by
  obtain ⟨l0, hl0⟩ := exists_params hγ hp
  have hpp : ∀ i < k, params γ l0 i = p i := hl0
  have h' : Sat R2 Om k m l D (params γ l0) := (sat_param_congr hpp).mpr h
  refine ⟨Classical.choose h', fun i hi => ?_, fun y hy => ?_⟩
  · have hw : witHeight ⟨k, m, l, D⟩ (params γ l0) =
        (Finset.range m).sup fun i => Order.succ (Classical.choose h' i) := dif_pos h'
    have h1 : Order.succ (Classical.choose h' i) ≤ witHeight ⟨k, m, l, D⟩ (params γ l0) := by
      rw [hw]
      exact Finset.le_sup (f := fun i => Order.succ (Classical.choose h' i))
        (Finset.mem_range.mpr hi)
    have h2 : witHeight ⟨k, m, l, D⟩ (params γ l0) ≤
        ⨆ q : Form × List ℕ, witHeight q.1 (params γ q.2) :=
      Ordinal.le_iSup (fun q : Form × List ℕ => witHeight q.1 (params γ q.2)) (⟨k, m, l, D⟩, l0)
    have h3 := (Order.lt_succ (Classical.choose h' i)).trans_le (h1.trans (h2.trans
      (le_max_right γ _)))
    exact h3.trans (Order.lt_succ _)
  · have := (Classical.choose_spec h').2 y hy
    rwa [cat_congr_left hpp] at this

/-! ### The tower and its limit -/

/-- `γ, next γ, next (next γ), …` -/
noncomputable def tower (γ : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => γ
  | n + 1 => next (tower γ n)

/-- The limit of the tower. -/
noncomputable def lam (γ : Ordinal.{0}) : Ordinal.{0} := ⨆ n, tower γ n

theorem tower_lt {γ : Ordinal.{0}} (hγ : γ < Om) : ∀ n, tower γ n < Om
  | 0 => hγ
  | n + 1 => next_lt (tower_lt hγ n)

theorem tower_mono (γ : Ordinal.{0}) {n n' : ℕ} (h : n ≤ n') : tower γ n ≤ tower γ n' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (lt_next _).le

theorem tower_le_lam (γ : Ordinal.{0}) (n : ℕ) : tower γ n ≤ lam γ :=
  Ordinal.le_iSup (fun n => tower γ n) n

theorem lam_lt {γ : Ordinal.{0}} (hγ : γ < Om) : lam γ < Om :=
  Ordinal.iSup_lt_omega_one (tower_lt hγ)

theorem lt_lam (γ : Ordinal.{0}) : γ < lam γ :=
  (lt_next γ).trans_le (tower_le_lam γ 1)

theorem exists_tower {γ : Ordinal.{0}} {p : ℕ → Ordinal.{0}} :
    ∀ k, (∀ i < k, p i < lam γ) → ∃ n, ∀ i < k, p i < tower γ n
  | 0, _ => ⟨0, fun i hi => absurd hi (by omega)⟩
  | k + 1, hp => by
    obtain ⟨n, hn⟩ := exists_tower k fun i hi => hp i (by omega)
    obtain ⟨n', hn'⟩ := Ordinal.lt_iSup_iff.mp (hp k (by omega))
    refine ⟨max n n', fun i hi => ?_⟩
    rcases (by omega : i < k ∨ i = k) with h | rfl
    · exact (hn i h).trans_le (tower_mono γ (le_max_left _ _))
    · exact hn'.trans_le (tower_mono γ (le_max_right _ _))

/-- True Σ₂ statements in `ω₁` with parameters below `lam γ` hold in `lam γ`. -/
theorem lam_down {γ : Ordinal.{0}} (hγ : γ < Om) {k m l : ℕ} {D : Set (Diag (k + m + l))}
    {p : ℕ → Ordinal.{0}} (hp : ∀ i < k, p i < lam γ) (h : Sat R2 Om k m l D p) :
    Sat R2 (lam γ) k m l D p := by
  obtain ⟨n, hn⟩ := exists_tower k hp
  obtain ⟨x, hx, hD⟩ := wit_below (tower_lt hγ n) hn h
  exact ⟨x, fun i hi => (hx i hi).trans_le (tower_le_lam γ (n + 1)),
    fun y hy => hD y fun j hj => (hy j hj).trans (lam_lt hγ)⟩

/-- `(lam γ; ≤, ≤₁, ≤₂) ≼_{Σ₂} (ω₁; ≤, ≤₁, ≤₂)`. -/
theorem lam_elem {γ : Ordinal.{0}} (hγ : γ < Om) {k m l : ℕ} {D : Set (Diag (k + m + l))}
    {p : ℕ → Ordinal.{0}} (hp : ∀ i < k, p i < lam γ) :
    Sat R2 (lam γ) k m l D p ↔ Sat R2 Om k m l D p := by
  refine ⟨fun ⟨x, hx, hD⟩ => ⟨x, fun i hi => (hx i hi).trans (lam_lt hγ), fun y hy => ?_⟩,
    lam_down hγ hp⟩
  by_contra hnot
  let D' : Set (Diag (k + m + l + 0)) := {d | d ∉ D}
  have hp' : ∀ i < k + m, cat k p x i < lam γ := by
    intro i hi
    unfold cat
    split_ifs with h1
    · exact hp i h1
    · exact hx _ (by omega)
  have heq : ∀ y' z : ℕ → Ordinal.{0},
      diag R2 (k + m + l + 0) (cat (k + m) (cat k p x) (cat l y' z)) =
        diag R2 (k + m + l) (cat k p (cat m x y')) := by
    intro y' z
    funext a b
    simp only [diag]
    rw [cat_assoc_lt (by omega : (a : ℕ) < k + m + l), cat_assoc_lt (by omega : (b : ℕ) < k + m + l)]
  have hΩ : Sat R2 Om (k + m) l 0 D' (cat k p x) := by
    refine ⟨y, fun j hj => hy j hj, fun z _ => ?_⟩
    show diag R2 (k + m + l + 0) (cat (k + m) (cat k p x) (cat l y z)) ∉ D
    rw [heq]
    exact hnot
  obtain ⟨y', hy', hD'⟩ := lam_down hγ hp' hΩ
  have h1 := hD' (fun _ => 0) (fun j hj => absurd hj (by omega))
  change diag R2 (k + m + l + 0) (cat (k + m) (cat k p x) (cat l y' fun _ => 0)) ∉ D at h1
  rw [heq] at h1
  exact h1 (hD y' hy')

/-! ### Chains -/

theorem lt2_lam {γ δ : Ordinal.{0}} (hγ : γ < Om) (hδ : δ < Om) (hlt : lam γ < lam δ) :
    lt2 (lam γ) (lam δ) := by
  refine ⟨hlt, le2_iff.mpr ⟨hlt.le, fun k m l D p hp => ?_⟩⟩
  exact (lam_elem hγ hp).trans (lam_elem hδ fun i hi => (hp i hi).trans hlt).symm

/-- `lam 0 < lam (lam 0) < ⋯` -/
noncomputable def lamChain : ℕ → Ordinal.{0}
  | 0 => lam 0
  | n + 1 => lam (lamChain n)

theorem lamChain_lt : ∀ n, lamChain n < Om
  | 0 => lam_lt om_pos
  | n + 1 => lam_lt (lamChain_lt n)

theorem lamChain_strictMono : StrictMono lamChain :=
  strictMono_nat_of_lt_succ fun n => lt_lam (lamChain n)

/-- Every finite length of `<₂`-chain occurs in R2. -/
theorem exists_lt2_chain (n : ℕ) :
    ∃ c : ℕ → Ordinal.{0}, ∀ i j, i < j → j < n → lt2 (c i) (c j) := by
  refine ⟨fun i => lamChain (i + 1), fun i j hij _ => ?_⟩
  have h : lamChain (i + 1) < lamChain (j + 1) := lamChain_strictMono (by omega)
  exact lt2_lam (lamChain_lt i) (lamChain_lt j) h

end Wilken
