/-
  Arbitrarily long finite chains in R_N whose members are related at every level.

  For every `γ < ω₁`, a closure argument inside `ω₁` gives `Λ ∈ (γ, ω₁)` such that every
  formula with parameters below `Λ` has the same truth value in `Λ` and in `ω₁`.
  Any two such ordinals are related by all of `≤₁, …, ≤_N`.

  This file only proves existence, using `ω₁`.  How small such chains can be is not formalized.
-/
import Pattern.Basic

open Classical Cardinal Ordinal

namespace Pat

variable {N : ℕ}

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

/-- A formula: size of the diagram, matrix, quantifier blocks, number of parameters. -/
abbrev Form (N : ℕ) : Type := Σ n : ℕ, Set (Diag N n) × List ℕ × ℕ

/-- The height of the chosen witness of a true statement in `ω₁` (`0` otherwise). -/
noncomputable def witHeight (φ : Form N) (p : ℕ → Ordinal.{0}) : Ordinal.{0} :=
  match φ with
  | ⟨n, D, b :: bs, k⟩ =>
    if h : Sig (RN N) Om n D (b :: bs) k p then
      (Finset.range b).sup fun i => Order.succ (Classical.choose (sig_cons.mp h) i)
    else 0
  | ⟨_, _, [], _⟩ => 0

theorem witHeight_lt (φ : Form N) (p : ℕ → Ordinal.{0}) : witHeight φ p < Om := by
  obtain ⟨n, D, bs, k⟩ := φ
  cases bs with
  | nil => exact om_pos
  | cons b bs =>
    simp only [witHeight]
    split_ifs with h
    · refine (Finset.sup_lt_iff (lt_of_le_of_lt bot_le om_pos)).mpr fun i hi => ?_
      exact om_succ_lt ((Classical.choose_spec (sig_cons.mp h)).1 i (Finset.mem_range.mp hi))
    · exact om_pos

/-- One closure step. -/
noncomputable def next (N : ℕ) (γ : Ordinal.{0}) : Ordinal.{0} :=
  Order.succ (max γ (⨆ q : Form N × List ℕ, witHeight q.1 (params γ q.2)))

theorem lt_next (γ : Ordinal.{0}) : γ < next N γ :=
  lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)

theorem next_lt {γ : Ordinal.{0}} (h : γ < Om) : next N γ < Om :=
  om_succ_lt (max_lt h (Ordinal.iSup_lt_omega_one fun _ => witHeight_lt _ _))

/-- A true statement in `ω₁` with parameters below `γ` has a witness below `next γ`. -/
theorem wit_below {γ : Ordinal.{0}} (hγ : γ < Om) {n : ℕ} {D : Set (Diag N n)} {b : ℕ}
    {bs : List ℕ} {k : ℕ} {p : ℕ → Ordinal.{0}} (hn : n ≤ k + (b :: bs).sum)
    (hp : ∀ i < k, p i < γ) (h : Sig (RN N) Om n D (b :: bs) k p) :
    ∃ x : ℕ → Ordinal.{0}, (∀ i < b, x i < next N γ) ∧
      ¬ Sig (RN N) Om n D bs (k + b) (cat k p x) := by
  obtain ⟨l0, hl0⟩ := exists_params hγ hp
  have h' : Sig (RN N) Om n D (b :: bs) k (params γ l0) := (sig_param_congr hn hl0).mpr h
  have hc := sig_cons.mp h'
  refine ⟨Classical.choose hc, fun i hi => ?_, ?_⟩
  · have hw : witHeight (⟨n, D, b :: bs, k⟩ : Form N) (params γ l0) =
        (Finset.range b).sup fun i => Order.succ (Classical.choose hc i) := by
      simp only [witHeight, dif_pos h']
    have h1 : Order.succ (Classical.choose hc i) ≤
        witHeight (⟨n, D, b :: bs, k⟩ : Form N) (params γ l0) := by
      rw [hw]
      exact Finset.le_sup (f := fun i => Order.succ (Classical.choose hc i))
        (Finset.mem_range.mpr hi)
    have h2 : witHeight (⟨n, D, b :: bs, k⟩ : Form N) (params γ l0) ≤
        ⨆ q : Form N × List ℕ, witHeight q.1 (params γ q.2) :=
      Ordinal.le_iSup (fun q : Form N × List ℕ => witHeight q.1 (params γ q.2))
        (⟨n, D, b :: bs, k⟩, l0)
    exact ((Order.lt_succ _).trans_le (h1.trans (h2.trans (le_max_right γ _)))).trans
      (Order.lt_succ _)
  · have := (Classical.choose_spec hc).2
    rwa [cat_congr_left hl0] at this

/-! ### The tower and its limit -/

/-- `γ, next γ, next (next γ), …` -/
noncomputable def tower (N : ℕ) (γ : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => γ
  | t + 1 => next N (tower N γ t)

/-- The limit of the tower. -/
noncomputable def lam (N : ℕ) (γ : Ordinal.{0}) : Ordinal.{0} := ⨆ t, tower N γ t

theorem tower_lt {γ : Ordinal.{0}} (hγ : γ < Om) : ∀ t, tower N γ t < Om
  | 0 => hγ
  | t + 1 => next_lt (tower_lt hγ t)

theorem tower_mono (γ : Ordinal.{0}) {t t' : ℕ} (h : t ≤ t') : tower N γ t ≤ tower N γ t' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (lt_next _).le

theorem tower_le_lam (γ : Ordinal.{0}) (t : ℕ) : tower N γ t ≤ lam N γ :=
  Ordinal.le_iSup (fun t => tower N γ t) t

theorem lam_lt {γ : Ordinal.{0}} (hγ : γ < Om) : lam N γ < Om :=
  Ordinal.iSup_lt_omega_one (tower_lt hγ)

theorem lt_lam (γ : Ordinal.{0}) : γ < lam N γ :=
  (lt_next γ).trans_le (tower_le_lam γ 1)

theorem exists_tower {γ : Ordinal.{0}} {p : ℕ → Ordinal.{0}} :
    ∀ k, (∀ i < k, p i < lam N γ) → ∃ t, ∀ i < k, p i < tower N γ t
  | 0, _ => ⟨0, fun i hi => absurd hi (by omega)⟩
  | k + 1, hp => by
    obtain ⟨t, ht⟩ := exists_tower k fun i hi => hp i (by omega)
    obtain ⟨t', ht'⟩ := Ordinal.lt_iSup_iff.mp (hp k (by omega))
    refine ⟨max t t', fun i hi => ?_⟩
    rcases (by omega : i < k ∨ i = k) with h | rfl
    · exact (ht i h).trans_le (tower_mono γ (le_max_left _ _))
    · exact ht'.trans_le (tower_mono γ (le_max_right _ _))

/-- Every formula with parameters below `lam γ` has the same truth value in `lam γ` and `ω₁`. -/
theorem lam_elem {γ : Ordinal.{0}} (hγ : γ < Om) {n : ℕ} {D : Set (Diag N n)} :
    ∀ (bs : List ℕ) (k : ℕ) (p : ℕ → Ordinal.{0}), n ≤ k + bs.sum →
      (∀ i < k, p i < lam N γ) → (Sig (RN N) (lam N γ) n D bs k p ↔ Sig (RN N) Om n D bs k p)
  | [], _, _, _, _ => Iff.rfl
  | b :: bs, k, p, hn, hp => by
    have hn' : n ≤ (k + b) + bs.sum := by simp at hn; omega
    constructor
    · rintro ⟨x, hx, hnot⟩
      refine ⟨x, fun i hi => (hx i hi).trans (lam_lt hγ), fun hΩ => hnot ?_⟩
      exact (lam_elem hγ bs (k + b) (cat k p x) hn' (cat_lt hp hx)).mpr hΩ
    · intro h
      obtain ⟨t, ht⟩ := exists_tower k hp
      obtain ⟨x, hx, hnot⟩ := wit_below (tower_lt hγ t) hn ht h
      have hx' : ∀ i < b, x i < lam N γ :=
        fun i hi => (hx i hi).trans_le (tower_le_lam γ (t + 1))
      exact ⟨x, hx', fun hl =>
        hnot ((lam_elem hγ bs (k + b) (cat k p x) hn' (cat_lt hp hx')).mp hl)⟩

/-- Two such limits are related at every level. -/
theorem lab_lam {γ δ : Ordinal.{0}} (hγ : γ < Om) (hδ : δ < Om) (hlt : lam N γ < lam N δ)
    {j : ℕ} (hj : j < N) : lab N j (lam N γ) (lam N δ) := by
  refine ⟨hlt, (lev_iff hj).mpr ⟨hlt.le, fun bs _ k n hn D p hp => ?_⟩⟩
  exact (lam_elem hγ bs k p (by omega) hp).trans
    (lam_elem hδ bs k p (by omega) fun i hi => (hp i hi).trans hlt).symm

/-- `lam 0 < lam (lam 0) < ⋯` -/
noncomputable def lamChain (N : ℕ) : ℕ → Ordinal.{0}
  | 0 => lam N 0
  | t + 1 => lam N (lamChain N t)

theorem lamChain_lt : ∀ t, lamChain N t < Om
  | 0 => lam_lt om_pos
  | t + 1 => lam_lt (lamChain_lt t)

theorem lamChain_strictMono : StrictMono (lamChain N) :=
  strictMono_nat_of_lt_succ fun t => lt_lam (lamChain N t)

/-- Every finite length of chain related at all levels occurs in R_N. -/
theorem exists_chain (N len : ℕ) :
    ∃ c : ℕ → Ordinal.{0}, ∀ i j, i < j → j < len → ∀ k < N, lab N k (c i) (c j) := by
  refine ⟨fun i => lamChain N (i + 1), fun i j hij _ k hk => ?_⟩
  have h : lamChain N (i + 1) < lamChain N (j + 1) := lamChain_strictMono (by omega)
  exact lab_lam (lamChain_lt i) (lamChain_lt j) h hk

end Pat
