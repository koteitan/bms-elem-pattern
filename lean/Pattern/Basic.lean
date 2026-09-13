/-
  The structure R_N = (Ord; ≤, ≤₁, …, ≤_N) of pure elementary patterns of order N:

    α ≤_{j+1} β  :⟺  (α; ≤, ≤₁, …, ≤_N) is a Σ_{j+1}-elementary substructure of (β; ≤, ≤₁, …, ≤_N)

  defined simultaneously for all j < N by recursion on β.

  Formulas are not written as syntax.  A formula with quantifier blocks `bs = [b₁, …, b_r]`,
  `k` parameters and matrix `D` (a set of atomic diagrams of `n = k + b₁ + ⋯ + b_r` points) is
  evaluated by

    Sig []        v = (diag v ∈ D)
    Sig (b :: bs) v = ∃ x₀ … x_{b-1} < M, ¬ Sig bs (v, x)

  so `Sig [b₁, …, b_r]` is a Σ_r formula, and every Σ_r formula has this form.
-/
import Mathlib

open Classical

namespace Pat

variable {N : ℕ}

/-! ### Formulas -/

/-- Relations `≤₁, …, ≤_N` on ordinals; index `j : Fin N` is `≤_{j+1}`. -/
structure Rels (N : ℕ) where
  rel : Fin N → Ordinal.{0} → Ordinal.{0} → Prop

/-- Atomic diagrams of `n` points: for each pair, the truth values of `≤, ≤₁, …, ≤_N`. -/
abbrev Diag (N n : ℕ) := Fin n → Fin n → Fin (N + 1) → Bool

/-- The truth values of `a ≤ b, a ≤₁ b, …, a ≤_N b`. -/
noncomputable def bits (R : Rels N) (a b : Ordinal.{0}) : Fin (N + 1) → Bool :=
  Fin.cases (decide (a ≤ b)) fun j => decide (R.rel j a b)

@[simp] theorem bits_zero (R : Rels N) (a b : Ordinal.{0}) : bits R a b 0 = decide (a ≤ b) :=
  rfl

@[simp] theorem bits_succ (R : Rels N) (a b : Ordinal.{0}) (j : Fin N) :
    bits R a b j.succ = decide (R.rel j a b) := rfl

/-- The atomic diagram of the first `n` entries of a tuple. -/
noncomputable def diag (R : Rels N) (n : ℕ) (v : ℕ → Ordinal.{0}) : Diag N n :=
  fun a b => bits R (v a) (v b)

/-- Concatenation: the first `k` entries come from `p`, the rest from `q`. -/
def cat (k : ℕ) (p q : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0} :=
  fun i => if i < k then p i else q (i - k)

theorem cat_left {k : ℕ} {p q : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < k) : cat k p q i = p i := by
  simp [cat, hi]

theorem cat_right {k : ℕ} {p q : ℕ → Ordinal.{0}} (i : ℕ) : cat k p q (k + i) = q i := by
  simp [cat]

theorem cat_lt {k m : ℕ} {p x : ℕ → Ordinal.{0}} {B : Ordinal.{0}} (hp : ∀ i < k, p i < B)
    (hx : ∀ i < m, x i < B) : ∀ i < k + m, cat k p x i < B := by
  intro i hi
  unfold cat
  split_ifs with h
  · exact hp i h
  · exact hx _ (by omega)

theorem cat_congr_left {k : ℕ} {p p' q : ℕ → Ordinal.{0}} (h : ∀ i < k, p i = p' i) :
    cat k p q = cat k p' q := by
  funext i
  unfold cat
  split_ifs with hi
  · exact h i hi
  · rfl

/-- Evaluation of a formula with quantifier blocks `bs` in the structure below `M`.
`k` entries of `v` are already assigned. -/
def Sig (R : Rels N) (M : Ordinal.{0}) (n : ℕ) (D : Set (Diag N n)) :
    List ℕ → ℕ → (ℕ → Ordinal.{0}) → Prop
  | [], _, v => diag R n v ∈ D
  | b :: bs, k, v =>
    ∃ x : ℕ → Ordinal.{0}, (∀ i < b, x i < M) ∧ ¬ Sig R M n D bs (k + b) (cat k v x)

@[simp] theorem sig_nil {R : Rels N} {M : Ordinal.{0}} {n : ℕ} {D : Set (Diag N n)} {k : ℕ}
    {v : ℕ → Ordinal.{0}} : Sig R M n D [] k v ↔ diag R n v ∈ D := Iff.rfl

theorem sig_cons {R : Rels N} {M : Ordinal.{0}} {n : ℕ} {D : Set (Diag N n)} {b : ℕ}
    {bs : List ℕ} {k : ℕ} {v : ℕ → Ordinal.{0}} :
    Sig R M n D (b :: bs) k v ↔
      ∃ x : ℕ → Ordinal.{0}, (∀ i < b, x i < M) ∧ ¬ Sig R M n D bs (k + b) (cat k v x) :=
  Iff.rfl

/-- `(α; ≤, ≤₁, …) ≼_{Σ_j} (β; ≤, ≤₁, …)`: agreement on all formulas with at most `j` blocks
and parameters below `α`. -/
def Elem (R : Rels N) (j : ℕ) (α β : Ordinal.{0}) : Prop :=
  ∀ (bs : List ℕ), bs.length ≤ j → ∀ (k n : ℕ), n = k + bs.sum → ∀ (D : Set (Diag N n))
    (p : ℕ → Ordinal.{0}), (∀ i < k, p i < α) → (Sig R α n D bs k p ↔ Sig R β n D bs k p)

/-! ### Only pairs below the top matter -/

theorem diag_congr {R R' : Rels N} {B : Ordinal.{0}} {n : ℕ} {v : ℕ → Ordinal.{0}}
    (hR : ∀ j a b, a < B → b < B → (R.rel j a b ↔ R'.rel j a b)) (hv : ∀ i < n, v i < B) :
    diag R n v = diag R' n v := by
  funext a b c
  cases c using Fin.cases with
  | zero => rfl
  | succ j => simp only [diag, bits_succ, hR j _ _ (hv a a.2) (hv b b.2)]

theorem sig_congr {R R' : Rels N} {B M : Ordinal.{0}} (hMB : M ≤ B)
    (hR : ∀ j a b, a < B → b < B → (R.rel j a b ↔ R'.rel j a b)) {n : ℕ} {D : Set (Diag N n)} :
    ∀ (bs : List ℕ) (k : ℕ) (v : ℕ → Ordinal.{0}), n ≤ k + bs.sum → (∀ i < k, v i < B) →
      (Sig R M n D bs k v ↔ Sig R' M n D bs k v)
  | [], k, v, hn, hv => by
    simp only [sig_nil]
    rw [diag_congr hR (fun i hi => hv i (by simp at hn; omega))]
  | b :: bs, k, v, hn, hv => by
    simp only [sig_cons]
    refine exists_congr fun x => and_congr_right fun hx => not_congr ?_
    exact sig_congr hMB hR bs (k + b) (cat k v x) (by simp at hn; omega)
      (cat_lt hv fun i hi => (hx i hi).trans_le hMB)

theorem sig_param_congr {R : Rels N} {M : Ordinal.{0}} {n : ℕ} {D : Set (Diag N n)}
    {bs : List ℕ} {k : ℕ} {p p' : ℕ → Ordinal.{0}} (hn : n ≤ k + bs.sum)
    (h : ∀ i < k, p i = p' i) : Sig R M n D bs k p ↔ Sig R M n D bs k p' := by
  cases bs with
  | nil =>
    simp only [sig_nil]
    have : diag R n p = diag R n p' := by
      funext a b
      simp only [diag]
      rw [h a (by simp at hn; omega), h b (by simp at hn; omega)]
    rw [this]
  | cons b bs =>
    simp only [sig_cons, cat_congr_left h]

/-! ### The recursion on `β` -/

/-- The relations on pairs below `β`, read off from the earlier stages. -/
def stage (β : Ordinal.{0}) (IH : ∀ b : Ordinal.{0}, b < β → Ordinal.{0} → Fin N → Prop) :
    Rels N :=
  ⟨fun j a b => ∃ h : b < β, a ≤ b ∧ IH b h a j⟩

/-- `RFix N β α j` is `α ≤_{j+1} β`. -/
noncomputable def RFix (N : ℕ) : Ordinal.{0} → Ordinal.{0} → Fin N → Prop :=
  (wellFounded_lt (α := Ordinal.{0})).fix (C := fun _ => Ordinal.{0} → Fin N → Prop)
    fun β IH α j => α ≤ β ∧ Elem (stage β IH) (j.val + 1) α β

/-- The relations of R_N. -/
noncomputable def RN (N : ℕ) : Rels N := ⟨fun j a b => RFix N b a j⟩

theorem RFix_eq (β : Ordinal.{0}) :
    RFix N β = fun α j => α ≤ β ∧ Elem (stage β fun b _ => RFix N b) (j.val + 1) α β :=
  WellFounded.fix_eq _ _ _

theorem rel_le {j : Fin N} {a b : Ordinal.{0}} (h : (RN N).rel j a b) : a ≤ b := by
  have h' : RFix N b a j := h
  rw [RFix_eq] at h'
  exact h'.1

theorem stage_agree (β : Ordinal.{0}) :
    ∀ j a b, a < β → b < β → ((stage β fun b _ => RFix N b).rel j a b ↔ (RN N).rel j a b) := by
  intro j a b _ hb
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hb, rel_le h, h⟩⟩

theorem elem_congr {j : ℕ} {α β : Ordinal.{0}} (hαβ : α ≤ β) :
    Elem (stage β fun b _ => RFix N b) j α β ↔ Elem (RN N) j α β := by
  have hR := stage_agree (N := N) β
  constructor
  · intro h bs hbs k n hn D p hp
    have hp' : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [← sig_congr hαβ hR bs k p (by omega) hp', ← sig_congr le_rfl hR bs k p (by omega) hp']
    exact h bs hbs k n hn D p hp
  · intro h bs hbs k n hn D p hp
    have hp' : ∀ i < k, p i < β := fun i hi => (hp i hi).trans_le hαβ
    rw [sig_congr hαβ hR bs k p (by omega) hp', sig_congr le_rfl hR bs k p (by omega) hp']
    exact h bs hbs k n hn D p hp

theorem rel_iff {j : Fin N} {α β : Ordinal.{0}} :
    (RN N).rel j α β ↔ α ≤ β ∧ Elem (RN N) (j.val + 1) α β := by
  show RFix N β α j ↔ _
  rw [RFix_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (elem_congr h1).mp h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, (elem_congr h1).mpr h2⟩⟩

/-! ### Levels -/

/-- `a ≤_{j+1} b` in R_N (false for `j ≥ N`). -/
def lev (N : ℕ) (j : ℕ) (a b : Ordinal.{0}) : Prop := ∃ h : j < N, (RN N).rel ⟨j, h⟩ a b

/-- `a <_{j+1} b` in R_N. -/
def lab (N : ℕ) (j : ℕ) (a b : Ordinal.{0}) : Prop := a < b ∧ lev N j a b

theorem lev_iff {j : ℕ} (hj : j < N) {α β : Ordinal.{0}} :
    lev N j α β ↔ α ≤ β ∧ Elem (RN N) (j + 1) α β :=
  ⟨fun ⟨_, h⟩ => rel_iff.mp h, fun h => ⟨hj, rel_iff.mpr h⟩⟩

theorem lev_lt {j : ℕ} {a b : Ordinal.{0}} (h : lev N j a b) : j < N := h.1

theorem lev_le {j : ℕ} {a b : Ordinal.{0}} (h : lev N j a b) : a ≤ b := rel_le h.2

theorem lev_refl {j : ℕ} (hj : j < N) (a : Ordinal.{0}) : lev N j a a :=
  (lev_iff hj).mpr ⟨le_rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩

theorem lev_trans {j : ℕ} {a b c : Ordinal.{0}} (hab : lev N j a b) (hbc : lev N j b c) :
    lev N j a c := by
  have hj := hab.1
  obtain ⟨h1, e1⟩ := (lev_iff hj).mp hab
  obtain ⟨h2, e2⟩ := (lev_iff hj).mp hbc
  refine (lev_iff hj).mpr ⟨h1.trans h2, fun bs hbs k n hn D p hp => ?_⟩
  exact (e1 bs hbs k n hn D p hp).trans (e2 bs hbs k n hn D p fun i hi => (hp i hi).trans_le h1)

theorem lev_mono {j j' : ℕ} (hjj' : j ≤ j') {a b : Ordinal.{0}} (h : lev N j' a b) :
    lev N j a b := by
  have hj' := h.1
  obtain ⟨hab, e⟩ := (lev_iff hj').mp h
  exact (lev_iff (by omega)).mpr ⟨hab, fun bs hbs => e bs (by omega)⟩

theorem lab_trans {j : ℕ} {a b c : Ordinal.{0}} (hab : lab N j a b) (hbc : lab N j b c) :
    lab N j a c :=
  ⟨hab.1.trans hbc.1, lev_trans hab.2 hbc.2⟩

theorem lab_mono {j j' : ℕ} (hjj' : j ≤ j') {a b : Ordinal.{0}} (h : lab N j' a b) :
    lab N j a b :=
  ⟨h.1, lev_mono hjj' h.2⟩

/-! ### Short block lists -/

theorem length_le_one {bs : List ℕ} (h : bs.length ≤ 1) : bs = [] ∨ ∃ b, bs = [b] := by
  match bs, h with
  | [], _ => exact Or.inl rfl
  | [b], _ => exact Or.inr ⟨b, rfl⟩
  | _ :: _ :: _, h => simp at h

theorem length_le_two {bs : List ℕ} (h : bs.length ≤ 2) :
    bs = [] ∨ (∃ b, bs = [b]) ∨ ∃ b c, bs = [b, c] := by
  match bs, h with
  | [], _ => exact Or.inl rfl
  | [b], _ => exact Or.inr (Or.inl ⟨b, rfl⟩)
  | [b, c], _ => exact Or.inr (Or.inr ⟨b, c, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

/-- Σ₁ statements go up. -/
theorem sig_up1 {R : Rels N} {M M' : Ordinal.{0}} (h : M ≤ M') {n : ℕ} {D : Set (Diag N n)}
    {b k : ℕ} {p : ℕ → Ordinal.{0}} : Sig R M n D [b] k p → Sig R M' n D [b] k p := by
  rintro ⟨x, hx, hD⟩
  exact ⟨x, fun i hi => (hx i hi).trans_le h, hD⟩

/-- A finite family below a nonzero ordinal has an upper bound below it. -/
theorem exists_bound {α : Ordinal.{0}} (hα : 0 < α) (b : ℕ) (x : ℕ → Ordinal.{0})
    (hx : ∀ i < b, x i < α) : ∃ z < α, ∀ i < b, x i ≤ z := by
  refine ⟨(Finset.range b).sup x, ?_, fun i hi => Finset.le_sup (Finset.mem_range.mpr hi)⟩
  exact (Finset.sup_lt_iff (lt_of_le_of_lt bot_le hα)).mpr fun i hi =>
    hx i (Finset.mem_range.mp hi)

/-! ### Continuity along cofinal sets (levels 1 and 2) -/

/-- If `y` is `Σ_j`-elementary (`j ≤ 2`) in cofinally many `v < α`, it is so in `α`. -/
theorem elem_cofinal {R : Rels N} {j : ℕ} (hj : j ≤ 2) {y α : Ordinal.{0}} (hyα : y < α)
    (hS : ∀ z < α, ∃ v, z < v ∧ v < α ∧ y ≤ v ∧ Elem R j y v) : Elem R j y α := by
  have hα0 : 0 < α := lt_of_le_of_lt zero_le hyα
  intro bs hbs k n hn D p hp
  rcases length_le_two (hbs.trans hj) with rfl | ⟨b, rfl⟩ | ⟨b, c, rfl⟩
  · exact Iff.rfl
  · refine ⟨sig_up1 hyα.le, ?_⟩
    rintro ⟨x, hx, hD⟩
    obtain ⟨z, hz, hxz⟩ := exists_bound hα0 b x hx
    obtain ⟨v, hzv, _, _, ev⟩ := hS z hz
    have hsv : Sig R v n D [b] k p := ⟨x, fun i hi => (hxz i hi).trans_lt hzv, hD⟩
    exact (ev [b] hbs k n hn D p hp).mpr hsv
  · constructor
    · rintro ⟨x, hx, hnot⟩
      refine ⟨x, fun i hi => (hx i hi).trans hyα, fun hα => hnot ?_⟩
      obtain ⟨z, hz, hD⟩ := hα
      obtain ⟨w, hw, hzw⟩ := exists_bound hα0 c z hz
      obtain ⟨v, hwv, _, _, ev⟩ := hS w hw
      have hsv : Sig R v n D [c] (k + b) (cat k p x) :=
        ⟨z, fun i hi => (hzw i hi).trans_lt hwv, hD⟩
      exact (ev [c] (by simp at hbs ⊢; omega) (k + b) n (by simp at hn ⊢; omega) D (cat k p x)
        (cat_lt hp hx)).mpr hsv
    · rintro ⟨x, hx, hnot⟩
      obtain ⟨w, hw, hxw⟩ := exists_bound hα0 b x hx
      obtain ⟨v, hwv, hvα, _, ev⟩ := hS w hw
      have hsv : Sig R v n D [b, c] k p :=
        ⟨x, fun i hi => (hxw i hi).trans_lt hwv, fun hv => hnot (sig_up1 hvα.le hv)⟩
      exact (ev [b, c] hbs k n hn D p hp).mpr hsv

/-! ### Level 1 -/

/-- `≤₁` respects `≤`. -/
theorem lev0_of_le {a b c : Ordinal.{0}} (hab : a ≤ b) (hbc : b ≤ c) (hac : lev N 0 a c) :
    lev N 0 a b := by
  have hN := hac.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp hac
  refine (lev_iff hN).mpr ⟨hab, fun bs hbs k n hn D p hp => ?_⟩
  rcases length_le_one hbs with rfl | ⟨b0, rfl⟩
  · exact Iff.rfl
  · exact ⟨sig_up1 hab, fun hb => (e _ hbs k n hn D p hp).mpr (sig_up1 hbc hb)⟩

/-- Continuity of `≤₁` at an ordinal closed under successor. -/
theorem lev0_of_forall (hN : 0 < N) {y α : Ordinal.{0}} (hyα : y ≤ α)
    (hlim : ∀ z < α, Order.succ z < α) (h : ∀ v, y ≤ v → v < α → lev N 0 y v) :
    lev N 0 y α := by
  rcases hyα.lt_or_eq with hlt | rfl
  · refine (lev_iff hN).mpr ⟨hyα, elem_cofinal (by omega) hlt fun z hz => ?_⟩
    refine ⟨max y (Order.succ z), lt_of_lt_of_le (Order.lt_succ z) (le_max_right _ _),
      max_lt hlt (hlim z hz), le_max_left _ _, ?_⟩
    exact ((lev_iff hN).mp (h _ (le_max_left _ _) (max_lt hlt (hlim z hz)))).2
  · exact lev_refl hN y

/-! ### Reading diagrams at natural-number positions -/

/-- The entry of a diagram at positions `a, b` (`false` outside). -/
def get {n : ℕ} (d : Diag N n) (a b : ℕ) (c : Fin (N + 1)) : Bool :=
  if h : a < n ∧ b < n then d ⟨a, h.1⟩ ⟨b, h.2⟩ c else false

/-- `v_a ≤ v_b`, read off a diagram. -/
def GLe {n : ℕ} (d : Diag N n) (a b : ℕ) : Prop := get d a b 0 = true

/-- `v_a ≤_{j+1} v_b`, read off a diagram. -/
def GLev {n : ℕ} (d : Diag N n) (j a b : ℕ) : Prop := ∃ h : j < N, get d a b (Fin.succ ⟨j, h⟩) = true

theorem gle_diag {R : Rels N} {n : ℕ} {v : ℕ → Ordinal.{0}} {a b : ℕ} (ha : a < n) (hb : b < n) :
    GLe (diag R n v) a b ↔ v a ≤ v b := by
  simp [GLe, get, diag, ha, hb]

theorem glev_diag {n : ℕ} {v : ℕ → Ordinal.{0}} {j a b : ℕ} (ha : a < n) (hb : b < n) :
    GLev (diag (RN N) n v) j a b ↔ lev N j (v a) (v b) := by
  unfold GLev lev
  refine exists_congr fun hj => ?_
  rw [get, dif_pos (And.intro ha hb)]
  show decide ((RN N).rel ⟨j, hj⟩ (v a) (v b)) = true ↔ _
  exact decide_eq_true_iff

/-- A `<₁`-lower end is closed under successor. -/
theorem succ_lt_of_lab0 {α β : Ordinal.{0}} (h : lab N 0 α β) : ∀ z < α, Order.succ z < α := by
  intro z hz
  by_contra hcon
  have hαz : α = Order.succ z := le_antisymm (not_lt.mp hcon) (Order.succ_le_of_lt hz)
  have hN := h.2.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  let D : Set (Diag N 2) := {d | ¬ (GLe d 0 1 ∧ ¬ GLe d 1 0)}
  have hmem : ∀ x : ℕ → Ordinal.{0},
      diag (RN N) 2 (cat 1 (fun _ => z) x) ∉ D ↔ (z ≤ x 0 ∧ ¬ x 0 ≤ z) := by
    intro x
    have c0 : cat 1 (fun _ => z) x 0 = z := by simp [cat]
    have c1 : cat 1 (fun _ => z) x 1 = x 0 := by simp [cat]
    show ¬ ¬ (GLe _ 0 1 ∧ ¬ GLe _ 1 0) ↔ _
    rw [not_not, gle_diag (show (0 : ℕ) < 2 by decide) (show (1 : ℕ) < 2 by decide),
      gle_diag (show (1 : ℕ) < 2 by decide) (show (0 : ℕ) < 2 by decide), c0, c1]
  have hβ : Sig (RN N) β 2 D [1] 1 (fun _ => z) :=
    ⟨fun _ => α, fun _ _ => h.1, (hmem _).mpr ⟨hz.le, not_le.mpr hz⟩⟩
  obtain ⟨x, hx, hD⟩ := (e [1] (by simp) 1 2 (by simp) D (fun _ => z) fun _ _ => hz).mpr hβ
  have hzx := not_le.mp ((hmem x).mp hD).2
  have hx0 : x 0 < α := hx 0 (by omega)
  rw [hαz] at hx0
  exact absurd (Order.succ_le_of_lt hzx) (not_le.mpr hx0)

/-! ### Level 2 -/

/-- `≤₂` respects `≤₁`. -/
theorem lev1_of_lev0 {p q r : Ordinal.{0}} (hpq : lev N 0 p q) (hqr : lev N 0 q r)
    (hpr : lev N 1 p r) : lev N 1 p q := by
  have hN := hpr.1
  obtain ⟨_, e0pq⟩ := (lev_iff (by omega)).mp hpq
  obtain ⟨_, e0qr⟩ := (lev_iff (by omega)).mp hqr
  obtain ⟨_, e1pr⟩ := (lev_iff hN).mp hpr
  have hpq' := lev_le hpq
  have hqr' := lev_le hqr
  refine (lev_iff hN).mpr ⟨hpq', fun bs hbs k n hn D P hP => ?_⟩
  rcases length_le_two hbs with rfl | ⟨b, rfl⟩ | ⟨b, c, rfl⟩
  · exact Iff.rfl
  · exact e0pq [b] (by simp) k n hn D P hP
  · constructor
    · rintro ⟨x, hx, hnot⟩
      refine ⟨x, fun i hi => (hx i hi).trans_le hpq', fun hq => hnot ?_⟩
      exact (e0pq [c] (by simp) (k + b) n (by simp at hn ⊢; omega) D (cat k P x)
        (cat_lt hP hx)).mpr hq
    · rintro ⟨x, hx, hnot⟩
      have hr : Sig (RN N) r n D [b, c] k P := by
        refine ⟨x, fun i hi => (hx i hi).trans_le hqr', fun hr => hnot ?_⟩
        exact (e0qr [c] (by simp) (k + b) n (by simp at hn ⊢; omega) D (cat k P x)
          (cat_lt (fun i hi => (hP i hi).trans_le hpq') hx)).mpr hr
      exact (e1pr [b, c] hbs k n hn D P hP).mpr hr

/-- If `y <₂ β`, then `β` is closed under successor. -/
theorem succ_lt_of_lab1_top {y β : Ordinal.{0}} (h : lab N 1 y β) :
    ∀ z < β, Order.succ z < β := by
  intro z hz
  by_contra hcon
  have hβz : β = Order.succ z := le_antisymm (not_lt.mp hcon) (Order.succ_le_of_lt hz)
  have hN := h.2.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  have hylim := succ_lt_of_lab0 (lab_mono (Nat.zero_le 1) h)
  let D : Set (Diag N 2) := {d | GLe d 1 0}
  have hmem : ∀ x w : ℕ → Ordinal.{0},
      diag (RN N) 2 (cat (0 + 1) (cat 0 (fun _ => 0) x) w) ∈ D ↔ w 0 ≤ x 0 := by
    intro x w
    have c0 : cat (0 + 1) (cat 0 (fun _ => 0) x) w 0 = x 0 := by simp [cat]
    have c1 : cat (0 + 1) (cat 0 (fun _ => 0) x) w 1 = w 0 := by simp [cat]
    show GLe _ 1 0 ↔ _
    rw [gle_diag (show (1 : ℕ) < 2 by decide) (show (0 : ℕ) < 2 by decide), c0, c1]
  have hβ : Sig (RN N) β 2 D [1, 1] 0 (fun _ => 0) := by
    refine ⟨fun _ => z, fun _ _ => hz, ?_⟩
    rintro ⟨w, hw, hD⟩
    apply hD
    have hw0 : w 0 < β := hw 0 (by omega)
    rw [hβz, Order.lt_succ_iff] at hw0
    exact (hmem _ w).mpr hw0
  obtain ⟨x, hx, hnot⟩ := (e [1, 1] (by simp) 0 2 (by simp) D (fun _ => 0)
    fun i hi => absurd hi (by omega)).mpr hβ
  have hx0 : x 0 < y := hx 0 (by omega)
  apply hnot
  refine ⟨fun _ => Order.succ (x 0), fun _ _ => hylim _ hx0, fun hD => ?_⟩
  exact not_le.mpr (Order.lt_succ (x 0)) ((hmem x _).mp hD)

/-- If `α <₂ β`, then the `≤₁`-predecessors of `α` are unbounded in `α`. -/
theorem exists_lev0_below {α β : Ordinal.{0}} (h : lab N 1 α β) :
    ∀ z < α, ∃ u, z < u ∧ u < α ∧ lev N 0 u α := by
  intro z hz
  have hN := h.2.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  have h0 : lab N 0 α β := lab_mono (Nat.zero_le 1) h
  have hN0 : 0 < N := by omega
  let D : Set (Diag N 3) := {d | GLe d 0 1 ∧ ¬ GLe d 1 0 ∧ (GLe d 1 2 → GLev d 0 1 2)}
  have hmem : ∀ u w : ℕ → Ordinal.{0},
      diag (RN N) 3 (cat (1 + 1) (cat 1 (fun _ => z) u) w) ∈ D ↔
        (z ≤ u 0 ∧ ¬ u 0 ≤ z ∧ (u 0 ≤ w 0 → lev N 0 (u 0) (w 0))) := by
    intro u w
    have c0 : cat (1 + 1) (cat 1 (fun _ => z) u) w 0 = z := by simp [cat]
    have c1 : cat (1 + 1) (cat 1 (fun _ => z) u) w 1 = u 0 := by simp [cat]
    have c2 : cat (1 + 1) (cat 1 (fun _ => z) u) w 2 = w 0 := by simp [cat]
    show GLe _ 0 1 ∧ ¬ GLe _ 1 0 ∧ (GLe _ 1 2 → GLev _ 0 1 2) ↔ _
    rw [gle_diag (show (0 : ℕ) < 3 by decide) (show (1 : ℕ) < 3 by decide),
      gle_diag (show (1 : ℕ) < 3 by decide) (show (0 : ℕ) < 3 by decide),
      gle_diag (show (1 : ℕ) < 3 by decide) (show (2 : ℕ) < 3 by decide),
      glev_diag (show (1 : ℕ) < 3 by decide) (show (2 : ℕ) < 3 by decide), c0, c1, c2]
  have hβ : Sig (RN N) β 3 D [1, 1] 1 (fun _ => z) := by
    refine ⟨fun _ => α, fun _ _ => h.1, ?_⟩
    rintro ⟨w, hw, hD⟩
    apply hD
    have hw0 : w 0 < β := hw 0 (by omega)
    exact (hmem _ w).mpr ⟨hz.le, not_le.mpr hz, fun hle => lev0_of_le hle hw0.le h0.2⟩
  obtain ⟨u, hu, hnot⟩ := (e [1, 1] (by simp) 1 3 (by simp) D (fun _ => z)
    fun _ _ => hz).mpr hβ
  have hu0 : u 0 < α := hu 0 (by omega)
  have key : ∀ w, w < α → (u 0 ≤ w → lev N 0 (u 0) w) ∧ z < u 0 := by
    intro w hw
    by_contra hc
    apply hnot
    refine ⟨fun _ => w, fun _ _ => hw, fun hD => hc ?_⟩
    obtain ⟨_, h2, h3⟩ := (hmem u _).mp hD
    exact ⟨h3, not_le.mp h2⟩
  refine ⟨u 0, (key _ hu0).2, hu0, ?_⟩
  exact lev0_of_forall hN0 hu0.le (succ_lt_of_lab0 h0) fun w hw hwα => (key w hwα).1 hw

end Pat
