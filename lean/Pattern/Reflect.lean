/-
  Finite pattern reflection (the `reflect` field of the label interface) in R_N with

    ◁ₖ = <_{k+1}      (k < N ≤ 3).

  n = 0: Σ₁-elementarity copies a finite configuration below `α`.
  n = 1: a Σ₂ formula additionally keeps the `<₁`-connections to the top.
  n = 2: a Σ₃ formula additionally keeps the `<₂`-connections to the top.
-/
import Pattern.Basic
import Bm4.Label

open Classical

namespace Pat

variable {N : ℕ}

/-! ### Tuples -/

/-- A finite set of ordinals as a tuple of length `X.card`. -/
noncomputable def listTuple (X : Finset Ordinal.{0}) : ℕ → Ordinal.{0} :=
  fun i => X.toList.getD i 0

theorem listTuple_lt {X : Finset Ordinal.{0}} {α : Ordinal.{0}} (hX : ∀ x ∈ X, x < α) :
    ∀ i < X.card, listTuple X i < α := by
  intro i hi
  have hi' : i < X.toList.length := by simpa using hi
  unfold listTuple
  rw [List.getD_eq_getElem _ _ hi']
  exact hX _ (Finset.mem_toList.mp (List.getElem_mem hi'))

theorem mem_listTuple {X : Finset Ordinal.{0}} {x : Ordinal.{0}} (hx : x ∈ X) :
    ∃ i < X.card, listTuple X i = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hx)
  refine ⟨i, by simpa using hi, ?_⟩
  unfold listTuple
  rw [List.getD_eq_getElem _ _ hi, hix]

/-! ### Diagrams of copies -/

/-- The first `m` positions of `d` carry the diagram of `w`. -/
def Agree {n : ℕ} (d : Diag N n) (m : ℕ) (w : ℕ → Ordinal.{0}) : Prop :=
  ∀ a < m, ∀ b < m, ∀ c, get d a b c = bits (RN N) (w a) (w b) c

/-- `y'` has the same diagram as `y` over the parameters `p` (`k` of them). -/
def SameBits (k s : ℕ) (p y y' : ℕ → Ordinal.{0}) : Prop :=
  ∀ a < k + s, ∀ b < k + s,
    bits (RN N) (cat k p y' a) (cat k p y' b) = bits (RN N) (cat k p y a) (cat k p y b)

theorem agree_iff {n m : ℕ} (hm : m ≤ n) {v w w' : ℕ → Ordinal.{0}}
    (hv : ∀ a < m, v a = w' a) :
    Agree (diag (RN N) n v) m w ↔
      ∀ a < m, ∀ b < m, bits (RN N) (w' a) (w' b) = bits (RN N) (w a) (w b) := by
  constructor
  · intro h a ha b hb
    funext c
    have := h a ha b hb c
    rw [get, dif_pos (And.intro (by omega) (by omega))] at this
    simpa [diag, hv a ha, hv b hb] using this
  · intro h a ha b hb c
    rw [get, dif_pos (And.intro (by omega) (by omega))]
    simp only [diag, hv a ha, hv b hb, h a ha b hb]

theorem lab_transfer {a b c d : Ordinal.{0}} (h : bits (RN N) a b = bits (RN N) c d)
    (h' : bits (RN N) b a = bits (RN N) d c) :
    (c < d → a < b) ∧ ∀ j, lab N j c d → lab N j a b := by
  have hle : ∀ {x y u w : Ordinal.{0}}, bits (RN N) x y = bits (RN N) u w → (x ≤ y ↔ u ≤ w) :=
    fun e => by simpa using congrFun e 0
  have hrel : ∀ {x y u w : Ordinal.{0}} (j : Fin N), bits (RN N) x y = bits (RN N) u w →
      ((RN N).rel j x y ↔ (RN N).rel j u w) :=
    fun j e => by simpa using congrFun e j.succ
  have hlt : c < d → a < b := fun hcd => lt_of_not_ge fun hba => not_le.mpr hcd ((hle h').mp hba)
  exact ⟨hlt, fun j ⟨hcd, hj, hr⟩ => ⟨hlt hcd, hj, (hrel ⟨j, hj⟩ h).mpr hr⟩⟩

/-- A copy with the same diagram satisfies the clauses (a), (b), (c) of `reflect`. -/
theorem copy_props {X : Finset Ordinal.{0}} {α : Ordinal.{0}} {s : ℕ} {y y' : ℕ → Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) (hs : 0 < s) (hyge : ∀ i, i < s → α ≤ y i)
    (hsame : SameBits (N := N) X.card s (listTuple X) y y')
    (hy : ∀ i j, i < j → j < s → y i < y j) :
    (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, lab N k x (y i) → lab N k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, lab N k (y i) (y j) → lab N k (y' i) (y' j)) := by
  have tr : ∀ a < X.card + s, ∀ b < X.card + s,
      (cat X.card (listTuple X) y a < cat X.card (listTuple X) y b →
        cat X.card (listTuple X) y' a < cat X.card (listTuple X) y' b) ∧
      ∀ j, lab N j (cat X.card (listTuple X) y a) (cat X.card (listTuple X) y b) →
        lab N j (cat X.card (listTuple X) y' a) (cat X.card (listTuple X) y' b) :=
    fun a ha b hb => lab_transfer (hsame a ha b hb) (hsame b hb a ha)
  refine ⟨fun i j hij hj => ?_, fun x hx => ?_, fun x hx i hi j hr => ?_,
    fun i j hi hj t hr => ?_⟩
  · have := (tr (X.card + i) (by omega) (X.card + j) (by omega)).1
    simp only [cat_right] at this
    exact this (hy i j hij hj)
  · obtain ⟨a, ha, rfl⟩ := mem_listTuple hx
    have := (tr a (by omega) (X.card + 0) (by omega)).1
    simp only [cat_right, cat_left ha] at this
    exact this ((hX _ hx).trans_le (hyge 0 hs))
  · obtain ⟨a, ha, rfl⟩ := mem_listTuple hx
    have := (tr a (by omega) (X.card + i) (by omega)).2 j
    simp only [cat_right, cat_left ha] at this
    exact this hr
  · have := (tr (X.card + i) (by omega) (X.card + j) (by omega)).2 t
    simp only [cat_right] at this
    exact this hr

/-! ### n = 0 -/

theorem reflect_zero {α β : Ordinal.{0}} (h : lab N 0 α β) {X : Finset Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) {s : ℕ} {y : ℕ → Ordinal.{0}} (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧
      SameBits (N := N) X.card s (listTuple X) y y' := by
  set k := X.card
  set p := listTuple X
  have hp : ∀ i < k, p i < α := listTuple_lt hX
  have hN := h.2.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  let D : Set (Diag N (k + s)) := {d | ¬ Agree d (k + s) (cat k p y)}
  have hmem : ∀ u : ℕ → Ordinal.{0},
      diag (RN N) (k + s) (cat k p u) ∉ D ↔ SameBits (N := N) k s p y u := by
    intro u
    show ¬ ¬ Agree _ _ _ ↔ _
    rw [not_not, agree_iff le_rfl (fun a _ => rfl)]
    rfl
  have hβ : Sig (RN N) β (k + s) D [s] k p :=
    ⟨y, hylt, (hmem y).mpr fun _ _ _ _ => rfl⟩
  obtain ⟨y', hy', hD⟩ := (e [s] (by simp) k (k + s) (by simp) D p hp).mpr hβ
  exact ⟨y', hy', (hmem y').mp hD⟩

/-! ### n = 1 -/

theorem reflect_one {α β : Ordinal.{0}} (h : lab N 1 α β) {X : Finset Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) {s : ℕ} (hs : 0 < s) {y : ℕ → Ordinal.{0}}
    (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧
      SameBits (N := N) X.card s (listTuple X) y y' ∧
      ∀ i, i < s → lab N 0 (y i) β → lab N 0 (y' i) α := by
  set k := X.card
  set p := listTuple X
  have hp : ∀ i < k, p i < α := listTuple_lt hX
  have hN := h.2.1
  have hN0 : 0 < N := by omega
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  have h0 : lab N 0 α β := lab_mono (Nat.zero_le 1) h
  let T : (ℕ → Ordinal.{0}) → (ℕ → Ordinal.{0}) → ℕ → Ordinal.{0} :=
    fun u v => cat (k + s) (cat k p u) v
  have Tlt : ∀ u v a, a < k + s → T u v a = cat k p u a := fun u v a ha => cat_left ha
  have Tu : ∀ u v i, i < s → T u v (k + i) = u i := fun u v i hi => by
    show cat (k + s) (cat k p u) v (k + i) = u i
    rw [cat_left (by omega), cat_right]
  have Tv : ∀ u v i, T u v (k + s + i) = v i := fun u v i => cat_right i
  let D : Set (Diag N (k + s + s)) :=
    {d | Agree d (k + s) (cat k p y) ∧
      ∀ i < s, lab N 0 (y i) β → GLe d (k + i) (k + s + i) → GLev d 0 (k + i) (k + s + i)}
  have hmem : ∀ u v : ℕ → Ordinal.{0}, diag (RN N) (k + s + s) (T u v) ∈ D ↔
      (SameBits (N := N) k s p y u ∧
        ∀ i < s, lab N 0 (y i) β → u i ≤ v i → lev N 0 (u i) (v i)) := by
    intro u v
    show Agree _ _ _ ∧ _ ↔ _
    rw [agree_iff (by omega) (fun a ha => Tlt u v a ha)]
    refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun hi => ?_)
    rw [gle_diag (by omega) (by omega), glev_diag (by omega) (by omega), Tu u v i hi, Tv]
  have hβ : Sig (RN N) β (k + s + s) D [s, s] k p := by
    refine ⟨y, hylt, ?_⟩
    rintro ⟨v, hv, hD⟩
    apply hD
    refine (hmem y v).mpr ⟨fun _ _ _ _ => rfl, fun i hi hi0 hle => ?_⟩
    have hvβ : v i < β := hv i hi
    exact lev0_of_le hle hvβ.le hi0.2
  obtain ⟨u, hu, hnot⟩ := (e [s, s] (by simp) k (k + s + s) (by simp; omega) D p hp).mpr hβ
  have hall : ∀ v : ℕ → Ordinal.{0}, (∀ i < s, v i < α) → diag (RN N) (k + s + s) (T u v) ∈ D :=
    fun v hv => by
      by_contra hc
      exact hnot ⟨v, hv, hc⟩
  have hu0 : u 0 < α := hu 0 hs
  refine ⟨u, hu, ((hmem u _).mp (hall (fun _ => u 0) fun _ _ => hu0)).1, fun i hi hi0 => ?_⟩
  refine ⟨hu i hi, lev0_of_forall hN0 (hu i hi).le (succ_lt_of_lab0 h0) fun t ht htα => ?_⟩
  exact ((hmem u _).mp (hall (fun _ => t) fun _ _ => htα)).2 i hi hi0 ht

/-! ### n = 2 -/

theorem reflect_two {α β : Ordinal.{0}} (h : lab N 2 α β) {X : Finset Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) {s : ℕ} (hs : 0 < s) {y : ℕ → Ordinal.{0}}
    (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧
      SameBits (N := N) X.card s (listTuple X) y y' ∧
      (∀ i, i < s → lab N 0 (y i) β → lab N 0 (y' i) α) ∧
      (∀ i, i < s → lab N 1 (y i) β → lab N 1 (y' i) α) := by
  set k := X.card
  set p := listTuple X
  have hp : ∀ i < k, p i < α := listTuple_lt hX
  have hN := h.2.1
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  have h0 : lab N 0 α β := lab_mono (Nat.zero_le 2) h
  have h1 : lab N 1 α β := lab_mono (by omega) h
  let T : (ℕ → Ordinal.{0}) → (ℕ → Ordinal.{0}) → (ℕ → Ordinal.{0}) → ℕ → Ordinal.{0} :=
    fun u v w => cat (k + s + s) (cat (k + s) (cat k p u) v) w
  have Tlt : ∀ u v w a, a < k + s → T u v w a = cat k p u a := fun u v w a ha => by
    show cat (k + s + s) (cat (k + s) (cat k p u) v) w a = _
    rw [cat_left (by omega), cat_left ha]
  have Tu : ∀ u v w i, i < s → T u v w (k + i) = u i := fun u v w i hi => by
    show cat (k + s + s) (cat (k + s) (cat k p u) v) w (k + i) = u i
    rw [cat_left (by omega), cat_left (by omega), cat_right]
  have Tv : ∀ u v w i, i < s → T u v w (k + s + i) = v i := fun u v w i hi => by
    show cat (k + s + s) (cat (k + s) (cat k p u) v) w (k + s + i) = v i
    rw [cat_left (by omega), cat_right]
  have Tw : ∀ u v w i, T u v w (k + s + s + i) = w i := fun u v w i => cat_right i
  /- the matrix -/
  let Mat : Diag N (k + s + s + s) → Prop := fun d =>
    Agree d (k + s) (cat k p y) ∧
      ∀ i < s,
        (lab N 0 (y i) β → GLe d (k + i) (k + s + i) → GLev d 0 (k + i) (k + s + i)) ∧
        (lab N 1 (y i) β → GLev d 0 (k + i) (k + s + i) →
          (GLe d (k + s + i) (k + s + s + i) ∧ ¬ GLev d 0 (k + s + i) (k + s + s + i)) ∨
            GLev d 1 (k + i) (k + s + i))
  let D : Set (Diag N (k + s + s + s)) := {d | ¬ Mat d}
  have hmat : ∀ u v w : ℕ → Ordinal.{0}, Mat (diag (RN N) (k + s + s + s) (T u v w)) ↔
      (SameBits (N := N) k s p y u ∧
        ∀ i < s,
          (lab N 0 (y i) β → u i ≤ v i → lev N 0 (u i) (v i)) ∧
          (lab N 1 (y i) β → lev N 0 (u i) (v i) →
            (v i ≤ w i ∧ ¬ lev N 0 (v i) (w i)) ∨ lev N 1 (u i) (v i))) := by
    intro u v w
    show Agree _ _ _ ∧ _ ↔ _
    rw [agree_iff (by omega) (fun a ha => Tlt u v w a ha)]
    refine and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun hi => ?_)
    rw [gle_diag (by omega) (by omega), glev_diag (by omega) (by omega),
      gle_diag (by omega) (by omega), glev_diag (by omega) (by omega),
      glev_diag (by omega) (by omega), Tu u v w i hi, Tv u v w i hi, Tw]
  /- the formula is true in β -/
  have hβ : Sig (RN N) β (k + s + s + s) D [s, s, s] k p := by
    refine ⟨y, hylt, ?_⟩
    rintro ⟨v, hv, hnot⟩
    apply hnot
    have ex : ∀ i, (i < s ∧ lab N 1 (y i) β ∧ lev N 0 (y i) (v i) ∧ ¬ lev N 1 (y i) (v i)) →
        ∃ t, v i ≤ t ∧ t < β ∧ ¬ lev N 0 (v i) t := by
      intro i ⟨hi, hi1, hi0, hn1⟩
      by_contra hne
      push Not at hne
      have hvβ : v i < β := hv i hi
      have hv0 : lev N 0 (v i) β :=
        lev0_of_forall hN0 hvβ.le (succ_lt_of_lab1_top hi1) fun t ht htβ => hne t ht htβ
      exact hn1 (lev1_of_lev0 hi0 hv0 hi1.2)
    let w : ℕ → Ordinal.{0} := fun i =>
      if hc : i < s ∧ lab N 1 (y i) β ∧ lev N 0 (y i) (v i) ∧ ¬ lev N 1 (y i) (v i) then
        Classical.choose (ex i hc)
      else v i
    refine ⟨w, fun i hi => ?_, ?_⟩
    · by_cases hc : i < s ∧ lab N 1 (y i) β ∧ lev N 0 (y i) (v i) ∧ ¬ lev N 1 (y i) (v i)
      · simp only [w, dif_pos hc]
        exact (Classical.choose_spec (ex i hc)).2.1
      · simp only [w, dif_neg hc]
        exact hv i hi
    · show ¬ ¬ Mat _
      rw [not_not, hmat]
      refine ⟨fun _ _ _ _ => rfl, fun i hi => ⟨fun hi0 hle => lev0_of_le hle (hv i hi).le hi0.2,
        fun hi1 hl0 => ?_⟩⟩
      by_cases hl1 : lev N 1 (y i) (v i)
      · exact Or.inr hl1
      · have hc : i < s ∧ lab N 1 (y i) β ∧ lev N 0 (y i) (v i) ∧ ¬ lev N 1 (y i) (v i) :=
          ⟨hi, hi1, hl0, hl1⟩
        simp only [w, dif_pos hc]
        exact Or.inl ⟨(Classical.choose_spec (ex i hc)).1, (Classical.choose_spec (ex i hc)).2.2⟩
  /- transfer to α -/
  obtain ⟨u, hu, hnot⟩ :=
    (e [s, s, s] (by simp) k (k + s + s + s) (by simp; omega) D p hp).mpr hβ
  have hall : ∀ v : ℕ → Ordinal.{0}, (∀ i < s, v i < α) →
      ∃ w : ℕ → Ordinal.{0}, (∀ i < s, w i < α) ∧
        Mat (diag (RN N) (k + s + s + s) (T u v w)) := by
    intro v hv
    by_contra hc
    apply hnot
    refine ⟨v, hv, ?_⟩
    rintro ⟨w, hw, hD⟩
    exact hc ⟨w, hw, not_not.mp hD⟩
  have hu0 : u 0 < α := hu 0 hs
  have hsame : SameBits (N := N) k s p y u := by
    obtain ⟨w, _, hw⟩ := hall (fun _ => u 0) fun _ _ => hu0
    exact ((hmat _ _ _).mp hw).1
  have top0 : ∀ i, i < s → lab N 0 (y i) β → lab N 0 (u i) α := by
    intro i hi hi0
    refine ⟨hu i hi, lev0_of_forall hN0 (hu i hi).le (succ_lt_of_lab0 h0) fun t ht htα => ?_⟩
    obtain ⟨w, _, hw⟩ := hall (fun _ => t) fun _ _ => htα
    exact (((hmat _ _ _).mp hw).2 i hi).1 hi0 ht
  refine ⟨u, hu, hsame, top0, fun i hi hi1 => ?_⟩
  have hui : u i < α := hu i hi
  have hu0i : lev N 0 (u i) α := (top0 i hi (lab_mono (Nat.zero_le 1) hi1)).2
  refine ⟨hui, (lev_iff hN1).mpr ⟨hui.le, elem_cofinal le_rfl hui fun z hz => ?_⟩⟩
  obtain ⟨t, hzt, htα, ht0⟩ := exists_lev0_below h1 (max z (u i)) (max_lt hz hui)
  obtain ⟨w, hw, hmw⟩ := hall (fun _ => t) fun _ _ => htα
  have hut : u i ≤ t := (le_max_right _ _).trans hzt.le
  have hl0 : lev N 0 (u i) t := lev0_of_le hut htα.le hu0i
  rcases (((hmat _ _ _).mp hmw).2 i hi).2 hi1 hl0 with ⟨hle, hn⟩ | hl1
  · exact absurd (lev0_of_le hle (hw i hi).le ht0) hn
  · exact ⟨t, (le_max_left _ _).trans_lt hzt, htα, hut, ((lev_iff hN1).mp hl1).2⟩

/-! ### The label system -/

/-- R_N as a label system for arrays with `N ≤ 3` rows. -/
noncomputable def labelSystem (N : ℕ) (hN : N ≤ 3) : BM4.LabelSystem.{1} N where
  Lab := Ordinal.{0}
  rel := lab N
  rel_lt := fun h => h.1
  rel_trans := lab_trans
  reflect := by
    intro n α β hn hrel X hX s y hs hy hyge hylt
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · obtain ⟨y', hy'lt, hsame⟩ := reflect_zero hrel hX hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      exact ⟨y', h1, hy'lt, h2, fun x hx i hi k _ => h3 x hx i hi k,
        fun i j hi hj k _ => h4 i j hi hj k, fun _ _ m hm => absurd hm (by omega)⟩
    · obtain ⟨y', hy'lt, hsame, htop⟩ := reflect_one hrel hX hs hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      refine ⟨y', h1, hy'lt, h2, fun x hx i hi k _ => h3 x hx i hi k,
        fun i j hi hj k _ => h4 i j hi hj k, fun i hi m hm hr => ?_⟩
      rcases (by omega : m = 0) with rfl
      exact htop i hi hr
    · obtain ⟨y', hy'lt, hsame, htop0, htop1⟩ := reflect_two hrel hX hs hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      refine ⟨y', h1, hy'lt, h2, fun x hx i hi k _ => h3 x hx i hi k,
        fun i j hi hj k _ => h4 i j hi hj k, fun i hi m hm hr => ?_⟩
      rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
      · exact htop0 i hi hr
      · exact htop1 i hi hr

end Pat
