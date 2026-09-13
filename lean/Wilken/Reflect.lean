/-
  Finite pattern reflection (the `reflect` field of the label interface) for R2 with two rows:

    ◁₀ = <₁,   ◁₁ = <₂.

  n = 0: Σ₁-elementarity of `α` in `β` copies a finite configuration below `α`.
  n = 1: Σ₂-elementarity additionally keeps the `<₁`-connections to the top
         (Carlson–Wilken, Tracking chains of Σ₂-elementarity, Lemma 7.6).
-/
import Wilken.R2
import Bm4.Label

open Classical

namespace Wilken

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

theorem cat_left {k : ℕ} {p q : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < k) : cat k p q i = p i := by
  simp [cat, hi]

theorem cat_right {k : ℕ} {p q : ℕ → Ordinal.{0}} (i : ℕ) : cat k p q (k + i) = q i := by
  simp [cat]

theorem cat_self {k : ℕ} {p q : ℕ → Ordinal.{0}} : cat k p q k = q 0 := by
  simp [cat]

theorem cat_cat_lt {k m : ℕ} {p x y : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < k + m) :
    cat k p (cat m x y) i = cat k p x i := by
  unfold cat
  split_ifs with h1 h2 <;> first | rfl | omega

/-! ### The label relations -/

/-- `◁₀ = <₁`, `◁₁ = <₂`; higher rows are not used. -/
def rel : ℕ → Ordinal.{0} → Ordinal.{0} → Prop
  | 0 => lt1
  | 1 => lt2
  | _ + 2 => fun _ _ => False

theorem rel_lt {k : ℕ} {a b : Ordinal.{0}} (h : rel k a b) : a < b := by
  match k, h with
  | 0, h => exact h.1
  | 1, h => exact h.1

theorem rel_trans {k : ℕ} {a b c : Ordinal.{0}} (h1 : rel k a b) (h2 : rel k b c) : rel k a c := by
  match k, h1, h2 with
  | 0, h1, h2 => exact lt1_trans h1 h2
  | 1, h1, h2 => exact lt2_trans h1 h2

/-! ### Reading a copy off a diagram -/

/-- Same atomic bits on positions `< k + s` of `cat k p y'` and `cat k p y`. -/
def SameBits (k s : ℕ) (p y y' : ℕ → Ordinal.{0}) : Prop :=
  ∀ a < k + s, ∀ b < k + s,
    bits R2 (cat k p y' a) (cat k p y' b) = bits R2 (cat k p y a) (cat k p y b)

theorem lt_transfer {a b c d : Ordinal.{0}} (h : bits R2 a b = bits R2 c d)
    (h' : bits R2 b a = bits R2 d c) :
    (c < d → a < b) ∧ (rel 0 c d → rel 0 a b) ∧ (rel 1 c d → rel 1 a b) := by
  have e := bits_eq_iff h
  have e' := bits_eq_iff h'
  have hlt : c < d → a < b := fun hcd => lt_of_not_ge fun hba => not_le.mpr hcd (e'.1.mp hba)
  refine ⟨hlt, fun hr => ⟨hlt hr.1, e.2.1.mpr hr.2⟩, fun hr => ⟨hlt hr.1, e.2.2.mpr hr.2⟩⟩

/-- A tuple `y'` below `α` with the same diagram as `y` over the parameters `X` satisfies the
first five clauses of `reflect`. -/
theorem copy_props {X : Finset Ordinal.{0}} {α : Ordinal.{0}} {s : ℕ} {y y' : ℕ → Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) (hs : 0 < s) (hyge : ∀ i, i < s → α ≤ y i)
    (hsame : SameBits X.card s (listTuple X) y y') :
    (∀ i j, i < j → j < s → y i < y j) →
      (∀ i j, i < j → j < s → y' i < y' j) ∧
      (∀ x ∈ X, x < y' 0) ∧
      (∀ x ∈ X, ∀ i, i < s → ∀ k, k < 2 → rel k x (y i) → rel k x (y' i)) ∧
      (∀ i j, i < s → j < s → ∀ k, k < 2 → rel k (y i) (y j) → rel k (y' i) (y' j)) := by
  intro hy
  have tr : ∀ a < X.card + s, ∀ b < X.card + s,
      (cat X.card (listTuple X) y a < cat X.card (listTuple X) y b →
        cat X.card (listTuple X) y' a < cat X.card (listTuple X) y' b) ∧
      (rel 0 (cat X.card (listTuple X) y a) (cat X.card (listTuple X) y b) →
        rel 0 (cat X.card (listTuple X) y' a) (cat X.card (listTuple X) y' b)) ∧
      (rel 1 (cat X.card (listTuple X) y a) (cat X.card (listTuple X) y b) →
        rel 1 (cat X.card (listTuple X) y' a) (cat X.card (listTuple X) y' b)) :=
    fun a ha b hb => lt_transfer (hsame a ha b hb) (hsame b hb a ha)
  have two : ∀ {j : ℕ}, j < 2 → j = 0 ∨ j = 1 := fun h => by omega
  refine ⟨fun i j hij hj => ?_, fun x hx => ?_, fun x hx i hi j hj hr => ?_,
    fun i j hi hj t ht hr => ?_⟩
  · have := (tr (X.card + i) (by omega) (X.card + j) (by omega)).1
    simp only [cat_right] at this
    exact this (hy i j hij hj)
  · obtain ⟨a, ha, rfl⟩ := mem_listTuple hx
    have := (tr a (by omega) (X.card + 0) (by omega)).1
    simp only [cat_right, cat_left ha] at this
    exact this ((hX _ hx).trans_le (hyge 0 hs))
  · obtain ⟨a, ha, rfl⟩ := mem_listTuple hx
    have h := tr a (by omega) (X.card + i) (by omega)
    simp only [cat_right, cat_left ha] at h
    rcases two hj with rfl | rfl
    · exact h.2.1 hr
    · exact h.2.2 hr
  · have h := tr (X.card + i) (by omega) (X.card + j) (by omega)
    simp only [cat_right] at h
    rcases two ht with rfl | rfl
    · exact h.2.1 hr
    · exact h.2.2 hr

/-! ### n = 0 -/

theorem reflect_zero {α β : Ordinal.{0}} (h : lt1 α β) {X : Finset Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) {s : ℕ} {y : ℕ → Ordinal.{0}} (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧ SameBits X.card s (listTuple X) y y' := by
  have hp : ∀ i < X.card, listTuple X i < α := listTuple_lt hX
  let D : Set (Diag (X.card + s + 0)) :=
    {d | ∀ a b : Fin (X.card + s + 0),
      d a b = bits R2 (cat X.card (listTuple X) y a) (cat X.card (listTuple X) y b)}
  have hβ : Sat R2 β X.card s 0 D (listTuple X) := by
    refine ⟨y, fun i hi => hylt i hi, fun z _ => ?_⟩
    intro a b
    simp only [diag]
    rw [cat_cat_lt (by omega : (a : ℕ) < X.card + s), cat_cat_lt (by omega : (b : ℕ) < X.card + s)]
  obtain ⟨_, e⟩ := le1_iff.mp h.2
  obtain ⟨y', hy', hD⟩ := (e X.card s D (listTuple X) hp).mpr hβ
  refine ⟨y', hy', fun a ha b hb => ?_⟩
  have := hD (fun _ => 0) (fun j hj => absurd hj (by omega)) ⟨a, by omega⟩ ⟨b, by omega⟩
  simp only [diag] at this
  rwa [cat_cat_lt (by omega : a < X.card + s), cat_cat_lt (by omega : b < X.card + s)] at this

/-! ### n = 1 -/

theorem reflect_one {α β : Ordinal.{0}} (h : lt2 α β) {X : Finset Ordinal.{0}}
    (hX : ∀ x ∈ X, x < α) {s : ℕ} (hs : 0 < s) {y : ℕ → Ordinal.{0}}
    (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧ SameBits X.card s (listTuple X) y y' ∧
      ∀ i, i < s → lt1 (y i) β → lt1 (y' i) α := by
  have hp : ∀ i < X.card, listTuple X i < α := listTuple_lt hX
  let D : Set (Diag (X.card + s + 1)) :=
    {d | (∀ a b : Fin (X.card + s + 1), (a : ℕ) < X.card + s → (b : ℕ) < X.card + s →
          d a b = bits R2 (cat X.card (listTuple X) y a) (cat X.card (listTuple X) y b)) ∧
        ∀ i (hi : i < s), lt1 (y i) β →
          (d ⟨X.card + i, by omega⟩ ⟨X.card + s, by omega⟩).1 = true →
          (d ⟨X.card + i, by omega⟩ ⟨X.card + s, by omega⟩).2.1 = true}
  have hβ : Sat R2 β X.card s 1 D (listTuple X) := by
    refine ⟨y, fun i hi => hylt i hi, fun z hz => ⟨fun a b ha hb => ?_, fun i hi hi1 hle => ?_⟩⟩
    · simp only [diag]
      rw [cat_cat_lt ha, cat_cat_lt hb]
    · simp only [diag, bits, cat_right, cat_left hi, cat_self, decide_eq_true_eq] at hle ⊢
      exact le1_of_le_of_le1 hle (hz 0 (by omega)).le hi1.2
  obtain ⟨_, e⟩ := le2_iff.mp h.2
  obtain ⟨y', hy', hD⟩ := (e X.card s 1 D (listTuple X) hp).mpr hβ
  have hα0 : 0 < α := lt_of_le_of_lt zero_le (hy' 0 hs)
  refine ⟨y', hy', fun a ha b hb => ?_, fun i hi hi1 => ⟨hy' i hi, ?_⟩⟩
  · have := (hD (fun _ => 0) (fun _ _ => hα0)).1 ⟨a, by omega⟩ ⟨b, by omega⟩ ha hb
    simp only [diag] at this
    rwa [cat_cat_lt ha, cat_cat_lt hb] at this
  · refine le1_of_forall (hy' i hi).le (succ_lt_of_lt1 (lt1_of_lt2 h)) fun v hv hvα => ?_
    have h2 := (hD (fun _ => v) (fun _ _ => hvα)).2 i hi hi1
    simp only [diag, bits, cat_right, cat_left hi, cat_self, decide_eq_true_eq] at h2
    exact h2 hv

/-! ### The label system -/

/-- R2 as a label system for arrays with two rows. -/
noncomputable def labelSystem : BM4.LabelSystem.{1} 2 where
  Lab := Ordinal.{0}
  rel := rel
  rel_lt := rel_lt
  rel_trans := rel_trans
  reflect := by
    intro n α β hn hrel X hX s y hs hy hyge hylt
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
    · obtain ⟨y', hy'lt, hsame⟩ := reflect_zero hrel hX hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      exact ⟨y', h1, hy'lt, h2, h3, h4, fun _ _ m hm => absurd hm (by omega)⟩
    · obtain ⟨y', hy'lt, hsame, htop⟩ := reflect_one hrel hX hs hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      refine ⟨y', h1, hy'lt, h2, h3, h4, fun i hi m hm hr => ?_⟩
      rcases (by omega : m = 0) with rfl
      exact htop i hi hr

end Wilken
