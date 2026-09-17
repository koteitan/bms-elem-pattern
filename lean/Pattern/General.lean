/-
  Finite pattern reflection in R_N for every level (towards termination of BMS with any number
  of rows).

  Semantic part: continuity along cofinal sets at every level (P4'), `≤_{j+1}` closed along
  `≤_j` (general P2), and the formulas `Φ_m` that say "`u` is `≤_m`-connected to the top".
-/
import Pattern.Reflect

open Classical

namespace Pat

variable {N : ℕ}

/-! ### P4 for every level -/

/-- Continuity along a cofinal set at level `j`, provided every `v ∈ S` is
`Σ_{j-2}`-elementary in `α`. -/
theorem elem_cofinal_gen {R : Rels N} {j : ℕ} {y α : Ordinal.{0}} (hyα : y < α)
    (hS : ∀ z < α, ∃ v, z < v ∧ v < α ∧ y ≤ v ∧ Elem R j y v ∧ Elem R (j - 2) v α) :
    Elem R j y α := by
  have hα0 : 0 < α := lt_of_le_of_lt zero_le hyα
  intro bs hbs k n hn D p hp
  match bs, hbs, hn with
  | [], _, _ => exact Iff.rfl
  | [b], hbs, hn =>
    refine ⟨sig_up1 hyα.le, ?_⟩
    rintro ⟨x, hx, hD⟩
    obtain ⟨z, hz, hxz⟩ := exists_bound hα0 b x hx
    obtain ⟨v, hzv, _, _, ev, _⟩ := hS z hz
    have hsv : Sig R v n D [b] k p := ⟨x, fun i hi => (hxz i hi).trans_lt hzv, hD⟩
    exact (ev [b] hbs k n hn D p hp).mpr hsv
  | b :: c :: rest, hbs, hn =>
    have hlen : rest.length ≤ j - 2 := by simp at hbs; omega
    constructor
    · rintro ⟨x, hx, hnot⟩
      refine ⟨x, fun i hi => (hx i hi).trans hyα, fun hα => hnot ?_⟩
      obtain ⟨z, hz, hnz⟩ := hα
      obtain ⟨w, hw, hzw⟩ := exists_bound hα0 c z hz
      obtain ⟨v, hwv, _, hyv, ev, evα⟩ := hS w hw
      have hq : ∀ i < k + b, cat k p x i < v := cat_lt (fun i hi => (hp i hi).trans_le hyv)
        (fun i hi => (hx i hi).trans_le hyv)
      have hqz : ∀ i < k + b + c, cat (k + b) (cat k p x) z i < v :=
        cat_lt hq (fun i hi => (hzw i hi).trans_lt hwv)
      have hrest : ¬ Sig R v n D rest (k + b + c) (cat (k + b) (cat k p x) z) := fun hv =>
        hnz ((evα rest hlen (k + b + c) n (by simp at hn ⊢; omega) D _ hqz).mp hv)
      have hsv : Sig R v n D (c :: rest) (k + b) (cat k p x) :=
        ⟨z, fun i hi => (hzw i hi).trans_lt hwv, hrest⟩
      exact (ev (c :: rest) (by simp at hbs ⊢; omega) (k + b) n (by simp at hn ⊢; omega) D
        (cat k p x) (cat_lt hp hx)).mpr hsv
    · rintro ⟨x, hx, hnot⟩
      obtain ⟨w, hw, hxw⟩ := exists_bound hα0 b x hx
      obtain ⟨v, hwv, hvα, hyv, ev, evα⟩ := hS w hw
      have hq : ∀ i < k + b, cat k p x i < v := cat_lt (fun i hi => (hp i hi).trans_le hyv)
        (fun i hi => (hxw i hi).trans_lt hwv)
      have hsv : Sig R v n D (b :: c :: rest) k p := by
        refine ⟨x, fun i hi => (hxw i hi).trans_lt hwv, fun hv => hnot ?_⟩
        obtain ⟨z, hz, hnz⟩ := hv
        have hqz : ∀ i < k + b + c, cat (k + b) (cat k p x) z i < v := cat_lt hq hz
        refine ⟨z, fun i hi => (hz i hi).trans hvα, fun hα => hnz ?_⟩
        exact (evα rest hlen (k + b + c) n (by simp at hn ⊢; omega) D _ hqz).mpr hα
      exact (ev (b :: c :: rest) hbs k n hn D p hp).mpr hsv

/-! ### General P2 -/

/-- `Σ_{j+1}` along `Σ_j`: if `a ≼_j b ≼_j c` and `a ≼_{j+1} c`, then `a ≼_{j+1} b`. -/
theorem elem_of_elem_top {R : Rels N} {j : ℕ} {a b c : Ordinal.{0}} (hab : a ≤ b) (hbc : b ≤ c)
    (eab : Elem R j a b) (ebc : Elem R j b c) (eac : Elem R (j + 1) a c) :
    Elem R (j + 1) a b := by
  intro bs hbs k n hn D p hp
  match bs, hbs, hn with
  | [], _, _ => exact Iff.rfl
  | b0 :: rest, hbs, hn =>
    have hlen : rest.length ≤ j := by simp at hbs; omega
    have hn' : n = k + b0 + rest.sum := by simp at hn; omega
    constructor
    · rintro ⟨x, hx, hnot⟩
      refine ⟨x, fun i hi => (hx i hi).trans_le hab, fun hb => hnot ?_⟩
      exact (eab rest hlen (k + b0) n hn' D (cat k p x) (cat_lt hp hx)).mpr hb
    · rintro ⟨x, hx, hnot⟩
      have hc : Sig R c n D (b0 :: rest) k p := by
        refine ⟨x, fun i hi => (hx i hi).trans_le hbc, fun hc => hnot ?_⟩
        exact (ebc rest hlen (k + b0) n hn' D (cat k p x)
          (cat_lt (fun i hi => (hp i hi).trans_le hab) hx)).mpr hc
      exact (eac (b0 :: rest) hbs k n hn D p hp).mpr hc

/-- `≤_{j+1}` along `≤_j`. -/
theorem lev_of_lev_top {j : ℕ} {a b c : Ordinal.{0}} (hab : lev N j a b) (hbc : lev N j b c)
    (hac : lev N (j + 1) a c) : lev N (j + 1) a b := by
  have hN := hac.1
  obtain ⟨hab', eab⟩ := (lev_iff hab.1).mp hab
  obtain ⟨hbc', ebc⟩ := (lev_iff hbc.1).mp hbc
  obtain ⟨_, eac⟩ := (lev_iff hN).mp hac
  exact (lev_iff hN).mpr ⟨hab', elem_of_elem_top hab' hbc' eab ebc eac⟩

/-- If `u ≤ s ≤ γ`, `u ≤_{j+1} γ` and `s ≤_j γ` (nothing for `j = 0`), then `u ≤_{j+1} s`. -/
theorem lev_below_top : ∀ {j : ℕ} {u s γ : Ordinal.{0}}, u ≤ s → s ≤ γ → lev N j u γ →
    (∀ i, i + 1 ≤ j → lev N i s γ) → lev N j u s
  | 0, _, _, _, hus, hsγ, hu, _ => lev0_of_le hus hsγ hu
  | j + 1, _, _, _, hus, hsγ, hu, hs => by
    have hs' : lev N j _ _ := hs j le_rfl
    have hus' : lev N j _ _ := lev_below_top hus hsγ (lev_mono (Nat.le_succ j) hu)
      fun i hi => hs i (by omega)
    exact lev_of_lev_top hus' hs' hu

/-! ### Connection to the top: `Φ_m` -/

/-- `Φ_m(u)` evaluated below `γ` (level `m ≥ 1`; `Φ_0` is true):
`Φ₁(u) = ∀w (u ≤ w → u ≤₁ w)`, `Φ₂(u) = ∀z ∃s (z < s ∧ u ≤₂ s)`,
`Φ_{m+2}(u) = ∀z ∃s (z < s ∧ u ≤_{m+2} s ∧ Φ_m(s))`. -/
def Phi (N : ℕ) (γ : Ordinal.{0}) : ℕ → Ordinal.{0} → Prop
  | 0, _ => True
  | 1, u => ∀ w < γ, u ≤ w → lev N 0 u w
  | 2, u => ∀ z < γ, ∃ s < γ, z < s ∧ lev N 1 u s
  | m + 3, u => ∀ z < γ, ∃ s < γ, z < s ∧ lev N (m + 2) u s ∧ Phi N γ (m + 1) s

/-- The `≤_{j+1}`-predecessors of `γ` are cofinal in `γ`. -/
def Cof (N : ℕ) (j : ℕ) (γ : Ordinal.{0}) : Prop := ∀ z < γ, ∃ s, z < s ∧ s < γ ∧ lev N j s γ

theorem Cof.mono {i j : ℕ} {γ : Ordinal.{0}} (hij : i ≤ j) (h : Cof N j γ) : Cof N i γ :=
  fun z hz => (h z hz).imp fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2, lev_mono hij h3⟩

/-- `Φ_m(u)` below a successor-closed `γ` gives `u ≤_m γ`. -/
theorem lev_of_phi (hγ : ∀ z < γ, Order.succ z < γ) :
    ∀ {m : ℕ} {u : Ordinal.{0}}, m < N → u < γ → Phi N γ (m + 1) u → lev N m u γ
  | 0, u, hN, hu, h => lev0_of_forall (by omega) hu.le hγ fun w huw hw => h w hw huw
  | 1, u, hN, hu, h => by
    refine (lev_iff hN).mpr ⟨hu.le, elem_cofinal le_rfl hu fun z hz => ?_⟩
    obtain ⟨s, hs, hzs, hl⟩ := h (max z u) (max_lt hz hu)
    exact ⟨s, (le_max_left _ _).trans_lt hzs, hs, ((le_max_right _ _).trans hzs.le),
      ((lev_iff hN).mp hl).2⟩
  | m + 2, u, hN, hu, h => by
    refine (lev_iff hN).mpr ⟨hu.le, elem_cofinal_gen hu fun z hz => ?_⟩
    obtain ⟨s, hs, hzs, hl, hphi⟩ := h (max z u) (max_lt hz hu)
    have hsγ : lev N m s γ := lev_of_phi hγ (by omega) hs hphi
    refine ⟨s, (le_max_left _ _).trans_lt hzs, hs, (le_max_right _ _).trans hzs.le,
      ((lev_iff hN).mp hl).2, ?_⟩
    simpa using ((lev_iff hsγ.1).mp hsγ).2

/-- Conversely, `u ≤_m γ` gives `Φ_m(u)` below `γ` when the `≤_{m-1}`-predecessors of `γ`
are cofinal. -/
theorem phi_of_lev :
    ∀ {m : ℕ} {u γ : Ordinal.{0}}, u < γ → lev N m u γ → (∀ i, i + 1 ≤ m → Cof N (i) γ) →
      Phi N γ (m + 1) u
  | 0, u, γ, hu, h, _ => fun w hw huw => lev0_of_le huw hw.le h
  | 1, u, γ, hu, h, hc => by
    intro z hz
    obtain ⟨s, hzs, hs, hsγ⟩ := hc 0 le_rfl (max z u) (max_lt hz hu)
    refine ⟨s, hs, (le_max_left _ _).trans_lt hzs, ?_⟩
    exact lev_below_top ((le_max_right _ _).trans hzs.le) hs.le h fun i hi => by
      rcases (by omega : i = 0) with rfl; exact hsγ
  | m + 2, u, γ, hu, h, hc => by
    intro z hz
    obtain ⟨s, hzs, hs, hsγ⟩ := hc (m + 1) le_rfl (max z u) (max_lt hz hu)
    refine ⟨s, hs, (le_max_left _ _).trans_lt hzs, ?_, ?_⟩
    · exact lev_below_top ((le_max_right _ _).trans hzs.le) hs.le h fun i hi =>
        lev_mono (by omega) hsγ
    · exact phi_of_lev hs (lev_mono (by omega) hsγ) fun i hi => hc i (by omega)

/-! ### Conditions on diagrams -/

/-- A condition on diagrams of any size, read through `get`. -/
abbrev DP (N : ℕ) := ∀ {n : ℕ}, Diag N n → Prop

/-- `P` only reads the entries between positions below `B`. -/
def Reads (P : DP N) (B : ℕ) : Prop :=
  ∀ {n n' : ℕ} (d : Diag N n) (d' : Diag N n'),
    (∀ a < B, ∀ b < B, ∀ c, get d a b c = get d' a b c) → (P d ↔ P d')

theorem get_diag {n : ℕ} {v : ℕ → Ordinal.{0}} {a b : ℕ} (ha : a < n) (hb : b < n)
    (c : Fin (N + 1)) : get (diag (RN N) n v) a b c = bits (RN N) (v a) (v b) c := by
  simp [get, diag, ha, hb]

theorem Reads.diag_iff {P : DP N} {B : ℕ} (hP : Reads P B) {n n' : ℕ} {v w : ℕ → Ordinal.{0}}
    (hn : B ≤ n) (hn' : B ≤ n') (hvw : ∀ i < B, v i = w i) :
    P (diag (RN N) n v) ↔ P (diag (RN N) n' w) :=
  hP _ _ fun a ha b hb c => by
    rw [get_diag (by omega) (by omega), get_diag (by omega) (by omega), hvw a ha, hvw b hb]

theorem Reads.mono {P : DP N} {B B' : ℕ} (h : Reads P B) (hBB' : B ≤ B') : Reads P B' :=
  fun d d' hdd' => h d d' fun a ha b hb c => hdd' a (by omega) b (by omega) c

theorem reads_gle {a b B : ℕ} (ha : a < B) (hb : b < B) :
    Reads (N := N) (fun d => GLe d a b) B :=
  fun d d' h => by
    show get d a b 0 = true ↔ get d' a b 0 = true
    rw [h a ha b hb]

theorem reads_glev {j a b B : ℕ} (ha : a < B) (hb : b < B) :
    Reads (N := N) (fun d => GLev d j a b) B :=
  fun d d' h => by
    show (∃ hj : j < N, get d a b (Fin.succ ⟨j, hj⟩) = true) ↔
      (∃ hj : j < N, get d' a b (Fin.succ ⟨j, hj⟩) = true)
    simp only [h a ha b hb]

/-! ### Skolem normal forms for coordinatewise conditions -/

theorem skolem_one {γ : Ordinal.{0}} (hγ : 0 < γ) {s : ℕ} {G : Prop} {Q : ℕ → Prop}
    {P : ℕ → Ordinal.{0} → Prop} :
    (∃ W : ℕ → Ordinal.{0}, (∀ i < s, W i < γ) ∧ (G ∧ ∀ i < s, Q i ∨ P i (W i))) ↔
      (G ∧ ∀ i < s, Q i ∨ ∃ w < γ, P i w) := by
  constructor
  · rintro ⟨W, hW, hG, h⟩
    exact ⟨hG, fun i hi => (h i hi).imp_right fun hp => ⟨W i, hW i hi, hp⟩⟩
  · rintro ⟨hG, h⟩
    have hc : ∀ i, ∃ w, w < γ ∧ (i < s → Q i ∨ P i w) := by
      intro i
      by_cases hi : i < s
      · rcases h i hi with hq | ⟨w, hw, hp⟩
        · exact ⟨0, hγ, fun _ => Or.inl hq⟩
        · exact ⟨w, hw, fun _ => Or.inr hp⟩
      · exact ⟨0, hγ, fun h' => absurd h' hi⟩
    choose W hW hWp using hc
    exact ⟨W, fun i _ => hW i, hG, fun i hi => hWp i hi⟩

theorem skolem_two {γ : Ordinal.{0}} (hγ : 0 < γ) {s : ℕ} {G : Prop} {Q : ℕ → Prop}
    {P : ℕ → Ordinal.{0} → Ordinal.{0} → Prop} :
    (∃ Z : ℕ → Ordinal.{0}, (∀ i < s, Z i < γ) ∧
        ∀ S : ℕ → Ordinal.{0}, (∀ i < s, S i < γ) → (G ∧ ∀ i < s, Q i ∨ P i (Z i) (S i))) ↔
      (G ∧ ∀ i < s, Q i ∨ ∃ z < γ, ∀ t < γ, P i z t) := by
  constructor
  · rintro ⟨Z, hZ, h⟩
    refine ⟨(h (fun _ => 0) fun _ _ => hγ).1, fun i hi => ?_⟩
    by_cases hq : Q i
    · exact Or.inl hq
    · refine Or.inr ⟨Z i, hZ i hi, fun t ht => ?_⟩
      exact ((h (fun _ => t) fun _ _ => ht).2 i hi).resolve_left hq
  · rintro ⟨hG, h⟩
    have hc : ∀ i, ∃ z, z < γ ∧ (i < s → Q i ∨ ∀ t < γ, P i z t) := by
      intro i
      by_cases hi : i < s
      · rcases h i hi with hq | ⟨z, hz, hp⟩
        · exact ⟨0, hγ, fun _ => Or.inl hq⟩
        · exact ⟨z, hz, fun _ => Or.inr hp⟩
      · exact ⟨0, hγ, fun h' => absurd h' hi⟩
    choose Z hZ hZp using hc
    exact ⟨Z, fun i _ => hZ i, fun S hS => ⟨hG, fun i hi =>
      (hZp i hi).imp_right fun hp => hp (S i) (hS i hi)⟩⟩

/-! ### `G ∧ ∀ i < s, Q_i ∨ ¬ Φ_d(v_{c+i})` in block form -/

/-- The matrix of the block form (blocks `replicate d s`). The tuple is at `c, …, c+s-1`;
the block variables of a pair of blocks are at `c+s, …` and `c+2s, …`. -/
def tnMat (s : ℕ) (G : DP N) : ℕ → ℕ → (ℕ → DP N) → DP N
  | 0, _, Q => fun d => G d ∧ ∀ i < s, Q i d
  | 1, c, Q => fun d => ¬ (G d ∧ ∀ i < s, Q i d ∨
      (GLe d (c + i) (c + s + i) ∧ ¬ GLev d 0 (c + i) (c + s + i)))
  | 2, c, Q => fun d => G d ∧ ∀ i < s, Q i d ∨
      ¬ (¬ GLe d (c + s + s + i) (c + s + i) ∧ GLev d 1 (c + i) (c + s + s + i))
  | m + 3, c, Q => tnMat s G (m + 1) (c + s + s) fun i {_} d => Q i d ∨
      ¬ (¬ GLe d (c + s + s + i) (c + s + i) ∧ GLev d (m + 2) (c + i) (c + s + s + i))

theorem cat2_v {c s : ℕ} {v Z S : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < c + s) :
    cat (c + s + s) (cat (c + s) v Z) S i = v i := by
  rw [cat_left (by omega), cat_left hi]

theorem cat2_Z {c s : ℕ} {v Z S : ℕ → Ordinal.{0}} {i : ℕ} (hi : i < s) :
    cat (c + s + s) (cat (c + s) v Z) S (c + s + i) = Z i := by
  rw [cat_left (by omega), cat_right]

theorem cat2_S {c s : ℕ} {v Z S : ℕ → Ordinal.{0}} (i : ℕ) :
    cat (c + s + s) (cat (c + s) v Z) S (c + s + s + i) = S i := cat_right i

theorem not_phi_one {γ u : Ordinal.{0}} :
    ¬ Phi N γ 1 u ↔ ∃ w < γ, u ≤ w ∧ ¬ lev N 0 u w := by
  simp only [Phi, not_forall, exists_prop]

theorem not_phi_two {γ u : Ordinal.{0}} :
    ¬ Phi N γ 2 u ↔ ∃ z < γ, ∀ t < γ, ¬ (z < t ∧ lev N 1 u t) := by
  simp only [Phi, not_forall, not_exists, exists_prop]
  exact exists_congr fun z => and_congr_right fun _ => forall_congr' fun t => by tauto

theorem not_phi_add_three {γ u : Ordinal.{0}} {m : ℕ} :
    ¬ Phi N γ (m + 3) u ↔
      ∃ z < γ, ∀ t < γ, ¬ (z < t ∧ lev N (m + 2) u t) ∨ ¬ Phi N γ (m + 1) t := by
  simp only [Phi, not_forall, not_exists, exists_prop]
  exact exists_congr fun z => and_congr_right fun _ => forall_congr' fun t => by tauto

theorem not_exists_and_not {α : Type*} {B P : α → Prop} :
    (¬ ∃ x, B x ∧ ¬ P x) ↔ ∀ x, B x → P x :=
  ⟨fun h x hb => by_contra fun hp => h ⟨x, hb, hp⟩, fun h ⟨x, hb, hp⟩ => hp (h x hb)⟩

/-- The block form of `G ∧ ∀ i < s, Q_i ∨ ¬ Φ_d(v_{c+i})`. -/
theorem tn_sig {s : ℕ} {γ : Ordinal.{0}} (hγ : 0 < γ) {G : DP N} :
    ∀ (d c : ℕ) (Q : ℕ → DP N) (n : ℕ) (v : ℕ → Ordinal.{0}),
      Reads G c → (∀ i < s, Reads (Q i) (c + s)) → c + s + d * s ≤ n →
      (Sig (RN N) γ n {x | tnMat s G d c Q x} (List.replicate d s) (c + s) v ↔
        (G (diag (RN N) c v) ∧ ∀ i < s, Q i (diag (RN N) (c + s) v) ∨ ¬ Phi N γ d (v (c + i))))
  | 0, c, Q, n, v, hG, hQ, hn => by
    have hn' : c + s ≤ n := by simpa using hn
    simp only [List.replicate, sig_nil, Set.mem_setOf_eq, tnMat, Phi, not_true_eq_false,
      or_false]
    rw [hG.diag_iff (by omega) le_rfl fun _ _ => rfl]
    exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi =>
      Reads.diag_iff (hQ i hi) hn' le_rfl fun _ _ => rfl
  | 1, c, Q, n, v, hG, hQ, hn => by
    have hn' : c + s + s ≤ n := by simpa using hn
    have key : ∀ W : ℕ → Ordinal.{0},
        (¬ Sig (RN N) γ n {x | tnMat s G 1 c Q x} [] (c + s + s) (cat (c + s) v W)) ↔
          (G (diag (RN N) c v) ∧ ∀ i < s, Q i (diag (RN N) (c + s) v) ∨
            (v (c + i) ≤ W i ∧ ¬ lev N 0 (v (c + i)) (W i))) := by
      intro W
      simp only [sig_nil, Set.mem_setOf_eq, tnMat, not_not]
      rw [hG.diag_iff (by omega) le_rfl fun i hi => cat_left (by omega)]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi => ?_
      rw [Reads.diag_iff (hQ i hi) (by omega) le_rfl fun j hj => cat_left hj,
        gle_diag (by omega) (by omega), glev_diag (by omega) (by omega),
        cat_left (by omega), cat_right]
    show (∃ W : ℕ → Ordinal.{0}, (∀ i < s, W i < γ) ∧
        ¬ Sig (RN N) γ n {x | tnMat s G 1 c Q x} [] (c + s + s) (cat (c + s) v W)) ↔ _
    simp only [key]
    refine (skolem_one hγ (G := G (diag (RN N) c v)) (Q := fun i => Q i (diag (RN N) (c + s) v))
      (P := fun i w => v (c + i) ≤ w ∧ ¬ lev N 0 (v (c + i)) w)).trans ?_
    exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun _ =>
      or_congr_right not_phi_one.symm
  | 2, c, Q, n, v, hG, hQ, hn => by
    have hn' : c + s + s + s ≤ n := by
      have : 2 * s = s + s := by ring
      omega
    have key : ∀ Z S : ℕ → Ordinal.{0},
        (¬ Sig (RN N) γ n {x | tnMat s G 2 c Q x} [] (c + s + s + s)
            (cat (c + s + s) (cat (c + s) v Z) S)) ↔
          ¬ (G (diag (RN N) c v) ∧ ∀ i < s, Q i (diag (RN N) (c + s) v) ∨
            ¬ (Z i < S i ∧ lev N 1 (v (c + i)) (S i))) := by
      intro Z S
      simp only [sig_nil, Set.mem_setOf_eq, tnMat]
      refine not_congr ?_
      rw [hG.diag_iff (by omega) le_rfl fun i hi => cat2_v (by omega)]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi => ?_
      rw [Reads.diag_iff (hQ i hi) (by omega) le_rfl fun j hj => cat2_v hj,
        gle_diag (by omega) (by omega), glev_diag (by omega) (by omega),
        cat2_S, cat2_Z hi, cat2_v (by omega), not_le]
    show (∃ Z : ℕ → Ordinal.{0}, (∀ i < s, Z i < γ) ∧ ¬ ∃ S : ℕ → Ordinal.{0},
        (∀ i < s, S i < γ) ∧ ¬ Sig (RN N) γ n {x | tnMat s G 2 c Q x} [] (c + s + s + s)
          (cat (c + s + s) (cat (c + s) v Z) S)) ↔ _
    simp only [key, not_exists_and_not]
    refine (skolem_two hγ (G := G (diag (RN N) c v)) (Q := fun i => Q i (diag (RN N) (c + s) v))
      (P := fun i z t => ¬ (z < t ∧ lev N 1 (v (c + i)) t))).trans ?_
    exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun _ =>
      or_congr_right not_phi_two.symm
  | m + 3, c, Q, n, v, hG, hQ, hn => by
    have hn' : c + s + s + s + (m + 1) * s ≤ n := by
      have : c + s + s + s + (m + 1) * s = c + s + (m + 3) * s := by ring
      omega
    have hQ' : ∀ i < s, Reads (N := N) (fun d => Q i d ∨
        ¬ (¬ GLe d (c + s + s + i) (c + s + i) ∧ GLev d (m + 2) (c + i) (c + s + s + i)))
        (c + s + s + s) := by
      intro i hi _ _ d d' h
      have e1 := Reads.mono (hQ i hi) (show c + s ≤ c + s + s + s by omega) d d' h
      have e2 := reads_gle (N := N) (a := c + s + s + i) (b := c + s + i)
        (show c + s + s + i < c + s + s + s by omega) (by omega) d d' h
      have e3 := reads_glev (N := N) (j := m + 2) (a := c + i) (b := c + s + s + i)
        (show c + i < c + s + s + s by omega) (by omega) d d' h
      exact or_congr e1 (not_congr (and_congr (not_congr e2) e3))
    have key : ∀ Z S : ℕ → Ordinal.{0},
        (Sig (RN N) γ n {x | tnMat s G (m + 3) c Q x} (List.replicate (m + 1) s)
            (c + s + s + s) (cat (c + s + s) (cat (c + s) v Z) S)) ↔
          (G (diag (RN N) c v) ∧ ∀ i < s, Q i (diag (RN N) (c + s) v) ∨
            (¬ (Z i < S i ∧ lev N (m + 2) (v (c + i)) (S i)) ∨ ¬ Phi N γ (m + 1) (S i))) := by
      intro Z S
      show Sig (RN N) γ n {x | tnMat s G (m + 1) (c + s + s) _ x} (List.replicate (m + 1) s)
        (c + s + s + s) _ ↔ _
      rw [tn_sig hγ (m + 1) (c + s + s) _ n _ (hG.mono (by omega)) hQ' hn']
      rw [hG.diag_iff (by omega) le_rfl fun i hi => cat2_v (by omega)]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi => ?_
      rw [Reads.diag_iff (hQ i hi) (by omega) le_rfl fun j hj => cat2_v hj,
        gle_diag (by omega) (by omega), glev_diag (by omega) (by omega),
        cat2_S, cat2_Z hi, cat2_v (by omega), not_le, or_assoc]
    show (∃ Z : ℕ → Ordinal.{0}, (∀ i < s, Z i < γ) ∧ ¬ ∃ S : ℕ → Ordinal.{0},
        (∀ i < s, S i < γ) ∧ ¬ Sig (RN N) γ n {x | tnMat s G (m + 3) c Q x}
          (List.replicate (m + 1) s) (c + s + s + s)
          (cat (c + s + s) (cat (c + s) v Z) S)) ↔ _
    simp only [key, not_exists_and_not]
    refine (skolem_two hγ (G := G (diag (RN N) c v)) (Q := fun i => Q i (diag (RN N) (c + s) v))
      (P := fun i z t => ¬ (z < t ∧ lev N (m + 2) (v (c + i)) t) ∨ ¬ Phi N γ (m + 1) t)).trans ?_
    exact and_congr_right fun _ => forall_congr' fun i => forall_congr' fun _ =>
      or_congr_right not_phi_add_three.symm

/-! ### Two sentences with one `Φ` -/

/-- The matrix of `∃ u (z < u ∧ Φ_d(u))` (`z` at position 0, `u` at position 1). -/
def exPhiMat (d : ℕ) : DP N := tnMat 1 (fun _ => True) d 1 fun _ {_} x => GLe x 1 0

theorem sig_exists_phi {γ : Ordinal.{0}} (hγ : 0 < γ) (d n : ℕ) (hn : 1 + 1 + d * 1 ≤ n)
    (p : ℕ → Ordinal.{0}) :
    Sig (RN N) γ n {x | exPhiMat d x} (1 :: List.replicate d 1) 1 p ↔
      ∃ u < γ, p 0 < u ∧ Phi N γ d u := by
  have hG : Reads (N := N) (fun _ => True) 1 := fun _ _ _ => Iff.rfl
  have hQ : ∀ i < 1, Reads (N := N) (fun x => GLe x 1 0) (1 + 1) :=
    fun _ _ => reads_gle (by omega) (by omega)
  show (∃ x : ℕ → Ordinal.{0}, (∀ i < 1, x i < γ) ∧
      ¬ Sig (RN N) γ n {x | exPhiMat d x} (List.replicate d 1) (1 + 1) (cat 1 p x)) ↔ _
  simp only [exPhiMat]
  simp only [tn_sig hγ d 1 _ n _ hG hQ hn]
  have hval : ∀ x : ℕ → Ordinal.{0},
      (GLe (diag (RN N) (1 + 1) (cat 1 p x)) 1 0 ↔ x 0 ≤ p 0) ∧ cat 1 p x (1 + 0) = x 0 := by
    intro x
    refine ⟨?_, by simp [cat]⟩
    rw [gle_diag (n := 1 + 1) (a := 1) (b := 0) (by norm_num) (by norm_num)]
    simp [cat]
  constructor
  · rintro ⟨x, hx, hnot⟩
    have h1 : ¬ (GLe (diag (RN N) (1 + 1) (cat 1 p x)) 1 0 ∨
        ¬ Phi N γ d (cat 1 p x (1 + 0))) :=
      fun hc => hnot ⟨trivial, fun i hi => by rcases (by omega : i = 0) with rfl; exact hc⟩
    obtain ⟨hle, hphi⟩ := not_or.mp h1
    rw [(hval x).1] at hle
    rw [(hval x).2, not_not] at hphi
    exact ⟨x 0, hx 0 (by omega), not_le.mp hle, hphi⟩
  · rintro ⟨u, hu, hpu, hphi⟩
    refine ⟨fun _ => u, fun _ _ => hu, fun ⟨_, h⟩ => ?_⟩
    rcases h 0 (by omega) with hle | hn'
    · rw [(hval _).1] at hle
      exact not_le.mpr hpu hle
    · rw [(hval _).2] at hn'
      exact hn' hphi

theorem sig_forall_exists_phi {γ : Ordinal.{0}} (hγ : 0 < γ) (d n : ℕ) (hn : 1 + 1 + d * 1 ≤ n)
    (p : ℕ → Ordinal.{0}) :
    Sig (RN N) γ n {x | exPhiMat d x} (1 :: 1 :: List.replicate d 1) 0 p ↔
      ∃ z < γ, ¬ ∃ u < γ, z < u ∧ Phi N γ d u := by
  show (∃ x : ℕ → Ordinal.{0}, (∀ i < 1, x i < γ) ∧
      ¬ Sig (RN N) γ n {x | exPhiMat d x} (1 :: List.replicate d 1) 1 (cat 0 p x)) ↔ _
  simp only [sig_exists_phi hγ d n hn]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x 0, hx 0 (by omega), by simpa [cat] using h⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨fun _ => z, fun _ _ => hz, by simpa [cat] using h⟩

/-! ### P7 for every level -/

/-- A `<_{j+1}`-lower end is nonzero. -/
theorem pos_of_lab {j : ℕ} {α β : Ordinal.{0}} (h : lab N j α β) : 0 < α := by
  by_contra h0
  have hα : α = 0 := le_antisymm (not_lt.mp h0) zero_le
  obtain ⟨_, e⟩ := (lev_iff h.2.1).mp h.2
  have t := e [1] (by simp) 0 1 (by simp) (∅ : Set (Diag N 1)) (fun _ => 0)
    fun i hi => absurd hi (by omega)
  have hβ : Sig (RN N) β 1 (∅ : Set (Diag N 1)) [1] 0 (fun _ => 0) :=
    ⟨fun _ => 0, fun _ _ => hα ▸ h.1, fun h' => h'⟩
  obtain ⟨x, hx, _⟩ := t.mpr hβ
  have := hx 0 (by omega)
  rw [hα] at this
  exact absurd this (not_lt.mpr zero_le)

/-- If `α <_{j+2} β`, then the `≤_{i+1}`-predecessors of `α` are cofinal in `α` for all
`i ≤ j`. -/
theorem cof_of_lab : ∀ (j : ℕ) {α β : Ordinal.{0}}, lab N (j + 1) α β → ∀ i, i ≤ j → Cof N i α
  | 0, α, β, h, i, hi => by
    rcases (by omega : i = 0) with rfl
    exact exists_lev0_below h
  | j + 1, α, β, h, i, hi => by
    have ih : ∀ i, i ≤ j → Cof N i α := cof_of_lab j (lab_mono (by omega) h)
    rcases (by omega : i ≤ j ∨ i = j + 1) with hij | rfl
    · exact ih i hij
    have hN : j + 2 < N := h.2.1
    obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
    have hαβ : α < β := h.1
    have hα0 : 0 < α := pos_of_lab h
    have hβ0 : 0 < β := hα0.trans hαβ
    have hαlim := succ_lt_of_lab0 (lab_mono (show 0 ≤ j + 2 by omega) h)
    have hβlim := succ_lt_of_lab1_top (lab_mono (show 1 ≤ j + 2 by omega) h)
    set n := 1 + 1 + (j + 2) * 1 with hn
    -- Step A: `∀ z ∃ s (z < s ∧ Φ_{j+1}(s))` below `α`
    have hA : ¬ ∃ z < α, ¬ ∃ u < α, z < u ∧ Phi N α (j + 1) u := by
      rintro ⟨z, hz, hnot⟩
      obtain ⟨s, hzs, hsα, hs⟩ := ih j le_rfl z hz
      exact hnot ⟨s, hsα, hzs, phi_of_lev hsα hs fun i hi => ih i (by omega)⟩
    -- Step B: the same below `β`
    have hB : ¬ ∃ z < β, ¬ ∃ u < β, z < u ∧ Phi N β (j + 1) u := by
      have t := e (1 :: 1 :: List.replicate (j + 1) 1) (by simp) 0 (1 + 1 + (j + 1) * 1)
        (by simp; omega) {x | exPhiMat (j + 1) x} (fun _ => 0) fun i hi => absurd hi (by omega)
      rw [sig_forall_exists_phi hα0 (j + 1) _ le_rfl, sig_forall_exists_phi hβ0 (j + 1) _ le_rfl]
        at t
      exact fun hb => hA (t.mpr hb)
    -- Step C: `Cof_j` below `β`
    have hCβ : Cof N j β := by
      intro z hz
      by_contra hc
      apply hB
      refine ⟨z, hz, fun ⟨u, hu, hzu, hphi⟩ => hc ⟨u, hzu, hu, ?_⟩⟩
      exact lev_of_phi hβlim (by omega) hu hphi
    -- Step D: `Φ_{j+2}(α)` below `β`
    have hD : Phi N β (j + 2) α :=
      phi_of_lev hαβ (lev_mono (by omega) h.2) fun i hi => hCβ.mono (by omega)
    -- Step E: back to `α`
    intro z hz
    have t := e (1 :: List.replicate (j + 2) 1) (by simp) 1 n (by simp [hn]; omega)
      {x | exPhiMat (j + 2) x} (fun _ => z) fun _ _ => hz
    rw [sig_exists_phi hα0 (j + 2) n (by omega), sig_exists_phi hβ0 (j + 2) n (by omega)] at t
    obtain ⟨u, hu, hzu, hphi⟩ := t.mpr ⟨α, hαβ, hz, hD⟩
    exact ⟨u, hzu, hu, lev_of_phi hαlim (by omega) hu hphi⟩

/-! ### Finite reflection at every level -/

theorem elem_zero {R : Rels N} {a b : Ordinal.{0}} : Elem R 0 a b := by
  intro bs hbs k n hn D p hp
  rcases List.length_eq_zero_iff.mp (Nat.le_zero.mp hbs) with rfl
  exact Iff.rfl

/-- `Σ_i`-elementarity from `v ≤_{j+1} α` for `i ≤ j + 1`. -/
theorem elem_of_lev {j i : ℕ} {v α : Ordinal.{0}} (h : lev N j v α) (hi : i ≤ j + 1) :
    Elem (RN N) i v α := by
  obtain ⟨_, e⟩ := (lev_iff h.1).mp h
  exact fun bs hbs => e bs (hbs.trans hi)

/-- Finite reflection for `α <_{n+1} β` with `n ≥ 1`, keeping all connections to the top. -/
theorem reflect_gen {n : ℕ} (hn1 : 1 ≤ n) {α β : Ordinal.{0}} (h : lab N n α β)
    {X : Finset Ordinal.{0}} (hX : ∀ x ∈ X, x < α) {s : ℕ} (hs : 0 < s) {y : ℕ → Ordinal.{0}}
    (hylt : ∀ i, i < s → y i < β) :
    ∃ y' : ℕ → Ordinal.{0}, (∀ i, i < s → y' i < α) ∧
      SameBits (N := N) X.card s (listTuple X) y y' ∧
      ∀ i, i < s → ∀ m, m < n → lab N m (y i) β → lab N m (y' i) α := by
  set k := X.card
  set p := listTuple X
  have hp : ∀ i < k, p i < α := listTuple_lt hX
  have hN : n < N := h.2.1
  obtain ⟨_, e⟩ := (lev_iff hN).mp h.2
  have hαβ : α < β := h.1
  have hα0 : 0 < α := pos_of_lab h
  have hβ0 : 0 < β := hα0.trans hαβ
  have hαlim := succ_lt_of_lab0 (lab_mono (Nat.zero_le n) h)
  have hβlim := succ_lt_of_lab1_top (lab_mono hn1 h)
  let G : DP N := fun d => Agree d (k + s) (cat k p y)
  let Q : ℕ → DP N := fun i {_} d => ¬ GLe d (k + i) (k + s + i) ∨
    ∀ m < n, lab N m (y i) β → GLev d m (k + i) (k + s + i)
  have hG : Reads G (k + s) := by
    intro _ _ d d' hdd'
    show Agree d (k + s) (cat k p y) ↔ Agree d' (k + s) (cat k p y)
    unfold Agree
    exact forall_congr' fun a => forall_congr' fun ha => forall_congr' fun b =>
      forall_congr' fun hb => forall_congr' fun c => by rw [hdd' a ha b hb c]
  have hQ : ∀ i < s, Reads (Q i) (k + s + s) := by
    intro i hi _ _ d d' hdd'
    have e1 := reads_gle (N := N) (a := k + i) (b := k + s + i) (B := k + s + s)
      (by omega) (by omega) d d' hdd'
    have e2 : ∀ m, GLev d m (k + i) (k + s + i) ↔ GLev d' m (k + i) (k + s + i) := fun m =>
      reads_glev (N := N) (j := m) (a := k + i) (b := k + s + i) (B := k + s + s)
        (by omega) (by omega) d d' hdd'
    exact or_congr (not_congr e1) (forall_congr' fun m => forall_congr' fun _ =>
      forall_congr' fun _ => e2 m)
  set bs := s :: s :: List.replicate (n - 1) s with hbs
  set nd := k + bs.sum with hnd
  have hbound : k + s + s + (n - 1) * s ≤ nd := by
    simp only [hnd, hbs, List.sum_cons, List.sum_replicate, smul_eq_mul]
    omega
  have hsem : ∀ γ : Ordinal.{0}, 0 < γ →
      (Sig (RN N) γ nd {x | tnMat s G (n - 1) (k + s) Q x} bs k p ↔
        ∃ U : ℕ → Ordinal.{0}, (∀ i < s, U i < γ) ∧ ∀ V : ℕ → Ordinal.{0}, (∀ i < s, V i < γ) →
          (SameBits (N := N) k s p y U ∧ ∀ i < s,
            (¬ U i ≤ V i ∨ ∀ m < n, lab N m (y i) β → lev N m (U i) (V i)) ∨
              ¬ Phi N γ (n - 1) (V i))) := by
    intro γ hγ
    show (∃ U : ℕ → Ordinal.{0}, (∀ i < s, U i < γ) ∧ ¬ ∃ V : ℕ → Ordinal.{0},
        (∀ i < s, V i < γ) ∧ ¬ Sig (RN N) γ nd {x | tnMat s G (n - 1) (k + s) Q x}
          (List.replicate (n - 1) s) (k + s + s) (cat (k + s) (cat k p U) V)) ↔ _
    refine exists_congr fun U => and_congr_right fun _ => ?_
    rw [not_exists_and_not]
    refine forall_congr' fun V => forall_congr' fun _ => ?_
    rw [tn_sig hγ (n - 1) (k + s) Q nd _ hG hQ hbound]
    refine and_congr ?_ (forall_congr' fun i => forall_congr' fun hi => or_congr ?_ ?_)
    · show Agree _ (k + s) (cat k p y) ↔ _
      rw [agree_iff le_rfl fun a ha => cat_left ha]
      rfl
    · show (¬ GLe _ (k + i) (k + s + i) ∨ ∀ m < n, lab N m (y i) β → GLev _ m (k + i) (k + s + i)) ↔ _
      rw [gle_diag (n := k + s + s) (a := k + i) (b := k + s + i) (by omega) (by omega),
        cat_left (show k + i < k + s by omega), cat_right, cat_right]
      refine or_congr Iff.rfl (forall_congr' fun m => forall_congr' fun _ =>
        forall_congr' fun _ => ?_)
      rw [glev_diag (n := k + s + s) (a := k + i) (b := k + s + i) (by omega) (by omega),
        cat_left (show k + i < k + s by omega), cat_right, cat_right]
    · rw [cat_right]
  -- the sentence holds below `β`
  have hβsat : Sig (RN N) β nd {x | tnMat s G (n - 1) (k + s) Q x} bs k p := by
    refine (hsem β hβ0).mpr ⟨y, hylt, fun V hV => ⟨fun _ _ _ _ => rfl, fun i hi => ?_⟩⟩
    by_cases hle : y i ≤ V i
    swap
    · exact Or.inl (Or.inl hle)
    by_cases hphi : Phi N β (n - 1) (V i)
    swap
    · exact Or.inr hphi
    refine Or.inl (Or.inr fun m hm hlab => ?_)
    refine lev_below_top hle (hV i hi).le hlab.2 fun i' hi' => ?_
    have hn2 : n - 2 + 1 = n - 1 := by omega
    have hVβ : lev N (n - 2) (V i) β :=
      lev_of_phi hβlim (by omega) (hV i hi) (by rw [hn2]; exact hphi)
    exact lev_mono (by omega) hVβ
  -- and therefore below `α`
  have hαsat := (e bs (by simp [hbs]; omega) k nd hnd _ p hp).mpr hβsat
  rw [hsem α hα0] at hαsat
  obtain ⟨U, hU, hall⟩ := hαsat
  refine ⟨U, hU, (hall (fun _ => 0) fun _ _ => hα0).1, fun i hi m hm hlab => ?_⟩
  refine ⟨hU i hi, (lev_iff (by omega)).mpr ⟨(hU i hi).le, elem_cofinal_gen (hU i hi) fun z hz => ?_⟩⟩
  have hz' : max z (U i) < α := max_lt hz (hU i hi)
  -- a point `v` above `max z (U i)` with `Φ_{n-1}(v)` below `α`
  obtain ⟨v, hzv, hvα, hphi, hvtop⟩ : ∃ v, max z (U i) < v ∧ v < α ∧ Phi N α (n - 1) v ∧
      (2 ≤ n → lev N (n - 2) v α) := by
    rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
    · exact ⟨Order.succ (max z (U i)), Order.lt_succ _, hαlim _ hz', trivial, fun h => by omega⟩
    · have h' : lab N (n - 2 + 1) α β := by rw [show n - 2 + 1 = n - 1 by omega]; exact lab_mono (by omega) h
      obtain ⟨v, hzv, hvα, hv⟩ := cof_of_lab (n - 2) h' (n - 2) le_rfl _ hz'
      have hphi : Phi N α (n - 2 + 1) v := phi_of_lev hvα hv fun i' hi' => cof_of_lab (n - 2) h' i' (by omega)
      exact ⟨v, hzv, hvα, by rwa [show n - 2 + 1 = n - 1 by omega] at hphi, fun _ => hv⟩
  have hUv : U i ≤ v := (le_max_right _ _).trans hzv.le
  have hcl := ((hall (fun _ => v) fun _ _ => hvα).2 i hi)
  have hlev : lev N m (U i) v := by
    rcases hcl with (hc | hc) | hc
    · exact absurd hUv hc
    · exact hc m hm hlab
    · exact absurd hphi hc
  refine ⟨v, (le_max_left _ _).trans_lt hzv, hvα, hUv, ((lev_iff (by omega)).mp hlev).2, ?_⟩
  rcases (by omega : m = 0 ∨ 1 ≤ m) with rfl | hm1
  · exact elem_zero
  · have h2 : 2 ≤ n := by omega
    exact elem_of_lev (hvtop h2) (by omega)

/-! ### The label system for any number of rows -/

/-- R_N as a label system for arrays with `N` rows. -/
noncomputable def labelSystemGen (N : ℕ) : BM4.LabelSystem.{1} N where
  Lab := Ordinal.{0}
  rel := lab N
  rel_lt := fun h => h.1
  rel_trans := lab_trans
  reflect := by
    intro n α β hn hrel X hX s y hs hy hyge hylt
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · obtain ⟨y', hy'lt, hsame⟩ := reflect_zero hrel hX hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      exact ⟨y', h1, hy'lt, h2, fun x hx i hi k _ => h3 x hx i hi k,
        fun i j hi hj k _ => h4 i j hi hj k, fun _ _ m hm => absurd hm (by omega)⟩
    · obtain ⟨y', hy'lt, hsame, htop⟩ := reflect_gen hn1 hrel hX hs hylt
      obtain ⟨h1, h2, h3, h4⟩ := copy_props hX hs hyge hsame hy
      exact ⟨y', h1, hy'lt, h2, fun x hx i hi k _ => h3 x hx i hi k,
        fun i j hi hj k _ => h4 i j hi hj k, fun i hi m hm hr => htop i hi m hm hr⟩

end Pat
