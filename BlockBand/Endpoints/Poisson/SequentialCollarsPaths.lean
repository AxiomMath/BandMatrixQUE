module

public import BlockBand.Endpoints.Poisson.SequentialCollarsLaw

/-!
# Sequential collar removal: old components are Gaussian paths

Items (i) and (iii) of the sequential collars lemma. Item (i), second clause ("every old
component incident to it is a Gaussian path", Steps 2–3 of the proof). A run
`p₀, …, p₀+r-1` of an old network (`IsOldRun`: avoids the collars of `S ∪ {k}`, consecutive
bonds, bonds only from its left neighbour) is shown to be a Gaussian path:

* `IsOldRun.interior`: on its sites the stage matrix is the `pathMatrix` of
  `runSample p₀ r ω` minus `e`, plus the diagonal source;
* `IsOldRun.ports`: its couplings to the end ports `p₀ - 1`, `runRight` are
  `pathPortCoupling` (port `0` bond `B_{p₀-1}ᴴ`, port `1` bond `B_{p₀+r-1}`);
* `IsOldRun.decoupled`: it couples to no other site (a connected component);
* `hasLaw_runSample`: under the original prior the run sample has the law
  `Layers.pathLaw W r b` (uses `ginibre_map_conjTranspose`: `Gin(t)` is `ᴴ`-invariant);
* `IsOldRun.indepFun_freshCollar`: it is independent of the fresh collar.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathLaw pathMatrix pathPortCoupling)

section Paths

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

variable (L s) in
/-- Position `p` belongs to one of the collars in `T`. -/
def InCollars (T : Finset (Fin m)) (p : ZMod n) : Prop := ∃ j ∈ T, InCollar L s j p

variable (L s) in
/-- A run of `r` consecutive block positions `p₀, …, p₀+r-1` of the old network at stage
`(π, S)` with selected collar `k`, which avoids the collars in `S ∪ {k}`, carries the pairing's
bonds between consecutive positions, receives bonds only from its left neighbour, and whose left
neighbour bonds into it. -/
structure IsOldRun (π : Pairing) (S : Finset (Fin m)) (k : Fin m) (p₀ : ZMod n) (r : ℕ) : Prop where
  one_le : 1 ≤ r
  lt : r + 1 < n
  avoid : ∀ j < r, ¬ InCollars L s (insert k S) (p₀ + (j : ℕ))
  succ : ∀ j, j + 1 < r → bondTarget L s π (p₀ + (j : ℕ)) = p₀ + ((j + 1 : ℕ) : ZMod n)
  pred : ∀ q, ∀ j < r, bondTarget L s π q = p₀ + (j : ℕ) → q + 1 = p₀ + (j : ℕ)
  left : bondTarget L s π (p₀ - 1) = p₀
  ends_ne : bondTarget L s π (p₀ + ((r - 1 : ℕ) : ZMod n)) ≠ p₀ - 1

variable (L s) in
/-- The right end `q_R` (bond target of the last position). -/
def runRight (π : Pairing) (p₀ : ZMod n) (r : ℕ) : ZMod n :=
  bondTarget L s π (p₀ + ((r - 1 : ℕ) : ZMod n))

/-- The Gaussian path read along a run: blocks `A_{p₀+i}`, internal bonds `B_{p₀+i}`,
port `0` (left) bond `B_{p₀-1}ᴴ`, port `1` (right) bond `B_{p₀+r-1}`. -/
def runSample (p₀ : ZMod n) (r : ℕ) (ω : RingCoords n W) : PathSample W r :=
  (fun i => ω.1 (p₀ + (i.val : ℕ)), fun i => ω.2 (p₀ + (i.val : ℕ)),
    ![(ω.2 (p₀ - 1))ᴴ, ω.2 (p₀ + ((r - 1 : ℕ) : ZMod n))])

theorem add_natCast_inj {p₀ : ZMod n} {i j : ℕ} (hi : i < n) (hj : j < n) :
    p₀ + (i : ZMod n) = p₀ + (j : ZMod n) ↔ i = j := by
  constructor
  · intro h
    have h1 := add_left_cancel h
    rw [ZMod.natCast_eq_natCast_iff' _ _ n, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h1
    exact h1
  · rintro rfl; rfl

theorem sub_one_eq_add {p₀ : ZMod n} (hn : 1 ≤ n) : p₀ - 1 = p₀ + ((n - 1 : ℕ) : ZMod n) := by
  have : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub hn, ZMod.natCast_self]; simp
  rw [this, sub_eq_add_neg]

variable (L s) in
/-- Sites of a run, in path coordinates. -/
abbrev runSite (p₀ : ZMod n) {r : ℕ} (x : Fin r × Fin W) : RingSite n W := (p₀ + (x.1.val : ℕ), x.2)

variable (L s) in
/-- The two end ports of a run: `p₀ - 1` (port `0`) and `q_R` (port `1`). -/
abbrev runPortSite (π : Pairing) (p₀ : ZMod n) (r : ℕ) (x : Fin 2 × Fin W) : RingSite n W :=
  (if x.1 = 0 then p₀ - 1 else runRight L s π p₀ r, x.2)

namespace IsOldRun

variable {π : Pairing} {S : Finset (Fin m)} {k : Fin m} {p₀ : ZMod n} {r : ℕ}

theorem pos_inj (h : IsOldRun L s π S k p₀ r) {i j : ℕ} (hi : i ≤ r) (hj : j ≤ r) :
    p₀ + (i : ZMod n) = p₀ + (j : ZMod n) ↔ i = j :=
  add_natCast_inj (by have := h.lt; omega) (by have := h.lt; omega)

theorem sub_one_ne (h : IsOldRun L s π S k p₀ r) {j : ℕ} (hj : j < r) :
    p₀ - 1 ≠ p₀ + (j : ZMod n) := by
  rw [sub_one_eq_add (by have := h.lt; omega)]
  intro he
  have := (add_natCast_inj (p₀ := p₀) (by have := h.lt; omega) (by have := h.lt; omega)).mp he
  have := h.lt; omega

theorem target_in_run (h : IsOldRun L s π S k p₀ r) {i j : ℕ} (hi : i < r) (hj : j < r) :
    bondTarget L s π (p₀ + (i : ℕ)) = p₀ + (j : ℕ) ↔ j = i + 1 := by
  constructor
  · intro he
    have h1 := h.pred _ j hj he
    rw [add_assoc, show ((i : ZMod n) + 1) = ((i + 1 : ℕ) : ZMod n) by push_cast; ring] at h1
    have := (h.pos_inj (i := i + 1) (j := j) (by omega) (by omega)).mp h1
    omega
  · rintro rfl
    exact h.succ i hj

theorem right_ne_run (h : IsOldRun L s π S k p₀ r) {j : ℕ} (hj : j < r) :
    runRight L s π p₀ r ≠ p₀ + (j : ℕ) := by
  intro he
  have := (h.target_in_run (i := r - 1) (j := j) (by have := h.one_le; omega) hj).mp he
  have := h.one_le; omega

theorem target_of_lt (h : IsOldRun L s π S k p₀ r) {i : ℕ} (hi : i < r) :
    bondTarget L s π (p₀ + (i : ℕ)) = runRight L s π p₀ r ∨
      (i + 1 < r ∧ bondTarget L s π (p₀ + (i : ℕ)) = p₀ + ((i + 1 : ℕ) : ZMod n)) := by
  by_cases hi' : i + 1 < r
  · exact Or.inr ⟨hi', h.succ i hi'⟩
  · left
    have : i = r - 1 := by omega
    subst this; rfl

theorem not_matched (h : IsOldRun L s π S k p₀ r) {j : ℕ} (hj : j < r) :
    ¬ IsMatched L s S (p₀ + (j : ℕ)) := by
  rintro ⟨i, hi, he | he⟩
  · exact h.avoid j hj ⟨i, Finset.mem_insert_of_mem hi, Or.inl he⟩
  · exact h.avoid j hj ⟨i, Finset.mem_insert_of_mem hi, Or.inr (Or.inr he)⟩

theorem not_deleted (h : IsOldRun L s π S k p₀ r) {j : ℕ} (hj : j < r) :
    ¬ IsDeleted L s S (p₀ + (j : ℕ)) := by
  rintro ⟨i, hi, he⟩
  exact h.avoid j hj ⟨i, Finset.mem_insert_of_mem hi, Or.inr (Or.inl he)⟩

theorem not_inCollar (h : IsOldRun L s π S k p₀ r) {j : ℕ} (hj : j < r) :
    ¬ InCollar L s k (p₀ + (j : ℕ)) :=
  fun hc => h.avoid j hj ⟨k, Finset.mem_insert_self _ _, hc⟩

/-- On its own sites the old network is the path matrix of the run sample, shifted by `-e`
and with the (diagonal) source. -/
theorem interior (h : IsOldRun L s π S k p₀ r) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    (stageFull L s π S e z buf κ ω).submatrix (runSite p₀) (runSite p₀) =
      pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1 +
        diagonal fun x : Fin r × Fin W =>
          ((stageAbsorption L s S buf κ z.im W (p₀ + (x.1.val : ℕ)) : ℝ) : ℂ) * Complex.I := by
  ext ⟨i, a⟩ ⟨i', b⟩
  have hi := i.isLt
  have hi' := i'.isLt
  have hm := h.not_matched hi
  simp only [submatrix_apply, stageFull, stageHerm, Matrix.add_apply, Matrix.sub_apply,
    diagonal_apply, pathMatrix, runSample, Matrix.smul_apply, one_apply, Prod.mk.injEq,
    smul_eq_mul]
  have hpos : p₀ + ((i : ℕ) : ZMod n) = p₀ + ((i' : ℕ) : ZMod n) ↔ i = i' := by
    rw [h.pos_inj hi.le hi'.le, Fin.val_inj]
  have hb1 := h.target_in_run hi hi'
  have hb2 := h.target_in_run hi' hi
  by_cases hii : i = i'
  · subst hii
    have hn1 : ¬ ((i : ℕ) = i + 1) := by omega
    simp only [ite_true, hm, ite_false, hb1, hn1, true_and]
    split_ifs <;> ring
  · have hpos' : ¬ p₀ + ((i : ℕ) : ZMod n) = p₀ + ((i' : ℕ) : ZMod n) := fun he => hii (hpos.mp he)
    have hv : ¬ (i : ℕ) = i' := fun he => hii (Fin.ext he)
    simp only [hpos', hii, ite_false, false_and, zero_add, add_zero, mul_zero, sub_zero, hb1, hb2]
    split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- A run is a component: its sites couple to no site outside the run except its two end
ports `p₀ - 1` and `q_R`. -/
theorem decoupled (h : IsOldRun L s π S k p₀ r) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) (x : Fin r × Fin W) (y : RingSite n W)
    (hy : ∀ j < r, y.1 ≠ p₀ + (j : ℕ)) (hyl : y.1 ≠ p₀ - 1) (hyr : y.1 ≠ runRight L s π p₀ r) :
    stageFull L s π S e z buf κ ω (runSite p₀ x) y = 0 ∧
      stageFull L s π S e z buf κ ω y (runSite p₀ x) = 0 := by
  obtain ⟨⟨i, hi⟩, a⟩ := x
  have hne : (p₀ + (i : ℕ)) ≠ y.1 := fun he => hy i hi he.symm
  have hxy : runSite p₀ (W := W) (⟨i, hi⟩, a) ≠ y := fun he => hne (congrArg Prod.fst he)
  have hb1 : bondTarget L s π (p₀ + (i : ℕ)) ≠ y.1 := by
    rcases h.target_of_lt hi with he | ⟨hi', he⟩
    · rw [he]; exact fun e' => hyr e'.symm
    · rw [he]; exact fun e' => hy (i + 1) hi' e'.symm
  have hb2 : bondTarget L s π y.1 ≠ p₀ + (i : ℕ) := by
    intro he
    have h1 := h.pred y.1 i hi he
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      apply hyl
      simp only [Nat.cast_zero, add_zero] at h1
      rw [← h1]; ring
    · apply hy (i - 1) (by omega)
      have : p₀ + ((i : ℕ) : ZMod n) = p₀ + ((i - 1 : ℕ) : ZMod n) + 1 := by
        rw [Nat.cast_sub (by omega)]; ring
      rw [this] at h1
      exact add_right_cancel h1
  constructor
  · simp [stageFull, stageHerm, hne, hxy, hb1, hb2]
  · simp [stageFull, stageHerm, Ne.symm hne, Ne.symm hxy, hb1, hb2]

/-- The couplings of the run to its two end ports are the port bonds of the run sample. -/
theorem ports (h : IsOldRun L s π S k p₀ r) (e : ℝ) (z : ℂ) (buf : ℕ) (κ : ℝ)
    (ω : RingCoords n W) :
    (stageFull L s π S e z buf κ ω).submatrix (runSite p₀) (runPortSite L s π p₀ r) =
      pathPortCoupling (runSample p₀ r ω) := by
  ext ⟨⟨i, hi⟩, a⟩ ⟨c, b⟩
  have hl := h.sub_one_ne hi
  have hr := h.right_ne_run hi
  fin_cases c
  · -- left port `p₀ - 1`
    have hb1 : bondTarget L s π (p₀ + (i : ℕ)) ≠ p₀ - 1 := by
      rcases h.target_of_lt hi with he | ⟨hi', he⟩
      · rw [he]; exact h.ends_ne
      · rw [he]; exact (h.sub_one_ne hi').symm
    have hb2 : bondTarget L s π (p₀ - 1) = p₀ + (i : ℕ) ↔ i = 0 := by
      rw [h.left]
      constructor
      · intro he
        have := (h.pos_inj (i := 0) (j := i) (by omega) hi.le).mp (by simpa using he)
        omega
      · rintro rfl; simp
    simp only [submatrix_apply, stageFull, stageHerm, Matrix.add_apply, diagonal_apply,
      pathPortCoupling, runSample, runPortSite, Fin.zero_eta, ite_true, Prod.mk.injEq]
    simp only [Ne.symm hl, hb1, hb2, ite_false, false_and, zero_add, add_zero, true_and]
    by_cases h0 : i = 0
    · simp [h0, conjTranspose_apply]
    · simp [h0]
  · -- right port `q_R`
    have hb1 : bondTarget L s π (p₀ + (i : ℕ)) = runRight L s π p₀ r ↔ i + 1 = r := by
      constructor
      · intro he
        by_contra hne
        have hi' : i + 1 < r := by omega
        rw [h.succ i hi'] at he
        exact h.right_ne_run hi' he.symm
      · intro he
        have : i = r - 1 := by omega
        subst this; rfl
    have hb2 : bondTarget L s π (runRight L s π p₀ r) ≠ p₀ + (i : ℕ) := by
      intro he
      have h1 := h.pred _ i hi he
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        apply h.ends_ne
        simp only [Nat.cast_zero, add_zero] at h1
        exact eq_sub_of_add_eq h1
      · apply h.right_ne_run (j := i - 1) (by omega)
        have : p₀ + ((i : ℕ) : ZMod n) = p₀ + ((i - 1 : ℕ) : ZMod n) + 1 := by
          rw [Nat.cast_sub (by omega)]; ring
        rw [this] at h1
        exact add_right_cancel h1
    have hone : (1 : Fin 2) ≠ 0 := by decide
    simp only [submatrix_apply, stageFull, stageHerm, Matrix.add_apply, diagonal_apply,
      pathPortCoupling, runSample, runPortSite, Prod.mk.injEq]
    simp only [show ((⟨1, by norm_num⟩ : Fin 2) = 0) = False from by simp, ite_false]
    simp only [Ne.symm hr, hb2, ite_false, false_and, add_zero, zero_add, hb1]
    by_cases hlast : i + 1 = r
    · have : i = r - 1 := by omega
      subst this
      simp [hlast]
    · simp [hlast]

end IsOldRun

/-!
### The law of a run sample
-/

open BlockBand.Internal.Contracts.Layers (ginibreMeasure)

theorem measurable_conjTranspose' {ι : Type*} :
    Measurable (fun M : Matrix ι ι ℂ => Mᴴ) :=
  Measurable.of_eval_matrix _ fun x y =>
    continuous_star.measurable.comp (Matrix.measurable_apply (i := y) (j := x))

/-- The Ginibre law is invariant under `B ↦ Bᴴ`. -/
theorem ginibre_map_conjTranspose (W : ℕ) (t : NNReal) :
    (ginibreMeasure (Fin W) (Fin W) t).map (fun M => Mᴴ) = ginibreMeasure (Fin W) (Fin W) t := by
  set g : Fin W × Fin W × Fin 2 → Measure ℝ := fun _ => gaussianReal 0 (t / 2)
  set G : (Fin W × Fin W × Fin 2 → ℝ) → Matrix (Fin W) (Fin W) ℂ :=
    fun r => Matrix.of fun x y => (r (x, y, 0) : ℂ) + (r (x, y, 1) : ℂ) * Complex.I
  set σ : Fin W × Fin W × Fin 2 → Fin W × Fin W × Fin 2 := fun i => (i.2.1, i.1, i.2.2)
  set f : Fin W × Fin W × Fin 2 → ℝ → ℝ := fun i => if i.2.2 = 0 then id else fun u => -u
  set T : (Fin W × Fin W × Fin 2 → ℝ) → (Fin W × Fin W × Fin 2 → ℝ) := fun r i => f i (r (σ i))
  have hG : Measurable G := Measurable.of_eval_matrix _ fun x y => by
    simp only [G, Matrix.of_apply]
    exact (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
      ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)
  have hf : ∀ i, Measurable (f i) := fun i => by
    simp only [f]; split_ifs
    · exact measurable_id
    · exact measurable_neg
  have hσ : Function.Injective σ := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [σ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    rw [h1, h2, h3]
  have hT : MeasurePreserving T (Measure.pi g) (Measure.pi g) := by
    have hI : iIndepFun (fun i (r : Fin W × Fin W × Fin 2 → ℝ) => f i (r (σ i)))
        (Measure.pi g) := by
      have h0 := iIndepFun_pi (μ := g) (X := fun _ => id) (fun _ => aemeasurable_id)
      exact (h0.precomp hσ).comp (fun i => f i) hf
    have hm : ∀ i, HasLaw (fun r : Fin W × Fin W × Fin 2 → ℝ => f i (r (σ i))) (g i)
        (Measure.pi g) := by
      intro i
      have hev := (measurePreserving_eval g (σ i)).hasLaw
      refine ⟨((hf i).comp (measurable_pi_apply _)).aemeasurable, ?_⟩
      rw [show (fun r : Fin W × Fin W × Fin 2 → ℝ => f i (r (σ i))) =
          f i ∘ Function.eval (σ i) from rfl,
        ← Measure.map_map (hf i) (measurable_pi_apply _), hev.map_eq]
      simp only [f, g]
      split_ifs
      · exact Measure.map_id
      · rw [gaussianReal_map_neg, neg_zero]
    exact ((iIndepFun_iff_hasLaw_pi_pi hm).mp hI).measurePreserving
      (measurable_pi_iff.mpr fun i => (hf i).comp (measurable_pi_apply _))
  have hcomm : (fun M : Matrix (Fin W) (Fin W) ℂ => Mᴴ) ∘ G = G ∘ T := by
    funext r
    ext x y
    simp only [Function.comp_apply, conjTranspose_apply, G, T, f, σ, Matrix.of_apply]
    simp
  unfold ginibreMeasure
  rw [Measure.map_map measurable_conjTranspose' hG, hcomm, ← Measure.map_map hG hT.measurable,
    hT.map_eq]

/-- The coordinates read by a run sample. -/
def runIdx (p₀ : ZMod n) (r : ℕ) : Fin r ⊕ (Fin (r - 1) ⊕ Fin 2) → ZMod n ⊕ ZMod n
  | Sum.inl i => Sum.inl (p₀ + (i.val : ℕ))
  | Sum.inr (Sum.inl j) => Sum.inr (p₀ + (j.val : ℕ))
  | Sum.inr (Sum.inr c) => Sum.inr (if c = 0 then p₀ - 1 else p₀ + ((r - 1 : ℕ) : ZMod n))

theorem runIdx_injective {p₀ : ZMod n} {r : ℕ} (h1 : 1 ≤ r) (hr : r < n) :
    Function.Injective (runIdx p₀ r) := by
  have hl : ∀ j : ℕ, j < r → p₀ - 1 ≠ p₀ + (j : ZMod n) := by
    intro j hj he
    rw [sub_one_eq_add (by omega)] at he
    have := (add_natCast_inj (p₀ := p₀) (by omega) (by omega)).mp he
    omega
  have hlast : p₀ - 1 ≠ p₀ + ((r - 1 : ℕ) : ZMod n) := hl (r - 1) (by omega)
  rintro (i | j | c) (i' | j' | c') h <;>
    simp only [runIdx, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
  · exact congrArg Sum.inl (Fin.ext ((add_natCast_inj (by omega) (by omega)).mp h))
  · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext ((add_natCast_inj (by omega) (by omega)).mp h))
  · exfalso
    split_ifs at h
    · exact hl j (by omega) h.symm
    · have := (add_natCast_inj (p₀ := p₀) (by omega) (by omega)).mp h; omega
  · exfalso
    split_ifs at h
    · exact hl j' (by omega) h
    · have := (add_natCast_inj (p₀ := p₀) (by omega) (by omega)).mp h; omega
  · congr 2
    split_ifs at h with h1 h2 h2
    · rw [h1, h2]
    · exact absurd h hlast
    · exact absurd h.symm hlast
    · exact (Fin.eq_one_of_ne_zero c h1).trans (Fin.eq_one_of_ne_zero c' h2).symm

/-- `![Bᴴ, B']` on the two port bonds. -/
def portMap (v : Fin 2 → Matrix (Fin W) (Fin W) ℂ) : Fin 2 → Matrix (Fin W) (Fin W) ℂ :=
  fun c => if c = 0 then (v c)ᴴ else v c

theorem measurePreserving_portMap (b : ℝ) :
    MeasurePreserving (portMap (W := W)) (Measure.pi fun _ : Fin 2 => ginBondLaw W b)
      (Measure.pi fun _ : Fin 2 => ginBondLaw W b) := by
  have : (portMap (W := W)) = fun v c =>
      (fun c (M : Matrix (Fin W) (Fin W) ℂ) => if c = 0 then Mᴴ else M) c (v c) := by
    funext v c; simp only [portMap]
  rw [this]
  refine measurePreserving_pi (fun _ : Fin 2 => ginBondLaw W b) (fun _ : Fin 2 => ginBondLaw W b)
    (f := fun c (M : Matrix (Fin W) (Fin W) ℂ) => if c = 0 then Mᴴ else M) fun c => ?_
  by_cases hc : c = 0
  · simp only [hc, ite_true]
    exact ⟨measurable_conjTranspose', ginibre_map_conjTranspose W _⟩
  · simp only [hc, ite_false]
    exact MeasurePreserving.id _

/-- The run sample of any run of length `r < n` is a Gaussian path: it has the law
`pathLaw W r b` under the original prior. -/
theorem hasLaw_runSample [NeZero n] (p₀ : ZMod n) {r : ℕ} (h1 : 1 ≤ r) (hr : r < n) (b : ℝ) :
    HasLaw (runSample (W := W) p₀ r) (pathLaw W r b) (ringCoordLaw n W b) := by
  obtain ⟨hI, hm⟩ := iIndepFun_ringCoord (n := n) (W := W) b
  have hv : HasLaw (fun ω j => ringCoord (W := W) (runIdx p₀ r j) ω)
      (Measure.pi fun j => ringCoordMarginal W b (runIdx p₀ r j)) (ringCoordLaw n W b) :=
    (hI.precomp (runIdx_injective h1 hr)).hasLaw_pi fun j => hm _
  have e1 := measurePreserving_sumPiEquivProdPi
    (fun j : Fin r ⊕ (Fin (r - 1) ⊕ Fin 2) => ringCoordMarginal (n := n) W b (runIdx p₀ r j))
  have e2 := measurePreserving_sumPiEquivProdPi
    (fun j : Fin (r - 1) ⊕ Fin 2 => ringCoordMarginal (n := n) W b (runIdx p₀ r (Sum.inr j)))
  have e3 := (MeasurePreserving.id (Measure.pi fun _ : Fin r => gueBlockLaw W b)).prod
    ((MeasurePreserving.id (Measure.pi fun _ : Fin (r - 1) => ginBondLaw W b)).prod
      (measurePreserving_portMap (W := W) b))
  have e4 := (MeasurePreserving.id (Measure.pi fun _ : Fin r => gueBlockLaw W b)).prod e2
  have hchain := (e3.comp e4).comp e1
  have := hchain.comp_hasLaw hv
  have heq : runSample (W := W) p₀ r = (Prod.map id (Prod.map id portMap) ∘
      Prod.map id (MeasurableEquiv.sumPiEquivProdPi _) ∘ MeasurableEquiv.sumPiEquivProdPi _) ∘
      (fun ω j => ringCoord (W := W) (runIdx p₀ r j) ω) := by
    funext ω
    simp only [runSample, Function.comp_apply, Prod.map]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext c
    fin_cases c <;> rfl
  rw [heq]
  exact this

theorem measurable_runSample (p₀ : ZMod n) (r : ℕ) : Measurable (runSample (W := W) p₀ r) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
  · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_snd
  · refine Measurable.of_eval fun c => ?_
    fin_cases c
    · exact measurable_conjTranspose'.comp ((measurable_pi_apply _).comp measurable_snd)
    · show Measurable fun ω : RingCoords n W => ω.2 (p₀ + ((r - 1 : ℕ) : ZMod n))
      exact (measurable_pi_apply _).comp measurable_snd

/-- The run sample is a function of the old coordinates only. -/
theorem IsOldRun.runSample_congr [NeZero n] (hL : IsCollarLayout n L) {π : Pairing}
    {S : Finset (Fin m)} {k : Fin m} {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r)
    {ω ω' : RingCoords n W} (hω : oldCoords L s k ω = oldCoords L s k ω') :
    runSample p₀ r ω = runSample p₀ r ω' := by
  have hA : ∀ p, ¬ InCollar L s k p → ω.1 p = ω'.1 p := fun p hp =>
    congrFun hω ⟨Sum.inl p, (mem_oldCoordSet_inl k p).mpr hp⟩
  have hB : ∀ p, ¬ (p = unitPos n L s k 0 ∨ p = unitPos n L s k 1) → ω.2 p = ω'.2 p :=
    fun p hp => congrFun hω ⟨Sum.inr p, (mem_oldCoordSet_inr k p).mpr hp⟩
  have hrun : ∀ j < r, ¬ (p₀ + (j : ZMod n) = unitPos n L s k 0 ∨
      p₀ + (j : ZMod n) = unitPos n L s k 1) := fun j hj hc =>
    h.not_inCollar hj (hc.elim Or.inl fun e => Or.inr (Or.inl e))
  have hleft : ¬ (p₀ - 1 = unitPos n L s k 0 ∨ p₀ - 1 = unitPos n L s k 1) := by
    rintro (he | he)
    · have := h.left
      rw [he, bondTarget_collar hL π k (by norm_num)] at this
      exact h.not_inCollar (j := 0) h.one_le (by simp [← this]; exact Or.inr (Or.inl rfl))
    · have := h.left
      rw [he, bondTarget_collar hL π k (by norm_num)] at this
      exact h.not_inCollar (j := 0) h.one_le (by simp [← this]; exact Or.inr (Or.inr rfl))
  simp only [runSample]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; exact hA _ (h.not_inCollar i.isLt)
  · funext i; exact hB _ (hrun i (by have := i.isLt; omega))
  · funext c
    fin_cases c
    · simp [hB _ hleft]
    · simp [hB _ (hrun (r - 1) (by have := h.one_le; omega))]

/-- Item (i): the fresh collar is independent of every incident old path. -/
theorem IsOldRun.indepFun_freshCollar [NeZero n] (hL : IsCollarLayout n L) {π : Pairing}
    {S : Finset (Fin m)} {k : Fin m} {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r) (b : ℝ) :
    IndepFun (freshCollar L s k) (runSample (W := W) p₀ r) (ringCoordLaw n W b) := by
  have heq : runSample (W := W) p₀ r = (runSample p₀ r ∘ glueOld L s k) ∘ oldCoords L s k := by
    funext ω
    exact h.runSample_congr hL (oldCoords_glueOld k ω).symm
  rw [heq]
  exact (indepFun_freshCollar_oldCoords k b).comp measurable_id
    ((measurable_runSample p₀ r).comp (measurable_glueOld k))

end Paths

end BlockBand.Endpoints
