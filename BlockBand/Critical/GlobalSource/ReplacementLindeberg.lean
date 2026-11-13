module

public import BlockBand.Critical.GlobalSource.ReplacementPath

/-!
# Global Gaussian source, source replacement: the Lindeberg telescope

* `lintegral_quadMoment_tag_le`, `quadMoment_gauss_eq`: `E|X^*GX|²` for a swapped tag (from the
  hypothesis `RawTagTwo` = second clause of `rawTagMoments` at `p = 2`) and for a swapped Gaussian
  probe (`= E[|Tr A_r|² + ‖A_r‖²_HS]`, the `p = 2` quantity of `extendedSourceMoments`);
* `lintegral_path_swapRemainder_le`: the expected remainder of one swap is
  `≤ t³(1+2‖u‖)³ stepConst`, uniformly in the width, the path length, the profiles and `M`;
* `hybridChar`, `norm_hybridChar_insert_sub_le`, `norm_hybridChar_univ_sub_empty_le`: the
  `J·M` replacements telescope to `2J(1+2‖u‖)³ stepConst / √M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Quad
variable {W L : ℕ}

theorem measurable_quad_form {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G)
    (lam : Fin L × Fin W → ℝ) :
    Measurable fun x : Ω × (Fin L × Fin W → ℂ) =>
      ENNReal.ofReal (‖star (weightVec lam x.2) ⬝ᵥ (G x.1 *ᵥ weightVec lam x.2)‖ ^ 2) := by
  have hG' : ∀ y z, Measurable fun x : Ω × (Fin L × Fin W → ℂ) => G x.1 y z :=
    fun y z => (measurable_pi_apply z).comp ((measurable_pi_apply y).comp (hG.comp measurable_fst))
  refine ENNReal.measurable_ofReal.comp ((Measurable.norm ?_).pow_const 2)
  unfold dotProduct Matrix.mulVec dotProduct weightVec
  refine Finset.measurable_sum _ fun y _ => Measurable.mul ?_ (Finset.measurable_sum _ fun z _ =>
    (hG' y z).mul ?_)
  · exact (continuous_star.measurable).comp (measurable_const.mul
      ((measurable_pi_apply _).comp measurable_snd))
  · exact measurable_const.mul ((measurable_pi_apply _).comp measurable_snd)

theorem measurable_tag_quad {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G) (k : Fin L) (m : ℝ) :
    Measurable fun x : Ω × (Fin W → ℂ) =>
      ENNReal.ofReal (‖star (tagVector W L k m x.2) ⬝ᵥ (G x.1 *ᵥ tagVector W L k m x.2)‖ ^ 2) := by
  simp_rw [tagVector_eq]
  have hG' : ∀ y z, Measurable fun x : Ω × (Fin W → ℂ) => G x.1 y z :=
    fun y z => (measurable_pi_apply z).comp ((measurable_pi_apply y).comp (hG.comp measurable_fst))
  refine ENNReal.measurable_ofReal.comp ((Measurable.norm ?_).pow_const 2)
  unfold dotProduct Matrix.mulVec dotProduct
  refine Finset.measurable_sum _ fun y _ => Measurable.mul ?_ (Finset.measurable_sum _ fun z _ =>
    (hG' y z).mul ?_)
  · exact (continuous_star.measurable).comp (measurable_const.mul
      ((measurable_pi_apply _).comp measurable_snd))
  · exact measurable_const.mul ((measurable_pi_apply _).comp measurable_snd)

theorem measurable_tag_quad_fixed (G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ) (k : Fin L)
    (m : ℝ) : Measurable fun g : Fin W → ℂ =>
      ENNReal.ofReal (‖star (tagVector W L k m g) ⬝ᵥ (G *ᵥ tagVector W L k m g)‖ ^ 2) := by
  simp_rw [tagVector_eq]
  refine ENNReal.measurable_ofReal.comp ((Measurable.norm ?_).pow_const 2)
  unfold dotProduct Matrix.mulVec dotProduct
  refine Finset.measurable_sum _ fun y _ => Measurable.mul ?_ (Finset.measurable_sum _ fun z _ =>
    measurable_const.mul ?_)
  · exact (continuous_star.measurable).comp (measurable_const.mul (measurable_pi_apply _))
  · exact measurable_const.mul (measurable_pi_apply _)

/-- The raw tag hypothesis of `ComplexSourceLawContract.rawTagMoments` (`p = 2`, same tag). -/
def RawTagTwo (b E : ℝ) (W L : ℕ) (C : ℝ) : Prop :=
  ∀ (k : Fin L) (m : ℝ), 0 ≤ m →
    ∫⁻ x, ENNReal.ofReal (‖star (tagVector W L k m x.2) ⬝ᵥ
        ((fullInverse b E W L x.1).toBlocks₁₁ *ᵥ tagVector W L k m x.2)‖ ^ (2 : ℝ))
      ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) ≤
      ENNReal.ofReal (C * (m * m) ^ ((2 : ℝ) / 2))

theorem sum_blockLaw_mul_const {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (c : ℝ≥0∞) :
    ∑ o, (discreteBlockLaw W L r) {o} * c = c := by
  have := isProbabilityMeasure_discreteBlockLaw (W := W) hr
  rw [← Finset.sum_mul, sum_measure_singleton, Finset.coe_univ, measure_univ, one_mul]

/-- **Tag case of the quadratic moment** (from `rawTagMoments`, `p = 2`). -/
theorem lintegral_quadMoment_tag_le {b E C : ℝ} (hraw : RawTagTwo b E W L C) {r : Fin L → ℝ}
    (hr : ∀ k, 0 ≤ r k) {μ : ℝ} (hμ : profileMass W L r ≤ μ) :
    ∫⁻ ω, quadMoment W L r (leadG b E W L ω) (tagWeight W L (profileMass W L r))
        ∂growthPathLaw W b ≤ ENNReal.ofReal (max C 0 * μ ^ 2) := by
  have hm := profileMass_nonneg (W := W) hr
  set m := profileMass W L r
  have hT : ∀ ω, quadMoment W L r (leadG b E W L ω) (tagWeight W L m) =
      ∑ o, (discreteBlockLaw W L r) {o} * ∫⁻ h, ENNReal.ofReal
        (‖star (weightVec (tagWeight W L m o) h) ⬝ᵥ
          (leadG b E W L ω *ᵥ weightVec (tagWeight W L m o) h)‖ ^ 2) ∂circularVectorLaw _ := by
    intro ω
    unfold quadMoment
    rw [lintegral_slotLaw (measurable_swapQ _ _)]
    rfl
  simp_rw [hT]
  have hmeas : ∀ o, Measurable fun ω => ∫⁻ h, ENNReal.ofReal
      (‖star (weightVec (tagWeight W L m o) h) ⬝ᵥ
        (leadG b E W L ω *ᵥ weightVec (tagWeight W L m o) h)‖ ^ 2) ∂circularVectorLaw _ :=
    fun o => (measurable_quad_form (measurable_leadG b E W L) _).lintegral_prod_right'
  rw [lintegral_finsetSum _ fun o _ => (hmeas o).const_mul _]
  simp_rw [lintegral_const_mul _ (hmeas _)]
  have hbo : ∀ o, ∫⁻ ω, ∫⁻ h, ENNReal.ofReal
      (‖star (weightVec (tagWeight W L m o) h) ⬝ᵥ
        (leadG b E W L ω *ᵥ weightVec (tagWeight W L m o) h)‖ ^ 2) ∂circularVectorLaw _
        ∂growthPathLaw W b ≤ ENNReal.ofReal (max C 0 * μ ^ 2) := by
    intro o
    induction o using Fin.lastCases with
    | last =>
      have h0 : ∀ h : Fin L × Fin W → ℂ, weightVec (tagWeight W L m (Fin.last L)) h = 0 := by
        intro h; funext x; simp [weightVec, tagWeight_last]
      simp [h0]
    | cast k =>
      simp_rw [weightVec_tagWeight_castSucc]
      have hrow : ∀ ω, ∫⁻ h, ENNReal.ofReal (‖star (tagVector W L k m fun y => h (k, y)) ⬝ᵥ
          (leadG b E W L ω *ᵥ tagVector W L k m fun y => h (k, y))‖ ^ 2)
            ∂circularVectorLaw (Fin L × Fin W) =
          ∫⁻ g, ENNReal.ofReal (‖star (tagVector W L k m g) ⬝ᵥ
            (leadG b E W L ω *ᵥ tagVector W L k m g)‖ ^ 2) ∂circularVectorLaw (Fin W) := by
        intro ω
        rw [← circularVectorLaw_map_row (α := Fin L) (β := Fin W) k,
          lintegral_map (measurable_tag_quad_fixed _ k m)
          (Measurable.of_eval fun y => measurable_pi_apply (k, y))]
      simp_rw [hrow]
      have hj := measurable_tag_quad (measurable_leadG b E W L) k m
      rw [← lintegral_prod _ hj.aemeasurable]
      have h2 := hraw k m hm
      simp only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Real.rpow_two] at h2
      refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
      calc C * (m * m) ≤ max C 0 * (m * m) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hm hm)
        _ ≤ max C 0 * μ ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            rw [sq]; exact mul_le_mul hμ hμ hm (hm.trans hμ)
  calc ∑ o, (discreteBlockLaw W L r) {o} * ∫⁻ ω, ∫⁻ h, ENNReal.ofReal
        (‖star (weightVec (tagWeight W L m o) h) ⬝ᵥ
          (leadG b E W L ω *ᵥ weightVec (tagWeight W L m o) h)‖ ^ 2) ∂circularVectorLaw _
          ∂growthPathLaw W b
      ≤ ∑ o, (discreteBlockLaw W L r) {o} * ENNReal.ofReal (max C 0 * μ ^ 2) := by
        gcongr with o; exact hbo o
    _ = _ := sum_blockLaw_mul_const hr _

theorem weightMat_gaussWeight (b E : ℝ) (r : Fin L → ℝ) (ω : GrowthPath W) :
    weightMat (gaussWeight W L r) (leadG b E W L ω) = extendedSourceMatrix b E W L r ω := by
  ext x y
  rw [extendedSourceMatrix_apply]
  rfl

/-- **Gaussian case of the quadratic moment**: `E|ζ^*Gζ|² = |Tr A_r|² + ‖A_r‖²_HS`. -/
theorem quadMoment_gauss_eq (b E : ℝ) {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) (ω : GrowthPath W) :
    quadMoment W L r (leadG b E W L ω) (fun _ => gaussWeight W L r) =
      ENNReal.ofReal (sourceMoment2 b E W L r ω) := by
  unfold quadMoment
  rw [lintegral_slotLaw (measurable_swapQ _ _)]
  unfold swapQ
  simp only
  simp_rw [quad_weightVec, lintegral_norm_sq_quadratic, weightMat_gaussWeight]
  rw [sum_blockLaw_mul_const hr]
  rfl

end Quad

section Step
variable {W L J M : ℕ}

theorem continuous_pairFour (r : Fin J → Fin L → ℝ) (b a : Fin J) :
    Continuous fun G : Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ => pairFour W L r G b a := by
  unfold pairFour pairHS; fun_prop

/-- The constant of one swap. -/
def stepConst (J : ℕ) (C₄ C₂ Ce μ : ℝ) : ℝ :=
  5 + 40 * (J : ℝ) ^ 3 * ∑ _b : Fin J, (4 * (max C₄ 0 * μ ^ 4) + 4 * (max C₄ 0 * μ ^ 4)) +
    6 * (max Ce 0 + max C₂ 0 * μ ^ 2)

theorem stepConst_nonneg (J : ℕ) (C₄ C₂ Ce μ : ℝ) : 0 ≤ stepConst J C₄ C₂ Ce μ := by
  unfold stepConst; positivity

/-- **Path average of the remainder of one swap**: the uniform moments bound its expected
absolute value by a constant times `E[‖A‖³+‖C‖³+‖A‖‖C‖+‖C‖²]`. -/
theorem lintegral_path_swapRemainder_le {b E C₄ C₂ Ce : ℝ} (hraw4 : RawTagFour b E W L C₄)
    (hraw2 : RawTagTwo b E W L C₂) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) {μ : ℝ}
    (hμ : ∀ a, profileMass W L (r a) ≤ μ)
    (hext : ∀ a, ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W L (r a) ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal Ce)
    (hM : 0 < M) {Λ₀ : Fin (J * M) → Fin (L + 1) → Fin L × Fin W → ℝ}
    (hΛ : ∀ s, IsSlotWeight W L r s (Λ₀ s)) (j : Fin (J * M)) (lam : Fin (L + 1) → Fin L × Fin W → ℝ)
    (hlam : lam = tagWeight W L (profileMass W L (r (tagGroup j))) ∨
      lam = fun _ => gaussWeight W L (r (tagGroup j)))
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    ∫⁻ ω, ∫⁻ x, ∫⁻ y', swapRemainder (leadG b E W L ω) Λ₀ u j lam x y'
        ∂slotLaw W L (r (tagGroup j)) ∂Measure.pi (slotMeasures W L r) ∂growthPathLaw W b ≤
      ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3 * stepConst J C₄ C₂ Ce μ) := by
  set a := tagGroup j
  set c := ENNReal.ofReal ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3)
  have hpt := fun ω => lintegral_swapRemainder_le hr hM hΛ j lam hlam (leadG b E W L ω) u
  refine (lintegral_mono hpt).trans ?_
  have hP : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hmA : ∀ b' : Fin J, Measurable fun ω =>
      ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω) b' a) := fun b' =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((continuous_pairFour r b' a).measurable.comp (measurable_leadG b E W L)))
  have hmB : ∀ b' : Fin J, Measurable fun ω =>
      ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω)ᴴ b' a) := fun b' =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((continuous_pairFour r b' a).measurable.comp
        ((Continuous.matrix_conjTranspose continuous_id).measurable.comp
          (measurable_leadG b E W L))))
  have hmAB : ∀ b' : Fin J, Measurable fun ω =>
      ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω) b' a) +
        ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω)ᴴ b' a) := fun b' =>
    (hmA b').add (hmB b')
  have hF : ∀ b', ∫⁻ ω, ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω) b' a)
      ∂growthPathLaw W b ≤ ENNReal.ofReal (4 * (max C₄ 0 * μ ^ 4)) := fun b' => by
    simpa using lintegral_pairFour_le hraw4 hr hμ b' a false
  have hF' : ∀ b', ∫⁻ ω, ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω)ᴴ b' a)
      ∂growthPathLaw W b ≤ ENNReal.ofReal (4 * (max C₄ 0 * μ ^ 4)) := fun b' => by
    simpa using lintegral_pairFour_le hraw4 hr hμ b' a true
  have hQ : ∫⁻ ω, quadMoment W L (r a) (leadG b E W L ω) lam ∂growthPathLaw W b ≤
      ENNReal.ofReal (max Ce 0 + max C₂ 0 * μ ^ 2) := by
    rcases hlam with h | h
    · rw [h]
      refine (lintegral_quadMoment_tag_le hraw2 (hr a) (hμ a)).trans (ENNReal.ofReal_le_ofReal ?_)
      have := le_max_right Ce 0
      linarith
    · rw [h]
      simp_rw [quadMoment_gauss_eq b E (hr a)]
      refine (hext a).trans (ENNReal.ofReal_le_ofReal ?_)
      have := le_max_left Ce 0
      have : 0 ≤ max C₂ 0 * μ ^ 2 := mul_nonneg (le_max_right _ _) (sq_nonneg _)
      linarith
  have hm1 : Measurable fun ω => ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
      ∑ b', (ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω) b' a) +
        ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω)ᴴ b' a)) := by
    exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun b' _ => hmAB b'))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm1,
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ fun b' _ => hmAB b']
  simp_rw [lintegral_add_left (hmA _)]
  calc c * (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
        ∑ b', (∫⁻ ω, ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω) b' a) ∂growthPathLaw W b +
          ∫⁻ ω, ENNReal.ofReal (4 * pairFour W L r (leadG b E W L ω)ᴴ b' a) ∂growthPathLaw W b) +
        ENNReal.ofReal 6 * ∫⁻ ω, quadMoment W L (r a) (leadG b E W L ω) lam ∂growthPathLaw W b)
      ≤ c * (ENNReal.ofReal 5 + ENNReal.ofReal (40 * (J : ℝ) ^ 3) *
        ∑ _b' : Fin J, (ENNReal.ofReal (4 * (max C₄ 0 * μ ^ 4)) +
          ENNReal.ofReal (4 * (max C₄ 0 * μ ^ 4))) +
        ENNReal.ofReal 6 * ENNReal.ofReal (max Ce 0 + max C₂ 0 * μ ^ 2)) := by
        gcongr with b' _
        · exact hF b'
        · exact hF' b'
    _ = _ := by
        rw [← ofReal_combo _ _ _ _ (by positivity) (fun _ => by positivity)
          (fun _ => by positivity) (by positivity)]
        rfl

end Step

section Telescope
variable {W L J M : ℕ}

/-- Characteristic value of the hybrid where the slots of `S` are sampled tags. -/
def hybridChar (b E : ℝ) (W L J M : ℕ) (r : Fin J → Fin L → ℝ) (S : Finset (Fin (J * M)))
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) : ℂ :=
  ∫ z, hybridF (leadG b E W L) (slotWeight W L r S) u z
    ∂(growthPathLaw W b).prod (Measure.pi (slotMeasures W L r))

theorem slotWeight_insert (r : Fin J → Fin L → ℝ) {S : Finset (Fin (J * M))} {j : Fin (J * M)} :
    slotWeight W L r (insert j S) =
      Function.update (slotWeight W L r S) j (tagWeight W L (profileMass W L (r (tagGroup j)))) := by
  funext s
  by_cases h : s = j
  · subst h; funext o; simp [slotWeight]
  · rw [Function.update_of_ne h]
    funext o
    simp [slotWeight, Finset.mem_insert, h]

theorem slotWeight_self (r : Fin J → Fin L → ℝ) {S : Finset (Fin (J * M))} {j : Fin (J * M)}
    (hj : j ∉ S) :
    slotWeight W L r S =
      Function.update (slotWeight W L r S) j (fun _ => gaussWeight W L (r (tagGroup j))) := by
  refine (Function.update_eq_self_iff.2 ?_).symm
  funext o
  simp [slotWeight, hj]

/-- **One Lindeberg replacement** costs `2 t³ (1+2‖u‖)³ C`, `t = M^{-1/2}`. -/
theorem norm_hybridChar_insert_sub_le {b E C₄ C₂ Ce : ℝ} (hraw4 : RawTagFour b E W L C₄)
    (hraw2 : RawTagTwo b E W L C₂) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) {μ : ℝ}
    (hμ : ∀ a, profileMass W L (r a) ≤ μ)
    (hext : ∀ a, ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W L (r a) ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal Ce)
    (hM : 0 < M) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) (S : Finset (Fin (J * M)))
    (j : Fin (J * M)) (hj : j ∉ S) :
    ‖hybridChar b E W L J M r (insert j S) u - hybridChar b E W L J M r S u‖ ≤
      2 * ((Real.sqrt M)⁻¹ ^ 3 * (1 + 2 * ‖u‖) ^ 3 * stepConst J C₄ C₂ Ce μ) := by
  have hP : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hμs : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  have hρ : IsProbabilityMeasure (slotLaw W L (r (tagGroup j))) := isProbabilityMeasure_slotLaw (hr _)
  set Λ₀ := slotWeight W L r S
  set lt := tagWeight W L (profileMass W L (r (tagGroup j)))
  set lg : Fin (L + 1) → Fin L × Fin W → ℝ := fun _ => gaussWeight W L (r (tagGroup j))
  have e1 : hybridChar b E W L J M r (insert j S) u =
      ∫ z, hybridF (leadG b E W L) (Function.update Λ₀ j lt) u z
        ∂(growthPathLaw W b).prod (Measure.pi (slotMeasures W L r)) := by
    unfold hybridChar; rw [slotWeight_insert]
  have e2 : hybridChar b E W L J M r S u =
      ∫ z, hybridF (leadG b E W L) (Function.update Λ₀ j lg) u z
        ∂(growthPathLaw W b).prod (Measure.pi (slotMeasures W L r)) := by
    unfold hybridChar; rw [← slotWeight_self r hj]
  have hbound := enorm_integral_hybridF_swap_le (growthPathLaw W b) (measurable_leadG b E W L)
    hr hM Λ₀ j u
  rw [← e1, ← e2] at hbound
  have hΛ : ∀ s, IsSlotWeight W L r s (Λ₀ s) := isSlotWeight_slotWeight r S
  have hmeas : ∀ lam : Fin (L + 1) → Fin L × Fin W → ℝ,
      Measurable fun p : GrowthPath W × (Fin (J * M) → SlotSample W L) =>
        ∫⁻ y', swapRemainder (leadG b E W L p.1) Λ₀ u j lam p.2 y' ∂slotLaw W L (r (tagGroup j)) :=
    fun lam => (measurable_swapRemainder (measurable_leadG b E W L) Λ₀ u j lam).lintegral_prod_right'
  have hsplit : ∫⁻ ω, ∫⁻ x, (∫⁻ y', swapRemainder (leadG b E W L ω) Λ₀ u j lt x y'
        ∂slotLaw W L (r (tagGroup j)) + ∫⁻ y', swapRemainder (leadG b E W L ω) Λ₀ u j lg x y'
        ∂slotLaw W L (r (tagGroup j))) ∂Measure.pi (slotMeasures W L r) ∂growthPathLaw W b =
      ∫⁻ ω, ∫⁻ x, ∫⁻ y', swapRemainder (leadG b E W L ω) Λ₀ u j lt x y'
        ∂slotLaw W L (r (tagGroup j)) ∂Measure.pi (slotMeasures W L r) ∂growthPathLaw W b +
      ∫⁻ ω, ∫⁻ x, ∫⁻ y', swapRemainder (leadG b E W L ω) Λ₀ u j lg x y'
        ∂slotLaw W L (r (tagGroup j)) ∂Measure.pi (slotMeasures W L r) ∂growthPathLaw W b := by
    rw [← lintegral_add_left ((hmeas lt).lintegral_prod_right')]
    refine lintegral_congr fun ω => ?_
    exact lintegral_add_left ((hmeas lt).comp measurable_prodMk_left) _
  rw [hsplit] at hbound
  have h1 := lintegral_path_swapRemainder_le hraw4 hraw2 hr hμ hext hM hΛ j lt (Or.inl rfl) u
  have h2 := lintegral_path_swapRemainder_le hraw4 hraw2 hr hμ hext hM hΛ j lg (Or.inr rfl) u
  have h3 := hbound.trans (add_le_add h1 h2)
  rw [← ENNReal.ofReal_add (by positivity [stepConst_nonneg J C₄ C₂ Ce μ])
    (by positivity [stepConst_nonneg J C₄ C₂ Ce μ]), ← ofReal_norm] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by
    have := stepConst_nonneg J C₄ C₂ Ce μ; positivity)).1 h3
  linarith

/-- **Telescoping the `J·M` replacements** (each replacement costs `CM^{-3/2}`). -/
theorem norm_hybridChar_univ_sub_empty_le {b E C₄ C₂ Ce : ℝ} (hraw4 : RawTagFour b E W L C₄)
    (hraw2 : RawTagTwo b E W L C₂) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) {μ : ℝ}
    (hμ : ∀ a, profileMass W L (r a) ≤ μ)
    (hext : ∀ a, ∫⁻ ω, ENNReal.ofReal (sourceMoment2 b E W L (r a) ω) ∂growthPathLaw W b ≤
      ENNReal.ofReal Ce)
    (hM : 0 < M) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    ‖hybridChar b E W L J M r Finset.univ u - hybridChar b E W L J M r ∅ u‖ ≤
      2 * J * (1 + 2 * ‖u‖) ^ 3 * stepConst J C₄ C₂ Ce μ / Real.sqrt M := by
  have h := norm_sub_le_card_mul_of_insert (fun S => hybridChar b E W L J M r S u) _
    fun S j hj => norm_hybridChar_insert_sub_le hraw4 hraw2 hr hμ hext hM u S j hj
  refine h.trans (le_of_eq ?_)
  rw [Fintype.card_fin]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM'.le
  have hs0 : 0 < Real.sqrt M := Real.sqrt_pos.2 hM'
  push_cast
  field_simp
  rw [hs]

end Telescope

end BlockBand.Critical.GlobalSource
