module

public import BlockBand.Endpoints.Clock.OpenClockLimit
public import BlockBand.Endpoints.Clock.DetLaplace
public import BlockBand.Endpoints.Clock.CommonPortRatiosLaplace
public import BlockBand.Endpoints.Clock.SmallBall
public import BlockBand.Endpoints.Clock.OpenInputsPath
public import BlockBand.Endpoints.Clock.ClockMixingMeasure
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# The Gaussian probe of the one-ended clock and the Laplace calculus

* `hasDerivAt_lap`, `deriv_deriv_lap`: for a finite law `μ` on `[0,∞)` and `b > 0`,
  `∂_b lap μ = -∫ x e^{-bx} dμ` and `∂_b² lap μ = lap2 μ = ∫ x² e^{-bx} dμ` (via Mathlib's
  analytic moment generating function).
* `oneEndedQ_posSemidef`: `Q_j^q ⪰ 0` for every sample when `q ≥ 0` (induction on
  `Y_{j+1} = q C + L* Y L`, `C = 𝒢₁₂* 𝒢₁₂`).
* `openProbeLaw W b E q j`: the law of `g* Q_j^q g` under (one-ended layers) ⊗ `CN(0, I_W)`;
  a probability law on `[0,∞)`.
* `lap_openProbeLaw`: `lap (openProbeLaw …) a = E F_a(Q_j^q)` (`detLaplace`) for `a ≥ 0`
  (Fubini and the circular Gaussian identity `integral_exp_neg_quadForm_circular`).
* `integral_openProbeLaw_id`: `∫ x d(openProbeLaw) = E γ_j^q` (`integral_quadForm_circular`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal ComplexOrder Matrix

/-!
## 1. Derivatives of Laplace transforms
-/

section Deriv

variable (μ : Measure ℝ)

theorem neg_mem_interior_integrableExpSet [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ} (hb : 0 < b) :
    -b ∈ interior (integrableExpSet id μ) := by
  have hsub : Iio (0 : ℝ) ⊆ integrableExpSet id μ := by
    intro t ht
    show Integrable (fun x => exp (t * id x)) μ
    refine Integrable.of_bound (C := 1)
      (continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable ?_
    filter_upwards [hμ] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht) hx
  refine interior_mono hsub ?_
  rw [(isOpen_Iio : IsOpen (Iio (0 : ℝ))).interior_eq]
  simpa using hb

theorem lap_eq_mgf (b : ℝ) : lap μ b = mgf id μ (-b) := by
  unfold lap mgf; congr 1; funext x; congr 1; simp

/-- `∂_b lap μ (b) = -∫ x e^{-bx} dμ` for `b > 0`. -/
theorem hasDerivAt_lap [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ} (hb : 0 < b) :
    HasDerivAt (lap μ) (-∫ x, x * exp (-(b * x)) ∂μ) b := by
  have h := hasDerivAt_mgf (neg_mem_interior_integrableExpSet μ hμ hb)
  have hc := h.comp b (hasDerivAt_neg b)
  have e : lap μ = mgf id μ ∘ fun b => -b := funext fun b => lap_eq_mgf μ b
  rw [e]
  convert hc using 1
  simp only [id, mul_neg, mul_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 2; ring

/-- `∂_b² lap μ (b) = lap2 μ b = ∫ x² e^{-bx} dμ` for `b > 0`. -/
theorem deriv_deriv_lap [IsFiniteMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {b : ℝ} (hb : 0 < b) :
    deriv (deriv (lap μ)) b = lap2 μ b := by
  have hev : deriv (lap μ) =ᶠ[𝓝 b] fun b' => -∫ x, x * exp (-(b' * x)) ∂μ := by
    filter_upwards [lt_mem_nhds hb] with b' hb'
    exact (hasDerivAt_lap μ hμ hb').deriv
  rw [hev.deriv_eq]
  have h := hasDerivAt_integral_pow_mul_exp_real (neg_mem_interior_integrableExpSet μ hμ hb) 1
  have hc := (h.comp b (hasDerivAt_neg b)).neg
  have e : (fun b' => -∫ x, x * exp (-(b' * x)) ∂μ) =
      -((fun t => ∫ x, id x ^ 1 * exp (t * id x) ∂μ) ∘ fun b => -b) := by
    funext b'
    simp only [Pi.neg_apply, Function.comp_apply, id, pow_one]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; congr 2; ring
  rw [e, hc.deriv]
  unfold lap2
  simp only [id, mul_neg, mul_one, neg_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only; congr 2; ring

end Deriv

/-!
## 2. Positivity of the one-ended clock
-/

section Chain

variable {W : ℕ}

theorem oneEndedY_posSemidef (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (ω : Fin j → OneEndedLayer W) :
    (oneEndedY b E q D j ω).PosSemidef := by
  induction j with
  | zero => exact PosSemidef.zero
  | succ j ih =>
    show (((q (((j + 1 : ℕ) : ℝ) / W) : ℝ) : ℂ) •
          freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)) +
        (freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j)))ᴴ *
          oneEndedY b E q D j (Fin.init ω) *
          freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))).PosSemidef
    refine PosSemidef.add ?_ ?_
    · refine (posSemidef_conjTranspose_mul_self _).smul ?_
      exact Complex.zero_le_real.mpr (hq _)
    · exact (ih (Fin.init ω)).conjTranspose_mul_mul_same _

theorem oneEndedQ_posSemidef (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (ω : Fin j → OneEndedLayer W) :
    (oneEndedQ b E q D j ω).PosSemidef := by
  unfold oneEndedQ
  refine (oneEndedY_posSemidef b E hq D j ω).smul ?_
  rw [show (((W : ℝ) ^ 2)⁻¹ : ℂ) = ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by positivity)

instance freshLaw_isProbabilityMeasure' (W : ℕ) (b : ℝ) : IsProbabilityMeasure (freshLaw W b) :=
  BlockBand.Layers.meq_isProbabilityMeasure_layerLaw W b _

instance oneEndedLaw_isProbabilityMeasure' (W : ℕ) (b : ℝ) (j : ℕ) :
    IsProbabilityMeasure (oneEndedLaw W b j) := by
  unfold oneEndedLaw; infer_instance

/-- Measurability of `(Q, h) ↦ Re h* Q h` along measurable maps. -/
theorem measurable_quadForm_comp {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]
    {f : α → Matrix ι ι ℂ} {g : α → ι → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => quadForm (f x) (g x)) := by
  unfold quadForm
  refine Complex.measurable_re.comp ?_
  simp only [dotProduct, mulVec]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine ((continuous_star.measurable).comp ((measurable_pi_apply i).comp hg)).mul ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (ClockMixingProb.meas_entry hf i k).mul ((measurable_pi_apply k).comp hg)

/-- The law of the Gaussian probe `g* Q_j^q g` of the one-ended clock started from `X_0 = 0`,
under the first `j` fresh layers ⊗ `g ~ CN(0, I_W)`. -/
def openProbeLaw (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) : Measure ℝ :=
  ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))).map
    (fun p => quadForm (oneEndedQ b E q 0 j p.1) p.2)

theorem measurable_probe (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) :
    Measurable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      quadForm (oneEndedQ b E q 0 j p.1) p.2) :=
  measurable_quadForm_comp ((ClockMixingProb.meas_Q b E q 0 j).comp measurable_fst)
    measurable_snd

instance openProbeLaw_isProbabilityMeasure (W : ℕ) (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) :
    IsProbabilityMeasure (openProbeLaw W b E q j) := by
  unfold openProbeLaw; infer_instance

theorem openProbeLaw_nonneg (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ) :
    ∀ᵐ x ∂openProbeLaw W b E q j, 0 ≤ x := by
  unfold openProbeLaw
  rw [ae_map_iff (measurable_probe b E q j).aemeasurable measurableSet_Ici]
  exact Filter.Eventually.of_forall fun p =>
    CommonPortRatios.quadForm_nonneg_of_posSemidef (oneEndedQ_posSemidef b E hq 0 j p.1) p.2

/-- `F_a(Q) = E_g exp(-a g*Qg)` for `Q ⪰ 0`, `a ≥ 0`. -/
theorem detLaplace_eq_integral {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) :
    detLaplace Q a = ∫ h, exp (-(a * quadForm Q h)) ∂circularVectorLaw (Fin W) := by
  have hA : ((a : ℂ) • Q).PosSemidef := hQ.smul (Complex.zero_le_real.mpr ha)
  have h := integral_exp_neg_quadForm_circular hA
  simp_rw [CommonPortRatios.quadForm_smul_real] at h
  rw [h]; rfl

/-- **The Gaussian probe identity**: for `a ≥ 0`,
`lap (openProbeLaw W b E q j) a = E F_a(Q_j^q)`. -/
theorem lap_openProbeLaw (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ) {a : ℝ}
    (ha : 0 ≤ a) :
    lap (openProbeLaw W b E q j) a =
      ∫ ω, detLaplace (oneEndedQ b E q 0 j ω) a ∂oneEndedLaw W b j := by
  unfold lap openProbeLaw
  have hm := measurable_probe (W := W) b E q j
  rw [integral_map hm.aemeasurable
    (show Continuous (fun x : ℝ => exp (-(a * x))) by fun_prop).aestronglyMeasurable]
  have hI : Integrable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      exp (-(a * quadForm (oneEndedQ b E q 0 j p.1) p.2)))
      ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))) := by
    refine Integrable.of_bound ((measurable_exp.comp ((measurable_const.mul hm).neg)).aestronglyMeasurable)
      1 (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg ha (CommonPortRatios.quadForm_nonneg_of_posSemidef
      (oneEndedQ_posSemidef b E hq 0 j p.1) p.2)
  rw [integral_prod _ hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact (detLaplace_eq_integral (oneEndedQ_posSemidef b E hq 0 j ω) ha).symm

/-- The probe is integrable as soon as the clock `γ_j^q` is, and
`∫ x d(openProbeLaw) = E γ_j^q` (Gaussian conditioning `E_g g*Qg = Re Tr Q`). -/
theorem integral_openProbeLaw_id (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) (j : ℕ)
    (hint : Integrable (oneEndedGamma b E q 0 j) (oneEndedLaw W b j)) :
    Integrable id (openProbeLaw W b E q j) ∧
      ∫ x, x ∂openProbeLaw W b E q j = ∫ ω, oneEndedGamma b E q 0 j ω ∂oneEndedLaw W b j := by
  have hm := measurable_probe (W := W) b E q j
  have hnn : ∀ p : (Fin j → OneEndedLayer W) × (Fin W → ℂ),
      0 ≤ quadForm (oneEndedQ b E q 0 j p.1) p.2 := fun p =>
    CommonPortRatios.quadForm_nonneg_of_posSemidef (oneEndedQ_posSemidef b E hq 0 j p.1) p.2
  have hlin : ∀ ω, ∫ h, quadForm (oneEndedQ b E q 0 j ω) h ∂circularVectorLaw (Fin W) =
      oneEndedGamma b E q 0 j ω := fun ω => integral_quadForm_circular _
  have hI : Integrable (fun p : (Fin j → OneEndedLayer W) × (Fin W → ℂ) =>
      quadForm (oneEndedQ b E q 0 j p.1) p.2)
      ((oneEndedLaw W b j).prod (circularVectorLaw (Fin W))) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · dsimp only
      exact integrable_quadForm_circular (oneEndedQ b E q 0 j ω)
    dsimp only
    refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
    show oneEndedGamma b E q 0 j ω =
      ∫ h, ‖quadForm (oneEndedQ b E q 0 j ω) h‖ ∂circularVectorLaw (Fin W)
    rw [← hlin ω]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    show quadForm (oneEndedQ b E q 0 j ω) h = ‖quadForm (oneEndedQ b E q 0 j ω) h‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn (ω, h))]
  unfold openProbeLaw
  refine ⟨(integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).mpr hI, ?_⟩
  rw [integral_map hm.aemeasurable
    (show Continuous (fun x : ℝ => x) from continuous_id).aestronglyMeasurable,
    integral_prod _ hI]
  exact integral_congr_ae (Filter.Eventually.of_forall hlin)

/-- `lap μ b ≥ 1 - b ∫ x dμ` for a probability law on `[0,∞)` with a first moment, `b ≥ 0`. -/
theorem one_sub_le_lap (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (hI : Integrable id μ) {b : ℝ} (hb : 0 ≤ b) : 1 - b * ∫ x, x ∂μ ≤ lap μ b := by
  unfold lap
  have hI' : Integrable (fun x => b * x) μ := hI.const_mul b
  have h1 : Integrable (fun x => 1 - b * x) μ := (integrable_const 1).sub hI'
  have h2 : Integrable (fun x => exp (-(b * x))) μ := by
    refine Integrable.of_bound (C := 1)
      (continuous_exp.comp (continuous_const.mul continuous_id).neg).aestronglyMeasurable ?_
    filter_upwards [hμ] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hb hx
  have := integral_mono h1 h2 fun x => by
    have := add_one_le_exp (-(b * x)); linarith
  rw [integral_sub (integrable_const 1) hI', integral_const_mul] at this
  simpa using this

end Chain

end OpenClock
end BlockBand.Endpoints.Clock
