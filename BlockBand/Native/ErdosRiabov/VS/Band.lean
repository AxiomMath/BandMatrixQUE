module

public import BlockBand.Native.ErdosRiabov.Stochastic.OURingLinear

set_option autoImplicit false

/-!
# The variance-scaling band process `H_t`

The VS band process `H_t`, a scaled band Brownian motion started at `0`, is a continuous
Hermitian semimartingale whose value at time `1` has the law of the Gaussian ring.

## Setting

Sample space `RingSample p = DriverSample p.SiteMatrix (Fin (ringDim p))` (initial state `x.1`,
unused here, and one real Wiener path `x.2 i` per real Gaussian coordinate), law
`driverLaw μ = μ ⊗ Wiener^d` for an **arbitrary** probability law `μ` of the initial state
(in the application `μ = model.law`), filtration `driverAugmented μ`. With
`Y = driverNoise (ringVariance p)`, `Y^i_t = √(v_i) B^i_t`:

* `vsNoise p t x = Y_t(x) - Y_0(x)` and `vsBand p t x = ringMatrix p (vsNoise p t x)`.

## Main results

* `vsBand_isHermitian` (every sample and time), `vsBand_zero` (`H_0 = 0` for every
  sample, because of the subtraction of `Y_0`), `continuous_vsBand` (every sample),
  `ringCoords_vsBand` (`ringCoords H_t = Y_t - Y_0`, every sample), `vsBand_sub`
  (`H_t - H_s = ringMatrix (Y_t - Y_s)`), and `isContinuousSemimartingale_vsNoise`: the real
  coordinates `Y_t - Y_0` of `H_t` form a continuous semimartingale with characteristics
  `(0, diag v)` for `(driverLaw μ, driverAugmented μ)`. The subtraction of the `𝓖_0`-measurable
  `Y_0` is the general `isContinuousSemimartingale_sub_initial` (same localizing sequence;
  the compensated coordinates are unchanged pointwise).
* The terminal law: `hasLaw_vsNoise_one` (the law of `Y_1 - Y_0` is
  `∏_i N(0, v_i)`), `hasLaw_ringCoords` (the law of `ringCoords` under `model.law` is the same
  product), and `vsBand_law_one`: `Measure.map (vsBand p 1) (driverLaw μ) = model.law` for every
  initial law `μ`, in particular for `μ = model.law` (`vsBand_law_one_model`). Proof: the Brownian
  increment law `hasLaw_commonRealBrownian_increment` (`s = 0`, `t = 1`),
  coordinatewise scaling (`gaussianReal_map_const_mul`), and the reconstruction
  `ringMatrix ∘ ringCoords = id` on the a.s. Hermitian support. For the law of the coordinates the
  full
  independent family `iIndepFun_gaussianExtraction` with the marginals
  `gaussianExtraction_coordinate_hasLaw` is used directly (inactive labels have law
  `N(0, 0) = δ_0`), which is the proof of `gaussianActiveExtraction_hasLaw` without the
  restriction to active labels. No characteristic function and no stationarity are used.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal ENNReal Matrix

/-!
### Subtracting the initial value of a continuous semimartingale
-/

section General

variable {Ω : Type*} {d : ℕ}

/-- Subtracting the initial value does not change the compensated coordinates. -/
theorem smCompensated_sub_initial (Y β : ℝ≥0 → Ω → Fin d → ℝ) (i : Fin d) :
    smCompensated (fun t ω => Y t ω - Y 0 ω) β i = smCompensated Y β i := by
  funext t ω
  simp only [smCompensated, Pi.sub_apply, sub_self, sub_zero]

variable [MeasurableSpace Ω]

/-- **Subtracting the initial value.** If `Y` is a continuous semimartingale with
characteristics `(β, α)`, so is `Y - Y_0`, with the same localizing sequence (the compensated
coordinates coincide for every sample, `smCompensated_sub_initial`). -/
theorem isContinuousSemimartingale_sub_initial {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (h : IsContinuousSemimartingale Q 𝓖 Y β α) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => Y t ω - Y 0 ω) β α := by
  obtain ⟨τ, hτ, hτlim, hm⟩ := h.localizing
  have e := smCompensated_sub_initial Y β
  refine ⟨fun t => (h.adapted t).sub ((h.adapted 0).mono (𝓖.mono zero_le)),
    h.progressive.sub (isStronglyProgressive_initial (h.adapted 0)), ?_,
    h.drift_progressive, h.cov_progressive, h.integrable,
    ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [h.continuous] with ω hω
    exact hω.sub continuous_const
  · rw [e]
    exact (hm n).1 i
  · rw [e, e]
    exact (hm n).2 i j

end General

/-!
### The VS band process
-/

variable (p : BlockBand.Parameters)

/-- The real coordinates of the VS band process: `Y_t - Y_0` with
`Y = driverNoise (ringVariance p)`, i.e. `(√v_i (B^i_t - B^i_0))_i`. -/
def vsNoise (t : ℝ≥0) (x : RingSample p) : Fin (ringDim p) → ℝ :=
  driverNoise (ringVariance p) t x - driverNoise (ringVariance p) 0 x

/-- **The VS band process** `H_t = ringMatrix (Y_t - Y_0)` (scaled band Brownian motion). -/
def vsBand (t : ℝ≥0) (x : RingSample p) : p.SiteMatrix := ringMatrix p (vsNoise p t x)

theorem vsNoise_apply (t : ℝ≥0) (x : RingSample p) (i : Fin (ringDim p)) :
    vsNoise p t x i = Real.sqrt (ringVariance p i) * (x.2 i t - x.2 i 0) := by
  simp only [vsNoise, driverNoise, Pi.sub_apply, mul_sub]

theorem vsNoise_zero (x : RingSample p) : vsNoise p 0 x = 0 := by
  simp only [vsNoise, sub_self]

theorem continuous_vsNoise (x : RingSample p) : Continuous fun t => vsNoise p t x := by
  refine continuous_pi fun i => ?_
  simp only [vsNoise_apply]
  exact continuous_const.mul ((x.2 i).continuous.sub continuous_const)

theorem measurable_vsNoise (t : ℝ≥0) : Measurable (vsNoise p t) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [vsNoise_apply]
  have hev : ∀ s : ℝ≥0, Measurable fun x : RingSample p => x.2 i s := fun s =>
    (ContinuousMap.measurable_eval s).comp ((measurable_pi_apply i).comp measurable_snd)
  exact measurable_const.mul ((hev t).sub (hev 0))

/-- The redundant coordinates of `Y_t - Y_0` vanish for every sample and time. -/
theorem vsNoise_of_isRingRedundant {i : Fin (ringDim p)} (hi : IsRingRedundant p i)
    (t : ℝ≥0) (x : RingSample p) : vsNoise p t x i = 0 := by
  rw [vsNoise_apply, ringVariance_of_isRingRedundant hi, Real.sqrt_zero, zero_mul]

/-- `H_t` is Hermitian for every sample and time. -/
theorem vsBand_isHermitian (t : ℝ≥0) (x : RingSample p) : (vsBand p t x).IsHermitian :=
  ringMatrix_isHermitian p _

/-- `H_0 = 0` for **every** sample. -/
theorem vsBand_zero (x : RingSample p) : vsBand p 0 x = 0 := by
  rw [vsBand, vsNoise_zero, ringMatrix_zero]

/-- `t ↦ H_t` is continuous for every sample. -/
theorem continuous_vsBand (x : RingSample p) : Continuous fun t => vsBand p t x :=
  (continuous_ringMatrix p).comp (continuous_vsNoise p x)

theorem measurable_vsBand (t : ℝ≥0) : Measurable (vsBand p t) :=
  (measurable_ringMatrix p).comp (measurable_vsNoise p t)

/-- `ringCoords H_t = Y_t - Y_0` for every sample and time. -/
theorem ringCoords_vsBand (t : ℝ≥0) (x : RingSample p) :
    ringCoords p (vsBand p t x) = vsNoise p t x :=
  ringCoords_ringMatrix fun _ hi => vsNoise_of_isRingRedundant p hi t x

/-- Increments: `H_t - H_s = ringMatrix (Y_t - Y_s)` for every sample. -/
theorem vsBand_sub (s t : ℝ≥0) (x : RingSample p) :
    vsBand p t x - vsBand p s x =
      ringMatrix p (driverNoise (ringVariance p) t x - driverNoise (ringVariance p) s x) := by
  rw [vsBand, vsBand, ← ringMatrix_sub]
  congr 1
  simp only [vsNoise, sub_sub_sub_cancel_right]

variable {p}

/-- **The coordinates of `H_t` form a continuous semimartingale with characteristics
`(0, diag v)`.** For every probability law `μ` of the (unused) old state, under `driverLaw μ`
with the null-augmented filtration `driverAugmented μ`, the real coordinates
`Y_t - Y_0 = ringCoords H_t` of the VS band process are a continuous semimartingale
(`IsContinuousSemimartingale`) with zero drift and constant covariance `diag (ringVariance p)`. -/
theorem isContinuousSemimartingale_vsNoise (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] :
    IsContinuousSemimartingale (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ) (vsNoise p) (fun _ _ => 0)
      (fun _ _ => Matrix.diagonal (ringVariance p)) :=
  isContinuousSemimartingale_sub_initial
    (isContinuousSemimartingale_driverNoise μ (ringVariance_nonneg p))

/-!
### The terminal law
-/

/-- **The increment law**: under `driverLaw μ`, `Y_1 - Y_0` has law `∏_i N(0, v_i)`. -/
theorem hasLaw_vsNoise_one (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ] :
    HasLaw (vsNoise p 1)
      (Measure.pi fun i : Fin (ringDim p) =>
        gaussianReal 0 (p.gaussianCoordinateVariance ((ringEquiv p).symm i)))
      (driverLaw (κ := Fin (ringDim p)) μ) := by
  have hB := hasLaw_commonRealBrownian_increment (κ := Fin (ringDim p)) μ 0 1
  have h1 : nndist (1 : ℝ≥0) 0 = 1 := by simp [NNReal.nndist_eq]
  rw [h1] at hB
  set g : (Fin (ringDim p) → ℝ) → Fin (ringDim p) → ℝ :=
    fun z i => Real.sqrt (ringVariance p i) * z i with hg
  have hgm : Measurable g :=
    measurable_pi_iff.2 fun i => measurable_const.mul (measurable_pi_apply i)
  have hgl : HasLaw g (Measure.pi fun i : Fin (ringDim p) =>
      gaussianReal 0 (p.gaussianCoordinateVariance ((ringEquiv p).symm i)))
      (Measure.pi fun _ : Fin (ringDim p) => gaussianReal 0 1) := by
    refine ⟨hgm.aemeasurable, ?_⟩
    rw [hg, Measure.pi_map_pi (f := fun i (z : ℝ) => Real.sqrt (ringVariance p i) * z)
      fun i => (measurable_const.mul measurable_id).aemeasurable]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    simp only [NNReal.coe_mk]
    exact Real.sq_sqrt (ringVariance_nonneg p i)
  have hc := hgl.comp hB
  refine hc.congr (ae_of_all _ fun x => ?_)
  funext i
  simp only [Function.comp_apply, hg, vsNoise_apply, commonRealBrownian]

/-- Under the physical law, the real coordinates `ringCoords` have law `∏_i N(0, v_i)`
(the redundant labels have variance `0`, i.e. law `δ_0`). -/
theorem hasLaw_ringCoords (model : p.GaussianRingModel) :
    HasLaw (ringCoords p)
      (Measure.pi fun i : Fin (ringDim p) =>
        gaussianReal 0 (p.gaussianCoordinateVariance ((ringEquiv p).symm i)))
      (model.law : Measure p.SiteMatrix) :=
  (model.iIndepFun_gaussianExtraction.precomp (ringEquiv p).symm.injective).hasLaw_pi
    fun i => model.gaussianExtraction_coordinate_hasLaw ((ringEquiv p).symm i)

/-- **The terminal law of the VS band process is the physical law.** For
every probability law `μ` of the (unused) initial state, the law of `H_1 = vsBand p 1` under
`driverLaw μ` is `model.law`. -/
theorem vsBand_law_one (model : p.GaussianRingModel) (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] :
    Measure.map (vsBand p 1) (driverLaw (κ := Fin (ringDim p)) μ) =
      (model.law : Measure p.SiteMatrix) := by
  have hae : (ringMatrix p ∘ ringCoords p) =ᵐ[(model.law : Measure p.SiteMatrix)] id := by
    filter_upwards [model.isPhysical.1] with H hH
    exact ringMatrix_ringCoords p hH
  have e : vsBand p 1 = ringMatrix p ∘ vsNoise p 1 := rfl
  rw [e, ← Measure.map_map (measurable_ringMatrix p) (measurable_vsNoise p 1),
    (hasLaw_vsNoise_one μ).map_eq, ← (hasLaw_ringCoords model).map_eq,
    Measure.map_map (measurable_ringMatrix p) (measurable_ringCoords p), Measure.map_congr hae,
    Measure.map_id]

/-- `HasLaw` form of `vsBand_law_one`. -/
theorem hasLaw_vsBand_one (model : p.GaussianRingModel) (μ : Measure p.SiteMatrix)
    [IsProbabilityMeasure μ] :
    HasLaw (vsBand p 1) (model.law : Measure p.SiteMatrix)
      (driverLaw (κ := Fin (ringDim p)) μ) :=
  ⟨(measurable_vsBand p 1).aemeasurable, vsBand_law_one model μ⟩

/-- **The terminal law with `μ = model.law`**: under `driverLaw model.law`, the law of `H_1` is
`model.law`. -/
theorem vsBand_law_one_model (model : p.GaussianRingModel) :
    Measure.map (vsBand p 1)
        (driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)) =
      (model.law : Measure p.SiteMatrix) :=
  vsBand_law_one model _

end BlockBand.Native.ErdosRiabov.VS
