module

public import BlockBand.Density.MeanMeasure
public import BlockBand.Density.GaussianConvolution
public import BlockBand.Model.Construction.GaussianTranslationPhysical
public import BlockBand.Model.Construction.GaussianTranslationSpectral

/-!
# The mean density is smooth and strictly positive

Law: the physical Gaussian ring law of any admissible `p` and any realization `model`. The scalar
trace `t = N⁻¹ Σ_x H_xx` has law `N(0, c/(NW))` and is independent of the traceless matrix
`H' = H - t`; the increasing eigenvalues satisfy `λ_i(H) = λ_i(H') + t`. Hence
`μ = meanEmpiricalMeasure p model` has the Lebesgue density `gaussConv ν σ²`,
`ν = N⁻¹ Σ_i Law(λ_i(H'))`, `σ² = c/(NW)`, which is `C^∞` and strictly positive. This proves
clause 1 of `Internal.Contracts.Inputs.CriticalDensityEstimate` and identifies every continuous
density of `μ` with `gaussConv ν σ²`. (One may also extract `t` from half of the diagonal
randomness; the full trace used here gives the same conclusion.)
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory ProbabilityTheory Set
open BlockBand.Counting BlockBand.External
open scoped ENNReal NNReal ContDiff

/-- Law of `Y + X` for `X ~ N(0,v)` independent of `Y`: `S ↦ ∫ N(y,v)(S) dLaw(Y)`. -/
theorem map_add_gaussian_apply {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {v : ℝ≥0} (hXm : Measurable X)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hY : Measurable Y) (hXY : IndepFun X Y P) (S : Set ℝ) (hS : MeasurableSet S) :
    Measure.map (fun w => Y w + X w) P S = ∫⁻ y, gaussianReal y v S ∂(Measure.map Y P) := by
  have hadd : Measurable (fun q : ℝ × ℝ => q.1 + q.2) := measurable_fst.add measurable_snd
  have hprod : Measure.map (fun w => (Y w, X w)) P = (Measure.map Y P).prod (gaussianReal 0 v) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hXm.aemeasurable).mp hXY.symm,
      hX.map_eq]
  have hcomp : (fun w => Y w + X w) = (fun q : ℝ × ℝ => q.1 + q.2) ∘ (fun w => (Y w, X w)) := rfl
  rw [hcomp, ← Measure.map_map hadd (hY.prodMk hXm), hprod, Measure.map_apply hadd hS,
    Measure.prod_apply (hadd hS)]
  apply lintegral_congr
  intro y
  rw [← zero_add y, ← gaussianReal_map_add_const y, Measure.map_apply (measurable_add_const y) hS,
    zero_add]
  congr 1
  ext x
  simp [add_comm]

/-- For Hermitian `H`, `λ_i(H) = λ_i(H - t) + t` with `t` the scalar trace. -/
theorem physicalEigenvalue_eq_traceless_add (p : Parameters) (H : p.SiteMatrix)
    (hH : H.IsHermitian) (i : Fin (Fintype.card p.Site)) :
    physicalEigenvalue p H i =
      physicalEigenvalue p (p.tracelessGaussianMatrix H) i + p.scalarTrace H := by
  have hH' : (p.tracelessGaussianMatrix H).IsHermitian := by
    unfold Parameters.tracelessGaussianMatrix
    exact hH.sub (by simp [Matrix.IsHermitian])
  have e1 : (p.physicalHermitianVersion H).1 = H := p.gaussianReconstruction_gaussianExtraction H hH
  have e2 : (p.physicalHermitianVersion (p.tracelessGaussianMatrix H)).1 =
      p.tracelessGaussianMatrix H := p.gaussianReconstruction_gaussianExtraction _ hH'
  have e3 : H = Model.Construction.gaussianSpectralTranslate (p.scalarTrace H)
      (p.tracelessGaussianMatrix H) := by
    unfold Model.Construction.gaussianSpectralTranslate Parameters.tracelessGaussianMatrix
    simp
  unfold physicalEigenvalue
  rw [increasingEigenvalue_congr e1 (p.physicalHermitianVersion H).2 hH,
    increasingEigenvalue_congr e2 _ hH',
    increasingEigenvalue_congr e3 hH
      (Model.Construction.isHermitian_gaussianSpectralTranslate _ _ hH')]
  exact congrFun (Model.Construction.orderedEigenvalue_gaussianSpectralTranslate
    (p.scalarTrace H) ⟨_, hH'⟩) i

/-- The traceless mean measure `ν = N⁻¹ Σ_i Law(λ_i(H - t))` (a probability measure). -/
def tracelessMeanMeasure (p : Parameters) (model : p.GaussianRingModel) : Measure ℝ :=
  (p.N : ℝ≥0∞)⁻¹ • ∑ i : Fin (Fintype.card p.Site),
    Measure.map (fun H => physicalEigenvalue p (p.tracelessGaussianMatrix H) i)
      (model.law : Measure p.SiteMatrix)

theorem measurable_tracelessEigenvalue (p : Parameters) (i : Fin (Fintype.card p.Site)) :
    Measurable (fun H => physicalEigenvalue p (p.tracelessGaussianMatrix H) i) :=
  (measurable_physicalEigenvalue p i).comp p.measurable_tracelessGaussianMatrix

theorem tracelessMeanMeasure_univ (p : Parameters) (model : p.GaussianRingModel) :
    tracelessMeanMeasure p model univ = 1 := by
  unfold tracelessMeanMeasure
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.map_apply (measurable_tracelessEigenvalue p _) MeasurableSet.univ,
    preimage_univ, measure_univ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, p.card_site, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast p.N_pos.ne') (ENNReal.natCast_ne_top _)

instance (p : Parameters) (model : p.GaussianRingModel) :
    IsProbabilityMeasure (tracelessMeanMeasure p model) :=
  ⟨tracelessMeanMeasure_univ p model⟩

theorem scalarTraceVariance_pos (p : Parameters) : 0 < ((p.scalarTraceVariance : ℝ≥0) : ℝ) := by
  change 0 < p.c / ((p.N : ℝ) * (p.W : ℝ))
  have := p.c_pos
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  positivity

/-- The smooth mean density `ρ_{n,W} = gaussConv ν (c/(NW))`. -/
def meanDensity (p : Parameters) (model : p.GaussianRingModel) : ℝ → ℝ :=
  gaussConv (tracelessMeanMeasure p model) p.scalarTraceVariance

/-- `μ = ρ_{n,W} · Lebesgue` (convolution with the law of `t`). -/
theorem meanEmpiricalMeasure_eq_withDensity (p : Parameters) (model : p.GaussianRingModel) :
    Internal.Contracts.Inputs.meanEmpiricalMeasure p model =
      volume.withDensity (fun e => ENNReal.ofReal (meanDensity p model e)) := by
  have hv : p.scalarTraceVariance ≠ 0 := by
    intro h
    have := scalarTraceVariance_pos p
    rw [h] at this
    simp at this
  ext S hS
  rw [meanDensity, ← lintegral_gaussianReal_eq_withDensity _ hv S hS]
  unfold Internal.Contracts.Inputs.meanEmpiricalMeasure tracelessMeanMeasure
    finiteSpectralIntensity
  rw [lintegral_smul_measure, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    lintegral_finsetSum_measure, Measure.coe_finsetSum, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hae : (fun H => Foundations.Spectral.increasingEigenvalue
      (p.physicalHermitianVersion H).2 i) =ᵐ[(model.law : Measure p.SiteMatrix)]
      fun H => physicalEigenvalue p (p.tracelessGaussianMatrix H) i + p.scalarTrace H := by
    filter_upwards [model.isPhysical.1] with H hH
    exact physicalEigenvalue_eq_traceless_add p H hH i
  rw [Measure.map_congr hae]
  exact map_add_gaussian_apply _ p.measurable_scalarTrace model.scalarTrace_hasLaw
    (measurable_tracelessEigenvalue p i)
    (model.scalarTrace_independent_tracelessMatrix.comp measurable_id
      (measurable_physicalEigenvalue p i)) S hS

theorem contDiff_meanDensity (p : Parameters) (model : p.GaussianRingModel) :
    ContDiff ℝ ∞ (meanDensity p model) :=
  contDiff_gaussConv _ (scalarTraceVariance_pos p)

theorem meanDensity_pos (p : Parameters) (model : p.GaussianRingModel) (e : ℝ) :
    0 < meanDensity p model e :=
  gaussConv_pos _ (IsProbabilityMeasure.ne_zero _) (scalarTraceVariance_pos p) e

/-- **Clause 1 of `CriticalDensityEstimate`**: for every admissible `p` and every realization, the
normalized expected empirical measure has a `C^∞`, nonnegative Lebesgue density. -/
theorem criticalDensity_smooth : ∀ (p : Parameters) (model : p.GaussianRingModel),
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ e, 0 ≤ ρ e) ∧
      Internal.Contracts.Inputs.meanEmpiricalMeasure p model =
        volume.withDensity (fun e => ENNReal.ofReal (ρ e)) :=
  fun p model => ⟨meanDensity p model, contDiff_meanDensity p model,
    fun e => (meanDensity_pos p model e).le, meanEmpiricalMeasure_eq_withDensity p model⟩

/-- Every continuous density of `μ` is the smooth density `ρ_{n,W}`. -/
theorem eq_meanDensity_of_withDensity (p : Parameters) (model : p.GaussianRingModel)
    {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (h : Internal.Contracts.Inputs.meanEmpiricalMeasure p model =
      volume.withDensity (fun e => ENNReal.ofReal (ρ e))) : ρ = meanDensity p model :=
  eq_of_withDensity_eq_of_pos hρ (contDiff_meanDensity p model).continuous
    (meanDensity_pos p model) (h.symm.trans (meanEmpiricalMeasure_eq_withDensity p model))

/-- `ρ_{n,W} ≤ K_b` (first bound of the smooth-density estimate). Uses `PSSS.SourceContract`. -/
theorem meanDensity_le (source : PSSS.SourceContract.{0}) (p : Parameters)
    (model : p.GaussianRingModel) (e : ℝ) : meanDensity p model e ≤ densityBound source p.b :=
  le_of_withDensity_le_smul_volume (contDiff_meanDensity p model).continuous
    (densityBound_pos source p.b_lt_half).le
    ((meanEmpiricalMeasure_eq_withDensity p model) ▸ meanEmpiricalMeasure_le_volume source p model)
    e

end BlockBand.Density
