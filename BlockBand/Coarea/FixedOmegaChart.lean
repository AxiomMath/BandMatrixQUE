module

public import BlockBand.Coarea.FixedOmegaFrame
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSelectedSimpleCoareaCover

/-!
# Fixed-`ω` coarea: the linear chart `x ↦ (E, z, B)` is Lebesgue measure preserving

Support lemmas for the fixed-`ω` coarea formula `CoareaContract.formula_fixed`.

*Measures.* Lebesgue measure `volume` on the real coordinate space
`HermitianCoordinateSpace d` and the product Lebesgue measure on
`ChartSpace d = ℝ × ((Fin (d-1) → ℂ) × HermitianCoordinateSpace (d-1))`.
*Domain.* Every `d` and every chart pivot `i : Fin d`. Exact identities; no limit.

## Main results

* `chartEquiv d i`: the incidence coordinates `eigenpairIncidenceCoordinates i`
  followed by the real coordinates of the complementary block, a real-linear
  equivalence `HermitianCoordinateSpace d ≃ₗ[ℝ] ChartSpace d`.
* `hermitianOfFinCoordinates_chartEquiv_symm`: the matrix of `chartEquiv.symm (E,z,b)` is the
  pivot-first un-reindexing of `[[E, zᴴ], [z, B]]`, `B = mat b`.
* `hilbertSchmidtNormSq_chartEquiv_symm`: `‖mat x‖²_HS = E² + 2|z|² + ‖B‖²_HS`.
* `lintegral_exp_hilbertSchmidt`: `∫ e^{-‖mat x‖²/(2t)} dx = Z_d(t)` (`gueNormalizer`).
* `measurePreserving_chartEquiv`: `chartEquiv d i` maps Lebesgue measure to Lebesgue measure.
  The image is an additive Haar measure, hence `c • volume`; the Gaussian
  `e^{-(E² + 2|z|² + ‖B‖²)/2}` integrates to `Z_d(1)` on both sides
  (`Z_d(1) = √(2π) π^{d-1} Z_{d-1}(1)`), so `c = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory ProbabilityTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal ComplexConjugate

/-- Chart coordinates `(E, z, b)`: energy, affine projective coordinate, real coordinates of
the complementary block. -/
abbrev ChartSpace (d : ℕ) := ℝ × ((Fin (d - 1) → ℂ) × HermitianCoordinateSpace (d - 1))

/-- The linear incidence chart `x ↦ (E, z, b)` of pivot `i`. -/
def chartEquiv (d : ℕ) (i : Fin d) : HermitianCoordinateSpace d ≃ₗ[ℝ] ChartSpace d :=
  (selectedEigenpairFinCoordinateLinearEquiv i).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
      (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (Fin (d - 1) → ℂ))
        (hermitianFinCoordinatesLinearEquiv (d - 1)).symm))

theorem chartEquiv_apply_fst (d : ℕ) (i : Fin d) (x : HermitianCoordinateSpace d) :
    (chartEquiv d i x).1 = (eigenpairIncidenceCoordinates i x).1 := rfl

theorem chartEquiv_apply_snd_fst (d : ℕ) (i : Fin d) (x : HermitianCoordinateSpace d) :
    (chartEquiv d i x).2.1 = (eigenpairIncidenceCoordinates i x).2.1 := rfl

theorem hermitianOfFinCoordinates_chartEquiv_snd_snd (d : ℕ) (i : Fin d)
    (x : HermitianCoordinateSpace d) :
    hermitianOfFinCoordinates (d - 1) (chartEquiv d i x).2.2 =
      (eigenpairIncidenceCoordinates i x).2.2 :=
  (hermitianFinCoordinatesLinearEquiv (d - 1)).apply_symm_apply _

theorem eigenpairIncidenceCoordinates_chartEquiv_symm (d : ℕ) (i : Fin d) (p : ChartSpace d) :
    eigenpairIncidenceCoordinates i ((chartEquiv d i).symm p) =
      (p.1, p.2.1, hermitianOfFinCoordinates (d - 1) p.2.2) := by
  have h := (chartEquiv d i).apply_symm_apply p
  obtain ⟨E, z, b⟩ := p
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun q => q.2.1) h
  have h3 := congrArg (fun q => hermitianOfFinCoordinates (d - 1) q.2.2) h
  simp only at h1 h2 h3
  rw [hermitianOfFinCoordinates_chartEquiv_snd_snd] at h3
  rw [chartEquiv_apply_fst] at h1
  rw [chartEquiv_apply_snd_fst] at h2
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- The matrix of a chart point: `mat(chartEquiv.symm (E,z,b))` is the pivot-first
un-reindexing of `[[E, zᴴ],[z, B]]`. -/
theorem hermitianOfFinCoordinates_chartEquiv_symm (d : ℕ) (i : Fin d) (p : ChartSpace d) :
    (hermitianOfFinCoordinates d ((chartEquiv d i).symm p)).1 =
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
        (Matrix.fromBlocks ((p.1 : ℂ) • (1 : Matrix Unit Unit ℂ))
          (eigenpairTangentColumn p.2.1)ᴴ (eigenpairTangentColumn p.2.1)
          (hermitianOfFinCoordinates (d - 1) p.2.2).1) := by
  change ((hermitianFinCoordinatesLinearEquiv d) ((hermitianFinCoordinatesLinearEquiv d).symm
    ((selectedCoordinateEigenpairLinearEquiv i).symm _))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem hilbertSchmidtNormSq_eigenpairTangentColumn {n : Type*} [Fintype n] (z : n → ℂ) :
    hilbertSchmidtNormSq (eigenpairTangentColumn z) = ∑ k, Complex.normSq (z k) := by
  simp [hilbertSchmidtNormSq, eigenpairTangentColumn]

/-- `‖mat x‖²_HS = E² + 2|z|² + ‖B‖²_HS` in chart coordinates. -/
theorem hilbertSchmidtNormSq_chartEquiv_symm (d : ℕ) (i : Fin d) (p : ChartSpace d) :
    hilbertSchmidtNormSq (hermitianOfFinCoordinates d ((chartEquiv d i).symm p)).1 =
      p.1 ^ 2 + 2 * ProjectiveHaar.chartSq p.2.1 +
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) p.2.2).1 := by
  rw [hermitianOfFinCoordinates_chartEquiv_symm, hilbertSchmidtNormSq_reindex,
    hilbertSchmidtNormSq_fromBlocks, FixedOmega.hilbertSchmidtNormSq_conjTranspose,
    hilbertSchmidtNormSq_eigenpairTangentColumn, FixedOmega.hilbertSchmidtNormSq_unit]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Complex.normSq_ofReal,
    ProjectiveHaar.chartSq]
  ring

/-!
## Gaussian integrals
-/

/-- `∫ e^{-‖mat x‖²/(2t)} dx = Z_d(t)` over the real coordinates (`t > 0`). -/
theorem lintegral_exp_hilbertSchmidt (d : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x : HermitianCoordinateSpace d,
        ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq (hermitianOfFinCoordinates d x).1 /
          (2 * t))) = ENNReal.ofReal (gueNormalizer d t) := by
  have hZ : 0 < gueNormalizer d t := by unfold gueNormalizer; positivity
  have h1 : ∫⁻ x : HermitianCoordinateSpace d, hermitianGUEDensity d t (hermitianGUEBlock d x) =
      1 := by
    have := lintegral_hermitianGUECoordinateMeasure_eq d ht (fun _ => (1 : ℝ≥0∞))
    simp only [lintegral_const, measure_univ, mul_one] at this
    exact this.symm
  have h2 : ∀ x : HermitianCoordinateSpace d,
      hermitianGUEDensity d t (hermitianGUEBlock d x) =
        ENNReal.ofReal ((gueNormalizer d t)⁻¹) *
          ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq (hermitianOfFinCoordinates d x).1 /
            (2 * t))) := by
    intro x
    rw [hermitianGUEDensity, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv, mul_comm]
    rfl
  simp_rw [h2] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
  rw [mul_comm] at h1
  have h3 := ENNReal.eq_inv_of_mul_eq_one_left h1
  rw [h3, ENNReal.ofReal_inv_of_pos hZ, inv_inv]

theorem lintegral_exp_neg_sq_half :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(x ^ 2) / 2)) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
  have h := lintegral_gaussianPDF_eq_one 0 (v := (1 : ℝ≥0)) one_ne_zero
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h2 : ∀ x : ℝ, gaussianPDF 0 1 x =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
        ENNReal.ofReal (Real.exp (-(x ^ 2) / 2)) := by
    intro x
    rw [gaussianPDF, gaussianPDFReal_def, ← ENNReal.ofReal_mul (by positivity)]
    simp
  simp_rw [h2] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm] at h
  rw [ENNReal.eq_inv_of_mul_eq_one_left h, ENNReal.ofReal_inv_of_pos hs, inv_inv]

theorem lintegral_exp_neg_chartSq (n : ℕ) :
    ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (Real.exp (-ProjectiveHaar.chartSq z)) =
      ENNReal.ofReal (Real.pi ^ n) := by
  have hprob : (circularVectorLaw (Fin n)) Set.univ = 1 := measure_univ
  rw [ProjectiveHaar.circularVectorLaw_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hprob
  have hpi : 0 < Real.pi ^ n := by have := Real.pi_pos; positivity
  have h2 : ∀ z : Fin n → ℂ, ProjectiveHaar.circularDensity (Fin n) z =
      ENNReal.ofReal ((Real.pi ^ n)⁻¹) *
        ENNReal.ofReal (Real.exp (-ProjectiveHaar.chartSq z)) := by
    intro z
    rw [ProjectiveHaar.circularDensity, ← ENNReal.ofReal_mul (by positivity), Fintype.card_fin]
    rfl
  simp_rw [h2] at hprob
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm] at hprob
  rw [ENNReal.eq_inv_of_mul_eq_one_left hprob, ENNReal.ofReal_inv_of_pos hpi, inv_inv]

/-- The chart Gaussian `e^{-(E² + 2|z|² + ‖B‖²)/2}` integrates to `√(2π) π^{d-1} Z_{d-1}(1)`. -/
theorem lintegral_chartGaussian (d : ℕ) :
    ∫⁻ p : ChartSpace d, ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + 2 * ProjectiveHaar.chartSq p.2.1 +
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) p.2.2).1) / (2 * 1))) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * (ENNReal.ofReal (Real.pi ^ (d - 1)) *
        ENNReal.ofReal (gueNormalizer (d - 1) 1)) := by
  have hsplit : ∀ p : ChartSpace d,
      ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + 2 * ProjectiveHaar.chartSq p.2.1 +
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) p.2.2).1) / (2 * 1))) =
      ENNReal.ofReal (Real.exp (-(p.1 ^ 2) / 2)) *
        (ENNReal.ofReal (Real.exp (-ProjectiveHaar.chartSq p.2.1)) *
          ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
            (hermitianOfFinCoordinates (d - 1) p.2.2).1 / (2 * 1)))) := by
    intro p
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hsplit]
  have hm1 : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(x ^ 2) / 2)) := by fun_prop
  have hm2 : Measurable fun z : Fin (d - 1) → ℂ =>
      ENNReal.ofReal (Real.exp (-ProjectiveHaar.chartSq z)) := by
    have := ProjectiveHaar.measurable_chartSq (n := Fin (d - 1)); fun_prop
  have hm3 : Measurable fun b : HermitianCoordinateSpace (d - 1) =>
      ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
        (hermitianOfFinCoordinates (d - 1) b).1 / (2 * 1))) := by
    have h0 := measurable_hermitianOfFinCoordinates (d - 1)
    have hc : Continuous (fun M : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ =>
        hilbertSchmidtNormSq M) := by
      unfold hilbertSchmidtNormSq; fun_prop
    have h1 : Measurable fun b : HermitianCoordinateSpace (d - 1) =>
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) b).1 :=
      hc.measurable.comp (measurable_subtype_coe.comp h0)
    fun_prop
  have hin := lintegral_prod_mul (μ := (volume : Measure (Fin (d - 1) → ℂ)))
    (ν := (volume : Measure (HermitianCoordinateSpace (d - 1)))) hm2.aemeasurable
    hm3.aemeasurable
  have hout := lintegral_prod_mul (μ := (volume : Measure ℝ))
    (ν := ((volume : Measure (Fin (d - 1) → ℂ)).prod
      (volume : Measure (HermitianCoordinateSpace (d - 1))))) hm1.aemeasurable
    ((hm2.comp measurable_fst).mul (hm3.comp measurable_snd)).aemeasurable
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  refine hout.trans ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hin, lintegral_exp_neg_sq_half, lintegral_exp_neg_chartSq,
    lintegral_exp_hilbertSchmidt _ one_pos]

/-- `Z_d(1) = √(2π) π^{d-1} Z_{d-1}(1)`. -/
theorem gueNormalizer_succ_one (d : ℕ) (hd : 1 ≤ d) :
    gueNormalizer d 1 = Real.sqrt (2 * Real.pi) * Real.pi ^ (d - 1) * gueNormalizer (d - 1) 1 := by
  have h := gueNormalizer_div_succ (d - 1) (t := 1) one_pos
  rw [Nat.sub_add_cancel hd] at h
  have hZ : 0 < gueNormalizer d 1 := by unfold gueNormalizer; positivity
  have hZ' : 0 < gueNormalizer (d - 1) 1 := by unfold gueNormalizer; positivity
  simp only [mul_one] at h
  rw [div_eq_iff hZ.ne', one_div, inv_mul_eq_div, eq_div_iff (by positivity)] at h
  rw [← Real.sqrt_eq_rpow, Real.rpow_natCast] at h
  rw [← h]
  ring

instance instIsAddHaarMeasureChartSpace (d : ℕ) :
    (volume : Measure (ChartSpace d)).IsAddHaarMeasure := by
  have : (volume : Measure ((Fin (d - 1) → ℂ) × HermitianCoordinateSpace (d - 1))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

/-- **The linear incidence chart preserves Lebesgue measure.** -/
theorem measurePreserving_chartEquiv (d : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    MeasurePreserving (chartEquiv d i) volume volume := by
  have hL : Measurable (chartEquiv d i) :=
    (chartEquiv d i).toContinuousLinearEquiv.continuous.measurable
  refine ⟨hL, ?_⟩
  set μ : Measure (ChartSpace d) := (volume : Measure (HermitianCoordinateSpace d)).map
    (chartEquiv d i)
  have : μ.IsAddHaarMeasure :=
    (chartEquiv d i).toContinuousLinearEquiv.isAddHaarMeasure_map volume
  have hHaar : μ = μ.addHaarScalarFactor volume • volume :=
    Measure.isAddLeftInvariant_eq_smul μ volume
  set c := μ.addHaarScalarFactor volume
  set φ : ChartSpace d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(p.1 ^ 2 + 2 * ProjectiveHaar.chartSq p.2.1 +
      hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) p.2.2).1) / (2 * 1)))
  have hφ : Measurable φ := by
    have h0 := measurable_hermitianOfFinCoordinates (d - 1)
    have hc : Continuous (fun M : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ =>
        hilbertSchmidtNormSq M) := by
      unfold hilbertSchmidtNormSq; fun_prop
    have h1 : Measurable fun b : HermitianCoordinateSpace (d - 1) =>
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) b).1 :=
      hc.measurable.comp (measurable_subtype_coe.comp h0)
    have h2 := ProjectiveHaar.measurable_chartSq (n := Fin (d - 1))
    have h1' : Measurable fun p : ChartSpace d =>
        hilbertSchmidtNormSq (hermitianOfFinCoordinates (d - 1) p.2.2).1 :=
      h1.comp (measurable_snd.comp measurable_snd)
    have h2' : Measurable fun p : ChartSpace d => ProjectiveHaar.chartSq p.2.1 :=
      h2.comp (measurable_fst.comp measurable_snd)
    simp only [φ]
    fun_prop
  have hleft : ∫⁻ p, φ p ∂μ = ENNReal.ofReal (gueNormalizer d 1) := by
    rw [lintegral_map hφ hL, ← lintegral_exp_hilbertSchmidt d one_pos]
    refine lintegral_congr fun x => ?_
    simp only [φ]
    rw [← hilbertSchmidtNormSq_chartEquiv_symm d i, LinearEquiv.symm_apply_apply]
  have hright : ∫⁻ p, φ p ∂μ = (c : ℝ≥0∞) * ENNReal.ofReal (gueNormalizer d 1) := by
    conv_lhs => rw [hHaar]
    rw [lintegral_smul_measure, lintegral_chartGaussian, gueNormalizer_succ_one d hd,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
    rfl
  have hZ : 0 < gueNormalizer d 1 := by unfold gueNormalizer; positivity
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have h := hleft.symm.trans hright
    have hne : ENNReal.ofReal (gueNormalizer d 1) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hZ
    exact (ENNReal.mul_eq_right hne ENNReal.ofReal_ne_top).1 h.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hHaar, hc1', one_smul]

end BlockBand.Coarea.FixedOmega
