module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic

/-!
# The scalar Gaussian Palm kernel

The scalar component of `GUE_N(c₀/N)` is Gaussian with variance `c₀/N²`; its density
`scalarWeight c₀ N E ν` at `E - ν` is the Palm kernel. Adding this independent scalar to a
spectral coordinate `ν` disintegrates the marked spectral measure against this kernel.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The variance `c₀/N²` of the scalar component of `GUE_N(c₀/N)`. -/
def scalarVariance (c₀ : ℝ≥0) (N : ℕ) : ℝ≥0 := c₀ / (N : ℝ≥0) ^ 2

/-- The Gaussian density of variance `c₀/N²` at `E - ν` (unnormalized spectral weight). -/
def scalarWeight (c₀ : ℝ≥0) (N : ℕ) (E ν : ℝ) : ℝ :=
  gaussianPDFReal 0 (scalarVariance c₀ N) (E - ν)

/-- The same weight in `ℝ≥0∞`. -/
def scalarWeightENN (c₀ : ℝ≥0) (N : ℕ) (E ν : ℝ) : ℝ≥0∞ :=
  gaussianPDF 0 (scalarVariance c₀ N) (E - ν)

/-- The variance is nonzero for `c₀ ≠ 0` and `N ≠ 0`. -/
theorem scalarVariance_ne_zero {c₀ : ℝ≥0} {N : ℕ}
    (hc₀ : c₀ ≠ 0) (hN : N ≠ 0) : scalarVariance c₀ N ≠ 0 := by
  exact div_ne_zero hc₀ (pow_ne_zero 2 (by exact_mod_cast hN))

/-- The variance as a real number is `c₀/N²`. -/
theorem coe_scalarVariance (c₀ : ℝ≥0) (N : ℕ) :
    (scalarVariance c₀ N : ℝ) = (c₀ : ℝ) / (N : ℝ) ^ 2 := by
  simp [scalarVariance]

/-- The real Palm weight is nonnegative for every energy and spectral coordinate. -/
theorem scalarWeight_nonneg (c₀ : ℝ≥0) (N : ℕ) (E ν : ℝ) :
    0 ≤ scalarWeight c₀ N E ν := gaussianPDFReal_nonneg _ _ _

/-- Both versions represent the same weight. -/
theorem scalarWeightENN_eq_ofReal (c₀ : ℝ≥0) (N : ℕ) (E ν : ℝ) :
    scalarWeightENN c₀ N E ν = ENNReal.ofReal (scalarWeight c₀ N E ν) := rfl

/-- Uniform Gaussian density bound, with prefactor `N/√(2πc₀)`. -/
theorem scalarWeight_le_prefactor (c₀ : ℝ≥0) (N : ℕ) (E ν : ℝ) :
    scalarWeight c₀ N E ν ≤ (Real.sqrt (2 * Real.pi * scalarVariance c₀ N))⁻¹ := by
  unfold scalarWeight gaussianPDFReal
  have he : Real.exp (-((E - ν) - 0) ^ 2 / (2 * scalarVariance c₀ N)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  exact (mul_le_mul_of_nonneg_left he
    (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi * scalarVariance c₀ N)))).trans_eq
      (mul_one _)

/-- Scalar identity at a fixed base point: for every measurable nonnegative `ψ`,
`∫ ψ(ν + g) dN(0, c₀/N²)(g) = ∫ ψ(E) scalarWeight(E, ν) dE`. -/
theorem lintegral_scalarShift_eq_kernel
    {c₀ : ℝ≥0} {N : ℕ} (hc₀ : c₀ ≠ 0) (hN : N ≠ 0)
    (ν : ℝ) {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    (∫⁻ g, ψ (ν + g) ∂gaussianReal 0 (scalarVariance c₀ N)) =
      ∫⁻ E, ψ E * scalarWeightENN c₀ N E ν := by
  have hv := scalarVariance_ne_zero hc₀ hN
  calc
    (∫⁻ g, ψ (ν + g) ∂gaussianReal 0 (scalarVariance c₀ N)) =
        ∫⁻ E, ψ E ∂gaussianReal ν (scalarVariance c₀ N) := by
      have hm : (gaussianReal 0 (scalarVariance c₀ N)).map (fun g => ν + g) =
          gaussianReal ν (scalarVariance c₀ N) := by
        simpa only [zero_add] using
          (gaussianReal_map_const_add (μ := 0) (v := scalarVariance c₀ N) ν)
      rw [← hm]
      exact (lintegral_map hψ
        (show Measurable (fun g : ℝ => ν + g) from
          measurable_const.add measurable_id)).symm
    _ = ∫⁻ E, gaussianPDF ν (scalarVariance c₀ N) E * ψ E := by
      rw [gaussianReal_of_var_ne_zero _ hv]
      exact lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF _ _) hψ
    _ = _ := by
      apply lintegral_congr
      intro E
      simp [scalarWeightENN, gaussianPDF, gaussianPDFReal_sub, mul_comm]

/-- Scalar disintegration for a nonnegative test depending jointly on the base data and the
energy. -/
theorem lintegral_dependentScalarShift_eq_kernel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {c₀ : ℝ≥0} {N : ℕ} (hc₀ : c₀ ≠ 0) (hN : N ≠ 0)
    {ν : Ω → ℝ} (hν : Measurable ν)
    {Φ : Ω × ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ p : Ω × ℝ, Φ (p.1, ν p.1 + p.2)
      ∂μ.prod (gaussianReal 0 (scalarVariance c₀ N))) =
      ∫⁻ E, ∫⁻ ω, Φ (ω, E) * scalarWeightENN c₀ N E (ν ω) ∂μ := by
  have hshift : Measurable (fun p : Ω × ℝ => (p.1, ν p.1 + p.2)) :=
    measurable_fst.prodMk ((hν.comp measurable_fst).add measurable_snd)
  rw [lintegral_prod (fun p : Ω × ℝ => Φ (p.1, ν p.1 + p.2))
    (hΦ.comp hshift).aemeasurable]
  calc
    (∫⁻ ω, ∫⁻ g, Φ (ω, ν ω + g)
        ∂gaussianReal 0 (scalarVariance c₀ N) ∂μ) =
        ∫⁻ ω, ∫⁻ E, Φ (ω, E) * scalarWeightENN c₀ N E (ν ω) ∂volume ∂μ := by
      apply lintegral_congr
      intro ω
      exact lintegral_scalarShift_eq_kernel hc₀ hN (ν ω)
        (hΦ.comp (measurable_const.prodMk measurable_id))
    _ = _ := by
      apply lintegral_lintegral_swap
      unfold scalarWeightENN gaussianPDF gaussianPDFReal
      fun_prop

/-- The marked spectral measure of the scalar shift under the product law equals the base law
with the Gaussian Palm kernel density. -/
theorem map_scalarShift_eq_withDensity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {c₀ : ℝ≥0} {N : ℕ} (hc₀ : c₀ ≠ 0) (hN : N ≠ 0)
    {ν : Ω → ℝ} (hν : Measurable ν) :
    (μ.prod (gaussianReal 0 (scalarVariance c₀ N))).map
        (fun p : Ω × ℝ => (p.1, ν p.1 + p.2)) =
      (μ.prod (volume : Measure ℝ)).withDensity
        (fun p : Ω × ℝ => scalarWeightENN c₀ N p.2 (ν p.1)) := by
  have hshift : Measurable (fun p : Ω × ℝ => (p.1, ν p.1 + p.2)) :=
    measurable_fst.prodMk ((hν.comp measurable_fst).add measurable_snd)
  have hd : Measurable (fun p : Ω × ℝ => scalarWeightENN c₀ N p.2 (ν p.1)) := by
    unfold scalarWeightENN gaussianPDF gaussianPDFReal
    fun_prop
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hshift,
    lintegral_dependentScalarShift_eq_kernel μ hc₀ hN hν hΦ,
    lintegral_withDensity_eq_lintegral_mul _ hd hΦ]
  change (∫⁻ E, ∫⁻ ω, Φ (ω, E) * scalarWeightENN c₀ N E (ν ω) ∂μ) =
    ∫⁻ p : Ω × ℝ, scalarWeightENN c₀ N p.2 (ν p.1) * Φ p ∂μ.prod volume
  have hp : Measurable (fun p : Ω × ℝ =>
      scalarWeightENN c₀ N p.2 (ν p.1) * Φ p) := hd.mul hΦ
  rw [lintegral_prod_symm (fun p : Ω × ℝ =>
    scalarWeightENN c₀ N p.2 (ν p.1) * Φ p) hp.aemeasurable]
  apply lintegral_congr
  intro E
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

/-- Marked scalar disintegration under the independent product law, for an arbitrary base mark
`f` and measurable coordinate `ν`, uniformly in `E`, `ν`, `f` and the base law. -/
theorem lintegral_markedScalarShift_eq_kernel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {c₀ : ℝ≥0} {N : ℕ} (hc₀ : c₀ ≠ 0) (hN : N ≠ 0)
    {ν : Ω → ℝ} (hν : Measurable ν)
    {f : Ω → ℝ≥0∞} (hf : Measurable f)
    {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) :
    (∫⁻ p : Ω × ℝ, f p.1 * ψ (ν p.1 + p.2)
      ∂μ.prod (gaussianReal 0 (scalarVariance c₀ N))) =
      ∫⁻ E, ψ E * ∫⁻ ω, f ω * scalarWeightENN c₀ N E (ν ω) ∂μ := by
  have hΦ : Measurable (fun p : Ω × ℝ => f p.1 * ψ p.2) :=
    (hf.comp measurable_fst).mul (hψ.comp measurable_snd)
  calc
    (∫⁻ p : Ω × ℝ, f p.1 * ψ (ν p.1 + p.2)
      ∂μ.prod (gaussianReal 0 (scalarVariance c₀ N))) =
        ∫⁻ E, ∫⁻ ω, (f ω * ψ E) * scalarWeightENN c₀ N E (ν ω) ∂μ :=
      lintegral_dependentScalarShift_eq_kernel μ hc₀ hN hν hΦ
    _ = _ := by
      apply lintegral_congr
      intro E
      have hm : Measurable (fun ω => f ω * scalarWeightENN c₀ N E (ν ω)) := by
        unfold scalarWeightENN gaussianPDF gaussianPDFReal
        fun_prop
      rw [← lintegral_const_mul (ψ E) hm]
      apply lintegral_congr
      intro ω
      ring

/-- The unnormalized sector masses integrate to the total mass of the base law. -/
theorem lintegral_scalarSectorMass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {c₀ : ℝ≥0} {N : ℕ} (hc₀ : c₀ ≠ 0) (hN : N ≠ 0)
    {ν : Ω → ℝ} (hν : Measurable ν) :
    (∫⁻ E, ∫⁻ ω, scalarWeightENN c₀ N E (ν ω) ∂μ) = μ Set.univ := by
  have h := lintegral_markedScalarShift_eq_kernel μ hc₀ hN hν
    (f := fun _ => 1) measurable_const (ψ := fun _ => 1) measurable_const
  have hm : (μ.prod (gaussianReal 0 (scalarVariance c₀ N))) Set.univ = μ Set.univ := by
    have hg : (gaussianReal 0 (scalarVariance c₀ N)) Set.univ = 1 := measure_univ
    rw [← Set.univ_prod_univ, Measure.prod_prod, hg, mul_one]
  simpa only [one_mul, lintegral_one, hm] using h.symm

end BlockBand.Palm
