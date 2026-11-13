module

public import Mathlib
public import BlockBand.GaussianCalculus.LpGradientRotation
public import BlockBand.GaussianCalculus.LpGradientMoments

/-!
# The dimension-free Gaussian `L^p` gradient inequality (Pisier)

Law: `μ = gaussianProduct v` on `ι → ℝ`, finite `ι`, all variances `v i ≥ 0` (zero allowed). With
the absolute constant `C = 2π`, for every real `p ≥ 1` and every complex `C¹` function
`f ∈ L^p(μ)`, `‖f - E f‖_{L^p(μ)} ≤ 2π √p ‖(∑ᵢ vᵢ |∂ᵢ f|²)^{1/2}‖_{L^p(μ)}` (the right side may
be `∞`).

Proof by Pisier's rotation argument. For independent `X, Y ~ μ`,
`f(X) - f(Y) = ∫₀^{π/2} Df(X_θ)(X'_θ) dθ` with `(X_θ, X'_θ) = pairRot θ (X, Y)`, a pair of
independent `μ`-vectors for each `θ` (`measurePreserving_pairRot`). Jensen on `[0, π/2]`,
Tonelli and rotation invariance give `E|f(X) - f(Y)|^p ≤ (π/2)^p E|Df(X)Y|^p`; the Gaussian
moment bound `lintegral_enorm_linear_rpow_le` gives `E_Y|Df(x)Y|^p ≤ 4 (√p |∇f(x)|_v)^p`;
Jensen in `Y` gives `E|f - Ef|^p ≤ E|f(X) - f(Y)|^p`. Only `MemLp f p` (for integrability of
`f`) and `C¹` are used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- Jensen/Hölder for lower integrals on a finite measure:
`(∫⁻ g)^p ≤ ν(univ)^{p-1} ∫⁻ g^p` for `p ≥ 1`. -/
theorem lintegral_rpow_le_measure_univ_mul {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ a, g a ∂ν) ^ p ≤ ν univ ^ (p - 1) * ∫⁻ a, g a ^ p ∂ν := by
  have hp0 : 0 < p := by linarith
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp) hg.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable] at h
  simp only [enorm_eq_self, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le, div_one] at h
  calc (∫⁻ a, g a ∂ν) ^ p
      ≤ ((∫⁻ a, g a ^ p ∂ν) ^ (1 / p) * ν univ ^ (1 - 1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ν univ ^ (p - 1) * ∫⁻ a, g a ^ p ∂ν := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one,
          show (1 - 1 / p) * p = p - 1 by field_simp, mul_comm]

/-- Fundamental theorem of calculus along the rotation path: for `f` of class `C¹`,
`f x - f y = ∫₀^{π/2} Df(sin θ x + cos θ y)(cos θ x - sin θ y) dθ`. -/
theorem sub_eq_integral_pairRot {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (z : (ι → ℝ) × (ι → ℝ)) :
    f z.1 - f z.2 =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), fderiv ℝ f (pairRot θ z).1 (pairRot θ z).2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc : Continuous (fun θ : ℝ => pairRot θ z) :=
    continuous_pairRot.comp (continuous_id.prodMk continuous_const)
  have hderiv (θ : ℝ) : HasDerivAt (fun θ => f (pairRot θ z).1)
      (fderiv ℝ f (pairRot θ z).1 (pairRot θ z).2) θ := by
    have hγ : HasDerivAt (fun θ : ℝ => (pairRot θ z).1) (pairRot θ z).2 θ := by
      simp only [pairRot]
      have := ((Real.hasDerivAt_sin θ).smul_const z.1).add
        ((Real.hasDerivAt_cos θ).smul_const z.2)
      convert this using 1
      rw [neg_smul, sub_eq_add_neg]
    exact (hd _).hasFDerivAt.comp_hasDerivAt θ hγ
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (((hcont.comp hc.fst).clm_apply hc.snd).intervalIntegrable _ _)]
  simp [pairRot]

/-- The Fréchet derivative applied to `y` is the coordinate expansion `∑ᵢ yᵢ ∂ᵢ f(x)`. -/
theorem fderiv_apply_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ)
    (x y : ι → ℝ) :
    fderiv ℝ f x y = ∑ i, y i • fderiv ℝ f x (Pi.single i 1) := by
  have h := LinearMap.pi_apply_eq_sum_univ (fderiv ℝ f x).toLinearMap y
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **Gaussian `L^p` gradient bound** (Pisier), with the absolute constant `C = 2π`. Law
`gaussianProduct v` on `ι → ℝ`; the quantifiers are those of `GaussianLpGradient` (`C` first,
then every `p ≥ 1`, finite `ι`, `v ≥ 0`, complex `C¹` `f ∈ L^p`). Norms: `eLpNorm` at exponent
`ENNReal.ofReal p`; the gradient is `weightedGradientNorm v f = (∑ᵢ vᵢ ‖Df(x) eᵢ‖²)^{1/2}`. -/
theorem gaussianLpGradient_holds : GaussianLpGradient := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro p hp ι _ _ v f hf hmem
  have hγ : ∀ i, IsProbabilityMeasure (gaussianReal 0 (v i)) := fun i =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v i)
  have hμ : IsProbabilityMeasure (gaussianProduct v) := by
    unfold gaussianProduct
    infer_instance
  have hp0 : 0 < p := by linarith
  set μ := gaussianProduct v with hμdef
  set κ := μ.prod μ with hκdef
  have hPtoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hfc : Continuous f := hf.continuous
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  let D : (ι → ℝ) × (ι → ℝ) → ℂ := fun z => fderiv ℝ f z.1 z.2
  have hDc : Continuous D := (hcont.comp continuous_fst).clm_apply continuous_snd
  set G := weightedGradientNorm v f with hGdef
  have hGc : Continuous G := by
    rw [hGdef]
    unfold weightedGradientNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
    exact continuous_const.mul ((continuous_norm.comp (hcont.clm_apply continuous_const)).pow 2)
  have hG0 (x : ι → ℝ) : 0 ≤ G x := Real.sqrt_nonneg _
  -- Step D: Jensen in the second variable.
  have hint : Integrable f μ := hmem.integrable (ENNReal.one_le_ofReal.mpr hp)
  have hstepD : ∫⁻ x, ‖f x - ∫ y, f y ∂μ‖ₑ ^ p ∂μ ≤
      ∫⁻ z, ‖f z.1 - f z.2‖ₑ ^ p ∂κ := by
    rw [hκdef, lintegral_prod (fun z : (ι → ℝ) × (ι → ℝ) => ‖f z.1 - f z.2‖ₑ ^ p)
      ((ENNReal.continuous_rpow_const.comp
      (continuous_enorm.comp ((hfc.comp continuous_fst).sub
        (hfc.comp continuous_snd)))).measurable.aemeasurable)]
    refine lintegral_mono fun x => ?_
    have hx : f x - ∫ y, f y ∂μ = ∫ y, (f x - f y) ∂μ := by
      rw [integral_sub (integrable_const _) hint, integral_const]
      simp
    rw [hx]
    calc ‖∫ y, (f x - f y) ∂μ‖ₑ ^ p ≤ (∫⁻ y, ‖f x - f y‖ₑ ∂μ) ^ p :=
          ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hp0.le
      _ ≤ μ univ ^ (p - 1) * ∫⁻ y, ‖f x - f y‖ₑ ^ p ∂μ :=
          lintegral_rpow_le_measure_univ_mul μ
            ((continuous_enorm.comp (continuous_const.sub hfc)).measurable.aemeasurable) hp
      _ = ∫⁻ y, ‖f x - f y‖ₑ ^ p ∂μ := by rw [measure_univ, ENNReal.one_rpow, one_mul]
  -- Step B: rotation interpolation, Jensen in `θ`, Tonelli, rotation invariance.
  let ν : Measure ℝ := volume.restrict (Ioc 0 (Real.pi / 2))
  have hνuniv : ν univ = ENNReal.ofReal (Real.pi / 2) := by
    simp only [ν, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  have hΦc : Continuous (fun q : ((ι → ℝ) × (ι → ℝ)) × ℝ => ‖D (pairRot q.2 q.1)‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.comp (continuous_enorm.comp
      (hDc.comp (continuous_pairRot.comp (continuous_snd.prodMk continuous_fst))))
  have hDpc : Continuous (fun z => ‖D z‖ₑ ^ p) :=
    ENNReal.continuous_rpow_const.comp (continuous_enorm.comp hDc)
  have hpt (z : (ι → ℝ) × (ι → ℝ)) : ‖f z.1 - f z.2‖ₑ ^ p ≤
      ENNReal.ofReal ((Real.pi / 2) ^ (p - 1)) * ∫⁻ θ, ‖D (pairRot θ z)‖ₑ ^ p ∂ν := by
    rw [sub_eq_integral_pairRot hf z, intervalIntegral.integral_of_le (by positivity)]
    calc ‖∫ θ in Ioc 0 (Real.pi / 2), D (pairRot θ z)‖ₑ ^ p
        ≤ (∫⁻ θ, ‖D (pairRot θ z)‖ₑ ∂ν) ^ p :=
          ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) hp0.le
      _ ≤ ν univ ^ (p - 1) * ∫⁻ θ, ‖D (pairRot θ z)‖ₑ ^ p ∂ν :=
          lintegral_rpow_le_measure_univ_mul ν ((continuous_enorm.comp (hDc.comp
            (continuous_pairRot.comp (continuous_id.prodMk continuous_const)))).measurable.aemeasurable)
            hp
      _ = _ := by
          rw [hνuniv, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
  have hstepB : ∫⁻ z, ‖f z.1 - f z.2‖ₑ ^ p ∂κ ≤
      ENNReal.ofReal ((Real.pi / 2) ^ p) * ∫⁻ z, ‖D z‖ₑ ^ p ∂κ := by
    calc ∫⁻ z, ‖f z.1 - f z.2‖ₑ ^ p ∂κ
        ≤ ∫⁻ z, ENNReal.ofReal ((Real.pi / 2) ^ (p - 1)) *
            ∫⁻ θ, ‖D (pairRot θ z)‖ₑ ^ p ∂ν ∂κ := lintegral_mono hpt
      _ = ENNReal.ofReal ((Real.pi / 2) ^ (p - 1)) *
            ∫⁻ θ, ∫⁻ z, ‖D (pairRot θ z)‖ₑ ^ p ∂κ ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_lintegral_swap hΦc.measurable.aemeasurable]
      _ = ENNReal.ofReal ((Real.pi / 2) ^ (p - 1)) * ∫⁻ _θ, ∫⁻ z, ‖D z‖ₑ ^ p ∂κ ∂ν := by
          congr 1
          refine lintegral_congr fun θ => ?_
          exact (measurePreserving_pairRot v θ).lintegral_comp hDpc.measurable
      _ = ENNReal.ofReal ((Real.pi / 2) ^ p) * ∫⁻ z, ‖D z‖ₑ ^ p ∂κ := by
          rw [lintegral_const, hνuniv, mul_comm (∫⁻ z, ‖D z‖ₑ ^ p ∂κ), ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          rw [Real.rpow_sub_one (by positivity)]
          field_simp
  -- Step C: Gaussian moments of the linear form `y ↦ Df(x) y`.
  have hstepC : ∫⁻ z, ‖D z‖ₑ ^ p ∂κ ≤
      ENNReal.ofReal (4 * Real.sqrt p ^ p) * ∫⁻ x, ‖G x‖ₑ ^ p ∂μ := by
    rw [hκdef, lintegral_prod _ hDpc.measurable.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    have h := lintegral_enorm_linear_rpow_le v (fun i => fderiv ℝ f x (Pi.single i 1)) hp0
    refine (lintegral_congr fun y => ?_).trans_le (h.trans (le_of_eq ?_))
    · change ‖fderiv ℝ f x y‖ₑ ^ p = _
      rw [fderiv_apply_eq_sum f x y]
    rw [Real.enorm_of_nonneg (hG0 x), ENNReal.ofReal_rpow_of_nonneg (hG0 x) hp0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_assoc, ← Real.mul_rpow (Real.sqrt_nonneg _) (hG0 x)]
    rfl
  -- Combine.
  have hconst : (Real.pi / 2) ^ p * (4 * Real.sqrt p ^ p) ≤ (2 * Real.pi * Real.sqrt p) ^ p := by
    have h4 : (4 : ℝ) ≤ 4 ^ p := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp
    have heq : (2 * Real.pi * Real.sqrt p) ^ p =
        (Real.pi / 2) ^ p * (4 ^ p * Real.sqrt p ^ p) := by
      rw [← Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _),
        ← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      ring
    rw [heq]
    gcongr
  have hX : ∫⁻ x, ‖f x - ∫ y, f y ∂μ‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal ((2 * Real.pi * Real.sqrt p) ^ p) * ∫⁻ x, ‖G x‖ₑ ^ p ∂μ := by
    calc ∫⁻ x, ‖f x - ∫ y, f y ∂μ‖ₑ ^ p ∂μ
        ≤ ENNReal.ofReal ((Real.pi / 2) ^ p) *
            (ENNReal.ofReal (4 * Real.sqrt p ^ p) * ∫⁻ x, ‖G x‖ₑ ^ p ∂μ) :=
          hstepD.trans (hstepB.trans (by gcongr))
      _ ≤ _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          gcongr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun x => f x - ∫ y, f y ∂μ) hP0
      ENNReal.ofReal_ne_top (hfc.sub continuous_const).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 ENNReal.ofReal_ne_top hGc.aestronglyMeasurable,
    hPtoReal]
  calc (∫⁻ x, ‖f x - ∫ y, f y ∂μ‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal ((2 * Real.pi * Real.sqrt p) ^ p) * ∫⁻ x, ‖G x‖ₑ ^ p ∂μ) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hX (by positivity)
    _ = ENNReal.ofReal (2 * Real.pi * Real.sqrt p) * (∫⁻ x, ‖G x‖ₑ ^ p ∂μ) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end BlockBand.GaussianCalculus
