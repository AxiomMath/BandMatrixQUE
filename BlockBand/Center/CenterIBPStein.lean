module

public import BlockBand.Model.Construction.GaussianIntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Gaussian Stein identity for Lipschitz functions and an a.e. chain rule

* `cib_stein_lipschitz`: for a centered real Gaussian `gaussianReal 0 v` (any `v ≥ 0`,
  the degenerate Dirac case included) and a `K`-Lipschitz `F : ℝ → ℝ`, the functions
  `x * F x` and `deriv F` (everywhere-defined `deriv`, junk value `0` where `F` is not
  differentiable) are integrable and `E[X F(X)] = v E[F'(X)]`.
* `cib_chain_ae`: for a monotone Lipschitz `lam` and a measurable `ψ` with `|ψ| ≤ 1`,
  the primitive `y ↦ ∫_{e₀}^{lam y} ψ` has derivative `ψ (lam x) * deriv lam x` at
  Lebesgue-a.e. `x`.
* `cib_deriv_primitive_ae`: the corresponding `deriv` identity holds
  `gaussianReal 0 v`-a.e. **for `v ≠ 0`**. The hypothesis `v ≠ 0` is necessary: for
  `v = 0` the Gaussian is `dirac 0`, and `lam = id`, `ψ = indicator {0} 1`, `e₀ = 0`
  give `deriv (fun y => ∫ E in 0..y, ψ E) 0 = 0 ≠ 1 = ψ (lam 0) * deriv lam 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

/-!
## Part 1: Stein identity for Lipschitz functions
-/

/-- Linear growth of a Lipschitz function. -/
theorem cib_lipschitz_abs_le {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) (x : ℝ) :
    |F x| ≤ |F 0| + K * |x| := by
  have h := hF.dist_le_mul x 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

/-- The coordinate product `x * F x` of a Lipschitz `F` is integrable for every centered
real Gaussian. -/
theorem cib_integrable_coord_mul (v : ℝ≥0) {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    Integrable (fun x => x * F x) (gaussianReal 0 v) := by
  have h1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 v) :=
    ((memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl).abs
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  refine Integrable.mono' ((h1.const_mul |F 0|).add (h2.const_mul (K : ℝ)))
    (continuous_id.mul hF.continuous).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hb := cib_lipschitz_abs_le hF x
  have hx : 0 ≤ |x| := abs_nonneg x
  rw [Real.norm_eq_abs, abs_mul]
  calc |x| * |F x| ≤ |x| * (|F 0| + K * |x|) := by gcongr
    _ = |F 0| * |x| + (K : ℝ) * x ^ 2 := by rw [← sq_abs x]; ring

/-- The everywhere-defined derivative of a `K`-Lipschitz function is integrable for every
centered real Gaussian (it is measurable and bounded by `K`). -/
theorem cib_integrable_deriv (v : ℝ≥0) {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    Integrable (deriv F) (gaussianReal 0 v) :=
  Integrable.of_bound (measurable_deriv F).aestronglyMeasurable K
    (ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hF)

/-- The centered Gaussian density in the form `c * exp (-a x²)`. -/
theorem cib_gaussianPDFReal_eq (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x =
      (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x ^ 2) := by
  rw [gaussianPDFReal, sub_zero]
  congr 2
  ring

/-- Boundary decay: `F x * φ x → 0` at infinity for Lipschitz `F` and the nondegenerate
centered Gaussian density `φ`. -/
theorem cib_tendsto_boundary {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) :
    Tendsto (fun x => F x * gaussianPDFReal 0 v x) (cocompact ℝ) (𝓝 0) := by
  have hvpos : (0 : ℝ) < v := by
    have := v.coe_nonneg
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne this (Ne.symm hv')
  have ha : (0 : ℝ) < (2 * (v : ℝ))⁻¹ := by positivity
  set c : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set e : ℝ → ℝ := fun x => Real.exp (-(2 * (v : ℝ))⁻¹ * x ^ 2) with he
  have h0 := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha 0
  have h1 := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha 1
  have hlim : Tendsto (fun x : ℝ => c * (|F 0| * (|x| ^ (0 : ℝ) * e x) +
      (K : ℝ) * (|x| ^ (1 : ℝ) * e x))) (cocompact ℝ) (𝓝 0) := by
    have := ((h0.const_mul |F 0|).add (h1.const_mul (K : ℝ))).const_mul c
    simpa [he] using this
  refine squeeze_zero_norm (fun x => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, cib_gaussianPDFReal_eq, Real.rpow_zero, Real.rpow_one,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * e x)]
  have hb := cib_lipschitz_abs_le hF x
  have hce : 0 ≤ c * e x := by positivity
  calc |F x| * (c * e x) ≤ (|F 0| + K * |x|) * (c * e x) := by gcongr
    _ = c * (|F 0| * (1 * e x) + (K : ℝ) * (|x| * e x)) := by ring

/-- Interval integration by parts against the Gaussian density for a Lipschitz `F`. -/
theorem cib_interval_identity {v : ℝ≥0} (hv : v ≠ 0) {F : ℝ → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) (a b : ℝ) :
    (∫ x in a..b, gaussianPDFReal 0 v x * deriv F x) =
      F b * gaussianPDFReal 0 v b - F a * gaussianPDFReal 0 v a +
        (v : ℝ)⁻¹ * ∫ x in a..b, gaussianPDFReal 0 v x * (x * F x) := by
  have hFac : AbsolutelyContinuousOnInterval F a b :=
    (hF.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  have hφcd : ContDiff ℝ 1 (gaussianPDFReal 0 v) := by
    have : gaussianPDFReal 0 v = fun x =>
        (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x ^ 2) :=
      funext (cib_gaussianPDFReal_eq v)
    rw [this]
    fun_prop
  have hφac : AbsolutelyContinuousOnInterval (gaussianPDFReal 0 v) a b :=
    hφcd.contDiffOn.absolutelyContinuousOnInterval
  have h := hFac.integral_mul_deriv_eq_deriv_mul hφac
  have hd : ∀ x, deriv (gaussianPDFReal 0 v) x = -(x / (v : ℝ)) * gaussianPDFReal 0 v x := by
    intro x
    simpa [sub_zero] using (BlockBand.Model.Construction.hasDerivAt_gaussianDensity 0 v hv x).deriv
  simp_rw [hd] at h
  have e1 : (∫ x in a..b, F x * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x)) =
      -(v : ℝ)⁻¹ * ∫ x in a..b, gaussianPDFReal 0 v x * (x * F x) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  have e2 : (∫ x in a..b, deriv F x * gaussianPDFReal 0 v x) =
      ∫ x in a..b, gaussianPDFReal 0 v x * deriv F x := by
    congr 1
    funext x
    ring
  rw [e1, e2] at h
  linarith

/-- **Gaussian integration by parts (Stein) for Lipschitz functions**, with the
everywhere-defined `deriv`. Holds for every variance, including `v = 0`. -/
theorem cib_stein_lipschitz (v : ℝ≥0) {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) :
    Integrable (fun x => x * F x) (gaussianReal 0 v) ∧ Integrable (deriv F) (gaussianReal 0 v) ∧
      ∫ x, x * F x ∂gaussianReal 0 v = (v : ℝ) * ∫ x, deriv F x ∂gaussianReal 0 v := by
  refine ⟨cib_integrable_coord_mul v hF, cib_integrable_deriv v hF, ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp [gaussianReal_zero_var]
  have hA := (BlockBand.Model.Construction.integrable_gaussian_iff_density 0 v hv
    (deriv F)).mp (cib_integrable_deriv v hF)
  have hB := (BlockBand.Model.Construction.integrable_gaussian_iff_density 0 v hv
    (fun x => x * F x)).mp (cib_integrable_coord_mul v hF)
  simp only [smul_eq_mul] at hA hB
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  set A := ∫ x, gaussianPDFReal 0 v x * deriv F x
  set B := ∫ x, gaussianPDFReal 0 v x * (x * F x)
  have hL : Tendsto (fun R : ℝ => ∫ x in -R..R, gaussianPDFReal 0 v x * deriv F x)
      atTop (𝓝 A) :=
    intervalIntegral_tendsto_integral hA tendsto_neg_atTop_atBot tendsto_id
  have hbd := cib_tendsto_boundary hv hF
  have hR1 : Tendsto (fun R : ℝ => F R * gaussianPDFReal 0 v R) atTop (𝓝 0) :=
    hbd.mono_left atTop_le_cocompact
  have hR2 : Tendsto (fun R : ℝ => F (-R) * gaussianPDFReal 0 v (-R)) atTop (𝓝 0) :=
    (hbd.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have hR3 : Tendsto (fun R : ℝ => ∫ x in -R..R, gaussianPDFReal 0 v x * (x * F x))
      atTop (𝓝 B) :=
    intervalIntegral_tendsto_integral hB tendsto_neg_atTop_atBot tendsto_id
  have hR : Tendsto (fun R : ℝ => ∫ x in -R..R, gaussianPDFReal 0 v x * deriv F x)
      atTop (𝓝 (0 - 0 + (v : ℝ)⁻¹ * B)) := by
    refine ((hR1.sub hR2).add (hR3.const_mul (v : ℝ)⁻¹)).congr fun R => ?_
    exact (cib_interval_identity hv hF (-R) R).symm
  have hAB : A = (v : ℝ)⁻¹ * B := by
    simpa using tendsto_nhds_unique hL hR
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [hAB, ← mul_assoc, mul_inv_cancel₀ hvR, one_mul]

/-!
## Part 2: a.e. chain rule for an energy primitive
-/

/-- A measurable function bounded by `1` is locally integrable. -/
theorem cib_locallyIntegrable_of_abs_le_one {ψ : ℝ → ℝ} (hψ : Measurable ψ)
    (hψb : ∀ E, |ψ E| ≤ 1) : LocallyIntegrable ψ volume :=
  locallyIntegrable_iff.mpr fun _ hk =>
    IntegrableOn.of_bound hk.measure_lt_top hψ.aestronglyMeasurable 1
      (ae_of_all _ fun E => by rw [Real.norm_eq_abs]; exact hψb E)

/-- The primitive of a function bounded by `1` is `1`-Lipschitz. -/
theorem cib_primitive_abs_sub_le {ψ : ℝ → ℝ} (hψ : Measurable ψ) (hψb : ∀ E, |ψ E| ≤ 1)
    (e₀ a b : ℝ) :
    |(∫ E in e₀..b, ψ E) - ∫ E in e₀..a, ψ E| ≤ |b - a| := by
  have hloc := cib_locallyIntegrable_of_abs_le_one hψ hψb
  have hii (x y : ℝ) : IntervalIntegrable ψ volume x y :=
    intervalIntegrable_iff.mpr <|
      (hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  rw [intervalIntegral.integral_interval_sub_left (hii e₀ b) (hii e₀ a)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := ψ) (fun x _ => by rw [Real.norm_eq_abs]; exact hψb x)
  rw [Real.norm_eq_abs, one_mul] at this
  exact this

/-- If `lam` has derivative `0` at `x` and `G` is `1`-Lipschitz, then `G ∘ lam` has
derivative `0` at `x`. -/
theorem cib_hasDerivAt_comp_zero {lam G : ℝ → ℝ} {x : ℝ} (hd : HasDerivAt lam 0 x)
    (hG : ∀ a b, |G b - G a| ≤ |b - a|) : HasDerivAt (fun y => G (lam y)) 0 x := by
  rw [hasDerivAt_iff_isLittleO] at hd ⊢
  simp only [smul_zero, sub_zero] at hd ⊢
  refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)) hd
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  exact hG (lam x) (lam y)

/-- For monotone `lam` and a measurable Lebesgue-null set `N`, at a.e. point where `lam`
is differentiable and `lam x ∈ N`, the derivative vanishes. -/
theorem cib_ae_deriv_eq_zero_of_mem_null {lam : ℝ → ℝ} (hmono : Monotone lam) {N : Set ℝ}
    (hN : MeasurableSet N) (hN0 : volume N = 0) :
    ∀ᵐ x ∂(volume : Measure ℝ), DifferentiableAt ℝ lam x → lam x ∈ N → deriv lam x = 0 := by
  set s : Set ℝ := {x | DifferentiableAt ℝ lam x} ∩ lam ⁻¹' N with hs_def
  have hs : MeasurableSet s :=
    (measurableSet_of_differentiableAt ℝ lam).inter (hmono.measurable hN)
  have himg := lintegral_deriv_eq_volume_image_of_monotoneOn hs
    (fun x hx => hx.1.hasDerivAt.hasDerivWithinAt) (hmono.monotoneOn s)
  have hsub : lam '' s ⊆ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hzero : (∫⁻ x in s, ENNReal.ofReal (deriv lam x)) = 0 := by
    rw [himg]
    exact measure_mono_null hsub hN0
  rw [lintegral_eq_zero_iff (measurable_deriv lam).ennreal_ofReal] at hzero
  have h2 := (ae_restrict_iff' hs).mp hzero
  filter_upwards [h2] with x hx hdx hxN
  have h0 : ENNReal.ofReal (deriv lam x) = 0 := hx ⟨hdx, hxN⟩
  rw [ENNReal.ofReal_eq_zero] at h0
  exact le_antisymm h0 hmono.deriv_nonneg

/-- **A.e. chain rule** for the energy primitive `y ↦ ∫_{e₀}^{lam y} ψ` along a monotone
Lipschitz curve `lam`, with merely measurable `ψ`, `|ψ| ≤ 1`. -/
theorem cib_chain_ae {lam : ℝ → ℝ} (hmono : Monotone lam) {K : ℝ≥0} (hlip : LipschitzWith K lam)
    {ψ : ℝ → ℝ} (hψ : Measurable ψ) (hψb : ∀ E, |ψ E| ≤ 1) (e₀ : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      HasDerivAt (fun y => ∫ E in e₀..lam y, ψ E) (ψ (lam x) * deriv lam x) x := by
  set G : ℝ → ℝ := fun y => ∫ E in e₀..y, ψ E with hG_def
  have hloc := cib_locallyIntegrable_of_abs_le_one hψ hψb
  have hLDT := LocallyIntegrable.ae_hasDerivAt_integral hloc
  set B : Set ℝ := {y | ¬ HasDerivAt G (ψ y) y} with hB_def
  have hB0 : volume B = 0 := ae_iff.mp (hLDT.mono fun y hy => hy e₀)
  set N : Set ℝ := toMeasurable volume B with hN_def
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by rw [hN_def, measure_toMeasurable]; exact hB0
  have hGlip : ∀ a b, |G b - G a| ≤ |b - a| := cib_primitive_abs_sub_le hψ hψb e₀
  filter_upwards [hlip.ae_differentiableAt_real, cib_ae_deriv_eq_zero_of_mem_null hmono hN hN0]
    with x hdx hz
  by_cases hxN : lam x ∈ N
  · have h0 := hz hdx hxN
    have hd0 : HasDerivAt lam 0 x := h0 ▸ hdx.hasDerivAt
    rw [h0, mul_zero]
    exact cib_hasDerivAt_comp_zero hd0 hGlip
  · have hGd : HasDerivAt G (ψ (lam x)) (lam x) := by
      by_contra h
      exact hxN (subset_toMeasurable _ _ h)
    exact hGd.comp x hdx.hasDerivAt

/-- `deriv` form of `cib_chain_ae`, a.e. for the nondegenerate centered Gaussian.
The hypothesis `v ≠ 0` cannot be dropped (see the module docstring). -/
theorem cib_deriv_primitive_ae (v : ℝ≥0) (hv : v ≠ 0) {lam : ℝ → ℝ} (hmono : Monotone lam)
    {K : ℝ≥0} (hlip : LipschitzWith K lam) {ψ : ℝ → ℝ} (hψ : Measurable ψ)
    (hψb : ∀ E, |ψ E| ≤ 1) (e₀ : ℝ) :
    deriv (fun y => ∫ E in e₀..lam y, ψ E) =ᵐ[gaussianReal 0 v]
      fun x => ψ (lam x) * deriv lam x := by
  filter_upwards [(gaussianReal_absolutelyContinuous 0 hv).ae_le
    (cib_chain_ae hmono hlip hψ hψb e₀)] with x hx using hx.deriv

end BlockBand.Center
