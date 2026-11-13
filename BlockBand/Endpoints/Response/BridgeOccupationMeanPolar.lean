module

public import BlockBand.Endpoints.Response.BridgeOccupationMeanDefs
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Hyperbolic bridge mass and moment in radial and planar coordinates

* `bom_lintegral_Ici_X`: the change of variables `x' = (cosh r' - 1)/2`, `dx' = (sinh r'/2) dr'`;
* `bom_mass_eq`, `bom_moment_eq`: `bopXMass`, `bopXMoment` as radial integrals `bomRadialInt` of
  the product `lbkHypRadial(D₀s/2) x₀ x(r') · lbkHypRadial(D₀(T-s)/2) x(r') 0`;
* `bom_radialInt_eucl`: with the comparison kernels `bomEuclRadial` in place of `lbkHypRadial`,
  the radial integral is (a positive constant times) the planar integral `∫ G(q) W(q) dq` of the
  planar Brownian-bridge weight `W = bomW` (polar coordinates; the `h`-factors cancel through
  `σ(r') sinh r' = r'`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Real
open scoped ENNReal

/-!
### The change of variables `x' = (cosh r' - 1)/2`
-/

theorem bom_image_X : bomX '' Ici 0 = Ici 0 := by
  ext y
  constructor
  · rintro ⟨r, -, rfl⟩
    exact bom_X_nonneg r
  · intro hy
    have hy' : (0 : ℝ) ≤ y := hy
    refine ⟨Real.arcosh (1 + 2 * y), Real.arcosh_nonneg (by linarith), ?_⟩
    unfold bomX
    rw [Real.cosh_arcosh (by linarith)]
    ring

theorem bom_lintegral_Ici_X (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ici (0 : ℝ), g x =
      ∫⁻ r in Ici (0 : ℝ), ENNReal.ofReal (Real.sinh r / 2) * g (bomX r) := by
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivWithinAt bomX (Real.sinh r / 2) (Ici 0) r := by
    intro r _
    unfold bomX
    exact (((Real.hasDerivAt_cosh r).sub_const 1).div_const 2).hasDerivWithinAt
  have hinj : InjOn bomX (Ici 0) := by
    intro r hr r' hr' h
    unfold bomX at h
    exact Real.cosh_strictMonoOn.injOn hr hr' (by linarith)
  conv_lhs => rw [← bom_image_X]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ici hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ici fun r hr => ?_
  have : 0 ≤ Real.sinh r := Real.sinh_nonneg_iff.2 hr
  rw [abs_of_nonneg (by positivity)]

/-!
### Mass and moment as radial integrals
-/

/-- The hyperbolic bridge integrand on `x' ≥ 0`. -/
theorem bom_kernel_prod {D0 T s x₀ x' : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hsT : s < T) :
    ENNReal.ofReal (lbkKernelX D0 s x₀ x') * ENNReal.ofReal (lbkKernelX D0 (T - s) x' 0) =
      (Ici 0).indicator (fun x' => ENNReal.ofReal (lbkHypRadial (D0 * s / 2) x₀ x' *
        lbkHypRadial (D0 * (T - s) / 2) x' 0)) x' := by
  have hu : 0 < T - s := sub_pos.2 hsT
  by_cases hx : 0 ≤ x'
  · rw [indicator_of_mem (show x' ∈ Ici 0 from hx), lbk_kernelX_eq hs hx,
      lbk_kernelX_eq hu le_rfl, ENNReal.ofReal_mul (lbk_hypRadial_nonneg (by positivity) _ _)]
  · rw [indicator_of_notMem (show x' ∉ Ici 0 from hx)]
    simp [lbkKernelX, hx]

theorem bom_mass_eq {D0 T s : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hsT : s < T) (x₀ : ℝ) :
    bopXMass D0 x₀ T s = bomRadialInt 1 (fun r => lbkHypRadial (D0 * s / 2) x₀ (bomX r) *
      lbkHypRadial (D0 * (T - s) / 2) (bomX r) 0) := by
  unfold bopXMass
  simp_rw [bom_kernel_prod (x₀ := x₀) hD0 hs hsT]
  rw [lintegral_indicator measurableSet_Ici, bom_lintegral_Ici_X]
  unfold bomRadialInt
  simp only [Pi.one_apply, one_mul]

theorem bom_moment_eq {D0 T s : ℝ} (hD0 : 0 < D0) (hs : 0 < s) (hsT : s < T) (x₀ : ℝ) :
    bopXMoment D0 x₀ T s = bomRadialInt (fun r => ENNReal.ofReal (bomX r))
      (fun r => lbkHypRadial (D0 * s / 2) x₀ (bomX r) *
        lbkHypRadial (D0 * (T - s) / 2) (bomX r) 0) := by
  unfold bopXMoment
  simp_rw [bom_kernel_prod (x₀ := x₀) hD0 hs hsT]
  have h : ∀ x' : ℝ, ENNReal.ofReal x' * (Ici 0).indicator (fun x' =>
      ENNReal.ofReal (lbkHypRadial (D0 * s / 2) x₀ x' * lbkHypRadial (D0 * (T - s) / 2) x' 0)) x' =
      (Ici 0).indicator (fun x' => ENNReal.ofReal x' *
        ENNReal.ofReal (lbkHypRadial (D0 * s / 2) x₀ x' * lbkHypRadial (D0 * (T - s) / 2) x' 0))
        x' := by
    intro x'
    by_cases hx : x' ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  simp_rw [h]
  rw [lintegral_indicator measurableSet_Ici, bom_lintegral_Ici_X]
  rfl

/-!
### Monotonicity and scaling of the radial integral
-/

theorem bom_radialInt_mono {g : ℝ → ℝ≥0∞} {k k' : ℝ → ℝ} (h : ∀ r, 0 ≤ r → k r ≤ k' r) :
    bomRadialInt g k ≤ bomRadialInt g k' := by
  unfold bomRadialInt
  refine setLIntegral_mono' measurableSet_Ici fun r hr => ?_
  gcongr
  exact h r hr

theorem bom_radialInt_const_mul (g : ℝ → ℝ≥0∞) (k : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    bomRadialInt g (fun r => c * k r) = ENNReal.ofReal c * bomRadialInt g k := by
  unfold bomRadialInt
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun r => ?_
  rw [ENNReal.ofReal_mul hc]
  ring

/-!
### The comparison kernels in planar coordinates
-/

theorem bom_euclRadial_pole {b : ℝ} (r : ℝ) :
    bomEuclRadial b r 0 = 2 / (4 * π * b) * Real.sqrt (lbkSdivSinh r) *
      (2 * π * Real.exp (-r ^ 2 / (4 * b))) := by
  unfold bomEuclRadial
  rw [bom_sdivSinh_zero, mul_one]
  have h : ∀ φ : ℝ, Real.exp (-(r ^ 2 + (0 : ℝ) ^ 2 - 2 * r * 0 * Real.cos φ) / (4 * b)) =
      Real.exp (-r ^ 2 / (4 * b)) := by
    intro φ
    congr 1
    ring
  simp_rw [h]
  rw [setIntegral_const, Measure.real, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

/-- The positive constant relating the radial and planar integrals. -/
def bomK1 (a b r₀ : ℝ) : ℝ :=
  2 / (4 * π * a) * (2 / (4 * π * b)) * (2 * π) * Real.sqrt (lbkSdivSinh r₀) / 2

theorem bom_K1_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r₀ : ℝ) : 0 ≤ bomK1 a b r₀ := by
  unfold bomK1
  have := Real.pi_pos
  positivity

/-- Pointwise: `(sinh r'/2) E_a(r₀,r') E_b(r',0) = K₁ r' I(r') e^{-r'²/(4b)}`. -/
theorem bom_eucl_prod_eq (a b r₀ r' : ℝ) :
    Real.sinh r' / 2 * (bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) =
      bomK1 a b r₀ * (r' * ((∫ φ in Ioo (-π) π,
        Real.exp (-(r₀ ^ 2 + r' ^ 2 - 2 * r₀ * r' * Real.cos φ) / (4 * a))) *
          Real.exp (-r' ^ 2 / (4 * b)))) := by
  rw [bom_euclRadial_pole]
  unfold bomEuclRadial bomK1
  have hσ0 : 0 ≤ lbkSdivSinh r₀ := (lbk_sdivSinh_pos r₀).le
  have hσ1 : 0 ≤ lbkSdivSinh r' := (lbk_sdivSinh_pos r').le
  rw [Real.sqrt_mul hσ0]
  have hsq := Real.mul_self_sqrt hσ1
  have hs := bom_sdivSinh_mul_sinh r'
  set I := ∫ φ in Ioo (-π) π, Real.exp (-(r₀ ^ 2 + r' ^ 2 - 2 * r₀ * r' * Real.cos φ) / (4 * a))
  set e := Real.exp (-r' ^ 2 / (4 * b))
  set K := 2 / (4 * π * a) * (2 / (4 * π * b)) * (2 * π) * Real.sqrt (lbkSdivSinh r₀) / 2
  linear_combination (K * I * e * Real.sinh r') * hsq + (K * I * e) * hs

theorem bom_W_polar (a b r₀ r φ : ℝ) :
    bomW a b r₀ (r * Real.cos φ, r * Real.sin φ) =
      Real.exp (-(r₀ ^ 2 + r ^ 2 - 2 * r₀ * r * Real.cos φ) / (4 * a)) *
        Real.exp (-r ^ 2 / (4 * b)) := by
  unfold bomW
  have h := Real.sin_sq_add_cos_sq φ
  rw [show (r * Real.cos φ - r₀) ^ 2 + (r * Real.sin φ) ^ 2 =
      r₀ ^ 2 + r ^ 2 - 2 * r₀ * r * Real.cos φ by linear_combination r ^ 2 * h,
    show (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 by linear_combination r ^ 2 * h]

/-- **Radial integral of the comparison kernels = planar bridge integral.** For a measurable
radial weight `G` with radial profile `γ`, `∫_{r' ≥ 0} (sinh r'/2) γ(r') E_a(r₀,r') E_b(r',0) dr'
= K₁ ∫_{ℝ²} G(q) W(q) dq`. -/
theorem bom_radialInt_eucl {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (G : ℝ × ℝ → ℝ≥0∞)
    (hG : Measurable G) (γ : ℝ → ℝ≥0∞)
    (hγ : ∀ r : ℝ, 0 < r → ∀ φ : ℝ, G (r * Real.cos φ, r * Real.sin φ) = γ r) :
    bomRadialInt γ (fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) =
      ENNReal.ofReal (bomK1 a b r₀) * ∫⁻ q, G q * ENNReal.ofReal (bomW a b r₀ q) := by
  have hK := bom_K1_nonneg ha hb r₀
  have hWm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (bomW a b r₀ (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :=
    ((bom_W_continuous a b r₀).comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 * Real.cos p.2, p.1 * Real.sin p.2))).measurable.ennreal_ofReal
  -- Step 1: pointwise identity, and `Ici 0 ↦ Ioi 0`.
  have h1 : bomRadialInt γ (fun r' => bomEuclRadial a r₀ r' * bomEuclRadial b r' 0) =
      ENNReal.ofReal (bomK1 a b r₀) * ∫⁻ r' in Ioi (0 : ℝ), ENNReal.ofReal r' *
        (γ r' * ENNReal.ofReal ((∫ φ in Ioo (-π) π,
          Real.exp (-(r₀ ^ 2 + r' ^ 2 - 2 * r₀ * r' * Real.cos φ) / (4 * a))) *
            Real.exp (-r' ^ 2 / (4 * b)))) := by
    unfold bomRadialInt
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_congr Ioi_ae_eq_Ici.symm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hsh : 0 ≤ Real.sinh r / 2 := by
      have := Real.sinh_nonneg_iff.2 hr0
      positivity
    have hI : 0 ≤ (∫ φ in Ioo (-π) π,
        Real.exp (-(r₀ ^ 2 + r ^ 2 - 2 * r₀ * r * Real.cos φ) / (4 * a))) :=
      setIntegral_nonneg measurableSet_Ioo fun φ _ => (Real.exp_pos _).le
    calc ENNReal.ofReal (Real.sinh r / 2) *
          (γ r * ENNReal.ofReal (bomEuclRadial a r₀ r * bomEuclRadial b r 0))
        = γ r * ENNReal.ofReal (Real.sinh r / 2 *
            (bomEuclRadial a r₀ r * bomEuclRadial b r 0)) := by
          rw [ENNReal.ofReal_mul hsh]
          ring
      _ = _ := by
          rw [bom_eucl_prod_eq, ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hr0]
          ring
  -- Step 2: the angle integral as a lower integral, `γ` as `G` in polar coordinates.
  have h2 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal r *
      (γ r * ENNReal.ofReal ((∫ φ in Ioo (-π) π,
        Real.exp (-(r₀ ^ 2 + r ^ 2 - 2 * r₀ * r * Real.cos φ) / (4 * a))) *
          Real.exp (-r ^ 2 / (4 * b)))) =
      ∫⁻ φ in Ioo (-π) π, ENNReal.ofReal r * (G (r * Real.cos φ, r * Real.sin φ) *
        ENNReal.ofReal (bomW a b r₀ (r * Real.cos φ, r * Real.sin φ))) := by
    intro r hr
    have hI : ENNReal.ofReal ((∫ φ in Ioo (-π) π,
        Real.exp (-(r₀ ^ 2 + r ^ 2 - 2 * r₀ * r * Real.cos φ) / (4 * a))) *
          Real.exp (-r ^ 2 / (4 * b))) =
        ∫⁻ φ in Ioo (-π) π, ENNReal.ofReal (bomW a b r₀ (r * Real.cos φ, r * Real.sin φ)) := by
      rw [← integral_mul_const, ofReal_integral_eq_lintegral_ofReal
        ((bom_eucl_integrableOn a r₀ r).mul_const _)
        (ae_of_all _ fun φ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)]
      refine lintegral_congr fun φ => ?_
      rw [bom_W_polar]
    have hm1 : Measurable fun φ : ℝ =>
        ENNReal.ofReal (bomW a b r₀ (r * Real.cos φ, r * Real.sin φ)) :=
      ((bom_W_continuous a b r₀).comp (by fun_prop : Continuous fun φ : ℝ =>
        (r * Real.cos φ, r * Real.sin φ))).measurable.ennreal_ofReal
    rw [hI, ← lintegral_const_mul _ hm1, ← lintegral_const_mul _ (hm1.const_mul (γ r))]
    refine lintegral_congr fun φ => ?_
    rw [hγ r hr φ]
  -- Step 3: Tonelli on `Ioi 0 ×ˢ Ioo (-π) π` and polar coordinates.
  rw [h1, setLIntegral_congr_fun measurableSet_Ioi h2]
  congr 1
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
      (G (p.1 * Real.cos p.2, p.1 * Real.sin p.2) *
        ENNReal.ofReal (bomW a b r₀ (p.1 * Real.cos p.2, p.1 * Real.sin p.2))) :=
    measurable_fst.ennreal_ofReal.mul ((hG.comp (by fun_prop : Continuous fun p : ℝ × ℝ =>
      (p.1 * Real.cos p.2, p.1 * Real.sin p.2)).measurable).mul hWm)
  rw [← lintegral_comp_polarCoord_symm (fun q => G q * ENNReal.ofReal (bomW a b r₀ q)),
    polarCoord_target]
  simp only [polarCoord_symm_apply, smul_eq_mul]
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hmeas.aemeasurable]

end BlockBand.Endpoints
