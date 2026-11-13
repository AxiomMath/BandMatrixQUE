module

public import BlockBand.Diffusion.Kernel.McKeanDefs
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Isometry invariance of the angular law

Headline `mk_lintegral_hypCos`: for `x ≥ 0` and every measurable `g : ℝ → ℝ≥0∞`,
`∫_{(0,∞)} ∫_{(-π,π)} g(mkHypCos x x' θ) dθ dx' = π ∫_{(1,∞)} g(c) dc`
(Lebesgue measures, lower integrals). So the law of `cosh d(z, z')` under `dx' dθ` does not depend
on the start `x`; this is the hyperbolic isometry invariance of the area measure, proved without
hyperbolic geometry:

1. polar coordinates `p = r(cos θ, sin θ)` and `x' = (√(1+r²) - 1)/2` turn `dx' dθ` into
   `dp / (2√(1+|p|²))` and `mkHypCos x x' θ` into `cosh ρ √(1+|p|²) - sinh ρ p₁`,
   `ρ = arcosh(1+2x)` (`mk_lintegral_polar`);
2. for fixed `p₂ = y`, the substitution `p₁ = √(1+y²) sinh v` makes the weight `dv/2` and the
   argument `√(1+y²) cosh(v - ρ)`; a translation removes `ρ` (`mk_lintegral_boost`);
3. at `x = 0` the left side is `2π ∫_0^∞ g(1+2x') dx' = π ∫_1^∞ g`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-- The boost step. -/
theorem mk_lintegral_boost (ρ y : ℝ) {g : ℝ → ℝ≥0∞} :
    ∫⁻ p : ℝ, ENNReal.ofReal (2 * Real.sqrt (1 + p ^ 2 + y ^ 2))⁻¹ *
        g (Real.cosh ρ * Real.sqrt (1 + p ^ 2 + y ^ 2) - Real.sinh ρ * p) =
      ∫⁻ u : ℝ, ENNReal.ofReal (1 / 2) * g (Real.sqrt (1 + y ^ 2) * Real.cosh u) := by
  set m := Real.sqrt (1 + y ^ 2) with hm
  have hm0 : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hmsq : m ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hsurj : (fun v => m * Real.sinh v) '' univ = univ := by
    rw [image_univ, eq_univ_iff_forall]
    intro p
    obtain ⟨v, hv⟩ := Real.sinh_surjective (p / m)
    exact ⟨v, by simp only [hv]; field_simp⟩
  have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ)
    (f := fun v => m * Real.sinh v) (f' := fun v => m * Real.cosh v) MeasurableSet.univ
    (fun v _ => ((Real.hasDerivAt_sinh v).const_mul m).hasDerivWithinAt)
    (fun a _ b _ h => Real.sinh_injective (mul_left_cancel₀ hm0.ne' h))
    (fun p => ENNReal.ofReal (2 * Real.sqrt (1 + p ^ 2 + y ^ 2))⁻¹ *
        g (Real.cosh ρ * Real.sqrt (1 + p ^ 2 + y ^ 2) - Real.sinh ρ * p))
  rw [hsurj, Measure.restrict_univ] at him
  rw [him, ← lintegral_sub_right_eq_self
    (fun u => ENNReal.ofReal (1 / 2) * g (m * Real.cosh u)) ρ]
  refine lintegral_congr fun v => ?_
  have hc : 0 < Real.cosh v := Real.cosh_pos v
  have hsq : Real.sqrt (1 + (m * Real.sinh v) ^ 2 + y ^ 2) = m * Real.cosh v := by
    rw [show 1 + (m * Real.sinh v) ^ 2 + y ^ 2 = (m * Real.cosh v) ^ 2 by
      rw [mul_pow, mul_pow, Real.cosh_sq, hmsq]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, abs_of_pos (by positivity), ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    Real.cosh_sub]
  congr 2
  · field_simp
  · ring

/-- The radial reparametrisation `x' = (√(1+r²) - 1)/2`. -/
def mkRad (r : ℝ) : ℝ := (Real.sqrt (1 + r ^ 2) - 1) / 2

theorem mk_rad_image : mkRad '' Ioi (0 : ℝ) = Ioi 0 := by
  ext x'
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr0 : 0 < r := hr
    have : 1 < Real.sqrt (1 + r ^ 2) := by
      rw [Real.lt_sqrt (by norm_num)]; nlinarith
    show 0 < mkRad r
    unfold mkRad; linarith
  · intro hx
    have hx0 : 0 < x' := hx
    have : 0 < Real.sqrt (x' * (1 + x')) := Real.sqrt_pos.2 (by positivity)
    refine ⟨2 * Real.sqrt (x' * (1 + x')), mem_Ioi.2 (by positivity), ?_⟩
    unfold mkRad
    rw [mul_pow, Real.sq_sqrt (by positivity),
      show 1 + 2 ^ 2 * (x' * (1 + x')) = (1 + 2 * x') ^ 2 by ring,
      Real.sqrt_sq (by linarith)]
    ring

theorem mk_rad_hasDerivAt (r : ℝ) :
    HasDerivAt mkRad (r / (2 * Real.sqrt (1 + r ^ 2))) r := by
  have h1 : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add 1)
  have h2 := ((h1.sqrt (by positivity)).sub_const 1).div_const 2
  convert h2 using 1
  · rfl
  · ring

theorem mk_rad_injOn : InjOn mkRad (Ioi 0) := by
  intro a ha b hb h
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := le_of_lt hb
  unfold mkRad at h
  have h' : Real.sqrt (1 + a ^ 2) = Real.sqrt (1 + b ^ 2) := by linarith
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h'
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

theorem mk_hypCos_rad {x : ℝ} (hx : 0 ≤ x) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    mkHypCos x (mkRad r) θ = Real.cosh (Real.arcosh (1 + 2 * x)) * Real.sqrt (1 + r ^ 2) -
      Real.sinh (Real.arcosh (1 + 2 * x)) * (r * Real.cos θ) := by
  have h1 : (1 : ℝ) ≤ 1 + 2 * x := by linarith
  have hs : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hrad : mkRad r * (1 + mkRad r) = (r / 2) ^ 2 := by
    unfold mkRad; nlinarith [hs]
  rw [Real.cosh_arcosh h1, Real.sinh_arcosh h1]
  unfold mkHypCos
  rw [show (1 + 2 * x) ^ 2 - 1 = 2 ^ 2 * (x * (1 + x)) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
    hrad, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ r / 2)]
  unfold mkRad
  ring

/-- The planar weight `(2√(1+|p|²))⁻¹` and boosted cosine. -/
def mkPlanar (ρ : ℝ) (g : ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * Real.sqrt (1 + p.1 ^ 2 + p.2 ^ 2))⁻¹ *
    g (Real.cosh ρ * Real.sqrt (1 + p.1 ^ 2 + p.2 ^ 2) - Real.sinh ρ * p.1)

theorem mk_planar_measurable (ρ : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (mkPlanar ρ g) := by
  unfold mkPlanar
  refine Measurable.mul ?_ (hg.comp ?_) <;> fun_prop

theorem mk_lintegral_polar {x : ℝ} (hx : 0 ≤ x) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x' in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, g (mkHypCos x x' θ) =
      ∫⁻ p : ℝ × ℝ, mkPlanar (Real.arcosh (1 + 2 * x)) g p := by
  set ρ := Real.arcosh (1 + 2 * x)
  have hL := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun r _ => (mk_rad_hasDerivAt r).hasDerivWithinAt) mk_rad_injOn
      (fun x' => ∫⁻ θ in Ioo (-π) π, g (mkHypCos x x' θ))
  rw [mk_rad_image] at hL
  rw [hL, ← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ ?_]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hsq : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.2 (by positivity)
    simp_rw [polarCoord_symm_apply, mkPlanar, smul_eq_mul]
    have hpol : ∀ θ : ℝ, (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := fun θ => by
      have := Real.cos_sq_add_sin_sq θ; nlinarith
    simp_rw [add_assoc, hpol]
    simp_rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos (by positivity)]
    congr 1
    refine lintegral_congr fun θ => ?_
    rw [mk_hypCos_rad hx hr0.le, mul_assoc]
  · simp_rw [polarCoord_symm_apply]
    exact (measurable_fst.ennreal_ofReal.smul ((mk_planar_measurable ρ hg).comp
      (by fun_prop))).aemeasurable

theorem mk_lintegral_planar (ρ : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p : ℝ × ℝ, mkPlanar ρ g p =
      ∫⁻ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (1 / 2) * g (Real.sqrt (1 + y ^ 2) * Real.cosh u) := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ (mk_planar_measurable ρ hg).aemeasurable]
  exact lintegral_congr fun y => mk_lintegral_boost ρ y

/-- **Isometry invariance of the angular law.** For `x ≥ 0` and measurable `g ≥ 0`,
`∫_0^∞ ∫_{-π}^{π} g(cosh d(x, x', θ)) dθ dx' = π ∫_1^∞ g(c) dc`, independently of `x`. -/
theorem mk_lintegral_hypCos {x : ℝ} (hx : 0 ≤ x) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x' in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π, g (mkHypCos x x' θ) =
      ENNReal.ofReal π * ∫⁻ c in Ioi (1 : ℝ), g c := by
  have hz : Real.arcosh (1 + 2 * 0) = 0 := by simp
  rw [mk_lintegral_polar hx hg, mk_lintegral_planar _ hg, ← mk_lintegral_planar 0 hg, ← hz,
    ← mk_lintegral_polar le_rfl hg]
  have h0 : ∀ x' θ : ℝ, mkHypCos 0 x' θ = 1 + 2 * x' := fun x' θ => by simp [mkHypCos]
  simp_rw [h0, setLIntegral_const, Real.volume_Ioo, sub_neg_eq_add]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ))
    (f := fun x' => 1 + 2 * x') (f' := fun _ => 2) measurableSet_Ioi
    (fun x' _ => (((hasDerivAt_id x').const_mul 2).const_add 1).hasDerivWithinAt.congr_deriv
      (by simp)) (fun a _ b _ h => by simpa using h) g
  have himg : (fun x' : ℝ => 1 + 2 * x') '' Ioi 0 = Ioi 1 := by
    ext c; constructor
    · rintro ⟨x', hx', rfl⟩; exact mem_Ioi.2 (by have := mem_Ioi.1 hx'; linarith)
    · intro hc; exact ⟨(c - 1) / 2, mem_Ioi.2 (by have := mem_Ioi.1 hc; linarith), by ring⟩
  rw [himg, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_two] at him
  rw [him, ← mul_assoc, mul_comm, ← ENNReal.ofReal_mul Real.pi_pos.le]
  congr 1
  ring_nf

end BlockBand.Diffusion
