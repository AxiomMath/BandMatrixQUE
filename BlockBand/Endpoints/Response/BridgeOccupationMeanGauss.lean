module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Planar Gaussian moments of `(cosh ‖v‖ - 1)/2` (bridge-mean bounds, Gaussian part)

With `X(v) = (cosh ‖v‖ - 1)/2` (`bomPlanarX`, Euclidean norm written out on `ℝ × ℝ`) and the
unnormalised planar bridge weight
`W(q) = exp(-‖q - r₀e₁‖²/(4a)) exp(-‖q‖²/(4b))` (`bomW`, Lebesgue measure on `ℝ × ℝ`):
* `bom_planarW_lower`: `X(m e₁) ∫ W ≤ ∫ X W`, `m = b r₀/(a+b)` (in the paper by
  Jensen for the convex `X`; here by symmetrisation `w ↦ -w` of the centred Gaussian and
  `cosh A + cosh B ≥ 2 cosh((A+B)/2)`);
* `bom_planarW_upper`: `∫ X W ≤ e^{4σ² + m} ∫ W`, `σ² = ab/(a+b)` (by a bounded exponential moment
  of the radius of a centred planar Gaussian with covariance `≤ κ`).
Completing the square, `W(q) = e^{-r₀²/(4(a+b))} exp(-‖q - m e₁‖²/(4σ²))` (`bom_W_eq`).
All statements are for every `a, b > 0`, `r₀ ≥ 0`; constants are explicit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Real
open scoped ENNReal

/-- The planar radial observable `X(q) = (cosh ‖q‖ - 1)/2` (Euclidean norm on `ℝ × ℝ`). -/
def bomPlanarX (q : ℝ × ℝ) : ℝ := (Real.cosh (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) - 1) / 2

/-- The centred planar Gaussian weight `exp(-‖w‖²/(4σ²))`. -/
def bomGauss (σ2 : ℝ) (w : ℝ × ℝ) : ℝ := Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * σ2))

/-- The unnormalised planar bridge weight `exp(-‖q - r₀e₁‖²/(4a)) exp(-‖q‖²/(4b))`. -/
def bomW (a b r₀ : ℝ) (q : ℝ × ℝ) : ℝ :=
  Real.exp (-((q.1 - r₀) ^ 2 + q.2 ^ 2) / (4 * a)) * Real.exp (-(q.1 ^ 2 + q.2 ^ 2) / (4 * b))

theorem bom_planarX_nonneg (q : ℝ × ℝ) : 0 ≤ bomPlanarX q := by
  unfold bomPlanarX
  linarith [Real.one_le_cosh (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))]

theorem bom_planarX_continuous : Continuous bomPlanarX := by
  unfold bomPlanarX
  fun_prop

theorem bom_gauss_continuous (σ2 : ℝ) : Continuous (bomGauss σ2) := by
  unfold bomGauss
  fun_prop

theorem bom_W_continuous (a b r₀ : ℝ) : Continuous (bomW a b r₀) := by
  unfold bomW
  fun_prop

/-- `cosh A + cosh B ≥ 2 cosh m` when `A + B ≥ 2m ≥ 0`. -/
theorem bom_cosh_add_cosh_ge {A B m : ℝ} (hm : 0 ≤ m) (h : 2 * m ≤ A + B) :
    2 * Real.cosh m ≤ Real.cosh A + Real.cosh B := by
  have hid : Real.cosh A + Real.cosh B =
      2 * Real.cosh ((A + B) / 2) * Real.cosh ((A - B) / 2) := by
    have h1 := Real.cosh_add ((A + B) / 2) ((A - B) / 2)
    have h2 := Real.cosh_sub ((A + B) / 2) ((A - B) / 2)
    rw [show (A + B) / 2 + (A - B) / 2 = A by ring] at h1
    rw [show (A + B) / 2 - (A - B) / 2 = B by ring] at h2
    rw [h1, h2]
    ring
  have hc1 : 1 ≤ Real.cosh ((A - B) / 2) := Real.one_le_cosh _
  have hcm : Real.cosh m ≤ Real.cosh ((A + B) / 2) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hm, abs_of_nonneg (by linarith)]
    linarith
  have hpos : 0 < Real.cosh ((A + B) / 2) := Real.cosh_pos _
  rw [hid]
  nlinarith

/-- Pointwise symmetrisation: `X(m e₁ + w) + X(m e₁ - w) ≥ 2 X(m e₁)`. -/
theorem bom_planarX_sym {m : ℝ} (hm : 0 ≤ m) (w : ℝ × ℝ) :
    2 * ((Real.cosh m - 1) / 2) ≤ bomPlanarX (w + (m, 0)) + bomPlanarX (-w + (m, 0)) := by
  unfold bomPlanarX
  simp only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, add_zero]
  have hA : |w.1 + m| ≤ Real.sqrt ((w.1 + m) ^ 2 + w.2 ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg w.2])
  have hB : |-w.1 + m| ≤ Real.sqrt ((-w.1 + m) ^ 2 + (-w.2) ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg w.2])
  have h := bom_cosh_add_cosh_ge (A := Real.sqrt ((w.1 + m) ^ 2 + w.2 ^ 2))
    (B := Real.sqrt ((-w.1 + m) ^ 2 + (-w.2) ^ 2)) hm
    (by linarith [le_abs_self (w.1 + m), le_abs_self (-w.1 + m)])
  linarith

/-- **Symmetrisation lower bound**: for an even weight `h`, `X(m e₁) ∫ h ≤ ∫ X(· + m e₁) h`. -/
theorem bom_planar_lower {m : ℝ} (hm : 0 ≤ m) (h : ℝ × ℝ → ℝ≥0∞) (hhm : Measurable h)
    (hh : ∀ w, h (-w) = h w) :
    ENNReal.ofReal ((Real.cosh m - 1) / 2) * ∫⁻ w, h w ≤
      ∫⁻ w, ENNReal.ofReal (bomPlanarX (w + (m, 0))) * h w := by
  set L := ∫⁻ w, ENNReal.ofReal (bomPlanarX (w + (m, 0))) * h w with hLdef
  have hL' : ∫⁻ w, ENNReal.ofReal (bomPlanarX (-w + (m, 0))) * h w = L := by
    rw [hLdef, ← lintegral_neg_eq_self (fun w => ENNReal.ofReal (bomPlanarX (w + (m, 0))) * h w)]
    simp only [hh]
  have hmeas : Measurable fun w : ℝ × ℝ => ENNReal.ofReal (bomPlanarX (w + (m, 0))) * h w :=
    ((bom_planarX_continuous.comp (continuous_id.add continuous_const)).measurable.ennreal_ofReal).mul
      hhm
  have h2 : 2 * (ENNReal.ofReal ((Real.cosh m - 1) / 2) * ∫⁻ w, h w) ≤ 2 * L := by
    calc 2 * (ENNReal.ofReal ((Real.cosh m - 1) / 2) * ∫⁻ w, h w)
        = ∫⁻ w, ENNReal.ofReal (2 * ((Real.cosh m - 1) / 2)) * h w := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat, mul_assoc]
      _ ≤ ∫⁻ w, (ENNReal.ofReal (bomPlanarX (w + (m, 0))) * h w +
            ENNReal.ofReal (bomPlanarX (-w + (m, 0))) * h w) := by
          refine lintegral_mono fun w => ?_
          rw [← add_mul, ← ENNReal.ofReal_add (bom_planarX_nonneg _) (bom_planarX_nonneg _)]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (bom_planarX_sym hm w)) _
      _ = 2 * L := by
          rw [lintegral_add_left' hmeas.aemeasurable, hL', two_mul]
  exact (ENNReal.mul_le_mul_iff_right (a := 2) (by norm_num) (by norm_num)).1 h2

/-- The one-dimensional Gaussian lower integral `∫⁻ e^{-βt²} = √(π/β)`. -/
theorem bom_lintegral_gauss1 {β : ℝ} (hβ : 0 < β) :
    ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-β * t ^ 2)) = ENNReal.ofReal (Real.sqrt (π / β)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hβ)
    (ae_of_all _ fun t => (Real.exp_pos _).le), integral_gaussian]

/-- The planar Gaussian lower integral `∫⁻ exp(-‖w‖²/c) = πc`. -/
theorem bom_lintegral_gauss2 {c : ℝ} (hc : 0 < c) :
    ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / c)) = ENNReal.ofReal (π * c) := by
  have hβ : 0 < 1 / c := by positivity
  have hpt : ∀ w : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / c)) =
      ENNReal.ofReal (Real.exp (-(1 / c) * w.1 ^ 2)) *
        ENNReal.ofReal (Real.exp (-(1 / c) * w.2 ^ 2)) := by
    intro w
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hpt]
  rw [Measure.volume_eq_prod,
    lintegral_prod_mul (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-(1 / c) * t ^ 2)))
      (g := fun t : ℝ => ENNReal.ofReal (Real.exp (-(1 / c) * t ^ 2))) (by fun_prop) (by fun_prop),
    bom_lintegral_gauss1 hβ, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    Real.mul_self_sqrt (by positivity)]
  congr 1
  field_simp

/-- Exponential moment of the centred Gaussian: `X(w + m e₁) g(w) ≤ ½ e^{4σ²+m} e^{-‖w‖²/(8σ²)}`. -/
theorem bom_planarX_gauss_le {m σ2 : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ2) (w : ℝ × ℝ) :
    bomPlanarX (w + (m, 0)) * bomGauss σ2 w ≤
      Real.exp (4 * σ2 + m) / 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (8 * σ2)) := by
  unfold bomPlanarX bomGauss
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  set A := Real.sqrt ((w.1 + m) ^ 2 + w.2 ^ 2) with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA1 : A ≤ |w.1| + |w.2| + m := by
    rw [hAdef, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h1 : (w.1 + m) ^ 2 ≤ (|w.1| + m) ^ 2 := by
      have : |w.1 + m| ≤ |w.1| + m := by
        calc |w.1 + m| ≤ |w.1| + |m| := abs_add_le _ _
          _ = |w.1| + m := by rw [abs_of_nonneg hm]
      rw [← sq_abs (w.1 + m)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [abs_nonneg w.1, abs_nonneg w.2, sq_abs w.2, mul_nonneg (abs_nonneg w.2)
      (add_nonneg (abs_nonneg w.1) hm)]
  have hamgm : ∀ t : ℝ, |t| ≤ t ^ 2 / (8 * σ2) + 2 * σ2 := by
    intro t
    have h8 : 0 < 8 * σ2 := by positivity
    rw [div_add' _ _ _ h8.ne', le_div_iff₀ h8]
    nlinarith [sq_nonneg (|t| - 4 * σ2), sq_abs t]
  have hA2 : A ≤ m + 4 * σ2 + (w.1 ^ 2 + w.2 ^ 2) / (8 * σ2) := by
    have := hamgm w.1
    have := hamgm w.2
    have : (w.1 ^ 2 + w.2 ^ 2) / (8 * σ2) = w.1 ^ 2 / (8 * σ2) + w.2 ^ 2 / (8 * σ2) := add_div _ _ _
    linarith
  have hcosh : (Real.cosh A - 1) / 2 ≤ Real.exp A / 2 := by
    rw [Real.cosh_eq]
    have : Real.exp (-A) ≤ Real.exp A := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_pos (-A)]
  have hX0 : 0 ≤ (Real.cosh A - 1) / 2 := by linarith [Real.one_le_cosh A]
  calc (Real.cosh A - 1) / 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * σ2))
      ≤ Real.exp A / 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * σ2)) := by gcongr
    _ ≤ Real.exp (m + 4 * σ2 + (w.1 ^ 2 + w.2 ^ 2) / (8 * σ2)) / 2 *
          Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (4 * σ2)) := by gcongr
    _ = Real.exp (4 * σ2 + m) / 2 * Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (8 * σ2)) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
        congr 2
        field_simp
        ring

/-- **Exponential-moment upper bound**: `∫ X(· + m e₁) g ≤ e^{4σ²+m} ∫ g`. -/
theorem bom_planar_upper {m σ2 : ℝ} (hm : 0 ≤ m) (hσ : 0 < σ2) :
    ∫⁻ w, ENNReal.ofReal (bomPlanarX (w + (m, 0))) * ENNReal.ofReal (bomGauss σ2 w) ≤
      ENNReal.ofReal (Real.exp (4 * σ2 + m)) * ∫⁻ w, ENNReal.ofReal (bomGauss σ2 w) := by
  have h8 : (0 : ℝ) < 8 * σ2 := by positivity
  have h4 : (0 : ℝ) < 4 * σ2 := by positivity
  calc ∫⁻ w, ENNReal.ofReal (bomPlanarX (w + (m, 0))) * ENNReal.ofReal (bomGauss σ2 w)
      ≤ ∫⁻ w : ℝ × ℝ, ENNReal.ofReal (Real.exp (4 * σ2 + m) / 2) *
          ENNReal.ofReal (Real.exp (-(w.1 ^ 2 + w.2 ^ 2) / (8 * σ2))) := by
        refine lintegral_mono fun w => ?_
        rw [← ENNReal.ofReal_mul (bom_planarX_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (bom_planarX_gauss_le hm hσ w)
    _ = ENNReal.ofReal (Real.exp (4 * σ2 + m)) * ∫⁻ w, ENNReal.ofReal (bomGauss σ2 w) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, bom_lintegral_gauss2 h8]
        unfold bomGauss
        rw [bom_lintegral_gauss2 h4, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Completing the square: `W(q) = e^{-r₀²/(4(a+b))} g_{σ²}(q - m e₁)`, `m = b r₀/(a+b)`,
`σ² = ab/(a+b)`. -/
theorem bom_W_eq {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (q : ℝ × ℝ) :
    bomW a b r₀ q = Real.exp (-r₀ ^ 2 / (4 * (a + b))) *
      bomGauss (a * b / (a + b)) (q - (b * r₀ / (a + b), 0)) := by
  unfold bomW bomGauss
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Planar bridge lower bound** (Jensen step):
`X(m e₁) ∫ W ≤ ∫ X W`, `m = b r₀/(a+b)`. -/
theorem bom_planarW_lower {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r₀) :
    ENNReal.ofReal ((Real.cosh (b * r₀ / (a + b)) - 1) / 2) *
        ∫⁻ q, ENNReal.ofReal (bomW a b r₀ q) ≤
      ∫⁻ q, ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q) := by
  set m := b * r₀ / (a + b) with hmdef
  have hm : 0 ≤ m := by positivity
  set K := Real.exp (-r₀ ^ 2 / (4 * (a + b)))
  set σ2 := a * b / (a + b)
  have hW : ∀ w : ℝ × ℝ, bomW a b r₀ (w + (m, 0)) = K * bomGauss σ2 w := by
    intro w
    rw [bom_W_eq ha hb, add_sub_cancel_right]
  rw [← lintegral_add_right_eq_self (fun q => ENNReal.ofReal (bomW a b r₀ q)) (m, 0),
    ← lintegral_add_right_eq_self
      (fun q => ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q)) (m, 0)]
  simp only [hW]
  refine bom_planar_lower hm _ ?_ ?_
  · exact ((continuous_const.mul (bom_gauss_continuous σ2)).measurable).ennreal_ofReal
  · intro w
    unfold bomGauss
    simp only [Prod.fst_neg, Prod.snd_neg, neg_sq]

/-- **Planar bridge upper bound** (exponential moment):
`∫ X W ≤ e^{4σ² + m} ∫ W`, `σ² = ab/(a+b)`, `m = b r₀/(a+b)`. -/
theorem bom_planarW_upper {a b r₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ r₀) :
    ∫⁻ q, ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q) ≤
      ENNReal.ofReal (Real.exp (4 * (a * b / (a + b)) + b * r₀ / (a + b))) *
        ∫⁻ q, ENNReal.ofReal (bomW a b r₀ q) := by
  set m := b * r₀ / (a + b) with hmdef
  have hm : 0 ≤ m := by positivity
  set K := Real.exp (-r₀ ^ 2 / (4 * (a + b)))
  set σ2 := a * b / (a + b)
  have hσ : 0 < σ2 := by positivity
  have hW : ∀ w : ℝ × ℝ, bomW a b r₀ (w + (m, 0)) = K * bomGauss σ2 w := by
    intro w
    rw [bom_W_eq ha hb, add_sub_cancel_right]
  rw [← lintegral_add_right_eq_self (fun q => ENNReal.ofReal (bomW a b r₀ q)) (m, 0),
    ← lintegral_add_right_eq_self
      (fun q => ENNReal.ofReal (bomPlanarX q) * ENNReal.ofReal (bomW a b r₀ q)) (m, 0)]
  simp only [hW]
  have hK : 0 ≤ K := (Real.exp_pos _).le
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp_rw [mul_left_comm (ENNReal.ofReal (bomPlanarX _)) (ENNReal.ofReal K)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_left_comm]
  gcongr
  exact bom_planar_upper hm hσ

end BlockBand.Endpoints
