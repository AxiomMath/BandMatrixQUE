module

public import BlockBand.Critical.Herglotz.PoissonExp
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Matrix closing, boundary clause: the Cayley phase and the scalar Poisson kernel

Deterministic analysis; the only measure is the standard Cauchy law `Cauchy(0,1)` on `ℝ`. No
hypothesis is used.

* `pk w ζ = 2 Re (1 - wζ)⁻¹ - 1`, the scalar Poisson kernel `(1 - |wζ|²)/|1 - wζ|²` (`pk_eq`),
  nonnegative and bounded on `‖w‖ < 1`, `‖ζ‖ ≤ 1` (`pk_nonneg`, `abs_pk_le`).
* `integral_pk_mul_exp`: its Fourier coefficients in the phase of `w = ρe^{iφ}`,
  `∫₀^{2π} P(ρe^{iφ}ζ) e^{-inφ} dφ = 2π(ρζ)ⁿ` (`n ≥ 1`).
* `cay t = (t + i)/(t - i)`, the Cayley phase of a real point: unimodular, injective.
  `pk_cay_real`: `P(ρ c(t)) = r(t² + 1)/(t² + r²)` for `ρ = (r-1)/(r+1)` (tightness).
* `integral_cay_pow_cauchy`: `∫ c(t)ⁿ d Cauchy(0,1) = 0` for `n ≥ 1` (bounded Cauchy–Poisson
  formula `BlockBand.Critical.Collar.integral_standardCauchyWeight_smul_eq_of_analyticAt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open Complex MeasureTheory Filter
open scoped Real Topology ComplexConjugate NNReal
open CoareaNative.BlockBand (standardCauchyWeight)

theorem integral_exp_int_mul_I (m : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * π), cexp ((m : ℂ) * I * φ) = if m = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hm
  · subst hm; simp
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have : cexp ((m : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show (m : ℂ) * I * ((2 * π : ℝ) : ℂ) = m * (2 * π * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
    push_cast at this
    simp [this]

theorem norm_mul_exp_I (x : ℂ) (φ : ℝ) : ‖x * cexp (φ * I)‖ = ‖x‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Fourier coefficients of the geometric kernel `(1 - x e^{iφ})⁻¹`, `‖x‖ < 1`. -/
theorem integral_inv_one_sub_mul_exp {x : ℂ} (hx : ‖x‖ < 1) (m : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * π), (1 - x * cexp (φ * I))⁻¹ * cexp ((m : ℂ) * I * φ) =
      if m ≤ 0 then ((2 * π : ℝ) : ℂ) * x ^ (-m).toNat else 0 := by
  have hterm : ∀ (k : ℕ) (φ : ℝ), (x * cexp (φ * I)) ^ k * cexp ((m : ℂ) * I * φ) =
      x ^ k * cexp (((k + m : ℤ) : ℂ) * I * φ) := by
    intro k φ
    rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hsum : ∀ φ : ℝ, HasSum (fun k : ℕ => x ^ k * cexp (((k + m : ℤ) : ℂ) * I * φ))
      ((1 - x * cexp (φ * I))⁻¹ * cexp ((m : ℂ) * I * φ)) := by
    intro φ
    have h := (hasSum_geometric_of_norm_lt_one (ξ := x * cexp (φ * I))
      (by rw [norm_mul_exp_I]; exact hx)).mul_right
      (cexp ((m : ℂ) * I * φ))
    simpa only [hterm] using h
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 2 * π)
    (F := fun (k : ℕ) (φ : ℝ) => x ^ k * cexp (((k + m : ℤ) : ℂ) * I * φ))
    (f := fun φ : ℝ => (1 - x * cexp (φ * I))⁻¹ * cexp ((m : ℂ) * I * φ))
    (fun k _ => ‖x‖ ^ k)
    (fun k => (Continuous.aestronglyMeasurable (by fun_prop)))
    (fun k => Eventually.of_forall fun φ _ => by
      rw [norm_mul, norm_pow, mul_comm ((k + m : ℤ) : ℂ) I, mul_assoc,
        show (I * ((((k + m : ℤ) : ℂ)) * (φ : ℂ))) = ((((k + m : ℤ) : ℝ) * φ : ℝ) : ℂ) * I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one])
    (Eventually.of_forall fun φ _ => summable_geometric_of_lt_one (norm_nonneg _) hx)
    intervalIntegrable_const
    (Eventually.of_forall fun φ _ => hsum φ)
  have hval : ∀ k : ℕ, ∫ φ in (0 : ℝ)..(2 * π), x ^ k * cexp (((k + m : ℤ) : ℂ) * I * φ) =
      if (k : ℤ) + m = 0 then ((2 * π : ℝ) : ℂ) * x ^ k else 0 := by
    intro k
    rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
    split_ifs <;> ring
  simp only [hval] at hdom
  refine hdom.unique ?_
  split_ifs with hm
  · have hk : (((-m).toNat : ℕ) : ℤ) + m = 0 := by omega
    convert hasSum_single ((-m).toNat) (fun k hk' => ?_) using 1
    · simp only [hk, ite_true]
    · have : ¬ ((k : ℤ) + m = 0) := by omega
      simp only [this, ite_false]
  · convert hasSum_zero with k
    have : ¬ ((k : ℤ) + m = 0) := by omega
    simp only [this, ite_false]

theorem intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ φ in a..b, conj (f φ) = conj (∫ φ in a..b, f φ) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- The scalar Poisson kernel `2 Re (1 - wζ)⁻¹ - 1` (`= (1 - |wζ|²)/|1 - wζ|²`). -/
def pk (w ζ : ℂ) : ℝ := 2 * ((1 - w * ζ)⁻¹).re - 1

theorem pk_ofReal (w ζ : ℂ) :
    (pk w ζ : ℂ) = (1 - w * ζ)⁻¹ + conj ((1 - w * ζ)⁻¹) - 1 := by
  rw [Complex.add_conj, pk]; push_cast; ring

theorem continuous_inv_one_sub_mul_exp {x : ℂ} (hx : ‖x‖ < 1) :
    Continuous fun φ : ℝ => (1 - x * cexp (φ * I))⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun φ h => ?_
  have h1 : x * cexp (φ * I) = 1 := by linear_combination -h
  have := congrArg norm h1
  rw [norm_mul_exp_I, norm_one] at this
  linarith

/-- **Fourier coefficients of the scalar Poisson kernel**: for `‖ζ‖ ≤ 1`, `0 ≤ ρ < 1`, `n ≥ 1`,
`∫₀^{2π} P(ρe^{iφ}ζ) e^{-inφ} dφ = 2π (ρζ)^n`. -/
theorem integral_pk_mul_exp {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ∫ φ in (0 : ℝ)..(2 * π), (pk ((ρ : ℂ) * cexp (φ * I)) ζ : ℂ) * cexp (-(n : ℂ) * I * φ) =
      ((2 * π : ℝ) : ℂ) * ((ρ : ℂ) * ζ) ^ n := by
  set x : ℂ := (ρ : ℂ) * ζ
  have hx : ‖x‖ < 1 := by
    simp only [x, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0]
    calc ρ * ‖ζ‖ ≤ ρ * 1 := by gcongr
      _ < 1 := by linarith
  have hw : ∀ φ : ℝ, (1 - (ρ : ℂ) * cexp (φ * I) * ζ) = 1 - x * cexp (φ * I) := by
    intro φ; simp only [x]; ring
  set A : ℝ → ℂ := fun φ => (1 - x * cexp (φ * I))⁻¹
  have hA : Continuous A := continuous_inv_one_sub_mul_exp hx
  have hpt : ∀ φ : ℝ, (pk ((ρ : ℂ) * cexp (φ * I)) ζ : ℂ) * cexp (-(n : ℂ) * I * φ) =
      A φ * cexp (((-n : ℤ) : ℂ) * I * φ) +
        conj (A φ * cexp (((n : ℤ) : ℂ) * I * φ)) - cexp (((-n : ℤ) : ℂ) * I * φ) := by
    intro φ
    rw [pk_ofReal, hw]
    have hc : conj (cexp (((n : ℤ) : ℂ) * I * φ)) = cexp (((-n : ℤ) : ℂ) * I * φ) := by
      rw [← Complex.exp_conj]; congr 1; push_cast
      simp only [map_mul, Complex.conj_natCast, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [map_mul, hc]
    push_cast; ring
  simp_rw [hpt]
  have i1 : IntervalIntegrable (fun φ : ℝ => A φ * cexp (((-n : ℤ) : ℂ) * I * φ)) volume 0 (2 * π) :=
    (hA.mul (by fun_prop)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun φ : ℝ => conj (A φ * cexp (((n : ℤ) : ℂ) * I * φ))) volume 0
      (2 * π) :=
    ((Complex.continuous_conj.comp (hA.mul (by fun_prop)))).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun φ : ℝ => cexp (((-n : ℤ) : ℂ) * I * φ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun φ : ℝ => cexp (((-n : ℤ) : ℂ) * I * φ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral_conj, integral_inv_one_sub_mul_exp hx, integral_inv_one_sub_mul_exp hx,
    integral_exp_int_mul_I]
  have hn0 : (-(n : ℤ)) ≤ 0 := by omega
  have hn1 : ¬ ((n : ℤ) ≤ 0) := by omega
  have hn2 : ¬ ((-(n : ℤ)) = 0) := by omega
  simp only [hn0, hn1, hn2, ite_true, ite_false, map_zero, add_zero, sub_zero, neg_neg]
  simp

/-- The Cayley phase `c(t) = (t + i)/(t - i)` of a real point. -/
def cay (t : ℝ) : ℂ := ((t : ℂ) + I) / ((t : ℂ) - I)

theorem ofReal_sub_I_ne_zero (t : ℝ) : (t : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem norm_ofReal_add_I (t : ℝ) : ‖(t : ℂ) + I‖ = ‖(t : ℂ) - I‖ := by
  rw [← Complex.norm_conj ((t : ℂ) - I)]
  simp

theorem norm_cay (t : ℝ) : ‖cay t‖ = 1 := by
  rw [cay, norm_div, norm_ofReal_add_I, div_self (norm_ne_zero_iff.2 (ofReal_sub_I_ne_zero t))]

theorem cay_ne_zero (t : ℝ) : cay t ≠ 0 :=
  div_ne_zero (ofReal_add_I_ne_zero t) (ofReal_sub_I_ne_zero t)

theorem conj_cay (t : ℝ) : conj (cay t) = (cay t)⁻¹ := by
  rw [cay, map_div₀, inv_div]
  simp [Complex.conj_ofReal, sub_eq_add_neg]

theorem continuous_cay : Continuous cay := by
  unfold cay
  exact Continuous.div (by fun_prop) (by fun_prop) ofReal_sub_I_ne_zero

theorem cay_injective : Function.Injective cay := by
  intro s t h
  unfold cay at h
  rw [div_eq_div_iff (ofReal_sub_I_ne_zero s) (ofReal_sub_I_ne_zero t)] at h
  have h2 : (2 * I) * ((t : ℂ) - s) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · simp at h3
  · exact_mod_cast (sub_eq_zero.1 h3).symm

/-!
## The scalar Poisson kernel on the closed disk
-/

theorem one_sub_ne_zero_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have : z = 1 := by linear_combination -h
  rw [this, norm_one] at hz
  exact lt_irrefl _ hz

theorem norm_mul_lt_one {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ ≤ 1) : ‖w * ζ‖ < 1 := by
  rw [norm_mul]
  calc ‖w‖ * ‖ζ‖ ≤ ‖w‖ * 1 := by gcongr
    _ < 1 := by linarith

/-- `P(z) = (1 - |z|²)/|1 - z|²`. -/
theorem pk_eq {w ζ : ℂ} (h : 1 - w * ζ ≠ 0) :
    pk w ζ = (1 - Complex.normSq (w * ζ)) / Complex.normSq (1 - w * ζ) := by
  have hn : Complex.normSq (1 - w * ζ) ≠ 0 := (Complex.normSq_pos.2 h).ne'
  rw [pk, Complex.inv_re]
  set a := (w * ζ).re
  set b := (w * ζ).im
  have h1 : Complex.normSq (1 - w * ζ) = (1 - a) ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply]; simp [a, b]; ring
  have h2 : Complex.normSq (w * ζ) = a ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have h3 : (1 - w * ζ).re = 1 - a := by simp [a]
  rw [h3, h2]
  rw [h1] at hn ⊢
  field_simp
  ring

theorem pk_nonneg {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ ≤ 1) : 0 ≤ pk w ζ := by
  have hz := norm_mul_lt_one hw hζ
  rw [pk_eq (one_sub_ne_zero_of_norm_lt hz)]
  refine div_nonneg ?_ (Complex.normSq_nonneg _)
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (w * ζ)]

theorem norm_inv_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) : ‖(1 - z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  have := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one] at this
  linarith

theorem abs_pk_le {w ζ : ℂ} (hw : ‖w‖ < 1) (hζ : ‖ζ‖ ≤ 1) :
    |pk w ζ| ≤ 2 * (1 - ‖w‖)⁻¹ + 1 := by
  have hz := norm_mul_lt_one hw hζ
  have h1 : ‖(1 - w * ζ)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
    refine (norm_inv_one_sub_le hz).trans (inv_anti₀ (by linarith) ?_)
    rw [norm_mul]
    have : ‖w‖ * ‖ζ‖ ≤ ‖w‖ * 1 := by gcongr
    linarith
  rw [pk]
  refine (abs_sub _ _).trans ?_
  rw [abs_one, abs_mul, abs_two]
  gcongr
  exact (Complex.abs_re_le_norm _).trans h1

theorem continuousAt_pk {w ζ : ℂ} (h : 1 - w * ζ ≠ 0) :
    ContinuousAt (fun z => pk w z) ζ := by
  unfold pk
  refine ContinuousAt.sub (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
  refine Complex.continuous_re.continuousAt.comp ?_
  exact ContinuousAt.inv₀ (by fun_prop) h

/-- **The Poisson kernel at a real point `ρ = (r-1)/(r+1)`** of the Cayley phase:
`P(ρ c(t)) = r(t² + 1)/(t² + r²)`. -/
theorem pk_cay_real {r : ℝ} (hr : 1 ≤ r) (t : ℝ) :
    pk ((((r - 1) / (r + 1) : ℝ)) : ℂ) (cay t) = r * (t ^ 2 + 1) / (t ^ 2 + r ^ 2) := by
  set ρ : ℝ := (r - 1) / (r + 1)
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  have hρ1 : ρ < 1 := by rw [div_lt_one hr1]; linarith
  have hρ0 : 0 ≤ ρ := div_nonneg (by linarith) hr1.le
  have hw : ‖(ρ : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hρ0]; exact hρ1
  have hne := one_sub_ne_zero_of_norm_lt (norm_mul_lt_one hw (norm_cay t).le)
  rw [pk_eq hne]
  have hd := ofReal_sub_I_ne_zero t
  have e1 : (1 : ℂ) - (ρ : ℂ) * cay t =
      ((((1 - ρ) * t : ℝ) : ℂ) - (((1 + ρ) : ℝ) : ℂ) * I) / ((t : ℂ) - I) := by
    rw [cay]; field_simp; push_cast; ring
  have e2 : (ρ : ℂ) * cay t = ((ρ : ℝ) : ℂ) * cay t := rfl
  rw [e1, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
  have hc : Complex.normSq (cay t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_cay, one_pow]
  rw [hc]
  have n1 : Complex.normSq ((((1 - ρ) * t : ℝ) : ℂ) - (((1 + ρ) : ℝ) : ℂ) * I) =
      ((1 - ρ) * t) ^ 2 + (1 + ρ) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have n2 : Complex.normSq ((t : ℂ) - I) = t ^ 2 + 1 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [n1, n2]
  have hρdef : ρ * (r + 1) = r - 1 := by simp only [ρ]; field_simp
  have hpos : 0 < t ^ 2 + r ^ 2 := by nlinarith
  have hpos2 : 0 < t ^ 2 + 1 := by positivity
  have hpos3 : 0 < ((1 - ρ) * t) ^ 2 + (1 + ρ) ^ 2 := by nlinarith
  rw [div_div_eq_mul_div]
  rw [div_eq_div_iff (by positivity) hpos.ne']
  have : ρ = (r - 1) / (r + 1) := rfl
  rw [this]
  field_simp
  ring

/-- Tightness input: `P(ρ c(t)) ≥ r/2` on `|t| ≥ r` (`ρ = (r-1)/(r+1)`, `r ≥ 1`). -/
theorem pk_cay_real_ge {r : ℝ} (hr : 1 ≤ r) {t : ℝ} (ht : r ≤ |t|) :
    r / 2 ≤ pk ((((r - 1) / (r + 1) : ℝ)) : ℂ) (cay t) := by
  rw [pk_cay_real hr]
  have ht2 : r ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs t]; exact pow_le_pow_left₀ (by linarith) ht 2
  rw [le_div_iff₀ (by nlinarith)]
  nlinarith

/-!
## Cauchy moments of the Cayley phase
-/

/-- `E c(X)^n = 0` for `n ≥ 1` and `X` standard Cauchy (the Cayley phase is uniform). -/
theorem integral_cay_pow_cauchy {n : ℕ} (hn : 1 ≤ n) :
    ∫ t, cay t ^ n ∂ProbabilityTheory.cauchyMeasure 0 1 = 0 := by
  rw [BlockBand.Critical.Herglotz.integral_cauchyMeasure_eq_integral_standardCauchyWeight_smul_scale
    0 one_ne_zero]
  set F : ℂ → ℂ := fun z => ((z - I) / (z + I)) ^ n
  have hne : ∀ w : ℂ, 0 ≤ w.im → w + I ≠ 0 := by
    intro w hw h
    have := congrArg Complex.im h
    simp at this; linarith
  have hF := BlockBand.Critical.Collar.integral_standardCauchyWeight_smul_eq_of_analyticAt F
    (fun w hw => by
      have h1 : AnalyticAt ℂ (fun z : ℂ => (z - I) / (z + I)) w :=
        (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const) (hne w hw)
      exact h1.pow n) 1
    (fun w hw => by
      simp only [F, norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [norm_div, div_le_one (norm_pos_iff.2 (hne w hw))]
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
      simp; nlinarith)
  have hFI : F I = 0 := by simp [F, zero_pow (by omega : n ≠ 0)]
  rw [hFI] at hF
  have hpt : ∀ u : ℝ, standardCauchyWeight u • cay (0 + ((1 : ℝ≥0) : ℝ) * u) ^ n =
      conj (standardCauchyWeight u • F (u : ℂ)) := by
    intro u
    simp only [F, NNReal.coe_one, one_mul, zero_add, Complex.real_smul, map_mul, map_pow,
      Complex.conj_ofReal, map_div₀, map_sub, map_add, Complex.conj_I, cay]
    congr 2
    ring_nf
  simp_rw [hpt]
  rw [integral_conj, hF, map_zero]

end BlockBand.Critical.MatrixClosing.Boundary
