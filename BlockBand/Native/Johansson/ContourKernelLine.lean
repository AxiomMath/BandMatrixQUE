module

public import BlockBand.Native.Johansson.Biorthogonal

/-!
# Johansson's formula (2.18): the vertical line integral

For `S > 0`, a complex polynomial `P` and real `c`, the line integral
`∫ exp((c + iy)²/(2S)) P(c + iy) dy` (Lebesgue measure in `y ∈ ℝ`) does not depend on `c`
(`line_shift`). Proof: induction on the degree; `P = S Q₁ - S (divX P)' + P(0)` with
`Q₁ = X/S · divX P + (divX P)'`, the `Q₁`-term is the integral of a `y`-derivative of an integrable
function (`integral_eq_zero_of_hasDerivAt_of_integrable`), and the constant term is the Gaussian
integral `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`.

At `c = 0` and through `heatInvEval_holds` this gives, for a real polynomial `P` and real `L, v`,
`∫ exp(((L+iy)² - 2v(L+iy))/(2S)) P(L+iy) dy = exp(-v²/(2S)) √(2πS) (T P)(v)`
(`line_integral_heatInv`), with integrability (`line_integrable_heat`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory Polynomial Complex
open scoped NNReal Real

theorem line_integrable_abs_pow_mul_gauss {S : ℝ≥0} (hS : 0 < S) (k : ℕ) :
    Integrable (fun y : ℝ => |y| ^ k * Real.exp (-(y ^ 2) / (2 * (S : ℝ)))) := by
  have hb : (0 : ℝ) < 1 / (2 * (S : ℝ)) := by positivity
  have h := (integrable_rpow_mul_exp_neg_mul_sq hb (s := (k : ℝ))
    (by have := k.cast_nonneg (α := ℝ); linarith)).norm
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Real.rpow_natCast, norm_mul, Real.norm_eq_abs, abs_pow, Real.abs_exp]
  congr 2
  ring

theorem line_norm_eval_le (P : ℂ[X]) (c y : ℝ) :
    ‖P.eval ((c : ℂ) + y * I)‖ ≤
      ∑ k ∈ Finset.range ((P.comp (C (c : ℂ) + C I * X)).natDegree + 1),
        ‖(P.comp (C (c : ℂ) + C I * X)).coeff k‖ * |y| ^ k := by
  have h : P.eval ((c : ℂ) + y * I) = (P.comp (C (c : ℂ) + C I * X)).eval (y : ℂ) := by
    simp only [eval_comp, eval_add, eval_C, eval_mul, eval_X, mul_comm I]
  rw [h, eval_eq_sum_range]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_pow, Complex.norm_real]

theorem line_norm_cexp {S : ℝ≥0} (c y : ℝ) :
    ‖cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ)))‖ =
      Real.exp ((c : ℝ) ^ 2 / (2 * (S : ℝ))) * Real.exp (-(y ^ 2) / (2 * (S : ℝ))) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  have : ((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ)) =
      (((c ^ 2 - y ^ 2) / (2 * (S : ℝ)) : ℝ) : ℂ) + ((c * y / (S : ℝ) : ℝ) : ℂ) * I := by
    push_cast
    by_cases hS : (S : ℂ) = 0
    · simp [hS]
    · field_simp
      linear_combination (y : ℂ) ^ 2 * I_sq
  rw [this]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero]
  ring

theorem line_integrable {S : ℝ≥0} (hS : 0 < S) (P : ℂ[X]) (c : ℝ) :
    Integrable (fun y : ℝ => cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
      P.eval ((c : ℂ) + y * I)) := by
  set Q := P.comp (C (c : ℂ) + C I * X)
  have hb : Integrable (fun y : ℝ => Real.exp ((c : ℝ) ^ 2 / (2 * (S : ℝ))) *
      ∑ k ∈ Finset.range (Q.natDegree + 1),
        ‖Q.coeff k‖ * (|y| ^ k * Real.exp (-(y ^ 2) / (2 * (S : ℝ))))) :=
    (integrable_finsetSum _ fun k _ =>
      (line_integrable_abs_pow_mul_gauss hS k).const_mul _).const_mul _
  refine hb.mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [norm_mul, line_norm_cexp]
  have h1 := line_norm_eval_le P c y
  have h2 : 0 ≤ Real.exp ((c : ℝ) ^ 2 / (2 * (S : ℝ))) := (Real.exp_pos _).le
  have h3 : 0 < Real.exp (-(y ^ 2) / (2 * (S : ℝ))) := Real.exp_pos _
  calc Real.exp ((c : ℝ) ^ 2 / (2 * (S : ℝ))) * Real.exp (-(y ^ 2) / (2 * (S : ℝ))) *
        ‖P.eval ((c : ℂ) + y * I)‖
      ≤ Real.exp ((c : ℝ) ^ 2 / (2 * (S : ℝ))) * Real.exp (-(y ^ 2) / (2 * (S : ℝ))) *
        ∑ k ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff k‖ * |y| ^ k := by gcongr
    _ = _ := by
      rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring

theorem line_hasDerivAt {S : ℝ≥0} (hS : 0 < S) (Q : ℂ[X]) (c y : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (((c : ℂ) + t * I) ^ 2 / (2 * (S : ℂ))) *
        Q.eval ((c : ℂ) + t * I))
      (I * (cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
        (C ((S : ℂ)⁻¹) * X * Q + derivative Q).eval ((c : ℂ) + y * I))) y := by
  have hg : HasDerivAt (fun t : ℝ => (c : ℂ) + t * I) I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (c : ℂ)
  have hQ : HasDerivAt (fun t : ℝ => Q.eval ((c : ℂ) + t * I))
      ((derivative Q).eval ((c : ℂ) + y * I) * I) y :=
    HasDerivAt.comp (h₂ := fun w => Q.eval w) y (Q.hasDerivAt ((c : ℂ) + y * I)) hg
  have hE : HasDerivAt (fun t : ℝ => cexp (((c : ℂ) + t * I) ^ 2 / (2 * (S : ℂ))))
      (cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
        ((2 : ℕ) * ((c : ℂ) + y * I) ^ (2 - 1) * I / (2 * (S : ℂ)))) y :=
    ((hg.pow 2).div_const (2 * (S : ℂ))).cexp
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  convert hE.mul hQ using 1
  simp only [eval_add, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem line_integral_deriv_eq_zero {S : ℝ≥0} (hS : 0 < S) (Q : ℂ[X]) (c : ℝ) :
    ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
      (C ((S : ℂ)⁻¹) * X * Q + derivative Q).eval ((c : ℂ) + y * I) = 0 := by
  have h := integral_eq_zero_of_hasDerivAt_of_integrable (fun y => line_hasDerivAt hS Q c y)
    ((line_integrable hS _ c).const_mul I) (line_integrable hS Q c)
  rw [integral_const_mul] at h
  simpa [I_ne_zero] using h

theorem line_integral_const {S : ℝ≥0} (hS : 0 < S) (c : ℝ) :
    ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) =
      (Real.pi / (1 / (2 * (S : ℂ)))) ^ (1 / 2 : ℂ) := by
  have hb : 0 < (1 / (2 * (S : ℂ))).re := by
    have : (1 / (2 * (S : ℂ))) = ((1 / (2 * (S : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ofReal_re]; positivity
  rw [← GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I hb (-c)]
  congr 1
  ext y
  congr 1
  push_cast
  linear_combination ((c : ℂ) ^ 2 + (y : ℂ) ^ 2) / (2 * (S : ℂ)) * I_sq

theorem line_shift {S : ℝ≥0} (hS : 0 < S) (n : ℕ) :
    ∀ P : ℂ[X], P.natDegree ≤ n → ∀ c c' : ℝ,
      ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) * P.eval ((c : ℂ) + y * I) =
        ∫ y : ℝ, cexp (((c' : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) * P.eval ((c' : ℂ) + y * I) := by
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  -- the decomposition `P = S • Q₁ - S • Q' + C a`, with `Q = divX P`
  have hdec : ∀ (P : ℂ[X]) (c : ℝ),
      ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) * P.eval ((c : ℂ) + y * I) =
        P.coeff 0 * (∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ)))) -
          (S : ℂ) * ∫ y : ℝ, cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
            (derivative P.divX).eval ((c : ℂ) + y * I) := by
    intro P c
    set Q₁ := C ((S : ℂ)⁻¹) * X * P.divX + derivative P.divX
    set E : ℝ → ℂ := fun y => cexp (((c : ℂ) + y * I) ^ 2 / (2 * (S : ℂ)))
    have hP : ∀ w : ℂ, P.eval w = (S : ℂ) * Q₁.eval w - (S : ℂ) * (derivative P.divX).eval w +
        P.coeff 0 := by
      intro w
      conv_lhs => rw [← divX_mul_X_add P]
      simp only [Q₁, eval_add, eval_mul, eval_C, eval_X]
      field_simp
      ring
    have i1 := line_integrable hS Q₁ c
    have i2 := line_integrable hS (derivative P.divX) c
    have i3 := line_integrable hS 1 c
    simp only [eval_one, mul_one] at i3
    have hfun : (fun y : ℝ => E y * P.eval ((c : ℂ) + y * I)) =
        fun y => ((S : ℂ) * (E y * Q₁.eval ((c : ℂ) + y * I)) -
          (S : ℂ) * (E y * (derivative P.divX).eval ((c : ℂ) + y * I))) + P.coeff 0 * E y := by
      ext y; rw [hP]; ring
    change ∫ y, E y * P.eval ((c : ℂ) + y * I) = P.coeff 0 * (∫ y, E y) -
      (S : ℂ) * ∫ y, E y * (derivative P.divX).eval ((c : ℂ) + y * I)
    have j1 : Integrable (fun y : ℝ => (S : ℂ) * (E y * Q₁.eval ((c : ℂ) + y * I))) :=
      i1.const_mul _
    have j2 : Integrable (fun y : ℝ => (S : ℂ) *
        (E y * (derivative P.divX).eval ((c : ℂ) + y * I))) := i2.const_mul _
    have j12 : Integrable (fun y : ℝ => (S : ℂ) * (E y * Q₁.eval ((c : ℂ) + y * I)) -
        (S : ℂ) * (E y * (derivative P.divX).eval ((c : ℂ) + y * I))) := j1.sub j2
    have j3 : Integrable (fun y : ℝ => P.coeff 0 * E y) := i3.const_mul _
    rw [hfun, integral_add j12 j3, integral_sub j1 j2, integral_const_mul, integral_const_mul,
      integral_const_mul]
    have h0 : ∫ y, E y * Q₁.eval ((c : ℂ) + y * I) = 0 := line_integral_deriv_eq_zero hS _ c
    rw [h0]
    ring
  induction n with
  | zero =>
    intro P hP c c'
    rw [hdec P c, hdec P c', line_integral_const hS c, line_integral_const hS c']
    have : derivative P.divX = 0 := by
      rw [Nat.le_zero, natDegree_eq_zero] at hP
      obtain ⟨a, rfl⟩ := hP
      simp
    simp [this]
  | succ n ih =>
    intro P hP c c'
    rw [hdec P c, hdec P c', line_integral_const hS c, line_integral_const hS c',
      ih (derivative P.divX) ?_ c c']
    refine (natDegree_derivative_le _).trans ?_
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega

/-- The heat integrand of `kernel`, rewritten as a shifted line integrand. -/
theorem line_heat_integrand_eq (S : ℝ≥0) (P : ℝ[X]) (L v y : ℝ) :
    cexp ((((L : ℂ) + y * I) ^ 2 - 2 * (v : ℂ) * ((L : ℂ) + y * I)) / (2 * (S : ℂ))) *
        (P.map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I) =
      cexp (-(v : ℂ) ^ 2 / (2 * (S : ℂ))) *
        (cexp ((((L - v : ℝ) : ℂ) + y * I) ^ 2 / (2 * (S : ℂ))) *
          ((P.map (algebraMap ℝ ℂ)).comp (X + C (v : ℂ))).eval (((L - v : ℝ) : ℂ) + y * I)) := by
  have h1 : ((P.map (algebraMap ℝ ℂ)).comp (X + C (v : ℂ))).eval (((L - v : ℝ) : ℂ) + y * I) =
      (P.map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I) := by
    rw [eval_comp]
    congr 1
    simp only [eval_add, eval_X, eval_C]
    push_cast
    ring
  rw [h1, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem line_integrable_heat {S : ℝ≥0} (hS : 0 < S) (P : ℝ[X]) (L v : ℝ) :
    Integrable (fun y : ℝ =>
      cexp ((((L : ℂ) + y * I) ^ 2 - 2 * (v : ℂ) * ((L : ℂ) + y * I)) / (2 * (S : ℂ))) *
        (P.map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I)) := by
  simp_rw [line_heat_integrand_eq]
  exact (line_integrable hS _ (L - v)).const_mul _

/-- **The line integral**: `∫ exp(((L+iy)² - 2v(L+iy))/(2S)) P(L+iy) dy
= exp(-v²/(2S)) √(2πS) (T P)(v)`, for every real `L` and `v`. -/
theorem line_integral_heatInv {S : ℝ≥0} (hS : 0 < S) (P : ℝ[X]) (L v : ℝ) :
    ∫ y : ℝ, cexp ((((L : ℂ) + y * I) ^ 2 - 2 * (v : ℂ) * ((L : ℂ) + y * I)) / (2 * (S : ℂ))) *
        (P.map (algebraMap ℝ ℂ)).eval ((L : ℂ) + y * I) =
      cexp (-(v : ℂ) ^ 2 / (2 * (S : ℂ))) * ((Real.sqrt (2 * π * S) : ℝ) : ℂ) *
        (((heatInv S P).eval v : ℝ) : ℂ) := by
  simp_rw [line_heat_integrand_eq]
  rw [integral_const_mul, line_shift hS _ _ le_rfl (L - v) 0, mul_assoc]
  congr 1
  rw [heatInvEval_holds, integral_gaussianReal_eq_integral_smul hS.ne', ← integral_const_mul]
  have hs : Real.sqrt (2 * π * S) ≠ 0 := by
    have : (0 : ℝ) < 2 * π * S := by have : (0 : ℝ) < S := hS; positivity
    exact (Real.sqrt_pos.mpr this).ne'
  congr 1
  ext y
  rw [gaussianPDFReal_def, Complex.real_smul]
  simp only [eval_comp, eval_add, eval_X, eval_C]
  push_cast
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]
  congr 1
  · congr 1
    ring_nf
    rw [I_sq]
    ring
  · congr 1
    ring

end BlockBand.Native.Johansson
