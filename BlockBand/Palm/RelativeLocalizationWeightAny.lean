module

public import BlockBand.Palm.RelativeLocalizationWeight

/-!
# Relative localization: the weight `e^{νψ}` for a rate of either sign

The column field (in the paper, "the opposite weight that increases away from the initial
central label") uses `rlPhi (-ν)`. The bounds of `RelativeLocalizationWeight` were stated for
`ν ≥ 0`; here they are proved with `|ν|` for every real `ν`, together with
`-2R ≤ ψ` (so `rlPhi (-ν) ≤ e^{2νR}`), `rlPhi ν E d R E = 1`, and the far lower bound
`rlPhi (-ν) x ≥ exp(ν min(|x-E| - d, R))` for `ν ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

variable {R d ν E : ℝ}

theorem abs_rlPhi1_le_abs (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPhi1 ν E d R x| ≤ |ν| * weightConst * rlPhi ν E d R x := by
  rw [rlPhi1, abs_mul, abs_mul, abs_of_pos (rlPhi_pos x)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (abs_rlPsi1_le hd hR x) (abs_nonneg ν)) (rlPhi_pos x).le

theorem abs_rlPhi2_le_abs (hd : 0 < d) (hR : 0 < R) (x : ℝ) :
    |rlPhi2 ν E d R x| ≤
      (|ν| * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) * rlPhi ν E d R x := by
  rw [rlPhi2, abs_mul, abs_of_pos (rlPhi_pos x)]
  refine mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x).le
  calc _ ≤ |ν * rlPsi2 E d R x| + |ν ^ 2 * rlPsi1 E d R x ^ 2| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ν), abs_pow]
      have h1 := abs_rlPsi1_le (E := E) hd hR x
      have h2 := abs_rlPsi2_le (E := E) hd hR x
      have h3 : |rlPsi1 E d R x| ^ 2 ≤ weightConst ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      exact add_le_add (mul_le_mul_of_nonneg_left h2 (abs_nonneg ν))
        (mul_le_mul_of_nonneg_left h3 (sq_nonneg ν))

theorem rlPhi_le_exp_mul_abs (hd : 0 < d) (hR : 0 < R) (x y : ℝ) :
    rlPhi ν E d R y ≤ Real.exp (|ν| * weightConst * |y - x|) * rlPhi ν E d R x := by
  have hlip : ‖rlPsi E d R y - rlPsi E d R x‖ ≤ weightConst * ‖y - x‖ :=
    (convex_univ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (rlPsi_hasDerivAt hd hR z).hasDerivWithinAt)
      (fun z _ => by rw [Real.norm_eq_abs]; exact abs_rlPsi1_le hd hR z) (Set.mem_univ _)
      (Set.mem_univ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  rw [rlPhi, rlPhi, ← Real.exp_add, Real.exp_le_exp]
  have h1 : ν * (rlPsi E d R y - rlPsi E d R x) ≤ |ν| * (weightConst * |y - x|) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlip (abs_nonneg ν))
  nlinarith

theorem neg_two_mul_le_rlTheta (hR : 0 < R) (y : ℝ) : -(2 * R) ≤ rlTheta R y := by
  by_cases hy : y ≤ -2 * R
  · rw [rlTheta_eq_neg hR hy]; linarith
  · push Not at hy
    exact le_trans (by linarith) (le_rlTheta hR y)

theorem neg_two_mul_le_rlPsi (hR : 0 < R) (x : ℝ) : -(2 * R) ≤ rlPsi E d R x :=
  neg_two_mul_le_rlTheta hR _

/-- The increasing weight is bounded: `rlPhi (-ν) ≤ e^{2νR}` (`ν ≥ 0`). -/
theorem rlPhi_neg_le (hν : 0 ≤ ν) (hR : 0 < R) (x : ℝ) :
    rlPhi (-ν) E d R x ≤ Real.exp (2 * ν * R) := by
  rw [rlPhi, Real.exp_le_exp]
  have := neg_two_mul_le_rlPsi (E := E) (d := d) hR x
  nlinarith

theorem rlPhi_at_centre (hd : 0 < d) (hR : 0 < R) : rlPhi ν E d R E = 1 := by
  have hg : rlG d (E - E) = 0 := by
    simp [rlG, Real.sqrt_sq hd.le]
  rw [rlPhi, rlPsi, hg, rlTheta_eq_self hR (by linarith), mul_zero, Real.exp_zero]

/-- Far lower bound of the increasing weight. -/
theorem exp_le_rlPhi_neg (hν : 0 ≤ ν) (hR : 0 < R) (x : ℝ) :
    Real.exp (ν * min (|x - E| - d) R) ≤ rlPhi (-ν) E d R x := by
  rw [rlPhi, Real.exp_le_exp]
  have := rlPsi_le (E := E) (d := d) hR x
  nlinarith

end BlockBand.Palm.RelativeLocalization
