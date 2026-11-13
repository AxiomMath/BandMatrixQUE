module

public import BlockBand.Native.CEH.ETH.BlockBand.Probability.GaussianNormalization

/-!
# Consecutive GUE normalizer ratio

This module records the exact scalar normalizer cancellation in Claim 2 of
the coarea theorem.  It is separated from the eigenpair Jacobian so that no measure
change-of-variables statement is hidden in the algebraic constant.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

/-- Consecutive GUE normalizers in the paper's convention satisfy
`Z_d(t) / Z_{d+1}(t) = [(2πt)^{1/2}(πt)^d]⁻¹` for `t > 0`. -/
theorem gueNormalizer_div_succ
    (d : ℕ) {t : ℝ} (ht : 0 < t) :
    gueNormalizer d t / gueNormalizer (d + 1) t =
      1 / ((2 * Real.pi * t) ^ (1 / 2 : ℝ) *
        (Real.pi * t) ^ (d : ℝ)) := by
  let a : ℝ := 2 * Real.pi * t
  let b : ℝ := Real.pi * t
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  unfold gueNormalizer
  change a ^ ((d : ℝ) / 2) * b ^ ((d : ℝ) * ((d : ℝ) - 1) / 2) /
      (a ^ (((d + 1 : ℕ) : ℝ) / 2) *
        b ^ (((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) / 2)) =
    1 / (a ^ (1 / 2 : ℝ) * b ^ (d : ℝ))
  have haPow :
      a ^ ((d : ℝ) / 2) * a ^ (1 / 2 : ℝ) =
        a ^ (((d + 1 : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add ha]
    congr 1
    push_cast
    ring
  have hbPow :
      b ^ ((d : ℝ) * ((d : ℝ) - 1) / 2) * b ^ (d : ℝ) =
        b ^ (((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) / 2) := by
    rw [← Real.rpow_add hb]
    congr 1
    push_cast
    ring
  rw [div_eq_div_iff]
  · calc
      a ^ ((d : ℝ) / 2) * b ^ ((d : ℝ) * ((d : ℝ) - 1) / 2) *
          (a ^ (1 / 2 : ℝ) * b ^ (d : ℝ)) =
        (a ^ ((d : ℝ) / 2) * a ^ (1 / 2 : ℝ)) *
          (b ^ ((d : ℝ) * ((d : ℝ) - 1) / 2) * b ^ (d : ℝ)) := by ring
      _ = a ^ (((d + 1 : ℕ) : ℝ) / 2) *
          b ^ (((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) / 2) := by
        rw [haPow, hbPow]
      _ = 1 * (a ^ (((d + 1 : ℕ) : ℝ) / 2) *
          b ^ (((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) - 1) / 2)) := by
        rw [one_mul]
  · exact mul_ne_zero
      (ne_of_gt (Real.rpow_pos_of_pos ha _))
      (ne_of_gt (Real.rpow_pos_of_pos hb _))
  · exact mul_ne_zero
      (ne_of_gt (Real.rpow_pos_of_pos ha _))
      (ne_of_gt (Real.rpow_pos_of_pos hb _))

/-- The same ratio in the orientation used in Claim 2 of the coarea theorem. -/
theorem gueNormalizer_pred_div
    {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    gueNormalizer (d - 1) t / gueNormalizer d t =
      1 / ((2 * Real.pi * t) ^ (1 / 2 : ℝ) *
        (Real.pi * t) ^ ((d - 1 : ℕ) : ℝ)) := by
  have hds : d - 1 + 1 = d := Nat.sub_add_cancel hd
  simpa [hds] using gueNormalizer_div_succ (d - 1) ht

end CEHNative.BlockBand
