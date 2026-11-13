module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian tails paid by powers

Elementary bounds `e^{-s} ≤ (r/s)^r` and `exp(-c m²/n) ≤ C(q,c) (a/m)^q` for `a ≥ √n`, used to
pay the Gaussian rank tail in the window transfer theorem.
-/

@[expose] public section

namespace BlockBand.RankLocation.WindowTransfer

/-- `e^{-s} ≤ (r/s)^r` for `r, s > 0`. -/
theorem exp_neg_le_power (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Real.exp (-s) ≤ (r / s) ^ r := by
  let y : ℝ := s / r
  have hy : 0 < y := div_pos hs hr
  have hbound : y * Real.exp (-y) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one y).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ y * Real.exp (-y)) hbound hr.le
  rw [Real.mul_rpow hy.le (Real.exp_pos _).le, ← Real.exp_mul, Real.one_rpow] at hpow
  have hys : -y * r = -s := by unfold y; field_simp
  rw [hys] at hpow
  have hdiv : Real.exp (-s) ≤ (1 : ℝ) / y ^ r := (le_div_iff₀ (Real.rpow_pos_of_pos hy r)).mpr (by simpa [mul_comm] using hpow)
  have hid : (1 : ℝ) / y ^ r = (r / s) ^ r := by
    rw [one_div, ← Real.inv_rpow hy.le]
    congr 1
    unfold y
    field_simp
  exact hdiv.trans_eq hid

/-- Gaussian decay pays every positive power with a constant depending only on `q, c`, uniformly
in `u > 0`. -/
theorem gaussian_tail_power (q c u : ℝ) (hq : 0 < q) (hc : 0 < c) (hu : 0 < u) :
    Real.exp (-c * u ^ 2) ≤ (q / (2 * c)) ^ (q / 2) * u ^ (-q) := by
  have hh := exp_neg_le_power (q / 2) (c * u ^ 2) (by positivity) (by positivity)
  have heq : (q / 2) / (c * u ^ 2) = (q / (2 * c)) / u ^ 2 := by ring
  have hpower : (u ^ 2) ^ (q / 2) = u ^ q := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu.le]
    congr 1
    simp only [Nat.cast_ofNat]
    ring
  rw [heq, Real.div_rpow (by positivity) (by positivity), hpower] at hh
  rw [show -(c * u ^ 2) = -c * u ^ 2 by ring] at hh
  simpa only [Real.rpow_neg hu.le, div_eq_mul_inv] using hh

/-- The Gaussian rank-tail payment of the window transfer theorem: for real `q, c, n, m > 0` and
`a ≥ √n`, `exp(-c m²/n) ≤ C(q,c) (a/m)^q`, uniformly in `n, a, m`. -/
theorem gaussian_rank_tail_power (q c n a m : ℝ) (hq : 0 < q) (hc : 0 < c)
    (hn : 0 < n) (hm : 0 < m) (ha : Real.sqrt n ≤ a) :
    Real.exp (-c * m ^ 2 / n) ≤ (q / (2 * c)) ^ (q / 2) * (a / m) ^ q := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hh := gaussian_tail_power q c (m / Real.sqrt n) hq hc (div_pos hm hs)
  have hexp : -c * (m / Real.sqrt n) ^ 2 = -c * m ^ 2 / n := by
    rw [div_pow, Real.sq_sqrt hn.le]
    ring
  rw [hexp, Real.rpow_neg (div_nonneg hm.le hs.le)] at hh
  have hinv : ((m / Real.sqrt n) ^ q)⁻¹ = (Real.sqrt n / m) ^ q := by
    rw [← Real.inv_rpow (div_nonneg hm.le hs.le)]
    congr 1
    field_simp
  rw [hinv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right ha hm.le) hq.le)
    (Real.rpow_nonneg (by positivity) _))

end BlockBand.RankLocation.WindowTransfer
