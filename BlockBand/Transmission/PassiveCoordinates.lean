module

public import BlockBand.Prelude

/-!
# Noncommutative passive inverse and scattering identities

Exact algebraic identities for a matrix `R` inverse to `K`, without commutation or normality: the
inverse difference, the dissipative balance, the scattering defect, and the passive scattering
normalization `T = 4η R*YR = I - S*S` (`passive_scattering_physical`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Transmission

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inverse difference without commutation or normality of the Schur matrix. -/
theorem passive_inverse_difference (K R : Matrix ι ι ℂ) (hKR : K * R = 1) :
    star R - R = star R * (K - star K) * R := by
  have hs : star R * star K = 1 := by
    simpa only [star_mul, star_one] using congrArg star hKR
  rw [mul_sub, sub_mul, mul_assoc, hKR, mul_one, hs, one_mul]

/-- Dissipative balance with scalar coefficients, derived from the inverse
relation; Q is exactly R* Y R, not an arbitrary positive response. -/
theorem passive_inverse_balance (K R Y : Matrix ι ι ℂ) (c d : ℂ)
    (hKR : K * R = 1) (hK : K - star K = c • (1 : Matrix ι ι ℂ) + d • Y) :
    star R - R = c • (star R * R) + d • (star R * Y * R) := by
  rw [passive_inverse_difference K R hKR, hK]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]

/-- Exact scattering defect. For physical c=2iη and d=2i, its scalar is
-(cd)=4η. This algebra has no positivity or limiting-law hypotheses. -/
theorem passive_scattering_defect (R Q : Matrix ι ι ℂ) (c d : ℂ)
    (hc : star c = -c)
    (hR : star R - R = c • (star R * R) + d • Q) :
    1 - star (1-c • R) * (1-c • R) = (-(c*d)) • Q := by
  have hex : star (1-c • R) * (1-c • R) =
      1 + c • (star R - R) - (c*c) • (star R * R) := by
    simp only [star_sub, star_one, star_smul, hc, mul_sub, sub_mul,
      mul_one, one_mul, smul_mul_assoc, mul_smul_comm]
    module
  rw [hex, hR, smul_add, smul_smul, smul_smul]
  module

/-- The passive scattering normalization `T = 4η R*YR = I - S*S`.
Assumptions are exact inverse and dissipative balance identities for finite
complex matrices, not stochastic hypotheses. No normality is required. -/
theorem passive_scattering_physical (K R Y : Matrix ι ι ℂ) (η : ℝ)
    (hKR : K * R = 1)
    (hK : K - star K = (2 * Complex.I * (η : ℂ)) • (1 : Matrix ι ι ℂ) +
      (2 * Complex.I) • Y) :
    1 - star (1-(2 * Complex.I * (η : ℂ)) • R) *
      (1-(2 * Complex.I * (η : ℂ)) • R) =
      (4 * (η : ℂ)) • (star R * Y * R) := by
  have hc : star (2 * Complex.I * (η : ℂ)) = -(2 * Complex.I * (η : ℂ)) := by
    simp
  have hcoef : -((2 * Complex.I * (η : ℂ)) * (2 * Complex.I)) =
      4 * (η : ℂ) := by
    calc
      _ = -(4 * (η : ℂ) * (Complex.I * Complex.I)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [passive_scattering_defect R (star R * Y * R)
    (2 * Complex.I * (η : ℂ)) (2 * Complex.I) hc
    (passive_inverse_balance K R Y _ _ hKR hK), hcoef]

end BlockBand.Transmission
