module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneFinalAssembly

/-!
# Monolithic theta-one deterministic closure

This is the single deterministic conclusion consumed after the regular-window
canonical estimates have been extracted.  It joins the cutoff and the
theta-one regularized `s₂` bound without hiding either normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-- The explicit dimension-free constant delivered by the published `s₂`
bookkeeping. -/
def thetaOneSTwoBound (lambdaNorm L cΓ p d : ℝ) : ℝ :=
  (cΓ⁻¹ * L) * (1 + L * L / p) *
      (cΓ⁻¹ * L) * (1 + L * L / p) +
    lambdaNorm ^ 2 *
      ((L * (1 + L * L / p) * (cΓ⁻¹ * L)) *
        ((cΓ⁻¹ * L) * (1 + L * L / p) * L) / d)

/-- The cutoff half of the monolithic conclusion, in the spectral-lift normalization. -/
theorem thetaOneMonolithicCutoff
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) (q₁ q₂ : Fin N → ℂ)
    (hpair : 1 / 2 <
      (s * NTrace (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re) :
    regularizationCoefficient (Real.sqrt s : ℂ)
      (spectralLift hF q₁) (spectralLift hF q₂)ᴴ = 1 := by
  exact regularizationCoefficient_eq_one_of_scaled_pairing
    (Real.sq_sqrt hs.le) _ _ hpair

end CEHNative.BlockBand.External.CEH
