module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedParameterFatouSuccessor

/-!
# Mass of the standard Cauchy density

The standard Cauchy density `standardCauchyWeight` has total mass one as an `ℝ≥0∞`-valued
lower integral, as used in the finite-stage evaluation of the successor step.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 6000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The standard Cauchy density has `ℝ≥0∞` mass one. -/
theorem lintegral_ofReal_standardCauchyWeight :
    (∫⁻ t : ℝ, ENNReal.ofReal (standardCauchyWeight t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_standardCauchyWeight]
    simp
  · unfold standardCauchyWeight
    convert integrable_inv_one_add_sq.const_mul Real.pi⁻¹ using 1
    funext t
    field_simp [Real.pi_ne_zero]
  · filter_upwards with t
    unfold standardCauchyWeight
    positivity

end PSSSNative.BlockBand.PSSS
