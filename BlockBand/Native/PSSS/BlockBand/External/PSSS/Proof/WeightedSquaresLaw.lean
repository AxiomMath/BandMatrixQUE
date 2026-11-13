module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.FourierCriterion
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.FourierStieltjesJointLaw

/-!
# The weighted-square product as the joint Gaussian law

This module identifies the analytic product used in APSSS
(Aizenman–Peled–Schenker–Shamis–Sodin), (6.12)--(6.16), with
the Fourier characteristic integral of the two random variables occurring in
the quadratic-ratio argument.  The first component is the tail square energy
(after the first `r` dominant coordinates); the second is the complete signed
quadratic form translated by `a`.  Thus the scalar translation phase, and the
dominant/tail frequency split, are part of the proved identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Complex FourierTransform MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- The pair `(X,Y-a)` under the finite product standard-Gaussian law:
`X` is APSSS's tail square energy and `Y` is the complete signed quadratic
form.  This is the random vector to which Fourier–Stieltjes inversion is
applied. -/
def weightedSquaresRandomVector {n : ℕ} (E b : Fin n → ℝ) (r : ℕ)
    (a : ℝ) (g : Fin n → ℝ) : ℝ × ℝ :=
  (tailQuadraticRatioEnergy E b r g, quadraticRatioValue E b g - a)

/-- The weighted-square random vector is Borel measurable. -/
theorem measurable_weightedSquaresRandomVector {n : ℕ} (E b : Fin n → ℝ)
    (r : ℕ) (a : ℝ) : Measurable (weightedSquaresRandomVector E b r a) := by
  unfold weightedSquaresRandomVector tailQuadraticRatioEnergy quadraticRatioValue
  measurability

/-- Translation by `a` contributes precisely the scalar phase multiplying the
untranslated joint characteristic function. -/
theorem weightedSquaresCharFun_eq_phase_mul_quadraticRatioCharacteristic
    {n : ℕ} (E b : Fin n → ℝ) (r : ℕ) (ξ η a : ℝ) :
    weightedSquaresCharFun E b r (ξ : ℂ) (η : ℂ) a =
      Complex.exp (-(Complex.I * (η : ℂ) * (a : ℂ))) *
        quadraticRatioCharacteristic E b r ξ η := by
  rw [weightedSquaresCharFun_eq_product,
    quadraticRatioCharacteristic_eq_product]

end PSSSNative.BlockBand.PSSS
