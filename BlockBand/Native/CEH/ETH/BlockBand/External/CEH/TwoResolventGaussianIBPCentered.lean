module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPMaster
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventPencilAdapter

/-!
# Centered CEH two-resolvent loop algebra

The normalized GUE master cancellation and the exact algebraic decomposition of the CEH
underlined two-resolvent word into a deterministic MDE part and centered averaged and isotropic
remainders, with the stability equations they satisfy. No estimate on the remainders is made.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate
open PencilAdapter

/-- Exact cancellation for the normalized GUE product law. Its coordinate variance is `1/N`,
hence this theorem is the `lambda = 1` member of CEH's underlined family; arbitrary `lambda`
requires a separate scaled-coordinate transport. -/
theorem normalizedGUE_masterCancellation
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
      ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
        ∑ a : Fin N, (y k : ℂ) * gueCoordinateDirection N k p a *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ a q y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) +
      (∫ y : HermitianCoordinateSpace N,
        ((N : ℂ)⁻¹ * (fullGUEResolvent H₁ z₁ y).trace) *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y) p q +
          ((N : ℂ)⁻¹ *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y).trace) *
            fullGUEResolvent H₂ z₂ y p q
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) = 0 := by
  have h := normalizedGUEFullTwoResolvent_masterLoop_scalar
    hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ p q
  linear_combination h

/-- Centered normalized trace of a random resolvent around a specified deterministic
Stieltjes value. -/
def centeredResolventTrace {N : ℕ} (m : ℂ)
    (G : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace G - m

/-- Centered normalized trace of a two-resolvent word around a specified deterministic
comparison value. -/
def centeredTwoResolventTrace {N : ℕ} (t : ℂ)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (G₁ * A * G₂) - t

/-- The two centered trace contributions left after deterministic MDE values
are extracted from the Gaussian loop.  This is an observable, not an assumed
error estimate. -/
def centeredTraceRemainder {N : ℕ} (lambda : ℂ) (m t : ℂ)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (lambda ^ 2 * centeredResolventTrace m G₁) • (G₁ * A * G₂) +
    (lambda ^ 2 * centeredTwoResolventTrace t G₁ A G₂) • G₂

/-- Averaged remainder observable used in the normalized-trace bootstrap. -/
def averagedCenteredTraceRemainder {N : ℕ} (lambda : ℂ) (m t : ℂ)
    (M₁ G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  NTrace (M₁ * centeredTraceRemainder lambda m t G₁ A G₂)

/-- Entrywise (isotropic-coordinate) remainder observable.  No size estimate
is included in the definition. -/
def isotropicCenteredTraceRemainder {N : ℕ} (lambda : ℂ) (m t : ℂ)
    (M₁ G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) (p q : Fin N) : ℂ :=
  (M₁ * centeredTraceRemainder lambda m t G₁ A G₂) p q

/-- The random-pencil resolvent equation rewrites the complete `λ W G₁ A G₂`
source term without division by `λ`. -/
theorem lambda_W_twoResolvent_eq {N : ℕ}
    (f : Spectrum N) (lambda : ℝ)
    (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) (z₁ : ℂ)
    (hPG : resolventPencil f lambda W z₁ * G₁ = 1) :
    (lambda : ℂ) • (W * G₁ * A * G₂) =
      A * G₂ -
        (deformationMatrix f - z₁ • (1 : Matrix (Fin N) (Fin N) ℂ)) *
          G₁ * A * G₂ := by
  unfold resolventPencil deformedMatrix at hPG
  have hsource :
      ((lambda : ℂ) • W) * G₁ =
        1 - (deformationMatrix f - z₁ •
          (1 : Matrix (Fin N) (Fin N) ℂ)) * G₁ := by
    calc
      ((lambda : ℂ) • W) * G₁ =
          (deformationMatrix f + (lambda : ℂ) • W - z₁ •
            (1 : Matrix (Fin N) (Fin N) ℂ)) * G₁ -
          (deformationMatrix f - z₁ •
            (1 : Matrix (Fin N) (Fin N) ℂ)) * G₁ := by noncomm_ring
      _ = _ := by rw [hPG]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul]
  rw [hsource]
  noncomm_ring

/-- Deterministic plus centered decomposition of the exact CEH underlined
word.  The two final summands are the averaged/isotropic probabilistic
remainders that still require concentration or a local law. -/
theorem underlinedTwoResolventWord_centered {N : ℕ}
    (lambda m t : ℂ) (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    underlinedTwoResolventWord lambda W G₁ A G₂ =
      lambda • (W * G₁ * A * G₂) +
        (lambda ^ 2 * m) • (G₁ * A * G₂) +
        (lambda ^ 2 * t) • G₂ +
        centeredTraceRemainder lambda m t G₁ A G₂ := by
  unfold underlinedTwoResolventWord centeredTraceRemainder
    centeredResolventTrace centeredTwoResolventTrace
  module

/-- Scalar-matrix form of the concrete MDE pencil. -/
theorem mdePencil_eq_deformation_sub {N : ℕ}
    (f : Spectrum N) (lambda : ℝ) (z m : ℂ) :
    mdePencil f lambda z m =
      deformationMatrix f - z • (1 : Matrix (Fin N) (Fin N) ℂ) -
        (((lambda : ℂ) ^ 2 * m) •
          (1 : Matrix (Fin N) (Fin N) ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [mdePencil, deformationMatrix]
  · simp [mdePencil, deformationMatrix, hij]

/-- The resolvent equation and centered trace split combine into the exact
MDE-pencil source equation.  This is the algebraic coefficient equation before
any expectation, concentration, or local-law estimate. -/
theorem underlinedTwoResolventWord_mdeSource {N : ℕ}
    (f : Spectrum N) (lambda : ℝ) (m t : ℂ)
    (W G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) (z₁ : ℂ)
    (hPG : resolventPencil f lambda W z₁ * G₁ = 1) :
    underlinedTwoResolventWord (lambda : ℂ) W G₁ A G₂ =
      -(mdePencil f lambda z₁ m * G₁ * A * G₂) +
        (A + (((lambda : ℂ) ^ 2 * t) •
          (1 : Matrix (Fin N) (Fin N) ℂ))) * G₂ +
        centeredTraceRemainder (lambda : ℂ) m t G₁ A G₂ := by
  rw [underlinedTwoResolventWord_centered,
    lambda_W_twoResolvent_eq f lambda W G₁ A G₂ z₁ hPG]
  rw [mdePencil_eq_deformation_sub]
  noncomm_ring

/-- The averaged and entrywise remainder observables are the two projections
of the same centered random matrix. -/
theorem centeredRemainder_projections {N : ℕ}
    (lambda m t : ℂ) (M₁ G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin N) :
    averagedCenteredTraceRemainder lambda m t M₁ G₁ A G₂ =
        NTrace (M₁ * centeredTraceRemainder lambda m t G₁ A G₂) ∧
      isotropicCenteredTraceRemainder lambda m t M₁ G₁ A G₂ p q =
        (M₁ * centeredTraceRemainder lambda m t G₁ A G₂) p q := by
  exact ⟨rfl, rfl⟩

/-- Exact averaged stability coefficient and isotropic reconstruction from a
matrix remainder equation.  This exposes, without bounding it, the two
probabilistic inputs needed next: `NTrace R` and the entry `R p q`. -/
theorem twoBodyStability_remainder_equations {N : ℕ}
    (lambda : ℂ) (M₁ M₂ X R : Matrix (Fin N) (Fin N) ℂ)
    (p q : Fin N) (hR : twoBodyStability lambda M₁ M₂ X = R) :
    stabilityDenominator lambda (NTrace (M₁ * M₂)) * NTrace X =
        NTrace R ∧
      X p q = R p q +
        (lambda ^ 2 * NTrace X) * (M₁ * M₂) p q := by
  constructor
  · rw [← NTrace_twoBodyStability]
    rw [hR]
  · have hentry := congrFun (congrFun hR p) q
    unfold twoBodyStability at hentry
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hentry
    linear_combination hentry

/-- If the scalar stability coefficient is nonzero, the averaged error is
exactly the averaged remainder divided by it.  No estimate on that remainder
is assumed. -/
theorem NTrace_eq_remainder_div_stability {N : ℕ}
    (lambda : ℂ) (M₁ M₂ X R : Matrix (Fin N) (Fin N) ℂ)
    (hR : twoBodyStability lambda M₁ M₂ X = R)
    (hbeta : stabilityDenominator lambda (NTrace (M₁ * M₂)) ≠ 0) :
    NTrace X = NTrace R /
      stabilityDenominator lambda (NTrace (M₁ * M₂)) := by
  have h := congrArg NTrace hR
  rw [NTrace_twoBodyStability] at h
  exact (eq_div_iff hbeta).2 (by simpa [mul_comm] using h)

end CEHNative.BlockBand.External.CEH
