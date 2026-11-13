module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPLowerExpectation
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventLemma56

/-!
# Deterministic tensor lift of the CEH Gaussian-loop identities

The repository has no probability law for an independent `N*d` GUE block.
Accordingly this module proves the maximal exact lift currently justified:
every random matrix observable on the normalized `N`-coordinate law is
replicated pointwise by `X ↦ X ⊗ I_d`.  Bochner integrability and expectation
commute with this replication, deterministic two-resolvent
approximations replicate exactly, and the positive chain agrees exactly with
its four adjoint polarizations.  No claim is made that this tensor is
an independently sampled `N*d` GUE matrix.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal

/-- One entry of a tensor replicate is the original entry times the identity
Kronecker delta. -/
theorem tensorReplicate_apply {N d : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) (a b : Fin d) :
    tensorReplicate d X (i, a) (j, b) = X i j * (1 : Matrix (Fin d) (Fin d) ℂ) a b := by
  rfl

/-- Entrywise Bochner integrability is preserved by tensor
replication. -/
theorem Integrable.tensorReplicate_entry
    {N d : ℕ} {F : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ}
    {i j : Fin N} (hF : Integrable (fun y => F y i j)
      (normalizedGUEMeasure N)) (a b : Fin d) :
    Integrable (fun y => tensorReplicate d (F y) (i, a) (j, b))
      (normalizedGUEMeasure N) := by
  simpa only [tensorReplicate_apply] using
    hF.mul_const ((1 : Matrix (Fin d) (Fin d) ℂ) a b)

/-- Expectation commutes entrywise with tensor replication, with all
integrability made explicit. -/
theorem integral_tensorReplicate_entry
    {N d : ℕ} {F : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ}
    {i j : Fin N} (a b : Fin d) :
    (∫ y, tensorReplicate d (F y) (i, a) (j, b)
      ∂normalizedGUEMeasure N) =
      (∫ y, F y i j ∂normalizedGUEMeasure N) *
        (1 : Matrix (Fin d) (Fin d) ℂ) a b := by
  simp only [tensorReplicate_apply]
  rw [integral_mul_const]

/-- The replicated deterministic comparison appearing in every lifted
constellation is exactly `productTwoResolventApprox`; there is no finite-`d`
error. -/
theorem replicated_twoResolventApprox_exact
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (lambda : ℂ)
    (M₁ A M₂ : Matrix (Fin N) (Fin N) ℂ) :
    tensorReplicate d (twoResolventApprox lambda M₁ A M₂) =
      productTwoResolventApprox lambda (tensorReplicate d M₁)
        (tensorReplicate d A) (tensorReplicate d M₂) := by
  exact (productTwoResolventApprox_tensorReplicate hN hd lambda M₁ A M₂).symm

/-- Pointwise positive-chain replication, expressed through the repository's
positive-chain observable interface. -/
theorem replicated_positiveChain_exact
    {N d : ℕ} (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₁) *
        tensorReplicate d A *
        CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₂) *
        (tensorReplicate d A)ᴴ =
      tensorReplicate d
        (CEHNative.BlockBand.matrixImaginaryPart G₁ * A *
          CEHNative.BlockBand.matrixImaginaryPart G₂ * Aᴴ) := by
  exact (tensorReplicate_positiveChain G₁ A G₂).symm

/-- The normalized replicated positive-chain observable is exactly the
fourfold polarization of the four ordinary adjoint constellations. -/
theorem productNTrace_replicated_positiveChain_eq_fourfold
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (G₁ A G₂ : Matrix (Fin N) (Fin N) ℂ) :
    productNTrace
        (CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₁) *
          tensorReplicate d A *
          CEHNative.BlockBand.matrixImaginaryPart (tensorReplicate d G₂) *
          (tensorReplicate d A)ᴴ) =
      NTrace ((-(1 / 4 : ℂ)) •
        (G₁ * A * G₂ * Aᴴ + G₁ᴴ * A * G₂ᴴ * Aᴴ -
          G₁ * A * G₂ᴴ * Aᴴ - G₁ᴴ * A * G₂ * Aᴴ)) := by
  rw [productNTrace_replicated_positiveChain hN hd,
    positiveChainTrace_eq_fourfold]

end CEHNative.BlockBand.External.CEH
