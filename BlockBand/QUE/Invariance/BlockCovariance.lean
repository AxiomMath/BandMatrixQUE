module

public import BlockBand.QUE.Invariance.HermitianTests

/-!
# Physical weighted block covariance

The covariance of a Hermitian trace test under the physical law is the weighted sum of the
Frobenius norms of its rectangular blocks, hence invariant under conjugation by independently
chosen block unitaries (`hermitianTestVariance_blockUnitaryConjugation`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open Matrix BlockBand.QUE.Invariance

/-- The rectangular (k,l) block of a raw site matrix. -/
def siteMatrixBlock (p : BlockBand.Parameters) (A : p.SiteMatrix) (k l : ZMod p.n) :
    Matrix (Fin p.W) (Fin p.W) ℂ := fun a b => A (k,a) (l,b)

/-- The constant entry variance in a rectangular physical block. -/
def blockEntryVariance (p : BlockBand.Parameters) (k l : ZMod p.n) : ℝ :=
  if l = k then p.c / p.W else if l = k + 1 ∨ l = k - 1 then p.b / p.W else 0

theorem entryVariance_block (p : BlockBand.Parameters) (k l : ZMod p.n)
    (a b : Fin p.W) : p.entryVariance (k,a) (l,b) = p.blockEntryVariance k l := rfl

/-- Ordered-entry covariance is the weighted sum of rectangular norms. -/
theorem hermitianTestVariance_blocks (p : BlockBand.Parameters) (A : p.SiteMatrix) :
    p.hermitianTestVariance A =
      ∑ k : ZMod p.n, ∑ l : ZMod p.n,
        p.blockEntryVariance k l * frobeniusSq (p.siteMatrixBlock A k l) := by
  unfold hermitianTestVariance
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [entryVariance_block, frobeniusSq, siteMatrixBlock, Finset.mul_sum]

/-- Multiplication by a physical block diagonal matrix only sums inside the
matching block. -/
theorem blockUnitaryMatrix_mul_apply (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (A : p.SiteMatrix) (x y : p.Site) :
    (p.blockUnitaryMatrix U * A) x y =
      ∑ a : Fin p.W, U x.1 x.2 a * A (x.1,a) y := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type]

/-- The conjugated rectangular block is its left/right unitary transform. -/
theorem blockUnitaryConjugation_block (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (A : p.SiteMatrix)
    (k l : ZMod p.n) :
    p.siteMatrixBlock (p.blockUnitaryConjugation U A) k l =
      (U k : Matrix (Fin p.W) (Fin p.W) ℂ) * p.siteMatrixBlock A k l *
        (U l : Matrix (Fin p.W) (Fin p.W) ℂ)ᴴ := by
  ext a b
  simp [siteMatrixBlock, blockUnitaryConjugation, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, apply_ite]

/-- The physical covariance is invariant under independently chosen block unitaries
(deterministic, for every matrix). -/
theorem hermitianTestVariance_blockUnitaryConjugation (p : BlockBand.Parameters)
    (U : ZMod p.n → Matrix.unitaryGroup (Fin p.W) ℂ) (A : p.SiteMatrix) :
    p.hermitianTestVariance (p.blockUnitaryConjugation U A) = p.hermitianTestVariance A := by
  rw [p.hermitianTestVariance_blocks, p.hermitianTestVariance_blocks]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [p.blockUnitaryConjugation_block]
  have hf := frobeniusSq_unitary_both (U k) (star (U l)) (p.siteMatrixBlock A k l)
  exact congrArg (fun r : ℝ => p.blockEntryVariance k l * r) hf

end BlockBand.Parameters
