module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorGaussianLaplace
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalFixedVectorTail
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GaussianOrthogonalInvariance

/-!
# Complex matrix realification for the spherical Gaussian small-ball estimate

This module supplies the exact deterministic bridge from a complex matrix to its
positive real Gram matrix.  It records both pointwise quadratic-form preservation and
the factor-two Frobenius identity.  These normalizations are the input required before
applying the diagonal Gaussian Laplace product.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory

/-- The positive real Gram matrix associated with the realification of a complex
matrix. -/
def complexGramRealification {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℝ :=
  (complexMatrixRealification Q)ᵀ * complexMatrixRealification Q

/-- The realified Gram matrix is symmetric. -/
theorem complexGramRealification_isSymm {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    (complexGramRealification Q).IsSymm := by
  unfold complexGramRealification Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The realified Gram quadratic form is exactly the squared complex image norm,
with no normalization loss. -/
theorem dotProduct_complexGramRealification {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    dotProduct (complexVectorRealification z)
        (complexGramRealification Q *ᵥ complexVectorRealification z) =
      ∑ i : Fin N, ‖(Q *ᵥ z) i‖ ^ 2 := by
  let R := complexMatrixRealification Q
  let x := complexVectorRealification z
  have hmul : complexGramRealification Q *ᵥ x = Rᵀ *ᵥ (R *ᵥ x) := by
    simp [complexGramRealification, R, Matrix.mulVec_mulVec]
  rw [hmul]
  have hadj : dotProduct x (Rᵀ *ᵥ (R *ᵥ x)) = dotProduct (R *ᵥ x) (R *ᵥ x) :=
    Matrix.dotProduct_transpose_mulVec R x (R *ᵥ x)
  rw [hadj, show R *ᵥ x = complexVectorRealification (Q *ᵥ z) from
    complexMatrixRealification_mulVec Q z]
  unfold dotProduct
  simpa only [pow_two] using sum_sq_complexVectorRealification (Q *ᵥ z)

/-- Entrywise squared mass of the realification is exactly twice the complex
Frobenius squared mass.  The factor two comes from the two identical real/imaginary
blocks and is the critical normalization for the Gaussian spectral weights. -/
theorem sum_sq_complexMatrixRealification {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    ∑ p : Fin N × Fin 2, ∑ q : Fin N × Fin 2,
        complexMatrixRealification Q p q ^ 2 =
      2 * ∑ i : Fin N, ∑ j : Fin N, ‖Q i j‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp [complexMatrixRealification, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.sq_norm, Complex.normSq_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The trace of the positive real Gram matrix is twice the squared complex
Frobenius mass. -/
theorem trace_complexGramRealification {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) :
    (complexGramRealification Q).trace =
      2 * ∑ i : Fin N, ∑ j : Fin N, ‖Q i j‖ ^ 2 := by
  rw [show (complexGramRealification Q).trace =
      ∑ p : Fin N × Fin 2, ∑ q : Fin N × Fin 2,
        complexMatrixRealification Q q p ^ 2 by
    unfold complexGramRealification Matrix.trace
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp [Matrix.transpose_apply, pow_two]]
  rw [Finset.sum_comm]
  exact sum_sq_complexMatrixRealification Q

/-- Orthogonal spectral diagonalization of the realified complex image norm.  The
weights are the eigenvalues of the positive Gram operator, and the coordinates
are taken in its orthonormal eigenbasis. -/
theorem complexGramRealification_spectralQuadraticForm {N : ℕ}
    (Q : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    let T := Matrix.toEuclideanLin (complexGramRealification Q)
    let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
    let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
        Fintype.card (Fin N × Fin 2) := by simp
    ∑ k, hT.eigenvalues hdim k *
        ((hT.eigenvectorBasis hdim).repr
          (WithLp.toLp 2 (complexVectorRealification z)) k) ^ 2 =
      ∑ i : Fin N, ‖(Q *ᵥ z) i‖ ^ 2 := by
  dsimp only
  let T := Matrix.toEuclideanLin (complexGramRealification Q)
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (complexGramRealification_isSymm Q))
  let hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × Fin 2)) =
      Fintype.card (Fin N × Fin 2) := by simp
  have hdiag := hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hdim
    (WithLp.toLp 2 (complexVectorRealification z))
  change (∑ k, hT.eigenvalues hdim k *
      ((hT.eigenvectorBasis hdim).repr
        (WithLp.toLp 2 (complexVectorRealification z)) k) ^ 2) = _
  rw [show (∑ k, hT.eigenvalues hdim k *
      ((hT.eigenvectorBasis hdim).repr
        (WithLp.toLp 2 (complexVectorRealification z)) k) ^ 2) =
      RCLike.re (inner ℝ (T (WithLp.toLp 2 (complexVectorRealification z)))
        (WithLp.toLp 2 (complexVectorRealification z))) by
        simpa only [Real.norm_eq_abs, sq_abs] using hdiag.symm]
  change dotProduct (complexVectorRealification z)
      (complexGramRealification Q *ᵥ complexVectorRealification z) = _
  exact dotProduct_complexGramRealification Q z

end PSSSNative.BlockBand.PSSS
