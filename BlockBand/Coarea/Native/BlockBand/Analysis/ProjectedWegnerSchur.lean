module

public import BlockBand.Coarea.Native.BlockBand.Analysis.SchurPositivity
public import BlockBand.Coarea.Native.BlockBand.Analysis.ProjectedResolventTrace
public import BlockBand.Coarea.Native.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Coarea.Native.BlockBand.Analysis.PSSSPoissonAveraging

/-!
# Schur complements for projected Wegner averaging

This file gives the deterministic and conditioned one-block step in the proof of the projected
Wegner lemma.  The exposed block is the
upper-left block of a `Matrix.fromBlocks` decomposition.  Its resolvent block
is exactly the inverse of the lower-right Schur complement, and the Schur
complement inherits the full matrix's positive imaginary regulator.

For an exposed GUE block, the resulting arbitrary positive absorber is then
written in the noncommuting Cauchy–Poisson form.  Each real Cauchy background
is an ordinary deterministic Hermitian deformation, so the PSSS
Poisson estimate applies slice by slice.  No conditioning or independence
claim beyond the explicit `BlockGUE.Law` parameter is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

universe u

/-- The upper-left block of the nonsingular inverse of a block matrix is the
nonsingular inverse of the lower-right Schur complement.  Invertibility of the
exterior and of the full matrix are explicit; Schur invertibility follows from
Mathlib's block factorization. -/
theorem nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)] :
    ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl =
      (schurComplement₂₂ A B C D)⁻¹ := by
  change ((Matrix.fromBlocks A B C D)⁻¹).submatrix Sum.inl Sum.inl =
    (A - B * ⅟D * C)⁻¹
  let _ : Invertible (A - B * ⅟D * C) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  rw [← Matrix.invOf_eq_nonsing_inv, ← Matrix.invOf_eq_nonsing_inv]
  exact invOf_fromBlocks_submatrix₁₁ A B C D

/-- Trace form of the exposed-block inverse identity, in the paper's
negative-imaginary normalization. -/
theorem neg_im_trace_submatrix_nonsing_inv_fromBlocks_eq_schurComplement₂₂
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)] :
    -((((Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl).trace).im =
      -(((schurComplement₂₂ A B C D)⁻¹).trace).im := by
  rw [nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂
    A B C D]

/-- Deterministic Schur step for projected Wegner averaging: the exposed resolvent trace
is the Schur-resolvent trace, while an `η I` lower bound on the full matrix
imaginary part passes to the Schur complement.  The two conclusions use the
same block convention and no commutativity assumption. -/
theorem exposedBlock_trace_eq_schur_and_regulator_posSemidef
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    [Invertible D] [Invertible (Matrix.fromBlocks A B C D)]
    {η : ℝ} (hη : 0 ≤ η)
    (him :
      (matrixImaginaryPart (Matrix.fromBlocks A B C D) -
        (η : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef) :
    -((((Matrix.fromBlocks A B C D)⁻¹).submatrix
      Sum.inl Sum.inl).trace).im =
        -(((schurComplement₂₂ A B C D)⁻¹).trace).im ∧
      (matrixImaginaryPart (schurComplement₂₂ A B C D) -
        (η : ℂ) • (1 : Matrix m m ℂ)).PosSemidef := by
  constructor
  · exact neg_im_trace_submatrix_nonsing_inv_fromBlocks_eq_schurComplement₂₂
      A B C D
  · exact schurComplement₂₂_imaginaryPart_sub_smul_one_posSemidef
      A B C D hη him

/-- A real Cauchy shift of a deterministic Hermitian deformation.  Positivity
of `Q` is retained in the parameter because this is precisely the absorber
used in the noncommuting Cauchy identity. -/
def BlockGUE.realBackground
    {k : ℕ} {d : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) (t : ℝ) :
    HermitianMatrix (BlockGUE.Index d) :=
  ⟨A₀.1 + (t : ℂ) • Q,
    A₀.2.add (hQ.isHermitian.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal t)))⟩

/-- Pointwise conditioned one-block reduction.  An arbitrary deterministic
positive absorber `Q + η I` is a standard-Cauchy average of real Hermitian
backgrounds, and each boundary resolvent is exactly the ordered Poisson sum
of the corresponding exposed-block GUE deformation. -/
theorem blockGUE_absorbedTrace_eq_integral_poissonEigenvalueSum
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) (ω : M.Ω) :
    -((((BlockGUE.deformed M A₀ ω : Matrix _ _ ℂ) +
      Complex.I • (Q + η • (1 : Matrix _ _ ℂ)))⁻¹).trace).im =
      ∫ t : ℝ, standardCauchyWeight t *
        BlockGUE.poissonEigenvalueSum M
          (BlockGUE.realBackground A₀ Q hQ t) 0 η ω := by
  rw [← integral_standardCauchyWeight_mul_neg_im_real_background_resolvent
    (BlockGUE.deformed M A₀ ω : Matrix _ _ ℂ) Q
    (BlockGUE.deformed M A₀ ω).property hQ hη]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  have hspectral :=
    neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      (BlockGUE.deformed M (BlockGUE.realBackground A₀ Q hQ t) ω)
      0 hη
  simpa [BlockGUE.poissonEigenvalueSum, centeredPoissonKernel,
    BlockGUE.deformed, BlockGUE.realBackground, add_assoc, add_left_comm,
    add_comm] using hspectral

/-- The conditioned absorbed one-block trace is nonnegative.  This is proved
through the exact Cauchy/Poisson reduction, rather than by an eigenbasis
commuting with the absorber. -/
theorem blockGUE_absorbedTrace_nonneg
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) {η : ℝ} (hη : 0 < η) (ω : M.Ω) :
    0 ≤ -((((BlockGUE.deformed M A₀ ω : Matrix _ _ ℂ) +
      Complex.I • (Q + η • (1 : Matrix _ _ ℂ)))⁻¹).trace).im := by
  rw [blockGUE_absorbedTrace_eq_integral_poissonEigenvalueSum
    hd M A₀ Q hQ hη ω]
  apply integral_nonneg
  intro t
  apply mul_nonneg
  · unfold standardCauchyWeight
    positivity
  · unfold BlockGUE.poissonEigenvalueSum
    exact Finset.sum_nonneg fun i _hi =>
      centeredPoissonKernel_nonneg hη

/-- For every fixed real Cauchy background, the PSSS input supplies
integrability and the sharp `π C dim` expectation bound.  This is the exact
slice estimate needed before Tonelli in the conditioned one-block argument;
its deformation may depend on the conditioned exterior through `A₀` and `Q`. -/
theorem psss_realBackground_poisson_integrable_and_integral_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) (t : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (BlockGUE.poissonEigenvalueSum M
      (BlockGUE.realBackground A₀ Q hQ t) 0 η) M.P ∧
      ∫ ω, BlockGUE.poissonEigenvalueSum M
          (BlockGUE.realBackground A₀ Q hQ t) 0 η ω ∂M.P ≤
        Real.pi * input.C *
          (Fintype.card (BlockGUE.Index d) : ℝ) :=
  psss_poissonEigenvalueSum_integrable_and_integral_le
    input hd M (BlockGUE.realBackground A₀ Q hQ t) 0 hη

/-- Weighted slice form used directly by Tonelli/Fubini: for every real
Cauchy parameter, the conditioned one-block boundary integrand is integrable
in the exposed GUE randomness and is bounded by the same Cauchy weight times
`π C dim`.  All dependence on the conditioned exterior remains inside the
explicit deterministic parameters `A₀` and `Q`. -/
theorem psss_weighted_realBackground_poisson_integrable_and_integral_le
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (Q : Matrix (BlockGUE.Index d) (BlockGUE.Index d) ℂ)
    (hQ : Q.PosSemidef) (t : ℝ) {η : ℝ} (hη : 0 < η) :
    Integrable (fun ω => standardCauchyWeight t *
      BlockGUE.poissonEigenvalueSum M
        (BlockGUE.realBackground A₀ Q hQ t) 0 η ω) M.P ∧
      ∫ ω, standardCauchyWeight t *
          BlockGUE.poissonEigenvalueSum M
            (BlockGUE.realBackground A₀ Q hQ t) 0 η ω ∂M.P ≤
        standardCauchyWeight t *
          (Real.pi * input.C *
            (Fintype.card (BlockGUE.Index d) : ℝ)) := by
  have hslice :=
    psss_realBackground_poisson_integrable_and_integral_le
      input hd M A₀ Q hQ t hη
  constructor
  · exact hslice.1.const_mul (standardCauchyWeight t)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hslice.2 (by
      unfold standardCauchyWeight
      positivity)

end CoareaNative.BlockBand
