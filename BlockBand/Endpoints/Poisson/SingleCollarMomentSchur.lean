module

public import BlockBand.Internal.Contracts.Inputs

/-!
# Schur elimination of scalar matched blocks (deterministic algebra)

* `scm_det_schur`: for `X` on `ι` with `X_{MM} = z I` on the sites `M = {p}`,
  `det X = z^{|M|} det(X_{RR} - z⁻¹ X_{RM} X_{MR})` (`R` the complement).
* `scm_smul_inv_eq`: `-z⁻¹ G = -(Re z/|z|²) G + i (Im z/|z|²) G`, the split of the Schur term
  into the Hermitian deformation and the absorber `Y = Im z |z|⁻² G`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Matrix

section Schur

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The rest-rest block `X_{RR}` (sites outside `p`). -/
abbrev scmRR (p : ι → Prop) (X : Matrix ι ι ℂ) : Matrix {i // ¬ p i} {i // ¬ p i} ℂ :=
  X.submatrix Subtype.val Subtype.val

/-- The rest-matched block `X_{RM}`. -/
abbrev scmRM (p : ι → Prop) (X : Matrix ι ι ℂ) : Matrix {i // ¬ p i} {i // p i} ℂ :=
  X.submatrix Subtype.val Subtype.val

/-- The matched-rest block `X_{MR}`. -/
abbrev scmMR (p : ι → Prop) (X : Matrix ι ι ℂ) : Matrix {i // p i} {i // ¬ p i} ℂ :=
  X.submatrix Subtype.val Subtype.val

/-- **Schur elimination of a scalar block.** If the block of `X` on `{p}` is `z I` with `z ≠ 0`,
then `det X = z^{|{p}|} det(X_{RR} - z⁻¹ X_{RM} X_{MR})`. -/
theorem scm_det_schur (p : ι → Prop) [DecidablePred p] (X : Matrix ι ι ℂ) (z : ℂ) (hz : z ≠ 0)
    (hMM : ∀ i j : {i // p i}, X i j = if i = j then z else 0) :
    X.det = z ^ Fintype.card {i // p i} *
      (scmRR p X - z⁻¹ • (scmRM p X * scmMR p X)).det := by
  rw [← det_reindex_self (Equiv.sumCompl p).symm X]
  have hX : reindex (Equiv.sumCompl p).symm (Equiv.sumCompl p).symm X =
      fromBlocks (z • (1 : Matrix {i // p i} {i // p i} ℂ)) (scmMR p X) (scmRM p X)
        (scmRR p X) := by
    ext (i | i) (j | j)
    · simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.sumCompl_apply_inl,
        fromBlocks_apply₁₁, Matrix.smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      exact hMM i j
    · rfl
    · rfl
    · rfl
  let hinv : Invertible (z • (1 : Matrix {i // p i} {i // p i} ℂ)) :=
    ⟨z⁻¹ • 1, by rw [smul_mul_smul_comm, inv_mul_cancel₀ hz, one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hz, one_mul, one_smul]⟩
  rw [hX, det_fromBlocks₁₁]
  congr 1
  · rw [det_smul, det_one, mul_one]
  · congr 2
    show scmRM p X * (z⁻¹ • 1) * scmMR p X = _
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- `passiveLog` is invariant under simultaneous reindexing of `X` and `Q`. -/
theorem scm_passiveLog_reindex {κ : Type} [Fintype κ] [DecidableEq κ] (σ : ι ≃ κ)
    (X Q : Matrix ι ι ℂ) (a e : ℝ) :
    BlockBand.Internal.Contracts.Inputs.passiveLog (reindex σ σ X) (reindex σ σ Q) a e =
      BlockBand.Internal.Contracts.Inputs.passiveLog X Q a e := by
  unfold BlockBand.Internal.Contracts.Inputs.passiveLog
  have h : ∀ c : ℂ, reindex σ σ X - (e : ℂ) • (1 : Matrix κ κ ℂ) + c • reindex σ σ Q =
      reindex σ σ (X - (e : ℂ) • (1 : Matrix ι ι ℂ) + c • Q) := by
    intro c
    ext i j
    simp [reindex_apply, one_apply]
  have h0 := h 0
  simp only [zero_smul, add_zero] at h0
  rw [h, h0, det_reindex_self, det_reindex_self]

/-- `-z⁻¹ G = -(Re z/|z|²) G + i (Im z/|z|²) G`. -/
theorem scm_smul_inv_eq {κ : Type*} (z : ℂ) (G : Matrix κ κ ℂ) :
    z⁻¹ • G = ((z.re / Complex.normSq z : ℝ) : ℂ) • G -
      Complex.I • (((z.im / Complex.normSq z : ℝ) : ℂ) • G) := by
  rw [smul_smul, ← sub_smul]
  congr 1
  rw [Complex.inv_def]
  apply Complex.ext <;>
    simp [div_eq_mul_inv]

end Schur

end BlockBand.Endpoints
