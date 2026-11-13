module
public import BlockBand.SourceProcess.Stochastic.FiniteSource
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Step 9 bridge, part 1: ambient Gram states are feasible

`gramFeasible_of_twoProjection`: a constrained frame `V` (any finite ambient index type `ι`,
`P` Hermitian idempotent, `TwoProjection P 𝖣 V`) has a feasible Gram pair: reindexing `ι ≃ Fin n`
gives the realization required by `GramFeasible`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

omit [DecidableEq ι] in
theorem trace_submatrix_equiv {n : Type*} [Fintype n] (A : Matrix ι ι ℂ) (e : n ≃ ι) :
    (A.submatrix e e).trace = A.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => A i i)

omit [DecidableEq ι] [DecidableEq c] in
theorem gramFeasible_of_twoProjection {P : Matrix ι ι ℂ} {D : Matrix c c ℂ} {V : Matrix ι c ℂ}
    (hPH : Pᴴ = P) (hPP : P * P = P) (hV : TwoProjection P D V) :
    GramFeasible D (gramPair P V) := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  set r : c ≃ c := Equiv.refl c
  have hDr : D = D.submatrix r r := (submatrix_id_id D).symm
  have hgp : gramProjection (P.submatrix e e) (V.submatrix e r) D =
      (gramProjection P V D).submatrix e e := by
    unfold gramProjection
    rw [hDr, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, ← hDr]
    rfl
  refine ⟨Fintype.card ι, P.submatrix e e, V.submatrix e r, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [conjTranspose_submatrix, hPH]
  · rw [submatrix_mul_equiv, hPP]
  · rw [hgp, conjTranspose_submatrix, hV.1]
  · rw [hgp, submatrix_mul_equiv, hV.2.1]
  · rw [hgp, trace_submatrix_equiv, trace_submatrix_equiv, hV.2.2]
  · simp only [gramPair, sourceGram, nearGram, conjTranspose_submatrix, submatrix_mul_equiv]
    simp [r]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
