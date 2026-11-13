module
public import BlockBand.SourceProcess.Stochastic.RankBarrier
public import BlockBand.SourceProcess.Stochastic.RankBarrier.CauchyBinet
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# `e_k(U*U) = ‖∧^k U‖²`

In the paper: "with `e_k` the `k`-th elementary symmetric function,
`e_k(U*U) = ‖∧^k U‖²_HS` by Cauchy–Binet, also at singular matrices". With minors indexed by
index functions `f : Fin k → ι`, `g : Fin k → c` (`minorSq`), the exact identity is

  `principalMinorSum k (Uᴴ U) = (∑_{f,g} |det U_{f,g}|²) / (k!)²`   (`principalMinorSum_gram`).

We also rewrite `e_k(B)` and `e_k(M − B)` as `minorSq` of the near rows `P V` and far rows
`(1 − P) V` (`nearMinor_fun`, `farMinor_fun`), using only `Pᴴ = P`, `P² = P`.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Equiv Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [Fintype c]

/-- `‖∧^k U‖²` in function-indexed form: `∑_{f,g} |det U_{f,g}|²` over `f : Fin k → ι`,
`g : Fin k → c` (each subset minor counted `(k!)²` times). -/
def minorSq (k : ℕ) (U : Matrix ι c ℂ) : ℝ :=
  ∑ p : (Fin k → ι) × (Fin k → c), ‖det (U.submatrix p.1 p.2)‖ ^ 2

theorem minorSq_nonneg (k : ℕ) (U : Matrix ι c ℂ) : 0 ≤ minorSq k U :=
  Finset.sum_nonneg fun _ _ => by positivity

omit [Fintype c] in
/-- One column-function slice of Cauchy–Binet for the Gram matrix. -/
theorem factorial_mul_det_gram_submatrix (k : ℕ) (U : Matrix ι c ℂ) (g : Fin k → c) :
    (k.factorial : ℂ) * det ((Uᴴ * U).submatrix g g) =
      ∑ f : Fin k → ι, ((‖det (U.submatrix f g)‖ ^ 2 : ℝ) : ℂ) := by
  have hm : (Uᴴ * U).submatrix g g = (U.submatrix id g)ᴴ * (U.submatrix id g) := by
    ext a b; simp [mul_apply]
  have hp : (Fintype.card (Perm (Fin k)) : ℂ) = k.factorial := by
    simp [Fintype.card_perm]
  rw [hm, ← hp, cauchyBinet]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, submatrix_submatrix]
  simp only [Function.comp_id, Function.id_comp, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/-- **Cauchy–Binet for Gram matrices**: `e_k(UᴴU) = ∑_{f,g} |det U_{f,g}|² / (k!)²`. -/
theorem principalMinorSum_gram [DecidableEq c] (k : ℕ) (U : Matrix ι c ℂ) :
    principalMinorSum k (Uᴴ * U) = minorSq k U / (k.factorial : ℝ) ^ 2 := by
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  set S := ∑ s ∈ (Finset.univ : Finset c).powersetCard k, det (principalSub (Uᴴ * U) s)
  have hS : (k.factorial : ℂ) ^ 2 * S = ((minorSq k U : ℝ) : ℂ) := by
    rw [sq, mul_assoc, ← sum_det_submatrix_self, Finset.mul_sum]
    simp_rw [factorial_mul_det_gram_submatrix]
    rw [minorSq, Fintype.sum_prod_type, Finset.sum_comm]
    push_cast
    rfl
  have hS' : S = (((minorSq k U / (k.factorial : ℝ) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_div, ← hS]
    push_cast
    field_simp
  change S.re = _
  rw [hS', Complex.ofReal_re]

omit [Fintype c] in
/-- `B = VᴴPV = (PV)ᴴ(PV)` for a Hermitian idempotent `P`. -/
theorem nearGram_eq (P : Matrix ι ι ℂ) (hPH : Pᴴ = P) (hPP : P * P = P) (W : Matrix ι c ℂ) :
    nearGram P W = (P * W)ᴴ * (P * W) := by
  simp only [nearGram, conjTranspose_mul, hPH, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Wᴴ P P, hPP]

omit [Fintype c] in
/-- `M − B = Vᴴ(1−P)V = ((1−P)V)ᴴ((1−P)V)` for a Hermitian idempotent `P`. -/
theorem farGram_eq [DecidableEq ι] (P : Matrix ι ι ℂ) (hPH : Pᴴ = P) (hPP : P * P = P) (W : Matrix ι c ℂ) :
    sourceGram W - nearGram P W = ((1 - P) * W)ᴴ * ((1 - P) * W) := by
  have h1 : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPH, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P)ᴴ, h1, sourceGram, nearGram,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]

/-- `e_k(B)` as a function of the frame: `minorSq` of the near rows. -/
theorem nearMinor_fun [DecidableEq c] (k : ℕ) (P : Matrix ι ι ℂ) (hPH : Pᴴ = P) (hPP : P * P = P) :
    (fun W : Matrix ι c ℂ => principalMinorSum k (nearGram P W)) =
      fun W => minorSq k (P * W) / (k.factorial : ℝ) ^ 2 := by
  funext W
  rw [nearGram_eq P hPH hPP, principalMinorSum_gram]

/-- `e_k(M − B)` as a function of the frame: `minorSq` of the far rows. -/
theorem farMinor_fun [DecidableEq ι] [DecidableEq c] (k : ℕ) (P : Matrix ι ι ℂ) (hPH : Pᴴ = P) (hPP : P * P = P) :
    (fun W : Matrix ι c ℂ => principalMinorSum k (sourceGram W - nearGram P W)) =
      fun W => minorSq k ((1 - P) * W) / (k.factorial : ℝ) ^ 2 := by
  funext W
  rw [farGram_eq P hPH hPP, principalMinorSum_gram]

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
