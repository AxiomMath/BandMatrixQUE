module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWickGenPoly

/-!
# Rank-one realisation of the contraction rule `E[dB_ab dB_cd] = κ(P_ad P'_cb + P'_ad P_cb)`

* `wg_sum_trace_mul_trace`: `Σ_{α,β} [Tr(AU)Tr(BV) + Tr(AV)Tr(BU)] = Tr(APBP') + Tr(AP'BP)`
  (the `crossTerm` contraction `E Tr(A dB)Tr(B dB)`);
* `wg_sum_trace_mul_mul`: `Σ_{α,β} [Tr(AUBV) + Tr(AVBU)] = Tr(AP)Tr(BP') + Tr(AP')Tr(BP)`
  (the `pairTerm` contraction `E Tr(A dB B dB)`).

The two Hermitian directions `K₀ = U + V`, `K₁ = i(U - V)` (`wg_dir`) polarise the mixed products:
`Σ_c Tr(AK_c)Tr(BK_c) = 2[Tr(AU)Tr(BV) + Tr(AV)Tr(BU)]`, `Σ_c Tr(AK_cBK_c) = 2[Tr(AUBV) + Tr(AVBU)]`,
and on a vector `Σ_c (Re v*K_c v)² = 4|v*Uv|²` (`wg_sum_re_sq_dir`).

With `Q = R²`, `R* = R`, the conjugated direction `H = RKR` satisfies
`Tr(Q^a H Q^b H) = Tr(Q^{a+1} K Q^{b+1} K)` (`wg_trace_sandwich`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix Finset

variable {ι : Type} [Fintype ι]

/-!
## Rank-one traces
-/

theorem wg_trace_mul_vecMulVec (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    (A * vecMulVec x y).trace = y ⬝ᵥ (A *ᵥ x) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, vecMulVec_apply, dotProduct,
    mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem wg_vecMulVec_mul_mul_vecMulVec (B : Matrix ι ι ℂ) (x y z t : ι → ℂ) :
    vecMulVec x y * B * vecMulVec z t = (y ⬝ᵥ (B *ᵥ z)) • vecMulVec x t := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct,
    mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- `Tr(A x y*) Tr(B z t*) = Tr(A x t* B z y*)`. -/
theorem wg_trace_mul_trace_eq (A B : Matrix ι ι ℂ) (x y z t : ι → ℂ) :
    (A * vecMulVec x y).trace * (B * vecMulVec z t).trace =
      (A * vecMulVec x t * B * vecMulVec z y).trace := by
  rw [Matrix.mul_assoc A, Matrix.mul_assoc A, wg_vecMulVec_mul_mul_vecMulVec, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    wg_trace_mul_vecMulVec B]
  ring

/-!
## The contraction rule
-/

section Family

variable {α β : Type} [Fintype α] [Fintype β]

theorem wg_sum_trace_four (A B : Matrix ι ι ℂ) (X : α → Matrix ι ι ℂ) (Y : β → Matrix ι ι ℂ) :
    ∑ a, ∑ b, (A * X a * B * Y b).trace = (A * (∑ a, X a) * B * (∑ b, Y b)).trace := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  rw [Finset.sum_comm]

/-- **`crossTerm` contraction**: `Σ_{α,β}[Tr(AU)Tr(BV) + Tr(AV)Tr(BU)] = Tr(APBP') + Tr(AP'BP)`. -/
theorem wg_sum_trace_mul_trace (A B P P' : Matrix ι ι ℂ) (u : α → ι → ℂ) (w : β → ι → ℂ)
    (hu : ∑ a, vecMulVec (u a) (star (u a)) = P) (hw : ∑ b, vecMulVec (w b) (star (w b)) = P') :
    ∑ a, ∑ b, ((A * vecMulVec (u a) (star (w b))).trace * (B * vecMulVec (w b) (star (u a))).trace +
        (A * vecMulVec (w b) (star (u a))).trace * (B * vecMulVec (u a) (star (w b))).trace) =
      (A * P * B * P').trace + (A * P' * B * P).trace := by
  simp only [wg_trace_mul_trace_eq, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => (A * vecMulVec (w b) (star (w b)) * B *
    vecMulVec (u a) (star (u a))).trace), wg_sum_trace_four, wg_sum_trace_four, hu, hw]

/-- **`pairTerm` contraction**: `Σ_{α,β}[Tr(AUBV) + Tr(AVBU)] = Tr(AP)Tr(BP') + Tr(AP')Tr(BP)`. -/
theorem wg_sum_trace_mul_mul (A B P P' : Matrix ι ι ℂ) (u : α → ι → ℂ) (w : β → ι → ℂ)
    (hu : ∑ a, vecMulVec (u a) (star (u a)) = P) (hw : ∑ b, vecMulVec (w b) (star (w b)) = P') :
    ∑ a, ∑ b, ((A * vecMulVec (u a) (star (w b)) * B * vecMulVec (w b) (star (u a))).trace +
        (A * vecMulVec (w b) (star (u a)) * B * vecMulVec (u a) (star (w b))).trace) =
      (A * P).trace * (B * P').trace + (A * P').trace * (B * P).trace := by
  simp only [← wg_trace_mul_trace_eq, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Matrix.trace_sum, hu, hw]

end Family

/-!
## Two Hermitian directions
-/

/-- `K₀ = U + V`, `K₁ = i(U - V)`. -/
def wg_dir (U V : Matrix ι ι ℂ) : Fin 2 → Matrix ι ι ℂ :=
  ![U + V, Complex.I • (U - V)]

omit [Fintype ι] in
theorem wg_isHermitian_dir (U : Matrix ι ι ℂ) (c : Fin 2) : (wg_dir U Uᴴ c).IsHermitian := by
  unfold Matrix.IsHermitian
  fin_cases c
  · simp only [wg_dir, Fin.zero_eta, Matrix.cons_val_zero]
    rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  · simp only [wg_dir, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, Complex.star_def,
      Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem wg_sum_dir_trace_mul_trace (A B U V : Matrix ι ι ℂ) :
    ∑ c, (A * wg_dir U V c).trace * (B * wg_dir U V c).trace =
      2 * ((A * U).trace * (B * V).trace + (A * V).trace * (B * U).trace) := by
  simp only [Fin.sum_univ_two, wg_dir, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_sub, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem wg_sum_dir_trace_mul_mul (A B U V : Matrix ι ι ℂ) :
    ∑ c, (A * wg_dir U V c * B * wg_dir U V c).trace =
      2 * ((A * U * B * V).trace + (A * V * B * U).trace) := by
  simp only [Fin.sum_univ_two, wg_dir, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul,
    smul_sub, smul_smul]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem wg_dotProduct_conjTranspose (U : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (Uᴴ *ᵥ v) = star (star v ⬝ᵥ (U *ᵥ v)) := by
  rw [dotProduct_mulVec, ← star_mulVec, Matrix.star_dotProduct]

/-- `Σ_c (Re v*K_c v)² = 4 |v*Uv|²` for `V = U*`. -/
theorem wg_sum_re_sq_dir (U : Matrix ι ι ℂ) (v : ι → ℂ) :
    ∑ c, ((star v ⬝ᵥ (wg_dir U Uᴴ c *ᵥ v)).re) ^ 2 = 4 * Complex.normSq (star v ⬝ᵥ (U *ᵥ v)) := by
  simp only [Fin.sum_univ_two, wg_dir, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    add_mulVec, smul_mulVec, sub_mulVec, dotProduct_add, dotProduct_smul, dotProduct_sub,
    wg_dotProduct_conjTranspose, smul_eq_mul]
  set z := star v ⬝ᵥ (U *ᵥ v)
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.I_re,
    Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- `v*(x y*)v = (v*x)(y*v)`. -/
theorem wg_dotProduct_vecMulVec (x y v : ι → ℂ) :
    star v ⬝ᵥ (vecMulVec x (star y) *ᵥ v) = (star v ⬝ᵥ x) * (star y ⬝ᵥ v) := by
  rw [vecMulVec_mulVec]
  simp only [dotProduct, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- `Σ_α |v*u_α|² = v*Pv` for `P = Σ_α u_α u_α*`. -/
theorem wg_sum_normSq_dotProduct {α : Type} [Fintype α] (P : Matrix ι ι ℂ) (u : α → ι → ℂ)
    (hu : ∑ a, vecMulVec (u a) (star (u a)) = P) (v : ι → ℂ) :
    ((∑ a, Complex.normSq (star v ⬝ᵥ u a) : ℝ) : ℂ) = star v ⬝ᵥ (P *ᵥ v) := by
  rw [← hu, Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wg_dotProduct_vecMulVec, ← Complex.mul_conj, ← Complex.star_def, Matrix.star_dotProduct,
    star_star]

/-!
## The square-root sandwich
-/

theorem wg_sqrt_pow_mul [DecidableEq ι] {Q R : Matrix ι ι ℂ} (hR : R * R = Q) (n : ℕ) :
    R * Q ^ n * R = Q ^ (n + 1) := by
  have hQ : ∀ k, Q ^ k = R ^ (2 * k) := fun k => by rw [pow_mul, sq, hR]
  rw [hQ, hQ, ← pow_succ', ← pow_succ]
  ring_nf

/-- `Tr(Q^a (RKR) Q^b (RKR)) = Tr(Q^{a+1} K Q^{b+1} K)`. -/
theorem wg_trace_sandwich [DecidableEq ι] {Q R : Matrix ι ι ℂ} (hR : R * R = Q)
    (K : Matrix ι ι ℂ) (a b : ℕ) :
    (Q ^ a * (R * K * R) * Q ^ b * (R * K * R)).trace =
      (Q ^ (a + 1) * K * Q ^ (b + 1) * K).trace := by
  rw [← wg_sqrt_pow_mul hR, ← wg_sqrt_pow_mul hR]
  rw [show Q ^ a * (R * K * R) * Q ^ b * (R * K * R) =
      (Q ^ a * (R * K * R) * Q ^ b * (R * K)) * R by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `Tr(Q^a (RKR)) = Tr(Q^{a+1} K)`. -/
theorem wg_trace_sandwich_one [DecidableEq ι] {Q R : Matrix ι ι ℂ} (hR : R * R = Q)
    (K : Matrix ι ι ℂ) (a : ℕ) :
    (Q ^ a * (R * K * R)).trace = (Q ^ (a + 1) * K).trace := by
  rw [← wg_sqrt_pow_mul hR, show Q ^ a * (R * K * R) = (Q ^ a * (R * K)) * R by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The `s`-coefficient of `Tr(Q + sRKR)^r`: `Tr A_r = r Tr(Q^r K)`. -/
theorem wg_trace_A_sandwich [DecidableEq ι] {Q R : Matrix ι ι ℂ} (hR : R * R = Q)
    (K : Matrix ι ι ℂ) (r : ℕ) :
    (wg_A Q (R * K * R) r).trace = (r : ℂ) * (Q ^ r * K).trace := by
  rw [wg_A_eq, Matrix.trace_sum]
  rw [Finset.sum_congr rfl fun i hi => ?_, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hi' : i < r := Finset.mem_range.1 hi
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_add,
    show r - 1 - i + i = r - 1 by omega, wg_trace_sandwich_one hR, show r - 1 + 1 = r by omega]

/-- The `s²`-coefficient of `Tr(Q + sRKR)^r`:
`Tr B_r = Σ_{i<r} Σ_{i<j<r} Tr(Q^{r-(j-i)} K Q^{j-i} K)`. -/
theorem wg_trace_B_sandwich [DecidableEq ι] {Q R : Matrix ι ι ℂ} (hR : R * R = Q)
    (K : Matrix ι ι ℂ) (r : ℕ) :
    (wg_B Q (R * K * R) r).trace = ∑ i ∈ range r, ∑ j ∈ Ioo i r,
      (Q ^ (r - (j - i)) * K * Q ^ (j - i) * K).trace := by
  rw [wg_B_eq, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Ioo.1 hj
  rw [Matrix.trace_mul_comm,
    show Q ^ (r - 1 - j) * (Q ^ i * (R * K * R) * Q ^ (j - i - 1) * (R * K * R)) =
      Q ^ (r - 1 - j + i) * (R * K * R) * Q ^ (j - i - 1) * (R * K * R) by
        rw [pow_add]; simp only [Matrix.mul_assoc],
    wg_trace_sandwich hR, show r - 1 - j + i + 1 = r - (j - i) by omega,
    show j - i - 1 + 1 = j - i by omega]

end BlockBand.Endpoints
