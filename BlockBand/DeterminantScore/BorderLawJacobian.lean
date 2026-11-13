module

public import BlockBand.DeterminantScore.BorderLawCharpoly

/-!
# Diagonal border law: the Jacobian of `λ ↦ (r(λ), a(λ))`

`borderCoord μ λ = (r(λ), a(λ))` (`r_i(λ) = -∏_j(μ_i - λ_j)/c_i`, `a(λ) = Σλ - Σμ`, `a` in the last
slot) is polynomial with derivative the matrix `borderJac μ λ` (`hasFDerivAt_borderCoord`).
Factor `borderJac = jacLeft μ · jacRight λ`, where column `q` of `jacRight λ` holds the
coefficients of `∏_{l≠q}(X - λ_l)`; then `Vand(λ) · jacRight λ = diag(∏_{l≠q}(λ_q - λ_l))` and
`jacLeft μ` is a row-scaled Vandermonde matrix bordered by a unit row. Hence, for strictly
increasing `μ`, `λ`, `|det borderJac μ λ| = Δ(λ)/Δ(μ)` (`abs_det_borderJac`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open Matrix Polynomial

variable {n : ℕ}

/-- Coordinates `(r(λ), a(λ))` packed into `Fin (n+1) → ℝ` (`a` in the last slot). -/
def borderCoord (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (arrowWeight μ lam) (arrowCorner μ lam)

/-- The Jacobian matrix of `borderCoord μ` at `λ`. -/
def borderJac (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun p q => Fin.snoc (α := fun _ => ℝ)
    (fun i => (∏ l ∈ Finset.univ.erase q, (μ i - lam l)) / arrowDenom μ i) 1 p

/-- `borderCoord μ` has derivative `borderJac μ λ` at `λ`. -/
theorem hasFDerivAt_borderCoord (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) :
    HasFDerivAt (borderCoord μ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (borderJac μ lam))) lam := by
  refine hasFDerivAt_pi'.2 fun p => ?_
  induction p using Fin.lastCases with
  | last =>
    have hf : (fun x => borderCoord μ x (Fin.last n)) = fun x => ∑ j, x j - ∑ i, μ i := by
      funext x; simp [borderCoord, arrowCorner]
    rw [hf]
    refine ((HasFDerivAt.fun_sum fun j _ => hasFDerivAt_apply j lam).sub_const _).congr_fderiv ?_
    ext h
    simp [borderJac, Matrix.mulVec, dotProduct]
  | cast i =>
    have hf : (fun x => borderCoord μ x i.castSucc) =
        fun x => -(arrowDenom μ i)⁻¹ * ∏ j, (μ i - x j) := by
      funext x; simp [borderCoord, arrowWeight, div_eq_mul_inv, mul_comm]
    rw [hf]
    have hP : HasFDerivAt (fun x : Fin (n + 1) → ℝ => ∏ j ∈ Finset.univ, (μ i - x j))
        (∑ j ∈ Finset.univ, (∏ l ∈ Finset.univ.erase j, (μ i - lam l)) •
          -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j)) lam :=
      HasFDerivAt.finsetProd (g := fun j (x : Fin (n + 1) → ℝ) => μ i - x j)
        fun j _ => (hasFDerivAt_apply j lam).const_sub (μ i)
    refine (hP.const_mul _).congr_fderiv ?_
    ext h
    simp [borderJac, Matrix.mulVec, dotProduct, Finset.mul_sum, div_eq_mul_inv, mul_comm,
      mul_left_comm]

/-- Determinant of the derivative as a continuous linear map. -/
theorem det_borderJac_toCLM (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) :
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (borderJac μ lam))).det =
      (borderJac μ lam).det := by
  rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin']

/-!
## The Jacobian determinant
-/

/-- Left factor: rows `(μ_i^k / c_i)_k` and the last unit row `e_n`. -/
def jacLeft (μ : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun p k => Fin.snoc (α := fun _ => ℝ)
    (fun i => μ i ^ (k : ℕ) / arrowDenom μ i) (if k = Fin.last n then 1 else 0) p

/-- Right factor: column `q` holds the coefficients of `∏_{l≠q}(X - λ_l)`. -/
def jacRight (lam : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k q => (∏ l ∈ Finset.univ.erase q, (X - C (lam l))).coeff k

/-- `deg ∏_{l≠q}(X - λ_l) = n`. -/
theorem natDegree_prod_erase (lam : Fin (n + 1) → ℝ) (q : Fin (n + 1)) :
    (∏ l ∈ Finset.univ.erase q, (X - C (lam l))).natDegree = n := by
  rw [← Lagrange.nodal, Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ q),
    Finset.card_univ, Fintype.card_fin]
  rfl

/-- Evaluation of `∏_{l≠q}(X - λ_l)` through its coefficients. -/
theorem sum_mul_coeff_eq_eval (lam : Fin (n + 1) → ℝ) (q : Fin (n + 1)) (x : ℝ) :
    ∑ k : Fin (n + 1), x ^ (k : ℕ) * (∏ l ∈ Finset.univ.erase q, (X - C (lam l))).coeff k =
      ∏ l ∈ Finset.univ.erase q, (x - lam l) := by
  have h := eval_eq_sum_range' (n := n + 1) (p := ∏ l ∈ Finset.univ.erase q, (X - C (lam l)))
    (by rw [natDegree_prod_erase]; omega) x
  rw [eval_prod] at h
  simp only [eval_sub, eval_X, eval_C] at h
  rw [h, Finset.sum_range]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- `borderJac μ λ = jacLeft μ · jacRight λ`. -/
theorem borderJac_eq_mul (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) :
    borderJac μ lam = jacLeft μ * jacRight lam := by
  ext p q
  rw [Matrix.mul_apply]
  induction p using Fin.lastCases with
  | last =>
    simp only [borderJac, jacLeft, jacRight, Matrix.of_apply, Fin.snoc_last, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h := (Lagrange.nodal_monic (s := Finset.univ.erase q) (v := lam)).coeff_natDegree
    rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ q),
      Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  | cast i =>
    simp only [borderJac, jacLeft, jacRight, Matrix.of_apply, Fin.snoc_castSucc]
    rw [← sum_mul_coeff_eq_eval lam q (μ i), Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- `Vand(λ) · jacRight λ` is diagonal. -/
theorem vandermonde_mul_jacRight (lam : Fin (n + 1) → ℝ) :
    Matrix.vandermonde lam * jacRight lam =
      diagonal fun q => ∏ l ∈ Finset.univ.erase q, (lam q - lam l) := by
  ext m q
  simp only [Matrix.mul_apply, Matrix.vandermonde_apply, jacRight, Matrix.of_apply,
    sum_mul_coeff_eq_eval, diagonal_apply]
  split_ifs with hmq
  · rw [hmq]
  · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hmq, Finset.mem_univ m⟩) (sub_self _)

/-- Determinant of the left factor (expansion along the unit row). -/
theorem det_jacLeft (μ : Fin n → ℝ) :
    (jacLeft μ).det = (∏ i, (arrowDenom μ i)⁻¹) * (Matrix.vandermonde μ).det := by
  rw [det_succ_row _ (Fin.last n), Fintype.sum_eq_single (Fin.last n)]
  · have hsub : (jacLeft μ).submatrix (Fin.last n).succAbove (Fin.last n).succAbove =
        diagonal (fun i => (arrowDenom μ i)⁻¹) * Matrix.vandermonde μ := by
      ext i k
      simp [jacLeft, Fin.succAbove_last, diagonal_mul, Matrix.vandermonde_apply, div_eq_mul_inv,
        mul_comm]
    rw [hsub, det_mul, det_diagonal]
    simp [jacLeft, ← two_mul, pow_mul]
  · intro j hj
    simp [jacLeft, hj]

/-- `∏_q ∏_{l≠q} |x_q - x_l| = Δ(x)²` for strictly increasing `x`. -/
theorem prod_prod_erase_abs_eq_sq {m : ℕ} {x : Fin m → ℝ} (hx : StrictMono x) :
    ∏ q, ∏ l ∈ Finset.univ.erase q, |x q - x l| = SpectralConvexity.vandermonde x ^ 2 := by
  have h1 : ∀ q, ∏ l ∈ Finset.univ.erase q, |x q - x l| =
      (∏ l, if q < l then |x q - x l| else 1) * ∏ l, if l < q then |x q - x l| else 1 := by
    intro q
    rw [← Finset.prod_mul_distrib, ← Finset.filter_ne' Finset.univ q, Finset.prod_filter]
    refine Finset.prod_congr rfl fun l _ => ?_
    rcases lt_trichotomy q l with h | h | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.2 h.le]
  have hA : ∏ q, ∏ l, (if q < l then |x q - x l| else 1) = SpectralConvexity.vandermonde x := by
    refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun l _ => ?_
    split_ifs with h
    · rw [abs_sub_comm, abs_of_pos (sub_pos.2 (hx h))]
    · rfl
  have hB : ∏ q, ∏ l, (if l < q then |x q - x l| else 1) = SpectralConvexity.vandermonde x := by
    rw [Finset.prod_comm, ← hA]
    refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun l _ => ?_
    rw [abs_sub_comm]
  rw [Finset.prod_congr rfl fun q _ => h1 q, Finset.prod_mul_distrib, hA, hB, sq]

/-- `|det Vand(x)| = Δ(x)` for increasing `x`. -/
theorem abs_det_vandermonde {m : ℕ} {x : Fin m → ℝ} (hx : StrictMono x) :
    |(Matrix.vandermonde x).det| = SpectralConvexity.vandermonde x := by
  rw [← vandermonde_eq_det, abs_of_pos (SpectralConvexity.vandermonde_pos hx)]

/-- `|det jacRight λ| = Δ(λ)`. -/
theorem abs_det_jacRight {lam : Fin (n + 1) → ℝ} (hlam : StrictMono lam) :
    |(jacRight lam).det| = SpectralConvexity.vandermonde lam := by
  have h := congrArg (fun A => |Matrix.det A|) (vandermonde_mul_jacRight lam)
  simp only [det_mul, det_diagonal, abs_mul, Finset.abs_prod] at h
  rw [abs_det_vandermonde hlam, prod_prod_erase_abs_eq_sq hlam, sq] at h
  exact mul_left_cancel₀ (SpectralConvexity.vandermonde_pos hlam).ne' h

/-- `|det jacLeft μ| = 1/Δ(μ)`. -/
theorem abs_det_jacLeft {μ : Fin n → ℝ} (hμ : StrictMono μ) :
    |(jacLeft μ).det| = (SpectralConvexity.vandermonde μ)⁻¹ := by
  rw [det_jacLeft, abs_mul, abs_det_vandermonde hμ, Finset.abs_prod]
  simp only [abs_inv, arrowDenom, Finset.abs_prod]
  rw [Finset.prod_inv_distrib, prod_prod_erase_abs_eq_sq hμ, sq,
    mul_inv, mul_assoc, inv_mul_cancel₀ (SpectralConvexity.vandermonde_pos hμ).ne', mul_one]

/-- **The Jacobian**: `|det D(r, a)(λ)| = Δ(λ)/Δ(μ)`. -/
theorem abs_det_borderJac {μ : Fin n → ℝ} (hμ : StrictMono μ) {lam : Fin (n + 1) → ℝ}
    (hlam : StrictMono lam) :
    |(borderJac μ lam).det| =
      SpectralConvexity.vandermonde lam / SpectralConvexity.vandermonde μ := by
  rw [borderJac_eq_mul, det_mul, abs_mul, abs_det_jacLeft hμ, abs_det_jacRight hlam,
    div_eq_mul_inv, mul_comm]

end BlockBand.DeterminantScore.WeylIntegration
