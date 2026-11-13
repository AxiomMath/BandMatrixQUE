module

public import BlockBand.DeterminantScore.GaussianPolynomialGradient
public import BlockBand.DeterminantScore.PointwiseJacobi
public import BlockBand.Angular.DetFactorGUE
public import BlockBand.Angular.DetFactor

/-!
# The determinant as a degree-two polynomial of the whole row

The determinant `P = det M` is a real polynomial of degree at most two in the entire remaining
Gaussian row; in whitened real coordinates `‖∇ log|P|‖² = t|R_ww|² + 2t Σ_{j≠w}|R_jw|² ≥ t‖Rw‖²`.

Setting: Hermitian `K` on `Fin m` (`m ≠ 0`), the coordinates `HermCoord m` of `G_m(t)`
(`Sector.hermOfCoord`), the *row* coordinates `IsRow c` (those touching the index `0`), whitened
row variables `u` and fixed whitened remaining variables `w`, the point
`rowPoint σ u w = σ ⊙ (u, w)` and `M(u) = K + G(rowPoint σ u w)`.

* `rowPoly K σ w`: a real `MvPolynomial` in the row variables with
  `eval u (rowPoly K σ w) = Re det M(u)` (`eval_rowPoly`) and total degree `≤ 2`
  (`totalDegree_rowPoly_le`): every permutation term of the determinant meets row `0` and
  column `0` once each;
* `pderiv_rowPoly_eq`: at `det M(u) ≠ 0`, `∂_c P = σ_c (Re det M) w_c ρ_c` with
  `ρ = coord(M⁻¹)` and `w_c` the Frobenius weights (Jacobi's formula
  `hasDerivAt_det_realAffineLine`);
* `gradient_lower_bound`: with `σ_c² = Var(c)` (`t` diagonal, `t/2` off-diagonal),
  `t (Re det M)² ‖M⁻¹ e₀‖² ≤ ‖∇P(u)‖²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open Matrix MvPolynomial
open BlockBand.Internal.Contracts
open BlockBand.DeterminantScore.Sector BlockBand.DeterminantScore.GaussianGradient
open BlockBand.Angular.DetFactor
open scoped NNReal

/-!
## Real part of a complex polynomial
-/

section RePoly

variable {ι : Type*}

/-- The coefficientwise real part of a complex polynomial. -/
def rePoly (P : MvPolynomial ι ℂ) : MvPolynomial ι ℝ :=
  ∑ s ∈ P.support, monomial s (P.coeff s).re

theorem eval_rePoly (P : MvPolynomial ι ℂ) (x : ι → ℝ) :
    eval x (rePoly P) = (eval (fun i => (x i : ℂ)) P).re := by
  unfold rePoly
  rw [map_sum, eval_eq, Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [eval_monomial]
  have h : (∏ i ∈ s.support, (x i : ℂ) ^ s i) = ((∏ i ∈ s.support, x i ^ s i : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h, Complex.re_mul_ofReal]
  rfl

theorem totalDegree_rePoly_le (P : MvPolynomial ι ℂ) :
    (rePoly P).totalDegree ≤ P.totalDegree := by
  unfold rePoly
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hs)

end RePoly

/-!
## Row coordinates
-/

variable {m : ℕ} [NeZero m]

/-- Coordinates touching the index `0`: the diagonal entry and the real and imaginary parts of
the entries `(0, b)`. -/
def IsRow (c : HermCoord m) : Prop := c.1 = 0 ∨ c.2 = 0

instance : DecidablePred (IsRow (m := m)) := fun c => by unfold IsRow; infer_instance

variable (m) in
/-- Row variables. -/
abbrev RowIdx := {c : HermCoord m // IsRow c}

variable (m) in
/-- Remaining variables. -/
abbrev RestIdx := {c : HermCoord m // ¬ IsRow c}

/-- The coordinate point `σ ⊙ (u, w)`. -/
def rowPoint (σ : HermCoord m → ℝ) (u : RowIdx m → ℝ) (w : RestIdx m → ℝ) :
    HermCoord m → ℝ :=
  fun c => σ c * (if h : IsRow c then u ⟨c, h⟩ else w ⟨c, h⟩)

/-- Coordinate polynomials in the row variables. -/
def rowCoordPoly (σ : HermCoord m → ℝ) (w : RestIdx m → ℝ) (c : HermCoord m) :
    MvPolynomial (RowIdx m) ℂ :=
  if h : IsRow c then C (σ c : ℂ) * X ⟨c, h⟩ else C ((σ c * w ⟨c, h⟩ : ℝ) : ℂ)

/-- The polynomial matrix `K + G(σ ⊙ (X, w))`. -/
def rowPolyMatrix (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ) (w : RestIdx m → ℝ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (RowIdx m) ℂ) :=
  Matrix.of fun a b => C (K a b) +
    (if a = b then rowCoordPoly σ w (a, a)
    else if a < b then rowCoordPoly σ w (a, b) + C Complex.I * rowCoordPoly σ w (b, a)
    else rowCoordPoly σ w (b, a) - C Complex.I * rowCoordPoly σ w (a, b))

/-- The real row polynomial `Re det(K + G(σ ⊙ (u, w)))`. -/
def rowPoly (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ) (w : RestIdx m → ℝ) :
    MvPolynomial (RowIdx m) ℝ :=
  rePoly (rowPolyMatrix K σ w).det

theorem eval_rowCoordPoly (σ : HermCoord m → ℝ) (u : RowIdx m → ℝ) (w : RestIdx m → ℝ)
    (c : HermCoord m) :
    eval (fun j => (u j : ℂ)) (rowCoordPoly σ w c) = (rowPoint σ u w c : ℂ) := by
  unfold rowCoordPoly rowPoint
  split_ifs with h <;> simp

theorem mapMatrix_eval_rowPolyMatrix (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ)
    (u : RowIdx m → ℝ) (w : RestIdx m → ℝ) :
    (eval fun j => (u j : ℂ)).mapMatrix (rowPolyMatrix K σ w) =
      K + hermOfCoord (rowPoint σ u w) := by
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, rowPolyMatrix, Matrix.of_apply,
    Matrix.add_apply, hermOfCoord_apply]
  split_ifs <;> simp [eval_rowCoordPoly] <;> ring

theorem eval_rowPoly (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ) (u : RowIdx m → ℝ)
    (w : RestIdx m → ℝ) :
    eval u (rowPoly K σ w) = (K + hermOfCoord (rowPoint σ u w)).det.re := by
  unfold rowPoly
  rw [eval_rePoly, ← mapMatrix_eval_rowPolyMatrix, ← RingHom.map_det]

/-!
## Degree
-/

theorem totalDegree_rowCoordPoly_le (σ : HermCoord m → ℝ) (w : RestIdx m → ℝ)
    (c : HermCoord m) :
    (rowCoordPoly σ w c).totalDegree ≤ if IsRow c then 1 else 0 := by
  unfold rowCoordPoly
  split_ifs with h
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  · rw [totalDegree_C]

theorem totalDegree_rowPolyMatrix_le (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ)
    (w : RestIdx m → ℝ) (a b : Fin m) :
    (rowPolyMatrix K σ w a b).totalDegree ≤ if a = 0 ∨ b = 0 then 1 else 0 := by
  set d : ℕ := if a = 0 ∨ b = 0 then 1 else 0
  have hab : (rowCoordPoly σ w (a, b)).totalDegree ≤ d := by
    refine (totalDegree_rowCoordPoly_le σ w (a, b)).trans (le_of_eq ?_)
    simp only [IsRow, d]
  have hba : (rowCoordPoly σ w (b, a)).totalDegree ≤ d := by
    refine (totalDegree_rowCoordPoly_le σ w (b, a)).trans (le_of_eq ?_)
    simp only [IsRow, d, or_comm]
  have hI : ∀ P : MvPolynomial (RowIdx m) ℂ, P.totalDegree ≤ d →
      (C Complex.I * P).totalDegree ≤ d := fun P hP =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  simp only [rowPolyMatrix, Matrix.of_apply]
  refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
  split_ifs with h1 h2
  · subst h1; exact hab
  · exact (totalDegree_add _ _).trans (max_le hab (hI _ hba))
  · exact (totalDegree_sub _ _).trans (max_le hba (hI _ hab))

theorem sum_ite_perm_le (τ : Equiv.Perm (Fin m)) :
    (∑ i, if τ i = 0 ∨ i = 0 then 1 else 0 : ℕ) ≤ 2 := by
  have h1 : (∑ i, if τ i = 0 ∨ i = 0 then 1 else 0 : ℕ) ≤
      ∑ i, ((if τ i = 0 then 1 else 0) + (if i = 0 then 1 else 0) : ℕ) :=
    Finset.sum_le_sum fun i _ => by split_ifs <;> simp_all
  have h2 : (∑ i, (if τ i = 0 then 1 else 0 : ℕ)) = 1 := by
    rw [Equiv.sum_comp τ (fun j => if j = 0 then 1 else 0)]
    simp
  rw [Finset.sum_add_distrib, h2] at h1
  simpa using h1

/-- **Degree two in the whole row.** -/
theorem totalDegree_rowPoly_le (K : Matrix (Fin m) (Fin m) ℂ) (σ : HermCoord m → ℝ)
    (w : RestIdx m → ℝ) : (rowPoly K σ w).totalDegree ≤ 2 := by
  refine (totalDegree_rePoly_le _).trans ?_
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun τ _ => ?_)
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => totalDegree_rowPolyMatrix_le K σ w (τ i) i) ?_
  exact sum_ite_perm_le τ

/-!
## The gradient
-/

/-- Moving one row variable moves the matrix along the coordinate direction. -/
theorem rowPoint_update (σ : HermCoord m → ℝ) (u : RowIdx m → ℝ) (w : RestIdx m → ℝ)
    (c : RowIdx m) (s : ℝ) :
    rowPoint σ (Function.update u c s) w =
      rowPoint σ u w + ((s - u c) * σ c.1) • Pi.single c.1 1 := by
  funext j
  simp only [rowPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = c.1
  · subst hj
    simp only [c.2, ↓reduceDIte, Pi.single_eq_same, mul_one]
    rw [Function.update_self]
    ring
  · rw [Pi.single_eq_of_ne hj, mul_zero, add_zero]
    split_ifs with h
    · rw [Function.update_of_ne (fun e => hj (by rw [← e]))]
    · rfl

theorem hasDerivAt_eval_update {ι : Type*} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ)
    (u : ι → ℝ) (c : ι) :
    HasDerivAt (fun s => eval (Function.update u c s) P) (eval u (pderiv c P)) (u c) := by
  have h := hasDerivAt_polynomial_curve P (fun i s => Function.update u c s i)
    (Pi.single c 1) (u c) (fun i => by
      by_cases hi : i = c
      · subst hi; simpa using hasDerivAt_id' (u i)
      · simp only [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
        exact hasDerivAt_const _ _)
  simp only [Function.update_eq_self] at h
  convert h using 1
  unfold polynomialDirectional
  rw [Finset.sum_eq_single c (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
    (by simp)]
  simp

/-- `Re Tr(R G(e_c)) = w_c ρ_c` for Hermitian `R`, `ρ = coord(R)`. -/
theorem re_trace_mul_single {R : Matrix (Fin m) (Fin m) ℂ} (hR : R.IsHermitian)
    (c : HermCoord m) :
    (R * hermOfCoord (Pi.single c 1)).trace.re = coordWeight c * coordOfMatrix R c := by
  rw [← hermOfCoord_coordOfMatrix hR, re_trace_hermOfCoord_mul,
    hermOfCoord_coordOfMatrix hR]
  rw [Finset.sum_eq_single c (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
    (by simp)]
  simp

/-- **Partial derivatives of the row polynomial** at an invertible point. -/
theorem pderiv_rowPoly_eq {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (σ : HermCoord m → ℝ) (u : RowIdx m → ℝ) (w : RestIdx m → ℝ)
    (hdet : (K + hermOfCoord (rowPoint σ u w)).det ≠ 0) (c : RowIdx m) :
    eval u (pderiv c (rowPoly K σ w)) =
      σ c.1 * (K + hermOfCoord (rowPoint σ u w)).det.re * coordWeight c.1 *
        coordOfMatrix (K + hermOfCoord (rowPoint σ u w))⁻¹ c.1 := by
  set M := K + hermOfCoord (rowPoint σ u w) with hMdef
  have hMH : M.IsHermitian := hK.add (isHermitian_hermOfCoord _)
  set H : Matrix (Fin m) (Fin m) ℂ := (σ c.1 : ℂ) • hermOfCoord (Pi.single c.1 1)
  have hfun : (fun s => eval (Function.update u c s) (rowPoly K σ w)) =
      fun s => (Complex.reCLM ∘ (fun r : ℝ => (M + (r : ℂ) • H).det)) (s - u c) := by
    funext s
    rw [eval_rowPoly, rowPoint_update, hermOfCoord_add, hermOfCoord_smul]
    simp only [Function.comp_apply, Complex.reCLM_apply, H, smul_smul, ← add_assoc, hMdef]
    push_cast
    rfl
  have hJ := hasDerivAt_det_realAffineLine M H (isUnit_iff_ne_zero.mpr hdet)
  have hJ' : HasDerivAt (Complex.reCLM ∘ fun r : ℝ => (M + (r : ℂ) • H).det)
      (Complex.reCLM (M.det * (M⁻¹ * H).trace)) (u c - u c) := by
    rw [sub_self]
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hJ
  have h2 := hJ'.comp_sub_const (u c) (u c)
  rw [← hfun] at h2
  have h1 := hasDerivAt_eval_update (rowPoly K σ w) u c
  rw [h1.unique h2]
  have him := det_im_eq_zero hMH
  have hRH : M⁻¹.IsHermitian := hMH.inv
  have htr : (M⁻¹ * H).trace = (σ c.1 : ℂ) * (M⁻¹ * hermOfCoord (Pi.single c.1 1)).trace := by
    simp only [H, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Complex.reCLM_apply, htr, Complex.mul_re, him, zero_mul, sub_zero, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, re_trace_mul_single hRH]
  ring

/-- Coordinate weights times variances dominate `t`. -/
theorem le_hermVariance_mul_coordWeight_sq (t : ℝ≥0) (c : HermCoord m) :
    (t : ℝ) ≤ (hermVariance m t c : ℝ) * coordWeight c ^ 2 := by
  unfold hermVariance coordWeight
  split_ifs
  · simp
  · push_cast; nlinarith [t.2]

/-- `‖R e₀‖² ≤ Σ_{row c} ρ_c²` for Hermitian `R`. -/
theorem sum_norm_col_le {R : Matrix (Fin m) (Fin m) ℂ} (hR : R.IsHermitian) :
    (∑ a, ‖R a 0‖ ^ 2) ≤ ∑ c : RowIdx m, coordOfMatrix R c.1 ^ 2 := by
  have hcol : ∀ a, ‖R a 0‖ ^ 2 =
      coordOfMatrix R (0, a) ^ 2 + (if a = 0 then 0 else coordOfMatrix R (a, 0) ^ 2) := by
    intro a
    have hconj : R a 0 = star (R 0 a) := (hR.apply a 0).symm
    rw [hconj, norm_star, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    by_cases ha : a = 0
    · subst ha
      have him : (R 0 0).im = 0 := by
        have h := congrArg Complex.im (hR.apply 0 0)
        simp at h; linarith
      simp [coordOfMatrix, him]; ring
    · have hlt : (0 : Fin m) < a := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm ha)
      simp only [coordOfMatrix, ha, ↓reduceIte, Ne.symm ha, hlt, not_lt_of_gt hlt]
      ring
  rw [Finset.sum_congr rfl fun a _ => hcol a, Finset.sum_add_distrib]
  have hsub : (∑ c : RowIdx m, coordOfMatrix R c.1 ^ 2) =
      ∑ c : HermCoord m, if IsRow c then coordOfMatrix R c ^ 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    exact (Finset.sum_subtype _ (fun _ => by simp [Finset.mem_filter])
      (fun c => coordOfMatrix R c ^ 2)).symm
  rw [hsub, Fintype.sum_prod_type]
  have hsplit : ∀ a : Fin m, (∑ b : Fin m, if IsRow (a, b) then coordOfMatrix R (a, b) ^ 2 else 0) =
      (if a = 0 then ∑ b, coordOfMatrix R (0, b) ^ 2 else 0) +
        (if a = 0 then 0 else coordOfMatrix R (a, 0) ^ 2) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [IsRow]
    · simp [IsRow, ha]
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
  simp

/-- **Gradient lower bound** `‖∇P‖² ≥ t P² ‖M⁻¹e₀‖²` in whitened row coordinates
(`σ_c² = Var(c)`), at an invertible point. -/
theorem gradient_lower_bound {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (t : ℝ≥0)
    (u : RowIdx m → ℝ) (w : RestIdx m → ℝ)
    (hdet : (K + hermOfCoord (rowPoint (fun c => Real.sqrt (hermVariance m t c)) u w)).det ≠ 0) :
    (t : ℝ) * (eval u (rowPoly K (fun c => Real.sqrt (hermVariance m t c)) w)) ^ 2 *
        (∑ a, ‖(K + hermOfCoord (rowPoint (fun c => Real.sqrt (hermVariance m t c)) u w))⁻¹ a 0‖ ^ 2) ≤
      ‖polynomialGradient (rowPoly K (fun c => Real.sqrt (hermVariance m t c)) w) u‖ ^ 2 := by
  set σ : HermCoord m → ℝ := fun c => Real.sqrt (hermVariance m t c)
  set M := K + hermOfCoord (rowPoint σ u w)
  have hMH : M.IsHermitian := hK.add (isHermitian_hermOfCoord _)
  have hRH : M⁻¹.IsHermitian := hMH.inv
  set P := M.det.re
  have hev : eval u (rowPoly K σ w) = P := eval_rowPoly K σ u w
  rw [hev, polynomialGradient, PiLp.norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [pderiv_rowPoly_eq hK σ u w hdet]
  have hterm : ∀ c : RowIdx m, (t : ℝ) * P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2 ≤
      (σ c.1 * P * coordWeight c.1 * coordOfMatrix M⁻¹ c.1) ^ 2 := by
    intro c
    have hσ : σ c.1 ^ 2 = (hermVariance m t c.1 : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg _)
    have h := le_hermVariance_mul_coordWeight_sq t c.1
    have hnn : 0 ≤ P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2 := by positivity
    calc (t : ℝ) * P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2
        = (t : ℝ) * (P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2) := by ring
      _ ≤ ((hermVariance m t c.1 : ℝ) * coordWeight c.1 ^ 2) *
            (P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2) := mul_le_mul_of_nonneg_right h hnn
      _ = (σ c.1 * P * coordWeight c.1 * coordOfMatrix M⁻¹ c.1) ^ 2 := by rw [← hσ]; ring
  have hcol := sum_norm_col_le hRH
  calc (t : ℝ) * P ^ 2 * ∑ a, ‖M⁻¹ a 0‖ ^ 2
      ≤ (t : ℝ) * P ^ 2 * ∑ c : RowIdx m, coordOfMatrix M⁻¹ c.1 ^ 2 :=
        mul_le_mul_of_nonneg_left hcol (by positivity)
    _ = ∑ c : RowIdx m, (t : ℝ) * P ^ 2 * coordOfMatrix M⁻¹ c.1 ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun c _ => hterm c

end BlockBand.DeterminantScore.PhysicalColumn
