module

public import BlockBand.DeterminantScore.WeylIntegrationBorder

/-!
# Diagonal border law: the arrowhead characteristic polynomial

* `charpoly_borderHerm_diagonal`: `det(X - [[diag μ, v],[v*, a]])` is the image in `ℂ[X]` of the
  real arrowhead polynomial
  `arrowPoly μ (|v|²) a = (X - a)∏_k (X - μ_k) - Σ_i |v_i|² ∏_{k≠i}(X - μ_k)`
  (Schur complement off the poles `z = μ_i`, then polynomial identity on an infinite set). In
  particular the spectrum depends on `v` only through `|v_i|²` (no phase rotation is needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open Matrix Polynomial BlockBand.Internal.Contracts.CoareaPalm

variable {n : ℕ}

/-- Determinant of `z - [[diag μ, v],[v*, a]]` off the poles `z = μ_i` (Schur complement). -/
theorem det_scalar_sub_borderHerm_diagonal (μ : Fin n → ℂ) (v : Fin n → ℂ) (a : ℝ) (z : ℂ)
    (hz : ∀ i, z - μ i ≠ 0) :
    (scalar (Fin (n + 1)) z - borderHerm (diagonal μ) v a).det =
      (∏ k, (z - μ k)) * ((z - a) - ∑ i, star (v i) * v i / (z - μ i)) := by
  set A := scalar (Fin (n + 1)) z - borderHerm (diagonal μ) v a
  have hA : A.submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (diagonal fun i => z - μ i) (Matrix.of fun i (_ : Fin 1) => -v i)
        (Matrix.of fun (_ : Fin 1) j => -star (v j)) (Matrix.of fun _ _ => z - a) := by
    have h1 : ∀ i : Fin n, (finSumFinEquiv (Sum.inl i) : Fin (n + 1)) = i.castSucc :=
      fun i => rfl
    have h2 : ∀ j : Fin 1, (finSumFinEquiv (Sum.inr j) : Fin (n + 1)) = Fin.last n := fun j => by
      fin_cases j; rfl
    ext (i | i) (j | j)
    · by_cases hij : i = j
      · subst hij; simp [A, borderHerm, h1]
      · simp [A, borderHerm, hij, h1, Fin.castSucc_inj]
    · simp [A, borderHerm, h1, h2, Fin.castSucc_ne_last]
    · simp [A, borderHerm, h1, h2, (Fin.castSucc_ne_last _).symm]
    · simp [A, borderHerm, h2]
  let _ : Invertible (diagonal fun i => z - μ i) :=
    ⟨diagonal fun i => (z - μ i)⁻¹, by simp [diagonal_mul_diagonal, hz],
      by simp [diagonal_mul_diagonal, hz]⟩
  rw [← det_submatrix_equiv_self finSumFinEquiv A, hA, det_fromBlocks₁₁, det_diagonal,
    det_unique]
  have hinv : ⅟(diagonal fun i => z - μ i) = diagonal fun i => (z - μ i)⁻¹ := rfl
  rw [hinv]
  congr 1
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, diagonal_apply]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The arrowhead polynomial `(X - a) ∏_k (X - μ_k) - Σ_i r_i ∏_{k ≠ i} (X - μ_k)`. -/
def arrowPoly (μ r : Fin n → ℝ) (a : ℝ) : ℝ[X] :=
  (X - C a) * ∏ k, (X - C (μ k)) - ∑ i, C (r i) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k))

/-- `w̄ w = |w|²`. -/
theorem star_mul_self_eq_normSq (w : ℂ) : star w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow]; exact Complex.conj_mul' w

/-- **Arrowhead characteristic polynomial**: `det(X - [[diag μ, v],[v*, a]]) =
(X - a)∏_k (X - μ_k) - Σ_i |v_i|² ∏_{k ≠ i}(X - μ_k)`. -/
theorem charpoly_borderHerm_diagonal (μ : Fin n → ℝ) (v : Fin n → ℂ) (a : ℝ) :
    (borderHerm (diagonal fun i => (μ i : ℂ)) v a).charpoly =
      (arrowPoly μ (fun i => ‖v i‖ ^ 2) a).map (algebraMap ℝ ℂ) := by
  refine eq_of_infinite_eval_eq _ _ (Set.Infinite.mono (s := (Set.range fun i => (μ i : ℂ))ᶜ)
    (fun z hz => ?_) (Set.finite_range _).infinite_compl)
  have hz' : ∀ i, z - (μ i : ℂ) ≠ 0 := fun i h => hz ⟨i, (sub_eq_zero.1 h).symm⟩
  simp only [Set.mem_ofPred_eq]
  rw [eval_charpoly, det_scalar_sub_borderHerm_diagonal _ _ _ _ hz']
  simp only [arrowPoly, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_sum, Polynomial.map_X, Polynomial.map_C, eval_sub, eval_mul, eval_prod,
    eval_finsetSum, eval_X, eval_C, Complex.coe_algebraMap, star_mul_self_eq_normSq]
  rw [mul_sub, mul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun k => z - (μ k : ℂ)) (Finset.mem_univ i)]
  field_simp [hz' i]

/-!
## Real polynomial algebra of the arrowhead polynomial
-/

/-- `∏_j (X - λ_j)`. -/
def rootPoly {m : ℕ} (lam : Fin m → ℝ) : ℝ[X] := ∏ j, (X - C (lam j))

/-- `c_i = ∏_{k ≠ i} (μ_i - μ_k)`. -/
def arrowDenom (μ : Fin n → ℝ) (i : Fin n) : ℝ := ∏ k ∈ Finset.univ.erase i, (μ i - μ k)

/-- `r_i(λ) = -∏_j (μ_i - λ_j) / c_i`. -/
def arrowWeight (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  -(∏ j, (μ i - lam j)) / arrowDenom μ i

/-- `a(λ) = Σ_j λ_j - Σ_i μ_i`. -/
def arrowCorner (μ : Fin n → ℝ) (lam : Fin (n + 1) → ℝ) : ℝ := ∑ j, lam j - ∑ i, μ i

/-- `∏_j (X - λ_j)` is monic. -/
theorem rootPoly_monic {m : ℕ} (lam : Fin m → ℝ) : (rootPoly lam).Monic :=
  Lagrange.nodal_monic

/-- `deg ∏_j (X - λ_j) = m`. -/
theorem natDegree_rootPoly {m : ℕ} (lam : Fin m → ℝ) : (rootPoly lam).natDegree = m := by
  rw [rootPoly, ← Lagrange.nodal, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin]

/-- Leading coefficient. -/
theorem coeff_rootPoly_self {m : ℕ} (lam : Fin m → ℝ) : (rootPoly lam).coeff m = 1 := by
  have h := (rootPoly_monic lam).coeff_natDegree
  rwa [natDegree_rootPoly] at h

/-- Coefficients above the degree vanish. -/
theorem coeff_rootPoly_of_lt {m k : ℕ} (lam : Fin m → ℝ) (hk : m < k) :
    (rootPoly lam).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_rootPoly])

/-- Subleading coefficient `-Σ λ_j`. -/
theorem coeff_rootPoly_pred (lam : Fin (n + 1) → ℝ) : (rootPoly lam).coeff n = -∑ j, lam j := by
  have h := prod_X_sub_C_nextCoeff (s := Finset.univ) lam
  rw [nextCoeff_of_natDegree_pos (by rw [← rootPoly, natDegree_rootPoly]; omega)] at h
  rw [← rootPoly, natDegree_rootPoly] at h
  simpa using h

/-- `(X - a)∏_k (X - μ_k)` as a root polynomial. -/
theorem rootPoly_snoc (μ : Fin n → ℝ) (a : ℝ) :
    rootPoly (Fin.snoc μ a : Fin (n + 1) → ℝ) = (X - C a) * ∏ k, (X - C (μ k)) := by
  rw [rootPoly, Fin.prod_univ_castSucc]
  simp [mul_comm]

/-- Each tail term has degree `< n`. -/
theorem natDegree_arrowTail_lt (μ r : Fin n → ℝ) (i : Fin n) :
    (C (r i) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k))).natDegree < n := by
  refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
  rw [← Lagrange.nodal, Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]
  have := i.isLt; omega

/-- The tail has no coefficient in degree `≥ n`. -/
theorem coeff_arrowTail (μ r : Fin n → ℝ) {m : ℕ} (hk : n ≤ m) :
    (∑ i, C (r i) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k))).coeff m = 0 := by
  rw [finsetSum_coeff]
  exact Finset.sum_eq_zero fun i _ =>
    coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (natDegree_arrowTail_lt μ r i) hk)

/-- `arrowPoly = ∏(X - (μ, a)) - tail`. -/
theorem arrowPoly_eq (μ r : Fin n → ℝ) (a : ℝ) :
    arrowPoly μ r a = rootPoly (Fin.snoc μ a : Fin (n + 1) → ℝ) -
      ∑ i, C (r i) * ∏ k ∈ Finset.univ.erase i, (X - C (μ k)) := by
  rw [rootPoly_snoc, arrowPoly]

/-- Subleading coefficient of the arrowhead polynomial. -/
theorem coeff_arrowPoly_pred (μ r : Fin n → ℝ) (a : ℝ) :
    (arrowPoly μ r a).coeff n = -(∑ i, μ i + a) := by
  rw [arrowPoly_eq, coeff_sub, coeff_rootPoly_pred, coeff_arrowTail μ r le_rfl, sub_zero,
    Fin.sum_univ_castSucc]
  simp

/-- Value at a node: `arrowPoly(μ_i) = -r_i c_i`. -/
theorem eval_arrowPoly (μ r : Fin n → ℝ) (a : ℝ) (i : Fin n) :
    (arrowPoly μ r a).eval (μ i) = -(r i * arrowDenom μ i) := by
  simp only [arrowPoly, eval_sub, eval_mul, eval_prod, eval_finsetSum, eval_X, eval_C]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _), mul_zero, zero_sub,
    Finset.sum_eq_single i]
  · rfl
  · intro k _ hk
    rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hk h.symm, Finset.mem_univ i⟩)
      (sub_self _), mul_zero]
  · simp

/-- Evaluation of a root polynomial. -/
theorem eval_rootPoly {m : ℕ} (lam : Fin m → ℝ) (x : ℝ) :
    (rootPoly lam).eval x = ∏ j, (x - lam j) := by
  simp [rootPoly, eval_prod]

/-- `c_i ≠ 0` for distinct nodes. -/
theorem arrowDenom_ne_zero {μ : Fin n → ℝ} (hμ : Function.Injective μ) (i : Fin n) :
    arrowDenom μ i ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hk =>
    sub_ne_zero.2 fun h => (Finset.mem_erase.1 hk).1 (hμ h).symm

/-- A real polynomial without coefficients in degrees `≥ n` vanishing at `n` distinct points is
zero. -/
theorem eq_zero_of_coeff_of_eval {p : ℝ[X]} {μ : Fin n → ℝ} (hμ : Function.Injective μ)
    (hc : ∀ k, n ≤ k → p.coeff k = 0) (he : ∀ i, p.eval (μ i) = 0) : p = 0 := by
  by_contra hp
  have hdeg : p.natDegree < n := by
    by_contra h
    exact hp (leadingCoeff_eq_zero.1 (hc _ (not_lt.1 h)))
  exact hp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hμ he (by simpa using hdeg))

/-- If the arrowhead polynomial has roots `λ`, then `(r, a) = (r(λ), a(λ))`. -/
theorem arrowCoord_of_arrowPoly_eq {μ r : Fin n → ℝ} {a : ℝ} (hμ : Function.Injective μ)
    {lam : Fin (n + 1) → ℝ} (h : arrowPoly μ r a = rootPoly lam) :
    arrowWeight μ lam = r ∧ arrowCorner μ lam = a := by
  refine ⟨funext fun i => ?_, ?_⟩
  · have he := congrArg (fun p => p.eval (μ i)) h
    simp only [eval_arrowPoly, eval_rootPoly] at he
    rw [arrowWeight, ← he, neg_neg, mul_div_cancel_right₀ _ (arrowDenom_ne_zero hμ i)]
  · have hc := congrArg (fun p => p.coeff n) h
    simp only [coeff_arrowPoly_pred, coeff_rootPoly_pred] at hc
    rw [arrowCorner]; linarith

/-- Conversely, `λ` are the roots of the arrowhead polynomial with `(r, a) = (r(λ), a(λ))`. -/
theorem arrowPoly_arrowCoord {μ : Fin n → ℝ} (hμ : Function.Injective μ)
    (lam : Fin (n + 1) → ℝ) :
    arrowPoly μ (arrowWeight μ lam) (arrowCorner μ lam) = rootPoly lam := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_of_eval hμ (fun k hk => ?_) (fun i => ?_)
  · rw [coeff_sub]
    rcases hk.lt_or_eq with hk | rfl
    · rw [arrowPoly_eq, coeff_sub, coeff_arrowTail _ _ hk.le, sub_zero]
      rcases (Nat.succ_le_of_lt hk).lt_or_eq with hk' | hk'
      · rw [coeff_rootPoly_of_lt _ hk', coeff_rootPoly_of_lt _ hk', sub_zero]
      · rw [← hk', coeff_rootPoly_self, coeff_rootPoly_self, sub_self]
    · rw [coeff_arrowPoly_pred, coeff_rootPoly_pred, arrowCorner]; ring
  · rw [eval_sub, eval_arrowPoly, eval_rootPoly, arrowWeight,
      div_mul_cancel₀ _ (arrowDenom_ne_zero hμ i), neg_neg, sub_self]

end BlockBand.DeterminantScore.WeylIntegration
