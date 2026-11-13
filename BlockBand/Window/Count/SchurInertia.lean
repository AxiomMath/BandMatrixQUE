module

public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Sylvester inertia and Haynsworth additivity for the negative count

The negative count `N_-(M)` of a Hermitian matrix is characterized by negative-definite and
nonnegative subspaces; this gives Sylvester's law of inertia and Haynsworth's additivity of
inertia over a Schur complement. This is the Schur-inertia step
`N_H(E) = N_{H_R}(E) + N_-(A_k - E - Σ_k)` of the refined count.

Everything here is deterministic linear algebra over `ℂ`, for finite index types, with
`CoareaPalm.negativeCount` (Mathlib eigenvalue indexing; `0` off the Hermitian set) and the real
form `CoareaPalm.quadForm M x = Re(x* M x)`.

* `exists_negDef_nonneg_subspaces`: for Hermitian `M`, a subspace of dimension `N_-(M)` on
  which the form is negative definite and one of dimension `dim - N_-(M)` on which it is
  nonnegative (spans of eigenvectors).
* `negativeCount_eq_of_subspaces`: conversely such a pair of subspaces of dimensions
  `r`, `dim - r` forces `N_-(M) = r` (a negative-definite and a nonnegative subspace meet
  trivially).
* `negativeCount_eq_of_quadForm_eq`: Sylvester's law of inertia, `N_-` is invariant under
  any linear isomorphism intertwining the two forms (congruence, reindexing).
* `negativeCount_fromBlocks_diag`: `N_-(diag(S, D)) = N_-(S) + N_-(D)`.
* `negativeCount_fromBlocks_schur`: Haynsworth inertia additivity, for Hermitian `A`, `D`
  and invertible `D`, `N_-([[A, Cᴴ], [C, D]]) = N_-(A - Cᴴ D⁻¹ C) + N_-(D)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem negativeCount_eq_card_filter {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount M = (Finset.univ.filter fun j => hM.eigenvalues j < 0).card := by
  classical
  simp only [negativeCount, hM, dite_true]

omit [DecidableEq ι] [DecidableEq κ] in
/-- `quadForm (Pᴴ M P) x = quadForm M (P x)`. -/
theorem quadForm_conjTranspose_mul_mul (M : Matrix κ κ ℂ) (P : Matrix κ ι ℂ) (x : ι → ℂ) :
    quadForm (Pᴴ * M * P) x = quadForm M (P *ᵥ x) := by
  unfold quadForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/-- The form of a real diagonal matrix. -/
theorem quadForm_diagonal (d : ι → ℝ) (x : ι → ℂ) :
    quadForm (diagonal (fun j => (d j : ℂ))) x = ∑ j, d j * Complex.normSq (x j) := by
  simp only [quadForm, dotProduct, mulVec_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Extension by zero from the coordinates in `s`. -/
def extendByZero (s : Finset ι) : ({j // j ∈ s} → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun y j := if h : j ∈ s then y ⟨j, h⟩ else 0
  map_add' y y' := by funext j; by_cases h : j ∈ s <;> simp [h]
  map_smul' c y := by funext j; by_cases h : j ∈ s <;> simp [h]

omit [Fintype ι] in
theorem extendByZero_injective (s : Finset ι) : Function.Injective (extendByZero s) := by
  intro y y' h
  funext j
  have := congrFun h j.1
  simpa [extendByZero, j.2] using this

omit [Fintype ι] in
theorem extendByZero_apply_of_not_mem (s : Finset ι) (y : {j // j ∈ s} → ℂ) {j : ι}
    (hj : j ∉ s) : extendByZero s y j = 0 := by
  simp [extendByZero, hj]

/-- Spectral subspaces of a diagonal form: if `d < 0` on `s` the form is negative definite on
the coordinates of `s`; if `0 ≤ d` on `s` it is nonnegative there. -/
theorem quadForm_diagonal_extend_neg (d : ι → ℝ) (s : Finset ι) (hs : ∀ j ∈ s, d j < 0)
    (y : {j // j ∈ s} → ℂ) (hy : y ≠ 0) :
    quadForm (diagonal (fun j => (d j : ℂ))) (extendByZero s y) < 0 := by
  rw [quadForm_diagonal]
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := by
    by_contra h; push Not at h; exact hy (funext h)
  have hle : ∀ i ∈ Finset.univ, d i * Complex.normSq (extendByZero s y i) ≤ 0 := by
    intro i _
    by_cases hi : i ∈ s
    · exact mul_nonpos_of_nonpos_of_nonneg (hs i hi).le (Complex.normSq_nonneg _)
    · simp [extendByZero_apply_of_not_mem s y hi]
  have hlt : d j.1 * Complex.normSq (extendByZero s y j.1) < 0 := by
    have hval : extendByZero s y j.1 = y j := by simp [extendByZero, j.2]
    rw [hval]
    exact mul_neg_of_neg_of_pos (hs j.1 j.2) (Complex.normSq_pos.mpr hj)
  calc ∑ i, d i * Complex.normSq (extendByZero s y i) < ∑ _i : ι, (0 : ℝ) :=
        Finset.sum_lt_sum hle ⟨j.1, Finset.mem_univ _, hlt⟩
    _ = 0 := by simp

theorem quadForm_diagonal_extend_nonneg (d : ι → ℝ) (s : Finset ι) (hs : ∀ j ∈ s, 0 ≤ d j)
    (y : {j // j ∈ s} → ℂ) :
    0 ≤ quadForm (diagonal (fun j => (d j : ℂ))) (extendByZero s y) := by
  rw [quadForm_diagonal]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : i ∈ s
  · exact mul_nonneg (hs i hi) (Complex.normSq_nonneg _)
  · simp [extendByZero_apply_of_not_mem s y hi]

/-- The form is negative definite on `V`. -/
def NegDefOn (M : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ V, x ≠ 0 → quadForm M x < 0

/-- The form is nonnegative on `U`. -/
def NonnegOn (M : Matrix ι ι ℂ) (U : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ U, 0 ≤ quadForm M x

/-- The unitary eigenvector matrix diagonalizes `M` by congruence. -/
theorem star_eigenvectorUnitary_mul_mul {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    (hM.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * M * (hM.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun j => (hM.eigenvalues j : ℂ)) := by
  have h := hM.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h
  rw [← star_eq_conjTranspose]
  exact h

/-- Spectral subspaces: for Hermitian `M` there are subspaces of dimensions `N_-(M)` and
`dim - N_-(M)` on which the form is negative definite, resp. nonnegative. -/
theorem exists_negDef_nonneg_subspaces {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    ∃ V U : Submodule ℂ (ι → ℂ), NegDefOn M V ∧ NonnegOn M U ∧
      Module.finrank ℂ V = negativeCount M ∧
      Module.finrank ℂ U + negativeCount M = Fintype.card ι := by
  classical
  set Uu : Matrix ι ι ℂ := (hM.eigenvectorUnitary : Matrix ι ι ℂ)
  have hUU : Uuᴴ * Uu = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hUinj : Function.Injective (Matrix.mulVecLin Uu) := by
    intro x y h
    have h' : Uuᴴ *ᵥ (Uu *ᵥ x) = Uuᴴ *ᵥ (Uu *ᵥ y) := by
      simp only [mulVecLin_apply] at h; rw [h]
    simpa [mulVec_mulVec, hUU] using h'
  have hdiag := star_eigenvectorUnitary_mul_mul hM
  have hq : ∀ z, quadForm M (Uu *ᵥ z) =
      quadForm (diagonal (fun j => (hM.eigenvalues j : ℂ))) z := by
    intro z; rw [← hdiag, quadForm_conjTranspose_mul_mul]
  set s := Finset.univ.filter fun j => hM.eigenvalues j < 0
  set t := Finset.univ.filter fun j => ¬ hM.eigenvalues j < 0
  let FV := (Matrix.mulVecLin Uu).comp (extendByZero s)
  let FU := (Matrix.mulVecLin Uu).comp (extendByZero t)
  have hFV : Function.Injective FV := hUinj.comp (extendByZero_injective s)
  have hFU : Function.Injective FU := hUinj.comp (extendByZero_injective t)
  refine ⟨LinearMap.range FV, LinearMap.range FU, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, rfl⟩ hx
    have hy : y ≠ 0 := by rintro rfl; exact hx (map_zero _)
    change quadForm M (Uu *ᵥ extendByZero s y) < 0
    rw [hq]
    exact quadForm_diagonal_extend_neg _ s (fun j hj => (Finset.mem_filter.mp hj).2) y hy
  · rintro x ⟨y, rfl⟩
    change 0 ≤ quadForm M (Uu *ᵥ extendByZero t y)
    rw [hq]
    exact quadForm_diagonal_extend_nonneg _ t
      (fun j hj => not_lt.mp (Finset.mem_filter.mp hj).2) y
  · rw [LinearMap.finrank_range_of_inj hFV, negativeCount_eq_card_filter hM]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, s]
  · rw [LinearMap.finrank_range_of_inj hFU, negativeCount_eq_card_filter hM]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, t]
    rw [add_comm]
    exact Finset.card_filter_add_card_filter_not _

omit [DecidableEq ι] in
/-- A negative-definite and a nonnegative subspace meet trivially. -/
theorem finrank_add_le_of_negDef_nonneg {M : Matrix ι ι ℂ} {V U : Submodule ℂ (ι → ℂ)}
    (hV : NegDefOn M V) (hU : NonnegOn M U) :
    Module.finrank ℂ V + Module.finrank ℂ U ≤ Fintype.card ι := by
  have hinf : V ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra h0
    exact absurd (hU x hx.2) (not_le.mpr (hV x hx.1 h0))
  have h := Submodule.finrank_sup_add_finrank_inf_eq V U
  rw [hinf, finrank_bot, add_zero] at h
  rw [← h, ← Module.finrank_fintype_fun_eq_card (R := ℂ)]
  exact Submodule.finrank_le _

/-- Characterization of `N_-`: subspaces of dimensions `r` and `dim - r` on which the form
is negative definite, resp. nonnegative, force `N_-(M) = r`. -/
theorem negativeCount_eq_of_subspaces {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {r : ℕ}
    {V U : Submodule ℂ (ι → ℂ)} (hV : NegDefOn M V) (hU : NonnegOn M U)
    (hVr : Module.finrank ℂ V = r) (hUr : Module.finrank ℂ U + r = Fintype.card ι) :
    negativeCount M = r := by
  obtain ⟨V₀, U₀, hV₀, hU₀, hV₀r, hU₀r⟩ := exists_negDef_nonneg_subspaces hM
  have h1 := finrank_add_le_of_negDef_nonneg hV hU₀
  have h2 := finrank_add_le_of_negDef_nonneg hV₀ hU
  omega

/-- Sylvester's law of inertia: a linear isomorphism `T` with
`quadForm M' x = quadForm M (T x)` preserves the negative count. -/
theorem negativeCount_eq_of_quadForm_eq {M : Matrix κ κ ℂ} {M' : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hM' : M'.IsHermitian) (T : (ι → ℂ) ≃ₗ[ℂ] (κ → ℂ))
    (hT : ∀ x, quadForm M' x = quadForm M (T x)) :
    negativeCount M' = negativeCount M := by
  obtain ⟨V, U, hV, hU, hVr, hUr⟩ := exists_negDef_nonneg_subspaces hM
  have hcard : Fintype.card ι = Fintype.card κ := by
    have := T.finrank_eq
    simpa only [Module.finrank_fintype_fun_eq_card] using this
  refine negativeCount_eq_of_subspaces hM' (V := V.map T.symm.toLinearMap)
    (U := U.map T.symm.toLinearMap) ?_ ?_ ?_ ?_
  · intro x hx h0
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm] at hx
    rw [hT]
    exact hV _ hx (by simpa using h0)
  · intro x hx
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm] at hx
    rw [hT]
    exact hU _ hx
  · rw [LinearEquiv.finrank_map_eq, hVr]
  · rw [LinearEquiv.finrank_map_eq, hUr, hcard]

/-- Congruence by an invertible matrix preserves `N_-`. -/
theorem negativeCount_conj {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (P : Matrix ι ι ℂ)
    [Invertible P] : negativeCount (Pᴴ * M * P) = negativeCount M := by
  refine negativeCount_eq_of_quadForm_eq hM ?_ (Matrix.toLinearEquiv' P inferInstance) ?_
  · exact isHermitian_conjTranspose_mul_mul P hM
  · intro x
    rw [quadForm_conjTranspose_mul_mul]; rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- Reindexing preserves the form. -/
theorem quadForm_submatrix_equiv (M : Matrix κ κ ℂ) (e : ι ≃ κ) (x : ι → ℂ) :
    quadForm (M.submatrix e e) x = quadForm M (x ∘ e.symm) := by
  unfold quadForm
  rw [submatrix_mulVec_equiv]
  congr 1
  rw [dotProduct, dotProduct, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Reindexing preserves `N_-`. -/
theorem negativeCount_submatrix_equiv {M : Matrix κ κ ℂ} (hM : M.IsHermitian) (e : ι ≃ κ) :
    negativeCount (M.submatrix e e) = negativeCount M :=
  negativeCount_eq_of_quadForm_eq hM (hM.submatrix e)
    (LinearEquiv.funCongrLeft ℂ ℂ e.symm) fun x => by
      rw [quadForm_submatrix_equiv]; rfl

theorem negativeCount_reindex {M : Matrix κ κ ℂ} (hM : M.IsHermitian) (e : κ ≃ ι) :
    negativeCount (Matrix.reindex e e M) = negativeCount M :=
  negativeCount_submatrix_equiv hM e.symm

omit [DecidableEq ι] [DecidableEq κ] in
/-- The form of a block-diagonal matrix splits. -/
theorem quadForm_fromBlocks_diag (S : Matrix ι ι ℂ) (D : Matrix κ κ ℂ) (a : ι → ℂ)
    (b : κ → ℂ) :
    quadForm (fromBlocks S 0 0 D) (Sum.elim a b) = quadForm S a + quadForm D b := by
  unfold quadForm
  rw [fromBlocks_mulVec]
  have hs : star (Sum.elim a b) = Sum.elim (star a) (star b) := by
    funext i; cases i <;> rfl
  rw [hs]
  simp [dotProduct, Fintype.sum_sum_type, Complex.add_re]

/-- `N_-(diag(S, D)) = N_-(S) + N_-(D)`. -/
theorem negativeCount_fromBlocks_diag {S : Matrix ι ι ℂ} {D : Matrix κ κ ℂ}
    (hS : S.IsHermitian) (hD : D.IsHermitian) :
    negativeCount (fromBlocks S 0 0 D) = negativeCount S + negativeCount D := by
  obtain ⟨VS, US, hVS, hUS, hVSr, hUSr⟩ := exists_negDef_nonneg_subspaces hS
  obtain ⟨VD, UD, hVD, hUD, hVDr, hUDr⟩ := exists_negDef_nonneg_subspaces hD
  have hH : (fromBlocks S 0 0 D).IsHermitian := hS.fromBlocks (by simp) hD
  let J : ((ι → ℂ) × (κ → ℂ)) →ₗ[ℂ] (ι ⊕ κ → ℂ) :=
    (LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ).symm.toLinearMap
  have hJ : ∀ a b, J (a, b) = Sum.elim a b := fun a b => by
    funext i; cases i <;> rfl
  let FV := J.comp (VS.subtype.prodMap VD.subtype)
  let FU := J.comp (US.subtype.prodMap UD.subtype)
  have hFV : Function.Injective FV :=
    (LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ).symm.injective.comp
      (Prod.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
  have hFU : Function.Injective FU :=
    (LinearEquiv.sumArrowLequivProdArrow ι κ ℂ ℂ).symm.injective.comp
      (Prod.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩)
  refine negativeCount_eq_of_subspaces hH (V := LinearMap.range FV) (U := LinearMap.range FU)
    ?_ ?_ ?_ ?_
  · rintro x ⟨⟨a, b⟩, rfl⟩ hx
    change quadForm _ (J (a.1, b.1)) < 0
    rw [hJ, quadForm_fromBlocks_diag]
    have ha : quadForm S a.1 ≤ 0 := by
      by_cases h : a.1 = 0
      · simp [h, quadForm]
      · exact (hVS _ a.2 h).le
    have hb : quadForm D b.1 ≤ 0 := by
      by_cases h : b.1 = 0
      · simp [h, quadForm]
      · exact (hVD _ b.2 h).le
    by_cases h : a.1 = 0
    · have hb0 : b.1 ≠ 0 := by
        intro hb0; apply hx
        change J (a.1, b.1) = 0
        rw [h, hb0]; exact map_zero J
      have := hVD _ b.2 hb0
      linarith
    · have := hVS _ a.2 h
      linarith
  · rintro x ⟨⟨a, b⟩, rfl⟩
    change 0 ≤ quadForm _ (J (a.1, b.1))
    rw [hJ, quadForm_fromBlocks_diag]
    exact add_nonneg (hUS _ a.2) (hUD _ b.2)
  · rw [LinearMap.finrank_range_of_inj hFV, Module.finrank_prod, hVSr, hVDr]
  · rw [LinearMap.finrank_range_of_inj hFU, Module.finrank_prod, Fintype.card_sum]
    omega

/-- The Schur congruence: `[[A, Cᴴ], [C, D]] = Pᴴ diag(A - Cᴴ D⁻¹ C, D) P` with
`P = [[1, 0], [D⁻¹ C, 1]]`, for Hermitian invertible `D`. -/
theorem fromBlocks_eq_schur_congr (A : Matrix ι ι ℂ) (C : Matrix κ ι ℂ) {D : Matrix κ κ ℂ}
    (hD : D.IsHermitian) (hdet : IsUnit D.det) :
    fromBlocks A Cᴴ C D =
      (fromBlocks 1 0 (D⁻¹ * C) 1)ᴴ * fromBlocks (A - Cᴴ * D⁻¹ * C) 0 0 D *
        fromBlocks 1 0 (D⁻¹ * C) 1 := by
  have hDi : D⁻¹ᴴ = D⁻¹ := hD.inv
  have h1 : D⁻¹ * D = 1 := nonsing_inv_mul D hdet
  have h2 : D * D⁻¹ = 1 := mul_nonsing_inv D hdet
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_mul, hDi, Matrix.one_mul,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc, h1,
    Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  congr 1
  abel

/-- Haynsworth inertia additivity: for Hermitian `A`, `D` with `D` invertible,
`N_-([[A, Cᴴ], [C, D]]) = N_-(A - Cᴴ D⁻¹ C) + N_-(D)`. -/
theorem negativeCount_fromBlocks_schur {A : Matrix ι ι ℂ} (C : Matrix κ ι ℂ)
    {D : Matrix κ κ ℂ} (hA : A.IsHermitian) (hD : D.IsHermitian) (hdet : IsUnit D.det) :
    negativeCount (fromBlocks A Cᴴ C D) =
      negativeCount (A - Cᴴ * D⁻¹ * C) + negativeCount D := by
  have hS : (A - Cᴴ * D⁻¹ * C).IsHermitian := hA.sub (isHermitian_conjTranspose_mul_mul C hD.inv)
  let P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 0 (D⁻¹ * C) 1
  have hPinv : fromBlocks 1 0 (-(D⁻¹ * C)) 1 * P = 1 := by
    simp only [P, fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add, neg_add_cancel, fromBlocks_one]
  have : Invertible P := invertibleOfLeftInverse _ _ hPinv
  rw [fromBlocks_eq_schur_congr A C hD hdet]
  rw [negativeCount_conj (hS.fromBlocks (by simp) hD) P, negativeCount_fromBlocks_diag hS hD]

end BlockBand.Window.Count
