module

public import Mathlib
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Schur inertia (Haynsworth) for the negative count `N_-`

A deterministic component of the layer recursion: the integer phase of the conditional
increments is fixed by Schur inertia, and Schur inertia gives exactly
`N_H = N_{n-1} + N_-(A_0 - E - Σ)`.

The negative count is `BlockBand.Internal.Contracts.CoareaPalm.negativeCount`: for a Hermitian
matrix, the number of strictly negative eigenvalues counted with multiplicity (and `0` off the
Hermitian set). The form is `quadForm M x = Re (x* M x)`.

Contents.
* `IsNegDefOn M V`: the form is strictly negative on `V \ {0}`.
* Variational characterization (`exists_isNegDefOn_finrank_eq_negativeCount`,
  `finrank_le_negativeCount_of_isNegDefOn`): `N_-(M)` is the maximal dimension of a complex
  subspace of `ι → ℂ` on which the form is negative definite.
* Sylvester's law, negative part (`negativeCount_conjTranspose_mul_mul`).
* Block-diagonal additivity (`negativeCount_fromBlocks_diag`).
* Haynsworth inertia additivity for both Schur complements
  (`negativeCount_fromBlocks_schur11`, `negativeCount_fromBlocks_schur22`) and the shifted form
  used by the layer recursion (`negativeCount_fromBlocks_sub_smul_one`).

Everything is exact linear algebra over `ℂ` on finite index types; no dimension bound, no
probability and no norm bound enters.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix BlockBand.Internal.Contracts.CoareaPalm

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Hermitian form `x ↦ Re (x* M x)` is strictly negative on the nonzero vectors of `V`. -/
def IsNegDefOn (M : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) : Prop :=
  ∀ x ∈ V, x ≠ 0 → quadForm M x < 0

/-- `n` is the maximal dimension of a subspace on which `x ↦ Re (x* M x)` is negative definite:
some such subspace has dimension `n`, and every such subspace has dimension at most `n`. -/
def IsNegIndex (M : Matrix ι ι ℂ) (n : ℕ) : Prop :=
  (∃ V : Submodule ℂ (ι → ℂ), IsNegDefOn M V ∧ Module.finrank ℂ V = n) ∧
    ∀ V : Submodule ℂ (ι → ℂ), IsNegDefOn M V → Module.finrank ℂ V ≤ n

omit [DecidableEq ι] in
theorem IsNegIndex.unique {M : Matrix ι ι ℂ} {n m : ℕ} (hn : IsNegIndex M n)
    (hm : IsNegIndex M m) : n = m := by
  obtain ⟨⟨V, hV, rfl⟩, hn'⟩ := hn
  obtain ⟨⟨W, hW, rfl⟩, hm'⟩ := hm
  exact le_antisymm (hm' V hV) (hn' W hW)

/-!
## Congruence
-/

omit [DecidableEq ι] in
theorem quadForm_conjTranspose_mul_mul (M : Matrix ι ι ℂ) (L : Matrix ι ι ℂ) (x : ι → ℂ) :
    quadForm (Lᴴ * M * L) x = quadForm M (L *ᵥ x) := by
  unfold quadForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- A negative definite subspace for `Lᴴ M L` maps, under an injective `L`, to a negative definite
subspace for `M` of the same dimension. -/
theorem exists_isNegDefOn_of_conjTranspose_mul_mul {M L : Matrix ι ι ℂ} (hL : IsUnit L)
    {V : Submodule ℂ (ι → ℂ)} (hV : IsNegDefOn (Lᴴ * M * L) V) :
    ∃ W : Submodule ℂ (ι → ℂ), IsNegDefOn M W ∧
      Module.finrank ℂ W = Module.finrank ℂ V := by
  have hinj : Function.Injective (mulVecLin L) := mulVec_injective_iff_isUnit.mpr hL
  refine ⟨V.map (mulVecLin L), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ hy
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hy (map_zero _)
    have := hV x hx hx0
    rwa [quadForm_conjTranspose_mul_mul] at this
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)).symm

/-- The negative index is invariant under congruence by an invertible matrix. -/
theorem IsNegIndex.conjTranspose_mul_mul {M L : Matrix ι ι ℂ} (hL : IsUnit L) {n : ℕ}
    (h : IsNegIndex M n) : IsNegIndex (Lᴴ * M * L) n := by
  have hL' : IsUnit L⁻¹ := (isUnit_nonsing_inv_iff).mpr hL
  have hM : M = (L⁻¹)ᴴ * (Lᴴ * M * L) * L⁻¹ := by
    have h1 : (L⁻¹)ᴴ * Lᴴ = 1 := by
      rw [← conjTranspose_mul, mul_nonsing_inv _ ((isUnit_iff_isUnit_det L).mp hL),
        conjTranspose_one]
    have h2 : L * L⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det L).mp hL)
    calc M = ((L⁻¹)ᴴ * Lᴴ) * M * (L * L⁻¹) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
      _ = (L⁻¹)ᴴ * (Lᴴ * M * L) * L⁻¹ := by simp only [Matrix.mul_assoc]
  obtain ⟨⟨V, hV, hVn⟩, hmax⟩ := h
  refine ⟨?_, fun W hW => ?_⟩
  · rw [hM] at hV
    obtain ⟨W, hW, hWn⟩ := exists_isNegDefOn_of_conjTranspose_mul_mul hL' hV
    exact ⟨W, hW, hWn.trans hVn⟩
  · obtain ⟨V', hV', hV'n⟩ := exists_isNegDefOn_of_conjTranspose_mul_mul hL hW
    exact hV'n ▸ hmax V' hV'

/-!
## Diagonal matrices
-/

theorem quadForm_diagonal (d : ι → ℝ) (x : ι → ℂ) :
    quadForm (diagonal fun k => (d k : ℂ)) x = ∑ k, d k * Complex.normSq (x k) := by
  unfold quadForm
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  ring

/-- Extension by zero from the coordinates satisfying `p`. -/
def extendByZero (p : ι → Prop) [DecidablePred p] : ({k // p k} → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun y k := if h : p k then y ⟨k, h⟩ else 0
  map_add' y z := by
    funext k
    by_cases h : p k <;> simp [h]
  map_smul' c y := by
    funext k
    by_cases h : p k <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem extendByZero_injective (p : ι → Prop) [DecidablePred p] :
    Function.Injective (extendByZero p) := by
  intro y z hyz
  funext k
  have := congrFun hyz k.1
  simpa [extendByZero, k.2] using this

omit [DecidableEq ι] in
theorem finrank_range_extendByZero (p : ι → Prop) [DecidablePred p] :
    Module.finrank ℂ (LinearMap.range (extendByZero p)) = (Finset.univ.filter p).card := by
  rw [LinearMap.finrank_range_of_inj (extendByZero_injective p),
    Module.finrank_fintype_fun_eq_card, Fintype.card_subtype]

omit [Fintype ι] [DecidableEq ι] in
theorem eq_zero_of_mem_range_extendByZero {p : ι → Prop} [DecidablePred p] {x : ι → ℂ}
    (hx : x ∈ LinearMap.range (extendByZero p)) {k : ι} (hk : ¬ p k) : x k = 0 := by
  obtain ⟨y, rfl⟩ := hx
  simp [extendByZero, hk]

/-- The diagonal case of the variational characterization. -/
theorem isNegIndex_diagonal (d : ι → ℝ) :
    IsNegIndex (diagonal fun k => (d k : ℂ)) (Finset.univ.filter fun k => d k < 0).card := by
  classical
  refine ⟨⟨LinearMap.range (extendByZero fun k => d k < 0), ?_,
    finrank_range_extendByZero _⟩, fun V hV => ?_⟩
  · intro x hx hx0
    rw [quadForm_diagonal]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hx0
    have hdk : d k < 0 := by
      by_contra h
      exact hk (eq_zero_of_mem_range_extendByZero hx h)
    have hle : ∀ j ∈ Finset.univ, d j * Complex.normSq (x j) ≤ (fun _ => (0 : ℝ)) j := by
      intro j _
      by_cases hj : d j < 0
      · exact mul_nonpos_of_nonpos_of_nonneg hj.le (Complex.normSq_nonneg _)
      · simp [eq_zero_of_mem_range_extendByZero hx hj]
    have hlt : ∃ j ∈ Finset.univ, d j * Complex.normSq (x j) < (fun _ => (0 : ℝ)) j :=
      ⟨k, Finset.mem_univ _, mul_neg_of_neg_of_pos hdk (Complex.normSq_pos.mpr hk)⟩
    simpa using Finset.sum_lt_sum hle hlt
  · set W := LinearMap.range (extendByZero fun k => ¬ d k < 0)
    have hW : ∀ x ∈ W, 0 ≤ quadForm (diagonal fun k => (d k : ℂ)) x := by
      intro x hx
      rw [quadForm_diagonal]
      refine Finset.sum_nonneg fun j _ => ?_
      by_cases hj : d j < 0
      · simp [eq_zero_of_mem_range_extendByZero hx (not_not.mpr hj)]
      · exact mul_nonneg (not_lt.mp hj) (Complex.normSq_nonneg _)
    have hinf : V ⊓ W = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxV, hxW⟩
      by_contra hx0
      exact absurd (hW x hxW) (not_le.mpr (hV x hxV hx0))
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hinf, finrank_bot, add_zero, finrank_range_extendByZero] at hsum
    have hsup := Submodule.finrank_le (V ⊔ W)
    rw [Module.finrank_fintype_fun_eq_card] at hsup
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (fun k => d k < 0)
    rw [Finset.card_univ] at hcard
    omega

/-!
## The spectral theorem in congruence form
-/

theorem negativeCount_of_isHermitian {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    negativeCount M = (Finset.univ.filter fun k => hM.eigenvalues k < 0).card := by
  unfold negativeCount
  simp only [hM, ↓reduceDIte]

theorem exists_isUnit_eq_conjTranspose_mul_diagonal_mul {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) :
    ∃ L : Matrix ι ι ℂ, IsUnit L ∧
      M = Lᴴ * diagonal (fun k => (hM.eigenvalues k : ℂ)) * L := by
  set U : Matrix ι ι ℂ := (hM.eigenvectorUnitary : Matrix ι ι ℂ)
  refine ⟨star U, ?_, ?_⟩
  · have h : star U * U = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    exact (isUnit_iff_isUnit_det _).mpr (isUnit_det_of_right_inverse h)
  · conv_lhs => rw [hM.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose, ← star_eq_conjTranspose]
    rfl

/-- The negative count of a Hermitian matrix is its negative index. -/
theorem isNegIndex_negativeCount {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    IsNegIndex M (negativeCount M) := by
  obtain ⟨L, hL, hML⟩ := exists_isUnit_eq_conjTranspose_mul_diagonal_mul hM
  rw [negativeCount_of_isHermitian hM]
  conv => arg 1; rw [hML]
  exact (isNegIndex_diagonal _).conjTranspose_mul_mul hL

theorem negativeCount_eq_of_isNegIndex {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {n : ℕ}
    (h : IsNegIndex M n) : negativeCount M = n :=
  (isNegIndex_negativeCount hM).unique h

/-!
## 1. Variational characterization
-/

/-- **Variational characterization of `N_-`, existence half.** Setting: `M : Matrix ι ι ℂ`
Hermitian, `ι` finite; `N_-(M)` counts strictly negative eigenvalues with multiplicity. There is
a complex subspace of `ι → ℂ` of dimension `negativeCount M` on which `x ↦ Re (x* M x)` is
strictly negative off `0`. -/
theorem exists_isNegDefOn_finrank_eq_negativeCount {M : Matrix ι ι ℂ} (hM : M.IsHermitian) :
    ∃ V : Submodule ℂ (ι → ℂ), IsNegDefOn M V ∧ Module.finrank ℂ V = negativeCount M :=
  (isNegIndex_negativeCount hM).1

/-- **Variational characterization of `N_-`, maximality half.** Setting: `M` Hermitian
on a finite index type; counts with multiplicity, strict negativity. Every complex subspace on
which `x ↦ Re (x* M x)` is strictly negative off `0` has dimension at most `negativeCount M`. -/
theorem finrank_le_negativeCount_of_isNegDefOn {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {V : Submodule ℂ (ι → ℂ)} (hV : IsNegDefOn M V) :
    Module.finrank ℂ V ≤ negativeCount M :=
  (isNegIndex_negativeCount hM).2 V hV

/-!
## 2. Sylvester's law of inertia, negative part
-/

/-- **Sylvester's law of inertia (negative part)**, the congruence step behind Schur inertia.
Setting: `M` Hermitian, `L` with `det L ≠ 0`, both on the finite index type `ι`; `N_-` counts
strictly negative eigenvalues with multiplicity. Then `N_-(Lᴴ M L) = N_-(M)`. -/
theorem negativeCount_conjTranspose_mul_mul {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    {L : Matrix ι ι ℂ} (hL : L.det ≠ 0) :
    negativeCount (Lᴴ * M * L) = negativeCount M :=
  negativeCount_eq_of_isNegIndex (isHermitian_conjTranspose_mul_mul L hM)
    ((isNegIndex_negativeCount hM).conjTranspose_mul_mul
      ((isUnit_iff_isUnit_det L).mpr (isUnit_iff_ne_zero.mpr hL)))

/-!
## 3. Block-diagonal additivity
-/

/-- **Block-diagonal additivity of `N_-`**, the last step of Schur inertia. Setting: `P`, `S`
Hermitian on finite index types `ι`, `κ`; `N_-` counts strictly negative eigenvalues with
multiplicity. Then `N_-(diag(P, S)) = N_-(P) + N_-(S)` on `ι ⊕ κ`. -/
theorem negativeCount_fromBlocks_diag {P : Matrix ι ι ℂ} {S : Matrix κ κ ℂ}
    (hP : P.IsHermitian) (hS : S.IsHermitian) :
    negativeCount (fromBlocks P 0 0 S) = negativeCount P + negativeCount S := by
  obtain ⟨LP, hLP, hPL⟩ := exists_isUnit_eq_conjTranspose_mul_diagonal_mul hP
  obtain ⟨LS, hLS, hSL⟩ := exists_isUnit_eq_conjTranspose_mul_diagonal_mul hS
  set d : ι ⊕ κ → ℝ := Sum.elim hP.eigenvalues hS.eigenvalues
  have hB : fromBlocks P 0 0 S =
      (fromBlocks LP 0 0 LS)ᴴ * diagonal (fun k => (d k : ℂ)) * fromBlocks LP 0 0 LS := by
    have hd : (fun k => (d k : ℂ)) =
        Sum.elim (fun k => (hP.eigenvalues k : ℂ)) (fun k => (hS.eigenvalues k : ℂ)) := by
      funext k
      cases k <;> rfl
    rw [hd, ← fromBlocks_diagonal, fromBlocks_conjTranspose, fromBlocks_multiply,
      fromBlocks_multiply]
    simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [← hPL, ← hSL]
  have hL : IsUnit (fromBlocks LP 0 0 LS) := by
    rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₂₁]
    exact ((isUnit_iff_isUnit_det _).mp hLP).mul ((isUnit_iff_isUnit_det _).mp hLS)
  have hidx : IsNegIndex (fromBlocks P 0 0 S) (Finset.univ.filter fun k => d k < 0).card := by
    rw [hB]
    exact (isNegIndex_diagonal d).conjTranspose_mul_mul hL
  rw [negativeCount_eq_of_isNegIndex (hP.fromBlocks (by simp) hS) hidx,
    negativeCount_of_isHermitian hP, negativeCount_of_isHermitian hS]
  simp only [Finset.card_filter, Fintype.sum_sum_type, d, Sum.elim_inl, Sum.elim_inr]
  congr

/-!
## 4. Haynsworth inertia additivity
-/

/-- **Haynsworth inertia additivity (Schur complement of the upper-left block).** Setting:
`M = [[P, Q], [Qᴴ, R]]` Hermitian on `ι ⊕ κ` (finite), `det P ≠ 0`; `N_-` counts strictly
negative eigenvalues with multiplicity. Then `N_-(M) = N_-(P) + N_-(R - Qᴴ P⁻¹ Q)`. Proof:
`M = Lᴴ diag(P, R - Qᴴ P⁻¹ Q) L` with `L = [[1, P⁻¹ Q], [0, 1]]`, then Sylvester and block
additivity. -/
theorem negativeCount_fromBlocks_schur11 {P : Matrix ι ι ℂ} {Q : Matrix ι κ ℂ}
    {R : Matrix κ κ ℂ} (hM : (fromBlocks P Q Qᴴ R).IsHermitian) (hP : P.det ≠ 0) :
    negativeCount (fromBlocks P Q Qᴴ R) =
      negativeCount P + negativeCount (R - Qᴴ * P⁻¹ * Q) := by
  obtain ⟨hPh, -, -, hRh⟩ := isHermitian_fromBlocks_iff.mp hM
  let _ : Invertible P := invertibleOfIsUnitDet P (isUnit_iff_ne_zero.mpr hP)
  have hPi : P⁻¹.IsHermitian := hPh.inv
  have hSh : (R - Qᴴ * P⁻¹ * Q).IsHermitian := hRh.sub (isHermitian_conjTranspose_mul_mul Q hPi)
  set L : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 (P⁻¹ * Q) 0 1
  have hLH : Lᴴ = fromBlocks 1 0 (Qᴴ * P⁻¹) 1 := by
    simp only [L, fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
      conjTranspose_mul, hPi.eq]
  have hfac : fromBlocks P Q Qᴴ R = Lᴴ * fromBlocks P 0 0 (R - Qᴴ * P⁻¹ * Q) * L := by
    rw [hLH, fromBlocks_eq_of_invertible₁₁ P Q Qᴴ R, invOf_eq_nonsing_inv]
  have hL : L.det ≠ 0 := by
    simp [L]
  rw [hfac, negativeCount_conjTranspose_mul_mul (hPh.fromBlocks (by simp) hSh) hL,
    negativeCount_fromBlocks_diag hPh hSh]

/-- **Haynsworth inertia additivity (Schur complement of the lower-right block).** As
`negativeCount_fromBlocks_schur11`, eliminating the other block. Setting: `M = [[P, Q], [Qᴴ, R]]`
Hermitian on `ι ⊕ κ` (finite), `det R ≠ 0`; counts with multiplicity, strict negativity. Then
`N_-(M) = N_-(R) + N_-(P - Q R⁻¹ Qᴴ)`. -/
theorem negativeCount_fromBlocks_schur22 {P : Matrix ι ι ℂ} {Q : Matrix ι κ ℂ}
    {R : Matrix κ κ ℂ} (hM : (fromBlocks P Q Qᴴ R).IsHermitian) (hR : R.det ≠ 0) :
    negativeCount (fromBlocks P Q Qᴴ R) =
      negativeCount R + negativeCount (P - Q * R⁻¹ * Qᴴ) := by
  obtain ⟨hPh, -, -, hRh⟩ := isHermitian_fromBlocks_iff.mp hM
  let _ : Invertible R := invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hR)
  have hRi : R⁻¹.IsHermitian := hRh.inv
  have hSh : (P - Q * R⁻¹ * Qᴴ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Qᴴ hRi
    rw [conjTranspose_conjTranspose] at this
    exact hPh.sub this
  set L : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 0 (R⁻¹ * Qᴴ) 1
  have hLH : Lᴴ = fromBlocks 1 (Q * R⁻¹) 0 1 := by
    simp only [L, fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
      conjTranspose_mul, conjTranspose_conjTranspose, hRi.eq]
  have hfac : fromBlocks P Q Qᴴ R = Lᴴ * fromBlocks (P - Q * R⁻¹ * Qᴴ) 0 0 R * L := by
    rw [hLH, fromBlocks_eq_of_invertible₂₂ P Q Qᴴ R, invOf_eq_nonsing_inv]
  have hL : L.det ≠ 0 := by
    simp [L]
  rw [hfac, negativeCount_conjTranspose_mul_mul (hSh.fromBlocks (by simp) hRh) hL,
    negativeCount_fromBlocks_diag hSh hRh, add_comm]

/-!
## 5. The shifted form used by the layer recursion
-/

omit [Fintype ι] in
theorem isHermitian_sub_smul_one {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (E : ℝ) :
    (H - E • (1 : Matrix ι ι ℂ)).IsHermitian :=
  hH.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))

/-- **Schur inertia in the layer-recursion shape** (Schur inertia gives exactly
`N_H = N_{n-1} + N_-(A_0 - E - Σ)`). Setting: `H : Matrix ι ι ℂ` and `D : Matrix κ κ ℂ` Hermitian,
`C : Matrix ι κ ℂ` arbitrary, a real energy `E` with `det (H - E) ≠ 0`; `N_-` counts strictly
negative eigenvalues with multiplicity. Then
`N_-([[H - E, C], [Cᴴ, D - E]]) = N_-(H - E) + N_-(D - E - Cᴴ (H - E)⁻¹ C)`. -/
theorem negativeCount_fromBlocks_sub_smul_one {H : Matrix ι ι ℂ} {D : Matrix κ κ ℂ}
    (hH : H.IsHermitian) (hD : D.IsHermitian) (C : Matrix ι κ ℂ) (E : ℝ)
    (hdet : (H - E • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    negativeCount (fromBlocks (H - E • (1 : Matrix ι ι ℂ)) C Cᴴ (D - E • (1 : Matrix κ κ ℂ))) =
      negativeCount (H - E • (1 : Matrix ι ι ℂ)) +
        negativeCount (D - E • (1 : Matrix κ κ ℂ) - Cᴴ * (H - E • (1 : Matrix ι ι ℂ))⁻¹ * C) :=
  negativeCount_fromBlocks_schur11
    ((isHermitian_sub_smul_one hH E).fromBlocks rfl (isHermitian_sub_smul_one hD E)) hdet

end BlockBand.Layers
