module

public import BlockBand.LocalWindow.ProofCount
public import BlockBand.Coarea.SchurDerivative

/-!
# Truncating the exterior near the energy

Truncating the exterior resolvent near the energy changes the Schur complement by a perturbation
of small rank, in the form used by the counting estimates (`window_count_le`,
`spectralSum_poisson_le`): at a nonpole energy `E`
(`det(H_R - E) ≠ 0`), `F(E)` and `F̂(E)` agree on a subspace of codimension at most
`N_{H_R}([E - ε, E + ε])`; hence for every pair matrix `G`, `F̂(E) + G - E` is a perturbation of
rank `N_{H_R}([E-ε, E+ε])` and size `0` of `F(E) + G - E` (`isPerturbation_truncF`). On the
crowding event's complement this rank is `≤ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofCount

open Matrix Module Finset BlockBand.Coarea
open scoped InnerProductSpace

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The truncated inverse `g_ε(x) = x/ε²` for `|x| ≤ ε`, `x⁻¹` otherwise. -/
def truncInv (ε x : ℝ) : ℝ := if |x| ≤ ε then x / ε ^ 2 else x⁻¹

/-- `g_ε(H - E)` by the spectral theorem (`0` off the Hermitian matrices). -/
def truncResolvent (ε : ℝ) (H : Matrix α α ℂ) (E : ℝ) : Matrix α α ℂ :=
  if hH : H.IsHermitian then
    (hH.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun j => ((truncInv ε (hH.eigenvalues j - E) : ℝ) : ℂ)) *
        star (hH.eigenvectorUnitary : Matrix α α ℂ)
  else 0

/-- `F̂(E) = V - C* g_ε(H_R - E) C`. -/
def truncF (ε : ℝ) (H_R : Matrix α α ℂ) (C : Matrix α β ℂ) (V : Matrix β β ℂ) (E : ℝ) :
    Matrix β β ℂ :=
  V - Cᴴ * truncResolvent ε H_R E * C

/-- The exterior eigenvalues within `ε` of `E`. -/
def nearSet (ε : ℝ) {H : Matrix α α ℂ} (hH : H.IsHermitian) (E : ℝ) : Finset α :=
  univ.filter fun j => |hH.eigenvalues j - E| ≤ ε

section Spectral

variable {H : Matrix α α ℂ}

theorem conj_mul_conj (U : Matrix.unitaryGroup α ℂ) (d e : α → ℂ) :
    ((U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ)) *
        ((U : Matrix α α ℂ) * diagonal e * star (U : Matrix α α ℂ)) =
      (U : Matrix α α ℂ) * diagonal (d * e) * star (U : Matrix α α ℂ) := by
  have hsU : star (U : Matrix α α ℂ) * U = 1 := Unitary.coe_star_mul_self _
  calc ((U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ)) *
        ((U : Matrix α α ℂ) * diagonal e * star (U : Matrix α α ℂ))
      = U * diagonal d * (star (U : Matrix α α ℂ) * U) * diagonal e * star (U : Matrix α α ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsU, Matrix.mul_one, Matrix.mul_assoc (U : Matrix α α ℂ),
        diagonal_mul_diagonal]; rfl

theorem conj_sub_conj (U : Matrix.unitaryGroup α ℂ) (d e : α → ℂ) :
    (U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ) -
        (U : Matrix α α ℂ) * diagonal e * star (U : Matrix α α ℂ) =
      (U : Matrix α α ℂ) * diagonal (d - e) * star (U : Matrix α α ℂ) := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]; rfl

/-- `H - E = U diag(λ - E) U*`. -/
theorem sub_eq_conj (hH : H.IsHermitian) (E : ℝ) :
    H - (E : ℂ) • (1 : Matrix α α ℂ) =
      (hH.eigenvectorUnitary : Matrix α α ℂ) *
        diagonal (fun j => ((hH.eigenvalues j - E : ℝ) : ℂ)) *
          star (hH.eigenvectorUnitary : Matrix α α ℂ) := by
  set U := hH.eigenvectorUnitary
  have hUs : (U : Matrix α α ℂ) * star (U : Matrix α α ℂ) = 1 := Unitary.coe_mul_star_self _
  have hE : (E : ℂ) • (1 : Matrix α α ℂ) =
      (U : Matrix α α ℂ) * diagonal (fun _ => (E : ℂ)) * star (U : Matrix α α ℂ) := by
    rw [show diagonal (fun _ : α => (E : ℂ)) = (E : ℂ) • (1 : Matrix α α ℂ) by
      ext i j; by_cases h : i = j <;> simp [diagonal, h], Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hUs]
  conv_lhs => rw [show H = (U : Matrix α α ℂ) * diagonal (fun i => (hH.eigenvalues i : ℂ)) *
      star (U : Matrix α α ℂ) by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]; rfl]
  rw [hE, conj_sub_conj]
  refine congrArg (fun d => (U : Matrix α α ℂ) * diagonal d * star (U : Matrix α α ℂ))
    (funext fun j => ?_)
  simp

/-- At a nonpole energy every eigenvalue differs from `E`. -/
theorem eigenvalues_ne_of_det (hH : H.IsHermitian) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) (j : α) : hH.eigenvalues j ≠ E := by
  intro hj
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨hH.eigenvectorBasis j, ?_, ?_⟩
  · intro h0
    have h1 := (hH.eigenvectorBasis).orthonormal.1 j
    have : (hH.eigenvectorBasis j : EuclideanSpace ℂ α) = 0 :=
      WithLp.ofLp_injective 2 (by rw [WithLp.ofLp_zero]; exact h0)
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  · rw [Matrix.sub_mulVec, hH.mulVec_eigenvectorBasis j, hj, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]; exact sub_eq_zero.mpr rfl

/-- `(H - E)⁻¹ = U diag((λ - E)⁻¹) U*` at a nonpole energy. -/
theorem resolvent_eq_conj (hH : H.IsHermitian) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    physicalCoareaResolvent H E =
      (hH.eigenvectorUnitary : Matrix α α ℂ) *
        diagonal (fun j => (((hH.eigenvalues j - E)⁻¹ : ℝ) : ℂ)) *
          star (hH.eigenvectorUnitary : Matrix α α ℂ) := by
  unfold physicalCoareaResolvent
  apply Matrix.inv_eq_right_inv
  rw [sub_eq_conj hH E, conj_mul_conj]
  have : (fun j => ((hH.eigenvalues j - E : ℝ) : ℂ)) *
      (fun j => (((hH.eigenvalues j - E)⁻¹ : ℝ) : ℂ)) = 1 := by
    funext j
    have hne : hH.eigenvalues j - E ≠ 0 := sub_ne_zero.mpr (eigenvalues_ne_of_det hH hdet j)
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one]
  rw [this, show (diagonal (1 : α → ℂ)) = 1 from diagonal_one, Matrix.mul_one]
  exact Unitary.coe_mul_star_self _

/-- `(H - E)⁻¹ - g_ε(H - E) = U diag(h) U*` with `h_j = 0` when `|λ_j - E| > ε`. -/
theorem resolvent_sub_trunc (hH : H.IsHermitian) (ε : ℝ) {E : ℝ}
    (hdet : (H - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    physicalCoareaResolvent H E - truncResolvent ε H E =
      (hH.eigenvectorUnitary : Matrix α α ℂ) *
        diagonal (fun j => if |hH.eigenvalues j - E| ≤ ε then
            ((((hH.eigenvalues j - E)⁻¹ - truncInv ε (hH.eigenvalues j - E)) : ℝ) : ℂ) else 0) *
          star (hH.eigenvectorUnitary : Matrix α α ℂ) := by
  rw [resolvent_eq_conj hH hdet]
  unfold truncResolvent
  simp only [hH, ↓reduceDIte]
  rw [conj_sub_conj]
  refine congrArg (fun d => (hH.eigenvectorUnitary : Matrix α α ℂ) * diagonal d *
    star (hH.eigenvectorUnitary : Matrix α α ℂ)) (funext fun j => ?_)
  simp only [Pi.sub_apply]
  split_ifs with h
  · push_cast; ring
  · unfold truncInv; simp [h]

end Spectral

/-!
## Agreement off the near eigenvectors
-/

section Agree

variable {H_R : Matrix α α ℂ} (hH : H_R.IsHermitian) (C : Matrix α β ℂ)

/-- The coordinates `(U* C y)_j` of `C y` along the near exterior eigenvectors. -/
def nearCoords (ε E : ℝ) : EuclideanSpace ℂ β →ₗ[ℂ] ({j // j ∈ nearSet ε hH E} → ℂ) :=
  (Matrix.mulVecLin (Matrix.of fun (j : {j // j ∈ nearSet ε hH E}) (b : β) =>
      (star (hH.eigenvectorUnitary : Matrix α α ℂ) * C) j.1 b)).comp
    (WithLp.linearEquiv 2 ℂ (β → ℂ)).toLinearMap

theorem nearCoords_apply (ε E : ℝ) (y : EuclideanSpace ℂ β) (j : {j // j ∈ nearSet ε hH E}) :
    nearCoords hH C ε E y j =
      ((star (hH.eigenvectorUnitary : Matrix α α ℂ) * C) *ᵥ WithLp.ofLp y) j.1 := by
  simp [nearCoords, Matrix.mulVec, dotProduct]

/-- The kernel of `nearCoords` has codimension at most `#near`. -/
theorem finrank_ker_nearCoords (ε E : ℝ) :
    Fintype.card β ≤ finrank ℂ (LinearMap.ker (nearCoords hH C ε E)) +
      (nearSet ε hH E).card := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (nearCoords hH C ε E)
  have h2 := Submodule.finrank_le (LinearMap.range (nearCoords hH C ε E))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  rw [finrank_euclideanSpace] at h1
  omega

/-- **`F(E)` and `F̂(E)` agree on `ker nearCoords`** at a nonpole energy. -/
theorem physicalCoareaF_mulVec_eq (ε : ℝ) (V : Matrix β β ℂ) {E : ℝ}
    (hdet : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) {y : EuclideanSpace ℂ β}
    (hy : y ∈ LinearMap.ker (nearCoords hH C ε E)) :
    physicalCoareaF H_R C V E *ᵥ WithLp.ofLp y = truncF ε H_R C V E *ᵥ WithLp.ofLp y := by
  rw [LinearMap.mem_ker] at hy
  set U := hH.eigenvectorUnitary
  set h : α → ℂ := fun j => if |hH.eigenvalues j - E| ≤ ε then
    ((((hH.eigenvalues j - E)⁻¹ - truncInv ε (hH.eigenvalues j - E)) : ℝ) : ℂ) else 0
  have hdiff : physicalCoareaF H_R C V E - truncF ε H_R C V E =
      -(Cᴴ * ((U : Matrix α α ℂ) * diagonal h * star (U : Matrix α α ℂ)) * C) := by
    unfold physicalCoareaF truncF
    rw [← resolvent_sub_trunc hH ε hdet, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hz : diagonal h *ᵥ ((star (U : Matrix α α ℂ) * C) *ᵥ WithLp.ofLp y) = 0 := by
    ext j
    rw [mulVec_diagonal, Pi.zero_apply]
    by_cases hj : |hH.eigenvalues j - E| ≤ ε
    · have hmem : j ∈ nearSet ε hH E := by simp [nearSet, hj]
      have := congrFun hy ⟨j, hmem⟩
      rw [nearCoords_apply, Pi.zero_apply] at this
      rw [this, mul_zero]
    · simp [h, hj]
  have : (physicalCoareaF H_R C V E - truncF ε H_R C V E) *ᵥ WithLp.ofLp y = 0 := by
    rw [hdiff, Matrix.neg_mulVec]
    rw [show Cᴴ * ((U : Matrix α α ℂ) * diagonal h * star (U : Matrix α α ℂ)) * C =
      Cᴴ * (U : Matrix α α ℂ) * (diagonal h * (star (U : Matrix α α ℂ) * C)) by
        simp only [Matrix.mul_assoc]]
    rw [← Matrix.mulVec_mulVec (M := Cᴴ * (U : Matrix α α ℂ)),
      ← Matrix.mulVec_mulVec (M := diagonal h) (N := star (U : Matrix α α ℂ) * C), hz,
      Matrix.mulVec_zero, neg_zero]
  rwa [Matrix.sub_mulVec, sub_eq_zero] at this

/-- **Truncation is a perturbation of rank `N_{H_R}([E-ε,E+ε])`**: at a nonpole energy, for
every pair matrix `G`, `F̂(E) + G - E` agrees with `F(E) + G - E` on a subspace of codimension
at most `#{j : |λ_j(H_R) - E| ≤ ε}`. -/
theorem isPerturbation_truncF (ε : ℝ) (V G : Matrix β β ℂ) {E : ℝ}
    (hdet : (H_R - (E : ℂ) • (1 : Matrix α α ℂ)).det ≠ 0) :
    IsPerturbation (truncF ε H_R C V E + G - (E : ℂ) • 1)
      (physicalCoareaF H_R C V E + G - (E : ℂ) • 1) (nearSet ε hH E).card 0 := by
  refine isPerturbation_of_agree (LinearMap.ker (nearCoords hH C ε E))
    (finrank_ker_nearCoords hH C ε E) fun y hy => ?_
  apply WithLp.ofLp_injective (p := 2)
  show (physicalCoareaF H_R C V E + G - (E : ℂ) • 1) *ᵥ WithLp.ofLp y =
    (truncF ε H_R C V E + G - (E : ℂ) • 1) *ᵥ WithLp.ofLp y
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
    physicalCoareaF_mulVec_eq hH C ε V hdet hy]

/-- The near count is the exterior eigenvalue count in `[E - ε, E + ε]`. -/
theorem nearSet_card_eq (ε E : ℝ) :
    ((nearSet ε hH E).card : ℝ) =
      BlockBand.Internal.Contracts.Inputs.spectralSum H_R
        (fun l => if E - ε ≤ l ∧ l ≤ E + ε then 1 else 0) := by
  rw [spectralSum_Icc hH]
  congr 2
  ext j
  simp only [nearSet, mem_filter, mem_univ, true_and, abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end Agree

end BlockBand.LocalWindow.ProofCount
