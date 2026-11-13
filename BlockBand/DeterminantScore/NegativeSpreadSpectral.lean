module

public import BlockBand.DeterminantScore.NegativeSpreadEnergy
public import BlockBand.DeterminantScore.Sector.InverseForm

/-!
# Spectral identities for the spread test

For Hermitian `M` with `det M ≠ 0`: `Re Tr M⁻² = Σ_i λ_i⁻²` and `Re Tr M² = Σ_i λ_i²`
(`trace_inv_mul_inv_re`, `trace_mul_self_re`), and the ordered eigenvalues `orderedEigs`
satisfy `invSqSum (orderedEigs K x) = sectorInvSq K x` (`invSqSum_orderedEigs`),
`(invSqSum)⁻¹ ≤ Re Tr M²` and have no zero entry.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.NegativeSpread

open Matrix BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.Internal.Contracts.CoareaPalm

section Herm

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_conj_unitary (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem spectral_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M = (hM.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (hM.eigenvalues i : ℂ)) *
      star (hM.eigenvectorUnitary : Matrix n n ℂ) := by
  conv_lhs => rw [hM.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem trace_inv_mul_inv_re {M : Matrix n n ℂ} (hM : M.IsHermitian) (hdet : M.det ≠ 0) :
    (M⁻¹ * M⁻¹).trace.re = ∑ i, (hM.eigenvalues i)⁻¹ ^ 2 := by
  set U : Matrix n n ℂ := (hM.eigenvectorUnitary : Matrix n n ℂ)
  have hne : ∀ i, (hM.eigenvalues i : ℂ) ≠ 0 := by
    rw [hM.det_eq_prod_eigenvalues, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  set N := U * diagonal (fun i => ((hM.eigenvalues i : ℂ))⁻¹) * star U
  have hsU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUs : U * star U = 1 := Unitary.coe_mul_star_self _
  have hconj : ∀ d e : n → ℂ, (U * diagonal d * star U) * (U * diagonal e * star U) =
      U * diagonal (d * e) * star U := by
    intro d e
    calc (U * diagonal d * star U) * (U * diagonal e * star U)
        = U * diagonal d * (star U * U) * diagonal e * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (d * e) * star U := by
          rw [hsU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; rfl
  have hMN : M * N = 1 := by
    rw [spectral_eq hM, hconj]
    have : (fun i => (hM.eigenvalues i : ℂ)) * (fun i => ((hM.eigenvalues i : ℂ))⁻¹) = 1 := by
      funext i; simp [hne i]
    rw [this, show (diagonal (1 : n → ℂ)) = 1 from diagonal_one, Matrix.mul_one, hUs]
  rw [Matrix.inv_eq_right_inv hMN, hconj, trace_conj_unitary, trace_diagonal]
  simp only [Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re, sq]

theorem trace_mul_self_re {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (M * M).trace.re = ∑ i, hM.eigenvalues i ^ 2 := by
  set U : Matrix n n ℂ := (hM.eigenvectorUnitary : Matrix n n ℂ)
  have hsU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hconj : ∀ d e : n → ℂ, (U * diagonal d * star U) * (U * diagonal e * star U) =
      U * diagonal (d * e) * star U := by
    intro d e
    calc (U * diagonal d * star U) * (U * diagonal e * star U)
        = U * diagonal d * (star U * U) * diagonal e * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (d * e) * star U := by
          rw [hsU, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; rfl
  have hM2 : M * M = U * diagonal ((fun i => (hM.eigenvalues i : ℂ)) * fun i => (hM.eigenvalues i : ℂ)) * star U := by
    conv_lhs => rw [spectral_eq hM]
    exact hconj _ _
  rw [hM2, trace_conj_unitary, trace_diagonal]
  simp only [Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]

end Herm

section Ordered

variable {m : ℕ}

/-- The increasing eigenvalues are a reindexing of `eigenvalues`. -/
theorem sum_freshEigenvalue {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian) (g : ℝ → ℝ) :
    ∑ k, g (freshEigenvalue M k) = ∑ i, g (hM.eigenvalues i) := by
  have h1 : ∀ k, freshEigenvalue M k =
      hM.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm k).rev := by
    intro k
    simp [freshEigenvalue, BlockBand.Model.Construction.rawIncreasingEigenvalue, hM,
      BlockBand.Foundations.Spectral.increasingEigenvalue]
  simp only [h1, Matrix.IsHermitian.eigenvalues]
  let e1 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (finCongr (Fintype.card_fin m).symm).trans Fin.revPerm
  let e2 : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  rw [show (∑ k, g (hM.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm k).rev)) =
      ∑ k, g (hM.eigenvalues₀ (e1 k)) from rfl,
    show (∑ i, g (hM.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i))) =
      ∑ i, g (hM.eigenvalues₀ (e2 i)) from rfl,
    Equiv.sum_comp e1 (fun j => g (hM.eigenvalues₀ j)),
    Equiv.sum_comp e2 (fun j => g (hM.eigenvalues₀ j))]

theorem freshEigenvalue_ne_zero {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.IsHermitian)
    (hdet : M.det ≠ 0) (k : Fin m) : freshEigenvalue M k ≠ 0 := by
  have h1 : freshEigenvalue M k =
      hM.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm k).rev := by
    simp [freshEigenvalue, BlockBand.Model.Construction.rawIncreasingEigenvalue, hM,
      BlockBand.Foundations.Spectral.increasingEigenvalue]
  set j := (Fin.cast (Fintype.card_fin m).symm k).rev
  have hj : hM.eigenvalues₀ j = hM.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin _) j) := by
    simp [Matrix.IsHermitian.eigenvalues]
  rw [h1, hj]
  intro h0
  apply hdet
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ (Fintype.equivOfCardEq (Fintype.card_fin _) j))
    (by rw [h0]; simp)

theorem orderedEigs_ne_zero {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    {x : HermCoord m → ℝ} (hdet : (K + hermOfCoord x).det ≠ 0) (k : Fin m) :
    orderedEigs K x k ≠ 0 :=
  freshEigenvalue_ne_zero (isHermitian_add_hermOfCoord hK x) hdet k

theorem invSqSum_orderedEigs {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    {x : HermCoord m → ℝ} (hdet : (K + hermOfCoord x).det ≠ 0) :
    invSqSum (orderedEigs K x) = sectorInvSq K x := by
  have hM := isHermitian_add_hermOfCoord hK x
  rw [sectorInvSq, trace_inv_mul_inv_re hM hdet, invSqSum]
  exact sum_freshEigenvalue hM (fun y => y⁻¹ ^ 2)

theorem invSqSum_orderedEigs_inv_le {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    {x : HermCoord m → ℝ} (hdet : (K + hermOfCoord x).det ≠ 0) (j : Fin m) :
    (invSqSum (orderedEigs K x))⁻¹ ≤
      ((K + hermOfCoord x) * (K + hermOfCoord x)).trace.re := by
  have hM := isHermitian_add_hermOfCoord hK x
  rw [trace_mul_self_re hM, ← sum_freshEigenvalue hM (fun y => y ^ 2)]
  have hne := orderedEigs_ne_zero hK hdet
  have hpos : 0 < (orderedEigs K x j)⁻¹ ^ 2 := by have := hne j; positivity
  calc (invSqSum (orderedEigs K x))⁻¹ ≤ ((orderedEigs K x j)⁻¹ ^ 2)⁻¹ :=
        inv_anti₀ hpos (sq_le_invSqSum _ j)
    _ = orderedEigs K x j ^ 2 := by rw [inv_pow, inv_inv]
    _ ≤ ∑ k, freshEigenvalue (K + hermOfCoord x) k ^ 2 :=
        Finset.single_le_sum (f := fun k => freshEigenvalue (K + hermOfCoord x) k ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem measurable_orderedEigs (K : Matrix (Fin m) (Fin m) ℂ) :
    Measurable (orderedEigs K) := by
  refine Measurable.of_eval fun k => ?_
  exact (BlockBand.Model.Construction.measurable_rawIncreasingEigenvalue _).comp
    (continuous_add_hermOfCoord K).measurable

end Ordered

end BlockBand.DeterminantScore.NegativeSpread
