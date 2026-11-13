module

public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyRegular

/-!
# Physical-clock glue: the block clocks `D_j = L*P_jL` of the one-block reconstruction

Step 2 of the proof of the microscopic tag comparison: let `𝒯` be its physical Schur lift, and put
`D_j = 𝒯*P_j𝒯`, `D = Σ_j D_j = 𝒯*𝒯`. Then the scaled mass on block `j` is `n v*D_jv / v*Dv`.

* `mts_liftMatrix`: the Schur lift `𝒯 = L(e)` as a `Site × BlockSite` matrix,
  `𝒯 v = blockLift ω e v` (`mts_liftMatrix_mulVec`).
* `mts_blockClockMatrix j = 𝒯*P_j𝒯`: `v*D_jv = Σ_a ‖(𝒯v)_{(j,a)}‖² = mts_fieldClock j`
  (`mts_quadForm_blockClockMatrix`), PSD (`mts_blockClockMatrix_posSemidef`).
* `mts_sum_blockClockMatrix_sub_one`: `Σ_j D_j - 1 ⪰ 0` (the block-`k` part of `𝒯` is the
  identity), and the same after reindexing by `σ : BlockSite p k ≃ Fin N`
  (`mts_reindex_tags_sub_one`, `mts_quadForm_reindex`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder ComplexConjugate

variable (p : Parameters) (k : ZMod p.n)

/-- The Schur lift `𝒯 = L(e)`: identity on block `k`, `-T(e)` off it. -/
def mts_liftMatrix (ω : BlockState p k) (e : ℝ) : Matrix p.Site (BlockSite p k) ℂ :=
  fun x y => if hx : x.1 = k then (if (⟨x, hx⟩ : BlockSite p k) = y then 1 else 0)
    else -(physicalCoareaT ω.1 ω.2 e ⟨x, hx⟩ y)

theorem mts_liftMatrix_mulVec (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ) :
    mts_liftMatrix p k ω e *ᵥ v = blockLift p k ω e v := by
  funext x
  simp only [mulVec, dotProduct, mts_liftMatrix, blockLift]
  by_cases hx : x.1 = k
  · simp only [hx, dite_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  · simp only [hx, dite_false, neg_mul, Finset.sum_neg_distrib]

/-- `D_j = 𝒯*P_j𝒯`. -/
def mts_blockClockMatrix (ω : BlockState p k) (e : ℝ) (j : ZMod p.n) :
    Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  Matrix.conjTranspose (mts_liftMatrix p k ω e) *
    Matrix.diagonal (fun x : p.Site => (((if x.1 = j then 1 else 0 : ℝ)) : ℂ)) *
    mts_liftMatrix p k ω e

theorem mts_quadForm_blockClockMatrix (ω : BlockState p k) (e : ℝ) (j : ZMod p.n)
    (v : BlockSite p k → ℂ) :
    quadForm (mts_blockClockMatrix p k ω e j) v = mts_fieldClock p k e ω v j := by
  unfold mts_blockClockMatrix mts_fieldClock
  rw [mts_quadForm_conj_diagonal, mts_liftMatrix_mulVec, Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  simp

theorem mts_blockClockMatrix_posSemidef (ω : BlockState p k) (e : ℝ) (j : ZMod p.n) :
    (mts_blockClockMatrix p k ω e j).PosSemidef := by
  unfold mts_blockClockMatrix
  refine PosSemidef.conjTranspose_mul_mul_same ?_ _
  rw [posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

/-- A Hermitian matrix with nonnegative real quadratic form is PSD. -/
theorem mts_posSemidef_of_quadForm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (h : ∀ v, 0 ≤ quadForm A v) : A.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hA fun v => ?_
  have him : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    have := hA.star_dotProduct_mulVec_comm v v
    rw [Complex.star_def] at this
    exact Complex.conj_eq_iff_im.1 this
  rw [Complex.nonneg_iff]
  exact ⟨h v, him.symm⟩

theorem mts_quadForm_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    quadForm (1 : Matrix ι ι ℂ) v = ∑ i, ‖v i‖ ^ 2 := by
  unfold quadForm
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem mts_quadForm_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm (A - B) v = quadForm A v - quadForm B v := by
  unfold quadForm
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- `Σ_j D_j - 1 ⪰ 0`: the block-`k` clock of `𝒯v` is `‖v‖²`. -/
theorem mts_sum_blockClockMatrix_sub_one (ω : BlockState p k) (e : ℝ) :
    ((∑ j, mts_blockClockMatrix p k ω e j) - 1).PosSemidef := by
  have hS : (∑ j, mts_blockClockMatrix p k ω e j).PosSemidef :=
    posSemidef_sum _ fun j _ => mts_blockClockMatrix_posSemidef p k ω e j
  refine mts_posSemidef_of_quadForm (hS.isHermitian.sub isHermitian_one) fun v => ?_
  rw [mts_quadForm_sub, mts_quadForm_sum, mts_quadForm_one]
  simp only [mts_quadForm_blockClockMatrix]
  have hk : mts_fieldClock p k e ω v k = ∑ i, ‖v i‖ ^ 2 := by
    unfold mts_fieldClock
    rw [← (mts_blockSiteEquiv p k).symm.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [blockLift, mts_blockSiteEquiv]
  have hnn : ∀ j, 0 ≤ mts_fieldClock p k e ω v j := fun j =>
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have := Finset.single_le_sum (f := fun j => mts_fieldClock p k e ω v j)
    (fun j _ => hnn j) (Finset.mem_univ k)
  linarith

/-!
## Reindexing to `Fin N`
-/

theorem mts_quadForm_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (A : Matrix ι ι ℂ) (v : κ → ℂ) : quadForm (Matrix.reindex σ σ A) v = quadForm A (v ∘ σ) := by
  unfold quadForm
  rw [mts_reindex_mulVec, dotProduct_comp_equiv_symm]
  rfl

theorem mts_reindex_tags_sub_one {N : ℕ} (σ : BlockSite p k ≃ Fin N) (ω : BlockState p k)
    (e : ℝ) :
    ((∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)) - 1).PosSemidef := by
  have h : (∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)) - 1 =
      Matrix.reindex σ σ ((∑ j, mts_blockClockMatrix p k ω e j) - 1) := by
    simp only [Matrix.reindex_apply, submatrix_sub]
    congr 1
    · ext a b
      simp [Matrix.sum_apply]
    · exact (submatrix_one_equiv σ.symm).symm
  rw [h, Matrix.reindex_apply]
  exact (mts_sum_blockClockMatrix_sub_one p k ω e).submatrix _

theorem mts_reindex_blockClockMatrix_posSemidef {N : ℕ} (σ : BlockSite p k ≃ Fin N)
    (ω : BlockState p k) (e : ℝ) (j : ZMod p.n) :
    (Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)).PosSemidef := by
  rw [Matrix.reindex_apply]
  exact (mts_blockClockMatrix_posSemidef p k ω e j).submatrix _

end BlockBand.Endpoints
