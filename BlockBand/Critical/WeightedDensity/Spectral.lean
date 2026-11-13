module

public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Palm.FreshPalmShift
public import BlockBand.Model.Construction.OrderedSimpleSpectrum

/-!
# Simple spectrum of `F + GUE` and spectral sums of the fresh eigenprojectors

Support for the global weighted density lemma and the relative matrix density lemma: the
matrix spectral density `Σ_F(e)` is written with the selections `freshEigenvalue`,
`freshEigenvector` (`BlockBand.Internal.Contracts.CoareaPalm`), and the functional calculus
`1_I(F+G)` is Mathlib's `cfc`. This file identifies the two on simple spectrum.

*Law.* `G ~ gueMeasure (Fin N) t` (`GUE_N(t)`, diagonal variance `t`), `t > 0`.
*Domain.* every `N`, every Hermitian `F` (no norm bound); deterministic statements for every
Hermitian `K` with pairwise distinct increasing eigenvalues (`SimpleSpectrum K`).
No limit, norm or uniformity statement.

* `measurableSet_simpleSpectrum`: the simple-spectrum locus is Borel.
* `ae_simpleSpectrum_add_gue`: for Hermitian `F` and `t > 0`, `F + G` has simple spectrum
  `GUE_N(t)`-almost surely (Lebesgue density of the coordinates, translation invariance of
  Lebesgue measure, volume-a.e. separability of the characteristic polynomial).
* On simple spectrum: `mulVec_freshEigenvector` (eigen-equation), `orthonormal`,
  `sum_freshProjector` (`Σ_ℓ u_ℓ u_ℓ* = I`), `cfc_eq_sum` (`f(K) = Σ_ℓ f(λ_ℓ) u_ℓu_ℓ*` for every
  `f : ℝ → ℝ`), `inv_eq_sum` (`(K - z)⁻¹ = Σ_ℓ (λ_ℓ - z)⁻¹ u_ℓu_ℓ*`, `Im z ≠ 0`), and
  `add_smul_one` (stability under real scalar shifts).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.WeightedDensity

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.FreshPalm
  BlockBand.Model.Construction BlockBand.Foundations.Spectral
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

/-- Hermitian with pairwise distinct increasing eigenvalues. -/
def SimpleSpectrum (K : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  K.IsHermitian ∧ Function.Injective (freshEigenvalue K)

/-- The simple-spectrum locus is a Borel set of matrices. -/
theorem measurableSet_simpleSpectrum :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | SimpleSpectrum K} := by
  have hs : {K : Matrix (Fin N) (Fin N) ℂ | SimpleSpectrum K} =
      {K | K.IsHermitian} ∩ ⋂ ℓ : Fin N, ⋂ m : Fin N, ⋂ (_ : ℓ ≠ m),
        {K | freshEigenvalue K ℓ ≠ freshEigenvalue K m} := by
    ext K
    simp only [SimpleSpectrum, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    refine and_congr_right fun _ => ⟨fun h ℓ m hlm heq => hlm (h heq), fun h ℓ m heq => ?_⟩
    by_contra hlm
    exact h ℓ m hlm heq
  rw [hs]
  exact (measurableSet_isHermitian).inter (MeasurableSet.iInter fun ℓ => MeasurableSet.iInter
    fun m => MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_freshEigenvalue ℓ) (measurable_freshEigenvalue m)).compl)

/-!
## Translating the selections to the canonical eigenbasis
-/

/-- `freshEigenvalue` is the increasing eigenvalue at the cast rank. -/
theorem freshEigenvalue_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (ℓ : Fin N) :
    freshEigenvalue K ℓ = increasingEigenvalue hK (Fin.cast (Fintype.card_fin N).symm ℓ) := by
  unfold freshEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hK]

theorem freshEigenvector_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian) (ℓ : Fin N) :
    freshEigenvector K ℓ =
      orderedColumnSelection (Fin.cast (Fintype.card_fin N).symm ℓ) ⟨K, hK⟩ := by
  funext x
  unfold freshEigenvector
  rw [rawOrderedColumnSelection_eq _ _ hK]

theorem SimpleSpectrum.injective_orderedEigenvalue {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) :
    Function.Injective (orderedEigenvalue (⟨K, hK.1⟩ : Model.Construction.HermitianMatrix (Fin N))) := by
  intro i j hij
  have h := @hK.2 (Fin.cast (Fintype.card_fin N) i) (Fin.cast (Fintype.card_fin N) j)
  rw [freshEigenvalue_eq hK.1, freshEigenvalue_eq hK.1] at h
  have := h (by simpa [orderedEigenvalue] using hij)
  exact Fin.cast_injective _ this

theorem SimpleSpectrum.add_smul_one {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (ζ : ℝ) : SimpleSpectrum (K + (ζ : ℂ) • 1) := by
  refine ⟨hK.1.add (isHermitian_one.smul (Complex.conj_ofReal ζ)), fun ℓ m h => ?_⟩
  rw [freshEigenvalue_add_smul_one hK.1, freshEigenvalue_add_smul_one hK.1] at h
  exact hK.2 (add_right_cancel h)

theorem SimpleSpectrum.mulVec_freshEigenvector {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (ℓ : Fin N) :
    K *ᵥ freshEigenvector K ℓ = ((freshEigenvalue K ℓ : ℝ) : ℂ) • freshEigenvector K ℓ := by
  rw [freshEigenvector_eq hK.1, freshEigenvalue_eq hK.1]
  exact mulVec_orderedColumnSelection _ ⟨K, hK.1⟩ hK.injective_orderedEigenvalue

theorem SimpleSpectrum.orthonormal {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (ℓ m : Fin N) :
    star (freshEigenvector K ℓ) ⬝ᵥ freshEigenvector K m = if ℓ = m then 1 else 0 := by
  rw [freshEigenvector_eq hK.1, freshEigenvector_eq hK.1]
  have h := orderedColumnSelection_orthonormal (Fin.cast (Fintype.card_fin N).symm ℓ)
    (Fin.cast (Fintype.card_fin N).symm m) ⟨K, hK.1⟩ hK.injective_orderedEigenvalue
  simp only [Fin.cast_inj] at h
  rw [← h]
  rfl

theorem phase_cancel {z : ℂ} (hzz : z * starRingEnd ℂ z = 1) (u w : ℂ) :
    z * u * (star z * w) = u * w := by
  rw [show star z = starRingEnd ℂ z from rfl]
  linear_combination u * w * hzz

/-- On simple spectrum the fresh projector is the canonical eigenprojector (phases cancel). -/
theorem SimpleSpectrum.freshProjector_eq {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (ℓ : Fin N) :
    freshProjector K ℓ =
      vecMulVec (⇑(hK.1.eigenvectorBasis (increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ))))
        (star ⇑(hK.1.eigenvectorBasis
          (increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ)))) := by
  obtain ⟨z, hz, hsel⟩ := orderedColumnSelection_eq_phase (Fin.cast (Fintype.card_fin N).symm ℓ)
    ⟨K, hK.1⟩ hK.injective_orderedEigenvalue
  unfold freshProjector
  rw [freshEigenvector_eq hK.1, hsel]
  have hzz : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  ext a b
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_mul',
    increasingEigenvector, increasingEigenbasis_apply]
  exact phase_cancel hzz _ _

/-- `U diag(g) U* = Σ_j g_j b_j b_j*` for the Mathlib eigenvector unitary. -/
theorem unitary_diagonal_eq_sum {K : Matrix (Fin N) (Fin N) ℂ} (hK : K.IsHermitian)
    (g : Fin N → ℂ) :
    (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal g *
        star (hK.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) =
      ∑ j, g j • vecMulVec (⇑(hK.eigenvectorBasis j)) (star ⇑(hK.eigenvectorBasis j)) := by
  ext a b
  simp only [mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, star_apply, IsHermitian.eigenvectorUnitary_apply,
    Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Reindexing a sum over Mathlib eigen-indices by the fresh ranks. -/
theorem sum_increasingIndex_cast {M : Type*} [AddCommMonoid M] (g : Fin N → M) :
    ∑ ℓ : Fin N, g (increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ)) = ∑ j, g j :=
  Equiv.sum_comp ((finCongr (Fintype.card_fin N).symm).trans increasingIndex) g

theorem SimpleSpectrum.sum_smul_freshProjector {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) (g : Fin N → ℂ) :
    ∑ ℓ, g (increasingIndex (Fin.cast (Fintype.card_fin N).symm ℓ)) • freshProjector K ℓ =
      (hK.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) * diagonal g *
        star (hK.1.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) := by
  rw [unitary_diagonal_eq_sum hK.1 g]
  simp_rw [hK.freshProjector_eq]
  exact sum_increasingIndex_cast
    (fun j => g j • vecMulVec (⇑(hK.1.eigenvectorBasis j)) (star ⇑(hK.1.eigenvectorBasis j)))

theorem SimpleSpectrum.sum_freshProjector {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : SimpleSpectrum K) : ∑ ℓ, freshProjector K ℓ = 1 := by
  have h := hK.sum_smul_freshProjector (fun _ => 1)
  simp only [one_smul] at h
  rw [h, diagonal_one, mul_one]
  exact Unitary.mul_star_self_of_mem hK.1.eigenvectorUnitary.2

theorem SimpleSpectrum.cfc_eq_sum {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (f : ℝ → ℝ) :
    cfc f K = ∑ ℓ, ((f (freshEigenvalue K ℓ) : ℝ) : ℂ) • freshProjector K ℓ := by
  rw [hK.1.cfc_eq f, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [← hK.sum_smul_freshProjector]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 1
  simp only [Function.comp_apply, eigenvalue_increasingIndex, freshEigenvalue_eq hK.1]
  rfl

theorem SimpleSpectrum.mul_freshProjector {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (ℓ : Fin N) : K * freshProjector K ℓ = ((freshEigenvalue K ℓ : ℝ) : ℂ) • freshProjector K ℓ := by
  unfold freshProjector
  rw [mul_vecMulVec, hK.mulVec_freshEigenvector]
  ext a b
  simp [vecMulVec_apply, mul_assoc]

theorem SimpleSpectrum.inv_eq_sum {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    {z : ℂ} (hz : z.im ≠ 0) :
    (K - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      ∑ ℓ, (((freshEigenvalue K ℓ : ℝ) : ℂ) - z)⁻¹ • freshProjector K ℓ := by
  apply inv_eq_right_inv
  rw [Finset.mul_sum]
  have hne : ∀ ℓ : Fin N, ((freshEigenvalue K ℓ : ℝ) : ℂ) - z ≠ 0 := by
    intro ℓ h
    apply hz
    have := congrArg Complex.im h
    simpa using this.symm
  calc ∑ ℓ, (K - z • (1 : Matrix (Fin N) (Fin N) ℂ)) *
        ((((freshEigenvalue K ℓ : ℝ) : ℂ) - z)⁻¹ • freshProjector K ℓ)
      = ∑ ℓ, freshProjector K ℓ := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Matrix.mul_smul, sub_mul, hK.mul_freshProjector, smul_mul, one_mul, ← sub_smul,
          smul_smul, inv_mul_cancel₀ (hne ℓ), one_smul]
    _ = 1 := hK.sum_freshProjector

/-!
## Almost sure simple spectrum of `F + GUE_N(t)`
-/

open CoareaNative.BlockBand in
/-- Coordinate reconstruction is additive. -/
theorem hermitianMatrixOfCoordinates_add {d : ℕ} (x y : HermitianCoordinate d → ℝ) :
    hermitianMatrixOfCoordinates (x + y) =
      hermitianMatrixOfCoordinates x + hermitianMatrixOfCoordinates y := by
  ext i j
  simp only [hermitianMatrixOfCoordinates, Matrix.add_apply]
  split_ifs <;> simp [hermitianUpperEntry] <;> ring

open CoareaNative.BlockBand BlockBand.Coarea.GUELaw in
theorem ae_simpleSpectrum_add_gue {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ G ∂gueMeasure (Fin N) t, SimpleSpectrum (F + G) := by
  set M : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ :=
    fun x => (hermitianOfFinCoordinates N x).1 with hM
  have hMm : Measurable M := measurable_hermitianOfFinCoordinates_val N
  have hS : MeasurableSet {G : Matrix (Fin N) (Fin N) ℂ | SimpleSpectrum (F + G)} :=
    measurableSet_simpleSpectrum.preimage
      (BlockBand.Coarea.FixedOmega.measurable_matrix_add measurable_const measurable_id)
  rw [gueMeasure_eq_map_withDensity N ht, ae_map_iff hMm.aemeasurable hS]
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  -- coordinates of `F`
  set y : HermitianCoordinateSpace N :=
    coordsOfMatrix F ∘ (hermitianCoordinateEquivFin N).symm with hy
  have hMadd : ∀ x, F + M x = M (x + y) := by
    intro x
    simp only [hM, hermitianOfFinCoordinates, hermitianOfCoordinates]
    have : (x + y) ∘ hermitianCoordinateEquivFin N =
        x ∘ hermitianCoordinateEquivFin N + coordsOfMatrix F := by
      funext k; simp [hy]
    rw [this, hermitianMatrixOfCoordinates_add,
      hermitianMatrixOfCoordinates_coordsOfMatrix hF, add_comm]
  have hgood := ae_hermitianSimpleSpectrumCoordinates N
  have htr : ∀ᵐ x ∂(volume : Measure (HermitianCoordinateSpace N)),
      x + y ∈ hermitianSimpleSpectrumCoordinates N := by
    rw [ae_iff] at hgood ⊢
    have h := measure_preimage_add_right (volume : Measure (HermitianCoordinateSpace N)) y
      {x | ¬ x ∈ hermitianSimpleSpectrumCoordinates N}
    rw [← h] at hgood
    exact hgood
  filter_upwards [htr] with x hx
  rw [hMadd x]
  have hH : (M (x + y)).IsHermitian := (hermitianOfFinCoordinates N (x + y)).2
  have hinj := Model.Construction.orderedEigenvalue_injective_of_separable
    (⟨M (x + y), hH⟩ : Model.Construction.HermitianMatrix (Fin N)) hx
  refine ⟨hH, fun ℓ m h => ?_⟩
  rw [freshEigenvalue_eq hH, freshEigenvalue_eq hH] at h
  exact Fin.cast_injective _ (hinj h)

end BlockBand.Critical.WeightedDensity
