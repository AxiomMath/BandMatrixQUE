module

public import BlockBand.DeterminantScore.Sector.Coordinates
public import BlockBand.Model.Construction.OrderedSpectrum

/-!
# Regularity of the negative count off the determinant locus

The negative eigenvalue count `N_-` of a continuous Hermitian family is locally constant at points
where the determinant does not vanish and is Borel measurable; consequently the sector
`{x : N_-(K + G(x)) = ℓ}` is measurable and locally constant off `{det(K + G(x)) = 0}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open Matrix Filter MeasureTheory
open scoped Topology
open BlockBand.Model.Construction (HermitianMatrix orderedEigenvalue
  continuous_orderedEigenvalue)
open BlockBand.Internal.Contracts

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's eigenvalue `k` is an ordered eigenvalue at a fixed (matrix-independent) rank. -/
theorem eigenvalues_eq_orderedEigenvalue {B : Matrix n n ℂ} (hB : B.IsHermitian) (k : n) :
    hB.eigenvalues k = orderedEigenvalue ⟨B, hB⟩
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm k).rev := by
  simp [Matrix.IsHermitian.eigenvalues, orderedEigenvalue,
    BlockBand.Foundations.Spectral.increasingEigenvalue]

theorem continuous_eigenvalues_comp {X : Type*} [TopologicalSpace X] (f : X → Matrix n n ℂ)
    (hf : Continuous f) (hH : ∀ y, (f y).IsHermitian) (k : n) :
    Continuous fun y => (hH y).eigenvalues k := by
  simp_rw [eigenvalues_eq_orderedEigenvalue]
  exact (continuous_orderedEigenvalue _).comp (hf.subtype_mk hH)

theorem negativeCount_eq_card {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    CoareaPalm.negativeCount B = (Finset.univ.filter fun k => hB.eigenvalues k < 0).card := by
  classical
  simp only [CoareaPalm.negativeCount, hB, dite_true]

theorem negativeCount_eq_sum {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    CoareaPalm.negativeCount B = ∑ k, if hB.eigenvalues k < 0 then 1 else 0 := by
  rw [negativeCount_eq_card hB, Finset.card_filter]

theorem eigenvalues_ne_zero_of_det_ne_zero {B : Matrix n n ℂ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) (k : n) : hB.eigenvalues k ≠ 0 := by
  intro hk
  apply hdet
  rw [hB.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- Local constancy of the negative count at a nonsingular point of a continuous Hermitian
family. -/
theorem eventually_negativeCount_eq {X : Type*} [TopologicalSpace X] (f : X → Matrix n n ℂ)
    (hf : Continuous f) (hH : ∀ y, (f y).IsHermitian) {x : X} (hdet : (f x).det ≠ 0) :
    ∀ᶠ y in 𝓝 x, CoareaPalm.negativeCount (f y) = CoareaPalm.negativeCount (f x) := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ k,
      ((hH y).eigenvalues k < 0 ↔ (hH x).eigenvalues k < 0) := by
    rw [eventually_all]
    intro k
    have hc := (continuous_eigenvalues_comp f hf hH k).continuousAt (x := x)
    have hne := eigenvalues_ne_zero_of_det_ne_zero (hH x) hdet k
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact (hc.eventually (isOpen_Iio.mem_nhds hneg)).mono fun _ hy => iff_of_true hy hneg
    · exact (hc.eventually (isOpen_Ioi.mem_nhds hpos)).mono fun _ hy =>
        iff_of_false (not_lt_of_gt hy) (not_lt_of_gt hpos)
  filter_upwards [hall] with y hy
  rw [negativeCount_eq_card (hH y), negativeCount_eq_card (hH x)]
  congr 1
  exact Finset.filter_congr fun k _ => hy k

/-- The negative count along a continuous Hermitian family is Borel measurable. -/
theorem measurable_negativeCount_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (f : X → Matrix n n ℂ) (hf : Continuous f)
    (hH : ∀ y, (f y).IsHermitian) :
    Measurable fun y => CoareaPalm.negativeCount (f y) := by
  have h : (fun y => CoareaPalm.negativeCount (f y)) =
      fun y => ∑ k, if (hH y).eigenvalues k < 0 then 1 else 0 := by
    funext y
    exact negativeCount_eq_sum (hH y)
  rw [h]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite
    (measurableSet_lt (continuous_eigenvalues_comp f hf hH k).measurable measurable_const)
    measurable_const measurable_const

/-!
## The sector of `K + G(x)`
-/

variable {m : ℕ}

theorem isHermitian_add_hermOfCoord {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (x : HermCoord m → ℝ) : (K + hermOfCoord x).IsHermitian :=
  hK.add (isHermitian_hermOfCoord x)

theorem continuous_add_hermOfCoord (K : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun x : HermCoord m → ℝ => K + hermOfCoord x :=
  continuous_const.add continuous_hermOfCoord

theorem measurableSet_inSector {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ) :
    MeasurableSet {x : HermCoord m → ℝ | InSector K ℓ x} :=
  (measurableSet_singleton ℓ).preimage
    (measurable_negativeCount_comp _ (continuous_add_hermOfCoord K)
      (isHermitian_add_hermOfCoord hK))

theorem eventually_inSector_iff {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) (ℓ : ℕ)
    {x : HermCoord m → ℝ} (hdet : (K + hermOfCoord x).det ≠ 0) :
    ∀ᶠ y in 𝓝 x, (InSector K ℓ y ↔ InSector K ℓ x) := by
  filter_upwards [eventually_negativeCount_eq _ (continuous_add_hermOfCoord K)
    (isHermitian_add_hermOfCoord hK) hdet] with y hy
  simp only [InSector, hy]

end BlockBand.DeterminantScore.Sector
