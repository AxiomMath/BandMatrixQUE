module

public import BlockBand.Coarea.FixedOmegaChart

/-!
# Fixed-`ω` coarea: the chart decoder in global terms

The selected-simple chart decoder, the Schur data and the rank sector of the chart coordinates,
written with the global vector, frame and Schur complement of the coarea formula.

## Main results

* `hermitianOfFinCoordinates_physicalSelectedSimpleDecode`: the decoded matrix of chart `i`
  at incidence coordinates `(E, z, B)` is `E vvᴴ + U B Uᴴ - F(E)` with
  `F(E) = V - Cᴴ(H_R - E)⁻¹C` (`BlockBand.Coarea.physicalCoareaF`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

@[expose] public section
noncomputable section

namespace BlockBand.Coarea.FixedOmega

open Matrix MeasureTheory
open CoareaNative.BlockBand BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal NNReal ComplexConjugate

variable {d : ℕ}

/-!
## The pivot-first reindexing
-/

theorem selectedCoordinateEquiv_zero_succ (n : ℕ) (k : Fin n) :
    selectedCoordinateEquiv (0 : Fin (n + 1)) k.succ = Sum.inr k := by
  simp [selectedCoordinateEquiv, optionEquivUnitSum, finSuccEquiv'_zero, finSuccEquiv_succ]

theorem selectedCoordinateEquiv_zero_of_ne (hd : 1 ≤ d) (a : Fin d) (ha : (a : ℕ) ≠ 0) :
    selectedCoordinateEquiv (⟨0, hd⟩ : Fin d) a = Sum.inr ⟨(a : ℕ) - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨a, haa⟩ := a
  simp only at ha
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have := selectedCoordinateEquiv_zero_succ n ⟨k, by omega⟩
  simpa using this

theorem selectedCoordinateEquiv_zero_of_eq (hd : 1 ≤ d) (a : Fin d) (ha : (a : ℕ) = 0) :
    selectedCoordinateEquiv (⟨0, hd⟩ : Fin d) a = Sum.inl () := by
  have : a = ⟨0, hd⟩ := Fin.ext ha
  subst this
  exact selectedCoordinateEquiv_apply_selected _

/-!
## Global canonical vector and frame
-/

/-- The canonical unit vector of chart `i`, in the original index order. -/
def chartVector (i : Fin d) (z : Fin (d - 1) → ℂ) : Fin d → ℂ :=
  fun a => canonicalProjectiveUnitVector z (selectedCoordinateEquiv i a)

/-- The complementary columns of the phase-fixed Householder frame of chart `i`. -/
def chartFrame (i : Fin d) (z : Fin (d - 1) → ℂ) : Matrix (Fin d) (Fin (d - 1)) ℂ :=
  fun a j => physicalCoareaFrame z (selectedCoordinateEquiv i a) (Sum.inr j)

theorem physicalCoareaFrame_apply_inl (z : Fin (d - 1) → ℂ) (a : Unit ⊕ Fin (d - 1)) :
    physicalCoareaFrame z a (Sum.inl ()) = canonicalProjectiveUnitVector z a := by
  have h := phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector z
  have h2 := congrFun h a
  rw [phaseFixedCoordinateVector, Matrix.mulVec_single_one] at h2
  exact h2

theorem star_chartVector_dotProduct (i : Fin d) (z : Fin (d - 1) → ℂ) :
    star (chartVector i z) ⬝ᵥ chartVector i z = 1 := by
  have h := EuclideanSpace.norm_sq_eq (canonicalProjectiveUnitVector z)
  rw [norm_canonicalProjectiveUnitVector, one_pow] at h
  unfold chartVector
  simp only [dotProduct, Pi.star_apply]
  rw [(selectedCoordinateEquiv i).sum_comp (fun b =>
    star (canonicalProjectiveUnitVector z b) * canonicalProjectiveUnitVector z b)]
  have : ∀ b, star (canonicalProjectiveUnitVector z b) * canonicalProjectiveUnitVector z b =
      ((‖canonicalProjectiveUnitVector z b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [this]
  rw [← Complex.ofReal_sum, ← h, Complex.ofReal_one]

theorem l2Norm_chartVector (i : Fin d) (z : Fin (d - 1) → ℂ) :
    l2Norm (chartVector i z) = 1 := by
  have h := star_chartVector_dotProduct i z
  have h2 := l2Norm_sq_eq_re (chartVector i z)
  rw [h, Complex.one_re] at h2
  have h0 : 0 ≤ l2Norm (chartVector i z) := Real.sqrt_nonneg _
  nlinarith [h2, h0]

theorem isFrameOf_chartFrame (i : Fin d) (z : Fin (d - 1) → ℂ) :
    IsFrameOf (chartVector i z) (chartFrame i z) := by
  have hU := physicalCoareaFrame_unitary (d := d) z
  set e := selectedCoordinateEquiv i
  constructor
  · ext j k
    have h := congrFun (congrFun hU (Sum.inr j)) (Sum.inr k)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    simp only [chartFrame, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e.sum_comp (fun b => star (physicalCoareaFrame z b (Sum.inr j)) *
      physicalCoareaFrame z b (Sum.inr k)), h]
    simp [Matrix.one_apply]
  · funext j
    have h := congrFun (congrFun hU (Sum.inr j)) (Sum.inl ())
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, physicalCoareaFrame_apply_inl] at h
    simp only [chartFrame, chartVector, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
    rw [e.sum_comp (fun b => star (physicalCoareaFrame z b (Sum.inr j)) *
      canonicalProjectiveUnitVector z b), h]
    simp [Matrix.one_apply]

/-- The decoded block-diagonal matrix in the original index order. -/
theorem reindex_frame_conj_fromBlocks (i : Fin d) (z : Fin (d - 1) → ℂ) (E : ℝ)
    (B : Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ) :
    Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
        (physicalCoareaFrame z * Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B *
          (physicalCoareaFrame z)ᴴ) =
      (E : ℂ) • vecMulVec (chartVector i z) (star (chartVector i z)) +
        chartFrame i z * B * (chartFrame i z)ᴴ := by
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    zero_mul, Finset.sum_const_zero, add_zero, zero_add, Matrix.conjTranspose_apply,
    Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, chartVector, chartFrame,
    physicalCoareaFrame_apply_inl, Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Finset.sum_mul]
  have h0 : (default : Unit) = () := rfl
  rw [h0, physicalCoareaFrame_apply_inl, physicalCoareaFrame_apply_inl]
  ring

/-!
## The chart Schur data in global terms
-/

/-- The chart compression is the pivot-first reindexing of the generic `F(E)`. -/
theorem nativePhysicalCoareaF_chart {dR : ℕ} (H_R : Matrix (Fin dR) (Fin dR) ℂ)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) (E : ℝ) :
    CoareaNative.BlockBand.physicalCoareaF H_R (physicalChartCoupling C i)
        (physicalChartPotential V i) E =
      Matrix.reindex (selectedCoordinateEquiv i) (selectedCoordinateEquiv i)
        (BlockBand.Coarea.physicalCoareaF H_R C V E) := by
  ext a b
  simp [CoareaNative.BlockBand.physicalCoareaF, BlockBand.Coarea.physicalCoareaF,
    physicalChartCoupling, physicalChartPotential, CoareaNative.BlockBand.physicalCoareaResolvent,
    BlockBand.Coarea.physicalCoareaResolvent, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem nativeSchurClock_chart {dR : ℕ} (H_R : Matrix (Fin dR) (Fin dR) ℂ)
    (C : Matrix (Fin dR) (Fin d) ℂ) (i : Fin d) (E : ℝ) :
    CoareaNative.BlockBand.schurClock
        (CoareaNative.BlockBand.physicalCoareaT H_R (physicalChartCoupling C i) E) =
      Matrix.reindex (selectedCoordinateEquiv i) (selectedCoordinateEquiv i)
        (BlockBand.Coarea.physicalCoareaD H_R C E) := by
  ext a b
  simp [CoareaNative.BlockBand.schurClock, BlockBand.Coarea.schurClock,
    BlockBand.Coarea.physicalCoareaD, CoareaNative.BlockBand.physicalCoareaT,
    BlockBand.Coarea.physicalCoareaT, physicalChartCoupling,
    CoareaNative.BlockBand.physicalCoareaResolvent, BlockBand.Coarea.physicalCoareaResolvent,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]

/-- The crossing factor is the contract's crossing speed `Re(vᴴ D(E) v)`. -/
theorem physicalEigenpairCrossingQuadratic_eq {dR : ℕ} (H_R : Matrix (Fin dR) (Fin dR) ℂ)
    (C : Matrix (Fin dR) (Fin d) ℂ) (i : Fin d) (E : ℝ) (z : Fin (d - 1) → ℂ) :
    physicalEigenpairCrossingQuadratic
        (CoareaNative.BlockBand.physicalCoareaT H_R (physicalChartCoupling C i) E) z =
      (star (chartVector i z) ⬝ᵥ
        (BlockBand.Coarea.physicalCoareaD H_R C E *ᵥ chartVector i z)).re := by
  unfold physicalEigenpairCrossingQuadratic
  rw [nativeSchurClock_chart]
  congr 1
  set e := selectedCoordinateEquiv i
  set u := canonicalProjectiveUnitVector z
  set D := BlockBand.Coarea.physicalCoareaD H_R C E
  simp only [chartVector, dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply,
    Pi.star_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Selected readback of a Hermitian matrix is its pivot-first un-reindexing. -/
theorem hermitianOfFinCoordinates_selectedMatrixFinCoordinateReadCLM (i : Fin d)
    {M : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ} (hM : M.IsHermitian) :
    (hermitianOfFinCoordinates d (selectedMatrixFinCoordinateReadCLM i M)).1 =
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm M := by
  rw [selectedMatrixFinCoordinateReadCLM_hermitian i ⟨M, hM⟩]
  change ((hermitianFinCoordinatesLinearEquiv d) ((hermitianFinCoordinatesLinearEquiv d).symm
    ((selectedCoordinateEigenpairLinearEquiv i).symm
      (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) ⟨M, hM⟩)))).1 = _
  rw [LinearEquiv.apply_symm_apply]
  change ((selectedCoordinateHermitianLinearEquiv i).symm
    ((eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).symm
      (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) ⟨M, hM⟩))).1 = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- **The decoded matrix** of chart `i` at incidence coordinates `(E, z, B)`:
`E vvᴴ + U B Uᴴ - F(E)`, `v = chartVector i z`, `U = chartFrame i z`. -/
theorem hermitianOfFinCoordinates_physicalSelectedSimpleDecode {dR : ℕ}
    (R : HermitianCoordinateSpace dR) (C : Matrix (Fin dR) (Fin d) ℂ)
    (V : Matrix (Fin d) (Fin d) ℂ) (hV : V.IsHermitian) (i : Fin d)
    (x : HermitianCoordinateSpace d) :
    (hermitianOfFinCoordinates d (physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
        (physicalChartPotential V i) x)).1 =
      ((eigenpairIncidenceCoordinates i x).1 : ℂ) •
          vecMulVec (chartVector i (eigenpairIncidenceCoordinates i x).2.1)
            (star (chartVector i (eigenpairIncidenceCoordinates i x).2.1)) +
        chartFrame i (eigenpairIncidenceCoordinates i x).2.1 *
          (eigenpairIncidenceCoordinates i x).2.2.1 *
          (chartFrame i (eigenpairIncidenceCoordinates i x).2.1)ᴴ -
        BlockBand.Coarea.physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V
          (eigenpairIncidenceCoordinates i x).1 := by
  set y := eigenpairIncidenceCoordinates i x
  set H_R := (hermitianOfFinCoordinates dR R).1
  have hHR : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).2
  have hF' := CoareaNative.BlockBand.physicalCoareaF_isHermitian H_R (physicalChartCoupling C i)
    (physicalChartPotential V i) hHR (physicalChartPotential_isHermitian hV i) y.1
  have hM : ((canonicalEigenpairChartDecode y).1 -
      CoareaNative.BlockBand.physicalCoareaF H_R (physicalChartCoupling C i)
        (physicalChartPotential V i) y.1).IsHermitian :=
    (canonicalEigenpairChartDecode y).2.sub hF'
  change (hermitianOfFinCoordinates d (physicalSchurFinCoordinateDecode i
    (CoareaNative.BlockBand.physicalCoareaF H_R (physicalChartCoupling C i)
      (physicalChartPotential V i)) x)).1 = _
  rw [physicalSchurFinCoordinateDecode_eq_read,
    hermitianOfFinCoordinates_selectedMatrixFinCoordinateReadCLM i hM,
    canonicalEigenpairChartDecode_val, nativePhysicalCoareaF_chart]
  have hsub : ∀ A A' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ,
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm (A - A') =
        Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm A -
          Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm A' := by
    intro A A'; ext a b; simp
  rw [hsub, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
  congr 1
  exact reindex_frame_conj_fromBlocks i y.2.1 y.1 y.2.2.1

/-!
## Projective density and the pivot-`0` affine chart
-/

theorem norm_sq_canonicalReconstruction (z : Fin (d - 1) → ℂ) :
    ‖projectiveEigenvectorReconstruction (Sum.inl () : Unit ⊕ Fin (d - 1))
        (canonicalProjectiveChartCoordinates z)‖ ^ 2 = 1 + ProjectiveHaar.chartSq z := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  simp [projectiveEigenvectorReconstruction, ProjectiveHaar.chartSq, Complex.normSq_eq_norm_sq]

theorem norm_canonicalReconstruction (z : Fin (d - 1) → ℂ) :
    ‖projectiveEigenvectorReconstruction (Sum.inl () : Unit ⊕ Fin (d - 1))
        (canonicalProjectiveChartCoordinates z)‖ = Real.sqrt (1 + ProjectiveHaar.chartSq z) := by
  rw [← norm_sq_canonicalReconstruction, Real.sqrt_sq (norm_nonneg _)]

/-- The affine projective density is `(1 + |z|²)^{-d}`. -/
theorem canonicalProjectiveAffineDensity_eq (hd : 1 ≤ d) (z : Fin (d - 1) → ℂ) :
    canonicalProjectiveAffineDensity (d := d) z = ((1 + ProjectiveHaar.chartSq z) ^ d)⁻¹ := by
  unfold canonicalProjectiveAffineDensity projectiveAffineDensity
  rw [← norm_projectiveEigenvectorReconstruction_sq, norm_sq_canonicalReconstruction, inv_pow]
  congr 2
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

theorem canonicalProjectiveUnitVector_apply (z : Fin (d - 1) → ℂ) (a : Unit ⊕ Fin (d - 1)) :
    canonicalProjectiveUnitVector z a =
      ((Real.sqrt (1 + ProjectiveHaar.chartSq z))⁻¹ : ℂ) *
        projectiveEigenvectorReconstruction (Sum.inl ()) (canonicalProjectiveChartCoordinates z) a := by
  unfold canonicalProjectiveUnitVector projectiveUnitReconstruction
  rw [norm_canonicalReconstruction]
  simp [PiLp.smul_apply, Complex.real_smul]

/-- For the pivot `0`, the chart vector is the normalized affine lift `(1 + |z|²)^{-1/2} (1, z)`. -/
theorem chartVector_zero (hd : 1 ≤ d) (z : Fin (d - 1) → ℂ) :
    chartVector (⟨0, hd⟩ : Fin d) z =
      ((Real.sqrt (1 + ProjectiveHaar.chartSq z))⁻¹ : ℂ) • ProjectiveHaar.affineLift z := by
  funext a
  rw [chartVector, canonicalProjectiveUnitVector_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases ha : (a : ℕ) = 0
  · rw [selectedCoordinateEquiv_zero_of_eq hd a ha]
    simp [projectiveEigenvectorReconstruction, ProjectiveHaar.affineLift, ha]
  · rw [selectedCoordinateEquiv_zero_of_ne hd a ha]
    simp [projectiveEigenvectorReconstruction, ProjectiveHaar.affineLift, ha]

/-!
## The rank sector of the chart
-/

theorem negativeEigenvalueCount_eq_negativeCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian) : negativeEigenvalueCount hM = negativeCount M :=
  (negativeCount_of_isHermitian hM).symm

theorem shiftedInertia_eq_negativeCount (n : ℕ) (x : HermitianCoordinateSpace n) (E : ℝ) :
    shiftedInertia n x E = negativeCount ((hermitianOfFinCoordinates n x).1 - (E : ℂ) • 1) := by
  rw [shiftedInertia_eq_negativeEigenvalueCount, negativeEigenvalueCount_eq_negativeCount]

/-- **The additive rank sector** in contract terms (zero-based rank `α`). -/
theorem physicalEigenpairFixedRank_iff {dR : ℕ} (α : ℕ) (R : HermitianCoordinateSpace dR)
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1))) :
    physicalEigenpairFixedRank α R E B ↔
      negativeCount ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1) +
        negativeCount (B.1 - (E : ℂ) • 1) = α := by
  unfold physicalEigenpairFixedRank coareaRankIndex
  simp only
  rw [shiftedInertia_eq_negativeCount, shiftedInertia_eq_negativeCount]
  have hB : (hermitianOfFinCoordinates (d - 1)
      ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm B)).1 = B.1 :=
    congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv (d - 1)).apply_symm_apply B)
  rw [hB]
  omega

end BlockBand.Coarea.FixedOmega
