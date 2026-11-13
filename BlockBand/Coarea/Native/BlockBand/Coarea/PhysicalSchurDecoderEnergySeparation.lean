module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurDecoderChangeOfVariables
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalExhaustiveCoareaCoverComplete

/-!
# Deterministic energy separation for the physical Schur decoder

The spectral uniqueness mechanism behind the fixed-rank no-double-counting step of the coarea
theorem: an eigenvalue of a finite Hermitian matrix is determined by the number of ordered
eigenvalues strictly below it.  The proof is multiplicity-safe: no simple-spectrum assumption is
needed for this uniqueness statement.  All statements are finite-dimensional and deterministic.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix Set
open scoped ComplexOrder MatrixOrder InnerProductSpace

/-- Subtracting a real scalar matrix subtracts that scalar from every
increasingly ordered Hermitian eigenvalue. -/
theorem orderedEigenvalue_sub_real_smul_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (E : ℝ)
    (j : Fin (Fintype.card ι)) :
    let hshift : (A.1 - (E : ℂ) • 1).IsHermitian :=
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
    orderedEigenvalue ⟨A.1 - (E : ℂ) • 1, hshift⟩ j =
      orderedEigenvalue A j - E := by
  dsimp only
  let S : HermitianMatrix ι :=
    ⟨A.1 - (E : ℂ) • 1,
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))⟩
  apply le_antisymm
  · apply orderedEigenvalue_contract_of_rayleigh S A E
    intro x hx
    have hone : RCLike.re ⟪(Matrix.toEuclideanLin
        (1 : Matrix ι ι ℂ)) x, x⟫_ℂ = 1 := by
      simp [Matrix.toEuclideanLin_eq_toLin_orthonormal, hx]
    simp only [S, map_sub, LinearMap.sub_apply, map_smul,
      LinearMap.smul_apply, inner_sub_left, inner_smul_left, RCLike.mul_re]
    rw [hone]
    simp
  · have h := orderedEigenvalue_contract_of_rayleigh A S (-E) (fun x hx => by
      have hone : RCLike.re ⟪(Matrix.toEuclideanLin
          (1 : Matrix ι ι ℂ)) x, x⟫_ℂ = 1 := by
        simp [Matrix.toEuclideanLin_eq_toLin_orthonormal, hx]
      simp only [S, map_sub, LinearMap.sub_apply, map_smul,
        LinearMap.smul_apply, inner_sub_left, inner_smul_left, RCLike.mul_re]
      rw [hone]
      simp) j
    dsimp only [S] at h ⊢
    linarith

/-- Shifted strict inertia is the number of eigenvalues of the unshifted
Hermitian matrix strictly below the energy. -/
theorem negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (E : ℝ) :
    let hshift : (A.1 - (E : ℂ) • 1).IsHermitian :=
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
    negativeEigenvalueCount hshift = eigenCount A (Set.Iio E) := by
  dsimp only
  unfold negativeEigenvalueCount eigenCount
  classical
  let e : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
  let S : HermitianMatrix ι :=
    ⟨A.1 - (E : ℂ) • 1,
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))⟩
  have hordered (j : Fin (Fintype.card ι)) :
      orderedEigenvalue S j = orderedEigenvalue A j - E :=
    orderedEigenvalue_sub_real_smul_one A E j
  apply Finset.card_bij (fun i _ => (e i).rev)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have heq : S.property.eigenvalues i =
        orderedEigenvalue S (e i).rev := by
      simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, e]
    rw [heq, hordered] at hi
    change orderedEigenvalue A (e i).rev < E
    linarith
  · intro i _ j _ hij
    exact e.injective (Fin.rev_injective hij)
  · intro j hj
    refine ⟨e.symm j.rev, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have heq : S.property.eigenvalues (e.symm j.rev) =
          orderedEigenvalue S j := by
        simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, e]
      rw [heq, hordered]
      change orderedEigenvalue A j - E < 0
      change orderedEigenvalue A j < E at hj
      linarith
    · simp

/-- The two inertia APIs in the project use the same strict-negative
multiplicity count. -/
theorem inertia_eq_negativeEigenvalueCount
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) :
    inertia A = negativeEigenvalueCount A.property := by
  rw [inertia_def]
  let hzero : A.1.IsHermitian := A.property
  have h :
      negativeEigenvalueCount hzero = eigenCount A (Set.Iio 0) := by
    convert negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio A 0 using 1
    simp
  exact h.symm.trans (negativeEigenvalueCount_proof_irrel hzero A.property)

/-- The coordinate-level `shiftedInertia` used by the concrete pole cover is
the same strict lower spectral count. -/
theorem shiftedInertia_eq_eigenCount_Iio
    (d : ℕ) (R : HermitianCoordinateSpace d) (E : ℝ) :
    shiftedInertia d R E =
      eigenCount (hermitianOfFinCoordinates d R) (Set.Iio E) := by
  rw [shiftedInertia, inertia_eq_negativeEigenvalueCount]
  calc
    negativeEigenvalueCount (shiftedHermitianFinCoordinates d R E).property =
        negativeEigenvalueCount
          ((hermitianOfFinCoordinates d R).property.sub
            (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))) :=
      negativeEigenvalueCount_proof_irrel _ _
    _ = eigenCount (hermitianOfFinCoordinates d R) (Set.Iio E) :=
      negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio _ _

/-- In particular, coordinate shifted inertia agrees with the project's
negative-eigenvalue count of the shifted matrix. -/
theorem shiftedInertia_eq_negativeEigenvalueCount
    (d : ℕ) (R : HermitianCoordinateSpace d) (E : ℝ) :
    let hshift : ((hermitianOfFinCoordinates d R).1 -
        (E : ℂ) • 1).IsHermitian :=
      (hermitianOfFinCoordinates d R).property.sub
        (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
    shiftedInertia d R E = negativeEigenvalueCount hshift := by
  dsimp only
  rw [shiftedInertia_eq_eigenCount_Iio,
    ← negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio]

/-- If `E < E'` and `E` is an eigenvalue, then strictly more ordered
eigenvalues lie below `E'` than below `E`. -/
theorem eigenCount_Iio_lt_of_mem_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {E E' : ℝ} (hEE' : E < E')
    (hE : ∃ j, orderedEigenvalue A j = E) :
    eigenCount A (Set.Iio E) < eigenCount A (Set.Iio E') := by
  classical
  unfold eigenCount
  let s := Finset.univ.filter fun i => orderedEigenvalue A i ∈ Set.Iio E
  let t := Finset.univ.filter fun i => orderedEigenvalue A i ∈ Set.Iio E'
  have hst : s ⊆ t := by
    intro i hi
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_Iio] at hi ⊢
    exact hi.trans hEE'
  rcases hE with ⟨j, hj⟩
  have hjt : j ∈ t := by simp [t, hj, hEE']
  have hjs : j ∉ s := by simp [s, hj]
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hst, fun h => hjs ((congrArg (fun u => j ∈ u) h).mpr hjt)⟩)

/-- A real eigenvalue of a finite Hermitian matrix is uniquely determined by
the number of eigenvalues strictly below it.  Multiplicities cause no issue:
if `E < E'`, one occurrence of `E` witnesses strict growth of the count. -/
theorem eigenvalue_eq_of_eigenCount_Iio_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {E E' : ℝ}
    (hE : ∃ j, orderedEigenvalue A j = E)
    (hE' : ∃ j, orderedEigenvalue A j = E')
    (hcount : eigenCount A (Set.Iio E) = eigenCount A (Set.Iio E')) :
    E = E' := by
  rcases lt_trichotomy E E' with hlt | heq | hgt
  · exact False.elim ((eigenCount_Iio_lt_of_mem_spectrum A hlt hE).ne hcount)
  · exact heq
  · exact False.elim ((eigenCount_Iio_lt_of_mem_spectrum A hgt hE').ne hcount.symm)

/-- Kernel membership for a shifted Hermitian matrix gives membership in the
ordered real spectrum of the unshifted matrix. -/
theorem exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {E : ℝ} {v : ι → ℂ}
    (hv0 : v ≠ 0) (hv : (A.1 - (E : ℂ) • 1) *ᵥ v = 0) :
    ∃ j, orderedEigenvalue A j = E := by
  have hdet : (A.1 - (E : ℂ) • 1).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff (M := A.1 - (E : ℂ) • 1)).mp ⟨v, hv0, hv⟩
  let S : HermitianMatrix ι :=
    ⟨A.1 - (E : ℂ) • 1,
      A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))⟩
  rcases (hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero S).1 hdet with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  rw [orderedEigenvalue_sub_real_smul_one] at hj
  linarith

/-- Deterministic fixed-rank uniqueness for a constant finite Hermitian
matrix: two kernel energies whose shifted pencils have the same negative
index are equal. -/
theorem energy_eq_of_shift_kernel_and_negativeCount_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) {E E' : ℝ}
    {v v' : ι → ℂ} (hv0 : v ≠ 0) (hv0' : v' ≠ 0)
    (hv : (A.1 - (E : ℂ) • 1) *ᵥ v = 0)
    (hv' : (A.1 - (E' : ℂ) • 1) *ᵥ v' = 0)
    (hcount :
      let hE : (A.1 - (E : ℂ) • 1).IsHermitian :=
        A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
      let hE' : (A.1 - (E' : ℂ) • 1).IsHermitian :=
        A.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E'))
      negativeEigenvalueCount hE = negativeEigenvalueCount hE') :
    E = E' := by
  apply eigenvalue_eq_of_eigenCount_Iio_eq A
    (exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero A hv0 hv)
    (exists_orderedEigenvalue_eq_of_shift_mulVec_eq_zero A hv0' hv')
  rw [← negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio A E,
    ← negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio A E']
  exact hcount

/-- Coordinate form of fixed-rank spectral uniqueness.  This is the exact
readback used for both the exterior and complementary inertia terms of
`physicalEigenpairFixedRank`. -/
theorem energy_eq_of_shift_kernel_and_shiftedInertia_eq
    (d : ℕ) (R : HermitianCoordinateSpace d) {E E' : ℝ}
    {v v' : Fin d → ℂ} (hv0 : v ≠ 0) (hv0' : v' ≠ 0)
    (hv : ((hermitianOfFinCoordinates d R).1 - (E : ℂ) • 1) *ᵥ v = 0)
    (hv' : ((hermitianOfFinCoordinates d R).1 - (E' : ℂ) • 1) *ᵥ v' = 0)
    (hcount : shiftedInertia d R E = shiftedInertia d R E') :
    E = E' := by
  apply energy_eq_of_shift_kernel_and_negativeCount_eq
    (hermitianOfFinCoordinates d R) hv0 hv0' hv hv'
  simpa only [← shiftedInertia_eq_negativeEigenvalueCount] using hcount

end CoareaNative.BlockBand
