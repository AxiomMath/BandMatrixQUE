module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurDecoderEnergySeparation
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.SylvesterCongruence

/-!
# Selected-simple physical Schur coarea cover

The chart source `selectedOrderedEigenpairChartSource` of the physical coarea cover is the
image of the least-entry chart region of the *globally simple* spectrum locus.  This file
replaces it, for the direct physical
Schur decoder `G_i(E,z,B) = Decode_i(E,z,B) - (V - Cᴴ(H_R-E)⁻¹C)`, by the source
`physicalSelectedSimpleSource α R i`, which only requires

* the selected gap `det (E I - B) ≠ 0`,
* the fixed additive rank `N_R(E) + N_-(B-E) + 1 = α + 1`, and
* exterior pole avoidance `(R,E) ∈ coareaExteriorPoleFree`.

Main results:

* `injOn_physicalSchurFinCoordinateDecode_selectedSimple`: `G_i` is injective on the
  new source.  Energies are separated by the Haynsworth inertia identity of the full
  block matrix (`physicalSchur_energy_eq_of_count_eq`), multiplicity-safe; the
  selected gap then determines `(z,B)` (`canonicalEigenpairChartDecode_injective_of_gap`).
* `measurableSet_physicalSelectedSimpleSource`, measurable images, and the exact
  chart formula `lintegral_image_physicalSelectedSimpleDecode` with Jacobian
  `canonicalProjectiveAffineDensity z * |det (E I - B)|² * vᴴ 𝒟(E) v`.
* `mem_physicalSelectedSimpleDecode_image_iff`: the exact image of every chart, in
  intrinsic terms (pole-free energy, eigenvector with nonzero pivot, one-dimensional
  eigenspace, additive rank).
* `iUnion_physicalSelectedSimpleImage_eq_goodSet` and
  `lintegral_physicalSelectedSimpleGoodSet`: for chart-consistent physical data
  (`physicalChartCoupling`, `physicalChartPotential`), the deterministically
  disjointized charts form a finite measurable partition of the chart-free good set
  `physicalSelectedSimpleGoodSet`, with the exact finite-sum coarea formula.

Setting: the coarea theorem with fixed exterior data, its pole-interval and projective-chart
decomposition, and no double counting.  Normalization: ranks are zero-based in Lean; the
one-based rank of the paper is `α + 1`.  All sizes, the
exterior coordinates `R`, the coupling `C` and the potential `V` are fixed; there are
no asymptotic parameters and no limits.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped ENNReal ComplexOrder

section CanonicalDecode

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The phase-fixed frame of the canonical decoder. -/
abbrev canonicalEigenpairFrame (z : n → ℂ) :
    Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
  phaseFixedHouseholderFrame (Sum.inl Unit.unit) (canonicalProjectiveUnitVector z)

/-- The canonical phase-fixed frame is unitary (left inverse). -/
theorem canonicalEigenpairFrame_conjTranspose_mul (z : n → ℂ) :
    (canonicalEigenpairFrame z)ᴴ * canonicalEigenpairFrame z = 1 := by
  apply phaseFixedHouseholderFrame_unitary
  · exact norm_canonicalProjectiveUnitVector z
  · apply Complex.ext
    · rfl
    · rw [canonicalProjectiveUnitVector_selected]
      simp
  · exact canonicalProjectiveUnitVector_selected_re_pos z

/-- The canonical phase-fixed frame is unitary (right inverse). -/
theorem canonicalEigenpairFrame_mul_conjTranspose (z : n → ℂ) :
    canonicalEigenpairFrame z * (canonicalEigenpairFrame z)ᴴ = 1 :=
  mul_eq_one_comm.mp (canonicalEigenpairFrame_conjTranspose_mul z)

/-- The canonical decoder is conjugation of the block-diagonal matrix
`diag(E, B)` by the phase-fixed frame. -/
theorem canonicalEigenpairChartDecode_val
    (y : EigenpairHermitianBlockCoordinates n) :
    (canonicalEigenpairChartDecode y).1 =
      canonicalEigenpairFrame y.2.1 * eigenpairCanonicalMatrix y.1 y.2.2.1 *
        (canonicalEigenpairFrame y.2.1)ᴴ := by
  change canonicalEigenpairFrame y.2.1 *
      ((eigenpairHermitianBlockLinearEquiv n).symm (y.1, ((0 : n → ℂ), y.2.2))).1 *
        (canonicalEigenpairFrame y.2.1)ᴴ = _
  congr 2
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [eigenpairHermitianBlockLinearEquiv_symm_apply,
      decodeEigenpairHermitianBlocks, eigenpairCanonicalMatrix,
      eigenpairTangentColumn]

/-- The block-diagonal matrix is recovered from the canonical decoder by
conjugating back with the unitary phase-fixed frame. -/
theorem eigenpairCanonicalMatrix_eq_frame_conj
    (y : EigenpairHermitianBlockCoordinates n) :
    eigenpairCanonicalMatrix y.1 y.2.2.1 =
      (canonicalEigenpairFrame y.2.1)ᴴ * (canonicalEigenpairChartDecode y).1 *
        canonicalEigenpairFrame y.2.1 := by
  rw [canonicalEigenpairChartDecode_val]
  have h1 := canonicalEigenpairFrame_conjTranspose_mul y.2.1
  calc eigenpairCanonicalMatrix y.1 y.2.2.1 =
        ((canonicalEigenpairFrame y.2.1)ᴴ * canonicalEigenpairFrame y.2.1) *
          eigenpairCanonicalMatrix y.1 y.2.2.1 *
          ((canonicalEigenpairFrame y.2.1)ᴴ * canonicalEigenpairFrame y.2.1) := by
        rw [h1, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- With nonzero selected gap determinant, every eigenvector of the decoded
matrix at the selected energy is a scalar multiple of the decoded phase-fixed
unit vector.  No simplicity of the remaining spectrum is used. -/
theorem canonicalEigenpairChartDecode_eigenvector_eq_smul
    (y : EigenpairHermitianBlockCoordinates n)
    (hgap : (eigenpairGapMatrix y.1 y.2.2.1).det ≠ 0)
    (u : Unit ⊕ n → ℂ)
    (hu : (canonicalEigenpairChartDecode y).1 *ᵥ u = (y.1 : ℂ) • u) :
    ∃ c : ℂ, u = c • ⇑(canonicalProjectiveUnitVector y.2.1) := by
  set H := canonicalEigenpairFrame y.2.1 with hHdef
  set D := (canonicalEigenpairChartDecode y).1 with hDdef
  set w : Unit ⊕ n → ℂ := Hᴴ *ᵥ u with hwdef
  have hHH : H * Hᴴ = 1 := canonicalEigenpairFrame_mul_conjTranspose y.2.1
  have huw : u = H *ᵥ w := by
    rw [hwdef, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hw : eigenpairCanonicalMatrix y.1 y.2.2.1 *ᵥ w = (y.1 : ℂ) • w := by
    rw [eigenpairCanonicalMatrix_eq_frame_conj, ← hHdef, ← hDdef]
    calc (Hᴴ * D * H) *ᵥ w = Hᴴ *ᵥ (D *ᵥ (H *ᵥ w)) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Hᴴ *ᵥ (D *ᵥ u) := by rw [← huw]
      _ = (y.1 : ℂ) • w := by rw [hu, Matrix.mulVec_smul]
  have hker : eigenpairGapMatrix y.1 y.2.2.1 *ᵥ (fun a => w (Sum.inr a)) = 0 := by
    funext a
    have h := congrFun hw (Sum.inr a)
    simp only [eigenpairCanonicalMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
      Pi.smul_apply, smul_eq_mul] at h
    simp only [eigenpairGapMatrix, Matrix.mulVec, dotProduct, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Pi.zero_apply]
    rw [h]
    ring
  have hlow : (fun a => w (Sum.inr a)) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hgap hker
  set c := w (Sum.inl Unit.unit) with hcdef
  refine ⟨c, ?_⟩
  have hwe : w = c • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
    funext a
    rcases a with t | a
    · cases t
      simp [phaseFixedCoordinateVector, hcdef]
    · have := congrFun hlow a
      simp [phaseFixedCoordinateVector, this]
  rw [huw, hwe, Matrix.mulVec_smul, hHdef,
    phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector]

/-- Equality of phase-fixed vectors up to a scalar forces equality of affine
projective coordinates. -/
theorem eq_of_canonicalProjectiveUnitVector_eq_smul
    {z z' : n → ℂ} {c : ℂ}
    (h : ⇑(canonicalProjectiveUnitVector z') = c • ⇑(canonicalProjectiveUnitVector z)) :
    z' = z := by
  have hc : c ≠ 0 := by
    rintro rfl
    have h1 := congrFun h (Sum.inl Unit.unit)
    have h2 := canonicalProjectiveUnitVector_selected_re_pos z'
    simp only [zero_smul, Pi.zero_apply] at h1
    rw [h1] at h2
    simp at h2
  have hv : canonicalProjectiveUnitVector z' = c • canonicalProjectiveUnitVector z := by
    apply PiLp.ext
    intro a
    simpa using congrFun h a
  have hchart := congrArg (projectiveEigenvectorChart (Sum.inl Unit.unit)) hv
  rw [projectiveEigenvectorChart_smul _ c hc] at hchart
  have hc' : canonicalProjectiveChartCoordinates z' = canonicalProjectiveChartCoordinates z := by
    simpa [canonicalProjectiveUnitVector] using hchart
  funext j
  simpa using congrFun hc' ⟨Sum.inr j, by simp⟩

/-- **Fixed-energy injectivity of the canonical decoder.**  If two block
coordinates have the same selected energy and the same decoded matrix, and the
first has nonzero selected gap determinant `det (E I - B) ≠ 0`, then they are
equal.  Only the selected gap is used; the complementary block `B` may have
repeated eigenvalues. -/
theorem canonicalEigenpairChartDecode_injective_of_gap
    {y y' : EigenpairHermitianBlockCoordinates n}
    (hE : y.1 = y'.1)
    (hgap : (eigenpairGapMatrix y.1 y.2.2.1).det ≠ 0)
    (h : (canonicalEigenpairChartDecode y).1 = (canonicalEigenpairChartDecode y').1) :
    y = y' := by
  have hu := canonicalEigenpairChartDecode_mulVec_unitVector y'
  rw [← h, ← hE] at hu
  obtain ⟨c, hc⟩ := canonicalEigenpairChartDecode_eigenvector_eq_smul y hgap _ hu
  have hz : y'.2.1 = y.2.1 := eq_of_canonicalProjectiveUnitVector_eq_smul hc
  have hcanon : eigenpairCanonicalMatrix y.1 y.2.2.1 =
      eigenpairCanonicalMatrix y'.1 y'.2.2.1 := by
    rw [eigenpairCanonicalMatrix_eq_frame_conj y, eigenpairCanonicalMatrix_eq_frame_conj y', h,
      hz]
  have hB : y.2.2 = y'.2.2 := by
    apply Subtype.ext
    ext a b
    have := congrFun (congrFun hcanon (Sum.inr a)) (Sum.inr b)
    simpa [eigenpairCanonicalMatrix] using this
  obtain ⟨E, z, B⟩ := y
  obtain ⟨E', z', B'⟩ := y'
  simp only at hE hz hB
  subst hE hz hB
  rfl

end CanonicalDecode

section SpectralSeparation

/-- Negative counts only depend on the underlying matrix. -/
theorem negativeEigenvalueCount_congr_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    negativeEigenvalueCount hA = negativeEigenvalueCount hB := by
  subst h
  exact negativeEigenvalueCount_proof_irrel hA hB

/-- The zero Hermitian matrix has no negative eigenvalue. -/
theorem negativeEigenvalueCount_zero_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : (0 : Matrix ι ι ℂ).IsHermitian) :
    negativeEigenvalueCount h = 0 :=
  (negativeEigenvalueCount_eq_zero_iff h).2 Matrix.PosSemidef.zero

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Shifting the canonical decoded matrix by its selected energy leaves exactly
the strict negative inertia of `B - E`: the selected eigenvalue contributes the
zero eigenvalue only. -/
theorem negativeEigenvalueCount_canonicalDecode_sub
    (y : EigenpairHermitianBlockCoordinates n)
    (h1 : ((canonicalEigenpairChartDecode y).1 - (y.1 : ℂ) • 1).IsHermitian)
    (h2 : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian) :
    negativeEigenvalueCount h1 = negativeEigenvalueCount h2 := by
  set H := canonicalEigenpairFrame y.2.1 with hHdef
  have hHH : H * Hᴴ = 1 := canonicalEigenpairFrame_mul_conjTranspose y.2.1
  have hHH' : Hᴴ * H = 1 := canonicalEigenpairFrame_conjTranspose_mul y.2.1
  let A0 : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ :=
    Matrix.fromBlocks 0 0 0 (y.2.2.1 - (y.1 : ℂ) • 1)
  have hblock : eigenpairCanonicalMatrix y.1 y.2.2.1 - (y.1 : ℂ) • 1 = A0 := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [A0, eigenpairCanonicalMatrix, Matrix.one_apply]
  have hconj : (canonicalEigenpairChartDecode y).1 - (y.1 : ℂ) • 1 =
      (Hᴴ)ᴴ * A0 * Hᴴ := by
    rw [Matrix.conjTranspose_conjTranspose, ← hblock, canonicalEigenpairChartDecode_val,
      ← hHdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hHH]
  have hA0 : A0.IsHermitian := by
    have hz : (0 : Matrix Unit Unit ℂ).IsHermitian := Matrix.isHermitian_zero
    rw [Matrix.isHermitian_fromBlocks_iff]
    exact ⟨hz, Matrix.conjTranspose_zero, Matrix.conjTranspose_zero, h2⟩
  have hU : IsUnit Hᴴ := ⟨⟨Hᴴ, H, hHH', hHH⟩, rfl⟩
  rw [negativeEigenvalueCount_congr_eq hconj h1
      (Matrix.isHermitian_conjTranspose_mul_mul Hᴴ hA0),
    negativeEigenvalueCount_congruence hA0 hU]
  have hsplit := negativeEigenvalueCount_fromBlocks_zero
    (Matrix.isHermitian_zero : (0 : Matrix Unit Unit ℂ).IsHermitian) h2
  exact (negativeEigenvalueCount_proof_irrel _ _).trans
    (hsplit.trans (by rw [negativeEigenvalueCount_zero_matrix, zero_add]))

/-- The selected energy is an eigenvalue of the canonical decoded matrix. -/
theorem det_canonicalDecode_sub_eq_zero
    (y : EigenpairHermitianBlockCoordinates n) :
    ((canonicalEigenpairChartDecode y).1 - (y.1 : ℂ) • 1).det = 0 := by
  apply (Matrix.exists_mulVec_eq_zero_iff).mp
  refine ⟨⇑(canonicalProjectiveUnitVector y.2.1), ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 (Sum.inl Unit.unit)
    have h2 := canonicalProjectiveUnitVector_selected_re_pos y.2.1
    simp only [Pi.zero_apply] at h1
    rw [show (canonicalProjectiveUnitVector y.2.1) (Sum.inl Unit.unit) = 0 from h1] at h2
    simp at h2
  · rw [Matrix.sub_mulVec, canonicalEigenpairChartDecode_mulVec_unitVector,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

end SpectralSeparation

section PhysicalSeparation

variable {d r : ℕ}

/-- The full physical block matrix `[[A₀, Cᴴ], [C, H_R]]` with reduced block
`A₀ = K + V`, retained coordinates first and exterior coordinates second. -/
def selectedSimplePhysicalSchurFullMatrix (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (A0 : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Matrix ((Unit ⊕ Fin (d - 1)) ⊕ Fin r) ((Unit ⊕ Fin (d - 1)) ⊕ Fin r) ℂ :=
  Matrix.fromBlocks A0 Cᴴ C H_R

/-- The full physical block matrix is Hermitian. -/
theorem selectedSimplePhysicalSchurFullMatrix_isHermitian {H_R : Matrix (Fin r) (Fin r) ℂ}
    (hH : H_R.IsHermitian) (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    {A0 : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ}
    (hA0 : A0.IsHermitian) :
    (selectedSimplePhysicalSchurFullMatrix H_R C A0).IsHermitian :=
  Matrix.isHermitian_fromBlocks_iff.mpr
    ⟨hA0, Matrix.conjTranspose_conjTranspose C, rfl, hH⟩

/-- **Haynsworth readback at a decoded physical crossing.**  If the reduced block
`A₀` satisfies `Decode(E,z,B) = A₀ - Cᴴ(H_R-E)⁻¹C` at a pole-free energy `E`,
then the number of eigenvalues of the full block matrix strictly below `E` is
`N₋(B-E) + N₋(H_R-E)`, and `E` is an eigenvalue of the full block matrix.
All counts are with multiplicity; no simplicity of any spectrum is assumed. -/
theorem selectedSimplePhysicalSchurFullMatrix_eigenCount_and_mem
    {H_R : Matrix (Fin r) (Fin r) ℂ} (hH : H_R.IsHermitian)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    {A0 : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ}
    (hA0 : A0.IsHermitian)
    (y : EigenpairHermitianBlockCoordinates (Fin (d - 1)))
    (hpole : (H_R - (y.1 : ℂ) • 1).det ≠ 0)
    (hdec : (canonicalEigenpairChartDecode y).1 =
      A0 - Cᴴ * physicalCoareaResolvent H_R y.1 * C)
    (hB : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian)
    (hHE : (H_R - (y.1 : ℂ) • 1).IsHermitian) :
    eigenCount (⟨selectedSimplePhysicalSchurFullMatrix H_R C A0,
        selectedSimplePhysicalSchurFullMatrix_isHermitian hH C hA0⟩ :
          HermitianMatrix ((Unit ⊕ Fin (d - 1)) ⊕ Fin r)) (Set.Iio y.1) =
      negativeEigenvalueCount hB + negativeEigenvalueCount hHE ∧
    ∃ j, orderedEigenvalue (⟨selectedSimplePhysicalSchurFullMatrix H_R C A0,
        selectedSimplePhysicalSchurFullMatrix_isHermitian hH C hA0⟩ :
          HermitianMatrix ((Unit ⊕ Fin (d - 1)) ⊕ Fin r)) j = y.1 := by
  set E := y.1 with hEdef
  let Full : HermitianMatrix ((Unit ⊕ Fin (d - 1)) ⊕ Fin r) :=
    ⟨selectedSimplePhysicalSchurFullMatrix H_R C A0, selectedSimplePhysicalSchurFullMatrix_isHermitian hH C hA0⟩
  let _ : Invertible (H_R - (E : ℂ) • 1) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hpole)
  have hshift : Full.1 - (E : ℂ) • 1 =
      Matrix.fromBlocks (A0 - (E : ℂ) • 1) Cᴴ (Cᴴ)ᴴ (H_R - (E : ℂ) • 1) := by
    rw [Matrix.conjTranspose_conjTranspose]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Full, selectedSimplePhysicalSchurFullMatrix, Matrix.one_apply]
  have hSchur : A0 - (E : ℂ) • 1 - Cᴴ * ⅟(H_R - (E : ℂ) • 1) * (Cᴴ)ᴴ =
      (canonicalEigenpairChartDecode y).1 - (E : ℂ) • 1 := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.conjTranspose_conjTranspose, hdec,
      physicalCoareaResolvent]
    abel
  have hA0E : (A0 - (E : ℂ) • 1).IsHermitian :=
    hA0.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hFullE : (Full.1 - (E : ℂ) • 1).IsHermitian :=
    Full.property.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hdecE : ((canonicalEigenpairChartDecode y).1 - (E : ℂ) • 1).IsHermitian :=
    (canonicalEigenpairChartDecode y).2.sub
      (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  have hsplit := negativeEigenvalueCount_hermitianSchur (A0 - (E : ℂ) • 1) Cᴴ
    (H_R - (E : ℂ) • 1) hA0E hHE
  simp only at hsplit
  constructor
  · have hc := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio Full E
    simp only at hc
    change eigenCount Full (Set.Iio E) = _
    rw [← hc, negativeEigenvalueCount_congr_eq hshift _
      (Matrix.isHermitian_fromBlocks_iff.mpr
        ⟨hA0E, rfl, Matrix.conjTranspose_conjTranspose _, hHE⟩), hsplit,
      negativeEigenvalueCount_congr_eq hSchur _ hdecE,
      negativeEigenvalueCount_canonicalDecode_sub y hdecE hB]
  · have hdet : (Full.1 - (E : ℂ) • 1).det = 0 := by
      rw [hshift, Matrix.det_fromBlocks₂₂, hSchur, det_canonicalDecode_sub_eq_zero,
        mul_zero]
    obtain ⟨j, hj⟩ := (hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero
      (⟨Full.1 - (E : ℂ) • 1, hFullE⟩ :
        HermitianMatrix ((Unit ⊕ Fin (d - 1)) ⊕ Fin r))).1 hdet
    refine ⟨j, ?_⟩
    have h := orderedEigenvalue_sub_real_smul_one Full E j
    simp only at h
    change orderedEigenvalue Full j = E
    rw [h] at hj
    linarith

/-- **Deterministic energy separation from the additive rank.**  Two decoded
crossings sharing the same reduced block `A₀`, both at pole-free energies and
with equal additive strict inertia `N₋(B-E) + N₋(H_R-E)`, have the same
energy.  This is the fixed-rank no-double-counting step of the coarea theorem,
proved without any simple-spectrum hypothesis. -/
theorem physicalSchur_energy_eq_of_count_eq
    {H_R : Matrix (Fin r) (Fin r) ℂ} (hH : H_R.IsHermitian)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    {A0 : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ}
    (hA0 : A0.IsHermitian)
    {y y' : EigenpairHermitianBlockCoordinates (Fin (d - 1))}
    (hpole : (H_R - (y.1 : ℂ) • 1).det ≠ 0)
    (hpole' : (H_R - (y'.1 : ℂ) • 1).det ≠ 0)
    (hdec : (canonicalEigenpairChartDecode y).1 =
      A0 - Cᴴ * physicalCoareaResolvent H_R y.1 * C)
    (hdec' : (canonicalEigenpairChartDecode y').1 =
      A0 - Cᴴ * physicalCoareaResolvent H_R y'.1 * C)
    (hB : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian)
    (hHE : (H_R - (y.1 : ℂ) • 1).IsHermitian)
    (hB' : (y'.2.2.1 - (y'.1 : ℂ) • 1).IsHermitian)
    (hHE' : (H_R - (y'.1 : ℂ) • 1).IsHermitian)
    (hcount : negativeEigenvalueCount hB + negativeEigenvalueCount hHE =
      negativeEigenvalueCount hB' + negativeEigenvalueCount hHE') :
    y.1 = y'.1 := by
  obtain ⟨hc, hm⟩ :=
    selectedSimplePhysicalSchurFullMatrix_eigenCount_and_mem hH C hA0 y hpole hdec hB hHE
  obtain ⟨hc', hm'⟩ :=
    selectedSimplePhysicalSchurFullMatrix_eigenCount_and_mem hH C hA0 y' hpole' hdec' hB' hHE'
  exact eigenvalue_eq_of_eigenCount_Iio_eq _ hm hm' (by rw [hc, hc', hcount])

end PhysicalSeparation

section FiniteChart

variable {d : ℕ}

/-- Selected finite-coordinate readback of a Hermitian matrix is the inverse
block-coordinate equivalence applied to its block encoding. -/
theorem selectedMatrixFinCoordinateReadCLM_hermitian (i : Fin d)
    (M : RealHermitianMatrix (Unit ⊕ Fin (d - 1))) :
    selectedMatrixFinCoordinateReadCLM i M.1 =
      (selectedEigenpairFinCoordinateLinearEquiv i).symm
        (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M) := by
  have h := selectedMatrixFinCoordinateRead_decode i
    (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- Selected readback is injective on Hermitian matrices. -/
theorem selectedMatrixFinCoordinateReadCLM_injective_hermitian (i : Fin d)
    {M M' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ}
    (hM : M.IsHermitian) (hM' : M'.IsHermitian)
    (h : selectedMatrixFinCoordinateReadCLM i M = selectedMatrixFinCoordinateReadCLM i M') :
    M = M' := by
  have h1 := selectedMatrixFinCoordinateReadCLM_hermitian i ⟨M, hM⟩
  have h2 := selectedMatrixFinCoordinateReadCLM_hermitian i ⟨M', hM'⟩
  simp only at h1 h2
  rw [h1, h2] at h
  have := (eigenpairHermitianBlockLinearEquiv (Fin (d - 1))).injective
    ((selectedEigenpairFinCoordinateLinearEquiv i).symm.injective h)
  exact congrArg Subtype.val this

/-- The direct physical decoder is the selected readback of
`Decode(E,z,B) - F(E)`. -/
theorem physicalSchurFinCoordinateDecode_eq_read (i : Fin d)
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : HermitianCoordinateSpace d) :
    physicalSchurFinCoordinateDecode i F x =
      selectedMatrixFinCoordinateReadCLM i
        ((canonicalEigenpairChartDecode (eigenpairIncidenceCoordinates i x)).1 -
          F (eigenpairIncidenceCoordinates i x).1) := by
  rw [physicalSchurFinCoordinateDecode_eq, map_sub,
    selectedEigenpairFinCoordinateChartDecode_eq_read]
  rfl

end FiniteChart

section SelectedSimpleSource

variable {dR d : ℕ}

/-- Exterior pole avoidance in ordered-spectrum form gives an invertible
exterior pencil. -/
theorem det_exterior_sub_ne_zero_of_poleFree
    {R : HermitianCoordinateSpace dR} {E : ℝ}
    (h : (R, E) ∈ coareaExteriorPoleFree dR) :
    ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1).det ≠ 0 := by
  intro hdet
  have hsh : ((hermitianOfFinCoordinates dR R).1 - (E : ℂ) • 1).IsHermitian :=
    (hermitianOfFinCoordinates dR R).property.sub
      (Matrix.isHermitian_one.smul (RCLike.conj_ofReal E))
  obtain ⟨j, hj⟩ := (hermitian_det_eq_zero_iff_exists_orderedEigenvalue_eq_zero
    (⟨_, hsh⟩ : HermitianMatrix (Fin dR))).1 hdet
  have hsub := orderedEigenvalue_sub_real_smul_one (hermitianOfFinCoordinates dR R) E j
  simp only at hsub
  rw [hsub] at hj
  exact h j (by linarith)

/-- The complementary shifted inertia read from finite coordinates is the strict
negative count of `B - E`. -/
theorem shiftedInertia_complement_eq_negativeEigenvalueCount
    (E : ℝ) (B : RealHermitianMatrix (Fin (d - 1)))
    (hB : (B.1 - (E : ℂ) • 1).IsHermitian) :
    shiftedInertia (d - 1) ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm B) E =
      negativeEigenvalueCount hB := by
  rw [shiftedInertia_eq_negativeEigenvalueCount]
  apply negativeEigenvalueCount_congr_eq
  have hval : (hermitianOfFinCoordinates (d - 1)
      ((hermitianFinCoordinatesLinearEquiv (d - 1)).symm B)).1 = B.1 :=
    congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv (d - 1)).apply_symm_apply B)
  rw [hval]

/-- **Selected-simple physical chart source.**  For chart pivot `i`, the
source consists of the finite Hermitian coordinates whose incidence block data
`(E,z,B)` satisfy only

* the selected gap condition `det (E I - B) ≠ 0`,
* the fixed additive rank `N_R(E) + N_-(B-E) + 1 = α + 1`
  (`physicalEigenpairFixedRank`, one-based rank), and
* exterior pole avoidance `(R,E) ∈ coareaExteriorPoleFree`.

No global simple-spectrum condition on the decoded matrix and no least-entry
chart selection is imposed.  Exterior data `R` and sizes are
fixed; no limits. -/
def physicalSelectedSimpleSource (α : ℕ) (R : HermitianCoordinateSpace dR)
    (i : Fin d) : Set (HermitianCoordinateSpace d) :=
  {x | (eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0 ∧
      physicalEigenpairFixedRank α R (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2 ∧
      (R, (eigenpairIncidenceCoordinates i x).1) ∈ coareaExteriorPoleFree dR}

/-- **Injectivity of the direct physical Schur decoder on the selected-simple
source.**  With exterior block `H_R = hermitianOfFinCoordinates R`, arbitrary
coupling `C` and Hermitian `V`, the decoder
`(E,z,B) ↦ Decode(E,z,B) - (V - Cᴴ(H_R-E)⁻¹C)` is injective on
`physicalSelectedSimpleSource α R i`.  The fixed additive rank separates
energies via the Haynsworth inertia identity of the full block matrix, and the
selected gap then determines `(z,B)`. -/
theorem injOn_physicalSchurFinCoordinateDecode_selectedSimple
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian) :
    Set.InjOn (physicalSchurFinCoordinateDecode i
        (physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V))
      (physicalSelectedSimpleSource α R i) := by
  intro x hx x' hx' hG
  set H_R := (hermitianOfFinCoordinates dR R).1 with hHRdef
  have hH : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).property
  set y := eigenpairIncidenceCoordinates i x with hydef
  set y' := eigenpairIncidenceCoordinates i x' with hy'def
  set F := physicalCoareaF H_R C V with hFdef
  have hFH (E : ℝ) : (F E).IsHermitian := physicalCoareaF_isHermitian H_R C V hH hV E
  rw [physicalSchurFinCoordinateDecode_eq_read, physicalSchurFinCoordinateDecode_eq_read,
    ← hydef, ← hy'def] at hG
  have hmat : (canonicalEigenpairChartDecode y).1 - F y.1 =
      (canonicalEigenpairChartDecode y').1 - F y'.1 :=
    selectedMatrixFinCoordinateReadCLM_injective_hermitian i
      ((canonicalEigenpairChartDecode y).2.sub (hFH _))
      ((canonicalEigenpairChartDecode y').2.sub (hFH _)) hG
  set A0 := (canonicalEigenpairChartDecode y).1 - F y.1 + V with hA0def
  have hA0 : A0.IsHermitian := ((canonicalEigenpairChartDecode y).2.sub (hFH _)).add hV
  have hdec : (canonicalEigenpairChartDecode y).1 =
      A0 - Cᴴ * physicalCoareaResolvent H_R y.1 * C := by
    rw [hA0def, hFdef, physicalCoareaF]
    abel
  have hdec' : (canonicalEigenpairChartDecode y').1 =
      A0 - Cᴴ * physicalCoareaResolvent H_R y'.1 * C := by
    rw [hA0def, hmat, hFdef, physicalCoareaF]
    abel
  have hB : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian :=
    y.2.2.2.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
  have hB' : (y'.2.2.1 - (y'.1 : ℂ) • 1).IsHermitian :=
    y'.2.2.2.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
  have hHE : (H_R - (y.1 : ℂ) • 1).IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
  have hHE' : (H_R - (y'.1 : ℂ) • 1).IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
  have hrank := hx.2.1
  have hrank' := hx'.2.1
  rw [← hydef] at hrank
  rw [← hy'def] at hrank'
  unfold physicalEigenpairFixedRank coareaRankIndex at hrank hrank'
  simp only at hrank hrank'
  rw [shiftedInertia_eq_negativeEigenvalueCount,
    shiftedInertia_complement_eq_negativeEigenvalueCount y.1 y.2.2 hB] at hrank
  rw [shiftedInertia_eq_negativeEigenvalueCount,
    shiftedInertia_complement_eq_negativeEigenvalueCount y'.1 y'.2.2 hB'] at hrank'
  have hcount : negativeEigenvalueCount hB + negativeEigenvalueCount hHE =
      negativeEigenvalueCount hB' + negativeEigenvalueCount hHE' := by
    rw [negativeEigenvalueCount_proof_irrel _ hHE] at hrank
    rw [negativeEigenvalueCount_proof_irrel _ hHE'] at hrank'
    omega
  have hE : y.1 = y'.1 :=
    physicalSchur_energy_eq_of_count_eq hH C hA0
      (det_exterior_sub_ne_zero_of_poleFree hx.2.2)
      (det_exterior_sub_ne_zero_of_poleFree hx'.2.2) hdec hdec' hB hHE hB' hHE' hcount
  have hD : (canonicalEigenpairChartDecode y).1 = (canonicalEigenpairChartDecode y').1 := by
    have := hmat
    rw [← hE] at this
    exact sub_left_injective this
  have hyy : y = y' := canonicalEigenpairChartDecode_injective_of_gap hE hx.1 hD
  exact (selectedEigenpairFinCoordinateLinearEquiv i).injective hyy

end SelectedSimpleSource

section Measurability

variable {dR d : ℕ}

/-- The selected gap matrix in incidence coordinates is Borel measurable. -/
theorem measurable_eigenpairIncidenceGapMatrix (i : Fin d) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2.1) := by
  have hy := measurable_eigenpairIncidenceCoordinates_complete i
  have hE : Measurable (fun x : HermitianCoordinateSpace d =>
      (eigenpairIncidenceCoordinates i x).1) := measurable_fst.comp hy
  have hB : Measurable (fun x : HermitianCoordinateSpace d =>
      ((eigenpairIncidenceCoordinates i x).2.2 :
        Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ)) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp hy))
  rw [Matrix.measurable_iff]
  intro a b
  simp only [eigenpairGapMatrix, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (hE.complex_ofReal.mul measurable_const).sub (hB.eval_matrix (i := a) (j := b))

/-- The selected-simple source is Borel measurable. -/
theorem measurableSet_physicalSelectedSimpleSource (α : ℕ)
    (R : HermitianCoordinateSpace dR) (i : Fin d) :
    MeasurableSet (physicalSelectedSimpleSource (d := d) α R i) := by
  have hgap : MeasurableSet {x : HermitianCoordinateSpace d |
      (eigenpairGapMatrix (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2.1).det ≠ 0} :=
    ((measurableSet_singleton 0).preimage
      (Measurable.matrixDet (measurable_eigenpairIncidenceGapMatrix i))).compl
  have hrank : MeasurableSet {x : HermitianCoordinateSpace d |
      physicalEigenpairFixedRank α R (eigenpairIncidenceCoordinates i x).1
        (eigenpairIncidenceCoordinates i x).2.2} := by
    change MeasurableSet ((fun x : HermitianCoordinateSpace d =>
      (R, ((eigenpairIncidenceCoordinates i x).1,
        (hermitianFinCoordinatesLinearEquiv (d - 1)).symm
          (eigenpairIncidenceCoordinates i x).2.2))) ⁻¹'
            coareaRankSector dR (d - 1) α)
    exact (measurableSet_coareaRankSector dR (d - 1) α).preimage
      (measurable_eigenpairIncidenceSectorCoordinates_complete R i)
  have hpole : MeasurableSet {x : HermitianCoordinateSpace d |
      (R, (eigenpairIncidenceCoordinates i x).1) ∈ coareaExteriorPoleFree dR} :=
    (measurableSet_coareaExteriorPoleFree dR).preimage
      (measurable_const.prodMk (measurable_eigenpairIncidenceEnergy_complete i))
  exact hgap.inter (hrank.inter hpole)

/-- The direct physical Schur decoder is Borel measurable for every measurable
energy-dependent compression `F`. -/
theorem measurable_physicalSchurFinCoordinateDecode (i : Fin d)
    {F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ}
    (hF : Measurable F) :
    Measurable (physicalSchurFinCoordinateDecode i F) := by
  have h : physicalSchurFinCoordinateDecode i F = fun x =>
      selectedEigenpairFinCoordinateChartDecode i x -
        selectedMatrixFinCoordinateReadCLM i (F (eigenpairIncidenceCoordinates i x).1) := by
    funext x
    rw [physicalSchurFinCoordinateDecode_eq_read, map_sub,
      selectedEigenpairFinCoordinateChartDecode_eq_read]
    rfl
  rw [h]
  exact (measurable_selectedEigenpairFinCoordinateChartDecode i).sub
    ((selectedMatrixFinCoordinateReadCLM i).continuous.measurable.comp
      (hF.comp (measurable_eigenpairIncidenceEnergy_complete i)))

end Measurability

section ChartCoarea

variable {dR d : ℕ}

/-- The direct physical decoder at exterior coordinates `R`, coupling `C` and
retained potential `V`: `(E,z,B) ↦ Decode(E,z,B) - (V - Cᴴ(H_R-E)⁻¹C)`. -/
abbrev physicalSelectedSimpleDecode (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    HermitianCoordinateSpace d → HermitianCoordinateSpace d :=
  physicalSchurFinCoordinateDecode i
    (physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V)

/-- The decoded image of a selected-simple chart source is Borel measurable
(Lusin–Souslin for the injective measurable decoder). -/
theorem measurableSet_image_physicalSelectedSimpleDecode
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    {s : Set (HermitianCoordinateSpace d)} (hs : MeasurableSet s)
    (hsub : s ⊆ physicalSelectedSimpleSource α R i) :
    MeasurableSet (physicalSelectedSimpleDecode R i C V '' s) :=
  MeasurableSet.image_of_measurable_injOn hs
    (measurable_physicalSchurFinCoordinateDecode i (measurable_physicalCoareaF _ C V))
    ((injOn_physicalSchurFinCoordinateDecode_selectedSimple α R i C V hV).mono hsub)

/-- **Exact chart change of variables on the selected-simple source.**  For
every measurable `s ⊆ physicalSelectedSimpleSource α R i` and every
`g ≥ 0`,
`∫_{G(s)} g = ∫_s ρ(E,z,B) · g(G(E,z,B))` with the explicit Jacobian
`ρ = canonicalProjectiveAffineDensity z * |det (E I - B)|² * vᴴ 𝒟(E) v`
(`physicalSchurDecoderDensity`, `𝒟(E) = I + T(E)ᴴT(E)`, `T(E)=(H_R-E)⁻¹C`).
Injectivity comes from `injOn_physicalSchurFinCoordinateDecode_selectedSimple`,
not from a separation hypothesis.  Fixed sizes, fixed `R, C, V`; no limits. -/
theorem lintegral_image_physicalSelectedSimpleDecode
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    {s : Set (HermitianCoordinateSpace d)} (hs : MeasurableSet s)
    (hsub : s ⊆ physicalSelectedSimpleSource α R i)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in physicalSelectedSimpleDecode R i C V '' s, g K) =
      ∫⁻ x in s, ENNReal.ofReal
          (physicalSchurDecoderDensity i
            (physicalCoareaT (hermitianOfFinCoordinates dR R).1 C) x) *
        g (physicalSelectedSimpleDecode R i C V x) :=
  lintegral_image_physicalSchurFinCoordinateDecode i _ _ s hs
    ((injOn_physicalSchurFinCoordinateDecode_selectedSimple α R i C V hV).mono hsub)
    (fun _ hx => hasDerivAt_physicalCoareaF _ (hermitianOfFinCoordinates dR R).property
      C V _ (det_exterior_sub_ne_zero_of_poleFree (hsub hx).2.2)) g

end ChartCoarea

section GlobalCover

variable {dR d : ℕ}

/-- The decoded image of the full selected-simple source of chart `i`, for a
chart-indexed family of couplings `Cc` and retained potentials `Vc`. -/
def physicalSelectedSimpleImage (α : ℕ) (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) : Set (HermitianCoordinateSpace d) :=
  physicalSelectedSimpleDecode R i (Cc i) (Vc i) '' physicalSelectedSimpleSource α R i

/-- Deterministic disjointization: chart `i` keeps exactly the source points whose
decoded matrix is not already decoded by an earlier pivot `j < i`. -/
def physicalSelectedSimpleDisjointSource (α : ℕ) (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (i : Fin d) : Set (HermitianCoordinateSpace d) :=
  physicalSelectedSimpleSource α R i \
    physicalSelectedSimpleDecode R i (Cc i) (Vc i) ⁻¹'
      (⋃ j : Fin d, if j < i then physicalSelectedSimpleImage α R Cc Vc j else ∅)

theorem physicalSelectedSimpleDisjointSource_subset (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (i : Fin d) :
    physicalSelectedSimpleDisjointSource α R Cc Vc i ⊆ physicalSelectedSimpleSource α R i :=
  Set.sdiff_subset

/-- Every full selected-simple image is Borel measurable. -/
theorem measurableSet_physicalSelectedSimpleImage (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hV : ∀ i, (Vc i).IsHermitian) (i : Fin d) :
    MeasurableSet (physicalSelectedSimpleImage α R Cc Vc i) :=
  measurableSet_image_physicalSelectedSimpleDecode α R i (Cc i) (Vc i) (hV i)
    (measurableSet_physicalSelectedSimpleSource α R i) subset_rfl

/-- The disjointized sources are Borel measurable. -/
theorem measurableSet_physicalSelectedSimpleDisjointSource (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hV : ∀ i, (Vc i).IsHermitian) (i : Fin d) :
    MeasurableSet (physicalSelectedSimpleDisjointSource α R Cc Vc i) := by
  apply (measurableSet_physicalSelectedSimpleSource α R i).diff
  apply MeasurableSet.preimage _
    (measurable_physicalSchurFinCoordinateDecode i (measurable_physicalCoareaF _ _ _))
  apply MeasurableSet.iUnion
  intro j
  split_ifs
  · exact measurableSet_physicalSelectedSimpleImage α R Cc Vc hV j
  · exact MeasurableSet.empty

/-- The decoded images of the disjointized sources are pairwise disjoint. -/
theorem physicalSelectedSimpleDisjointSource_image_pairwise (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    Pairwise (Function.onFun Disjoint (fun i : Fin d =>
      physicalSelectedSimpleDecode R i (Cc i) (Vc i) ''
        physicalSelectedSimpleDisjointSource α R Cc Vc i)) := by
  intro i j hij
  change Disjoint (physicalSelectedSimpleDecode R i (Cc i) (Vc i) ''
      physicalSelectedSimpleDisjointSource α R Cc Vc i)
    (physicalSelectedSimpleDecode R j (Cc j) (Vc j) ''
      physicalSelectedSimpleDisjointSource α R Cc Vc j)
  rw [Set.disjoint_left]
  rintro K ⟨xi, hxi, rfl⟩ ⟨xj, hxj, hdec⟩
  rcases lt_or_gt_of_ne hij with h | h
  · apply hxj.2
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simp only [h, ↓reduceIte]
    exact ⟨xi, hxi.1, hdec.symm⟩
  · apply hxi.2
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    simp only [h, ↓reduceIte]
    exact ⟨xj, hxj.1, hdec⟩

/-- Disjointization loses nothing: the disjoint images cover exactly the union of
the full selected-simple images. -/
theorem iUnion_physicalSelectedSimpleDisjointSource_image (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    (⋃ i : Fin d, physicalSelectedSimpleDecode R i (Cc i) (Vc i) ''
        physicalSelectedSimpleDisjointSource α R Cc Vc i) =
      ⋃ i : Fin d, physicalSelectedSimpleImage α R Cc Vc i := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono fun i =>
      Set.image_mono (physicalSelectedSimpleDisjointSource_subset α R Cc Vc i)
  · intro K hK
    have hne : (Finset.univ.filter fun i : Fin d =>
        K ∈ physicalSelectedSimpleImage α R Cc Vc i).Nonempty := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hK
      exact ⟨i, by simp [hi]⟩
    set i := (Finset.univ.filter fun i : Fin d =>
        K ∈ physicalSelectedSimpleImage α R Cc Vc i).min' hne with hidef
    have hi := Finset.min'_mem _ hne
    rw [← hidef] at hi
    have hKi : K ∈ physicalSelectedSimpleImage α R Cc Vc i := (Finset.mem_filter.1 hi).2
    obtain ⟨x, hx, hxK⟩ := hKi
    refine Set.mem_iUnion.2 ⟨i, x, ⟨hx, ?_⟩, hxK⟩
    intro hlow
    simp only [Set.mem_preimage, Set.mem_iUnion] at hlow
    obtain ⟨j, hj⟩ := hlow
    split_ifs at hj with hji
    · rw [hxK] at hj
      have hjmem : j ∈ Finset.univ.filter fun i : Fin d =>
          K ∈ physicalSelectedSimpleImage α R Cc Vc i := by simp [hj]
      have := Finset.min'_le _ j hjmem
      rw [← hidef] at this
      exact absurd hji (not_lt_of_ge this)
    · exact hj

/-- **Global selected-simple coarea formula.**  For chart-indexed physical data
`(Cc i, Vc i)` with every `Vc i` Hermitian, the integral of any `g ≥ 0` over the
union of all selected-simple decoded images is the finite sum, over pivots `i`,
of the exact chart integrals over the disjointized sources.  There is no
multiplicity: the disjointized decoded images are pairwise disjoint, measurable,
and exhaust the union. -/
theorem lintegral_iUnion_physicalSelectedSimpleImage (α : ℕ)
    (R : HermitianCoordinateSpace dR)
    (Cc : Fin d → Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (Vc : Fin d → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hV : ∀ i, (Vc i).IsHermitian) (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in ⋃ i : Fin d, physicalSelectedSimpleImage α R Cc Vc i, g K) =
      ∑ i : Fin d, ∫⁻ x in physicalSelectedSimpleDisjointSource α R Cc Vc i,
        ENNReal.ofReal (physicalSchurDecoderDensity i
          (physicalCoareaT (hermitianOfFinCoordinates dR R).1 (Cc i)) x) *
        g (physicalSelectedSimpleDecode R i (Cc i) (Vc i) x) := by
  rw [← iUnion_physicalSelectedSimpleDisjointSource_image,
    MeasureTheory.lintegral_iUnion
      (fun i => measurableSet_image_physicalSelectedSimpleDecode α R i (Cc i) (Vc i) (hV i)
        (measurableSet_physicalSelectedSimpleDisjointSource α R Cc Vc hV i)
        (physicalSelectedSimpleDisjointSource_subset α R Cc Vc i))
      (physicalSelectedSimpleDisjointSource_image_pairwise α R Cc Vc),
    tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_image_physicalSelectedSimpleDecode α R i (Cc i) (Vc i) (hV i)
    (measurableSet_physicalSelectedSimpleDisjointSource α R Cc Vc hV i)
    (physicalSelectedSimpleDisjointSource_subset α R Cc Vc i) g

end GlobalCover

section CanonicalEncode

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Affine projective coordinates at the canonical pivot: `z_j = u_j / u_pivot`. -/
def canonicalAffineCoordinate (u : Unit ⊕ n → ℂ) : n → ℂ :=
  fun j => u (Sum.inr j) / u (Sum.inl Unit.unit)

/-- A vector with nonzero pivot is a nonzero multiple of the phase-fixed unit
vector decoded from its own affine coordinates. -/
theorem canonicalProjectiveUnitVector_canonicalAffineCoordinate
    (u : Unit ⊕ n → ℂ) (hu : u (Sum.inl Unit.unit) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      ⇑(canonicalProjectiveUnitVector (canonicalAffineCoordinate u)) = c • u := by
  set rec := projectiveEigenvectorReconstruction (Sum.inl Unit.unit : Unit ⊕ n)
    (canonicalProjectiveChartCoordinates (canonicalAffineCoordinate u)) with hrec
  have hrec0 : rec ≠ 0 := projectiveEigenvectorReconstruction_ne_zero _ _
  have hnorm : ‖rec‖ ≠ 0 := norm_ne_zero_iff.mpr hrec0
  refine ⟨((‖rec‖⁻¹ : ℝ) : ℂ) * (u (Sum.inl Unit.unit))⁻¹, ?_, ?_⟩
  · refine mul_ne_zero ?_ (inv_ne_zero hu)
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero hnorm)
  · funext a
    change (projectiveUnitReconstruction (Sum.inl Unit.unit)
      (canonicalProjectiveChartCoordinates (canonicalAffineCoordinate u))) a = _
    rw [projectiveUnitReconstruction, ← hrec]
    rcases a with t | j
    · cases t
      simp [hrec, projectiveEigenvectorReconstruction, hu]
    · simp only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, hrec,
        projectiveEigenvectorReconstruction]
      simp [canonicalAffineCoordinate]
      field_simp

/-- If `v(z)` is an eigenvector of a Hermitian `M` with eigenvalue `E`, then the
phase-fixed frame block-diagonalizes `M` as `diag(E, B)` with `B` the
lower-right block of `Hᴴ M H`. -/
theorem canonicalEigenpairFrame_conj_eq_canonical
    (M : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) (hM : M.IsHermitian) (z : n → ℂ) (E : ℝ)
    (hMv : M *ᵥ ⇑(canonicalProjectiveUnitVector z) =
      (E : ℂ) • ⇑(canonicalProjectiveUnitVector z)) :
    (canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z =
      eigenpairCanonicalMatrix E
        (((canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z).submatrix
          Sum.inr Sum.inr) := by
  set H := canonicalEigenpairFrame z with hHdef
  set v := ⇑(canonicalProjectiveUnitVector z) with hvdef
  have hHe : H *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit) = v :=
    phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector z
  have hunit : Hᴴ * H = 1 := canonicalEigenpairFrame_conjTranspose_mul z
  have hcol : (Hᴴ * M * H) *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit) =
      (E : ℂ) • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
    calc (Hᴴ * M * H) *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit) =
          Hᴴ *ᵥ (M *ᵥ (H *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit))) := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Hᴴ *ᵥ ((E : ℂ) • v) := by rw [hHe, hMv]
      _ = (E : ℂ) • (Hᴴ *ᵥ (H *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit))) := by
            rw [Matrix.mulVec_smul, hHe]
      _ = (E : ℂ) • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
            rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]
  set Cm := Hᴴ * M * H with hCm
  have hC : Cm.IsHermitian := isHermitian_unitaryConjugation H M hM
  ext a b
  rcases a with u | a <;> rcases b with w | b
  · cases u
    cases w
    have h := congrFun hcol (Sum.inl Unit.unit)
    simpa [eigenpairCanonicalMatrix, phaseFixedCoordinateVector, Matrix.mulVec] using h
  · cases u
    change Cm (Sum.inl Unit.unit) (Sum.inr b) = 0
    rw [← hC.apply (Sum.inl Unit.unit) (Sum.inr b)]
    have h := congrFun hcol (Sum.inr b)
    simpa [phaseFixedCoordinateVector, Matrix.mulVec] using congrArg star h
  · have h := congrFun hcol (Sum.inr a)
    change Cm (Sum.inr a) (Sum.inl Unit.unit) = 0
    simpa [phaseFixedCoordinateVector, Matrix.mulVec] using h
  · simp [eigenpairCanonicalMatrix]

/-- The complementary Hermitian block read in the phase-fixed frame of `z`. -/
def canonicalEncodeBlock (z : n → ℂ) (M : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ)
    (hM : M.IsHermitian) : RealHermitianMatrix n :=
  ⟨((canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z).submatrix
      Sum.inr Sum.inr,
    isHermitian_submatrix_inr
      ⟨(canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z,
        isHermitian_unitaryConjugation _ M hM⟩⟩

/-- **Encoding inverse.**  Decoding `(E, z, B)` with `B` the encoded block
returns `M` whenever `v(z)` is an `E`-eigenvector of the Hermitian matrix `M`. -/
theorem canonicalEigenpairChartDecode_encode
    (M : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) (hM : M.IsHermitian) (z : n → ℂ) (E : ℝ)
    (hMv : M *ᵥ ⇑(canonicalProjectiveUnitVector z) =
      (E : ℂ) • ⇑(canonicalProjectiveUnitVector z)) :
    (canonicalEigenpairChartDecode (E, z, canonicalEncodeBlock z M hM)).1 = M := by
  rw [canonicalEigenpairChartDecode_val]
  change canonicalEigenpairFrame z * eigenpairCanonicalMatrix E
      (((canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z).submatrix
        Sum.inr Sum.inr) * (canonicalEigenpairFrame z)ᴴ = M
  rw [← canonicalEigenpairFrame_conj_eq_canonical M hM z E hMv]
  have h1 := canonicalEigenpairFrame_mul_conjTranspose z
  calc canonicalEigenpairFrame z *
        ((canonicalEigenpairFrame z)ᴴ * M * canonicalEigenpairFrame z) *
          (canonicalEigenpairFrame z)ᴴ =
        (canonicalEigenpairFrame z * (canonicalEigenpairFrame z)ᴴ) * M *
          (canonicalEigenpairFrame z * (canonicalEigenpairFrame z)ᴴ) := by
          simp only [Matrix.mul_assoc]
    _ = M := by rw [h1, Matrix.one_mul, Matrix.mul_one]

/-- **The selected gap follows from simplicity of `E`.**  If every
`E`-eigenvector of `M` is a multiple of `v(z)`, then the encoded complementary
block has `det (E I - B) ≠ 0`. -/
theorem det_eigenpairGapMatrix_encode_ne_zero
    (M : Matrix (Unit ⊕ n) (Unit ⊕ n) ℂ) (hM : M.IsHermitian) (z : n → ℂ) (E : ℝ)
    (hMv : M *ᵥ ⇑(canonicalProjectiveUnitVector z) =
      (E : ℂ) • ⇑(canonicalProjectiveUnitVector z))
    (hsimple : ∀ w : Unit ⊕ n → ℂ, M *ᵥ w = (E : ℂ) • w →
      ∃ c : ℂ, w = c • ⇑(canonicalProjectiveUnitVector z)) :
    (eigenpairGapMatrix E (canonicalEncodeBlock z M hM).1).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  set H := canonicalEigenpairFrame z with hHdef
  set Cm := Hᴴ * M * H with hCm
  have hunit : Hᴴ * H = 1 := canonicalEigenpairFrame_conjTranspose_mul z
  have hHH : H * Hᴴ = 1 := canonicalEigenpairFrame_mul_conjTranspose z
  let w0 : Unit ⊕ n → ℂ := Sum.elim (fun _ => 0) w
  have hCw : Cm *ᵥ w0 = (E : ℂ) • w0 := by
    have hcan := canonicalEigenpairFrame_conj_eq_canonical M hM z E hMv
    rw [← hHdef, ← hCm] at hcan
    have hBw : ∀ j, (Cm.submatrix Sum.inr Sum.inr *ᵥ w) j = (E : ℂ) * w j := by
      intro j
      have := congrFun hw j
      simp only [eigenpairGapMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        sub_eq_zero] at this
      exact this.symm
    rw [hcan]
    funext a
    rcases a with t | j
    · simp [w0, eigenpairCanonicalMatrix, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type]
    · have := hBw j
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at this
      simp [w0, eigenpairCanonicalMatrix, Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type, this]
  have hMW : M *ᵥ (H *ᵥ w0) = (E : ℂ) • (H *ᵥ w0) := by
    have hMeq : M = H * Cm * Hᴴ := by
      rw [hCm]
      calc M = (H * Hᴴ) * M * (H * Hᴴ) := by rw [hHH, Matrix.one_mul, Matrix.mul_one]
        _ = H * (Hᴴ * M * H) * Hᴴ := by simp only [Matrix.mul_assoc]
    calc M *ᵥ (H *ᵥ w0) = H *ᵥ (Cm *ᵥ ((Hᴴ * H) *ᵥ w0)) := by
          rw [hMeq]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (E : ℂ) • (H *ᵥ w0) := by
          rw [hunit, Matrix.one_mulVec, hCw, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := hsimple _ hMW
  have hHe : H *ᵥ phaseFixedCoordinateVector (Sum.inl Unit.unit) =
      ⇑(canonicalProjectiveUnitVector z) :=
    phaseFixedHouseholderFrame_mulVec_canonicalProjectiveUnitVector z
  have hw0e : w0 = c • phaseFixedCoordinateVector (Sum.inl Unit.unit) := by
    have h2 := congrArg (fun t => Hᴴ *ᵥ t) hc
    simp only [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec, Matrix.mulVec_smul] at h2
    rw [← hHe, Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec] at h2
    exact h2
  apply hw0
  funext j
  have := congrFun hw0e (Sum.inr j)
  simpa [w0, phaseFixedCoordinateVector] using this

end CanonicalEncode

section ChartImage

variable {dR d : ℕ}

/-- Selected readback inverts the selected reindexing of finite Hermitian
coordinates. -/
theorem selectedMatrixFinCoordinateReadCLM_reindex (i : Fin d)
    (K : HermitianCoordinateSpace d) :
    selectedMatrixFinCoordinateReadCLM i
      (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).1 = K := by
  rw [selectedMatrixFinCoordinateReadCLM_hermitian]
  exact (selectedEigenpairFinCoordinateLinearEquiv i).symm_apply_apply K

/-- The reduced matrix `M_i(K,E) = K + F(E)` in the selected chart, with
`F(E) = V - Cᴴ(H_R-E)⁻¹C` and `K` read in the selected-first indexing. -/
def physicalSelectedReducedMatrix (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (K : HermitianCoordinateSpace d) (E : ℝ) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).1 +
    physicalCoareaF (hermitianOfFinCoordinates dR R).1 C V E

/-- **Intrinsic selected-simple crossing at energy `E` in chart `i`.**  The
energy avoids the exterior poles; `E` is an eigenvalue of the reduced matrix
`M = M_i(K,E)` with an eigenvector whose pivot entry is nonzero, every
`E`-eigenvector of `M` is a multiple of it (geometric simplicity of the
selected root only), and the additive strict rank is
`N_R(E) + #{eigenvalues of M below E} = α` (zero-based; the paper's
one-based rank is `α + 1`). -/
def PhysicalSelectedSimpleCrossing (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (K : HermitianCoordinateSpace d) (E : ℝ) : Prop :=
  (R, E) ∈ coareaExteriorPoleFree dR ∧
  ∃ u : Unit ⊕ Fin (d - 1) → ℂ, u (Sum.inl Unit.unit) ≠ 0 ∧
    physicalSelectedReducedMatrix R i C V K E *ᵥ u = (E : ℂ) • u ∧
    (∀ w : Unit ⊕ Fin (d - 1) → ℂ,
      physicalSelectedReducedMatrix R i C V K E *ᵥ w = (E : ℂ) • w →
        ∃ c : ℂ, w = c • u) ∧
    ∃ hM : (physicalSelectedReducedMatrix R i C V K E).IsHermitian,
      shiftedInertia dR R E +
        eigenCount (⟨_, hM⟩ : HermitianMatrix (Unit ⊕ Fin (d - 1))) (Set.Iio E) = α

/-- Strict lower eigenvalue count of a Hermitian matrix as a negative count of its
shift, transported along a matrix equality. -/
theorem eigenCount_Iio_eq_negativeEigenvalueCount_of_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M N : Matrix ι ι ℂ} (hM : M.IsHermitian) (E : ℝ) (hMN : M = N)
    (hN : (N - (E : ℂ) • 1).IsHermitian) :
    eigenCount (⟨M, hM⟩ : HermitianMatrix ι) (Set.Iio E) = negativeEigenvalueCount hN := by
  have h := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
    (⟨M, hM⟩ : HermitianMatrix ι) E
  simp only at h
  rw [← h]
  exact negativeEigenvalueCount_congr_eq (by rw [hMN]) _ _

/-- **Exact image of a selected-simple chart.**  A Hermitian coordinate `K` is
decoded by chart `i` from its selected-simple source if and only if it admits
an intrinsic selected-simple crossing at some energy.  This is the chart-level
exhaustion statement: nothing beyond selected gap, fixed additive rank and
exterior pole avoidance is required, and every such `K` is reached. -/
theorem mem_physicalSelectedSimpleDecode_image_iff
    (α : ℕ) (R : HermitianCoordinateSpace dR) (i : Fin d)
    (C : Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    (K : HermitianCoordinateSpace d) :
    K ∈ physicalSelectedSimpleDecode R i C V '' physicalSelectedSimpleSource α R i ↔
      ∃ E : ℝ, PhysicalSelectedSimpleCrossing α R i C V K E := by
  set H_R := (hermitianOfFinCoordinates dR R).1 with hHRdef
  have hH : H_R.IsHermitian := (hermitianOfFinCoordinates dR R).property
  set F := physicalCoareaF H_R C V with hFdef
  have hFH (E : ℝ) : (F E).IsHermitian := physicalCoareaF_isHermitian H_R C V hH hV E
  set Kr := (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).1
    with hKr
  have hKrH : Kr.IsHermitian :=
    (selectedCoordinateHermitianReindex i (hermitianFinCoordinatesLinearEquiv d K)).2
  have hMdef (E : ℝ) : physicalSelectedReducedMatrix R i C V K E = Kr + F E := rfl
  constructor
  · rintro ⟨x, hx, hxK⟩
    set y := eigenpairIncidenceCoordinates i x with hydef
    refine ⟨y.1, hx.2.2, ?_⟩
    have hG := physicalSchurFinCoordinateDecode_eq_read i F x
    rw [← hydef] at hG
    change physicalSchurFinCoordinateDecode i F x = K at hxK
    rw [hxK, ← selectedMatrixFinCoordinateReadCLM_reindex i K, ← hKr] at hG
    have hKreq : Kr = (canonicalEigenpairChartDecode y).1 - F y.1 :=
      selectedMatrixFinCoordinateReadCLM_injective_hermitian i hKrH
        ((canonicalEigenpairChartDecode y).2.sub (hFH _)) hG
    have hM : physicalSelectedReducedMatrix R i C V K y.1 =
        (canonicalEigenpairChartDecode y).1 := by
      rw [hMdef, hKreq, sub_add_cancel]
    refine ⟨⇑(canonicalProjectiveUnitVector y.2.1), ?_, ?_, ?_, ?_⟩
    · intro h0
      have h2 := canonicalProjectiveUnitVector_selected_re_pos y.2.1
      rw [show (canonicalProjectiveUnitVector y.2.1) (Sum.inl Unit.unit) = 0 from h0] at h2
      simp at h2
    · rw [hM]
      exact canonicalEigenpairChartDecode_mulVec_unitVector y
    · intro w hw
      rw [hM] at hw
      exact canonicalEigenpairChartDecode_eigenvector_eq_smul y hx.1 w hw
    · refine ⟨hM ▸ (canonicalEigenpairChartDecode y).2, ?_⟩
      have hB : (y.2.2.1 - (y.1 : ℂ) • 1).IsHermitian :=
        y.2.2.2.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
      have hdecE : ((canonicalEigenpairChartDecode y).1 - (y.1 : ℂ) • 1).IsHermitian :=
        (canonicalEigenpairChartDecode y).2.sub
          (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
      rw [eigenCount_Iio_eq_negativeEigenvalueCount_of_eq _ y.1 hM hdecE,
        negativeEigenvalueCount_canonicalDecode_sub y hdecE hB,
        ← shiftedInertia_complement_eq_negativeEigenvalueCount y.1 y.2.2 hB]
      have hrank := hx.2.1
      rw [← hydef] at hrank
      unfold physicalEigenpairFixedRank coareaRankIndex at hrank
      simp only at hrank
      omega
  · rintro ⟨E, hpole, u, hu0, hMu, hsimp, hM, hcount⟩
    set M := physicalSelectedReducedMatrix R i C V K E with hMdef'
    set z := canonicalAffineCoordinate u with hzdef
    obtain ⟨c, hc0, hcv⟩ := canonicalProjectiveUnitVector_canonicalAffineCoordinate u hu0
    rw [← hzdef] at hcv
    have hMv : M *ᵥ ⇑(canonicalProjectiveUnitVector z) =
        (E : ℂ) • ⇑(canonicalProjectiveUnitVector z) := by
      rw [hcv, Matrix.mulVec_smul, hMu, smul_comm]
    have hsimple : ∀ w : Unit ⊕ Fin (d - 1) → ℂ, M *ᵥ w = (E : ℂ) • w →
        ∃ c' : ℂ, w = c' • ⇑(canonicalProjectiveUnitVector z) := by
      intro w hw
      obtain ⟨c', hc'⟩ := hsimp w hw
      refine ⟨c' * c⁻¹, ?_⟩
      rw [hcv, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one, hc']
    set B := canonicalEncodeBlock z M hM with hBdef
    set y : EigenpairHermitianBlockCoordinates (Fin (d - 1)) := (E, z, B) with hydef
    have hdec : (canonicalEigenpairChartDecode y).1 = M :=
      canonicalEigenpairChartDecode_encode M hM z E hMv
    refine ⟨(selectedEigenpairFinCoordinateLinearEquiv i).symm y, ?_, ?_⟩
    · have hy : eigenpairIncidenceCoordinates i
          ((selectedEigenpairFinCoordinateLinearEquiv i).symm y) = y :=
        (selectedEigenpairFinCoordinateLinearEquiv i).apply_symm_apply y
      change (eigenpairGapMatrix (eigenpairIncidenceCoordinates i _).1
          (eigenpairIncidenceCoordinates i _).2.2.1).det ≠ 0 ∧
        physicalEigenpairFixedRank α R (eigenpairIncidenceCoordinates i _).1
          (eigenpairIncidenceCoordinates i _).2.2 ∧
        (R, (eigenpairIncidenceCoordinates i _).1) ∈ coareaExteriorPoleFree dR
      rw [hy]
      refine ⟨det_eigenpairGapMatrix_encode_ne_zero M hM z E hMv hsimple, ?_, hpole⟩
      have hB : (B.1 - (E : ℂ) • 1).IsHermitian :=
        B.2.sub (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
      have hdecE : ((canonicalEigenpairChartDecode y).1 - (E : ℂ) • 1).IsHermitian :=
        (canonicalEigenpairChartDecode y).2.sub
          (Matrix.isHermitian_one.smul (RCLike.conj_ofReal _))
      have hcnt := eigenCount_Iio_eq_negativeEigenvalueCount_of_eq hM E hdec.symm hdecE
      rw [negativeEigenvalueCount_canonicalDecode_sub y hdecE hB] at hcnt
      have h3 : shiftedInertia dR R E + negativeEigenvalueCount hB = α := by
        rw [← hcnt]
        exact hcount
      unfold physicalEigenpairFixedRank coareaRankIndex
      simp only
      rw [shiftedInertia_complement_eq_negativeEigenvalueCount E B hB]
      change shiftedInertia dR R E + negativeEigenvalueCount hB + 1 = α + 1
      omega
    · change physicalSchurFinCoordinateDecode i F
        ((selectedEigenpairFinCoordinateLinearEquiv i).symm y) = K
      rw [physicalSchurFinCoordinateDecode_eq_read]
      have hy : eigenpairIncidenceCoordinates i
          ((selectedEigenpairFinCoordinateLinearEquiv i).symm y) = y :=
        (selectedEigenpairFinCoordinateLinearEquiv i).apply_symm_apply y
      rw [hy, hdec]
      change selectedMatrixFinCoordinateReadCLM i (M - F E) = K
      rw [hMdef', hMdef, add_sub_cancel_right]
      exact selectedMatrixFinCoordinateReadCLM_reindex i K

end ChartImage

section ConsistentData

variable {dR d : ℕ}

/-- Chart-`i` coupling obtained from a full coupling `C : Fin dR × Fin d` by
putting the pivot `i` first. -/
def physicalChartCoupling (C : Matrix (Fin dR) (Fin d) ℂ) (i : Fin d) :
    Matrix (Fin dR) (Unit ⊕ Fin (d - 1)) ℂ :=
  C.submatrix id (selectedCoordinateEquiv i).symm

/-- Chart-`i` retained potential obtained from a full potential `V` by putting
the pivot `i` first. -/
def physicalChartPotential (V : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ :=
  Matrix.reindex (selectedCoordinateEquiv i) (selectedCoordinateEquiv i) V

theorem physicalChartPotential_isHermitian {V : Matrix (Fin d) (Fin d) ℂ}
    (hV : V.IsHermitian) (i : Fin d) : (physicalChartPotential V i).IsHermitian :=
  isHermitian_reindex_equiv _ V hV

/-- The chart-free reduced matrix `M(K,E) = K + V - Cᴴ(H_R-E)⁻¹C` on `Fin d`. -/
def physicalGlobalReducedMatrix (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ)
    (K : HermitianCoordinateSpace d) (E : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (hermitianOfFinCoordinates d K).1 + (V -
    Cᴴ * physicalCoareaResolvent (hermitianOfFinCoordinates dR R).1 E * C)

/-- Every chart reduced matrix is the pivot-first reindexing of the chart-free
reduced matrix. -/
theorem physicalSelectedReducedMatrix_eq_reindex (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (i : Fin d)
    (K : HermitianCoordinateSpace d) (E : ℝ) :
    physicalSelectedReducedMatrix R i (physicalChartCoupling C i) (physicalChartPotential V i)
        K E =
      Matrix.reindex (selectedCoordinateEquiv i) (selectedCoordinateEquiv i)
        (physicalGlobalReducedMatrix R C V K E) := by
  ext a b
  simp [physicalSelectedReducedMatrix, physicalGlobalReducedMatrix, physicalCoareaF,
    physicalChartCoupling, physicalChartPotential, selectedCoordinateHermitianReindex,
    Matrix.mul_apply, Matrix.reindex_apply, hermitianFinCoordinatesLinearEquiv]
  rfl

/-- **Chart-free selected-simple crossing.**  At energy `E` avoiding exterior
poles, `E` is an eigenvalue of the chart-free reduced matrix `M(K,E)` with
one-dimensional eigenspace spanned by `u ≠ 0`, and the zero-based additive rank
`N_R(E) + #{eigenvalues of M(K,E) below E}` equals `α`. -/
def PhysicalSelectedSimpleGlobalCrossing (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ)
    (K : HermitianCoordinateSpace d) (E : ℝ) : Prop :=
  (R, E) ∈ coareaExteriorPoleFree dR ∧
  ∃ u : Fin d → ℂ, u ≠ 0 ∧ physicalGlobalReducedMatrix R C V K E *ᵥ u = (E : ℂ) • u ∧
    (∀ w : Fin d → ℂ, physicalGlobalReducedMatrix R C V K E *ᵥ w = (E : ℂ) • w →
      ∃ c : ℂ, w = c • u) ∧
    ∃ hM : (physicalGlobalReducedMatrix R C V K E).IsHermitian,
      shiftedInertia dR R E + eigenCount (⟨_, hM⟩ : HermitianMatrix (Fin d)) (Set.Iio E) = α

/-- The chart-free physical good set: reduced coordinates admitting a
selected-simple crossing at some energy, at fixed additive rank `α`. -/
def physicalSelectedSimpleGoodSet (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) :
    Set (HermitianCoordinateSpace d) :=
  {K | ∃ E : ℝ, PhysicalSelectedSimpleGlobalCrossing α R C V K E}

/-- Reindexing commutes with matrix-vector multiplication. -/
theorem reindex_mulVec_comp {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (M : Matrix m m ℂ) (u : m → ℂ) :
    Matrix.reindex e e M *ᵥ (u ∘ e.symm) = (M *ᵥ u) ∘ e.symm := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply]
  exact Equiv.sum_comp e.symm (fun j => M (e.symm a) j * u j)

/-- Strict lower eigenvalue counts are invariant under reindexing. -/
theorem eigenCount_Iio_reindex {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (e : m ≃ n) {M : Matrix m m ℂ} (hM : M.IsHermitian)
    (hM' : (Matrix.reindex e e M).IsHermitian) (E : ℝ) :
    eigenCount (⟨_, hM'⟩ : HermitianMatrix n) (Set.Iio E) =
      eigenCount (⟨_, hM⟩ : HermitianMatrix m) (Set.Iio E) := by
  have h1 := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
    (⟨_, hM'⟩ : HermitianMatrix n) E
  have h2 := negativeEigenvalueCount_sub_real_smul_one_eq_eigenCount_Iio
    (⟨_, hM⟩ : HermitianMatrix m) E
  simp only at h1 h2
  rw [← h1, ← h2, negativeEigenvalueCount_eq_card_filter_roots,
    negativeEigenvalueCount_eq_card_filter_roots]
  rw [show Matrix.reindex e e M - (E : ℂ) • 1 = Matrix.reindex e e (M - (E : ℂ) • 1) by
    ext a b
    simp [Matrix.one_apply, Matrix.reindex_apply], Matrix.charpoly_reindex]

/-- Chart crossings are exactly the chart-free crossings whose eigenvector has a
nonzero entry at the pivot. -/
theorem physicalSelectedSimpleCrossing_iff_global
    (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ)
    (i : Fin d) (K : HermitianCoordinateSpace d) (E : ℝ) :
    PhysicalSelectedSimpleCrossing α R i (physicalChartCoupling C i)
        (physicalChartPotential V i) K E ↔
      (R, E) ∈ coareaExteriorPoleFree dR ∧
      ∃ u : Fin d → ℂ, u i ≠ 0 ∧ physicalGlobalReducedMatrix R C V K E *ᵥ u = (E : ℂ) • u ∧
        (∀ w : Fin d → ℂ, physicalGlobalReducedMatrix R C V K E *ᵥ w = (E : ℂ) • w →
          ∃ c : ℂ, w = c • u) ∧
        ∃ hM : (physicalGlobalReducedMatrix R C V K E).IsHermitian,
          shiftedInertia dR R E +
            eigenCount (⟨_, hM⟩ : HermitianMatrix (Fin d)) (Set.Iio E) = α := by
  set e := selectedCoordinateEquiv i with hedef
  set M := physicalGlobalReducedMatrix R C V K E with hMdef
  have hMi : physicalSelectedReducedMatrix R i (physicalChartCoupling C i)
      (physicalChartPotential V i) K E = Matrix.reindex e e M :=
    physicalSelectedReducedMatrix_eq_reindex R C V i K E
  have hpiv : e.symm (Sum.inl Unit.unit) = i := by
    rw [hedef, Equiv.symm_apply_eq, selectedCoordinateEquiv_apply_selected]
  have hMeig (u : Fin d → ℂ) :
      Matrix.reindex e e M *ᵥ (u ∘ e.symm) = (E : ℂ) • (u ∘ e.symm) ↔
        M *ᵥ u = (E : ℂ) • u := by
    rw [reindex_mulVec_comp]
    constructor
    · intro h
      funext a
      have := congrFun h (e a)
      simpa using this
    · intro h
      rw [h]
      rfl
  have hcomp (u : Unit ⊕ Fin (d - 1) → ℂ) : (u ∘ e) ∘ e.symm = u := by
    funext a
    simp
  have hHerm : M.IsHermitian ↔ (Matrix.reindex e e M).IsHermitian := by
    constructor
    · exact fun h => isHermitian_reindex_equiv e M h
    · intro h
      have := isHermitian_reindex_equiv e.symm _ h
      simpa using this
  rw [PhysicalSelectedSimpleCrossing, hMi]
  constructor
  · rintro ⟨hpole, u, hu0, hMu, hsimp, hM, hcount⟩
    refine ⟨hpole, u ∘ e, ?_, ?_, ?_, hHerm.2 hM, ?_⟩
    · simpa [hpiv.symm] using hu0
    · rw [← hMeig, hcomp]
      exact hMu
    · intro w hw
      obtain ⟨c, hc⟩ := hsimp (w ∘ e.symm) ((hMeig w).2 hw)
      refine ⟨c, ?_⟩
      funext a
      have := congrFun hc (e a)
      simpa using this
    · rw [← eigenCount_Iio_reindex e (hHerm.2 hM) hM E]
      exact hcount
  · rintro ⟨hpole, u, hu0, hMu, hsimp, hM, hcount⟩
    refine ⟨hpole, u ∘ e.symm, ?_, (hMeig u).2 hMu, ?_, hHerm.1 hM, ?_⟩
    · simpa [hpiv] using hu0
    · intro w hw
      have hw' : M *ᵥ (w ∘ e) = (E : ℂ) • (w ∘ e) := by
        rw [← hMeig, hcomp]
        exact hw
      obtain ⟨c, hc⟩ := hsimp _ hw'
      refine ⟨c, ?_⟩
      rw [← hcomp w, hc]
      rfl
    · rw [eigenCount_Iio_reindex e hM (hHerm.1 hM) E]
      exact hcount

/-- **Exhaustive selected-simple cover with chart-consistent physical data.**
The union over pivots of the selected-simple decoded images is exactly the
chart-free physical good set: every reduced coordinate admitting a crossing
with one-dimensional eigenspace, pole-free energy and fixed additive rank is
decoded by some chart, and conversely. -/
theorem iUnion_physicalSelectedSimpleImage_eq_goodSet
    (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V.IsHermitian) :
    (⋃ i : Fin d, physicalSelectedSimpleImage α R (physicalChartCoupling C)
        (physicalChartPotential V) i) =
      physicalSelectedSimpleGoodSet α R C V := by
  ext K
  simp only [Set.mem_iUnion, physicalSelectedSimpleImage]
  constructor
  · rintro ⟨i, hK⟩
    obtain ⟨E, hE⟩ := (mem_physicalSelectedSimpleDecode_image_iff α R i _ _
      (physicalChartPotential_isHermitian hV i) K).1 hK
    obtain ⟨hpole, u, hu0, hMu, hsimp, hM, hcount⟩ :=
      (physicalSelectedSimpleCrossing_iff_global α R C V i K E).1 hE
    refine ⟨E, hpole, u, ?_, hMu, hsimp, hM, hcount⟩
    intro h
    exact hu0 (by rw [h]; rfl)
  · rintro ⟨E, hpole, u, hu0, hMu, hsimp, hM, hcount⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
    refine ⟨i, (mem_physicalSelectedSimpleDecode_image_iff α R i _ _
      (physicalChartPotential_isHermitian hV i) K).2 ⟨E, ?_⟩⟩
    exact (physicalSelectedSimpleCrossing_iff_global α R C V i K E).2
      ⟨hpole, u, hi, hMu, hsimp, hM, hcount⟩

/-- The chart-free physical good set is Borel measurable. -/
theorem measurableSet_physicalSelectedSimpleGoodSet
    (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V.IsHermitian) :
    MeasurableSet (physicalSelectedSimpleGoodSet α R C V) := by
  rw [← iUnion_physicalSelectedSimpleImage_eq_goodSet α R C V hV]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_physicalSelectedSimpleImage α R _ _
      (physicalChartPotential_isHermitian hV) i

/-- **Exact physical selected-simple coarea formula on the full good set.**
For fixed exterior coordinates `R`, coupling `C`, Hermitian potential `V` and
zero-based rank `α`, and every `g ≥ 0`,
`∫_{good set} g = ∑_i ∫_{D_i} ρ_i · g ∘ G_i`, where `D_i` are the measurable,
deterministically disjointized selected-simple sources, `G_i` the direct
physical decoders, and `ρ_i = canonicalProjectiveAffineDensity z *
|det (E I - B)|² * vᴴ 𝒟(E) v`.  Sizes and exterior data are
fixed; no limit is taken. -/
theorem lintegral_physicalSelectedSimpleGoodSet
    (α : ℕ) (R : HermitianCoordinateSpace dR)
    (C : Matrix (Fin dR) (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) (hV : V.IsHermitian)
    (g : HermitianCoordinateSpace d → ℝ≥0∞) :
    (∫⁻ K in physicalSelectedSimpleGoodSet α R C V, g K) =
      ∑ i : Fin d, ∫⁻ x in physicalSelectedSimpleDisjointSource α R
          (physicalChartCoupling C) (physicalChartPotential V) i,
        ENNReal.ofReal (physicalSchurDecoderDensity i
          (physicalCoareaT (hermitianOfFinCoordinates dR R).1 (physicalChartCoupling C i)) x) *
        g (physicalSelectedSimpleDecode R i (physicalChartCoupling C i)
          (physicalChartPotential V i) x) := by
  rw [← iUnion_physicalSelectedSimpleImage_eq_goodSet α R C V hV]
  exact lintegral_iUnion_physicalSelectedSimpleImage α R _ _
    (physicalChartPotential_isHermitian hV) g

end ConsistentData

end CoareaNative.BlockBand
