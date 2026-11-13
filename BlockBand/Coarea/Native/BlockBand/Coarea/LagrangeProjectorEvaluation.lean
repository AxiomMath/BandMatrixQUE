module

public import BlockBand.Coarea.Native.BlockBand.Coarea.LagrangeProjectorFunctionalCalculus

/-!
# Evaluation of the Hermitian Lagrange projector

This module performs the finite-index bookkeeping left after diagonalizing each
Lagrange factor.  It identifies the complete diagonalized product with the
one-coordinate projection: every factor is one at the selected eigenvalue,
whereas at every other eigenbasis coordinate the factor indexed by that
coordinate is zero.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix

/-- The ordered rank corresponding to an index in Mathlib's Hermitian
eigenvector basis. -/
def eigenbasisOrderedRank (d : ℕ) (i : Fin d) : HermitianEigenRank d :=
  Fin.rev
    ((Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin d)))).symm i)

@[simp] theorem orderedEigenbasisIndex_eigenbasisOrderedRank
    (d : ℕ) (i : Fin d) :
    orderedEigenbasisIndex d (eigenbasisOrderedRank d i) = i := by
  simp [orderedEigenbasisIndex, eigenbasisOrderedRank]

@[simp] theorem eigenbasisOrderedRank_orderedEigenbasisIndex
    (d : ℕ) (r : HermitianEigenRank d) :
    eigenbasisOrderedRank d (orderedEigenbasisIndex d r) = r := by
  simp [orderedEigenbasisIndex, eigenbasisOrderedRank]

/-- Mathlib's eigenvalue at an arbitrary eigenbasis index, rewritten using the
project's increasing ordered rank. -/
theorem eigenvalues_eq_orderedEigenvalue_eigenbasisOrderedRank
    {d : ℕ} (A : HermitianMatrix (Fin d)) (i : Fin d) :
    A.property.eigenvalues i =
      orderedEigenvalue A (eigenbasisOrderedRank d i) := by
  rw [← eigenvalues_orderedEigenbasisIndex A
    (eigenbasisOrderedRank d i)]
  simp

@[simp] theorem mem_otherHermitianEigenRanks
    {d : ℕ} {r s : HermitianEigenRank d} :
    s ∈ otherHermitianEigenRanks d r ↔ s ≠ r := by
  simp only [otherHermitianEigenRanks, List.mem_filter, List.mem_ofFn']
  simp

/-- The scalar diagonal entry of the full Lagrange product is the indicator of
the selected eigenbasis coordinate. -/
theorem prod_lagrangeDiagonalEntry
    {d : ℕ} (x : HermitianCoordinateSpace d)
    (hsep : ((hermitianOfFinCoordinates d x : HermitianMatrix (Fin d)) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable)
    (r : HermitianEigenRank d) (i : Fin d) :
    (List.map (fun s =>
      (((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
        orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ)⁻¹ *
      (((hermitianOfFinCoordinates d x).property.eigenvalues i : ℂ) -
        (orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℂ))))
      (otherHermitianEigenRanks d r)).prod =
      if i = orderedEigenbasisIndex d r then 1 else 0 := by
  classical
  by_cases hi : i = orderedEigenbasisIndex d r
  · simp only [hi, ite_eq_left]
    apply List.prod_eq_one
    intro z hz
    rw [List.mem_map] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have hsr : s ≠ r := mem_otherHermitianEigenRanks.mp hs
    rw [eigenvalues_orderedEigenbasisIndex]
    have hne : ((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
        orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast orderedEigenvalue_sub_ne_zero_of_separable
        (hermitianOfFinCoordinates d x) hsep (Ne.symm hsr)
    simpa using inv_mul_cancel₀ hne
  · simp only [hi]
    apply List.prod_eq_zero
    rw [List.mem_map]
    let s := eigenbasisOrderedRank d i
    have hsr : s ≠ r := by
      intro h
      apply hi
      rw [← h]
      exact (orderedEigenbasisIndex_eigenbasisOrderedRank d i).symm
    refine ⟨s, mem_otherHermitianEigenRanks.mpr hsr, ?_⟩
    rw [eigenvalues_eq_orderedEigenvalue_eigenbasisOrderedRank]
    simp [s]

/-- The full ordered Lagrange product diagonalizes to the one-coordinate
projection at its ordered eigenvalue. -/
theorem diagonalize_hermitianLagrangeSpectralProjector
    {d : ℕ} (x : HermitianCoordinateSpace d)
    (hsep : ((hermitianOfFinCoordinates d x : HermitianMatrix (Fin d)) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable)
    (r : HermitianEigenRank d) :
    (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
      (star (hermitianOfFinCoordinates d x).property.eigenvectorUnitary))
        (hermitianLagrangeSpectralProjector d r x) =
      orderedEigenbasisProjection d r := by
  classical
  simp only [hermitianLagrangeSpectralProjector, map_list_prod,
    List.map_map]
  rw [show
    List.map
        ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
          (star (hermitianOfFinCoordinates d x).property.eigenvectorUnitary)) ∘
          fun s => hermitianSpectralLagrangeFactor d r s x)
        (otherHermitianEigenRanks d r) =
      List.map (fun s => Matrix.diagonal (fun i =>
        (((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
          orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ)⁻¹ *
        (((hermitianOfFinCoordinates d x).property.eigenvalues i : ℂ) -
          (orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℂ)))))
        (otherHermitianEigenRanks d r) by
      apply List.map_congr_left
      intro s hs
      exact diagonalize_hermitianSpectralLagrangeFactor x r s]
  let f : HermitianEigenRank d → Fin d → ℂ := fun s i =>
    (((orderedEigenvalue (hermitianOfFinCoordinates d x) r -
      orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℝ) : ℂ)⁻¹ *
    (((hermitianOfFinCoordinates d x).property.eigenvalues i : ℂ) -
      (orderedEigenvalue (hermitianOfFinCoordinates d x) s : ℂ)))
  change
    (List.map (Matrix.diagonal ∘ f)
      (otherHermitianEigenRanks d r)).prod =
      orderedEigenbasisProjection d r
  rw [← List.map_map, list_prod_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, List.map_map]
    dsimp only [Function.comp_apply, f]
    simp only [orderedEigenbasisProjection, Matrix.diagonal_apply_eq]
    exact prod_lagrangeDiagonalEntry x hsep r i
  · simp [orderedEigenbasisProjection, hij]

/-- Conjugating the diagonal formula back gives the Lagrange projector
explicitly as the unitary conjugate of a one-coordinate projection. -/
theorem hermitianLagrangeSpectralProjector_eq_unitaryConj
    {d : ℕ} (x : HermitianCoordinateSpace d)
    (hsep : ((hermitianOfFinCoordinates d x : HermitianMatrix (Fin d)) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable)
    (r : HermitianEigenRank d) :
    hermitianLagrangeSpectralProjector d r x =
      (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
        (star (hermitianOfFinCoordinates d x).property.eigenvectorUnitary)).symm
          (orderedEigenbasisProjection d r) := by
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
    (star (hermitianOfFinCoordinates d x).property.eigenvectorUnitary)
  apply Φ.injective
  exact (diagonalize_hermitianLagrangeSpectralProjector x hsep r).trans
    (Φ.apply_symm_apply (orderedEigenbasisProjection d r)).symm

/-- Conjugation by the Hermitian eigenvector unitary preserves matrix rank. -/
theorem rank_conjStarAlgAut_star_eigenvectorUnitary
    {d : ℕ} (A : HermitianMatrix (Fin d))
    (M : Matrix (Fin d) (Fin d) ℂ) :
    ((Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
      (star A.property.eigenvectorUnitary)) M).rank = M.rank := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [← Matrix.UnitaryGroup.inv_apply (star A.property.eigenvectorUnitary)]
  rw [
    Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (Matrix.UnitaryGroup.det_isUnit
        (star A.property.eigenvectorUnitary)⁻¹),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (Matrix.UnitaryGroup.det_isUnit (star A.property.eigenvectorUnitary))]

/-- The diagonal coordinate projector has matrix rank one. -/
theorem rank_orderedEigenbasisProjection
    {d : ℕ} (r : HermitianEigenRank d) :
    (orderedEigenbasisProjection d r).rank = 1 := by
  classical
  rw [orderedEigenbasisProjection, Matrix.rank_diagonal]
  simp

/-- The Lagrange product satisfies the complete correctness interface on the
simple-spectrum locus. -/
theorem hermitianLagrangeProjectorCorrect_of_separable
    {d : ℕ} (x : HermitianCoordinateSpace d)
    (hsep : ((hermitianOfFinCoordinates d x : HermitianMatrix (Fin d)) :
      Matrix (Fin d) (Fin d) ℂ).charpoly.Separable)
    (r : HermitianEigenRank d) :
    HermitianLagrangeProjectorCorrect d r x := by
  classical
  let A := hermitianOfFinCoordinates d x
  let P := hermitianLagrangeSpectralProjector d r x
  let D := orderedEigenbasisProjection d r
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ)
    (star A.property.eigenvectorUnitary)
  have hdiag : Φ P = D := by
    exact diagonalize_hermitianLagrangeSpectralProjector x hsep r
  have hDstar : star D = D := by
    ext i j
    by_cases hij : i = j
    · simp [D, orderedEigenbasisProjection, Matrix.star_apply, hij]
    · simp [D, orderedEigenbasisProjection, Matrix.star_apply, hij, Ne.symm hij]
  have hDidem : D * D = D := by
    ext i j
    by_cases hij : i = j <;>
      simp [D, orderedEigenbasisProjection, hij]
  refine
    { nonzero := ?_
      rank_one := ?_
      selfAdjoint := ?_
      idempotent := ?_
      left_eigen := ?_ }
  · intro hP
    have : D = 0 := by simpa [P, hP] using hdiag.symm
    have hii := congrArg
      (fun M : Matrix (Fin d) (Fin d) ℂ =>
        M (orderedEigenbasisIndex d r) (orderedEigenbasisIndex d r)) this
    simp [D, orderedEigenbasisProjection] at hii
  · rw [← rank_conjStarAlgAut_star_eigenvectorUnitary A P, hdiag]
    exact rank_orderedEigenbasisProjection r
  · change star P = P
    apply Φ.injective
    calc
      Φ (star P) = star (Φ P) := map_star Φ P
      _ = star D := by rw [hdiag]
      _ = D := hDstar
      _ = Φ P := hdiag.symm
  · change P * P = P
    apply Φ.injective
    calc
      Φ (P * P) = Φ P * Φ P := map_mul Φ P P
      _ = D * D := by rw [hdiag]
      _ = D := hDidem
      _ = Φ P := hdiag.symm
  · change
      (A : Matrix (Fin d) (Fin d) ℂ) * P =
        ((orderedEigenvalue A r : ℝ) : ℂ) • P
    apply Φ.injective
    calc
      Φ ((A : Matrix (Fin d) (Fin d) ℂ) * P) =
          Φ (A : Matrix (Fin d) (Fin d) ℂ) * Φ P := map_mul Φ _ _
      _ = Matrix.diagonal (fun i => ((A.property.eigenvalues i : ℝ) : ℂ)) * D := by
        rw [hdiag]
        exact congrArg (fun M => M * D)
          A.property.conjStarAlgAut_star_eigenvectorUnitary
      _ = ((orderedEigenvalue A r : ℝ) : ℂ) • D := by
        ext i j
        by_cases hij : i = j
        · subst j
          by_cases hir : i = orderedEigenbasisIndex d r
          · subst i
            simp [D, orderedEigenbasisProjection,
              eigenvalues_orderedEigenbasisIndex]
          · simp [D, orderedEigenbasisProjection, hir]
        · simp [D, orderedEigenbasisProjection, hij]
      _ = ((orderedEigenvalue A r : ℝ) : ℂ) • Φ P := by rw [hdiag]
      _ = Φ (((orderedEigenvalue A r : ℝ) : ℂ) • P) := by
        rw [map_smul]

/-- The finite-dimensional Hermitian spectral theorem supplies the
functional-calculus interface unconditionally. -/
theorem hermitianLagrangeFunctionalCalculus (d : ℕ) :
    HermitianLagrangeFunctionalCalculus d where
  correct x hx r :=
    hermitianLagrangeProjectorCorrect_of_separable x hx r

end CoareaNative.BlockBand
