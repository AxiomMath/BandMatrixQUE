module

public import BlockBand.Native.CEH.BlockBand.External.CEH.LocalLawContract
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEMatrixAdapter

/-!
# MDE adapter for the published CEH local law

The matrix Dyson equation used by the external CEH local law, in the vocabulary of the
regular-window statements: the two vocabularies share the imaginary part, the MDE density and the
relative matrix `Γ`, and the MDE has a unique solution for every Hermitian deformation, positive
variance parameter and spectral parameter in either nonreal half-plane.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand

open scoped ComplexOrder Matrix

/-- The local-law and regular-window vocabularies use the same matrix imaginary
part. -/
theorem cehImPart_eq_localETHImPart {N : ℕ} (M : CEHMatrix N) :
    cehImPart M = localETHImPart M := by
  rfl

/-- The local-law and regular-window vocabularies use the same normalized MDE
density. -/
theorem cehMDEDensity_eq_localETHMDEDensity {N : ℕ} (M : CEHMatrix N) :
    cehMDEDensity M = localETHMDEDensity M := by
  rfl

/-- The local-law and regular-window vocabularies use the same relative matrix
`Γ`. -/
theorem cehRelGamma_eq_localETHGamma {N : ℕ} (M : CEHMatrix N) :
    cehRelGamma M = localETHGamma M := by
  rfl

/-- The polynomial deformation bounds of the two statements are identical. -/
theorem cehDeformationBound_iff_localETHDeformationBound
    {N : ℕ} {κ C s : ℝ} {F : CEHMatrix N} :
    CEHDeformationBound κ C s F ↔ LocalETHDeformationBound κ C s F := by
  rfl

/-- The two matrix-MDE predicates are definitionally the same equation and sign condition. -/
theorem isCEHMDESolution_iff_isLocalETHMDESolution
    {N : ℕ} {s : ℝ} {F : CEHMatrix N} {z : ℂ} {M : CEHMatrix N} :
    IsCEHMDESolution s F z M ↔ IsLocalETHMDESolution s F z M := by
  constructor
  · rintro ⟨hinv, hpos⟩
    exact ⟨hinv, by simpa [cehImPart, localETHImPart] using hpos⟩
  · rintro ⟨hinv, hpos⟩
    exact ⟨hinv, by simpa [cehImPart, localETHImPart] using hpos⟩

/-- Existence of the unique matrix-MDE solution for every Hermitian deformation,
positive variance and nonreal spectral parameter. -/
theorem cehMDE_exists :
    ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (z : ℂ), z.im ≠ 0 →
      ∃ M : CEHMatrix N, IsCEHMDESolution s F.1 z M := by
  intro N s hs F z hz
  let M := CEH.hermitianMDEBranch F.2 hs z
  refine ⟨M, isCEHMDESolution_iff_isLocalETHMDESolution.mpr ?_⟩
  exact CEH.hermitianMDEBranch_isSolution F.2 hs hz

/-- Uniqueness of the matrix-MDE solution for Hermitian `F` and positive variance `s`, at every
spectral parameter `z`. -/
theorem cehMDE_unique :
    ∀ (N : ℕ) (s : ℝ), 0 < s →
    ∀ (F : HermitianMatrix (Fin N)) (z : ℂ) (M M' : CEHMatrix N),
      IsCEHMDESolution s F.1 z M → IsCEHMDESolution s F.1 z M' → M = M' := by
  intro N s hs F z M M' hM hM'
  by_cases hN : 0 < N
  · have hMl := isCEHMDESolution_iff_isLocalETHMDESolution.mp hM
    have hM'l := isCEHMDESolution_iff_isLocalETHMDESolution.mp hM'
    have hz : z.im ≠ 0 := by
      intro hz
      have hsign := CEH.normalizedTrace_im_sign hN hMl
      rw [hz, zero_mul] at hsign
      exact lt_irrefl 0 hsign
    exact (CEH.isLocalETHMDESolution_unique F.2 hs hz hMl).trans
      (CEH.isLocalETHMDESolution_unique F.2 hs hz hM'l).symm
  · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    exact Subsingleton.elim _ _

end CEHNative.BlockBand
