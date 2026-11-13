module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockDiagonalReconstruction

/-!
# Deterministic reconstruction of the physical multi-block coordinates

This module reconstructs the normalized off-diagonal Hermitian background from the
complementary physical upper-coordinate vector.  Together with the diagonal
reconstruction, this closes the deterministic input needed for the paper's simultaneous
multi-block count transport.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix MeasureTheory
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Membership of an explicitly oriented physical pair in the off-diagonal finset. -/
@[simp] theorem mk_mem_allOffDiagonalUpperPairs_iff (p : Params)
    (a b : Site p.n p.W) (h : siteLE p a b) :
    (⟨(a,b),h⟩ : UpperPair p) ∈ allOffDiagonalUpperPairs p ↔ a.1 ≠ b.1 :=
  mem_allOffDiagonalUpperPairs_iff p _

/-- Extend the simultaneous off-diagonal coordinate vector by zero. -/
def extendAllOffDiagonalCoordinates (p : Params)
    (u : allOffDiagonalUpperPairs p → ℂ) (q : UpperPair p) : ℂ := by
  classical
  exact if h : q ∈ allOffDiagonalUpperPairs p then u ⟨q,h⟩ else 0

/-- Zero-extension is measurable in the finite coordinate vector. -/
theorem measurable_extendAllOffDiagonalCoordinates (p : Params) :
    Measurable (extendAllOffDiagonalCoordinates p) := by
  rw [measurable_pi_iff]
  intro q
  by_cases h : q ∈ allOffDiagonalUpperPairs p
  · simpa [extendAllOffDiagonalCoordinates, h] using
      (measurable_pi_apply (⟨q,h⟩ : allOffDiagonalUpperPairs p))
  · simp [extendAllOffDiagonalCoordinates, h]

/-- On samples, zero-extension selects precisely cross-block upper entries. -/
theorem Law.extendAllOffDiagonalCoordinates_apply {p : Params} (M : Law p)
    (ω : M.Ω) (a b : Site p.n p.W) (h : siteLE p a b) :
    extendAllOffDiagonalCoordinates p (M.allOffDiagonalUpperCoordinates ω) ⟨(a,b),h⟩ =
      if a.1 ≠ b.1 then M.H ω a b else 0 := by
  dsimp only [extendAllOffDiagonalCoordinates]
  split_ifs with hm hb
  · rfl
  · exact False.elim (hb ((mk_mem_allOffDiagonalUpperPairs_iff p a b h).1 hm))
  · exfalso
    apply hm
    exact (mk_mem_allOffDiagonalUpperPairs_iff p a b h).2 (by assumption)
  · rfl

/-- Upper-coordinate reconstruction gives the off-diagonal part entrywise. -/
theorem Law.matrixOfUpperCoordinates_allOffDiagonal {p : Params} (M : Law p)
    (ω : M.Ω) (a b : Site p.n p.W) :
    matrixOfUpperCoordinates p
      (extendAllOffDiagonalCoordinates p (M.allOffDiagonalUpperCoordinates ω)) a b =
      if a.1 ≠ b.1 then M.H ω a b else 0 := by
  by_cases h : siteLE p a b
  · simp only [matrixOfUpperCoordinates, h]
    change extendAllOffDiagonalCoordinates p
      (M.allOffDiagonalUpperCoordinates ω) ⟨(a,b),h⟩ =
      if a.1 ≠ b.1 then M.H ω a b else 0
    rw [M.extendAllOffDiagonalCoordinates_apply ω a b h]
  · have hba := siteLE_reverse_of_not p a b h
    simp only [matrixOfUpperCoordinates, h]
    change star (extendAllOffDiagonalCoordinates p
      (M.allOffDiagonalUpperCoordinates ω) ⟨(b,a),hba⟩) =
      if a.1 ≠ b.1 then M.H ω a b else 0
    rw [M.extendAllOffDiagonalCoordinates_apply ω b a hba]
    have hH := congrFun (congrFun (M.H_hermitian ω) a) b
    simp only [Matrix.conjTranspose_apply] at hH
    by_cases hb : a.1 = b.1
    · simp [hb]
    · have hbr : b.1 ≠ a.1 := Ne.symm hb
      simp [hb, hbr, hH]

/-- Raw simultaneous off-diagonal reconstruction. -/
def reconstructAllOffDiagonalRaw (p : Params)
    (u : allOffDiagonalUpperPairs p → ℂ) :=
  normalizedReindexMatrix p
    (matrixOfUpperCoordinates p (extendAllOffDiagonalCoordinates p u))

/-- The raw off-diagonal reconstruction is measurable. -/
theorem measurable_reconstructAllOffDiagonalRaw (p : Params) :
    Measurable (reconstructAllOffDiagonalRaw p) := by
  have hm := (measurable_matrixOfUpperCoordinates p).comp
    (measurable_extendAllOffDiagonalCoordinates p)
  rw [Matrix.measurable_iff]
  intro x y
  exact (Matrix.measurable_iff.mp hm (allDiagonalSite x) (allDiagonalSite y)).const_mul _

/-- Bundle the Hermitian part, making off-diagonal reconstruction total on all vectors. -/
def reconstructAllOffDiagonalHermitian (p : Params)
    (u : allOffDiagonalUpperPairs p → ℂ) :
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) :=
  ⟨matrixHermitianPart (reconstructAllOffDiagonalRaw p u),
    matrixHermitianPart_isHermitian _⟩

/-- The bundled off-diagonal reconstruction is measurable. -/
theorem measurable_reconstructAllOffDiagonalHermitian (p : Params) :
    Measurable (reconstructAllOffDiagonalHermitian p) := by
  apply Measurable.subtype_mk
  exact Measurable.matrixHermitianPart (measurable_reconstructAllOffDiagonalRaw p)

/-- On physical samples, raw reconstruction is exactly the normalized cross-block matrix. -/
theorem Law.reconstructAllOffDiagonalRaw_apply {p : Params} (M : Law p) (ω : M.Ω) :
    reconstructAllOffDiagonalRaw p (M.allOffDiagonalUpperCoordinates ω) =
      (M.normalizedOffDiagonalBackground ω).1 := by
  ext x y
  rw [reconstructAllOffDiagonalRaw, normalizedReindexMatrix,
    M.matrixOfUpperCoordinates_allOffDiagonal]
  by_cases h : x.1 = y.1
  · have hs := (allDiagonalSite_fst_eq_iff x y).2 h
    simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero,
      Law.normalizedOffDiagonalBackground, Law.normalizedPhysicalMatrix]
    change 0 = ((Real.sqrt p.c)⁻¹ : ℂ) *
      M.H ω (allDiagonalSite x) (allDiagonalSite y) -
        M.normalizedAllDiagonalBlocks ω x y
    rw [M.normalizedAllDiagonalBlocks_apply_of_fst_eq ω x y h]
    simp
  · have hs : (allDiagonalSite x).1 ≠ (allDiagonalSite y).1 :=
      fun hs => h ((allDiagonalSite_fst_eq_iff x y).1 hs)
    simp only [hs, ne_eq, not_false_eq_true, ↓reduceIte,
      Law.normalizedOffDiagonalBackground, Law.normalizedPhysicalMatrix]
    change ((Real.sqrt p.c)⁻¹ : ℂ) *
      M.H ω (allDiagonalSite x) (allDiagonalSite y) =
        ((Real.sqrt p.c)⁻¹ : ℂ) *
          M.H ω (allDiagonalSite x) (allDiagonalSite y) -
            M.normalizedAllDiagonalBlocks ω x y
    rw [M.normalizedAllDiagonalBlocks_apply_of_fst_ne ω x y h]
    simp

/-- Pointwise recovery of the bundled simultaneous off-diagonal background. -/
theorem Law.reconstructAllOffDiagonalHermitian_apply
    {p : Params} (M : Law p) (ω : M.Ω) :
    reconstructAllOffDiagonalHermitian p (M.allOffDiagonalUpperCoordinates ω) =
      M.normalizedOffDiagonalBackground ω := by
  apply Subtype.ext
  change matrixHermitianPart
      (reconstructAllOffDiagonalRaw p (M.allOffDiagonalUpperCoordinates ω)) =
    (M.normalizedOffDiagonalBackground ω).1
  calc
    _ = matrixHermitianPart (M.normalizedOffDiagonalBackground ω).1 := by
      congr 1
      exact M.reconstructAllOffDiagonalRaw_apply ω
    _ = (M.normalizedOffDiagonalBackground ω).1 :=
      matrixHermitianPart_eq_self (M.normalizedOffDiagonalBackground ω).2

/-- The two complementary coordinate reconstructions for a physical Gaussian-ring law. -/
def Law.physicalMultiBlockCoordinateReconstruction {p : Params} (M : Law p) :
    PhysicalMultiBlockCoordinateReconstruction M where
  diagonal := reconstructAllDiagonalHermitian p
  offDiagonal := reconstructAllOffDiagonalHermitian p
  measurable_diagonal := measurable_reconstructAllDiagonalHermitian p
  measurable_offDiagonal := measurable_reconstructAllOffDiagonalHermitian p
  diagonal_apply := M.reconstructAllDiagonalHermitian_apply
  offDiagonal_apply := M.reconstructAllOffDiagonalHermitian_apply

/-- Unconditional physical multi-block count transport, after deterministic reconstruction
of both complementary upper-coordinate groups. -/
theorem Law.physicalMultiBlockCountTransport_unconditional {p : Params} (M : Law p) :
    PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
      M.normalizedAllDiagonalBlocksGUE (fun A => A)
      M.normalizedPhysicalIntervalCount :=
  M.physicalMultiBlockCoordinateReconstruction.countTransport

end GaussianRing
end CoareaNative.BlockBand
