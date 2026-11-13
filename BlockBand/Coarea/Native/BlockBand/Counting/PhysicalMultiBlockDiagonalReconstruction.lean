module
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockProductClosure
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalBlockConditioningReconstruction
public import BlockBand.Coarea.Native.BlockBand.LinearAlgebra.RegulatedSchurMeasurability

/-!
# Simultaneous diagonal-block reconstruction

The within-block upper-triangular coordinates of all diagonal blocks of the Gaussian ring
are extended by zero, reassembled into a site matrix, reindexed by the block-GUE index and
divided by `sqrt c`.  The resulting map is measurable and recovers, sample by sample, the
normalized block-diagonal part of the physical matrix as a Hermitian matrix.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix MeasureTheory
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Membership of an explicitly oriented physical pair in the all-diagonal finset. -/
@[simp] theorem mk_mem_allDiagonalUpperPairs_iff (p : Params)
    (a b : Site p.n p.W) (h : siteLE p a b) :
    (⟨(a,b),h⟩ : UpperPair p) ∈ allDiagonalUpperPairs p ↔ a.1 = b.1 :=
  mem_allDiagonalUpperPairs_iff p _

/-- Extend the simultaneous diagonal coordinate vector by zero. -/
def extendAllDiagonalCoordinates (p : Params)
    (u : allDiagonalUpperPairs p → ℂ) (q : UpperPair p) : ℂ := by
  classical
  exact if h : q ∈ allDiagonalUpperPairs p then u ⟨q,h⟩ else 0

/-- Zero-extension is measurable in the finite coordinate vector. -/
theorem measurable_extendAllDiagonalCoordinates (p : Params) :
    Measurable (extendAllDiagonalCoordinates p) := by
  rw [measurable_pi_iff]
  intro q
  by_cases h : q ∈ allDiagonalUpperPairs p
  · simpa [extendAllDiagonalCoordinates, h] using
      (measurable_pi_apply (⟨q,h⟩ : allDiagonalUpperPairs p))
  · simp [extendAllDiagonalCoordinates, h]

/-- On samples, zero-extension selects precisely within-block upper entries. -/
theorem Law.extendAllDiagonalCoordinates_apply {p : Params} (M : Law p)
    (ω : M.Ω) (a b : Site p.n p.W) (h : siteLE p a b) :
    extendAllDiagonalCoordinates p (M.allDiagonalUpperCoordinates ω) ⟨(a,b),h⟩ =
      if a.1 = b.1 then M.H ω a b else 0 := by
  dsimp only [extendAllDiagonalCoordinates]
  split_ifs with hm hb
  · rfl
  · exact False.elim (hb ((mk_mem_allDiagonalUpperPairs_iff p a b h).1 hm))
  · exfalso
    apply hm
    exact (mk_mem_allDiagonalUpperPairs_iff p a b h).2 (by assumption)
  · rfl

/-- Upper-coordinate reconstruction gives the block-diagonal part entrywise. -/
theorem Law.matrixOfUpperCoordinates_allDiagonal {p : Params} (M : Law p)
    (ω : M.Ω) (a b : Site p.n p.W) :
    matrixOfUpperCoordinates p
      (extendAllDiagonalCoordinates p (M.allDiagonalUpperCoordinates ω)) a b =
      if a.1 = b.1 then M.H ω a b else 0 := by
  by_cases h : siteLE p a b
  · simp only [matrixOfUpperCoordinates, h]
    change extendAllDiagonalCoordinates p (M.allDiagonalUpperCoordinates ω) ⟨(a,b),h⟩ =
      if a.1 = b.1 then M.H ω a b else 0
    rw [M.extendAllDiagonalCoordinates_apply ω a b h]
  · have hba := siteLE_reverse_of_not p a b h
    simp only [matrixOfUpperCoordinates, h]
    change star (extendAllDiagonalCoordinates p
      (M.allDiagonalUpperCoordinates ω) ⟨(b,a),hba⟩) =
      if a.1 = b.1 then M.H ω a b else 0
    rw [M.extendAllDiagonalCoordinates_apply ω b a hba]
    have hH := congrFun (congrFun (M.H_hermitian ω) a) b
    simp only [Matrix.conjTranspose_apply] at hH
    by_cases hb : a.1 = b.1
    · simp [hb, hH]
    · have hbr : b.1 ≠ a.1 := Ne.symm hb
      simp [hb, hbr]

/-- Reindex and divide a physical site matrix by `sqrt c`. -/
def normalizedReindexMatrix (p : Params)
    (A : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) :
    Matrix (BlockGUE.Index (physicalBlockSizes p))
      (BlockGUE.Index (physicalBlockSizes p)) ℂ :=
  fun x y => ((Real.sqrt p.c)⁻¹ : ℂ) * A (allDiagonalSite x) (allDiagonalSite y)

/-- Raw simultaneous diagonal-block reconstruction. -/
def reconstructAllDiagonalRaw (p : Params) (u : allDiagonalUpperPairs p → ℂ) :=
  normalizedReindexMatrix p
    (matrixOfUpperCoordinates p (extendAllDiagonalCoordinates p u))

/-- The raw reconstruction is measurable. -/
theorem measurable_reconstructAllDiagonalRaw (p : Params) :
    Measurable (reconstructAllDiagonalRaw p) := by
  have hm := (measurable_matrixOfUpperCoordinates p).comp
    (measurable_extendAllDiagonalCoordinates p)
  rw [Matrix.measurable_iff]
  intro x y
  exact (Matrix.measurable_iff.mp hm (allDiagonalSite x) (allDiagonalSite y)).const_mul _

/-- Bundle the Hermitian part, making the reconstruction total on arbitrary vectors. -/
def reconstructAllDiagonalHermitian (p : Params)
    (u : allDiagonalUpperPairs p → ℂ) :
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) :=
  ⟨matrixHermitianPart (reconstructAllDiagonalRaw p u),
    matrixHermitianPart_isHermitian _⟩

/-- The bundled reconstruction is measurable. -/
theorem measurable_reconstructAllDiagonalHermitian (p : Params) :
    Measurable (reconstructAllDiagonalHermitian p) := by
  apply Measurable.subtype_mk
  exact Measurable.matrixHermitianPart (measurable_reconstructAllDiagonalRaw p)

/-- Equality of outer physical sites is equality of the normalized block labels. -/
theorem allDiagonalSite_fst_eq_iff {p : Params}
    (x y : BlockGUE.Index (physicalBlockSizes p)) :
    (allDiagonalSite x).1 = (allDiagonalSite y).1 ↔ x.1 = y.1 := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa [allDiagonalSite, ZMod.val_natCast_of_lt x.1.isLt,
      ZMod.val_natCast_of_lt y.1.isLt] using hv
  · intro h
    simp [allDiagonalSite, h]

/-- On physical samples, the raw reconstruction is exactly the normalized block matrix. -/
theorem Law.reconstructAllDiagonalRaw_apply {p : Params} (M : Law p) (ω : M.Ω) :
    reconstructAllDiagonalRaw p (M.allDiagonalUpperCoordinates ω) =
      M.normalizedAllDiagonalBlocks ω := by
  ext x y
  rw [reconstructAllDiagonalRaw, normalizedReindexMatrix,
    M.matrixOfUpperCoordinates_allDiagonal]
  by_cases h : x.1 = y.1
  · have hs := (allDiagonalSite_fst_eq_iff x y).2 h
    simp [Law.normalizedAllDiagonalBlocks, h, hs]
  · have hs : (allDiagonalSite x).1 ≠ (allDiagonalSite y).1 :=
      fun hs => h ((allDiagonalSite_fst_eq_iff x y).1 hs)
    simp [Law.normalizedAllDiagonalBlocks, h, hs]

/-- Hermitian projection fixes an already Hermitian matrix. -/
theorem matrixHermitianPart_eq_self {ι : Type*} {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) : matrixHermitianPart A = A := by
  rw [matrixHermitianPart, hA]
  ext i j
  simp
  ring

/-- Pointwise recovery of the bundled simultaneous diagonal matrix. -/
theorem Law.reconstructAllDiagonalHermitian_apply {p : Params} (M : Law p) (ω : M.Ω) :
    reconstructAllDiagonalHermitian p (M.allDiagonalUpperCoordinates ω) =
      M.normalizedAllDiagonalBlocksHermitian ω := by
  apply Subtype.ext
  change matrixHermitianPart
      (reconstructAllDiagonalRaw p (M.allDiagonalUpperCoordinates ω)) =
    M.normalizedAllDiagonalBlocks ω
  calc
    _ = matrixHermitianPart (M.normalizedAllDiagonalBlocks ω) := by
      congr 1
      exact M.reconstructAllDiagonalRaw_apply ω
    _ = M.normalizedAllDiagonalBlocks ω :=
      matrixHermitianPart_eq_self (M.normalizedAllDiagonalBlocks_isHermitian ω)

end GaussianRing
end CoareaNative.BlockBand
