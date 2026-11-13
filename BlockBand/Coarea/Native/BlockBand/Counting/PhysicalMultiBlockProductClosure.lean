module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockProductIndependence

/-!
# Complementary physical upper-coordinate groups

This module identifies the exact complementary coordinate finsets needed for the final
matrix reconstruction step and packages only that deterministic reconstruction data.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand
open Matrix MeasureTheory ProbabilityTheory Set
namespace GaussianRing
local instance (p : Params) : NeZero p.n := p.neZero_n

/-- All physical upper coordinates lying in a diagonal block. -/
def allDiagonalUpperPairs (p : Params) : Finset (UpperPair p) := by
  classical
  let _ : Finite (UpperPair p) := by unfold UpperPair; infer_instance
  letI := Fintype.ofFinite (UpperPair p)
  exact Finset.univ.filter fun q => q.1.1.1 = q.1.2.1

/-- All physical upper coordinates joining distinct blocks. -/
def allOffDiagonalUpperPairs (p : Params) : Finset (UpperPair p) := by
  classical
  let _ : Finite (UpperPair p) := by unfold UpperPair; infer_instance
  letI := Fintype.ofFinite (UpperPair p)
  exact Finset.univ.filter fun q => q.1.1.1 ≠ q.1.2.1

@[simp] theorem mem_allDiagonalUpperPairs_iff (p : Params) (q : UpperPair p) :
    q ∈ allDiagonalUpperPairs p ↔ q.1.1.1 = q.1.2.1 := by
  classical simp [allDiagonalUpperPairs]

@[simp] theorem mem_allOffDiagonalUpperPairs_iff (p : Params) (q : UpperPair p) :
    q ∈ allOffDiagonalUpperPairs p ↔ q.1.1.1 ≠ q.1.2.1 := by
  classical simp [allOffDiagonalUpperPairs]

/-- The diagonal and cross-block coordinate sets are disjoint. -/
theorem allDiagonalUpperPairs_disjoint_offDiagonal (p : Params) :
    Disjoint (allDiagonalUpperPairs p) (allOffDiagonalUpperPairs p) := by
  classical
  rw [Finset.disjoint_left]
  intro q hd ho
  exact (mem_allOffDiagonalUpperPairs_iff p q).1 ho
    ((mem_allDiagonalUpperPairs_iff p q).1 hd)

/-- The two concrete restricted upper-coordinate vectors. -/
def Law.allDiagonalUpperCoordinates {p : Params} (M : Law p) (ω : M.Ω) :
    allDiagonalUpperPairs p → ℂ := fun q => M.H ω q.1.1.1 q.1.1.2

def Law.allOffDiagonalUpperCoordinates {p : Params} (M : Law p) (ω : M.Ω) :
    allOffDiagonalUpperPairs p → ℂ := fun q => M.H ω q.1.1.1 q.1.1.2

/-- The restricted coordinate vectors are measurable. -/
theorem Law.measurable_allDiagonalUpperCoordinates {p : Params} (M : Law p) :
    Measurable M.allDiagonalUpperCoordinates := by
  rw [measurable_pi_iff]
  intro q
  exact M.measurable_entry q.1.1.1 q.1.1.2

theorem Law.measurable_allOffDiagonalUpperCoordinates {p : Params} (M : Law p) :
    Measurable M.allOffDiagonalUpperCoordinates := by
  rw [measurable_pi_iff]
  intro q
  exact M.measurable_entry q.1.1.1 q.1.1.2

/-- The two complete coordinate groups are independent. -/
theorem Law.indepFun_allDiagonal_allOffDiagonal {p : Params} (M : Law p) :
    IndepFun M.allDiagonalUpperCoordinates M.allOffDiagonalUpperCoordinates M.P := by
  exact iIndepFun.indepFun_finset
    (allDiagonalUpperPairs p) (allOffDiagonalUpperPairs p)
    (allDiagonalUpperPairs_disjoint_offDiagonal p) M.upper_independent
    (fun q => M.measurable_entry q.1.1 q.1.2)

/-- Smallest remaining deterministic reconstruction interface.  It contains no
probabilistic assertion: only measurable maps from the two complementary coordinate
vectors and their pointwise recovery equations. -/
structure PhysicalMultiBlockCoordinateReconstruction {p : Params} (M : Law p) where
  diagonal : (allDiagonalUpperPairs p → ℂ) →
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p))
  offDiagonal : (allOffDiagonalUpperPairs p → ℂ) →
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p))
  measurable_diagonal : Measurable diagonal
  measurable_offDiagonal : Measurable offDiagonal
  diagonal_apply : ∀ ω,
    diagonal (M.allDiagonalUpperCoordinates ω) =
      M.normalizedAllDiagonalBlocksHermitian ω
  offDiagonal_apply : ∀ ω,
    offDiagonal (M.allOffDiagonalUpperCoordinates ω) =
      M.normalizedOffDiagonalBackground ω

/-- Deterministic reconstruction data closes grouped matrix independence. -/
theorem PhysicalMultiBlockCoordinateReconstruction.groupedIndependence
    {p : Params} {M : Law p} (h : PhysicalMultiBlockCoordinateReconstruction M) :
    PhysicalMultiBlockGroupedIndependence M := by
  have hi := M.indepFun_allDiagonal_allOffDiagonal.comp
    h.measurable_diagonal h.measurable_offDiagonal
  refine ⟨?_⟩
  rw [← funext h.offDiagonal_apply, ← funext h.diagonal_apply]
  exact hi.symm

/-- Hence the paper-facing transport follows from only deterministic reconstruction. -/
theorem PhysicalMultiBlockCoordinateReconstruction.countTransport
    {p : Params} {M : Law p} (h : PhysicalMultiBlockCoordinateReconstruction M) :
    PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
      M.normalizedAllDiagonalBlocksGUE (fun A => A)
      M.normalizedPhysicalIntervalCount :=
  h.groupedIndependence.countTransport

end GaussianRing
end CoareaNative.BlockBand
