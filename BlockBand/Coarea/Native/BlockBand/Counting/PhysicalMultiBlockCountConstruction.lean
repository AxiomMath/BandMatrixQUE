module

public import BlockBand.Coarea.Native.BlockBand.Counting.NormalizedAllDiagonalBlocksGUE
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockCountTransport
public import Mathlib.Probability.HasLaw

/-!
# Physical multi-block count construction

This module reduces the physical PSSS transport to one exact finite-dimensional
product-coupling statement.  It constructs the normalized physical matrix, its
cross-block Hermitian background, the simultaneous diagonal-block GUE law, and their
pointwise decomposition.  The only other input, `PhysicalMultiBlockProductCoupling`,
records that the joint law of the background and diagonal matrix is the product of its
marginals: the measurable grouping consequence of upper-coordinate independence.  It
contains no spectral estimate or count assertion.  It holds for every law
(`PhysicalMultiBlockGroupedIndependence.productCoupling` applied to
`PhysicalMultiBlockCoordinateReconstruction.groupedIndependence` for
`Law.physicalMultiBlockCoordinateReconstruction`), and the resulting count transport is
`Law.physicalMultiBlockCountTransport_unconditional`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The full physical ring matrix, reindexed by block coordinates and divided by
`sqrt c`. -/
def Law.normalizedPhysicalMatrix {p : Params} (M : Law p) (ω : M.Ω) :
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) := by
  let A : Matrix (BlockGUE.Index (physicalBlockSizes p))
      (BlockGUE.Index (physicalBlockSizes p)) ℂ :=
    fun x y => ((Real.sqrt p.c)⁻¹ : ℂ) *
      M.H ω (allDiagonalSite x) (allDiagonalSite y)
  refine ⟨A, ?_⟩
  change Aᴴ = A
  ext x y
  change star (((Real.sqrt p.c)⁻¹ : ℂ) *
    M.H ω (allDiagonalSite y) (allDiagonalSite x)) =
      ((Real.sqrt p.c)⁻¹ : ℂ) *
        M.H ω (allDiagonalSite x) (allDiagonalSite y)
  rw [star_mul']
  have hH := congrFun (congrFun (M.H_hermitian ω) (allDiagonalSite x))
    (allDiagonalSite y)
  simp only [Matrix.conjTranspose_apply] at hH
  rw [hH]
  congr 1
  norm_num

/-- The normalized full physical matrix is measurable. -/
theorem Law.measurable_normalizedPhysicalMatrix {p : Params} (M : Law p) :
    Measurable M.normalizedPhysicalMatrix := by
  apply Measurable.subtype_mk
  exact Matrix.measurable_iff.mpr fun x y =>
    (M.measurable_entry (allDiagonalSite x) (allDiagonalSite y)).const_mul _

/-- The random Hermitian background obtained by removing all diagonal GUE blocks from
the normalized physical matrix. -/
def Law.normalizedOffDiagonalBackground {p : Params} (M : Law p) (ω : M.Ω) :
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) :=
  ⟨M.normalizedPhysicalMatrix ω - M.normalizedAllDiagonalBlocks ω,
    (M.normalizedPhysicalMatrix ω).2.sub
      (M.normalizedAllDiagonalBlocks_isHermitian ω)⟩

/-- The cross-block background is measurable. -/
theorem Law.measurable_normalizedOffDiagonalBackground
    {p : Params} (M : Law p) :
    Measurable M.normalizedOffDiagonalBackground := by
  apply Measurable.subtype_mk
  have hfull : Measurable (fun ω =>
      (M.normalizedPhysicalMatrix ω).1) :=
    measurable_subtype_coe.comp M.measurable_normalizedPhysicalMatrix
  rw [Matrix.measurable_iff]
  intro x y
  exact (Matrix.measurable_iff.mp hfull x y).sub
    (Matrix.measurable_iff.mp M.measurable_normalizedAllDiagonalBlocks x y)

/-- Exact pointwise decomposition into the off-diagonal background and all normalized
diagonal GUE blocks. -/
theorem Law.normalized_background_add_diagonal
    {p : Params} (M : Law p) (ω : M.Ω) :
    (M.normalizedOffDiagonalBackground ω).1 +
      M.normalizedAllDiagonalBlocks ω = M.normalizedPhysicalMatrix ω := by
  simp [Law.normalizedOffDiagonalBackground]

/-- The simultaneous diagonal matrix bundled with its Hermitian proof. -/
def Law.normalizedAllDiagonalBlocksHermitian {p : Params} (M : Law p) (ω : M.Ω) :
    HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) :=
  ⟨M.normalizedAllDiagonalBlocks ω,
    M.normalizedAllDiagonalBlocks_isHermitian ω⟩

/-- The bundled simultaneous diagonal matrix is measurable. -/
theorem Law.measurable_normalizedAllDiagonalBlocksHermitian
    {p : Params} (M : Law p) :
    Measurable M.normalizedAllDiagonalBlocksHermitian := by
  apply Measurable.subtype_mk
  exact M.measurable_normalizedAllDiagonalBlocks

/-- The background marginal law used in the product representation. -/
def Law.normalizedOffDiagonalBackgroundLaw {p : Params} (M : Law p) :
    Measure (HermitianMatrix (BlockGUE.Index (physicalBlockSizes p))) :=
  M.P.map M.normalizedOffDiagonalBackground

instance Law.normalizedOffDiagonalBackgroundLaw_probability
    {p : Params} (M : Law p) :
    IsProbabilityMeasure M.normalizedOffDiagonalBackgroundLaw := by
  rw [Law.normalizedOffDiagonalBackgroundLaw]
  infer_instance

/-- The product-coupling input.

The right-hand sample uses a fresh background distributed according to its marginal and
a fresh ring sample, of which only `normalizedAllDiagonalBlocks` is observed.  Thus the
field states exactly independence of the off-diagonal coordinate group from the entire
diagonal-block coordinate group, already known coordinatewise from `Law.upper_independent`.
It is strictly smaller than `PhysicalMultiBlockCountTransport`: no eigenvalue count,
scaling, or PSSS conclusion is included. -/
structure PhysicalMultiBlockProductCoupling {p : Params} (M : Law p) : Prop where
  joint_identDistrib :
    IdentDistrib
      (fun ω => (M.normalizedOffDiagonalBackground ω,
        M.normalizedAllDiagonalBlocksHermitian ω))
      (fun z : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) × M.Ω =>
        (z.1, M.normalizedAllDiagonalBlocksHermitian z.2))
      M.P (M.normalizedOffDiagonalBackgroundLaw.prod M.P)

/-- The normalized physical closed-interval count.  Endpoints are divided by `sqrt c`,
so this is exactly the count appearing after the paper's spectral rescaling. -/
def Law.normalizedPhysicalIntervalCount {p : Params} (M : Law p)
    (a b : ℝ) (ω : M.Ω) : ℕ :=
  eigenCount (M.normalizedPhysicalMatrix ω) (Set.Icc (a / Real.sqrt p.c)
    (b / Real.sqrt p.c))

/-- Any eigenvalue count is bounded by the matrix dimension. -/
theorem eigenCount_le_dimension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (s : Set ℝ) :
    eigenCount A s ≤ Fintype.card ι := by
  classical
  unfold eigenCount
  calc
    (Finset.univ.filter (fun i => orderedEigenvalue A i ∈ s)).card ≤
        (Finset.univ : Finset (Fin (Fintype.card ι))).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card ι := by simp

/-- The normalized physical count never exceeds the physical dimension `nW`. -/
theorem Law.normalizedPhysicalIntervalCount_le_dimension
    {p : Params} (M : Law p) (a b : ℝ) (ω : M.Ω) :
    M.normalizedPhysicalIntervalCount a b ω ≤ p.n * p.W := by
  rw [← card_physicalBlockIndex p]
  exact eigenCount_le_dimension (ι := BlockGUE.Index (physicalBlockSizes p)) _ _

/-- Count functional of a Hermitian background/diagonal pair. -/
def coupledIntervalCountFunctional {p : Params} (a b : ℝ)
    (z : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) ×
      HermitianMatrix (BlockGUE.Index (physicalBlockSizes p))) : ℕ :=
  eigenCount
    ⟨z.1.1 + z.2.1, z.1.2.add z.2.2⟩
    (Set.Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c))

/-- The coupled count functional is measurable. -/
theorem measurable_coupledIntervalCountFunctional {p : Params} (a b : ℝ) :
    Measurable (coupledIntervalCountFunctional (p := p) a b) := by
  apply (measurable_eigenCount_Icc
    (a / Real.sqrt p.c) (b / Real.sqrt p.c)).comp
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact ((Matrix.measurable_iff.mp
    (measurable_subtype_coe.comp measurable_fst) x y).add
      (Matrix.measurable_iff.mp
        (measurable_subtype_coe.comp measurable_snd) x y))

/-- Evaluating the coupled functional on the two physical pieces recovers the
normalized physical count pointwise. -/
theorem Law.coupledIntervalCountFunctional_physical
    {p : Params} (M : Law p) (a b : ℝ) (ω : M.Ω) :
    coupledIntervalCountFunctional (p := p) a b
      (M.normalizedOffDiagonalBackground ω,
        M.normalizedAllDiagonalBlocksHermitian ω) =
      M.normalizedPhysicalIntervalCount a b ω := by
  unfold coupledIntervalCountFunctional
  change eigenCount
      ⟨(M.normalizedOffDiagonalBackground ω).1 +
        M.normalizedAllDiagonalBlocks ω, _⟩
      (Set.Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c)) =
    eigenCount (M.normalizedPhysicalMatrix ω)
      (Set.Icc (a / Real.sqrt p.c) (b / Real.sqrt p.c))
  congr 2
  change (M.normalizedOffDiagonalBackground ω).1 +
      M.normalizedAllDiagonalBlocks ω =
    (M.normalizedPhysicalMatrix ω).1
  exact M.normalized_background_add_diagonal ω

/-- On the product space, the coupled functional is definitionally the
random-background BlockGUE count. -/
theorem Law.coupledIntervalCountFunctional_product
    {p : Params} (M : Law p) (a b : ℝ)
    (z : HermitianMatrix (BlockGUE.Index (physicalBlockSizes p)) × M.Ω) :
    coupledIntervalCountFunctional (p := p) a b
      (z.1, M.normalizedAllDiagonalBlocksHermitian z.2) =
      BlockGUE.randomBackgroundIntervalCount
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        (a / Real.sqrt p.c) (b / Real.sqrt p.c) z := by
  rfl

/-- The exact physical multi-block transport follows from only the product-coupling
field.  All matrix construction, normalization, endpoint scaling, and dimension
control are proved in this module. -/
theorem Law.physicalMultiBlockCountTransport
    {p : Params} (M : Law p) (h : PhysicalMultiBlockProductCoupling M) :
    PhysicalMultiBlockCountTransport M.P M.normalizedOffDiagonalBackgroundLaw p
      M.normalizedAllDiagonalBlocksGUE (fun A => A)
      M.normalizedPhysicalIntervalCount where
  measurable_background := measurable_id
  count_identDistrib := by
    intro a b
    have hc := h.joint_identDistrib.comp
      (measurable_coupledIntervalCountFunctional (p := p) a b)
    change IdentDistrib
      (fun ω => M.normalizedPhysicalIntervalCount a b ω)
      (fun z => BlockGUE.randomBackgroundIntervalCount
        M.normalizedAllDiagonalBlocksGUE (fun A => A)
        (a / Real.sqrt p.c) (b / Real.sqrt p.c) z)
      M.P (M.normalizedOffDiagonalBackgroundLaw.prod M.P)
    simp only [Law.normalizedAllDiagonalBlocksGUE, Function.comp_def,
      M.coupledIntervalCountFunctional_physical,
      M.coupledIntervalCountFunctional_product] at hc
    convert hc using 1 <;> rfl
  count_le_dimension := M.normalizedPhysicalIntervalCount_le_dimension

end GaussianRing
end CoareaNative.BlockBand
