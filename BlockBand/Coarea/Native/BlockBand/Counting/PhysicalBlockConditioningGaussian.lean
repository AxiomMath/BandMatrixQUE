module

public import BlockBand.Coarea.Native.BlockBand.Counting.ProjectedWegnerPhysical
public import BlockBand.Coarea.Native.BlockBand.Model.GaussianRing
public import Mathlib.Probability.HasLaw

/-!
# Gaussian coordinate splitting for physical block conditioning

This module proves the model-part of the probability decomposition
needed to instantiate `PhysicalBlockConditioning`.  For a fixed physical block
it partitions the independent upper-triangular coordinates of
`GaussianRing.Law` into the coordinates internal to that block and all
remaining coordinates.  The two resulting random vectors are measurable and
independent, and their joint pushforward law is exactly the product of their
marginal laws.

This is a product-law decomposition, not a disintegration axiom.  It
does not by itself instantiate `PhysicalBlockConditioning`: the ring diagonal
block has variance `c/W`, whereas `BlockGUE.Law` is normalized at `1/W`, so
this also needs measurable reconstruction maps, the rescaling by `sqrt c`, and
the factorization of the Schur-trace functional through the exterior and exposed
coordinate vectors.  The final structure, `PhysicalConditioningGaussianCoupling`,
records these reconstruction and coupling data without any expectation estimate;
it is built by `PhysicalProjectedWegnerInstantiation.gaussianCoupling`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ComplexOrder ENNReal NNReal

universe u v

namespace GaussianRing

/-- Upper-triangular coordinates lying entirely inside physical block `j`. -/
def diagonalBlockUpperPairs (p : Params) (j : ZMod p.n) :
    Finset (UpperPair p) :=
  let _ := p.neZero_n
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  Finset.univ.filter fun q => q.1.1.1 = j ∧ q.1.2.1 = j

/-- All upper-triangular coordinates outside the exposed diagonal block. -/
def exteriorUpperPairs (p : Params) (j : ZMod p.n) :
    Finset (UpperPair p) :=
  let _ := p.neZero_n
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  Finset.univ.filter fun q => ¬(q.1.1.1 = j ∧ q.1.2.1 = j)

/-- The exposed and exterior upper-coordinate sets are disjoint. -/
theorem diagonalBlockUpperPairs_disjoint_exterior
    (p : Params) (j : ZMod p.n) :
    Disjoint (diagonalBlockUpperPairs p j) (exteriorUpperPairs p j) := by
  let _ := p.neZero_n
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  rw [Finset.disjoint_left]
  intro q hq hqext
  have hq' : q.1.1.1 = j ∧ q.1.2.1 = j := by
    simpa [diagonalBlockUpperPairs] using hq
  have hqext' : ¬(q.1.1.1 = j ∧ q.1.2.1 = j) := by
    simpa [exteriorUpperPairs] using hqext
  exact hqext' hq'

/-- The complete upper-coordinate vector internal to one diagonal block. -/
def Law.diagonalBlockUpperCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (q : diagonalBlockUpperPairs p j) : ℂ :=
  M.H ω q.1.1.1 q.1.1.2

/-- The complementary upper-coordinate vector. -/
def Law.exteriorUpperCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (q : exteriorUpperPairs p j) : ℂ :=
  M.H ω q.1.1.1 q.1.1.2

/-- The exposed upper-coordinate vector is measurable. -/
theorem Law.measurable_diagonalBlockUpperCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measurable (M.diagonalBlockUpperCoordinates j) := by
  rw [measurable_pi_iff]
  intro q
  exact M.measurable_entry q.1.1.1 q.1.1.2

/-- The exterior upper-coordinate vector is measurable. -/
theorem Law.measurable_exteriorUpperCoordinates
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measurable (M.exteriorUpperCoordinates j) := by
  rw [measurable_pi_iff]
  intro q
  exact M.measurable_entry q.1.1.1 q.1.1.2

/-- The model's mutual upper-entry independence implies that the entire
exposed diagonal-block upper triangle is independent of all exterior upper
coordinates. -/
theorem Law.indepFun_diagonalBlockUpperCoordinates_exterior
    {p : Params} (M : Law p) (j : ZMod p.n) :
    IndepFun (M.diagonalBlockUpperCoordinates j)
      (M.exteriorUpperCoordinates j) M.P := by
  exact iIndepFun.indepFun_finset
    (diagonalBlockUpperPairs p j) (exteriorUpperPairs p j)
    (diagonalBlockUpperPairs_disjoint_exterior p j)
    M.upper_independent
    (fun q => M.measurable_entry q.1.1 q.1.2)

/-- Consequently the joint coordinate law is exactly the product of the two
marginal pushforward laws.  This is the product decomposition needed before
applying any measurable Schur-complement reconstruction. -/
theorem Law.map_prod_diagonalBlockUpperCoordinates_exterior
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measure.map (fun ω =>
      (M.diagonalBlockUpperCoordinates j ω,
        M.exteriorUpperCoordinates j ω)) M.P =
      (Measure.map (M.diagonalBlockUpperCoordinates j) M.P).prod
        (Measure.map (M.exteriorUpperCoordinates j) M.P) := by
  exact (M.indepFun_diagonalBlockUpperCoordinates_exterior j).map_prod_eq_prod_map_map
    (M.measurable_diagonalBlockUpperCoordinates j).aemeasurable
    (M.measurable_exteriorUpperCoordinates j).aemeasurable

/-- The `W × W` principal diagonal block of the ring matrix. -/
def Law.diagonalBlock
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    Matrix (Fin p.W) (Fin p.W) ℂ :=
  (M.H ω).submatrix (fun a => (j, a)) (fun a => (j, a))

/-- The diagonal-block matrix is measurable entrywise. -/
theorem Law.measurable_diagonalBlock
    {p : Params} (M : Law p) (j : ZMod p.n) :
    Measurable (M.diagonalBlock j) := by
  rw [Matrix.measurable_iff]
  intro a b
  exact M.measurable_entry (j, a) (j, b)

/-- Every sampled physical diagonal block is Hermitian. -/
theorem Law.diagonalBlock_isHermitian
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω) :
    (M.diagonalBlock j ω).IsHermitian := by
  simpa only [Law.diagonalBlock] using
    (M.H_hermitian ω).submatrix (fun a : Fin p.W => (j, a))

/-- Admissibility `n ≥ 4` prevents cyclic self-neighbor collisions, so the
within-block weight is exactly `c`. -/
theorem blockWeight_self (p : Params) (j : ZMod p.n) :
    blockWeight p j j = p.c := by
  have hone : (1 : ZMod p.n) ≠ 0 := by
    intro h
    have hn : p.n = 1 := ZMod.one_eq_zero_iff.mp h
    have hfour : 4 ≤ p.n := p.n_ge_four
    omega
  have hp : j ≠ j + 1 := by
    intro h
    have hz : (0 : ZMod p.n) = 1 := by
      calc
        0 = j - j := by ring
        _ = (j + 1) - j := congrArg (fun x => x - j) h
        _ = 1 := by ring
    exact hone hz.symm
  have hm : j ≠ j - 1 := by
    intro h
    have hz : (0 : ZMod p.n) = 1 := by
      calc
        0 = j - j := by ring
        _ = j - (j - 1) := congrArg (fun x => j - x) h
        _ = 1 := by ring
    exact hone hz.symm
  simp [blockWeight, hp, hm]

/-- Every entry internal to one diagonal block has total variance `c/W`, the
scaled-GUE normalization occurring in the physical ring model. -/
theorem varianceProfile_diagonalBlock
    (p : Params) (j : ZMod p.n) (a b : Fin p.W) :
    varianceProfile p (j, a) (j, b) = p.c / (p.W : ℝ) := by
  simp [varianceProfile, blockWeight_self]

/-- Coupling data beyond the proved coordinate product split (built by
`PhysicalProjectedWegnerInstantiation.gaussianCoupling`).  It asks for an exposed standard `BlockGUE` realization and measurable
reconstruction maps from the exposed and exterior coordinate laws.  The trace
identity is kept as an `IdentDistrib`, exactly matching
`PhysicalBlockConditioning.identDistrib`; no Wegner estimate is assumed. -/
structure PhysicalConditioningGaussianCoupling
    {p : Params} (M : Law p) (j : ZMod p.n)
    {g : M.Ω → ℝ} {η : ℝ} where
  exposed : BlockGUE.Law.{u} (singletonBlockSize p.W)
    (singletonBlockSize_pos p.W_pos)
  Exterior : Type v
  [exteriorMeasurable : MeasurableSpace Exterior]
  exteriorLaw : Measure Exterior
  [exteriorProbability : IsProbabilityMeasure exteriorLaw]
  background : Exterior →
    HermitianMatrix (BlockGUE.Index (singletonBlockSize p.W))
  absorber : Exterior → Matrix (BlockGUE.Index (singletonBlockSize p.W))
    (BlockGUE.Index (singletonBlockSize p.W)) ℂ
  absorber_pos : ∀ ξ, (absorber ξ).PosSemidef
  joint_measurable : Measurable
    (conditionedAbsorbedTrace p.W_pos exposed background absorber η)
  trace_identDistrib : IdentDistrib g
    (conditionedAbsorbedTrace p.W_pos exposed background absorber η)
    M.P (exteriorLaw.prod exposed.P)

end GaussianRing

end CoareaNative.BlockBand
