module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalConditionalCoareaManuscript
public import BlockBand.Coarea.Native.BlockBand.Model.GaussianRing
public import Mathlib.Probability.IdentDistribIndep

/-!
# Adjacent-pair Gaussian split

The two adjacent physical blocks of a `GaussianRing.Law`, together with the complementary
exterior matrix and coupling.  This file proves the upper-coordinate product independence
available directly from `Law.upper_independent`, defines the pair/exterior pushforward law,
and derives the `IdentDistrib` identification with `physicalHermitianSplitMeasure` from the
single measure equality `Law.ActualPairGaussianSplitInput` (proved as
`Law.actualPairGaussianSplitInput`).  No independence or exceptional nullity beyond the `Law`
structure is used.

Setting: the coarea theorem at a fixed adjacent exposed pair.  The block edge,
finite sizes and split variance are fixed, with no limit or uniformity claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The site in the first, respectively forward-adjacent, block represented by
one coordinate of `Fin (2W)`. -/
def adjacentPairSite (p : Params) (j : ZMod p.n) (a : Fin (2 * p.W)) :
    Site p.n p.W :=
  Fin.addCases (fun u => (j, u)) (fun v => (j + 1, v))
    (Fin.cast (by omega) a)

/-- Physical sites complementary to the adjacent pair `(j,j+1)`. -/
abbrev AdjacentPairExteriorIndex (p : Params) (j : ZMod p.n) :=
  {x : Site p.n p.W // x.1 ≠ j ∧ x.1 ≠ j + 1}

/-- Complementary exterior Hermitian matrix together with its coupling into the
ordered adjacent pair. -/
abbrev ActualPairExteriorCouplingState (p : Params) (j : ZMod p.n) :=
  HermitianMatrix (AdjacentPairExteriorIndex p j) ×
    Matrix (AdjacentPairExteriorIndex p j) (Fin (2 * p.W)) ℂ

/-- Unnormalised adjacent two-block Hermitian principal matrix.  Its
coordinate variances are `physicalExposedPairCoordinateVariance`. -/
def Law.actualAdjacentPairMatrix {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) : HermitianMatrix (Fin (2 * p.W)) :=
  ⟨(M.H ω).submatrix (adjacentPairSite p j) (adjacentPairSite p j),
    (M.H_hermitian ω).submatrix (adjacentPairSite p j)⟩

/-- Finite real Hermitian coordinates of the adjacent pair. -/
def Law.actualAdjacentPairCoordinates {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) : HermitianCoordinateSpace (2 * p.W) :=
  hermitianFinCoordinateReadback (2 * p.W) (M.actualAdjacentPairMatrix j ω)

/-- Exterior principal matrix and pair-to-exterior coupling. -/
def Law.actualPairExteriorCouplingState {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) : ActualPairExteriorCouplingState p j :=
  (⟨(M.H ω).submatrix Subtype.val Subtype.val,
      (M.H_hermitian ω).submatrix Subtype.val⟩,
    (M.H ω).submatrix Subtype.val (adjacentPairSite p j))

/-- The adjacent matrix is measurable entrywise. -/
theorem Law.measurable_actualAdjacentPairMatrix {p : Params} (M : Law p)
    (j : ZMod p.n) : Measurable (M.actualAdjacentPairMatrix j) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro a b
  exact M.measurable_entry (adjacentPairSite p j a) (adjacentPairSite p j b)

/-- The adjacent-pair coordinate vector is measurable. -/
theorem Law.measurable_actualAdjacentPairCoordinates {p : Params} (M : Law p)
    (j : ZMod p.n) : Measurable (M.actualAdjacentPairCoordinates j) :=
  (measurable_hermitianFinCoordinateReadback (2 * p.W)).comp
    (M.measurable_actualAdjacentPairMatrix j)

/-- The complete exterior/coupling state is measurable. -/
theorem Law.measurable_actualPairExteriorCouplingState {p : Params} (M : Law p)
    (j : ZMod p.n) : Measurable (M.actualPairExteriorCouplingState j) := by
  apply Measurable.prodMk
  · apply Measurable.subtype_mk
    rw [Matrix.measurable_iff]
    intro a b
    exact M.measurable_entry a.1 b.1
  · rw [Matrix.measurable_iff]
    intro a b
    exact M.measurable_entry a.1 (adjacentPairSite p j b)

/-- Upper entries internal to the adjacent pair. -/
def adjacentPairUpperPairs (p : Params) (j : ZMod p.n) : Finset (UpperPair p) :=
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  Finset.univ.filter fun q =>
    (q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
      (q.1.2.1 = j ∨ q.1.2.1 = j + 1)

/-- All upper entries not internal to the adjacent pair. -/
def adjacentPairExteriorUpperPairs (p : Params) (j : ZMod p.n) :
    Finset (UpperPair p) :=
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  Finset.univ.filter fun q => ¬((q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
    (q.1.2.1 = j ∨ q.1.2.1 = j + 1))

/-- The internal-pair and exterior upper-coordinate families are disjoint. -/
theorem adjacentPairUpperPairs_disjoint_exterior (p : Params) (j : ZMod p.n) :
    Disjoint (adjacentPairUpperPairs p j) (adjacentPairExteriorUpperPairs p j) := by
  let _ : Finite (UpperPair p) := by
    unfold UpperPair
    infer_instance
  let _ : Fintype (UpperPair p) := Fintype.ofFinite _
  rw [Finset.disjoint_left]
  intro q hq hqe
  have h : (q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
      (q.1.2.1 = j ∨ q.1.2.1 = j + 1) := by
    simpa [adjacentPairUpperPairs] using hq
  have hn : ¬((q.1.1.1 = j ∨ q.1.1.1 = j + 1) ∧
      (q.1.2.1 = j ∨ q.1.2.1 = j + 1)) := by
    simpa [adjacentPairExteriorUpperPairs] using hqe
  exact hn h

/-- Raw upper-coordinate vectors on the pair and its complement. -/
def Law.actualPairUpperCoordinates {p : Params} (M : Law p) (j : ZMod p.n)
    (ω : M.Ω) (q : adjacentPairUpperPairs p j) : ℂ :=
  M.H ω q.1.1.1 q.1.1.2

def Law.actualPairExteriorUpperCoordinates {p : Params} (M : Law p)
    (j : ZMod p.n) (ω : M.Ω) (q : adjacentPairExteriorUpperPairs p j) : ℂ :=
  M.H ω q.1.1.1 q.1.1.2

/-- `Law.upper_independent` supplies independence of the two complete
raw coordinate groups; this is not an added split hypothesis. -/
theorem Law.indepFun_actualPairUpperCoordinates_exterior {p : Params} (M : Law p)
    (j : ZMod p.n) :
    IndepFun (M.actualPairUpperCoordinates j)
      (M.actualPairExteriorUpperCoordinates j) M.P := by
  exact iIndepFun.indepFun_finset
    (adjacentPairUpperPairs p j) (adjacentPairExteriorUpperPairs p j)
    (adjacentPairUpperPairs_disjoint_exterior p j) M.upper_independent
    (fun q => M.measurable_entry q.1.1 q.1.2)

/-- Pushforward law of the adjacent pair jointly with the complete
exterior/coupling state. -/
def Law.actualPairExteriorLaw {p : Params} (M : Law p) (j : ZMod p.n) :
    Measure (HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j) :=
  M.P.map fun ω =>
    (M.actualAdjacentPairCoordinates j ω, M.actualPairExteriorCouplingState j ω)

/-- Marginal law of the exterior/coupling state. -/
def Law.actualPairExteriorStateLaw {p : Params} (M : Law p) (j : ZMod p.n) :
    Measure (ActualPairExteriorCouplingState p j) :=
  M.P.map (M.actualPairExteriorCouplingState j)

instance Law.actualPairExteriorStateLaw.instIsProbabilityMeasure
    {p : Params} (M : Law p) (j : ZMod p.n) :
    IsProbabilityMeasure (M.actualPairExteriorStateLaw j) := by
  unfold Law.actualPairExteriorStateLaw
  infer_instance

/-- Readback from the residual-plus-fresh split to the pair coordinates and
the unchanged exterior/coupling state. -/
def physicalActualPairSplitReadback
    {p : Params} {j : ZMod p.n}
    (z : PhysicalHermitianSplitSample (2 * p.W)
      (ActualPairExteriorCouplingState p j)) :
    HermitianCoordinateSpace (2 * p.W) × ActualPairExteriorCouplingState p j :=
  (z.1.1 + z.2, z.1.2)

/-- The split readback is measurable. -/
theorem measurable_physicalActualPairSplitReadback
    {p : Params} {j : ZMod p.n} :
    Measurable (physicalActualPairSplitReadback (p := p) (j := j)) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro k
    change Measurable (fun z : PhysicalHermitianSplitSample (2 * p.W)
      (ActualPairExteriorCouplingState p j) => z.1.1 k + z.2 k)
    have hv : Measurable (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.1.1) :=
      measurable_fst.comp measurable_fst
    have hg : Measurable (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.2) :=
      measurable_snd
    exact ((measurable_pi_apply k).comp hv).add
      ((measurable_pi_apply k).comp hg)
  · exact measurable_snd.comp measurable_fst

/-- Every coordinate of the residual-plus-fresh readback, with the exterior state carried
along, has exactly the physical adjacent-pair Gaussian law (scalar convolution). -/
theorem physicalActualPairSplitReadback_coordinate_hasLaw
    {p : Params} {j : ZMod p.n} {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure (ActualPairExteriorCouplingState p j))
    [IsProbabilityMeasure exteriorLaw]
    (k : Fin (Fintype.card (HermitianCoordinate (2 * p.W)))) :
    HasLaw
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
          (ActualPairExteriorCouplingState p j) => z.1.1 k + z.2 k)
      (gaussianReal 0 (physicalExposedPairCoordinateVariance p k))
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) := by
  let μV := physicalExposedPairResidualMeasure p hs0 hsc hsb
  let μG := hermitianGUECoordinateMeasure (2 * p.W)
    (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0)
  have hV0 : HasLaw
      (fun x : HermitianCoordinateSpace (2 * p.W) => x k)
      (gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k)) μV :=
    (measurePreserving_eval
      (fun q => gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb q)) k).hasLaw
  have hV1 : HasLaw
      (fun x : HermitianCoordinateSpace (2 * p.W) ×
        ActualPairExteriorCouplingState p j => x.1 k)
      (gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k))
      (μV.prod exteriorLaw) :=
    hV0.fun_comp measurePreserving_fst.hasLaw
  have hV : HasLaw
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.1.1 k)
      (gaussianReal 0
        (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k))
      ((μV.prod exteriorLaw).prod μG) :=
    hV1.fun_comp measurePreserving_fst.hasLaw
  have hG0 : HasLaw
      (fun x : HermitianCoordinateSpace (2 * p.W) => x k)
      (gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k)) μG :=
    (measurePreserving_eval
      (fun q => gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) q)) k).hasLaw
  have hG : HasLaw
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.2 k)
      (gaussianReal 0
        (hermitianGUEFinCoordinateVariance (2 * p.W)
          (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k))
      ((μV.prod exteriorLaw).prod μG) :=
    hG0.fun_comp measurePreserving_snd.hasLaw
  have hind : IndepFun
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.1.1 k)
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
        (ActualPairExteriorCouplingState p j) => z.2 k)
      ((μV.prod exteriorLaw).prod μG) :=
    indepFun_prod
      ((measurable_pi_apply k).comp measurable_fst)
      (measurable_pi_apply k)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hV hG
  rw [physicalExposedPairResidual_add_fresh p hs0 hsc hsb k] at hsum
  refine ⟨(((measurable_pi_apply k).comp
      (measurable_fst.comp measurable_fst)).add
        ((measurable_pi_apply k).comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map ((fun z => z.1.1 k) + fun z => z.2 k)
      ((μV.prod exteriorLaw).prod μG) =
    gaussianReal 0 (physicalExposedPairCoordinateVariance p k)
  simpa using hsum

/-- The single full-vector convolution/reassociation pushforward equality, not part of
the `GaussianRing.Law` structure; it is proved as `Law.actualPairGaussianSplitInput`.  Raw
group independence was proved above from `Law.upper_independent`. -/
structure Law.ActualPairGaussianSplitInput {p : Params} (M : Law p)
    (j : ZMod p.n) {s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b) : Prop where
  map_eq : M.actualPairExteriorLaw j =
    Measure.map (physicalActualPairSplitReadback (p := p) (j := j))
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb)
        (M.actualPairExteriorStateLaw j))

/-- Under the vector-law identification `Law.ActualPairGaussianSplitInput`, the physical
pair/exterior random variable is identically distributed with residual plus a
fresh finite-product GUE block and the same exterior/coupling state. -/
theorem Law.identDistrib_actualPairExterior_physicalSplit
    {p : Params} (M : Law p) (j : ZMod p.n) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (input : M.ActualPairGaussianSplitInput j hs0 hsc hsb) :
    IdentDistrib
      (fun ω => (M.actualAdjacentPairCoordinates j ω,
        M.actualPairExteriorCouplingState j ω))
      (physicalActualPairSplitReadback (p := p) (j := j)) M.P
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb)
        (M.actualPairExteriorStateLaw j)) := by
  refine ⟨((M.measurable_actualAdjacentPairCoordinates j).prodMk
      (M.measurable_actualPairExteriorCouplingState j)).aemeasurable,
    measurable_physicalActualPairSplitReadback.aemeasurable, ?_⟩
  exact input.map_eq

/-- Equivalent pushforward-law form of the joint identification. -/
theorem Law.map_actualPairExterior_eq_physicalSplit
    {p : Params} (M : Law p) (j : ZMod p.n) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (input : M.ActualPairGaussianSplitInput j hs0 hsc hsb) :
    M.actualPairExteriorLaw j =
      Measure.map (physicalActualPairSplitReadback (p := p) (j := j))
        (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw j)) :=
  input.map_eq

/-- Every measurable nonnegative pair/exterior observable has exactly
the residual-plus-fresh split integral once the single vector-law input is
available. -/
theorem Law.lintegral_actualPairExterior_eq_physicalSplit
    {p : Params} (M : Law p) (j : ZMod p.n) {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (input : M.ActualPairGaussianSplitInput j hs0 hsc hsb)
    (Φ : HermitianCoordinateSpace (2 * p.W) ×
      ActualPairExteriorCouplingState p j → ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ ω, Φ (M.actualAdjacentPairCoordinates j ω,
      M.actualPairExteriorCouplingState j ω) ∂M.P) =
      ∫⁻ z, Φ (physicalActualPairSplitReadback (p := p) (j := j) z)
        ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw j) := by
  let actual := fun ω => (M.actualAdjacentPairCoordinates j ω,
    M.actualPairExteriorCouplingState j ω)
  have hactual : Measurable actual :=
    (M.measurable_actualAdjacentPairCoordinates j).prodMk
      (M.measurable_actualPairExteriorCouplingState j)
  calc
    (∫⁻ ω, Φ (actual ω) ∂M.P) =
        ∫⁻ y, Φ y ∂Measure.map actual M.P :=
      (lintegral_map hΦ hactual).symm
    _ = ∫⁻ y, Φ y ∂Measure.map
        (physicalActualPairSplitReadback (p := p) (j := j))
        (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw j)) := by
      rw [show Measure.map actual M.P = M.actualPairExteriorLaw j by rfl,
        input.map_eq]
    _ = ∫⁻ z, Φ (physicalActualPairSplitReadback (p := p) (j := j) z)
        ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
          (coareaGUEVariance_nonneg p hs0)
          (physicalExposedPairResidualMeasure p hs0 hsc hsb)
          (M.actualPairExteriorStateLaw j) :=
      lintegral_map hΦ measurable_physicalActualPairSplitReadback

end GaussianRing
end CoareaNative.BlockBand
