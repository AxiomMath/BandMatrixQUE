module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalActualPairGaussianSplit
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSparseGaussianPolynomialNull
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The full adjacent-pair Gaussian convolution

The full finite-vector convolution, rather than its one-dimensional marginals: the residual and
fresh coordinate product measures add to the product law with the original physical
exposed-pair variances, while the exterior state is carried unchanged.

Setting: the coarea theorem at a fixed adjacent exposed pair.  All dimensions, the block edge,
and the split variance are fixed; no limit or uniformity claim is made.
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

/-- The complete residual-plus-fresh coordinate vector has the original
physical exposed-pair product law.  This upgrades the scalar convolution in
`physicalActualPairSplitReadback_coordinate_hasLaw` to a single pushforward
identity for the whole finite vector. -/
theorem physicalActualPairSplitReadback_pair_hasLaw
    {p : Params} {j : ZMod p.n} {s : ℝ}
    (hs0 : 0 ≤ s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure (ActualPairExteriorCouplingState p j))
    [IsProbabilityMeasure exteriorLaw] :
    HasLaw
      (fun z : PhysicalHermitianSplitSample (2 * p.W)
          (ActualPairExteriorCouplingState p j) => z.1.1 + z.2)
      (Measure.pi fun k =>
        gaussianReal 0 (physicalExposedPairCoordinateVariance p k))
      (physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs0)
        (physicalExposedPairResidualMeasure p hs0 hsc hsb) exteriorLaw) := by
  let K := Fin (Fintype.card (HermitianCoordinate (2 * p.W)))
  let v : K → Measure ℝ := fun k => gaussianReal 0
    (physicalExposedPairResidualCoordinateVariance p hs0 hsc hsb k)
  let g : K → Measure ℝ := fun k => gaussianReal 0
    (hermitianGUEFinCoordinateVariance (2 * p.W)
      (coareaGUEVariance p s) (coareaGUEVariance_nonneg p hs0) k)
  let μV : Measure (K → ℝ) := Measure.pi v
  let μG : Measure (K → ℝ) := Measure.pi g
  have hsource : Measure.map
      (fun z : ((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ) =>
        (z.1.1, z.2)) ((μV.prod exteriorLaw).prod μG) = μV.prod μG := by
    calc
      Measure.map
          (fun z : ((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ) =>
            (z.1.1, z.2)) ((μV.prod exteriorLaw).prod μG) =
          (Measure.map Prod.fst (μV.prod exteriorLaw)).prod
            (Measure.map id μG) := by
              calc
                Measure.map (fun z : ((K → ℝ) ×
                    ActualPairExteriorCouplingState p j) × (K → ℝ) =>
                    (z.1.1, z.2)) ((μV.prod exteriorLaw).prod μG) =
                    Measure.map (Prod.map Prod.fst id)
                      ((μV.prod exteriorLaw).prod μG) := by
                        congr 1
                _ = _ := (Measure.map_prod_map
                  (μV.prod exteriorLaw) μG measurable_fst measurable_id).symm
      _ = μV.prod μG := by
        rw [measurePreserving_fst.map_eq, Measure.map_id]
  let addPair : (K → ℝ × ℝ) → (K → ℝ) := fun x k => (x k).1 + (x k).2
  have hadd_meas : Measurable addPair := by
    rw [measurable_pi_iff]
    intro k
    exact ((measurable_fst.comp (measurable_pi_apply k)).add
      (measurable_snd.comp (measurable_pi_apply k)))
  have hprod : Measure.map (fun z : (K → ℝ) × (K → ℝ) => z.1 + z.2)
      (μV.prod μG) = Measure.pi (fun k =>
        gaussianReal 0 (physicalExposedPairCoordinateVariance p k)) := by
    let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ K
    have he : Measure.map e.symm (μV.prod μG) =
        Measure.pi (fun k => (v k).prod (g k)) := by
      exact (measurePreserving_arrowProdEquivProdArrow ℝ ℝ K v g).symm.map_eq
    calc
      Measure.map (fun z : (K → ℝ) × (K → ℝ) => z.1 + z.2)
          (μV.prod μG) = Measure.map addPair
            (Measure.map e.symm (μV.prod μG)) := by
              rw [Measure.map_map hadd_meas e.symm.measurable]
              rfl
      _ = Measure.map addPair (Measure.pi (fun k => (v k).prod (g k))) := by rw [he]
      _ = Measure.pi (fun k => Measure.map (fun q : ℝ × ℝ => q.1 + q.2)
            ((v k).prod (g k))) := by
          exact Measure.pi_map_pi (fun _ =>
            (measurable_fst.add measurable_snd).aemeasurable)
      _ = Measure.pi (fun k =>
          gaussianReal 0 (physicalExposedPairCoordinateVariance p k)) := by
        congr 1
        funext k
        have hv : HasLaw (fun q : ℝ × ℝ => q.1)
            (v k) ((v k).prod (g k)) := by
          exact (measurePreserving_fst (μ := v k) (ν := g k)).hasLaw
        have hg : HasLaw (fun q : ℝ × ℝ => q.2)
            (g k) ((v k).prod (g k)) := by
          exact (measurePreserving_snd (μ := v k) (ν := g k)).hasLaw
        have hi : IndepFun (fun q : ℝ × ℝ => q.1)
            (fun q : ℝ × ℝ => q.2) ((v k).prod (g k)) :=
          indepFun_prod measurable_id measurable_id
        have hs := gaussianReal_add_gaussianReal_of_indepFun hi hv hg
        rw [physicalExposedPairResidual_add_fresh p hs0 hsc hsb k] at hs
        rw [zero_add] at hs
        have hfun : ((fun q : ℝ × ℝ => q.1) + fun q => q.2) =
            (fun q : ℝ × ℝ => q.1 + q.2) := by
          funext q
          rfl
        rw [hfun] at hs
        exact hs
  refine ⟨?_, ?_⟩
  · exact (measurable_pi_iff.mpr fun k =>
      ((measurable_pi_apply k).comp (measurable_fst.comp measurable_fst)).add
        ((measurable_pi_apply k).comp
          (show Measurable (fun z : ((K → ℝ) ×
            ActualPairExteriorCouplingState p j) × (K → ℝ) => z.2) from
            measurable_snd))).aemeasurable
  · change Measure.map
      (fun z : ((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ) =>
        z.1.1 + z.2) ((μV.prod exteriorLaw).prod μG) = _
    rw [← hprod, ← hsource]
    have hpair : Measurable
        (fun z : ((K → ℝ) × ActualPairExteriorCouplingState p j) × (K → ℝ) =>
          (z.1.1, z.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have hsum : Measurable (fun z : (K → ℝ) × (K → ℝ) => z.1 + z.2) :=
      measurable_pi_iff.mpr fun k =>
        ((measurable_pi_apply k).comp measurable_fst).add
          ((measurable_pi_apply k).comp measurable_snd)
    rw [Measure.map_map hsum hpair]
    rfl

end GaussianRing
end CoareaNative.BlockBand
