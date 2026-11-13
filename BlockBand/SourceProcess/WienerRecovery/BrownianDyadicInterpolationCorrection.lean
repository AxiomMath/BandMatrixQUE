module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCylinderContinuityAtEmptyClosure
public import BlockBand.SourceProcess.WienerRecovery.BrownianDyadicCompactExtension
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Index shift for Brownian dyadic interpolation

A compact-interpolation interface comparing the level-`n` and level-`n+1`
polygonal interpolants cannot require that a large difference be witnessed by a bad edge
at level `n`: a new midpoint can be arbitrarily far from both coarse
endpoints while the single coarse edge has zero increment.  We give the explicit
piecewise-linear counterexample below.

The interface `BrownianRawDyadicInterpolationData` charges the new edges at level `n+1`
and uses the level-`n+1` modulus.  Its approximants are determined by the raw
coordinates: every approximant is required to interpolate the raw coordinate at both
endpoints of every mesh edge, to obey the explicit affine formula on that edge, and to
be the unique compact path with those properties.  The Gaussian-envelope and
measurable-limit argument then goes through with a shifted geometric constant.  No
raw-path continuity hypothesis is introduced.  The polygonal interpolants themselves
and their fixed-time convergence against the raw Gaussian coordinates are constructed
in `canonicalBrownianRawDyadicInterpolationData` and
`brownianCanonicalDyadicInterpolationFacts`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace BrownianDyadicInterpolationCorrection

open BrownianDyadicChainingClosure
open BrownianDyadicGaussianEnvelope
open BrownianDyadicCompactExtension
open ScalarWienerMeasureConstruction

/-- A raw path supported at the first dyadic midpoint, with height `32`. -/
def midpointSpike (t : NNReal) : ℝ :=
  if t = (1 / 2 : NNReal) then 32 else 0

/-- The coarse level-zero interpolant for the midpoint-spike data. -/
def coarseZero : CompactPath 1 := 0

/-- The level-one polygonal interpolant for the midpoint-spike data.  On `[0,1]`
this is the triangular tent through `(0,0)`, `(1/2,32)`, `(1,0)`. -/
def midpointTent : CompactPath 1 where
  toFun t := 32 * (1 - |2 * (t.1 : ℝ) - 1|)
  continuous_toFun := by fun_prop

/-- The tent interpolates the left endpoint of the raw spike. -/
theorem midpointTent_zero :
    midpointTent ⟨0, by norm_num⟩ = midpointSpike 0 := by
  simp [midpointTent, midpointSpike]

/-- The tent interpolates the newly inserted dyadic midpoint. -/
theorem midpointTent_half :
    midpointTent ⟨(1 / 2 : NNReal), by norm_num⟩ =
      midpointSpike (1 / 2 : NNReal) := by
  norm_num [midpointTent, midpointSpike]

/-- The tent interpolates the right endpoint of the raw spike. -/
theorem midpointTent_one :
    midpointTent ⟨1, by norm_num⟩ = midpointSpike 1 := by
  norm_num [midpointTent, midpointSpike]

/-- The first refinement has uniform distance larger than the level-zero modulus. -/
theorem compactDyadicModulus_zero_lt_dist_coarseZero_midpointTent :
    compactDyadicModulus 1 0 < dist coarseZero midpointTent := by
  have hpoint := ContinuousMap.dist_apply_le_dist
    (f := coarseZero) (g := midpointTent)
    (⟨(1 / 2 : NNReal), by norm_num⟩ : Set.Icc (0 : NNReal) 1)
  norm_num [coarseZero, midpointTent, compactDyadicModulus] at hpoint ⊢
  linarith

/-- Nevertheless the unique level-zero dyadic edge of the midpoint spike is not bad:
both of its endpoints have value zero. -/
theorem unit_not_mem_levelZero_badEvent :
    () ∉ dyadicBadLevel (fun t (_ : Unit) => midpointSpike t) 1
      (compactDyadicModulus 1) 0 := by
  simp [dyadicBadLevel, dyadicLeft, dyadicRight, midpointSpike,
    compactDyadicModulus]

/-- Therefore a level-`n` `badStep_subset` condition cannot be proved for the natural
level-zero/level-one piecewise-linear interpolation, even deterministically.  This is
the precise index obstruction, not an analytic or measurability gap. -/
theorem not_badStep_subset_for_first_piecewiseLinear_refinement :
    ¬ ({_ω : Unit | compactDyadicModulus 1 0 <
          dist coarseZero midpointTent} ⊆
        dyadicBadLevel (fun t (_ : Unit) => midpointSpike t) 1
          (compactDyadicModulus 1) 0) := by
  intro h
  exact unit_not_mem_levelZero_badEvent
    (h compactDyadicModulus_zero_lt_dist_coarseZero_midpointTent)

/-- The exact raw-coordinate polygonal condition at one dyadic level.

The first two conjuncts impose equality with the raw coordinate at the two endpoints
of every mesh edge.  The last conjunct uses the normalization
`s = (t-left)/(right-left)` and asserts the affine formula
`(1-s) X(left) + s X(right)` throughout that edge.  It is stated with real coercions
so that it is the usual piecewise-linear interpolation formula. -/
def IsRawDyadicPiecewiseLinearInterpolant
    (T : NNReal) (ω : BrownianRawPath) (n : ℕ) (f : CompactPath T) : Prop :=
  (∀ (k : Fin (2 ^ n)) (t : Set.Icc (0 : NNReal) T),
      t.1 = dyadicLeft T n k →
        f t = rawCoordinateProcess (dyadicLeft T n k) ω) ∧
  (∀ (k : Fin (2 ^ n)) (t : Set.Icc (0 : NNReal) T),
      t.1 = dyadicRight T n k →
        f t = rawCoordinateProcess (dyadicRight T n k) ω) ∧
  ∀ (k : Fin (2 ^ n)) (t : Set.Icc (0 : NNReal) T),
    dyadicLeft T n k ≤ t.1 → t.1 ≤ dyadicRight T n k →
      f t =
        (((dyadicRight T n k : NNReal) : ℝ) - (t.1 : ℝ)) /
            (((dyadicRight T n k : NNReal) : ℝ) -
              ((dyadicLeft T n k : NNReal) : ℝ)) *
            rawCoordinateProcess (dyadicLeft T n k) ω +
          ((t.1 : ℝ) - ((dyadicLeft T n k : NNReal) : ℝ)) /
            (((dyadicRight T n k : NNReal) : ℝ) -
              ((dyadicLeft T n k : NNReal) : ℝ)) *
            rawCoordinateProcess (dyadicRight T n k) ω

/-- Finite-mesh data for raw dyadic interpolation.  The values of `approximant` are
determined by the raw dyadic coordinates through `isRawDyadicPiecewiseLinear`, and the
uniqueness field rules out any other compact path satisfying the same finite-mesh
specification.  Successive polygonal levels are charged to the new edges, i.e.
level `n+1`, with that level's summable modulus. -/
structure BrownianRawDyadicInterpolationData
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) where
  approximant : BrownianRawPath → ℕ → CompactPath T
  isRawDyadicPiecewiseLinear : ∀ ω n,
    IsRawDyadicPiecewiseLinearInterpolant T ω n (approximant ω n)
  unique_isRawDyadicPiecewiseLinear : ∀ ω n (f : CompactPath T),
    IsRawDyadicPiecewiseLinearInterpolant T ω n f →
      f = approximant ω n
  aemeasurable_approximant : ∀ n,
    AEMeasurable (fun ω => approximant ω n) (brownianRawMeasure hcont)
  badStep_subset : ∀ n : ℕ,
    {ω | compactDyadicModulus T n.succ <
      dist (approximant ω n) (approximant ω n.succ)} ⊆
      dyadicBadLevel rawCoordinateProcess T (compactDyadicModulus T) n.succ
  eval_tendsto : ∀ t : Set.Icc (0 : NNReal) T,
    ∀ᵐ ω ∂(brownianRawMeasure hcont),
      Tendsto (fun n => approximant ω n t) atTop
        (𝓝 (rawCoordinateProcess t.1 ω))

/-- The shifted modulus remains summable. -/
theorem summable_compactDyadicModulus_succ (T : NNReal) :
    Summable (fun n : ℕ => compactDyadicModulus T n.succ) :=
  (summable_compactDyadicModulus T).comp_injective Nat.succ_injective

/-- These finite-mesh data suffice for the measurable compact-path
modification theorem.  The extra geometric factor is exactly the one-level shift. -/
theorem exists_measurable_compactPath_modification_of_rawDyadic
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) (hT : 0 < T)
    (data : BrownianRawDyadicInterpolationData hcont T) :
    ∃ F : BrownianRawPath → CompactPath T,
      Measurable F ∧
      (∀ᵐ ω ∂(brownianRawMeasure hcont),
        Tendsto (data.approximant ω) atTop (𝓝 (F ω))) ∧
      ∀ t : Set.Icc (0 : NNReal) T,
        (fun ω => F ω t) =ᵐ[brownianRawMeasure hcont]
          rawCoordinateProcess t.1 := by
  let _ := isProbabilityMeasure_brownianRawMeasure hcont
  have hbad : ∀ n : ℕ,
      brownianRawMeasure hcont
          {ω | compactDyadicModulus T n.succ <
            dist (data.approximant ω n) (data.approximant ω n.succ)} ≤
        (gaussianDyadicRatioENNReal ^ 2) * gaussianDyadicRatioENNReal ^ n := by
    intro n
    refine le_trans (measure_mono (data.badStep_subset n)) ?_
    have h := measure_dyadicBadLevel_compactDyadicModulus_le
      (isPreBrownianReal_rawCoordinateProcess hcont) T hT n.succ
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨F, hFmeas, hFlim⟩ :=
    exists_measurable_compactPath_limit_of_geometric_badStep
      T data.approximant (fun n : ℕ => compactDyadicModulus T n.succ)
      data.aemeasurable_approximant (summable_compactDyadicModulus_succ T)
      (C := gaussianDyadicRatioENNReal ^ 2)
      (q := gaussianDyadicRatioENNReal)
      (by simp [gaussianDyadicRatioENNReal])
      gaussianDyadicRatioENNReal_lt_one hbad
  refine ⟨F, hFmeas, hFlim, ?_⟩
  intro t
  exact ae_eq_eval_of_approximants_tendsto hFlim
    (fun t ω => rawCoordinateProcess t.1 ω) data.eval_tendsto t

end BrownianDyadicInterpolationCorrection

end BlockBand.SourceProcess.WienerRecovery.CEH
