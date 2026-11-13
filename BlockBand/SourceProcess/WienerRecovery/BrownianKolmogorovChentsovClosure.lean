module

public import BlockBand.SourceProcess.WienerRecovery.ScalarWienerMeasureConstruction
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Quantitative input for the Brownian Kolmogorov–Chentsov construction

This module proves the quantitative part of Kolmogorov–Chentsov which follows
immediately, but nontrivially, from the finite-dimensional Brownian marginals.
Every increment has its exact centered Gaussian law, is in every finite `Lᵖ`,
and is sub-Gaussian with variance proxy `nndist s t`.  Consequently its
one-sided tails have the standard Gaussian Chernoff bound.  Conditional on a
proof of `BrownianCylinderContinuityAtEmpty`, these statements apply to the raw
coordinate process under the measure constructed by
`ScalarWienerMeasureConstruction`.

Thus, only after the separate cylinder-extension condition
`BrownianCylinderContinuityAtEmpty` is supplied, the remaining modification
work is the countable chaining/construction step: use these bounds on dyadic
increments, apply Borel–Cantelli on each compact time interval, construct the
uniformly Hölder continuous dyadic limit, prove the resulting map into
`C(NNReal, ℝ)` measurable, and prove fixed-time almost-everywhere
identification with the raw coordinates.  Mathlib contains neither
Kolmogorov–Chentsov nor that dyadic construction.  No assertion that a raw
path is almost surely continuous is made here; such an assertion would be
false for the uncountable product sigma-algebra.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped NNReal Topology ENNReal
open Filter MeasureTheory ProbabilityTheory

namespace BrownianKolmogorovChentsovClosure

open ScalarWienerMeasureConstruction

variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} {B : NNReal → Ω → ℝ}

/-- A pre-Brownian increment has exactly the centered Gaussian law with
variance equal to the distance between its two times. -/
theorem hasLaw_brownianIncrement
    (hB : IsPreBrownianReal B P) (s t : NNReal) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist s.1 t.1)) P :=
  hB.hasLaw_sub s t

/-- Every finite moment needed in a Kolmogorov–Chentsov argument exists for a
pre-Brownian increment. -/
theorem memLp_brownianIncrement
    (hB : IsPreBrownianReal B P) (s t : NNReal)
    (p : ENNReal) (hp : p ≠ ∞) :
    MemLp (B s - B t) p P := by
  exact (hB.hasLaw_sub s t).memLp
    (memLp_id_gaussianReal' p hp)

/-- A centered real Gaussian variable is sub-Gaussian with its variance as
variance proxy.  This packages the exact MGF and exponential integrability
facts from Mathlib in the form used by chaining estimates. -/
theorem hasSubgaussianMGF_of_hasLaw_centeredGaussian
    {X : Ω → ℝ} {v : NNReal}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    HasSubgaussianMGF X v P := by
  constructor
  · intro u
    exact hX.integrable_comp (integrable_exp_mul_gaussianReal u)
  · intro u
    rw [mgf_gaussianReal hX]
    simp

/-- Brownian increments have the exact sub-Gaussian variance proxy
`nndist s t`. -/
theorem hasSubgaussianMGF_brownianIncrement
    (hB : IsPreBrownianReal B P) (s t : NNReal) :
    HasSubgaussianMGF (B s - B t) (nndist s.1 t.1) P :=
  hasSubgaussianMGF_of_hasLaw_centeredGaussian (hB.hasLaw_sub s t)

/-- The standard one-sided Gaussian Chernoff bound for every pre-Brownian increment.
This is the quantitative estimate summed over dyadic edges in the
Kolmogorov–Chentsov/Borel–Cantelli argument. -/
theorem measureReal_brownianIncrement_ge_le
    (hB : IsPreBrownianReal B P) (s t : NNReal)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ B s ω - B t ω} ≤
      Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) := by
  exact (hasSubgaussianMGF_brownianIncrement hB s t).measure_ge_le hε

/-- The two-sided increment tail needed for dyadic chaining.  It is obtained
from the two one-sided Gaussian bounds and costs only the factor `2`. -/
theorem measureReal_abs_brownianIncrement_ge_le
    (hB : IsPreBrownianReal B P) (s t : NNReal)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |B s ω - B t ω|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) := by
  let A : Set Ω := {ω | ε ≤ B s ω - B t ω}
  let C : Set Ω := {ω | ε ≤ -(B s ω - B t ω)}
  have hset : {ω | ε ≤ |B s ω - B t ω|} = A ∪ C := by
    ext ω
    simp only [A, C, Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    P.real (A ∪ C) ≤ P.real A + P.real C :=
      measureReal_union_le A C
    _ ≤ Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) +
        Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) := by
      gcongr
      · exact measureReal_brownianIncrement_ge_le hB s t hε
      · exact
          (hasSubgaussianMGF_brownianIncrement hB s t).neg.measure_ge_le hε
    _ = 2 * Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) := by ring

/-- Finite-level chaining union bound.  Taking the index type to be the edges
of a dyadic mesh gives exactly the estimate which is subsequently summed over
mesh levels in the Borel–Cantelli argument. -/
theorem measureReal_iUnion_abs_brownianIncrement_ge_le
    {ι : Type*} [Fintype ι] (hB : IsPreBrownianReal B P)
    (s t : ι → NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real (⋃ i, {ω | ε ≤ |B (s i) ω - B (t i) ω|}) ≤
      ∑ i, 2 * Real.exp
        (-ε ^ 2 / (2 * (nndist (s i).1 (t i).1 : ℝ))) := by
  calc
    P.real (⋃ i, {ω | ε ≤ |B (s i) ω - B (t i) ω|}) ≤
        ∑ i, P.real {ω | ε ≤ |B (s i) ω - B (t i) ω|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, 2 * Real.exp
        (-ε ^ 2 / (2 * (nndist (s i).1 (t i).1 : ℝ))) := by
      gcongr with i
      exact measureReal_abs_brownianIncrement_ge_le hB (s i) (t i) hε

/-- All finite moments for increments of the canonical raw-coordinate process. -/
theorem memLp_rawCoordinateIncrement
    (hcont : BrownianCylinderContinuityAtEmpty) (s t : NNReal)
    (p : ENNReal) (hp : p ≠ ∞) :
    MemLp (rawCoordinateProcess s - rawCoordinateProcess t) p
      (brownianRawMeasure hcont) :=
  memLp_brownianIncrement
    (isPreBrownianReal_rawCoordinateProcess hcont) s t p hp

/-- Exact sub-Gaussian control of each canonical raw-coordinate increment. -/
theorem hasSubgaussianMGF_rawCoordinateIncrement
    (hcont : BrownianCylinderContinuityAtEmpty) (s t : NNReal) :
    HasSubgaussianMGF
      (rawCoordinateProcess s - rawCoordinateProcess t)
      (nndist s.1 t.1) (brownianRawMeasure hcont) :=
  hasSubgaussianMGF_brownianIncrement
    (isPreBrownianReal_rawCoordinateProcess hcont) s t

/-- Standard Gaussian Chernoff tail control on canonical raw-coordinate increments. -/
theorem measureReal_rawCoordinateIncrement_ge_le
    (hcont : BrownianCylinderContinuityAtEmpty) (s t : NNReal)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (brownianRawMeasure hcont).real
        {ω | ε ≤ rawCoordinateProcess s ω - rawCoordinateProcess t ω} ≤
      Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) :=
  measureReal_brownianIncrement_ge_le
    (isPreBrownianReal_rawCoordinateProcess hcont) s t hε

/-- Two-sided exponential tail control on canonical raw-coordinate
increments, in the exact form used for a dyadic union bound. -/
theorem measureReal_abs_rawCoordinateIncrement_ge_le
    (hcont : BrownianCylinderContinuityAtEmpty) (s t : NNReal)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (brownianRawMeasure hcont).real
        {ω | ε ≤
          |rawCoordinateProcess s ω - rawCoordinateProcess t ω|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (nndist s.1 t.1 : ℝ))) :=
  measureReal_abs_brownianIncrement_ge_le
    (isPreBrownianReal_rawCoordinateProcess hcont) s t hε

/-- Finite-level union bound for any chosen family of edges of the canonical
raw-coordinate process (in particular, for every finite dyadic mesh). -/
theorem measureReal_iUnion_abs_rawCoordinateIncrement_ge_le
    {ι : Type*} [Fintype ι]
    (hcont : BrownianCylinderContinuityAtEmpty)
    (s t : ι → NNReal) {ε : ℝ} (hε : 0 ≤ ε) :
    (brownianRawMeasure hcont).real
        (⋃ i, {ω | ε ≤
          |rawCoordinateProcess (s i) ω -
            rawCoordinateProcess (t i) ω|}) ≤
      ∑ i, 2 * Real.exp
        (-ε ^ 2 / (2 * (nndist (s i).1 (t i).1 : ℝ))) :=
  measureReal_iUnion_abs_brownianIncrement_ge_le
    (isPreBrownianReal_rawCoordinateProcess hcont) s t hε

end BrownianKolmogorovChentsovClosure

end BlockBand.SourceProcess.WienerRecovery.CEH
