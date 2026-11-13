module

public import BlockBand.SourceProcess.WienerRecovery.BrownianDyadicGaussianEnvelope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Measurable compact-path limits of Brownian dyadic interpolants

This module proves the deterministic completion and measurable-selection part of the
Brownian dyadic construction.  A sequence of measurable continuous interpolants on a
compact horizon whose successive uniform distances fail a summable bound with
geometrically small probability has an almost-sure limit in the continuous-map space.
The limit has a measurable path-space representative.  If the interpolants converge at
a fixed time to the raw coordinate, the representative agrees there almost everywhere.

The Brownian specialization uses the explicit Gaussian envelope for the dyadic bad
levels; it has no sample-path continuity hypothesis.  The finite-mesh data it needs
(measurable piecewise-linear dyadic interpolants, the containment of a large successive
uniform step in the corresponding dyadic bad-level event, and fixed-time convergence of
their evaluations) are the fields of `BrownianCompactDyadicInterpolationData`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace BrownianDyadicCompactExtension

open BrownianDyadicChainingClosure
open BrownianDyadicGaussianEnvelope
open ScalarWienerMeasureConstruction

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Continuous real paths on the compact nonnegative interval `[0,T]`. -/
abbrev CompactPath (T : NNReal) := C(Set.Icc (0 : NNReal) T, ℝ)

/-- The abstract completion step: measurable continuous approximants with a summable
successive-distance envelope and geometrically rare failures admit a measurable
continuous-path limit almost surely. -/
theorem exists_measurable_compactPath_limit_of_geometric_badStep
    (T : NNReal) (u : Ω → ℕ → CompactPath T) (d : ℕ → ℝ)
    (hu : ∀ n, AEMeasurable (fun ω => u ω n) μ)
    (hd : Summable d) {C q : ENNReal} (hC : C ≠ ∞) (hq : q < 1)
    (hbad : ∀ n, μ {ω | d n < dist (u ω n) (u ω n.succ)} ≤ C * q ^ n) :
    ∃ F : Ω → CompactPath T, Measurable F ∧
      ∀ᵐ ω ∂μ, Tendsto (u ω) atTop (𝓝 (F ω)) := by
  have hcauchy : ∀ᵐ ω ∂μ, CauchySeq (u ω) :=
    ae_cauchySeq_of_geometric_badStep_bound u d hd hC hq hbad
  have hlimit : ∀ᵐ ω ∂μ, ∃ f : CompactPath T,
      Tendsto (u ω) atTop (𝓝 f) := by
    filter_upwards [hcauchy] with ω hω
    exact cauchySeq_tendsto_of_complete hω
  exact measurable_limit_of_tendsto_metrizable_ae hu hlimit

/-- Evaluation of an almost-sure compact-path limit converges at every fixed time. -/
theorem ae_tendsto_eval_of_ae_tendsto_compactPath
    {T : NNReal} {u : Ω → ℕ → CompactPath T} {F : Ω → CompactPath T}
    (hlim : ∀ᵐ ω ∂μ, Tendsto (u ω) atTop (𝓝 (F ω)))
    (t : Set.Icc (0 : NNReal) T) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => u ω n t) atTop (𝓝 (F ω t)) := by
  filter_upwards [hlim] with ω hω
  exact (continuous_eval_const t).continuousAt.tendsto.comp hω

/-- Fixed-time identification by uniqueness of limits.  This requires
only convergence of the finite-mesh evaluations, not continuity of the raw sample
path. -/
theorem ae_eq_eval_of_approximants_tendsto
    {T : NNReal} {u : Ω → ℕ → CompactPath T} {F : Ω → CompactPath T}
    (hlim : ∀ᵐ ω ∂μ, Tendsto (u ω) atTop (𝓝 (F ω)))
    (X : Set.Icc (0 : NNReal) T → Ω → ℝ)
    (hX : ∀ t, ∀ᵐ ω ∂μ,
      Tendsto (fun n => u ω n t) atTop (𝓝 (X t ω)))
    (t : Set.Icc (0 : NNReal) T) :
    (fun ω => F ω t) =ᵐ[μ] X t := by
  filter_upwards [ae_tendsto_eval_of_ae_tendsto_compactPath hlim t, hX t]
    with ω hF hraw
  exact tendsto_nhds_unique hF hraw

/-- Finite-mesh interpolation data for one Brownian compact horizon: it consists of
measurable continuous interpolants, a deterministic containment of each excessive
successive uniform step in the dyadic bad event, and fixed-time
convergence to the canonical raw coordinate.  It does **not** assume any raw-path
continuity. -/
structure BrownianCompactDyadicInterpolationData
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) where
  approximant : BrownianRawPath → ℕ → CompactPath T
  aemeasurable_approximant : ∀ n,
    AEMeasurable (fun ω => approximant ω n) (brownianRawMeasure hcont)
  badStep_subset : ∀ n,
    {ω | compactDyadicModulus T n <
      dist (approximant ω n) (approximant ω n.succ)} ⊆
      dyadicBadLevel rawCoordinateProcess T (compactDyadicModulus T) n
  eval_tendsto : ∀ t : Set.Icc (0 : NNReal) T,
    ∀ᵐ ω ∂(brownianRawMeasure hcont),
      Tendsto (fun n => approximant ω n t) atTop
        (𝓝 (rawCoordinateProcess t.1 ω))

/-- The explicit Gaussian envelope plus concrete finite-mesh interpolation data produce
one measurable continuous-path representative on `[0,T]`, with fixed-time almost-
everywhere identification throughout that interval. -/
theorem exists_measurable_compactPath_modification
    (hcont : BrownianCylinderContinuityAtEmpty) (T : NNReal) (hT : 0 < T)
    (data : BrownianCompactDyadicInterpolationData hcont T) :
    ∃ F : BrownianRawPath → CompactPath T,
      Measurable F ∧
      (∀ᵐ ω ∂(brownianRawMeasure hcont),
        Tendsto (data.approximant ω) atTop (𝓝 (F ω))) ∧
      ∀ t : Set.Icc (0 : NNReal) T,
        (fun ω => F ω t) =ᵐ[brownianRawMeasure hcont]
          rawCoordinateProcess t.1 := by
  let _ := isProbabilityMeasure_brownianRawMeasure hcont
  have hbad : ∀ n,
      brownianRawMeasure hcont
          {ω | compactDyadicModulus T n <
            dist (data.approximant ω n) (data.approximant ω n.succ)} ≤
        gaussianDyadicRatioENNReal * gaussianDyadicRatioENNReal ^ n := by
    intro n
    exact le_trans (measure_mono (data.badStep_subset n))
      (measure_dyadicBadLevel_compactDyadicModulus_le
        (isPreBrownianReal_rawCoordinateProcess hcont) T hT n)
  obtain ⟨F, hFmeas, hFlim⟩ :=
    exists_measurable_compactPath_limit_of_geometric_badStep
      T data.approximant (compactDyadicModulus T)
      data.aemeasurable_approximant (summable_compactDyadicModulus T)
      (C := gaussianDyadicRatioENNReal) (q := gaussianDyadicRatioENNReal)
      (by simp [gaussianDyadicRatioENNReal])
      gaussianDyadicRatioENNReal_lt_one hbad
  refine ⟨F, hFmeas, hFlim, ?_⟩
  intro t
  exact ae_eq_eval_of_approximants_tendsto hFlim
    (fun t ω => rawCoordinateProcess t.1 ω) data.eval_tendsto t

end BrownianDyadicCompactExtension

end BlockBand.SourceProcess.WienerRecovery.CEH
