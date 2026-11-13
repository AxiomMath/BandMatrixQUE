module

public import BlockBand.SourceProcess.ModelExist.AmbientRank
public import BlockBand.SourceProcess.ModelExist.ModelData
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Main
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorNoLoss
public import BlockBand.SourceProcess.BornUnique.Data
public import BlockBand.SourceProcess.ModelExist.LocShift

/-!
# The extended frame solution and its near rank

On the driver space over `S` with ambient `Amb K R`, for a `𝓖₀`-measurable sequence `tq` with
values in `[0,1]` a.s.:
* `stronglyMeasurable_extFrame`, `twoProjection_extFrame`: the extended initial frame is an
  admissible initial condition of the finite source equation;
* `ae_rank_of_sol`: for a global solution `X`, a.s. for all `t`, `rank(P X_t) ≥ rank P = K + R`
  (no rank loss, `principalMinorSum_near_ae_forall_pos`, unstopped by continuity).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal ComplexOrder

variable {K R : ℕ}

theorem measurable_extFrame (h : ℝ) : Measurable fun t : ℕ → ℝ => extFrame K R t h := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun col => ?_
  rcases col with y | i
  · rcases r with x | j
    · have := (measurable_pi_iff.1 ((measurable_pi_iff.1
        (measurable_initialFrame K Unit h)) x)) (Sum.inl y)
      exact this
    · simp [extFrame]
  · simp [extFrame]

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  SourceSDE.frobBorelSpace SourceSDE.matrixPseudoMetrizable

omit [IsProbabilityMeasure μ] in
theorem stronglyMeasurable_extFrame {tq : DriverSample S (SourceNoise (Amb K R)) → ℕ → ℝ}
    (htq : Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] tq) (h : ℝ) :
    StronglyMeasurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0]
      (fun x => extFrame K R (tq x) h) := by
  have : SecondCountableTopology (Matrix (Amb K R) (ExtCol K R) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Amb K R → ExtCol K R → ℂ))
  exact ((measurable_extFrame h).comp htq).stronglyMeasurable

omit [MeasurableSpace S] [IsProbabilityMeasure μ] in
/-- On a continuous path, the trace stop at a large level does not act before `t`. -/
theorem exists_level_stop {Ω : Type*} {G : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ ×
    Matrix (ExtCol K R) (ExtCol K R) ℂ} {ω : Ω} (hc : Continuous fun t => G t ω) (t : ℝ≥0) :
    ∃ L : ℝ, stoppedProcess G (gramTraceStop G L) t ω = G t ω := by
  have hf : Continuous fun s => ((G s ω).1.trace).re :=
    Complex.continuous_re.comp ((continuous_fst.comp hc).matrix_trace)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).bddAbove_image hf.continuousOn
  refine ⟨C + 1, ?_⟩
  rw [stoppedProcess_eq_stopTime, stopTime_eq_self]
  refine le_iInf₂ fun s hs => ?_
  by_contra hlt
  have hst : s ≤ t := (WithTop.coe_lt_coe.1 (not_le.1 hlt)).le
  have := hC ⟨s, ⟨zero_le, hst⟩, rfl⟩
  linarith

/-- **No loss of near rank, at all times.** -/
theorem ae_rank_of_sol {D0 : ℝ} (hD0 : 0 < D0)
    {ξ : DriverSample S (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    (hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] ξ)
    (hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, TwoProjection (ambP K R) (extSig K R) (ξ x))
    (hξB : ∀ x, 0 < principalMinorSum (K + R) (nearGram (ambP K R) (ξ x)))
    {X : ℝ≥0 → DriverSample S (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    (hX : IsSDESolution μ (sourceDrift D0 (K + R) (ambP K R)) (sourceDiffusion D0 (ambP K R)
      (extSig K R)) ξ X) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ t,
      (ambP K R).rank ≤ (ambP K R * X t x).rank := by
  have h𝒢 := ambient_isGramMartingaleSolution μ hD0 (isNearProjection_ambP K R)
    (isSignature_extSig K R) hξm hξc hX
  have hpos := principalMinorSum_near_ae_forall_pos hD0 (isSignature_extSig K R) h𝒢 (K + R)
  have hPh : (ambP K R)ᴴ = ambP K R := (isNearProjection_ambP K R).1
  have hPP : ambP K R * ambP K R = ambP K R := (isNearProjection_ambP K R).2.1
  filter_upwards [hpos, hX.2, h𝒢.continuous] with x hp h0 hc t
  have h0' : 0 < principalMinorSum (K + R) (gramPair (ambP K R) (X 0 x)).2 := by
    rw [h0]; exact hξB x
  obtain ⟨L, hL⟩ := exists_level_stop (G := fun t x => gramPair (ambP K R) (X t x)) hc t
  have h1 := hp h0' t L
  rw [hL] at h1
  have h2 := rank_le_of_principalMinorSum_pos _ _ h1
  have e : (gramPair (ambP K R) (X t x)).2 =
      (ambP K R * X t x)ᴴ * (ambP K R * X t x) := by
    simp only [gramPair, nearGram, conjTranspose_mul, hPh, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (ambP K R) (ambP K R), hPP]
  rw [e, rank_conjTranspose_mul_self] at h2
  rw [rank_ambP]
  exact h2

end BlockBand.SourceProcess.ModelExist
