module

public import BlockBand.Critical.GlobalSource.Sampling

/-!
# Global Gaussian source: assembly from the Lindeberg bound

The global Gaussian source statement is assembled from

* `ComplexSourceLawContract` (fields `limit` for the sampled family and `extendedSourceMoments`
  for tightness),
* `ComplexSourceLimitAlongSequences` (the sampled source limit along every critical sequence), and
* the uniform-in-width Lindeberg replacement bound for the global probes, stated here as the `Prop`
  `GlobalProbeLindebergStatement`. It is proved elsewhere from `ComplexSourceLawContract`
  (`globalProbeLindebergBound_of_replacement` and `sourceReplacement_holds`); here it enters only
  as an explicit hypothesis of the reduction theorems below.

Contents:
* `sampledProbeMatrixLaw`: the law of the `M`-sampled finite-width matrix.
* `GlobalProbeLindebergBound`, `GlobalProbeLindebergStatement`: the Lindeberg estimate.
* `exists_sampledLimitLaw`: `sampledProbeValue` is integration against a probability measure
  `ρ_M` (Lévy continuity).
* `globalGaussianSource_of_lindeberg`, `globalGaussianSource_holds_of_lindeberg`: the reduction.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped InnerProductSpace RealInnerProductSpace
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws

/-- **Law of the `M`-sampled finite-width matrix** `sampledProbeMatrix` at width `W` and ring
size `n`, as a Borel measure on complex `J×J` matrices (push-forward of `sampledLaw`). -/
def sampledProbeMatrixLaw (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M W n : ℕ) :
    Measure (Matrix (Fin J) (Fin J) ℂ) :=
  (sampledLaw τ Q M W b).map (sampledProbeMatrix b E τ Q M W n)

/-- `sampledProbeMatrixLaw` is a probability measure (`τ > 0`, `q ≥ 0`). -/
theorem isProbabilityMeasure_sampledProbeMatrixLaw (b E : ℝ) {τ : ℝ} (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) (M W n : ℕ) :
    IsProbabilityMeasure (sampledProbeMatrixLaw b E τ Q M W n) := by
  have := isProbabilityMeasure_sampledBirthLaw hτ hQ M
  unfold sampledProbeMatrixLaw sampledLaw
  infer_instance

/-- **The uniform-in-width Lindeberg bound** for the global probe replacement, in
characteristic-function form, at fixed `(b, E, τ, Q)`. Proved from `ComplexSourceLawContract` in
`globalProbeLindebergBound_of_replacement`. -/
def GlobalProbeLindebergBound (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) : Prop :=
  ∀ s : CriticalSequence τ, ∃ ε : ℕ → EuclideanSpace ℝ (Fin J × Fin J × Fin 2) → ℝ,
    (∀ u, Tendsto (fun M => ε M u) atTop (𝓝 0)) ∧
    ∀ M u, ∀ᶠ j in atTop,
      ‖charFun (((globalProbeMatrixLaw b E (s.W j) (s.n j) Q :
          ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)) : Measure _).map (matrixCoord J)) u -
        charFun ((sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j)).map (matrixCoord J)) u‖ ≤
        ε M u

/-- `GlobalProbeLindebergBound` on the domain of `GlobalGaussianSourceStatement`: `0 < b < 1/2`,
`-2 < E < 2`, `τ > 0`, nonnegative continuous profiles. It follows from `ComplexSourceLawContract`
at every point of the domain (`globalProbeLindebergBound_of_replacement` with
`sourceReplacement_holds`). -/
def GlobalProbeLindebergStatement : Prop :=
  ∀ (b E : ℝ), 0 < b → b < 1 / 2 → -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (J : ℕ) (Q : Fin J → C(Torus, ℝ)), (∀ a x, 0 ≤ Q a x) →
      GlobalProbeLindebergBound b E τ.1 Q

/-- `E Φ(𝒦^{(M)}_W)` as an integral against `sampledProbeMatrixLaw`. -/
theorem integral_sampledProbeMatrixLaw (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (M W n : ℕ) {F : Matrix (Fin J) (Fin J) ℂ → ℝ} (hF : Continuous F) :
    ∫ K, F K ∂sampledProbeMatrixLaw b E τ Q M W n =
      ∫ y, F (sampledProbeMatrix b E τ Q M W n y) ∂sampledLaw τ Q M W b := by
  unfold sampledProbeMatrixLaw
  exact integral_map (measurable_sampledProbeMatrix b E τ Q M W n).aemeasurable
    hF.aestronglyMeasurable

/-- **The `M`-sampled limit law.** Domain as in `tendsto_integral_sampledProbeMatrix`.
There is a Borel probability measure `ρ_M` on complex `J×J` matrices with
`∫ Φ dρ_M = sampledProbeValue τ Q M (ν M) Φ` for every bounded continuous `Φ`; the `M`-sampled
finite-width laws converge to it along every critical sequence. Proof: convergence of the sampled laws along one critical
sequence, then Lévy continuity (`exists_tendsto_of_forall_integral_tendsto`); continuity of the
characteristic values from `continuous_sampledProbeValue`. Inputs: `hA` only. -/
theorem exists_sampledLimitLaw (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (M : ℕ) :
    ∃ ρ : ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ),
      ∀ Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ,
        ∫ K, Φ K ∂(ρ : Measure (Matrix (Fin J) (Fin J) ℂ)) = sampledProbeValue τ Q M (ν M) Φ := by
  set e := matrixCoord J
  set eC : C(Matrix (Fin J) (Fin J) ℂ, EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :=
    ⟨e, e.continuous⟩
  set eCs : C(EuclideanSpace ℝ (Fin J × Fin J × Fin 2), Matrix (Fin J) (Fin J) ℂ) :=
    ⟨e.symm, e.symm.continuous⟩
  obtain ⟨s⟩ := exists_criticalSequence hτ.le
  have hprob := isProbabilityMeasure_sampledProbeMatrixLaw b E hτ hQ M
  set μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) := fun j =>
    ProbabilityMeasure.map (⟨sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j), hprob _ _⟩ :
      ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)) e
  set L : BoundedContinuousFunction (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) ℝ → ℝ :=
    fun Φ => sampledProbeValue τ Q M (ν M) (Φ.compContinuous eC)
  have hL : ∀ Φ, Tendsto (fun j => ∫ x, Φ x ∂(μ j : Measure _)) atTop (𝓝 (L Φ)) := by
    intro Φ
    have h := tendsto_integral_sampledProbeMatrix hA hb hb' hE hE' hτ hQ hν s M
      (Φ.compContinuous eC)
    refine h.congr fun j => ?_
    change _ = ∫ x, Φ x ∂((sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j)).map e)
    rw [integral_map e.continuous.aemeasurable Φ.continuous.aestronglyMeasurable]
    exact (integral_sampledProbeMatrixLaw b E τ Q M _ _ (Φ.continuous.comp e.continuous)).symm
  have hcontΨ : ∀ (f : ℝ → ℝ), Continuous f → Continuous fun p :
      EuclideanSpace ℝ (Fin J × Fin J × Fin 2) × Matrix (Fin J) (Fin J) ℂ =>
        f ⟪e p.2, p.1⟫ := fun f hf =>
    hf.comp ((e.continuous.comp continuous_snd).inner continuous_fst)
  have hc : Continuous fun u => L (cosTest u) := by
    refine continuous_sampledProbeValue hA hb hb' hE hE' hτ hQ hν M
      (fun u => (cosTest u).compContinuous eC)
      (hcontΨ Real.cos Real.continuous_cos) (B := 1) fun u K => ?_
    simpa [cosTest] using Real.abs_cos_le_one _
  have hs : Continuous fun u => L (sinTest u) := by
    refine continuous_sampledProbeValue hA hb hb' hE hE' hτ hQ hν M
      (fun u => (sinTest u).compContinuous eC)
      (hcontΨ Real.sin Real.continuous_sin) (B := 1) fun u K => ?_
    simpa [sinTest] using Real.abs_sin_le_one _
  have hcont : ContinuousAt (fun u => ((L (cosTest u) : ℝ) : ℂ) + ((L (sinTest u) : ℝ) : ℂ) * I)
      0 :=
    ((continuous_ofReal.comp hc).add ((continuous_ofReal.comp hs).mul continuous_const)).continuousAt
  obtain ⟨ρ', -, hρ'⟩ := exists_tendsto_of_forall_integral_tendsto hL hcont
  refine ⟨ρ'.map e.symm, fun Φ => ?_⟩
  rw [ProbabilityMeasure.toMeasure_map, integral_map e.symm.continuous.aemeasurable
    Φ.continuous.aestronglyMeasurable]
  rw [show (fun x => Φ (e.symm x)) = fun x => (Φ.compContinuous eCs) x from rfl, hρ']
  simp only [L]
  congr 1
  ext K
  simp [eC, eCs]

/-- **Reduction of the global Gaussian source statement to the Lindeberg bound** at fixed
`(b, E, τ, Q)`, with the explicit hypothesis `GlobalProbeLindebergBound` (proved from
`ComplexSourceLawContract` in `globalProbeLindebergBound_of_replacement`). -/
theorem globalGaussianSource_of_lindeberg (hCS : ComplexSourceLawContract)
    (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    (hG2 : GlobalProbeLindebergBound b E τ Q) :
    ∃! κ : Measure (Matrix (Fin J) (Fin J) ℂ),
      IsGlobalProbeLaw b E τ Q κ ∧ IsGlobalProbeCriticalLimit b E τ Q κ := by
  obtain ⟨ν, hν⟩ := exists_isSampledSourceFamily hCS hb hb' hE hτ.le hQ
  have hρ := fun M => exists_sampledLimitLaw hA hb hb' hE.1 hE.2 hτ hQ hν M
  set ρ := fun M => Classical.choose (hρ M)
  have hprob := isProbabilityMeasure_sampledProbeMatrixLaw b E hτ hQ
  set σ : CriticalSequence τ → ℕ → ℕ → ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ) :=
    fun s M j => ⟨sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j), hprob _ _ _⟩
  have hσ : ∀ s M, Tendsto (σ s M) atTop (𝓝 (ρ M)) := by
    intro s M
    refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun Φ => ?_
    rw [Classical.choose_spec (hρ M) Φ]
    refine (tendsto_integral_sampledProbeMatrix hA hb hb' hE.1 hE.2 hτ hQ hν s M Φ).congr
      fun j => ?_
    exact (integral_sampledProbeMatrixLaw b E τ Q M _ _ Φ.continuous).symm
  set ε := fun s => Classical.choose (hG2 s)
  refine globalGaussianSource_of_sampling hτ hν ρ (fun M => Classical.choose_spec (hρ M)) σ hσ ε
    (fun s => (Classical.choose_spec (hG2 s)).1) (fun s M u => ?_)
    (fun s => isTightMeasureSet_globalProbeMatrixLaw hCS hb hb' hE.1 hE.2 hQ s)
  refine ((Classical.choose_spec (hG2 s)).2 M u).mono fun j hj => ?_
  convert hj using 4
  rw [ProbabilityMeasure.toMeasure_map]
  rfl

/-- **The global Gaussian source statement from the Lindeberg statement.**
`GlobalGaussianSourceStatement` follows from `ComplexSourceLawContract`,
`ComplexSourceLimitAlongSequences` and `GlobalProbeLindebergStatement` (the last follows from
`ComplexSourceLawContract` through `globalProbeLindebergBound_of_replacement` and
`sourceReplacement_holds`). -/
theorem globalGaussianSource_holds_of_lindeberg (hCS : ComplexSourceLawContract)
    (hA : ComplexSourceLimitAlongSequences) (hG2 : GlobalProbeLindebergStatement) :
    GlobalGaussianSourceStatement := by
  intro b E hb hb' hE τ J Q hQ
  exact globalGaussianSource_of_lindeberg hCS hA hb hb' hE τ.2 hQ (hG2 b E hb hb' hE τ J Q hQ)

end BlockBand.Critical.GlobalSource
