module

public import BlockBand.Critical.GlobalSource.Tightness
public import BlockBand.Critical.GlobalSource.SourceSequences
public import BlockBand.Critical.GlobalSource.CharTests

/-!
# Global Gaussian source: the `M`-sampled finite-width laws

For fixed `M`, sample `M` i.i.d. birth times per probe group from `probeBirthLaw` (density
`q_a(t/τ)/m_a`), put a tag of mass `m_a` at each, and group the source matrix of the remaining
path (`n - 3` blocks). Conditional on the times these are tags of the complex source law, so by
that law along `(W_j, n_j - 3)` (`ComplexSourceLimitAlongSequences`) and dominated convergence in
the times, the finite-width expectations converge to `sampledProbeValue`.

* `isProbabilityMeasure_probeBirthLaw`: the birth law has mass one.
* `sampledProbeMatrix`, `sampledLaw`, `measurable_sampledProbeMatrix`.
* `tendsto_integral_sampledProbeMatrix`: convergence of the sampled finite-width expectations.
* `continuous_sampledProbeValue`: continuity in a parameter of the test (used for Lévy
  continuity in `exists_sampledLimitLaw`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

attribute [local instance] sourceData_borelSpace

/-- `∫_{[0,τ]} q(t/τ) dt = τ ∫_𝕋 q` (Haar probability measure on `𝕋 = ℝ/ℤ`). -/
theorem integral_Icc_comp_div (τ : ℝ) (hτ : 0 < τ) (Q : C(BlockBand.Torus, ℝ)) :
    ∫ t in Set.Icc 0 τ, Q (QuotientAddGroup.mk (t / τ)) = τ * ∫ r, Q r := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ.le,
    intervalIntegral.integral_comp_div (fun u : ℝ => Q (QuotientAddGroup.mk u)) hτ.ne',
    zero_div, div_self hτ.ne', smul_eq_mul]
  congr 1
  have := AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) 0 (fun r => Q r)
  simpa using this

/-- `probeBirthLaw τ Q` (density `q(t/τ)/m` on `[0,τ]`, uniform for a zero-mass profile) is a
probability measure for `τ > 0`, `q ≥ 0`. -/
theorem isProbabilityMeasure_probeBirthLaw {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) : IsProbabilityMeasure (probeBirthLaw τ Q) := by
  constructor
  unfold probeBirthLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  by_cases hm : 0 < probeMass τ Q
  · have hd : ∀ t, birthDensity τ Q t = Q (QuotientAddGroup.mk (t / τ)) / probeMass τ Q := by
      intro t; simp only [birthDensity, hm, ↓reduceIte]
    simp_rw [hd]
    have hcont : Continuous fun t : ℝ => Q (QuotientAddGroup.mk (t / τ)) / probeMass τ Q := by
      fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal
      (hcont.continuousOn.integrableOn_compact isCompact_Icc)
      (Filter.Eventually.of_forall fun t => div_nonneg (hQ _) hm.le)]
    rw [integral_div, integral_Icc_comp_div τ hτ Q]
    unfold probeMass at hm ⊢
    rw [div_self hm.ne', ENNReal.ofReal_one]
  · have hd : ∀ t, birthDensity τ Q t = τ⁻¹ := by
      intro t; simp only [birthDensity, hm, ↓reduceIte]
    simp_rw [hd]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hτ.ne', ENNReal.ofReal_one]

/-- The `J·M` independent sampled birth times form a probability law. -/
theorem isProbabilityMeasure_sampledBirthLaw {τ : ℝ} (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) (M : ℕ) :
    IsProbabilityMeasure (sampledBirthLaw τ Q M) := by
  have := fun i : Fin (J * M) => isProbabilityMeasure_probeBirthLaw hτ (hQ (tagGroup i))
  unfold sampledBirthLaw
  infer_instance

/-- `J·M` birth times and the probed path, at width `W`. -/
abbrev SampledSample (W J M : ℕ) := (Fin (J * M) → ℝ) × ProbedPath W (J * M)

/-- i.i.d. birth times (`sampledBirthLaw`) independent of `probedPathLaw`. -/
def sampledLaw (τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ)) (M W : ℕ) (b : ℝ) :
    Measure (SampledSample W J M) :=
  (sampledBirthLaw τ Q M).prod (probedPathLaw W (J * M) b)

/-- **The `M`-sampled finite-width probe matrix**: `complexSourceK` of the remaining path of `n − 3`
blocks, with mass-`m_a` tags born at the sampled times, grouped by `groupedSourceMatrix`
(coefficient `1/M`; zero-mass groups are zero). -/
def sampledProbeMatrix (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (M W n : ℕ) (y : SampledSample W J M) : Matrix (Fin J) (Fin J) ℂ :=
  groupedSourceMatrix τ Q M
    (complexSourceK b E W (probePathLength n) y.1 (tagMasses τ Q M) y.2)

/-- `probeColumns` is jointly Borel in times and Gaussians. -/
theorem measurable_probeColumns (W n np : ℕ) (m : Fin np → ℝ) :
    Measurable fun y : (Fin np → ℝ) × (Fin np → Fin W → ℂ) => probeColumns W n y.1 m y.2 := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun j => ?_
  simp only [probeColumns]
  refine Measurable.ite ?_ (measurable_const.mul ((measurable_pi_apply x.2).comp
    ((measurable_pi_apply j).comp measurable_snd))) measurable_const
  have hf : Measurable fun y : (Fin np → ℝ) × (Fin np → Fin W → ℂ) =>
      ⌊(W : ℝ) * y.1 j⌋₊ :=
    Nat.measurable_floor.comp (measurable_const.mul ((measurable_pi_apply j).comp measurable_fst))
  exact hf (MeasurableSet.of_discrete (s := {k : ℕ | k < n ∧ x.1.val = n - 1 - k}))

/-- `complexSourceK` is jointly Borel in times and path. -/
theorem measurable_complexSourceK (b E : ℝ) (W n np : ℕ) (m : Fin np → ℝ) :
    Measurable fun y : (Fin np → ℝ) × ProbedPath W np => complexSourceK b E W n y.1 m y.2 := by
  have hP : Measurable fun y : (Fin np → ℝ) × ProbedPath W np => probeColumns W n y.1 m y.2.2 :=
    (measurable_probeColumns W n np m).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hG : Measurable fun y : (Fin np → ℝ) × ProbedPath W np =>
      (fullInverse b E W n y.2.1).toBlocks₁₁ := by
    have h : Measurable fun y : (Fin np → ℝ) × ProbedPath W np => fullInverse b E W n y.2.1 :=
      (measurable_matrix_inv.comp (measurable_fullPathMatrix b E W n)).comp
        (measurable_fst.comp measurable_snd)
    refine Measurable.of_eval fun x => Measurable.of_eval fun x' => ?_
    exact (measurable_pi_apply (Sum.inl x')).comp ((measurable_pi_apply (Sum.inl x)).comp h)
  refine Measurable.of_eval fun i => Measurable.of_eval fun i' => ?_
  simp only [complexSourceK, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.measurable_sum _ fun x _ => Measurable.mul ?_ ?_
  · refine Finset.measurable_sum _ fun x' _ => Measurable.mul ?_ ?_
    · exact (continuous_star.measurable).comp
        ((measurable_pi_apply i).comp ((measurable_pi_apply x').comp hP))
    · exact (measurable_pi_apply x).comp ((measurable_pi_apply x').comp hG)
  · exact (measurable_pi_apply i').comp ((measurable_pi_apply x).comp hP)

/-- `sampledProbeMatrix` is Borel. -/
theorem measurable_sampledProbeMatrix (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (M W n : ℕ) : Measurable (sampledProbeMatrix b E τ Q M W n) := by
  have hK := measurable_complexSourceK b E W (probePathLength n) (J * M) (tagMasses τ Q M)
  refine Measurable.of_eval fun a => Measurable.of_eval fun c => ?_
  simp only [sampledProbeMatrix, groupedSourceMatrix]
  split_ifs
  · refine measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun i' _ => ?_)
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hK)
  · exact measurable_const

/-- The grouping map `groupedSourceMatrix` is continuous. -/
theorem continuous_groupedSourceMatrix (τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (M : ℕ) : Continuous (groupedSourceMatrix τ Q M) := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [groupedSourceMatrix]
  split_ifs
  · exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _
      fun i' _ => (continuous_apply _).comp (continuous_apply _))
  · exact continuous_const

/-- Component `0` of the source data is `𝒦`. -/
theorem complexSourceData_zero (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ)
    (x : ProbedPath W np) : complexSourceData b E W n τ m x 0 = complexSourceK b E W n τ m x := by
  simp [complexSourceData]

/-- Along a critical sequence the remaining path length satisfies `(n_j - 3)/W_j → τ`. -/
theorem tendsto_probePathLength_div (τ : ℝ) (s : BlockBand.CriticalSequence τ) :
    Tendsto (fun j => (probePathLength (s.n j) : ℝ) / s.W j) atTop (𝓝 τ) := by
  have hW : Tendsto (fun j => (s.W j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have h3 : Tendsto (fun j => (3 : ℝ) / s.W j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hW
  have := s.ratio_tendsto.sub h3
  rw [sub_zero] at this
  refine this.congr fun j => ?_
  unfold probePathLength
  have h4 := s.n_ge_four j
  rw [Nat.cast_sub (by omega), sub_div]
  norm_num

/-- A bounded continuous test of a Borel map is integrable under a finite measure. -/
theorem integrable_bcf_comp {α X : Type*} [MeasurableSpace α] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure α} [IsFiniteMeasure μ]
    (Φ : BoundedContinuousFunction X ℝ) {F : α → X} (hF : Measurable F) :
    Integrable (fun y => Φ (F y)) μ :=
  (integrable_const ‖Φ‖).mono' (Φ.continuous.measurable.comp hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => Φ.norm_coe_le_norm _)

/-- `probedPathLaw` is a probability measure. -/
instance isProbabilityMeasure_probedPathLaw (W np : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedPathLaw W np b) := by
  unfold probedPathLaw growthPathLaw; infer_instance

/-- The birth-time-conditional expectation of `Φ(sampledProbeMatrix)` at width `W` and ring size `n`. -/
def sampledInner (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ)) (M W n : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) (t : Fin (J * M) → ℝ) : ℝ :=
  ∫ x, Φ (groupedSourceMatrix τ Q M
    (complexSourceK b E W (probePathLength n) t (tagMasses τ Q M) x)) ∂probedPathLaw W (J * M) b

/-- The birth-time-conditional limit value `∫ Φ(grouped(y 0)) dν_M(t)` of `sampledProbeValue`. -/
def sampledLimitInner (τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ)) (M : ℕ)
    (ν : (Fin (J * M) → ℝ) → Measure (SourceData (J * M)))
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) (t : Fin (J * M) → ℝ) : ℝ :=
  ∫ y, Φ (groupedSourceMatrix τ Q M (y 0)) ∂(ν t)

/-- `sampledInner` is measurable in the birth times. -/
theorem stronglyMeasurable_sampledInner (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ))
    (M W n : ℕ) (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    StronglyMeasurable (sampledInner b E τ Q M W n Φ) :=
  (Φ.continuous.measurable.comp (measurable_sampledProbeMatrix b E τ Q M W n)).stronglyMeasurable.integral_prod_right'

/-- Fubini: integrate out the probed path first. -/
theorem integral_sampledLaw_eq (b E τ : ℝ) (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) (M W n : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    ∫ y, Φ (sampledProbeMatrix b E τ Q M W n y) ∂sampledLaw τ Q M W b =
      ∫ t, sampledInner b E τ Q M W n Φ t ∂sampledBirthLaw τ Q M := by
  have := isProbabilityMeasure_sampledBirthLaw hτ hQ M
  have : IsProbabilityMeasure (probedPathLaw W (J * M) b) := by
    unfold probedPathLaw growthPathLaw; infer_instance
  unfold sampledLaw
  exact integral_prod _ (integrable_bcf_comp Φ (measurable_sampledProbeMatrix b E τ Q M _ _))

/-- For a.e. admissible `t`, `sampledInner → sampledLimitInner` along every critical sequence
(`ComplexSourceLimitAlongSequences` at time `τ`, path lengths `n_j − 3`). -/
theorem ae_tendsto_sampledInner (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (s : BlockBand.CriticalSequence τ) (M : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    ∀ᵐ t ∂sampledBirthLaw τ Q M, Tendsto (fun j => sampledInner b E τ Q M (s.W j) (s.n j) Φ t)
      atTop (𝓝 (sampledLimitInner τ Q M (ν M) Φ t)) := by
  set gK : C(SourceData (J * M), Matrix (Fin J) (Fin J) ℂ) :=
    ⟨fun y => groupedSourceMatrix τ Q M (y 0),
      (continuous_groupedSourceMatrix τ Q M).comp (continuous_apply 0)⟩
  have hm : ∀ i, 0 ≤ tagMasses τ Q M i := fun i => probeMass_nonneg hτ.le (hQ _)
  filter_upwards [ae_isAdmissibleBirthTimes τ Q M] with t ht
  have h := hA.tendsto_seq hb hb' hE hE' ht.1 ht.2.1 hm ht.2.2 (hν M t ht) s.width_tendsto
    (tendsto_probePathLength_div τ s) (Φ.compContinuous gK)
  refine h.congr fun j => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [gK, complexSourceData_zero]

/-- **Fixed `M`.** For `0<b<1/2`, `-2<E<2`, `τ>0`, nonnegative profiles, a sampled family `ν`
(`IsSampledSourceFamily`), every critical sequence and bounded continuous `Φ`:
`E Φ(sampledProbeMatrix at (W_j, n_j)) → sampledProbeValue τ Q M (ν M) Φ`. Proof: the limit along
`(W_j, n_j − 3)` for a.e. `t`, then dominated convergence in `t`. -/
theorem tendsto_integral_sampledProbeMatrix (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (s : BlockBand.CriticalSequence τ) (M : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    Tendsto (fun j => ∫ y, Φ (sampledProbeMatrix b E τ Q M (s.W j) (s.n j) y)
      ∂sampledLaw τ Q M (s.W j) b) atTop (𝓝 (sampledProbeValue τ Q M (ν M) Φ)) := by
  have := isProbabilityMeasure_sampledBirthLaw hτ hQ M
  have hP : ∀ W, IsProbabilityMeasure (probedPathLaw W (J * M) b) := fun W => by
    unfold probedPathLaw growthPathLaw; infer_instance
  simp_rw [integral_sampledLaw_eq b E τ hτ hQ M]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖Φ‖)
    (fun j => (stronglyMeasurable_sampledInner b E τ Q M _ _ Φ).aestronglyMeasurable)
    (integrable_const _) (fun j => Filter.Eventually.of_forall fun t => ?_)
    (ae_tendsto_sampledInner hA hb hb' hE hE' hτ hQ hν s M Φ)
  have := hP (s.W j)
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x =>
    Φ.norm_coe_le_norm _)).trans ?_
  simp

/-- `sampledLimitInner` is a.e.-measurable in `t` (an a.e. limit of measurable functions). -/
theorem aestronglyMeasurable_sampledLimitInner (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (M : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    AEStronglyMeasurable (sampledLimitInner τ Q M (ν M) Φ) (sampledBirthLaw τ Q M) := by
  obtain ⟨s⟩ := exists_criticalSequence hτ.le
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun j => (stronglyMeasurable_sampledInner b E τ Q M (s.W j) (s.n j) Φ).aestronglyMeasurable)
    (ae_tendsto_sampledInner hA hb hb' hE hE' hτ hQ hν s M Φ)

/-- Continuity of `p ↦ sampledProbeValue τ Q M (ν M) (Ψ p)` for a jointly continuous, uniformly bounded
family of tests `Ψ` (dominated convergence twice; `ν_M(t)` is a probability for admissible `t`). -/
theorem continuous_sampledProbeValue (hA : ComplexSourceLimitAlongSequences)
    {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hτ : 0 < τ)
    {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (M : ℕ) {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P]
    (Ψ : P → BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ)
    (hΨ : Continuous fun p : P × Matrix (Fin J) (Fin J) ℂ => Ψ p.1 p.2) {B : ℝ}
    (hB : ∀ p K, ‖Ψ p K‖ ≤ B) :
    Continuous fun p => sampledProbeValue τ Q M (ν M) (Ψ p) := by
  have := isProbabilityMeasure_sampledBirthLaw hτ hQ M
  unfold sampledProbeValue
  refine continuous_of_dominated (bound := fun _ => B)
    (fun p => aestronglyMeasurable_sampledLimitInner hA hb hb' hE hE' hτ hQ hν M (Ψ p))
    (fun p => ?_) (integrable_const _) ?_
  · filter_upwards [ae_isAdmissibleBirthTimes τ Q M] with t ht
    have := (hν M t ht).1
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hB _ _)).trans ?_
    simp
  · filter_upwards [ae_isAdmissibleBirthTimes τ Q M] with t ht
    have := (hν M t ht).1
    refine continuous_of_dominated (bound := fun _ => B) (fun p => ?_)
      (fun p => Filter.Eventually.of_forall fun y => hB _ _) (integrable_const _)
      (Filter.Eventually.of_forall fun y => ?_)
    · exact ((Ψ p).continuous.comp ((continuous_groupedSourceMatrix τ Q M).comp
        (continuous_apply 0))).aestronglyMeasurable
    · exact hΨ.comp (continuous_id.prodMk continuous_const)

end BlockBand.Critical.GlobalSource
