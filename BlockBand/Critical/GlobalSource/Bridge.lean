module

public import BlockBand.Critical.GlobalSource.Uniqueness
public import BlockBand.Critical.GlobalSource.Measurability
public import BlockBand.Critical.GlobalSource.Assembly

/-!
# Global Gaussian source: reduction to the sampling estimates

* `matrixCoord`: the real-coordinate homeomorphism `Matrix (Fin J) (Fin J) ℂ ≃ₜ ℝ^{J×J×2}`
  (Euclidean), used to test matrix laws by characteristic functions `exp(i⟨t,·⟩)`.
* `globalProbeMatrixLaw`: the law of `𝒦_W` as a probability measure (`measurable_globalProbeMatrix`).
* `isGlobalProbeCriticalLimit_of_tendsto`: weak convergence of the laws of `𝒦_W` along every
  critical sequence gives the joint `(𝒦_W, B_W)` statement `IsGlobalProbeCriticalLimit`.
* `exists_criticalSequence`: critical sequences exist for every `τ ≥ 0`.
* `globalGaussianSource_of_sampling`: the reduction. Its hypotheses are:
  - probability measures `ρ_M` that represent the `M`-sampled values;
  - along each critical sequence, finite-width sampled laws `σ_{M,j}` with `σ_{M,j} → ρ_M`;
  - the uniform-in-width Lindeberg bound between `𝒦_W` and the sampled matrices on
    characteristic-function tests;
  - tightness of the laws of `𝒦_W`.
  Conclusion: `∃! κ, IsGlobalProbeLaw b E τ Q κ ∧ IsGlobalProbeCriticalLimit b E τ Q κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CriticalEntire
open scoped Matrix

/-!
## Real coordinates of complex matrices
-/

/-- Real coordinates `(Re K_{ac}, Im K_{ac})` of a complex `J×J` matrix, as a homeomorphism onto
the Euclidean space `ℝ^{J×J×2}`. The tests `exp(i⟨t, matrixCoord K⟩)` are the characteristic
tests of the real and imaginary entries (bounded smooth tests of the finitely many real
and imaginary entries). -/
def matrixCoord (J : ℕ) :
    Matrix (Fin J) (Fin J) ℂ ≃ₜ EuclideanSpace ℝ (Fin J × Fin J × Fin 2) where
  toFun K := WithLp.toLp 2 fun p => if p.2.2 = 0 then (K p.1 p.2.1).re else (K p.1 p.2.1).im
  invFun v := fun a c => ((v (a, c, 0) : ℝ) : ℂ) + ((v (a, c, 1) : ℝ) : ℂ) * Complex.I
  left_inv K := by
    funext a c
    apply Complex.ext <;> simp
  right_inv v := by
    ext ⟨a, c, r⟩
    fin_cases r <;> simp
  continuous_toFun := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    refine continuous_pi fun p => ?_
    split_ifs
    · exact Complex.continuous_re.comp ((continuous_apply _).comp (continuous_apply _))
    · exact Complex.continuous_im.comp ((continuous_apply _).comp (continuous_apply _))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun c => ?_
    have h0 : Continuous fun v : EuclideanSpace ℝ (Fin J × Fin J × Fin 2) => v (a, c, 0) :=
      (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
    have h1 : Continuous fun v : EuclideanSpace ℝ (Fin J × Fin J × Fin 2) => v (a, c, 1) :=
      (continuous_apply _).comp (PiLp.continuous_ofLp 2 _)
    exact (Complex.continuous_ofReal.comp h0).add
      ((Complex.continuous_ofReal.comp h1).mul continuous_const)

/-- Pushing forward by `matrixCoord` and back is the identity on probability measures. -/
theorem map_matrixCoord_symm_map {J : ℕ} (μ : ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)) :
    (μ.map (matrixCoord J)).map (matrixCoord J).symm = μ := by
  apply Subtype.ext
  change ((μ : Measure (Matrix (Fin J) (Fin J) ℂ)).map (matrixCoord J)).map
    (matrixCoord J).symm = μ
  rw [Measure.map_map (matrixCoord J).symm.continuous.measurable
    (matrixCoord J).continuous.measurable]
  simp

/-!
## The law of `𝒦_W`
-/

/-- **The law of `𝒦_W`** under the path law and the independent probes, as a Borel probability
measure on the complex `J×J` matrices. -/
def globalProbeMatrixLaw (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ) :=
  ⟨(globalProbeLaw W n J b).map (globalProbeMatrix b E W n Q),
    inferInstance⟩

/-- `B = probeGram K = -η⁻¹ Im K` is continuous in `K`. -/
theorem continuous_probeGram (b E : ℝ) (J : ℕ) :
    Continuous (fun K : Matrix (Fin J) (Fin J) ℂ => probeGram b E K) := by
  have h : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => K - Kᴴ :=
    continuous_id.sub continuous_id.matrix_conjTranspose
  unfold probeGram BlockBand.Internal.Contracts.Critical.imPart
  exact (h.const_smul ((2 * Complex.I)⁻¹)).const_smul (-(((etaZ b E)⁻¹ : ℝ) : ℂ))

/-- **From convergence of the laws of `𝒦_W` to the joint statement.** If along every critical
sequence the laws of `𝒦_W` converge weakly to `κ`, then the joint laws of `(𝒦_W, B_W)` converge to
those of `(𝒦, probeGram 𝒦)`, `𝒦 ~ κ`, i.e. `IsGlobalProbeCriticalLimit` (continuous mapping by
`K ↦ (K, -η⁻¹ Im K)`). -/
theorem isGlobalProbeCriticalLimit_of_tendsto {b E τ : ℝ} {J : ℕ} {Q : Fin J → C(Torus, ℝ)}
    {κ : ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)}
    (h : ∀ s : CriticalSequence τ,
      Tendsto (fun j => globalProbeMatrixLaw b E (s.W j) (s.n j) Q) atTop (𝓝 κ)) :
    IsGlobalProbeCriticalLimit b E τ Q κ := by
  intro s Φ
  let g : C(Matrix (Fin J) (Fin J) ℂ, Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) :=
    ⟨fun K => (K, probeGram b E K), continuous_id.prodMk (continuous_probeGram b E J)⟩
  have hlim := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (h s))
    (Φ.compContinuous g)
  refine hlim.congr fun j => ?_
  change ∫ K, Φ (g K) ∂((globalProbeLaw (s.W j) (s.n j) J b).map
    (globalProbeMatrix b E (s.W j) (s.n j) Q)) = _
  exact integral_map (f := fun K => Φ (g K))
    (measurable_globalProbeMatrix b E (s.W j) (s.n j) Q).aemeasurable
    (Φ.continuous.comp g.continuous).aestronglyMeasurable

/-!
## Critical sequences exist
-/

/-- For every `τ ≥ 0` there is a critical sequence: `W_j = j+1`, `n_j = ⌊τ(j+1)⌋₊ + 4`. -/
theorem exists_criticalSequence {τ : ℝ} (hτ : 0 ≤ τ) : Nonempty (CriticalSequence τ) := by
  refine ⟨⟨fun j => ⌊τ * ((j : ℝ) + 1)⌋₊ + 4, fun j => j + 1, fun j => by omega,
    fun j => by omega, tendsto_add_atTop_nat 1, ?_⟩⟩
  have hc : ∀ c : ℝ, Tendsto (fun j : ℕ => τ + c * (1 / ((j : ℝ) + 1))) atTop (𝓝 τ) := by
    intro c
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hc 3) (hc 4) (fun j => ?_) (fun j => ?_)
  · have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hfl := Nat.lt_floor_add_one (τ * ((j : ℝ) + 1))
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [le_div_iff₀ hpos]
    field_simp
    nlinarith
  · have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hfl := Nat.floor_le (mul_nonneg hτ hpos.le)
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [div_le_iff₀ hpos]
    field_simp
    nlinarith

/-!
## The reduction
-/

/-- **Reduction of the global Gaussian source statement to the sampling estimates**, at fixed
`b, E`, `τ > 0` and profiles `Q`. Hypotheses:
* `hν` — a sampled source family (from `exists_isSampledSourceFamily`);
* `hρ` — `ρ_M` represents the `M`-sampled value of `ν`;
* `hσ` — along each critical sequence `s`, the finite-width `M`-sampled laws `σ s M j` converge
  weakly to `ρ_M` as `j → ∞`;
* `hε`, `happrox` — the Lindeberg bound of the global probe replacement on characteristic tests of
  the real coordinates: for large `j`, `|φ_{𝒦_W}(t) - φ_{σ_{M,j}}(t)| ≤ ε_s(M, t) → 0` as `M → ∞`
  (uniform in width);
* `htight` — the laws of `𝒦_W` are tight along each critical sequence.
Conclusion: `∃! κ, IsGlobalProbeLaw b E τ Q κ ∧ IsGlobalProbeCriticalLimit b E τ Q κ`. -/
theorem globalGaussianSource_of_sampling {b E τ : ℝ} (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(Torus, ℝ)}
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν)
    (ρ : ℕ → ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ))
    (hρ : ∀ M (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ),
      ∫ K, Φ K ∂(ρ M : Measure (Matrix (Fin J) (Fin J) ℂ)) = sampledProbeValue τ Q M (ν M) Φ)
    (σ : CriticalSequence τ → ℕ → ℕ → ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ))
    (hσ : ∀ s M, Tendsto (σ s M) atTop (𝓝 (ρ M)))
    (ε : CriticalSequence τ → ℕ → EuclideanSpace ℝ (Fin J × Fin J × Fin 2) → ℝ)
    (hε : ∀ s t, Tendsto (fun M => ε s M t) atTop (𝓝 0))
    (happrox : ∀ s M t, ∀ᶠ j in atTop,
      ‖charFun (((globalProbeMatrixLaw b E (s.W j) (s.n j) Q).map (matrixCoord J) :
          ProbabilityMeasure _) : Measure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2))) t -
        charFun ((((σ s M j).map (matrixCoord J)) : ProbabilityMeasure _) :
          Measure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2))) t‖ ≤ ε s M t)
    (htight : ∀ s : CriticalSequence τ,
      IsTightMeasureSet {((globalProbeMatrixLaw b E (s.W j) (s.n j) Q :
        ProbabilityMeasure _) : Measure (Matrix (Fin J) (Fin J) ℂ)) | j}) :
    ∃! κ : Measure (Matrix (Fin J) (Fin J) ℂ),
      IsGlobalProbeLaw b E τ Q κ ∧ IsGlobalProbeCriticalLimit b E τ Q κ := by
  set e := matrixCoord J
  have hee : ∀ μ : ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ), (μ.map e).map e.symm = μ :=
    map_matrixCoord_symm_map
  -- pushed-forward objects on the Euclidean space
  let μ' : CriticalSequence τ → ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :=
    fun s j => (globalProbeMatrixLaw b E (s.W j) (s.n j) Q).map e
  let σ' : CriticalSequence τ → ℕ → ℕ →
      ProbabilityMeasure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :=
    fun s M j => (σ s M j).map e
  let ρ' : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :=
    fun M => (ρ M).map e
  have hσ' : ∀ s M, Tendsto (σ' s M) atTop (𝓝 (ρ' M)) := fun s M =>
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hσ s M) e.continuous
  have htight' : ∀ s, IsTightMeasureSet {((μ' s j : ProbabilityMeasure _) :
      Measure (EuclideanSpace ℝ (Fin J × Fin J × Fin 2))) | j} := by
    intro s
    refine ((htight s).map e.continuous).subset ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, rfl⟩
  obtain ⟨s₀⟩ := exists_criticalSequence hτ.le
  obtain ⟨κ', hρκ', -⟩ := exists_tendsto_of_sampling_approx (μ := μ' s₀) (ν := σ' s₀)
    (hε s₀) (happrox s₀) (hσ' s₀) (htight' s₀)
  -- the limit on matrices
  set κ : ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ) := κ'.map e.symm with hκdef
  have hρκ : Tendsto ρ atTop (𝓝 κ) := by
    have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hρκ' e.symm.continuous
    simpa [ρ', hee] using this
  have hμκ : ∀ s : CriticalSequence τ,
      Tendsto (fun j => globalProbeMatrixLaw b E (s.W j) (s.n j) Q) atTop (𝓝 κ) := by
    intro s
    have h1 := tendsto_of_sampling_approx (μ := μ' s) (ν := σ' s) (hε s) (happrox s) (hσ' s)
      hρκ'
    have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h1 e.symm.continuous
    simpa [μ', hee] using this
  have hlaw : IsGlobalProbeLaw b E τ Q κ := by
    refine isGlobalProbeLaw_of_one_family hν fun Φ => ?_
    have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hρκ Φ
    exact this.congr fun M => hρ M Φ
  refine ⟨κ, ⟨hlaw, isGlobalProbeCriticalLimit_of_tendsto hμκ⟩, fun κ'' hκ'' => ?_⟩
  exact isGlobalProbeLaw_unique hκ''.1 hlaw

end BlockBand.Critical.GlobalSource
