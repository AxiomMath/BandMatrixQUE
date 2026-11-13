module

public import BlockBand.Critical.GlobalSource.Sampling
public import BlockBand.Critical.Collar.Density.SpectralSum
public import BlockBand.Critical.JointRecovery.ExtractionMeasurable
public import BlockBand.Critical.JointRecovery.FiniteIdentity

/-!
# The entire law: measurability of the integrands

The integrals in the statement of the entire law involve several functions whose measurability is
needed so that `ProbabilityMeasure.map` and the Bochner integrals are not junk values:

* `D_W` itself: `JointRecovery.measurable_finiteEntireDeterminant`;
  `finiteEntireLaw_toMeasure` records that `finiteEntireLaw` is the push-forward.
* the phase: `continuous_closedSourcePhase`, `measurable_closedSourcePhase`;
* `𝒯 = Re 𝒦 + η B^{1/2} C B^{1/2}`: `measurable_closedSourceMatrix` (every `K`: `B = probeGram K`
  is always Hermitian, `probeGram_isHermitian`, and the Hermitian `cfc` is the Borel eigenvalue
  formula `Collar.Density.rawCfc`); the integrand of `ClosedSourceMomentValue`,
  `measurable_closedSourcePhase_closedSourceMatrix`, and the inner `𝖢`-integral,
  `stronglyMeasurable_closedSourceInner`;
* the sampled-time integrand `t ↦ ∫ Φ dν_t` of `sampledProbeValue`:
  `aestronglyMeasurable_sampledLimitInner_of_family` (a.e., from `IsComplexSourceLimit` alone);
* the sum over real zeros (integrand of `extractorLaplace`): `aestronglyMeasurable_extractionValue`
  (a.e. on laws carried by `JointRecovery.goodEntire`, which contains every critical limit).

No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CriticalEntire
open scoped Matrix

variable {J : ℕ}

/-- Square complex matrices (product topology) are second countable (local instance). -/
theorem matrix_secondCountableTopology (ι : Type*) [Fintype ι] :
    SecondCountableTopology (Matrix ι ι ℂ) :=
  inferInstanceAs (SecondCountableTopology (ι → ι → ℂ))

attribute [local instance] matrix_secondCountableTopology

/-- `Im K = (K - K*)/(2i)` is Hermitian. -/
theorem imPart_isHermitian {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) :
    (BlockBand.Internal.Contracts.Critical.imPart K).IsHermitian := by
  unfold BlockBand.Internal.Contracts.Critical.imPart
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
    star_mul', star_sub, star_inv₀, star_ofNat]
  simp [Complex.conj_I]
  ring

/-- `B = probeGram K = -η⁻¹ Im K` is Hermitian for every `K`. -/
theorem probeGram_isHermitian (b E : ℝ) {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) :
    (probeGram b E K).IsHermitian := by
  unfold probeGram
  have h := imPart_isHermitian K
  rw [Matrix.IsHermitian] at h ⊢
  rw [Matrix.conjTranspose_smul, h]
  congr 1
  simp

/-- `probeGram` is continuous. -/
theorem continuous_probeGram (b E : ℝ) {ι : Type*} [Fintype ι] :
    Continuous (fun K : Matrix ι ι ℂ => probeGram b E K) := by
  have h : Continuous fun K : Matrix ι ι ℂ => K - Kᴴ :=
    continuous_id.sub continuous_id.matrix_conjTranspose
  unfold probeGram BlockBand.Internal.Contracts.Critical.imPart
  exact (h.const_smul ((2 * Complex.I)⁻¹)).const_smul (-(((etaZ b E)⁻¹ : ℝ) : ℂ))

/-- `K ↦ B^{1/2} = cfc √ (probeGram K)` is Borel (every `K`: `B` is always Hermitian, and the
Hermitian `cfc` agrees with the eigenvalue formula `rawCfc`, which is Borel). -/
theorem measurable_sqrtProbeGram (b E : ℝ) :
    Measurable (fun K : Matrix (Fin J) (Fin J) ℂ => cfc Real.sqrt (probeGram b E K)) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  have hraw := BlockBand.Critical.Collar.Density.measurable_rawCfc
    (continuous_probeGram b E (ι := Fin J)).measurable
    (g := fun (_ : Unit) => Real.sqrt) (Real.continuous_sqrt.measurable.comp measurable_snd) x y
  have heq : (fun K : Matrix (Fin J) (Fin J) ℂ => cfc Real.sqrt (probeGram b E K) x y) =
      (fun p : Unit × Matrix (Fin J) (Fin J) ℂ =>
        BlockBand.Critical.Collar.Density.rawCfc Real.sqrt (probeGram b E p.2) x y) ∘
        (fun K => ((), K)) := by
    funext K
    simp only [Function.comp_apply]
    rw [BlockBand.Critical.Collar.Density.rawCfc_eq_cfc (probeGram_isHermitian b E K)]
  rw [heq]
  exact hraw.comp measurable_prodMk_left

/-- The algebraic part `(K, C, S) ↦ Re K + η S C S` of `closedSourceMatrix` is continuous. -/
theorem continuous_closedSourceAlgebra (b E : ℝ) :
    Continuous (fun x : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ ×
        Matrix (Fin J) (Fin J) ℂ =>
      matrixRePart x.1 + ((etaZ b E : ℝ) : ℂ) • (x.2.2 * x.2.1 * x.2.2)) := by
  have h0 : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => matrixRePart K := by
    unfold matrixRePart
    fun_prop
  have h1 : Continuous fun x : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ ×
      Matrix (Fin J) (Fin J) ℂ => matrixRePart x.1 := h0.comp continuous_fst
  have h2 : Continuous fun x : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ ×
      Matrix (Fin J) (Fin J) ℂ => x.2.2 * x.2.1 * x.2.2 :=
    ((continuous_snd.comp continuous_snd).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_snd.comp continuous_snd)
  fun_prop

/-- **`(K, C) ↦ 𝒯 = Re K + η B^{1/2} C B^{1/2}` is Borel.** -/
theorem measurable_closedSourceMatrix (b E : ℝ) :
    Measurable (fun p : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ =>
      closedSourceMatrix b E p.1 p.2) := by
  have hS : Measurable fun p : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ =>
      cfc Real.sqrt (probeGram b E p.1) := (measurable_sqrtProbeGram (J := J) b E).comp measurable_fst
  have hT : Measurable fun p : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ =>
      (p.1, p.2, cfc Real.sqrt (probeGram b E p.1)) :=
    measurable_fst.prodMk (measurable_snd.prodMk hS)
  exact (continuous_closedSourceAlgebra (J := J) b E).measurable.comp hT

/-- **The phase `T ↦ exp{-i Σ_j σ_j T_jj}` is continuous.** -/
theorem continuous_closedSourcePhase (σ : Fin J → ℤˣ) :
    Continuous (closedSourcePhase σ) := by
  unfold closedSourcePhase
  refine Complex.continuous_exp.comp (continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul ?_)).neg
  exact (continuous_apply j).comp (continuous_apply j)

/-- **The phase is Borel.** -/
theorem measurable_closedSourcePhase (σ : Fin J → ℤˣ) :
    Measurable (closedSourcePhase σ) :=
  (continuous_closedSourcePhase σ).measurable

/-- **The integrand `(K, C) ↦ exp{-i Σ σ_j 𝒯_jj}` of `ClosedSourceMomentValue` is Borel.** -/
theorem measurable_closedSourcePhase_closedSourceMatrix (b E : ℝ) (σ : Fin J → ℤˣ) :
    Measurable (fun p : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ =>
      closedSourcePhase σ (closedSourceMatrix b E p.1 p.2)) :=
  (measurable_closedSourcePhase σ).comp (measurable_closedSourceMatrix b E)

/-- A realization of `𝖢_J(0)` is a Borel random matrix. -/
theorem measurable_matrix_of_isCanonicalCauchyAtZero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))} {C : Ω → Matrix (Fin J) (Fin J) ℂ}
    (hC : IsCanonicalCauchyAtZero J P Ξ C) : Measurable C :=
  Measurable.of_eval fun i => Measurable.of_eval fun j => hC.measurable i j

/-- **The inner `𝖢`-integral `K ↦ ∫ exp{-i Σ σ_j 𝒯(K, C(ω))_jj} dP(ω)` is strongly
measurable in `K`** (so the outer `κ`-integral of `ClosedSourceMomentValue` is not junk). -/
theorem stronglyMeasurable_closedSourceInner (b E : ℝ) (σ : Fin J → ℤˣ) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))} {C : Ω → Matrix (Fin J) (Fin J) ℂ}
    (hC : IsCanonicalCauchyAtZero J P Ξ C) :
    StronglyMeasurable (fun K : Matrix (Fin J) (Fin J) ℂ =>
      ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C ω)) ∂P) := by
  have hC' : Measurable C := measurable_matrix_of_isCanonicalCauchyAtZero hC
  have hpair : Measurable (fun p : Matrix (Fin J) (Fin J) ℂ × Ω => (p.1, C p.2)) :=
    measurable_fst.prodMk (hC'.comp measurable_snd)
  have h : Measurable (fun p : Matrix (Fin J) (Fin J) ℂ × Ω =>
      closedSourcePhase σ (closedSourceMatrix b E p.1 (C p.2))) := by
    exact Measurable.comp (f := fun p : Matrix (Fin J) (Fin J) ℂ × Ω => (p.1, C p.2))
      (measurable_closedSourcePhase_closedSourceMatrix (J := J) b E σ) hpair
  have hs : StronglyMeasurable (fun p : Matrix (Fin J) (Fin J) ℂ × Ω =>
      closedSourcePhase σ (closedSourceMatrix b E p.1 (C p.2))) := h.stronglyMeasurable
  exact StronglyMeasurable.integral_prod_right' (ν := P)
    (f := fun p : Matrix (Fin J) (Fin J) ℂ × Ω =>
      closedSourcePhase σ (closedSourceMatrix b E p.1 (C p.2))) hs

/-- **The sampled-time integrand `t ↦ ∫ Φ(grouped(y 0)) dν_M(t)` of `sampledProbeValue` is a.e.
strongly measurable for the birth law**, for every family `ν` with `IsSampledSourceFamily`. It is
the a.e. limit (admissible `t`) of the finite-width integrands at path length `⌊W τ⌋₊` (by
`IsComplexSourceLimit`), which are measurable in `t`. -/
theorem aestronglyMeasurable_sampledLimitInner_of_family {b E τ : ℝ} {Q : Fin J → C(Torus, ℝ)}
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν) (M : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    AEStronglyMeasurable (BlockBand.Critical.GlobalSource.sampledLimitInner τ Q M (ν M) Φ)
      (sampledBirthLaw τ Q M) := by
  set gK : C(SourceData (J * M), Matrix (Fin J) (Fin J) ℂ) :=
    ⟨fun y => groupedSourceMatrix τ Q M (y 0),
      (BlockBand.Critical.GlobalSource.continuous_groupedSourceMatrix τ Q M).comp
        (continuous_apply 0)⟩
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun (W : ℕ) =>
      BlockBand.Critical.GlobalSource.sampledInner b E τ Q M W (⌊(W : ℝ) * τ⌋₊ + 3) Φ)
    (fun W => (BlockBand.Critical.GlobalSource.stronglyMeasurable_sampledInner b E τ Q M _ _
      Φ).aestronglyMeasurable) ?_
  filter_upwards [BlockBand.Critical.GlobalSource.ae_isAdmissibleBirthTimes τ Q M] with t ht
  have h := (hν M t ht).2 (Φ.compContinuous gK)
  refine h.congr fun W => ?_
  unfold BlockBand.Critical.GlobalSource.sampledInner
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [gK, BlockBand.Critical.GlobalSource.complexSourceData_zero,
    BlockBand.Critical.GlobalSource.probePathLength]

/-- **The sum over real zeros.** For `τ > 0`, `ρ(E) > 0` and a law `μ` carried by the good
entire functions (`F(0) ≠ 0`, real-rooted axis, simple real zeros; the support of every critical
entire limit, `JointRecovery.limit_ae_goodEntire`), the integrand
`F ↦ exp(-Σ_{real zeros x} f(rootDerivativePoint E τ F x))` of `extractorLaplace` is a.e.
strongly measurable (it agrees on `goodEntire` with the Borel `extractionTest`). -/
theorem aestronglyMeasurable_extractionValue {m : ℕ} {E τ : ℝ} (hτ : 0 < τ)
    (hρ : 0 < Parameters.semicircleDensity E)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    {μ : Measure (EntireFunction (m + 1))}
    (hμ : ∀ᵐ F ∂μ, F ∈ BlockBand.Critical.JointRecovery.goodEntire m) :
    AEStronglyMeasurable (BlockBand.Critical.JointRecovery.extractionValue E τ f) μ := by
  have hm := (BlockBand.Critical.JointRecovery.measurable_extractionTest hρ f).comp
    (measurable_const.prodMk measurable_id : Measurable fun F : EntireFunction (m + 1) => (τ, F))
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hμ] with F hF
  exact BlockBand.Critical.JointRecovery.extractionTest_of_mem (p := (τ, F)) ⟨hτ, hF⟩

/-- **`D_W` is Borel** (`JointRecovery.measurable_finiteEntireDeterminant`), so
`finiteEntireLaw` is the push-forward of the physical law. -/
theorem finiteEntireLaw_toMeasure {p : Parameters} (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    (Q : Fin m → C(Torus, ℝ)) :
    (finiteEntireLaw R E Q : Measure (EntireFunction m)) =
      (R.model.law : Measure p.SiteMatrix).map (finiteEntireDeterminant p E Q) := by
  unfold finiteEntireLaw
  exact ProbabilityMeasure.toMeasure_map _

end BlockBand.Critical.EntireLaw
