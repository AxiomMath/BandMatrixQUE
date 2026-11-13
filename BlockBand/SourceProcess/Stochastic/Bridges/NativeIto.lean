module
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeItoAux
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bridge: an Itô process is a continuous semimartingale

Proof. Adaptedness, progressive measurability, continuity and the drift's progressive
measurability are fields of `IsNativeItoProcess`; `α` is progressive as a finite sum of
continuous images of the progressive `σ_a`. The localizing sequence is the one `τ_n`.
Local integrability of `α` comes from the integrands `σ_a^i 1{s ≤ τ_n}` (`L²(dt ⊗ P)`)
and `τ_n → ⊤` a.s. For the martingale clauses, on each horizon `T` the stopped compensated
coordinate is a.s. the raw continuous martingale `nativeAdaptedLimit` of `σ^i 1{s ≤ τ_n}`
(the identity clause of `ContinuousStoppedIntegral`), and the stopped compensated product is a.s.
the raw bracket martingale of `bracket_martingale`; `hasMartingaleModification_of_raw` turns these
horizon-wise raw martingales into one augmented martingale modification.
-/

namespace BlockBand.SourceProcess.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.Internal.Contracts.Transmission

variable {d : ℕ}

/-- The covariance density `∑_a σ_a^i σ_a^j` of progressively measurable `σ_a` is
progressively measurable (any filtration). -/
theorem isStronglyProgressive_covOf {Ω ι : Type*} {m : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m}
    [Fintype ι] {σ : ι → ℝ≥0 → Ω → Fin d → ℝ} (hσ : ∀ a, IsStronglyProgressive 𝓖 (σ a)) :
    IsStronglyProgressive 𝓖 (fun t x => Matrix.of fun i j => ∑ a, σ a t x i * σ a t x j) := by
  intro t
  have hc : Continuous fun v : Fin d → ℝ =>
      (Matrix.of fun i j => v i * v j : Matrix (Fin d) (Fin d) ℝ) :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply i).mul (continuous_apply j)
  have he : (fun p : Set.Iic t × Ω => Matrix.of fun i j => ∑ a, σ a p.1 p.2 i * σ a p.1 p.2 j) =
      fun p => ∑ a, Matrix.of fun i j => σ a p.1 p.2 i * σ a p.1 p.2 j := by
    funext p
    ext i j
    simp [Matrix.sum_apply]
  show StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝓖 t)] (fun p : Set.Iic t × Ω =>
    Matrix.of fun i j => ∑ a, σ a p.1 p.2 i * σ a p.1 p.2 j)
  rw [he]
  exact Finset.stronglyMeasurable_fun_sum _ fun a _ => hc.comp_stronglyMeasurable (hσ a t)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- Pathwise local integrability of the covariance density `∑_a σ_a^i σ_a^j`: for a.e. sample,
on every `(0,t]`, from the integrands `σ^i 1{s ≤ τ_n}` and `τ_n → ⊤` a.s. -/
theorem ae_integrableOn_covOf {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {τ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    (hτlim : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => τ n x) atTop (𝓝 ⊤))
    (hloc : ∀ n (ℓ : (Fin d → ℝ) →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand (τ n) (functionalIntegrand ℓ σ))) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, ∀ i j : Fin d,
      IntegrableOn (fun s : ℝ => ∑ a, σ a s.toNNReal x i * σ a s.toNNReal x j) (Ioc 0 t) := by
  have hall : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ (n m : ℕ) (i j : Fin d),
      IntegrableOn (fun s => bracketDensity (stopIntegrand (τ n) (functionalIntegrand
        (coordFun i) σ)) (stopIntegrand (τ n) (functionalIntegrand (coordFun j) σ)) (s, x))
        (Ioc 0 ((m : ℝ≥0) : ℝ)) := by
    simp only [ae_all_iff]
    intro n m i j
    exact ae_integrableOn_bracketDensity (hloc n _ m) (hloc n _ m)
  filter_upwards [hall, hτlim] with x hx hlim t i j
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  obtain ⟨m, hm⟩ := exists_nat_ge (t : ℝ)
  have h1 := (hx n m i j).mono_set (Ioc_subset_Ioc_right (by simpa using hm))
  refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioc
  have hle : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ n x :=
    (WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hn.le
  change bracketDensity _ _ (s, x) = _
  rw [bracketDensity_stopIntegrand]
  simp only [hle, ↓reduceIte]
  rfl

/-- **Itô processes are semimartingales.** An Itô process in `Fin d → ℝ` with drift
`b` and diffusion `σ` is a continuous semimartingale (`IsContinuousSemimartingale`) under
`driverLaw μ` for the
augmented filtration `driverAugmented μ`, with drift `b` and covariance density
`α^{ij} = ∑_a σ_a^i σ_a^j`. The localizing sequence is the one. -/
theorem IsNativeItoProcess.isContinuousSemimartingale
    {X b : ℝ≥0 → DriverSample S κ → Fin d → ℝ} {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    (h : IsNativeItoProcess μ X b σ) :
    IsContinuousSemimartingale (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ) X b
      (fun t x => Matrix.of fun i j => ∑ a, σ a t x i * σ a t x j) := by
  obtain ⟨τ, hτs, hτlim, hloc⟩ := h.localizing
  refine ⟨h.adapted, h.progressive, h.continuous, h.drift_progressive,
    isStronglyProgressive_covOf h.diffusion_progressive, ?_,
    ⟨τ, hτs, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [h.drift_integrable, ae_integrableOn_covOf hτlim hloc] with x hb hα t
    exact ⟨fun i => (coordFun i).integrable_comp (hb t), fun i j => hα t i j⟩
  · exact hasMartingaleModification_of_raw fun T =>
      ⟨nativeAdaptedLimit μ T (hloc n (coordFun i) T).family, nativeAdaptedLimit_martingale μ T _,
        fun u hu => stoppedProcess_smCompensated_ae_eq h (hτs n) i _ hu⟩
  · refine hasMartingaleModification_of_raw fun T => ?_
    obtain ⟨N, hN, hNe⟩ := bracket_martingale (hloc n (coordFun i) T) (hloc n (coordFun j) T)
    exact ⟨N, hN, fun u hu => stoppedProcess_bracket_ae_eq h (hτs n) i j _ _ hNe hu⟩

end BlockBand.SourceProcess.Stochastic
