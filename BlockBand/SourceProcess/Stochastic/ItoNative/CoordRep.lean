module
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto
public import BlockBand.SourceProcess.Stochastic.ItoNative.Calculus
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Coordinate representations

Sample space `Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration
`G = driverAugmented μ = F_t ∨ N`.

`CoordRep μ Z β h` says that the `ℝ^d`-valued process `Z` is `dZ = β dt + ∑_a h_a dW^a` in the
following *local* sense: the measurability fields of `IsNativeItoProcess` hold, and there is a
localizing sequence `ρ_n → ⊤` of augmented stopping times such that for every `n`, every
augmented stopping time `τ` and every coordinate `i`, on all large horizons `T` the stopped
coordinate integrand `h^i 1{s ≤ ρ_n ∧ τ}` is an integrand and the stopped compensated
coordinate `(Z^i − Z^i_0 − ∫ β^i)_{u ∧ ρ_n ∧ τ}` is a.s. the continuous integral
`nativeAdaptedLimit` of that integrand at every `u ≤ T`.

Unlike `IsNativeItoProcess`, this class is closed under concatenation without any `L²`
splitting problem, and it is what the bridge to the semimartingale contract
`IsContinuousSemimartingale` needs:

* `CoordRep.isContinuousSemimartingale`: a `CoordRep` is a continuous semimartingale for
  `(P, G)` with drift `β` and covariance `covOf h = ∑_a h_a h_aᵀ` (generalizing
  `IsNativeItoProcess.isContinuousSemimartingale`, same proof).
-/

namespace BlockBand.SourceProcess.Stochastic.ItoNative
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {d : ℕ}

/-- **Coordinate representation** of `dZ = β dt + ∑_a h_a dW^a` in `ℝ^d`. -/
structure CoordRep (μ : Measure S) [IsProbabilityMeasure μ]
    (Z β : ℝ≥0 → DriverSample S κ → Fin d → ℝ)
    (h : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ) : Prop where
  adapted : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Z t)
  progressive : IsStronglyProgressive (driverAugmented (κ := κ) μ) Z
  continuous : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Z t x
  drift_progressive : IsStronglyProgressive (driverAugmented (κ := κ) μ) β
  diffusion_progressive : ∀ a, IsStronglyProgressive (driverAugmented (κ := κ) μ) (h a)
  drift_integrable : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, ∀ i,
    IntegrableOn (fun s : ℝ => β s.toNNReal x i) (Set.Ioc 0 t)
  localizing : ∃ ρ : ℕ → DriverSample S κ → WithTop ℝ≥0,
    (∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (ρ n)) ∧
    (∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => ρ n x) atTop (𝓝 ⊤)) ∧
    ∀ n (τ : DriverSample S κ → WithTop ℝ≥0), IsStoppingTime (driverAugmented (κ := κ) μ) τ →
      ∀ i, ∀ᶠ T in atTop, ∃ hG : NativeIntegrand μ T
          (stopIntegrand (fun x => min (ρ n x) (τ x)) (functionalIntegrand (coordFun i) h)),
        ∀ u ≤ T, stoppedProcess (smCompensated Z β i) (fun x => min (ρ n x) (τ x)) u
          =ᵐ[driverLaw (κ := κ) μ] nativeAdaptedLimit μ T hG.family u

variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {Z β : ℝ≥0 → DriverSample S κ → Fin d → ℝ} {h : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ}

/-- The localizing clause with `τ = ⊤`. -/
theorem CoordRep.loc_top (H : CoordRep μ Z β h) :
    ∃ ρ : ℕ → DriverSample S κ → WithTop ℝ≥0,
      (∀ n, IsStoppingTime (driverAugmented (κ := κ) μ) (ρ n)) ∧
      (∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => ρ n x) atTop (𝓝 ⊤)) ∧
      ∀ n i, ∀ᶠ T in atTop, ∃ hG : NativeIntegrand μ T
          (stopIntegrand (ρ n) (functionalIntegrand (coordFun i) h)),
        ∀ u ≤ T, stoppedProcess (smCompensated Z β i) (ρ n) u
          =ᵐ[driverLaw (κ := κ) μ] nativeAdaptedLimit μ T hG.family u := by
  obtain ⟨ρ, hρs, hρlim, hloc⟩ := H.localizing
  refine ⟨ρ, hρs, hρlim, fun n i => ?_⟩
  have := hloc n _ (isStoppingTime_top_aug (μ := μ)) i
  have e : (fun x => min (ρ n x) (⊤ : WithTop ℝ≥0)) = ρ n := funext fun x => min_top_right _
  rw [e] at this
  exact this

/-- Pathwise local integrability of the covariance density `∑_a h_a^i h_a^j`. -/
theorem CoordRep.ae_integrableOn_cov (H : CoordRep μ Z β h) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t : ℝ≥0, ∀ i j : Fin d,
      IntegrableOn (fun s : ℝ => covOf (fun a => h a s.toNNReal x) i j) (Ioc 0 t) := by
  obtain ⟨ρ, -, hρlim, hloc⟩ := H.loc_top
  have hT : ∀ (n m : ℕ) (i j : Fin d), ∃ T : ℝ≥0, ((m : ℝ≥0) ≤ T ∧
      (∃ _ : NativeIntegrand μ T (stopIntegrand (ρ n) (functionalIntegrand (coordFun i) h)),
        True) ∧
      ∃ _ : NativeIntegrand μ T (stopIntegrand (ρ n) (functionalIntegrand (coordFun j) h)),
        True) := by
    intro n m i j
    obtain ⟨T, hm, ⟨hGi, -⟩, ⟨hGj, -⟩⟩ :=
      ((eventually_ge_atTop (m : ℝ≥0)).and ((hloc n i).and (hloc n j))).exists
    exact ⟨T, hm, ⟨hGi, trivial⟩, ⟨hGj, trivial⟩⟩
  choose T hTm hGi hGj using hT
  have hall : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ (n m : ℕ) (i j : Fin d),
      IntegrableOn (fun s => bracketDensity (stopIntegrand (ρ n) (functionalIntegrand
        (coordFun i) h)) (stopIntegrand (ρ n) (functionalIntegrand (coordFun j) h)) (s, x))
        (Ioc 0 ((T n m i j : ℝ≥0) : ℝ)) := by
    simp only [ae_all_iff]
    intro n m i j
    exact ae_integrableOn_bracketDensity (hGi n m i j).1 (hGj n m i j).1
  filter_upwards [hall, hρlim] with x hx hlim t i j
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  obtain ⟨m, hm⟩ := exists_nat_ge (t : ℝ)
  have htT : (t : ℝ) ≤ (T n m i j : ℝ) :=
    hm.trans (by exact_mod_cast hTm n m i j)
  have h1 := (hx n m i j).mono_set (Ioc_subset_Ioc_right htT)
  refine h1.congr_fun (fun s hs => ?_) measurableSet_Ioc
  have hle : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ n x :=
    (WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hn.le
  change bracketDensity _ _ (s, x) = _
  rw [bracketDensity_stopIntegrand]
  simp only [hle, ↓reduceIte]
  rfl

/-- **Bridge.** A coordinate representation is a continuous semimartingale
(`IsContinuousSemimartingale`) under `driverLaw μ` for `driverAugmented μ`, with drift `β` and
covariance `∑_a h_a h_aᵀ`. -/
theorem CoordRep.isContinuousSemimartingale (H : CoordRep μ Z β h) :
    IsContinuousSemimartingale (driverLaw (κ := κ) μ) (driverAugmented (κ := κ) μ) Z β
      (fun t x => covOf (fun a => h a t x)) := by
  obtain ⟨ρ, hρs, hρlim, hloc⟩ := H.loc_top
  refine ⟨H.adapted, H.progressive, H.continuous, H.drift_progressive,
    isStronglyProgressive_covOf H.diffusion_progressive, ?_,
    ⟨ρ, hρs, hρlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [H.drift_integrable, H.ae_integrableOn_cov] with x hb hα t
    exact ⟨fun i => hb t i, fun i j => hα t i j⟩
  · refine hasMartingaleModification_of_raw fun T => ?_
    obtain ⟨T', hT', hG, hid⟩ := ((eventually_ge_atTop T).and (hloc n i)).exists
    exact ⟨nativeAdaptedLimit μ T' hG.family, nativeAdaptedLimit_martingale μ T' _,
      fun u hu => hid u (hu.trans hT')⟩
  · refine hasMartingaleModification_of_raw fun T => ?_
    obtain ⟨T', hT', ⟨hGi, hidi⟩, ⟨hGj, hidj⟩⟩ :=
      ((eventually_ge_atTop T).and ((hloc n i).and (hloc n j))).exists
    obtain ⟨N, hN, hNe⟩ := bracket_martingale hGi hGj
    refine ⟨N, hN, fun u hu => ?_⟩
    have hu' := hu.trans hT'
    filter_upwards [hNe u, hidi u hu', hidj u hu'] with x h1 h2 h3
    rw [h1, ← h2, ← h3, bracketDrift_stopIntegrand, min_eq_left hu',
      setIntegral_switch (fun s => ∑ c, functionalIntegrand (coordFun i) h c (s, x) *
        functionalIntegrand (coordFun j) h c (s, x)) (ρ n x) u]
    rfl

end BlockBand.SourceProcess.Stochastic.ItoNative
