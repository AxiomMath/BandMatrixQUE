module

public import BlockBand.SourceProcess.BornRestart.Shift
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.MartingaleTools

/-!
# Martingale tools: dominated limits, bounded `𝓗₀` factors, complex optional stopping

* `exists_martingale_of_tendsto`: if `Y k u → V u` a.s., uniformly bounded in `k`, the limits are
  `𝓗_u`-measurable and `∫_B Y k t = ∫_B Y k s` for `B ∈ 𝓗_s`, then `V` has an `𝓗`-martingale
  modification (dominated convergence; no path regularity).
* `martingale_const_mul`: a bounded `𝓗₀`-measurable factor times a martingale is a martingale.
* `exists_martingale_restrict_complex`: `exists_martingale_restrict` for
  complex processes (real and imaginary parts).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open scoped NNReal ENNReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- **Dominated limits of martingale-like sequences have martingale modifications.** -/
theorem exists_martingale_of_tendsto {𝓗 : Filtration ℝ≥0 m} {Y : ℕ → ℝ≥0 → Ω → ℂ}
    {V : ℝ≥0 → Ω → ℂ}
    (hmeas : ∀ u, StronglyMeasurable[𝓗 u] fun ω => limUnder atTop fun k => Y k u ω)
    (hY : ∀ k u, AEStronglyMeasurable (Y k u) Q)
    (hconv : ∀ u, ∀ᵐ ω ∂Q, Tendsto (fun k => Y k u ω) atTop (𝓝 (V u ω)))
    (hbd : ∀ u, ∃ C, ∀ k, ∀ᵐ ω ∂Q, ‖Y k u ω‖ ≤ C)
    (hint : ∀ k s t, s ≤ t → ∀ B, MeasurableSet[𝓗 s] B →
      ∫ ω in B, Y k t ω ∂Q = ∫ ω in B, Y k s ω ∂Q) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓗 Q ∧ ∀ u, N u =ᵐ[Q] V u := by
  set N : ℝ≥0 → Ω → ℂ := fun u ω => limUnder atTop fun k => Y k u ω
  have hlim : ∀ u, ∀ᵐ ω ∂Q, Tendsto (fun k => Y k u ω) atTop (𝓝 (N u ω)) := fun u => by
    filter_upwards [hconv u] with ω h
    rw [show N u ω = V u ω from h.limUnder_eq]
    exact h
  have hNbd : ∀ u, ∃ C, ∀ᵐ ω ∂Q, ‖N u ω‖ ≤ C := fun u => by
    obtain ⟨C, hC⟩ := hbd u
    refine ⟨C, ?_⟩
    filter_upwards [hlim u, ae_all_iff.2 hC] with ω h1 h2
    exact le_of_tendsto' h1.norm h2
  have hNint : ∀ u, Integrable (N u) Q := fun u => by
    obtain ⟨C, hC⟩ := hNbd u
    exact Integrable.of_bound ((hmeas u).mono (𝓗.le u)).aestronglyMeasurable C hC
  have hsetlim : ∀ u B, Tendsto (fun k => ∫ ω in B, Y k u ω ∂Q) atTop
      (𝓝 (∫ ω in B, N u ω ∂Q)) := fun u B => by
    obtain ⟨C, hC⟩ := hbd u
    exact tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => (hY k u).restrict)
      (integrable_const C) (fun k => ae_restrict_of_ae (hC k)) (ae_restrict_of_ae (hlim u))
  refine ⟨N, ⟨fun u => hmeas u, fun s t hst => ?_⟩, fun u => ?_⟩
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hNint t)
      (fun B _ _ => (hNint s).integrableOn) (fun B hB _ => ?_)
      (hmeas s).aestronglyMeasurable).symm
    refine tendsto_nhds_unique (hsetlim s B) ?_
    simp_rw [← hint _ s t hst B hB]
    exact hsetlim t B
  · filter_upwards [hconv u] with ω h
    exact h.limUnder_eq

omit [IsProbabilityMeasure Q] in
/-- **A bounded `𝓗₀`-measurable factor times a martingale is a martingale.** -/
theorem martingale_const_mul {𝓗 : Filtration ℝ≥0 m} {N : ℝ≥0 → Ω → ℂ} (hN : Martingale N 𝓗 Q)
    {ζ : Ω → ℂ} (hζ : StronglyMeasurable[𝓗 0] ζ) {C : ℝ} (hC : ∀ᵐ ω ∂Q, ‖ζ ω‖ ≤ C) :
    Martingale (fun t ω => ζ ω * N t ω) 𝓗 Q := by
  refine ⟨fun t => (hζ.mono (𝓗.mono zero_le)).mul (hN.1 t), fun s t hst => ?_⟩
  have hint : Integrable (fun ω => ζ ω * N t ω) Q :=
    (hN.integrable t).bdd_mul ((hζ.mono (𝓗.le 0)).aestronglyMeasurable) hC
  have h1 := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    (hζ.mono (𝓗.mono zero_le)) (m := 𝓗 s) hint (hN.integrable t)
  filter_upwards [h1, hN.condExp_ae_eq hst] with ω h2 h3
  simp only [ContinuousLinearMap.mul_apply'] at h2
  rw [h2, h3]

/-- **Optional stopping at `ρ ≤ σ` for complex processes.** -/
theorem exists_martingale_restrict_complex {𝓖 : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℂ}
    {σ ρ ρ' : Ω → WithTop ℝ≥0} {N : ℝ≥0 → Ω → ℂ} (hN : Martingale N 𝓖 Q)
    (hNX : ∀ t, N t =ᵐ[Q] stoppedProcess X σ t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hρ : IsStoppingTime 𝓖 ρ) (hle : ∀ᵐ ω ∂Q, ρ ω ≤ σ ω) (heq : ∀ᵐ ω ∂Q, ρ' ω = ρ ω) :
    ∃ N' : ℝ≥0 → Ω → ℂ, Martingale N' 𝓖 Q ∧ ∀ t, N' t =ᵐ[Q] stoppedProcess X ρ' t := by
  have hre : HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω => (X t ω).re) σ) :=
    ⟨_, martingale_clm hN Complex.reCLM, fun t => by
      filter_upwards [hNX t] with ω h
      simp [h, stoppedProcess]⟩
  have him : HasMartingaleModification Q 𝓖 (stoppedProcess (fun t ω => (X t ω).im) σ) :=
    ⟨_, martingale_clm hN Complex.imCLM, fun t => by
      filter_upwards [hNX t] with ω h
      simp [h, stoppedProcess]⟩
  obtain ⟨Mr, hMr, hMrX⟩ := exists_martingale_restrict hre
    (hc.mono fun ω h => Complex.continuous_re.comp h) hρ hle heq
  obtain ⟨Mi, hMi, hMiX⟩ := exists_martingale_restrict him
    (hc.mono fun ω h => Complex.continuous_im.comp h) hρ hle heq
  refine ⟨fun t ω => Complex.ofRealCLM (Mr t ω) +
      (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I (Mi t ω),
    (martingale_clm hMr _).add (martingale_clm hMi _), fun t => ?_⟩
  filter_upwards [hMrX t, hMiX t] with ω h1 h2
  simp only [Complex.ofRealCLM_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, Complex.real_smul]
  rw [h1, h2]
  simp only [stoppedProcess]
  exact Complex.re_add_im _

end BlockBand.SourceProcess.BornRestart
