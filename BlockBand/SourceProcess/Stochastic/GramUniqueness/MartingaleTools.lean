module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Instance
public import BlockBand.Internal.Contracts.Transmission
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Martingale tools for the Gram bridge

On a probability space with a raw filtration:
* `martingale_clm`: a continuous linear image of a martingale is a martingale;
* `hasMartingaleModification_stopped_of_clm`: if `X = T₁ Z₁ + T₂ Z₂` pathwise a.s. and `Z₁^σ`,
  `Z₂^σ` have martingale modifications, so does `X^σ`;
* `exists_martingale_restrict`: if `X^σ` has a martingale modification, `X` has a.s. continuous
  paths, `ρ ≤ σ` a.s. for a stopping time `ρ`, and `ρ' = ρ` a.s., then `X^{ρ'}` has a martingale
  modification (optional stopping for modifications, `exists_martingale_stoppedProcess`);
* `integrableOn_Ioc_of_continuous`: a continuous path is integrable on `(0, t]`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

theorem martingale_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {N : ℝ≥0 → Ω → E}
    (hN : Martingale N 𝓖 Q) (T : E →L[ℝ] F) : Martingale (fun t ω => T (N t ω)) 𝓖 Q := by
  refine ⟨fun t => T.continuous.comp_stronglyMeasurable (hN.1 t), fun s t hst => ?_⟩
  have h1 := T.comp_condExp_comm (m := 𝓖 s) (hN.integrable t)
  filter_upwards [h1.symm, hN.condExp_ae_eq hst] with ω h2 h3
  simp only [Function.comp_apply] at h2 h3 ⊢
  rw [← h3]
  exact h2

theorem hasMartingaleModification_stopped_of_clm {E₁ E₂ : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [CompleteSpace E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [CompleteSpace E₂] {Z₁ : ℝ≥0 → Ω → E₁} {Z₂ : ℝ≥0 → Ω → E₂} {σ : Ω → WithTop ℝ≥0}
    {N₁ : ℝ≥0 → Ω → E₁} {N₂ : ℝ≥0 → Ω → E₂} (hN₁ : Martingale N₁ 𝓖 Q) (hN₂ : Martingale N₂ 𝓖 Q)
    (h₁ : ∀ t, N₁ t =ᵐ[Q] stoppedProcess Z₁ σ t) (h₂ : ∀ t, N₂ t =ᵐ[Q] stoppedProcess Z₂ σ t)
    (T₁ : E₁ →L[ℝ] ℝ) (T₂ : E₂ →L[ℝ] ℝ) {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂Q, ∀ t, X t ω = T₁ (Z₁ t ω) + T₂ (Z₂ t ω)) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X σ) := by
  refine ⟨fun t ω => T₁ (N₁ t ω) + T₂ (N₂ t ω),
    (martingale_clm hN₁ T₁).add (martingale_clm hN₂ T₂), fun t => ?_⟩
  filter_upwards [h₁ t, h₂ t, hX] with ω e₁ e₂ eX
  simp only [e₁, e₂, stoppedProcess, eX]

theorem exists_martingale_restrict [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    {σ ρ ρ' : Ω → WithTop ℝ≥0} (hX : HasMartingaleModification Q 𝓖 (stoppedProcess X σ))
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) (hρ : IsStoppingTime 𝓖 ρ)
    (hle : ∀ᵐ ω ∂Q, ρ ω ≤ σ ω) (heq : ∀ᵐ ω ∂Q, ρ' ω = ρ ω) :
    ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess X ρ' t := by
  obtain ⟨M, hM, hMX⟩ := hX
  have hcσ : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X σ t ω := by
    filter_upwards [hc] with ω h
    exact h.comp (continuous_stopTime (σ ω))
  obtain ⟨M', hM', hM'X⟩ := exists_martingale_stoppedProcess hM hMX hcσ hρ
  refine ⟨M', hM', fun t => ?_⟩
  filter_upwards [hM'X t, hle, heq] with ω h1 h2 h3
  rw [h1, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime,
    SemimartingaleIto.stopTime_eq_of_le ((stopTime_le_self _ t).trans h2), h3]

theorem integrableOn_Ioc_of_continuous {F : Type*} [NormedAddCommGroup F] {g : ℝ≥0 → F}
    (hg : Continuous g) (t : ℝ≥0) : IntegrableOn (fun s : ℝ => g s.toNNReal) (Ioc 0 t) :=
  ((hg.comp continuous_real_toNNReal).continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

end BlockBand.SourceProcess.Stochastic.GramUniqueness
