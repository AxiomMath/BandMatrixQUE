module

public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain

/-!
# Optional stopping for complex martingale modifications

* `martingale_map_clm`: a continuous `ℝ`-linear image of a martingale is a martingale.
* `exists_martingale_stopped_C`: the complex form of
  `Semimartingale.exists_martingale_stoppedProcess` (real and imaginary parts separately):
  if `X` has a.s. continuous paths and a `𝓖`-martingale modification, then for every
  `𝓖`-stopping time `ρ`, `X^ρ` has a `𝓖`-martingale modification.
* `stoppedProcess_ae_eq`: a.e. equal stopping times give a.e. equal stopped values.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m₀}

/-- A continuous `ℝ`-linear image of a martingale is a martingale. -/
theorem martingale_map_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {M : ℝ≥0 → Ω → E}
    (hM : Martingale M 𝓖 Q) (L : E →L[ℝ] F) : Martingale (fun t ω => L (M t ω)) 𝓖 Q := by
  refine ⟨fun t => L.continuous.comp_stronglyMeasurable (hM.1 t), fun s t hst => ?_⟩
  have h := L.comp_condExp_comm (m := 𝓖 s) (μ := Q) (hM.integrable t)
  refine h.symm.trans ?_
  filter_upwards [hM.2 s t hst] with ω hω
  simp only [Function.comp_apply, hω]

theorem stoppedProcess_ae_eq {β : Type*} (X : ℝ≥0 → Ω → β) {ρ σ : Ω → WithTop ℝ≥0}
    (h : ∀ᵐ ω ∂Q, ρ ω = σ ω) (t : ℝ≥0) :
    stoppedProcess X ρ t =ᵐ[Q] stoppedProcess X σ t := by
  filter_upwards [h] with ω hω
  simp only [stoppedProcess, hω]

variable [IsProbabilityMeasure Q] {ρ : Ω → WithTop ℝ≥0}

/-- **Complex optional stopping for modifications.** -/
theorem exists_martingale_stopped_C {X M : ℝ≥0 → Ω → ℂ} (hM : Martingale M 𝓖 Q)
    (hMX : ∀ t, M t =ᵐ[Q] X t) (hc : ∀ᵐ ω ∂Q, Continuous fun t => X t ω)
    (hρ : IsStoppingTime 𝓖 ρ) :
    ∃ M' : ℝ≥0 → Ω → ℂ, Martingale M' 𝓖 Q ∧ ∀ t, M' t =ᵐ[Q] stoppedProcess X ρ t := by
  obtain ⟨A, hA, hAe⟩ := Semimartingale.exists_martingale_stoppedProcess
    (X := fun t ω => (X t ω).re) (martingale_map_clm hM Complex.reCLM)
    (fun t => (hMX t).mono fun ω hω => by simp [hω])
    (hc.mono fun ω h => Complex.continuous_re.comp h) hρ
  obtain ⟨B, hB, hBe⟩ := Semimartingale.exists_martingale_stoppedProcess
    (X := fun t ω => (X t ω).im) (martingale_map_clm hM Complex.imCLM)
    (fun t => (hMX t).mono fun ω hω => by simp [hω])
    (hc.mono fun ω h => Complex.continuous_im.comp h) hρ
  refine ⟨fun t ω => Complex.ofRealCLM (A t ω) + (Complex.I • Complex.ofRealCLM) (B t ω),
    (martingale_map_clm hA Complex.ofRealCLM).add
      (martingale_map_clm hB (Complex.I • Complex.ofRealCLM)), fun t => ?_⟩
  filter_upwards [hAe t, hBe t] with ω h1 h2
  simp only [Complex.ofRealCLM_apply, smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [stoppedProcess]
  rw [mul_comm]; exact Complex.re_add_im _

end BlockBand.SourceProcess.ClosedLimit
