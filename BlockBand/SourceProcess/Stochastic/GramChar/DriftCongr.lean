module
public import BlockBand.SourceProcess.Stochastic.Ito
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Changing the drift of an Itô process on a null set

`IsNativeItoProcess.congr_drift`: if `X` is an Itô process with drift `b` and diffusion
`σ` on `driverLaw μ`, and `b'` is an augmented-progressive process with `b t x = b' t x` for all
`t`, for almost every `x`, then `X` is an Itô process with drift `b'` and the same
diffusion. Only the drift-integrability and identity clauses change, and both are pathwise
statements about `s ↦ b s x`, which is unchanged for a.e. `x`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramChar
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure S} [IsProbabilityMeasure μ]

omit [MeasurableSpace S] [Fintype κ] in
/-- Stopped drift integrals agree for drifts with the same path. -/
theorem stoppedDrift_congr {b b' : ℝ≥0 → DriverSample S κ → E} {x : DriverSample S κ}
    (h : ∀ t, b t x = b' t x) (τ : DriverSample S κ → WithTop ℝ≥0) (t : ℝ≥0) :
    stoppedDrift τ b t x = stoppedDrift τ b' t x := by
  simp only [stoppedDrift, h]

/-- **Drift congruence.** An Itô process keeps its diffusion when its drift is replaced
by a progressive drift with the same paths almost surely. -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.congr_drift
    {X b b' : ℝ≥0 → DriverSample S κ → E} {σ : κ → ℝ≥0 → DriverSample S κ → E}
    (h : IsNativeItoProcess μ X b σ)
    (hb' : IsStronglyProgressive (driverAugmented (κ := κ) μ) b')
    (hbb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, b t x = b' t x) :
    IsNativeItoProcess μ X b' σ := by
  refine ⟨h.adapted, h.progressive, h.continuous, hb', h.diffusion_progressive, ?_,
    h.localizing, ?_⟩
  · filter_upwards [h.drift_integrable, hbb] with x hx hxb t
    have he : (fun s : ℝ => b' s.toNNReal x) = fun s => b s.toNNReal x :=
      funext fun s => (hxb _).symm
    rw [he]
    exact hx t
  · intro ℓ τ hτ T hint t ht
    obtain ⟨hs, hid⟩ := h.identity ℓ τ hτ T hint t ht
    refine ⟨hs, ?_⟩
    filter_upwards [hid, hbb] with x hx hxb
    rw [← hx, stoppedDrift_congr hxb τ t]

end BlockBand.SourceProcess.Stochastic.GramChar
