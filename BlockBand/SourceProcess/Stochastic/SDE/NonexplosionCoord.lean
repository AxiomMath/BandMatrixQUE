module
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionLocalize
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Itô processes under continuous linear equivalences

`IsNativeItoProcess.map_equiv`: if `X` is an Itô process in `E` with drift `β` and
diffusion `γ` and `L : E ≃L[ℝ] F` (finite-dimensional `F`), then `L ∘ X` is an Itô
process in `F` with drift `L ∘ β` and diffusion `L ∘ γ`. Functionals `ℓ` of `F` pull back to
`ℓ ∘ L`; the drift integral commutes with `L` without any integrability
(`ContinuousLinearEquiv.integral_comp_comm`).

`coordEquiv E : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ)` is the coordinate equivalence of a basis; it
transports exit-time solutions to the space `Fin d → ℝ` of the semimartingale bridge.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

variable (E) in
/-- The coordinate equivalence `E ≃L[ℝ] ℝ^d` of the standard basis, `d = finrank ℝ E`. -/
def coordEquiv : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
  (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv

omit [MeasurableSpace S] [Fintype κ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem stoppedDrift_map_equiv (L : E ≃L[ℝ] F) (τ : DriverSample S κ → WithTop ℝ≥0)
    (β : ℝ≥0 → DriverSample S κ → E) (t : ℝ≥0) (x : DriverSample S κ) :
    stoppedDrift τ (fun t x => L (β t x)) t x = L (stoppedDrift τ β t x) := by
  unfold stoppedDrift
  rw [← L.integral_comp_comm]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  simp only
  split_ifs
  · rfl
  · exact L.map_zero.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] in
/-- **Transport of Itô processes** by a continuous linear equivalence. -/
theorem IsNativeItoProcess.map_equiv {X β : ℝ≥0 → DriverSample S κ → E}
    {γ : κ → ℝ≥0 → DriverSample S κ → E} (h : IsNativeItoProcess μ X β γ) (L : E ≃L[ℝ] F) :
    IsNativeItoProcess μ (fun t x => L (X t x)) (fun t x => L (β t x))
      (fun a t x => L (γ a t x)) := by
  obtain ⟨τ, hτs, hτlim, hloc⟩ := h.localizing
  refine ⟨fun t => L.continuous.comp_stronglyMeasurable (h.adapted t),
    fun i => L.continuous.comp_stronglyMeasurable (h.progressive i),
    h.continuous.mono fun x hx => L.continuous.comp hx,
    fun i => L.continuous.comp_stronglyMeasurable (h.drift_progressive i),
    fun a i => L.continuous.comp_stronglyMeasurable (h.diffusion_progressive a i),
    h.drift_integrable.mono fun x hx t => (L : E →L[ℝ] F).integrable_comp (hx t),
    ⟨τ, hτs, hτlim, fun n ℓ T => hloc n (ℓ.comp (L : E →L[ℝ] F)) T⟩, ?_⟩
  intro ℓ ρ hρ T hint t ht
  obtain ⟨hs, hid⟩ := h.identity (ℓ.comp (L : E →L[ℝ] F)) ρ hρ T hint t ht
  refine ⟨hs, ?_⟩
  filter_upwards [hid] with x hx
  rw [stoppedDrift_map_equiv]
  exact hx

end BlockBand.SourceProcess.Stochastic.NativeSDE
