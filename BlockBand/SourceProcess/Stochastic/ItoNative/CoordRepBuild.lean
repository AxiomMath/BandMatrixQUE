module
public import BlockBand.SourceProcess.Stochastic.ItoNative.CoordRep
public import BlockBand.SourceProcess.Stochastic.Bridges.Concat
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Building coordinate representations

Sample space `DriverSample S κ`, law `driverLaw μ`, augmented filtration `driverAugmented μ`.

* `stopIntegrand_stopIntegrand`: stopping twice is stopping at the minimum.
* `stoppedDrift_clm`: a continuous linear map commutes with the stopped drift integral when the
  drift path is integrable.
* `IsNativeItoProcess.map_clm`: the image of an Itô process under a continuous linear map
  `L : E →L F` is an Itô process with drift `L b` and diffusion `L σ_a`.
* `IsNativeItoProcess.coordRep`: an Itô process in `ℝ^d` is a `CoordRep`.
* `CoordRep.concat`: concatenation (`concatCoord`) of two `CoordRep`s, localized at the minimum
  of the two localizing sequences; no cross condition is needed.
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

omit [MeasurableSpace S] [Fintype κ] in
/-- Stopping at `ρ` and then at `τ` is stopping at `ρ ∧ τ`. -/
theorem stopIntegrand_stopIntegrand (ρ τ : DriverSample S κ → WithTop ℝ≥0)
    (g : κ → ℝ × DriverSample S κ → ℝ) :
    stopIntegrand τ (stopIntegrand ρ g) = stopIntegrand (fun x => min (ρ x) (τ x)) g := by
  funext c p
  simp only [stopIntegrand, le_min_iff]
  split_ifs <;> simp_all

/-- Switching a path off after `r` keeps integrability on `(0, t]`. -/
theorem integrableOn_switch {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {t : ℝ≥0}
    (hf : IntegrableOn f (Ioc 0 t)) (r : WithTop ℝ≥0) :
    IntegrableOn (fun s : ℝ => if (s.toNNReal : WithTop ℝ≥0) ≤ r then f s else 0) (Ioc 0 t) := by
  have e : (fun s : ℝ => if (s.toNNReal : WithTop ℝ≥0) ≤ r then f s else 0) =
      {s : ℝ | (s.toNNReal : WithTop ℝ≥0) ≤ r}.indicator f := by
    funext s
    by_cases hs : (s.toNNReal : WithTop ℝ≥0) ≤ r
    · rw [Set.indicator_of_mem (show s ∈ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} from hs),
        ite_eq_left hs]
    · rw [Set.indicator_of_notMem (show s ∉ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} from hs),
        ite_eq_right hs]
  rw [e]
  exact hf.indicator (measurableSet_toNNReal_le r)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace S] [Fintype κ] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F]
  [BorelSpace F] in
/-- A continuous linear map commutes with the stopped drift integral. -/
theorem stoppedDrift_clm (L : E →L[ℝ] F) {τ : DriverSample S κ → WithTop ℝ≥0}
    {b : ℝ≥0 → DriverSample S κ → E} {t : ℝ≥0} {x : DriverSample S κ}
    (hb : IntegrableOn (fun s : ℝ => b s.toNNReal x) (Ioc 0 t)) :
    L (stoppedDrift τ b t x) = stoppedDrift τ (fun s x => L (b s x)) t x := by
  unfold stoppedDrift
  rw [← L.integral_comp_comm (integrableOn_switch hb (τ x))]
  congr 1
  funext s
  split_ifs <;> simp

variable {μ : Measure S} [IsProbabilityMeasure μ]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- **Linear images of Itô processes.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.map_clm {X b : ℝ≥0 → DriverSample S κ → E}
    {σ : κ → ℝ≥0 → DriverSample S κ → E} (h : IsNativeItoProcess μ X b σ) (L : E →L[ℝ] F) :
    IsNativeItoProcess μ (fun t x => L (X t x)) (fun t x => L (b t x))
      (fun a t x => L (σ a t x)) := by
  obtain ⟨τ, hτs, hτlim, hloc⟩ := h.localizing
  refine ⟨fun t => L.continuous.comp_stronglyMeasurable (h.adapted t),
    fun t => L.continuous.comp_stronglyMeasurable (h.progressive t), ?_,
    fun t => L.continuous.comp_stronglyMeasurable (h.drift_progressive t),
    fun a t => L.continuous.comp_stronglyMeasurable (h.diffusion_progressive a t), ?_,
    ⟨τ, hτs, hτlim, fun n ℓ T => hloc n (ℓ.comp L) T⟩, ?_⟩
  · filter_upwards [h.continuous] with x hx
    exact L.continuous.comp hx
  · filter_upwards [h.drift_integrable] with x hx t
    exact L.integrable_comp (hx t)
  · intro ℓ ρ hρ T hG t ht
    obtain ⟨hs, hid⟩ := h.identity (ℓ.comp L) ρ hρ T hG t ht
    refine ⟨hs, ?_⟩
    filter_upwards [hid, h.drift_integrable] with x h1 h2
    rw [← stoppedDrift_clm L (h2 t)]
    exact h1

variable {d d₁ d₂ : ℕ}

/-- **Itô processes in `ℝ^d` are coordinate representations.** -/
theorem _root_.BlockBand.SourceProcess.Stochastic.IsNativeItoProcess.coordRep {X b : ℝ≥0 → DriverSample S κ → Fin d → ℝ}
    {σ : κ → ℝ≥0 → DriverSample S κ → Fin d → ℝ} (h : IsNativeItoProcess μ X b σ) :
    CoordRep μ X b σ := by
  obtain ⟨τ, hτs, hτlim, hloc⟩ := h.localizing
  refine ⟨h.adapted, h.progressive, h.continuous, h.drift_progressive, h.diffusion_progressive,
    ?_, ⟨τ, hτs, hτlim, fun n ρ hρ i => Eventually.of_forall fun T => ?_⟩⟩
  · filter_upwards [h.drift_integrable] with x hb t i
    exact (coordFun i).integrable_comp (hb t)
  · have hG : NativeIntegrand μ T (stopIntegrand (fun x => min (τ n x) (ρ x))
        (functionalIntegrand (coordFun i) σ)) := by
      rw [← stopIntegrand_stopIntegrand]
      exact stopIntegrand_nativeIntegrand (hloc n _ T) hρ
    exact ⟨hG, fun u hu => stoppedProcess_smCompensated_ae_eq h ((hτs n).min hρ) i hG hu⟩

omit [MeasurableSpace S] [Fintype κ] in
theorem functionalIntegrand_concat_inl (h₁ : κ → ℝ≥0 → DriverSample S κ → Fin d₁ → ℝ)
    (h₂ : κ → ℝ≥0 → DriverSample S κ → Fin d₂ → ℝ) (i : Fin d₁) :
    functionalIntegrand (coordFun (finSumFinEquiv (Sum.inl i)))
        (fun a t x => concatCoord (h₁ a t x) (h₂ a t x)) =
      functionalIntegrand (coordFun i) h₁ := by
  funext a p
  simp [functionalIntegrand]

omit [MeasurableSpace S] [Fintype κ] in
theorem functionalIntegrand_concat_inr (h₁ : κ → ℝ≥0 → DriverSample S κ → Fin d₁ → ℝ)
    (h₂ : κ → ℝ≥0 → DriverSample S κ → Fin d₂ → ℝ) (j : Fin d₂) :
    functionalIntegrand (coordFun (finSumFinEquiv (Sum.inr j)))
        (fun a t x => concatCoord (h₁ a t x) (h₂ a t x)) =
      functionalIntegrand (coordFun j) h₂ := by
  funext a p
  simp [functionalIntegrand]

/-- **Concatenation of coordinate representations.** -/
theorem CoordRep.concat {Z₁ β₁ : ℝ≥0 → DriverSample S κ → Fin d₁ → ℝ}
    {h₁ : κ → ℝ≥0 → DriverSample S κ → Fin d₁ → ℝ} {Z₂ β₂ : ℝ≥0 → DriverSample S κ → Fin d₂ → ℝ}
    {h₂ : κ → ℝ≥0 → DriverSample S κ → Fin d₂ → ℝ} (H₁ : CoordRep μ Z₁ β₁ h₁)
    (H₂ : CoordRep μ Z₂ β₂ h₂) :
    CoordRep μ (fun t x => concatCoord (Z₁ t x) (Z₂ t x)) (fun t x => concatCoord (β₁ t x) (β₂ t x))
      (fun a t x => concatCoord (h₁ a t x) (h₂ a t x)) := by
  obtain ⟨ρ₁, hρ₁, hρ₁l, hl₁⟩ := H₁.localizing
  obtain ⟨ρ₂, hρ₂, hρ₂l, hl₂⟩ := H₂.localizing
  have hc := continuous_concatCoord (d₁ := d₁) (d₂ := d₂)
  refine ⟨fun t => hc.comp_stronglyMeasurable ((H₁.adapted t).prodMk (H₂.adapted t)),
    fun t => hc.comp_stronglyMeasurable ((H₁.progressive t).prodMk (H₂.progressive t)), ?_,
    fun t => hc.comp_stronglyMeasurable ((H₁.drift_progressive t).prodMk
      (H₂.drift_progressive t)),
    fun a t => hc.comp_stronglyMeasurable ((H₁.diffusion_progressive a t).prodMk
      (H₂.diffusion_progressive a t)), ?_,
    ⟨fun n x => min (ρ₁ n x) (ρ₂ n x), fun n => (hρ₁ n).min (hρ₂ n), ?_, ?_⟩⟩
  · filter_upwards [H₁.continuous, H₂.continuous] with x h1 h2
    exact hc.comp (h1.prodMk h2)
  · filter_upwards [H₁.drift_integrable, H₂.drift_integrable] with x h1 h2 t k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    cases s with
    | inl i => simpa only [concatCoord_inl] using h1 t i
    | inr j => simpa only [concatCoord_inr] using h2 t j
  · filter_upwards [hρ₁l, hρ₂l] with x h1 h2
    simpa using h1.min h2
  · intro n τ hτ k
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective k
    cases s with
    | inl i =>
      have e : (fun x => min ((fun n x => min (ρ₁ n x) (ρ₂ n x)) n x) (τ x)) =
          fun x => min (ρ₁ n x) (min (ρ₂ n x) (τ x)) := funext fun x => min_assoc _ _ _
      rw [e, functionalIntegrand_concat_inl, smCompensated_concat_inl]
      exact hl₁ n _ ((hρ₂ n).min hτ) i
    | inr j =>
      have e : (fun x => min ((fun n x => min (ρ₁ n x) (ρ₂ n x)) n x) (τ x)) =
          fun x => min (ρ₂ n x) (min (ρ₁ n x) (τ x)) := funext fun x => by
        simp only
        rw [min_comm (ρ₁ n x), min_assoc]
      rw [e, functionalIntegrand_concat_inr, smCompensated_concat_inr]
      exact hl₂ n _ ((hρ₁ n).min hτ) j

end BlockBand.SourceProcess.Stochastic.ItoNative
