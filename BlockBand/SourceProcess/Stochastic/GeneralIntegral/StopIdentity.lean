module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.StopGrid
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The stopping identity for the general integral

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖` (no usual conditions),
`h : IsL2Integrator Q 𝓖 N α`, horizon `T`, `ν_T = bracketMeasure Q α T`,
`H ∈ PredL2 𝓖 ν_T`, `Z = h.contIntegral T H`. Stopping times are raw `𝓖`-stopping times
`τ : Ω → WithTop ℝ≥0` (`{τ ≤ t} ∈ 𝓖_t`); exit times of a.s. continuous paths are only a.s.
equal to such times (`Semimartingale.exists_stoppingTime_ae_eq_hitTime`), and the identities
below are a.s. statements, so they transfer.

`H 1{s ≤ τ}` is the predictable class `predInd 𝓖 (stopSet τ) _ H`
(`predInd_coeFn`: representative `1_{[[0,τ]]} H` `ν_T`-a.e.).

* `stochIntegral_stopped`: `∫_0^T H 1{s ≤ u ∧ τ} dN = Z_{u ∧ τ}` a.s. (in the form
  `stoppedProcess Z τ u`).
* `stochIntegral_predInd_Iic`: deterministic times, `∫_0^T H 1{s ≤ t} dN = Z_t` a.s.
* `contIntegral_predInd_stopSet`: **timewise** stopped identity
  `∫_0^v H 1{s ≤ τ} dN = Z_{v ∧ τ}` a.s. for every `v`, and
  `contIntegral_predInd_stopSet_all`: a.s. simultaneously for all `v` (both sides have a.s.
  continuous paths).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}

omit mΩ in
theorem coe_untopA_min (t : ℝ≥0) (a : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) a).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) a := by
  have hne : min (t : WithTop ℝ≥0) a ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

omit mΩ in
theorem continuous_untopA_min (a : WithTop ℝ≥0) :
    Continuous fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) a).untopA := by
  cases a with
  | top =>
      have he : (fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) ⊤).untopA) = id := by
        funext t
        apply WithTop.coe_injective
        rw [coe_untopA_min, min_top_right, id]
      rw [he]; exact continuous_id
  | coe σ =>
      have he : (fun t : ℝ≥0 => (min (t : WithTop ℝ≥0) (σ : WithTop ℝ≥0)).untopA) =
          fun t => min t σ := by
        funext t
        apply WithTop.coe_injective
        rw [coe_untopA_min, WithTop.coe_min]
      rw [he]; exact continuous_id.min continuous_const

omit mΩ in
/-- A stopped continuous path is continuous. -/
theorem continuous_stoppedProcess {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : Continuous fun t => X t ω)
    (τ : Ω → WithTop ℝ≥0) : Continuous fun t => stoppedProcess X τ t ω :=
  hX.comp (continuous_untopA_min (τ ω))

/-- Two a.s. continuous processes that agree a.s. at each time agree a.s. at all times. -/
theorem ae_forall_eq_of_continuous {X Y : ℝ≥0 → Ω → ℝ}
    (hX : ∀ᵐ ω ∂Q, Continuous fun t => X t ω) (hY : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    (h : ∀ t, X t =ᵐ[Q] Y t) : ∀ᵐ ω ∂Q, ∀ t, X t ω = Y t ω := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂Q, ∀ t : D, X t ω = Y t ω := ae_all_iff.2 fun t => h t
  filter_upwards [hX, hY, hall] with ω hx hy hxy
  exact fun t => congrFun (Continuous.ext_on hD hx hy (fun s hs => hxy ⟨s, hs⟩)) t

variable [IsFiniteMeasure Q] {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ}

namespace IsL2Integrator

variable (h : IsL2Integrator Q 𝓖 N α) (T : ℝ≥0) (H : PredL2 𝓖 (bracketMeasure Q α T))

/-- **Stopping identity** `∫_0^T H 1{s ≤ u ∧ τ} dN = Z_{u ∧ τ}` a.s. -/
theorem stochIntegral_stopped {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (u : ℝ≥0) :
    (h.stochIntegral T (predInd 𝓖 (stopSet fun ω => min (u : WithTop ℝ≥0) (τ ω))
      (measurableSet_stopSet 𝓖 ((isStoppingTime_const 𝓖 u).min hτ)) H) : Ω → ℝ) =ᵐ[Q]
      stoppedProcess (h.contIntegral T H) τ u := by
  let σ : Ω → ℝ≥0 := fun ω => (min (u : WithTop ℝ≥0) (τ ω)).untopA
  have hσcoe (ω : Ω) : ((σ ω : ℝ≥0) : WithTop ℝ≥0) = min (u : WithTop ℝ≥0) (τ ω) :=
    coe_untopA_min u (τ ω)
  have hσu (ω : Ω) : σ ω ≤ u := by
    have h1 := min_le_left (u : WithTop ℝ≥0) (τ ω)
    rw [← hσcoe ω] at h1
    exact_mod_cast h1
  have hσ (t : ℝ≥0) : MeasurableSet[𝓖 t] {ω | σ ω ≤ t} := by
    have he : {ω | σ ω ≤ t} = {ω | min (u : WithTop ℝ≥0) (τ ω) ≤ t} := by
      ext ω
      simp only [mem_ofPred_eq]
      rw [← hσcoe ω, WithTop.coe_le_coe]
    rw [he]
    exact (isStoppingTime_const 𝓖 u).min hτ t
  obtain ⟨hS, hae⟩ := h.stochIntegral_stopSet_of_bounded T H hσu hσ
  have hset : stopSet (fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) =
      stopSet fun ω => min (u : WithTop ℝ≥0) (τ ω) := by
    simp only [hσcoe]
  rw [predInd_congr 𝓖 _ hS (by rw [hset]) H]
  exact hae

/-- **Deterministic times**: `∫_0^T H 1{s ≤ t} dN = Z_t` a.s. -/
theorem stochIntegral_predInd_Iic (t : ℝ≥0) :
    (h.stochIntegral T (predInd 𝓖 (Iic (t : ℝ) ×ˢ univ) (measurableSet_Iic_prod_univ 𝓖 t) H) :
      Ω → ℝ) =ᵐ[Q] h.contIntegral T H t := by
  obtain ⟨hS, hae⟩ := h.stochIntegral_stopSet_of_bounded T H (σ := fun _ => t) (u := t)
    (fun _ => le_rfl) (fun t' => MeasurableSet.const _)
  rw [predInd_congr 𝓖 _ hS (by rw [stopSet_const]) H]
  exact hae

/-- **Timewise stopped identity** `∫_0^v H 1{s ≤ τ} dN = Z_{v ∧ τ}` a.s. -/
theorem contIntegral_predInd_stopSet {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (v : ℝ≥0) :
    h.contIntegral T (predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H) v =ᵐ[Q]
      stoppedProcess (h.contIntegral T H) τ v := by
  set H' := predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H
  have hIic := measurableSet_Iic_prod_univ (Ω := Ω) 𝓖 v
  have h1 := h.stochIntegral_predInd_Iic T H' v
  have hset : Iic (v : ℝ) ×ˢ (univ : Set Ω) ∩ stopSet τ =
      stopSet fun ω => min (v : WithTop ℝ≥0) (τ ω) := by
    rw [stopSet_min, stopSet_const]
  have h2 : predInd 𝓖 (Iic (v : ℝ) ×ˢ univ) hIic H' =
      predInd 𝓖 (stopSet fun ω => min (v : WithTop ℝ≥0) (τ ω))
        (measurableSet_stopSet 𝓖 ((isStoppingTime_const 𝓖 v).min hτ)) H := by
    simp only [H']
    rw [predInd_predInd]
    exact predInd_congr 𝓖 _ _ (by rw [hset]) H
  rw [h2] at h1
  exact h1.symm.trans (h.stochIntegral_stopped T H hτ v)

/-- The timewise stopped identity holds a.s. simultaneously for all times. -/
theorem contIntegral_predInd_stopSet_all {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    ∀ᵐ ω ∂Q, ∀ v, h.contIntegral T (predInd 𝓖 (stopSet τ) (measurableSet_stopSet 𝓖 hτ) H) v ω =
      stoppedProcess (h.contIntegral T H) τ v ω := by
  refine ae_forall_eq_of_continuous (h.contIntegral_continuous T _) ?_
    (h.contIntegral_predInd_stopSet T H hτ)
  filter_upwards [h.contIntegral_continuous T H] with ω hω
  exact continuous_stoppedProcess hω τ

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
