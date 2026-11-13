module

public import BlockBand.Transmission.Dual.MPConverse
public import BlockBand.SourceProcess.Stochastic.Levy.Product

/-!
# Tools for products of martingale-problem solutions

* `martingale_mul_lift`: for martingales `M₁` on `(Ω₁, 𝓖₁, Q₁)` and `M₂` on `(Ω₂, 𝓖₂, Q₂)`, the
  product `M₁(ω₁) M₂(ω₂)` is a martingale for the product filtration under `Q₁ ⊗ Q₂`
  (rectangles, `setIntegral_prod_mul`, π–λ); `hasMM_mul_lift` (modification form).
* `stopTime_stopTime_of_le`, `hasMM_stop_congr`: stopping again at an earlier exit time.
* `continuous_stopped_integral`: `t ↦ ∫_0^{t ∧ τ_W} g(Y_s) ds` is continuous for a continuous
  path, `g` continuous on `U ⊇ closure W`; `continuous_stopped_mpCompensated` and
  `continuous_stopped_bracket` (the stopped compensated coordinates and brackets).
* `exists_interiorDomain_superset`: a compact subset of an open `U` lies in an interior domain.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  stopTime_top stopTime_coe)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section Product

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {Q₁ : Measure Ω₁} {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₁] [IsProbabilityMeasure Q₂]
  {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
  {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}

/-- **Products of martingales of the two factors are martingales** of the product filtration. -/
theorem martingale_mul_lift {M₁ : ℝ≥0 → Ω₁ → ℝ} {M₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : Martingale M₁ 𝓖₁ Q₁) (h₂ : Martingale M₂ 𝓖₂ Q₂) :
    Martingale (fun t (x : Ω₁ × Ω₂) => M₁ t x.1 * M₂ t x.2) (prodFiltration 𝓖₁ 𝓖₂)
      (Q₁.prod Q₂) := by
  have hint : ∀ t, Integrable (fun x : Ω₁ × Ω₂ => M₁ t x.1 * M₂ t x.2) (Q₁.prod Q₂) := fun t =>
    (h₁.integrable t).mul_prod (h₂.integrable t)
  refine martingale_of_setIntegral_eq (fun t => ((h₁.1 t).comp_measurable
    (measurable_fst_prodFiltration t)).mul ((h₂.1 t).comp_measurable
    (measurable_snd_prodFiltration t))) hint fun s t hst S hS => ?_
  have h0 := setIntegral_eq_zero_of_rect (P := Q₁.prod Q₂)
    (D := fun x => M₁ t x.1 * M₂ t x.2 - M₁ s x.1 * M₂ s x.2)
    ((hint t).sub (hint s)) (fun A B hA hB => ?_) hS
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn] at h0
    linarith
  · rw [integral_sub (hint t).integrableOn (hint s).integrableOn,
      setIntegral_prod_mul (M₁ t) (M₂ t) A B, setIntegral_prod_mul (M₁ s) (M₂ s) A B,
      h₁.setIntegral_eq hst hA, h₂.setIntegral_eq hst hB, sub_self]

theorem hasMM_mul_lift {X₁ : ℝ≥0 → Ω₁ → ℝ} {X₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : HasMartingaleModification Q₁ 𝓖₁ X₁) (h₂ : HasMartingaleModification Q₂ 𝓖₂ X₂) :
    HasMartingaleModification (Q₁.prod Q₂) (prodFiltration 𝓖₁ 𝓖₂)
      (fun t x => X₁ t x.1 * X₂ t x.2) := by
  obtain ⟨M₁, hM₁, e₁⟩ := h₁
  obtain ⟨M₂, hM₂, e₂⟩ := h₂
  refine ⟨_, martingale_mul_lift hM₁ hM₂, fun t => ?_⟩
  have a₁ := measurePreserving_fst.quasiMeasurePreserving.ae_eq_comp (μa := Q₁.prod Q₂) (e₁ t)
  have a₂ := measurePreserving_snd.quasiMeasurePreserving.ae_eq_comp (μa := Q₁.prod Q₂) (e₂ t)
  filter_upwards [a₁, a₂] with x hx₁ hx₂
  simp only [Function.comp_apply] at hx₁ hx₂
  rw [hx₁, hx₂]

omit [IsProbabilityMeasure Q₁] in
theorem ae_fst {p : Ω₁ → Prop} (h : ∀ᵐ ω ∂Q₁, p ω) : ∀ᵐ x ∂(Q₁.prod Q₂), p x.1 :=
  measurePreserving_fst.quasiMeasurePreserving.ae h

theorem ae_snd {p : Ω₂ → Prop} (h : ∀ᵐ ω ∂Q₂, p ω) : ∀ᵐ x ∂(Q₁.prod Q₂), p x.2 :=
  measurePreserving_snd.quasiMeasurePreserving.ae h

end Product

/-!
## Stopping again
-/

theorem stopTime_stopTime_of_le {τ σ : WithTop ℝ≥0} (h : τ ≤ σ) (t : ℝ≥0) :
    stopTime σ (stopTime τ t) = stopTime τ t := by
  induction σ with
  | top => exact stopTime_top _
  | coe s =>
    induction τ with
    | top => exact absurd h (not_le.2 (WithTop.coe_lt_top s))
    | coe r =>
      rw [stopTime_coe, stopTime_coe, min_eq_left]
      exact (min_le_right t r).trans (WithTop.coe_le_coe.1 h)

section Stop

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Stopping a continuous martingale modification `Z` at an exit time `τ`, when `Z` and `X`
agree after stopping at `τ`. -/
theorem hasMM_stop_congr {Z X : ℝ≥0 → Ω → ℝ} (hZ : HasMartingaleModification Q 𝓖 Z)
    (hZc : ∀ᵐ ω ∂Q, Continuous fun t => Z t ω) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, Measurable[𝓖 t] (Y t)) (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω)
    {W : Set (Fin d → ℝ)} (hW : IsOpen W)
    (heq : ∀ t ω, stoppedProcess Z (exitTimeFrom W Y) t ω =
      stoppedProcess X (exitTimeFrom W Y) t ω) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X (exitTimeFrom W Y)) :=
  hasMM_congr (hasMM_stop hZ hZc hY hYc hW) fun t => Eventually.of_forall fun ω => heq t ω

end Stop

/-!
## Continuity of the stopped compensated processes
-/

section Cont

variable {d : ℕ} {Ω : Type*}

theorem stopTime_eq_self_of_le_stopTime {τ : WithTop ℝ≥0} {t s : ℝ≥0} (hs : s ≤ stopTime τ t) :
    stopTime τ s = s := by
  induction τ with
  | top => exact stopTime_top s
  | coe r =>
    rw [stopTime_coe] at hs ⊢
    exact min_eq_left (hs.trans (min_le_right _ _))

/-- `t ↦ ∫_0^{t ∧ τ_W} g(Y_s) ds` is continuous along a continuous path. -/
theorem continuous_stopped_integral {W U : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hWU : closure W ⊆ U) {g : (Fin d → ℝ) → ℝ} (hg : ContinuousOn g U)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hω : Continuous fun t => Y t ω) :
    Continuous fun t : ℝ≥0 =>
      ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), g (Y s.toNNReal ω) := by
  set τ := exitTimeFrom W Y ω
  by_cases h0 : Y 0 ω ∈ W
  · -- the stopped path stays in `closure W ⊆ U`
    have hmem : ∀ u, Y (stopTime τ u) ω ∈ closure W := fun u =>
      Semimartingale.stop_mem_closure hW hω h0 u
    have hcs : Continuous fun u : ℝ≥0 => Y (stopTime τ u) ω :=
      hω.comp (Semimartingale.continuous_stopTime τ)
    have hgc : Continuous fun s : ℝ => g (Y (stopTime τ s.toNNReal) ω) :=
      hg.comp_continuous (hcs.comp continuous_real_toNNReal) fun s => hWU (hmem _)
    have hprim := intervalIntegral.continuous_primitive
      (fun a c => hgc.intervalIntegrable (μ := volume) a c) (0 : ℝ)
    have he : (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) (stopTime τ t), g (Y s.toNNReal ω)) =
        fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(stopTime τ t : ℝ), g (Y (stopTime τ s.toNNReal) ω) := by
      funext t
      rw [intervalIntegral.integral_of_le (stopTime τ t).coe_nonneg]
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hle : s.toNNReal ≤ stopTime τ t := Real.toNNReal_le_iff_le_coe.2 hs.2
      simp only [stopTime_eq_self_of_le_stopTime hle]
    rw [he]
    exact hprim.comp (NNReal.continuous_coe.comp (Semimartingale.continuous_stopTime τ))
  · -- the exit time is `0`
    have hτ : τ = 0 := le_antisymm (iInf₂_le 0 h0) bot_le
    have : (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) (stopTime τ t), g (Y s.toNNReal ω)) = fun _ => 0 := by
      funext t
      have : stopTime τ t = 0 := by
        rw [hτ, show (0 : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) from rfl, stopTime_coe]
        exact min_eq_right bot_le
      simp [this]
    rw [this]; exact continuous_const

theorem continuous_stopped_mpCompensated {W U : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hWU : closure W ⊆ U) {b : (Fin d → ℝ) → Fin d → ℝ} (hb : ContinuousOn b U)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hω : Continuous fun t => Y t ω) (i : Fin d) :
    Continuous fun t => stoppedProcess (mpCompensated b Y i) (exitTimeFrom W Y) t ω := by
  simp only [stoppedProcess_eq_stopTime, mpCompensated]
  have hcs : Continuous fun u : ℝ≥0 => Y (stopTime (exitTimeFrom W Y ω) u) ω :=
    hω.comp (Semimartingale.continuous_stopTime _)
  exact (((continuous_apply i).comp hcs).sub continuous_const).sub
    (continuous_stopped_integral hW hWU ((continuous_apply i).comp_continuousOn hb) hω)

theorem continuous_stopped_bracket {W U : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hWU : closure W ⊆ U) {b : (Fin d → ℝ) → Fin d → ℝ} (hb : ContinuousOn b U)
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} (ha : ContinuousOn a U)
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hω : Continuous fun t => Y t ω) (i j : Fin d) :
    Continuous fun t => stoppedProcess (fun t ω => mpCompensated b Y i t ω *
      mpCompensated b Y j t ω - ∫ s in Ioc (0 : ℝ) t, a (Y s.toNNReal ω) i j)
      (exitTimeFrom W Y) t ω := by
  have hi := continuous_stopped_mpCompensated hW hWU hb hω i
  have hj := continuous_stopped_mpCompensated hW hWU hb hω j
  have haij : ContinuousOn (fun y => a y i j) U :=
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn ha)
  simp only [stoppedProcess_eq_stopTime] at hi hj ⊢
  exact (hi.mul hj).sub (continuous_stopped_integral hW hWU haij hω)

end Cont

/-- A compact subset of an open set lies in an interior domain of it. -/
theorem exists_interiorDomain_superset {d : ℕ} {K U : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) : ∃ W, IsInteriorDomain W U ∧ K ⊆ W := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  refine ⟨interior L, ⟨isOpen_interior, ?_, ?_⟩, hKL⟩
  · exact hL.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hL.isClosed)
  · exact (closure_minimal interior_subset hL.isClosed).trans hLU

end BlockBand.Transmission.Dual.G
