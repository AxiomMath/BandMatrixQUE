module

public import BlockBand.Transmission.DualFeller.PairStab
public import BlockBand.Transmission.Dual.Hitting

/-!
# Maximal form of the pair stability estimate

`measure_pair_sup_le`: with `c ≥ 0` a Lyapunov constant of the pair on the radius-`m` ball and
a `𝓖₀`-event `A` on which `‖ξ‖, ‖ξ'‖ ≤ m` and `pairDist(ξ, ξ') ≤ B`, for every `T` and `r > 0`,
`P(A ∩ {∃ t ≤ T, t ≤ e_m ∧ e'_m, pairDist(X_t, X'_t) ≥ r}) ≤ 2 e^{cT} B / r`.
Proof: `lintegral_pair_le` at the hitting time `θ` of `{pairDist ≥ r}` (a stopping time since
the paths are continuous at every `ω`); on the event, `θ ≤ T ∧ jointStop` and
`pairDist(X_θ, X'_θ) ≥ r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ ξ' : LΩ S → Fin 6 → ℝ}

theorem le_ofReal_div_of_mul_le {x y : ℝ} (hx : 0 < x) {P : ℝ≥0∞}
    (h : ENNReal.ofReal x * P ≤ ENNReal.ofReal y) : P ≤ ENNReal.ofReal (y / x) := by
  rw [ENNReal.ofReal_div_of_pos hx, ENNReal.le_div_iff_mul_le
    (Or.inl (by simpa using hx)) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

/-- **Maximal pair stability estimate.** -/
theorem measure_pair_sup_le (F : LiftFamily μ D0 ξ) (F' : LiftFamily μ D0 ξ') (m : ℕ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ y : P6, ‖y.1‖ ≤ m → ‖y.2‖ ≤ m →
      sdeGenerator (pairDrift D0) (pairSigma D0) pairDist y ≤ c * pairDist y)
    {A : Set (LΩ S)} (hA : MeasurableSet[L𝓖 μ 0] A)
    (hAm : ∀ ω ∈ A, ‖ξ ω‖ ≤ m ∧ ‖ξ' ω‖ ≤ m) {B : ℝ} (hB0 : 0 < B)
    (hB : ∀ ω ∈ A, pairDist (ξ ω, ξ' ω) ≤ B) (T : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    LP μ (A ∩ {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ min (F.e m ω) (F'.e m ω) ∧
      r ≤ pairDist (F.X m t ω, F'.X m t ω)}) ≤
      ENNReal.ofReal (2 / (exp (-c * T) * (B⁻¹ * r))) := by
  set V : ℝ≥0 → LΩ S → ℝ := fun t ω => -pairDist (F.X m t ω, F'.X m t ω) with hVdef
  have hVc : ∀ ω, Continuous fun t => V t ω := fun ω =>
    (contDiff_pairDist.continuous.comp ((F.continuous_X m ω).prodMk (F'.continuous_X m ω))).neg
  have hR : ∀ ω t, Tendsto (fun u => V u ω) (𝓝[≥] t) (𝓝 (V t ω)) := fun ω t =>
    (hVc ω).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hθ : IsStoppingTime (L𝓖 μ) (hitLe V (-r)) :=
    isStoppingTime_hitLe (fun t => (contDiff_pairDist.continuous.measurable.comp
      ((((F.strong m).sol.1.adapted t).measurable).prodMk
        (((F'.strong m).sol.1.adapted t).measurable))).neg) hR
      (fun ω => (hVc ω).lowerSemicontinuous) (-r)
  obtain ⟨hm, hle⟩ := lintegral_pair_le F F' m hc0 hc hA hAm hB0 hB hθ T
  set b : ℝ := exp (-c * T) * (B⁻¹ * r) with hbdef
  have hb : 0 < b := mul_pos (exp_pos _) (mul_pos (inv_pos.2 hB0) hr)
  refine le_ofReal_div_of_mul_le hb (le_trans ?_
    ((mul_meas_ge_le_lintegral₀ hm.ennreal_ofReal.aemeasurable (ENNReal.ofReal b)).trans hle))
  refine mul_le_mul_right (le_trans (measure_mono ?_) (Measure.le_restrict_apply _ _)) _
  rintro ω ⟨hωA, t, htT, hte, hrt⟩
  refine ⟨?_, hωA⟩
  have hθt : hitLe V (-r) ω ≤ t := (hitLe_le_iff (hR ω) t).2 ⟨t, le_rfl, by
    simp only [hVdef]; linarith⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hθt)
  have hst : s ≤ t := WithTop.coe_le_coe.1 (hs ▸ hθt)
  have hVs : V s ω ≤ -r := hitLe_attained (hR ω) hs.symm
  have hsj : hitLe V (-r) ω ≤ jointStop F F' m A ω := by
    simp only [jointStop, hωA, ite_true]
    exact hθt.trans hte
  have hmin : min (T : WithTop ℝ≥0) (min (hitLe V (-r) ω) (jointStop F F' m A ω)) = s := by
    rw [min_eq_left hsj, ← hs, min_eq_right (WithTop.coe_le_coe.2 (hst.trans htT))]
  simp only [mem_ofPred_eq, hmin]
  refine ENNReal.ofReal_le_ofReal ?_
  change exp (-c * T) * (B⁻¹ * r) ≤ exp (-c * s) * (1 + B⁻¹ * pairDist (F.X m s ω, F'.X m s ω))
  have h1 : exp (-c * T) ≤ exp (-c * s) := exp_le_exp.2 (by
    have : (s : ℝ) ≤ T := NNReal.coe_le_coe.2 (hst.trans htT)
    nlinarith)
  have h2 : B⁻¹ * r ≤ 1 + B⁻¹ * pairDist (F.X m s ω, F'.X m s ω) := by
    have : r ≤ pairDist (F.X m s ω, F'.X m s ω) := by simp only [hVdef] at hVs; linarith
    nlinarith [inv_pos.2 hB0]
  exact mul_le_mul h1 h2 (by positivity) (exp_pos _).le

end BlockBand.Transmission.DualFeller
