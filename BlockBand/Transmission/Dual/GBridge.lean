module

public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse

/-!
# Martingale problems from characteristics that are Markov up to the exits

A variant of `IsContinuousSemimartingale.isMPSolutionOn` for exit-time SDE solutions, whose
characteristics are switched off after their own exit time: if `Y` is a continuous
semimartingale with characteristics `(β, α)` and, for every relatively compact subdomain `W` of
`U`, `β_s = b(Y_s)` and `α_s = a(Y_s)` for `s ≤ τ_W` (`τ_W` the exit time from `W`), then `Y`
solves the `(b, a)` martingale problem in `U` (`isMPSolutionOn_of_agree`). The proof stops the
localization at the hitting time of `Wᶜ` and then removes it by domination; the stopped
compensated processes of `(β, α)` and of `(b(Y), a(Y))` coincide pathwise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}

theorem coe_stopTime_le (e : WithTop ℝ≥0) (t : ℝ≥0) : (stopTime e t : WithTop ℝ≥0) ≤ e := by
  induction e with
  | top => exact le_top
  | coe e₀ => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)

omit [MeasurableSpace Ω] in
theorem stopped_integral_agree {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    {f g : ℝ≥0 → ℝ} (h : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω → f s = g s)
    (t : ℝ≥0) :
    ∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), f u.toNNReal =
      ∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), g u.toNNReal := by
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => h _ ?_
  have hle : u.toNNReal ≤ stopTime (exitTimeFrom W Y ω) t :=
    Real.toNNReal_le_iff_le_coe.2 hu.2
  exact (WithTop.coe_le_coe.2 hle).trans (coe_stopTime_le _ _)

/-- **A semimartingale whose characteristics agree with `(b(Y), a(Y))` up to every exit from an
interior domain solves the `(b, a)` martingale problem in `U`.** -/
theorem isMPSolutionOn_of_agree {b : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {U : Set (Fin d → ℝ)} (hb : ContinuousOn b U)
    (ha : ContinuousOn a U) {Y : ℝ≥0 → Ω → Fin d → ℝ} {β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    (hagree : ∀ W, IsInteriorDomain W U → ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω →
      β s ω = b (Y s ω) ∧ α s ω = a (Y s ω)) :
    IsMPSolutionOn Q 𝓖 b a U Y := by
  obtain ⟨τ, -, hτlim, hmart⟩ := H.localizing
  have hmeas : ∀ t, Measurable[𝓖 t] (Y t) := fun t => (H.adapted t).measurable
  have key : ∀ W, IsInteriorDomain W U → ∀ (X : ℝ≥0 → Ω → ℝ),
      (∀ n, HasMartingaleModification Q 𝓖 (stoppedProcess X (τ n))) →
      (∀ᵐ ω ∂Q, Continuous fun t => X t ω) →
      (∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |X (stopTime (exitTimeFrom W Y ω) s) ω| ≤ C) →
      ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 Q ∧
        ∀ t, N t =ᵐ[Q] stoppedProcess X (exitTimeFrom W Y) t := by
    intro W hW X hX hXc hXb
    have hρ := isStoppingTime_rawHit (F := Wᶜ) hmeas
    have hae : ∀ᵐ ω ∂Q, rawHit Wᶜ Y ω = exitTimeFrom W Y ω := by
      filter_upwards [H.continuous] with ω hω
      exact rawHit_eq_hitTime hW.1.isClosed_compl hω
    have h1 : ∀ n, HasMartingaleModification Q 𝓖
        (stoppedProcess (stoppedProcess X (rawHit Wᶜ Y)) (τ n)) := fun n => by
      rw [stoppedProcess_stoppedProcess']
      exact hasMartingaleModification_stopped_min (hX n) hXc hρ fun ω => min_comm _ _
    obtain ⟨N, hN, hNe⟩ := hasMartingaleModification_of_localized hτlim h1 fun t => by
      obtain ⟨C, hC⟩ := hXb t
      refine ⟨C, ?_⟩
      filter_upwards [hC, hae] with ω h h'
      intro s hs
      simp only [stoppedProcess_eq_stopTime, h']
      exact h s hs
    refine ⟨N, hN, fun t => (hNe t).trans ?_⟩
    filter_upwards [hae] with ω h
    simp only [stoppedProcess_eq_stopTime, h]
  have hcomp : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => smCompensated Y β i t ω := by
    filter_upwards [H.continuous, H.integrable] with ω hω hi i
    exact continuous_smCompensated hω fun t => (hi t).1 i
  -- pathwise agreement of the stopped compensated coordinates
  have hsm : ∀ W, IsInteriorDomain W U → ∀ i ω t,
      smCompensated Y β i (stopTime (exitTimeFrom W Y ω) t) ω =
        smCompensated Y (fun t ω => b (Y t ω)) i (stopTime (exitTimeFrom W Y ω) t) ω := by
    intro W hW i ω t
    simp only [smCompensated]
    rw [stopped_integral_agree (f := fun s => β s ω i) (g := fun s => b (Y s ω) i)
      (fun s hs => by rw [(hagree W hW ω s hs).1])]
  have bounds : ∀ W, IsInteriorDomain W U → ∃ R B : ℝ, 0 ≤ R ∧ 0 ≤ B ∧
      (∀ y ∈ closure W, ‖y‖ ≤ R) ∧ ∀ y ∈ closure W, ‖b y‖ ≤ B := fun W hW => by
    obtain ⟨R, hR⟩ := hW.2.1.exists_bound_of_continuousOn continuousOn_id
    obtain ⟨B, hB⟩ := hW.2.1.exists_bound_of_continuousOn (hb.mono hW.2.2)
    exact ⟨max R 0, max B 0, le_max_right _ _, le_max_right _ _,
      fun y hy => (hR y hy).trans (le_max_left _ _), fun y hy => (hB y hy).trans (le_max_left _ _)⟩
  refine ⟨H.adapted, H.continuous, fun W hW i => ?_, fun W hW i j => ?_⟩
  · obtain ⟨R, B, hR, hB, hRW, hBW⟩ := bounds W hW
    have hbd : ∀ t : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t,
        |smCompensated Y β i (stopTime (exitTimeFrom W Y ω) s) ω| ≤ C := fun t =>
      ⟨2 * R + B * t, by
        filter_upwards [H.continuous] with ω hω s hs
        rw [hsm W hW]
        exact abs_smCompensated_stop_le hW.1 hω hR hB hRW hBW hs i⟩
    obtain ⟨N, hN, hNe⟩ := key W hW (smCompensated Y β i) (fun n => (hmart n).1 i)
      (hcomp.mono fun _ h => h i) hbd
    refine ⟨N, hN, fun t => (hNe t).trans (Eventually.of_forall fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, hsm W hW]
    rfl
  · obtain ⟨R, B, hR, hB, hRW, hBW⟩ := bounds W hW
    obtain ⟨A, hA⟩ := hW.2.1.exists_bound_of_continuousOn
      (((continuous_apply j).comp (continuous_apply i)).comp_continuousOn (ha.mono hW.2.2))
    have hint : ∀ ω t, ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), α s.toNNReal ω i j =
        ∫ s in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), a (Y s.toNNReal ω) i j :=
      fun ω t => stopped_integral_agree (f := fun s => α s ω i j) (g := fun s => a (Y s ω) i j)
        (fun s hs => by rw [(hagree W hW ω s hs).2]) t
    have hc : ∀ᵐ ω ∂Q, Continuous fun t => smCompensated Y β i t ω * smCompensated Y β j t ω -
        ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j := by
      filter_upwards [hcomp, H.integrable] with ω h1 h2
      exact ((h1 i).mul (h1 j)).sub
        (continuous_setIntegral_Ioc (g := fun u => α u ω i j) fun t => (h2 t).2 i j)
    have hbd : ∀ t : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t,
        |smCompensated Y β i (stopTime (exitTimeFrom W Y ω) s) ω *
          smCompensated Y β j (stopTime (exitTimeFrom W Y ω) s) ω -
          ∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) s), α u.toNNReal ω i j| ≤ C := fun t =>
      ⟨(2 * R + B * t) * (2 * R + B * t) + max A 0 * t, by
        filter_upwards [H.continuous] with ω hω s hs
        simp only [hsm W hW, hint]
        have hx := abs_smCompensated_stop_le hW.1 hω hR hB hRW hBW hs i
        have hy := abs_smCompensated_stop_le hW.1 hω hR hB hRW hBW hs j
        have hz := abs_integral_stop_le hW.1 hω (g := fun y => a y i j) (le_max_right A 0)
          (fun y hy => by rw [← Real.norm_eq_abs]; exact (hA y hy).trans (le_max_left _ _)) hs
        calc _ ≤ |smCompensated Y (fun t ω => b (Y t ω)) i (stopTime (exitTimeFrom W Y ω) s) ω *
              smCompensated Y (fun t ω => b (Y t ω)) j (stopTime (exitTimeFrom W Y ω) s) ω| +
              |∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) s), a (Y u.toNNReal ω) i j| :=
            abs_sub _ _
          _ ≤ _ := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)) hz⟩
    obtain ⟨N, hN, hNe⟩ := key W hW _ (fun n => (hmart n).2 i j) hc hbd
    refine ⟨N, hN, fun t => (hNe t).trans (Eventually.of_forall fun ω => ?_)⟩
    simp only [stoppedProcess_eq_stopTime, hsm W hW, hint]
    rfl

end BlockBand.Transmission.Dual.G
