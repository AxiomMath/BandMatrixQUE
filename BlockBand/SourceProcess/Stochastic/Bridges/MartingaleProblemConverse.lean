module
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.Bridges.Concat
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bridge: continuous semimartingales with Markov characteristics solve the martingale problem

Setting: filtered probability space `(Ω, 𝓖, Q)` with a raw filtration; an open domain
`U ⊆ ℝ^d`; coefficients `b, a` continuous on `U`.

* `hasMartingaleModification_of_localized`: if `X^{τ_n}` has a martingale modification for
  every `n`, `τ_n → ⊤` a.s., and for each `t` the values `X_s`, `s ≤ t`, are a.s. bounded by
  a constant, then `X` has a martingale modification (dominated convergence; no path
  regularity of `X` is needed).

* `IsContinuousSemimartingale.isMPSolutionOn`: a continuous semimartingale with characteristics
  `(b(Y), a(Y))` solves the `(b, a)` martingale problem in `U`.

With `IsMPSolutionOn.isContinuousSemimartingale` this gives, for `U = ℝ^d` and progressive `Y`,
the equivalence of the two notions.
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ}

/-!
### Pathwise facts for stopping at the exit time
-/

theorem stopTime_eq_of_le_stopTime {e : WithTop ℝ≥0} {u t : ℝ≥0} (h : u ≤ stopTime e t) :
    stopTime e u = u := by
  induction e with
  | top => exact stopTime_top u
  | coe e₀ =>
    rw [stopTime_coe] at h ⊢
    exact min_eq_left (h.trans (min_le_right _ _))

/-- Along a continuous path, up to the exit time from an open `W` the path stays in
`closure W`, unless it starts outside `W` (then the exit time is `0`). -/
theorem stopped_path_mem_closure {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) (t : ℝ≥0) :
    (∀ s ∈ Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), Y s.toNNReal ω ∈ closure W) ∧
      (Y (stopTime (exitTimeFrom W Y ω) t) ω = Y 0 ω ∨
        (Y (stopTime (exitTimeFrom W Y ω) t) ω ∈ closure W ∧ Y 0 ω ∈ closure W)) := by
  by_cases h0 : Y 0 ω ∈ W
  · refine ⟨fun s hs => ?_, Or.inr ⟨stop_mem_closure hW hY h0 t, subset_closure h0⟩⟩
    have hle : s.toNNReal ≤ stopTime (exitTimeFrom W Y ω) t :=
      Real.toNNReal_le_iff_le_coe.2 hs.2
    rw [← stopTime_eq_of_le_stopTime hle]
    exact stop_mem_closure hW hY h0 _
  · have he : exitTimeFrom W Y ω = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm (iInf₂_le 0 h0) bot_le
    have hs : stopTime (exitTimeFrom W Y ω) t = 0 := by
      rw [he, stopTime_coe]; exact min_eq_right zero_le
    refine ⟨fun s hs' => ?_, Or.inl (by rw [hs])⟩
    rw [hs] at hs'
    exact absurd (hs'.1.trans_le hs'.2) (lt_irrefl _)

/-!
### Removing a localizing sequence under domination
-/

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Removing the localization under domination.** -/
theorem hasMartingaleModification_of_localized {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : ∀ᵐ ω ∂Q, Tendsto (fun n => τ n ω) atTop (𝓝 ⊤))
    (hloc : ∀ n, HasMartingaleModification Q 𝓖 (stoppedProcess X (τ n)))
    (hbd : ∀ t, ∃ C, ∀ᵐ ω ∂Q, ∀ s ≤ t, |X s ω| ≤ C) :
    HasMartingaleModification Q 𝓖 X := by
  choose M hM hMX using hloc
  have hlim : ∀ t, ∀ᵐ ω ∂Q, Tendsto (fun n => M n t ω) atTop (𝓝 (X t ω)) := fun t => by
    filter_upwards [hτ, ae_all_iff.2 fun n => hMX n t] with ω h1 h2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 h1 t] with n hn
    rw [h2 n, stoppedProcess_eq_stopTime, stopTime_of_lt hn]
  have hbM : ∀ t, ∃ C, ∀ n, ∀ᵐ ω ∂Q, ‖M n t ω‖ ≤ C := fun t => by
    obtain ⟨C, hC⟩ := hbd t
    refine ⟨C, fun n => ?_⟩
    filter_upwards [hC, hMX n t] with ω h1 h2
    rw [h2, stoppedProcess_eq_stopTime, Real.norm_eq_abs]
    exact h1 _ (stopTime_le _ _)
  have hmeas : ∀ t, AEStronglyMeasurable (X t) Q := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => ((hM n).integrable t).1) (hlim t)
  have hDCT : ∀ t (A : Set Ω), Tendsto (fun n => ∫ ω in A, M n t ω ∂Q) atTop
      (𝓝 (∫ ω in A, X t ω ∂Q)) := fun t A => by
    obtain ⟨C, hC⟩ := hbM t
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hM n).integrable t).1.restrict) (integrable_const C)
      (fun n => ae_restrict_of_ae (hC n)) (ae_restrict_of_ae (hlim t))
  refine exists_martingale_modification (fun t => ?_) (fun t => ?_) (fun s t hst A hA => ?_)
  · obtain ⟨C, hC⟩ := hbd t
    refine Integrable.mono' (integrable_const C) (hmeas t) ?_
    filter_upwards [hC] with ω hω
    rw [Real.norm_eq_abs]; exact hω t le_rfl
  · exact aestronglyMeasurable_of_tendsto_ae_sub
      (fun n => ((hM n).1 t).aestronglyMeasurable) (hlim t)
  · have e : ∀ n, ∫ ω in A, M n t ω ∂Q = ∫ ω in A, M n s ω ∂Q := fun n =>
      ((hM n).setIntegral_eq hst hA).symm
    exact tendsto_nhds_unique ((hDCT t A).congr e) (hDCT s A)

/-!
### Bounds for the stopped compensated processes
-/

omit [MeasurableSpace Ω] in
/-- A bound `‖g‖ ≤ B` on `closure W` for the integrand bounds the integral up to the exit. -/
theorem abs_integral_stop_le {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {g : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀ y ∈ closure W, |g y| ≤ B) {t s : ℝ≥0} (hs : s ≤ t) :
    |∫ u in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) s), g (Y u.toNNReal ω)| ≤ B * t := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (f := fun u : ℝ => g (Y u.toNNReal ω)) measure_Ioc_lt_top
    (fun u hu => by rw [Real.norm_eq_abs]; exact hg _ ((stopped_path_mem_closure hW hY s).1 u hu))
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  simp only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (NNReal.coe_nonneg _)]
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ((stopTime_le _ _).trans hs)) hB

omit [MeasurableSpace Ω] in
/-- The increment of a coordinate up to the exit is bounded by `2R`. -/
theorem abs_sub_stop_le {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {R : ℝ} (hR : 0 ≤ R)
    (hRW : ∀ y ∈ closure W, ‖y‖ ≤ R) (s : ℝ≥0) (i : Fin d) :
    |Y (stopTime (exitTimeFrom W Y ω) s) ω i - Y 0 ω i| ≤ 2 * R := by
  rcases (stopped_path_mem_closure hW hY s).2 with h | ⟨h1, h2⟩
  · rw [h, sub_self, abs_zero]; linarith
  · have a1 := (norm_le_pi_norm (Y (stopTime (exitTimeFrom W Y ω) s) ω) i).trans (hRW _ h1)
    have a2 := (norm_le_pi_norm (Y 0 ω) i).trans (hRW _ h2)
    rw [Real.norm_eq_abs] at a1 a2
    calc _ ≤ |Y (stopTime (exitTimeFrom W Y ω) s) ω i| + |Y 0 ω i| := abs_sub _ _
      _ ≤ 2 * R := by linarith

omit [MeasurableSpace Ω] in
/-- Bound for the compensated coordinate up to the exit. -/
theorem abs_smCompensated_stop_le {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {b : (Fin d → ℝ) → Fin d → ℝ}
    {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B) (hRW : ∀ y ∈ closure W, ‖y‖ ≤ R)
    (hBW : ∀ y ∈ closure W, ‖b y‖ ≤ B) {t s : ℝ≥0} (hs : s ≤ t) (i : Fin d) :
    |smCompensated Y (fun t ω => b (Y t ω)) i (stopTime (exitTimeFrom W Y ω) s) ω| ≤
      2 * R + B * t := by
  have h1 := abs_sub_stop_le hW hY hR hRW s i
  have h2 := abs_integral_stop_le hW hY (g := fun y => b y i) hB
    (fun y hy => by rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm (b y) i).trans (hBW y hy)) hs
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- **Bridge semimartingale ⇒ martingale problem.** A continuous semimartingale with
characteristics `(b(Y), a(Y))`, `b, a` continuous on the open set `U`, solves the `(b, a)`
martingale problem in `U` (`IsMPSolutionOn`, localized by exits from relatively compact
subdomains). -/
theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.isMPSolutionOn
    {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {U : Set (Fin d → ℝ)} (hb : ContinuousOn b U) (ha : ContinuousOn a U)
    {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y (fun t ω => b (Y t ω)) (fun t ω => a (Y t ω))) :
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
  have hcomp : ∀ᵐ ω ∂Q, ∀ i, Continuous fun t => smCompensated Y (fun t ω => b (Y t ω)) i t ω := by
    filter_upwards [H.continuous, H.integrable] with ω hω hi i
    exact continuous_smCompensated hω fun t => (hi t).1 i
  have bounds : ∀ W, IsInteriorDomain W U → ∃ R B : ℝ, 0 ≤ R ∧ 0 ≤ B ∧
      (∀ y ∈ closure W, ‖y‖ ≤ R) ∧ ∀ y ∈ closure W, ‖b y‖ ≤ B := fun W hW => by
    obtain ⟨R, hR⟩ := hW.2.1.exists_bound_of_continuousOn continuousOn_id
    obtain ⟨B, hB⟩ := hW.2.1.exists_bound_of_continuousOn (hb.mono hW.2.2)
    exact ⟨max R 0, max B 0, le_max_right _ _, le_max_right _ _,
      fun y hy => (hR y hy).trans (le_max_left _ _), fun y hy => (hB y hy).trans (le_max_left _ _)⟩
  refine ⟨H.adapted, H.continuous, fun W hW i => ?_, fun W hW i j => ?_⟩
  · obtain ⟨R, B, hR, hB, hRW, hBW⟩ := bounds W hW
    refine key W hW (mpCompensated b Y i) (fun n => (hmart n).1 i) (hcomp.mono fun _ h => h i)
      fun t => ⟨2 * R + B * t, ?_⟩
    filter_upwards [H.continuous] with ω hω s hs
    exact abs_smCompensated_stop_le hW.1 hω hR hB hRW hBW hs i
  · obtain ⟨R, B, hR, hB, hRW, hBW⟩ := bounds W hW
    obtain ⟨A, hA⟩ := hW.2.1.exists_bound_of_continuousOn
      (((continuous_apply j).comp (continuous_apply i)).comp_continuousOn (ha.mono hW.2.2))
    refine key W hW _ (fun n => (hmart n).2 i j) ?_
      fun t => ⟨(2 * R + B * t) * (2 * R + B * t) + max A 0 * t, ?_⟩
    · filter_upwards [hcomp, H.integrable] with ω h1 h2
      exact ((h1 i).mul (h1 j)).sub
        (continuous_setIntegral_Ioc (g := fun u => a (Y u ω) i j) fun t => (h2 t).2 i j)
    · filter_upwards [H.continuous] with ω hω s hs
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
          exact add_le_add (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)) hz

end BlockBand.SourceProcess.Stochastic.Bridges
