module

public import BlockBand.Transmission.LawDuality.GridForward

/-!
# Duality strip, after `τ`: the stopped forward steps telescope

After the stopping time `τ` the dual point is fixed, so the forward steps telescope; their
contribution to the strip is at most `2η P'(τ ≤ t − a₀)` (`abs_integral_post_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

theorem clampT_max_left {a0 t : ℝ} (hat : a0 ≤ t) (x : ℝ) :
    clampT a0 t (max a0 x) = clampT a0 t x := by
  unfold clampT
  rcases le_total a0 x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, min_eq_left hat, max_self,
      max_eq_left ((min_le_left x t).trans h)]

theorem ratioStop_eq_of_tau_le {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {τ : Ω → WithTop ℝ≥0} (ν : FiniteMeasure unitInterval) {ω : Ω} {T : ℝ≥0} (hT : τ ω = T)
    {r : ℝ} (hr : (T : ℝ) ≤ r) : ratioStop ν N X Y τ r ω = ratioStop ν N X Y τ T ω := by
  have h1 : stopAt τ r.toNNReal ω = T := by
    unfold stopAt; rw [hT, ← WithTop.coe_min, min_eq_right (Real.le_toNNReal_iff_coe_le
      (T.coe_nonneg.trans hr) |>.2 hr)]; rfl
  have h2 : stopAt τ (T : ℝ).toNNReal ω = T := by
    unfold stopAt; rw [hT, Real.toNNReal_coe, min_self]; rfl
  unfold ratioStop; rw [h1, h2]

theorem killFac_eq_of_tau_le {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)) {k : ℝ → ℝ}
    (hk : Continuous k) {T : ℝ≥0} (hT : τ ω = T) {r : ℝ} (hr : (T : ℝ) ≤ r) :
    killFac k N X Y τ r ω = killFac k N X Y τ T ω := by
  unfold killFac killExp
  rw [max_eq_left (T.coe_nonneg.trans hr), max_eq_left T.coe_nonneg,
    ← intervalIntegral.integral_add_adjacent_intervals (b := (T : ℝ))
      (intervalIntegrable_killRate (continuous_killRate hP hk) _ _ _)
      (intervalIntegrable_killRate (continuous_killRate hP hk) _ _ _)]
  have : ∫ v in (T : ℝ)..r, killRate k N X Y ω v * killInd (τ ω) v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun v hv => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hr] at hv
    have : ¬ ((v.toNNReal : WithTop ℝ≥0) < τ ω) := by
      rw [hT, WithTop.coe_lt_coe, not_lt]
      exact (Real.le_toNNReal_iff_coe_le (T.coe_nonneg.trans hv.1)).2 hv.1
    simp only [killInd, this, ↓reduceIte, mul_zero]
  rw [this, add_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : ℝ → Ω → FiniteMeasure unitInterval}
  {Ω' : Type*} [m' : MeasurableSpace Ω'] {P' : Measure Ω'} {𝓖 : Filtration ℝ≥0 m'} {D0 : ℝ}
  {p : ℕ} {x y : Fin p → ℝ} {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ}
  (h : IsDualDeletionProcess P' 𝓖 D0 x y N X Y)
  (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
  {τ : Ω' → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
  {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v)
  (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hcont : ∀ ω, ContinuousOn (fun t => μ t ω) (Ioi 0))
  {a0 t : ℝ} (ha0 : 0 < a0)

include h hpath hτ hmeas hcont ha0 in
theorem measurable_ratioAvg :
    Measurable fun q : (ℝ × ℝ) × Ω' => ratioAvg P μ a0 t N X Y τ q.1.1 q.1.2 q.2 :=
  (((measurable_ratioStop_joint h hpath hτ).comp
    (f := fun z : Ω × ((ℝ × ℝ) × Ω') => (μ (clampT a0 t z.2.1.1) z.1, (z.2.1.2, z.2.2)))
    (((measurable_muClamp hmeas hcont ha0).comp (f := fun z : Ω × ((ℝ × ℝ) × Ω') =>
      (z.2.1.1, z.1)) ((measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
        measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))).stronglyMeasurable.integral_prod_left'
    (μ := P)).measurable

omit m' in
include hpath in
theorem abs_ratioAvg_le (s r : ℝ) (ω' : Ω') : |ratioAvg P μ a0 t N X Y τ s r ω'| ≤ 1 := by
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun ω => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact abs_pathRatio_le (hpath ω') _ _

include hτ in
theorem measurable_killInd_joint :
    Measurable fun q : ℝ × Ω' => killInd (τ q.2) q.1 :=
  measurable_uncurry_rightCont (u := fun s ω => stopInd τ s ω)
    (fun s => (measurable_stopInd hτ s).mono (𝓖.le _) le_rfl) fun ω s => tendsto_stopInd_right τ ω s

/-- The post-`τ` integrand of the forward strip steps. -/
def postInteg (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) (a0 t η : ℝ)
    (k : ℝ → ℝ) (N : ℝ≥0 → Ω' → ℕ) (X Y : ℝ≥0 → Ω' → ℕ → ℝ) (τ : Ω' → WithTop ℝ≥0) (r : ℝ)
    (ω' : Ω') : ℝ :=
  (1 - killInd (τ ω') r) * ((ratioAvg P μ a0 t N X Y τ (t - r) r ω' -
    ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω') * killFac k N X Y τ r ω')

include h hpath hτ hk hk0 hmeas hcont ha0 in
/-- Pathwise: `|∫_0^{t−a₀} post| ≤ 2η·1{τ ≤ t − a₀}`. -/
theorem abs_integral_postInteg_le (hat : a0 ≤ t) {η : ℝ} (hη : 0 ≤ η) (ω' : Ω') :
    |∫ r in (0 : ℝ)..t - a0, postInteg P μ a0 t η k N X Y τ r ω'| ≤
      2 * η * {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)}.indicator 1 ω' := by
  have hL : 0 ≤ t - a0 := by linarith
  by_cases hτL : τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)
  · rw [indicator_of_mem (show ω' ∈ {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} from hτL),
      Pi.one_apply, mul_one]
    obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hτL)
    replace hT := hT.symm
    set g : ℝ → ℝ := fun s => ratioAvg P μ a0 t N X Y τ s T ω' with hgdef
    have hg : Measurable g := (measurable_ratioAvg h hpath hτ hmeas hcont ha0).comp
      (f := fun s => ((s, (T : ℝ)), ω')) ((measurable_id.prodMk measurable_const).prodMk
        measurable_const)
    have hg1 : ∀ s, |g s| ≤ 1 := fun s => abs_ratioAvg_le hpath s T ω'
    have e : ∀ r ∈ uIcc 0 (t - a0), postInteg P μ a0 t η k N X Y τ r ω' =
        killFac k N X Y τ T ω' * (if (T : ℝ) ≤ r then g (t - r) - g (t - η - r) else 0) := by
      intro r hr
      rw [uIcc_of_le hL] at hr
      unfold postInteg
      by_cases hTr : (T : ℝ) ≤ r
      · have hki : killInd (τ ω') r = 0 := ite_eq_right_iff.2 fun h' => by
          rw [hT, WithTop.coe_lt_coe] at h'
          exact absurd ((Real.le_toNNReal_iff_coe_le hr.1).2 hTr) (not_le.2 h')
        have hR : ∀ s, ratioAvg P μ a0 t N X Y τ s r ω' = g s := fun s =>
          integral_congr_ae (ae_of_all _ fun ω => ratioStop_eq_of_tau_le _ hT hTr)
        have hgm : g (max a0 (t - η - r)) = g (t - η - r) := by
          simp only [hgdef, ratioAvg, clampT_max_left hat]
        rw [hki, hR, hR, hgm, killFac_eq_of_tau_le (hpath ω') hk hT hTr]
        simp only [hTr, ↓reduceIte]; ring
      · have hlt : (r.toNNReal : WithTop ℝ≥0) < τ ω' := by
          rw [hT]; exact WithTop.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe hr.1).2 (not_le.1 hTr))
        have hki : killInd (τ ω') r = 1 := ite_eq_left_iff.2 fun h' => absurd hlt h'
        rw [hki]; simp only [hTr, ↓reduceIte]; ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul, abs_mul]
    have hK := killFac_mem (τ := τ) (hpath ω') hk0 (T : ℝ)
    rw [abs_of_pos hK.1]
    calc _ ≤ 1 * (2 * η) := mul_le_mul hK.2 (abs_integral_shift_le hg hg1 T.coe_nonneg hL hη)
          (abs_nonneg _) zero_le_one
      _ = 2 * η := one_mul _
  · rw [indicator_of_notMem (show ω' ∉ {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} from hτL),
      mul_zero]
    have : ∀ r ∈ uIcc 0 (t - a0), postInteg P μ a0 t η k N X Y τ r ω' = 0 := by
      intro r hr
      rw [uIcc_of_le hL] at hr
      have hlt : (r.toNNReal : WithTop ℝ≥0) < τ ω' := lt_of_le_of_lt
        (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr.2)) (not_le.1 hτL)
      have hki : killInd (τ ω') r = 1 := ite_eq_left_iff.2 fun h' => absurd hlt h'
      unfold postInteg; rw [hki]; ring
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_zero, abs_zero]

include h hpath hτ hk hmeas hcont ha0 in
theorem measurable_postInteg (η : ℝ) :
    Measurable fun q : ℝ × Ω' => postInteg P μ a0 t η k N X Y τ q.1 q.2 := by
  have hR := measurable_ratioAvg (P := P) (t := t) h hpath hτ hmeas hcont ha0
  exact (measurable_const.sub (measurable_killInd_joint hτ)).mul
    ((((hR.comp (f := fun q : ℝ × Ω' => ((t - q.1, q.1), q.2))
      (((measurable_const.sub measurable_fst).prodMk measurable_fst).prodMk measurable_snd)).sub
      (hR.comp (f := fun q : ℝ × Ω' => ((max a0 (t - η - q.1), q.1), q.2))
        (((measurable_const.max (measurable_const.sub measurable_fst)).prodMk
          measurable_fst).prodMk measurable_snd))).mul
      (measurable_killFac_joint h hpath hτ hk)))

omit m' in
include hpath hk0 in
theorem abs_postInteg_le (η r : ℝ) (ω' : Ω') : |postInteg P μ a0 t η k N X Y τ r ω'| ≤ 2 := by
  unfold postInteg
  have hK := killFac_mem (τ := τ) (hpath ω') hk0 r
  have hI := killInd_mem (τ ω') r
  have h1 := abs_ratioAvg_le (P := P) (μ := μ) (a0 := a0) (t := t) (τ := τ) hpath (t - r) r ω'
  have h2 := abs_ratioAvg_le (P := P) (μ := μ) (a0 := a0) (t := t) (τ := τ) hpath
    (max a0 (t - η - r)) r ω'
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hI.2] : (0 : ℝ) ≤ 1 - killInd (τ ω') r),
    abs_of_pos hK.1]
  have h3 := abs_sub (ratioAvg P μ a0 t N X Y τ (t - r) r ω')
    (ratioAvg P μ a0 t N X Y τ (max a0 (t - η - r)) r ω')
  calc _ ≤ 1 * (2 * 1) := mul_le_mul (by linarith [hI.1]) (mul_le_mul (by linarith) hK.2
        hK.1.le (by norm_num)) (mul_nonneg (abs_nonneg _) hK.1.le) zero_le_one
    _ = 2 := by norm_num

include h hpath hτ hk hk0 hmeas hcont ha0 in
/-- **The post-`τ` forward steps are `≤ 2η P'(τ ≤ t − a₀)`.** -/
theorem abs_integral_post_le (hat : a0 ≤ t) {η : ℝ} (hη : 0 ≤ η) :
    |∫ r in (0 : ℝ)..t - a0, (∫ ω', postInteg P μ a0 t η k N X Y τ r ω' ∂P')| ≤
      2 * η * P'.real {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)} := by
  have := h.prob
  have hL : 0 ≤ t - a0 := by linarith
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (t - a0))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set S := {ω' | τ ω' ≤ ((t - a0).toNNReal : WithTop ℝ≥0)}
  have hS : MeasurableSet S := 𝓖.le _ _ (hτ (t - a0).toNNReal)
  have hm := measurable_postInteg (P := P) (t := t) h hpath hτ hk hmeas hcont ha0 η
  have hi : Integrable (Function.uncurry fun r ω' => postInteg P μ a0 t η k N X Y τ r ω')
      ((volume.restrict (Ioc (0 : ℝ) (t - a0))).prod P') :=
    Integrable.of_bound hm.aestronglyMeasurable 2 (ae_of_all _ fun q => by
      rw [Real.norm_eq_abs]; exact abs_postInteg_le hpath hk0 η q.1 q.2)
  rw [intervalIntegral.integral_of_le hL, integral_integral_swap hi, ← Real.norm_eq_abs]
  have hg : Integrable (fun ω' => 2 * η * S.indicator 1 ω') P' :=
    ((integrable_const (1 : ℝ)).indicator hS).const_mul _
  refine (norm_integral_le_of_norm_le hg (ae_of_all _ fun ω' => ?_)).trans ?_
  · rw [Real.norm_eq_abs, ← intervalIntegral.integral_of_le hL]
    exact abs_integral_postInteg_le h hpath hτ hk hk0 hmeas hcont ha0 hat hη ω'
  · rw [integral_const_mul, integral_indicator_one hS]

end BlockBand.Transmission.LawDuality
