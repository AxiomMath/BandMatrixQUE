module

public import BlockBand.Diffusion.Heat.Corner

/-!
# The corner heat identity: proof

`ch_cornerHeatIdentity`: `ChLbkCornerHeatIdentity D0` for every `D₀ > 0`; also `ch_excessive`:
`P_tH ≤ H` on the strip off the corner.

Proof. Write `L_s = ∫⁻ p_s(z,·)H` and `K(s) = p_s(z, (0,0))`.
1. (`ch_tendsto_lint`) `H_n = chHL (n+1) ↑ H` off the corner (closed form `(1 - e^{-(n+1)σ})/σ`,
   `σ = x' + y' > 0`), so `ofReal (P_sH_n(z)) → L_s` by monotone convergence.
2. (`ch_lint_le`) The finite-cutoff identity `ch_chP_chHL` gives `P_sH_n ≤ H_n ≤ H`, so
   `L_s ≤ H(z)` (excessiveness).
3. (`ch_lint_sub`) For `0 < δ ≤ t`, the finite-cutoff identities at `δ` and `t` give
   `P_δH_n(z) = P_tH_n(z) + (D₀/2)∫_{(δ,t]} P_uφ_{n+1}(z) du`; as `n → ∞`
   (`ch_tendsto_setIntegral_chPhi`, dominated convergence for `u ≥ δ`):
   `L_δ = L_t + (D₀/2)∫⁻_{(δ,t]} K`.
4. (`ch_lint_tendsto`) `L_δ → H(z)` as `δ → 0+`: `≤` by step 2; `≥` since `L_δ ≥ P_δH_m(z) →
   H_m(z)` (approximate identity `ch_tendsto_chP`, from path continuity) and `H_m(z) ↑ H(z)`.
5. `∫⁻_{(δ,t]} K ↑ ∫⁻_{(0,t]} K` (continuity from below); pass to the limit in step 3.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### The cutoffs `H_L`
-/

theorem ch_continuous_chExp_l (w : ℝ × ℝ) : Continuous fun l => chExp l w := by
  unfold chExp; fun_prop

theorem ch_chHL_eq (L : ℝ) {w : ℝ × ℝ} (hs : 0 < w.1 + w.2) :
    chHL L w = (1 - Real.exp (-(L * (w.1 + w.2)))) / (w.1 + w.2) := by
  have hs' : w.1 + w.2 ≠ 0 := hs.ne'
  have hd : ∀ l : ℝ, HasDerivAt (fun l => -Real.exp (-(l * (w.1 + w.2))) / (w.1 + w.2))
      (chExp l w) l := fun l => by
    have h1 : HasDerivAt (fun l => -(l * (w.1 + w.2))) (-(w.1 + w.2)) l :=
      (hasDerivAt_mul_const (-(w.1 + w.2))).congr_of_eventuallyEq
        (Eventually.of_forall fun y => by ring)
    refine (h1.exp.neg.div_const (w.1 + w.2)).congr_deriv ?_
    simp only [chExp]
    field_simp
  unfold chHL
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun l _ => hd l)
    ((ch_continuous_chExp_l w).intervalIntegrable _ _)]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  field_simp
  ring

theorem ch_chHL_nonneg {L : ℝ} (hL : 0 ≤ L) (w : ℝ × ℝ) : 0 ≤ chHL L w :=
  intervalIntegral.integral_nonneg hL fun _ _ => (Real.exp_pos _).le

theorem ch_abs_chHL_le {L : ℝ} (hL : 0 ≤ L) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    |chHL L w| ≤ L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L) (C := 1)
    (f := fun l => chExp l w) fun l hl => by
      rw [uIoc_of_le hL] at hl
      rw [Real.norm_eq_abs]; exact ch_abs_chExp_le hl.1.le hw
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hL, one_mul] at h
  exact h

theorem ch_continuous_chHL (L : ℝ) : Continuous (chHL L) := by
  have hc : Continuous (Function.uncurry fun (w : ℝ × ℝ) (l : ℝ) => chExp l w) := by
    unfold Function.uncurry chExp; fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hc continuous_const

theorem ch_pos_of_mem {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) (hw0 : w ≠ (0, 0)) :
    0 < w.1 + w.2 := by
  have hx : 0 ≤ w.1 := hw.1
  have hy : 0 ≤ w.2 := hw.2.1
  by_contra hn
  exact hw0 (Prod.ext (by simp only; linarith) (by simp only; linarith))

/-- `H_{n+1} ↑ H` off the corner. -/
theorem ch_chHL_mono_tendsto {w : ℝ × ℝ} (hs : 0 < w.1 + w.2) :
    Monotone (fun n : ℕ => ENNReal.ofReal (chHL ((n : ℝ) + 1) w)) ∧
      Tendsto (fun n : ℕ => ENNReal.ofReal (chHL ((n : ℝ) + 1) w)) atTop
        (𝓝 (ENNReal.ofReal (chHarm w))) ∧
      ∀ L : ℝ, chHL L w ≤ chHarm w := by
  set σ := w.1 + w.2 with hσ
  refine ⟨fun a b hab => ENNReal.ofReal_le_ofReal ?_, ENNReal.tendsto_ofReal ?_, fun L => ?_⟩
  · rw [ch_chHL_eq _ hs, ch_chHL_eq _ hs]
    refine div_le_div_of_nonneg_right ?_ hs.le
    have : ((a : ℝ) + 1) * σ ≤ ((b : ℝ) + 1) * σ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hab 1) hs.le
    have := Real.exp_le_exp.2 (neg_le_neg this)
    linarith
  · simp_rw [ch_chHL_eq _ hs]
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * σ) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hs
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    have h3 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2 |>.div_const σ
    simp only [sub_zero] at h3
    rw [chHarm, ← hσ, inv_eq_one_div]
    exact h3
  · rcases lt_or_ge L 0 with hL | hL
    · have : chHL L w ≤ 0 := by
        unfold chHL
        rw [intervalIntegral.integral_symm]
        have := intervalIntegral.integral_nonneg (μ := volume) hL.le
          (f := fun l => chExp l w) fun l _ => (Real.exp_pos _).le
        linarith
      exact this.trans (inv_nonneg.2 hs.le)
    · rw [ch_chHL_eq _ hs, chHarm, ← hσ, inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-(L * σ))]) hs.le

/-!
### The approximate corner delta on the strip
-/

theorem ch_chPhi_nonneg (L : ℝ) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) : 0 ≤ chPhi L w := by
  have : 0 ≤ 1 + w.1 - w.2 := by linarith [hw.1.out, hw.2.2]
  unfold chPhi; positivity

theorem ch_abs_chPhi_le {L : ℝ} (hL : 0 < L) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) :
    |chPhi L w| ≤ L ^ 2 * (2 + 4 / L ^ 2) := by
  have hx : 0 ≤ w.1 := hw.1
  have hy0 : 0 ≤ w.2 := hw.2.1
  rw [abs_of_nonneg (ch_chPhi_nonneg L hw), chPhi]
  have h := ch_sq_mul_exp_le hL hx
  have e : Real.exp (-(L * (w.1 + w.2))) = Real.exp (-(L * w.1)) * Real.exp (-(L * w.2)) := by
    rw [← Real.exp_add]; ring_nf
  have hey : Real.exp (-(L * w.2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hex := Real.exp_pos (-(L * w.1))
  have hey0 := Real.exp_pos (-(L * w.2))
  rw [e]
  have h1 : 1 + w.1 - w.2 ≤ (1 + w.1) ^ 2 := by nlinarith
  have h0 : 0 ≤ 1 + w.1 - w.2 := by linarith [hw.2.2]
  calc L ^ 2 * (1 + w.1 - w.2) * (Real.exp (-(L * w.1)) * Real.exp (-(L * w.2)))
      ≤ L ^ 2 * ((1 + w.1) ^ 2 * Real.exp (-(L * w.1))) * 1 := by
        rw [show L ^ 2 * (1 + w.1 - w.2) * (Real.exp (-(L * w.1)) * Real.exp (-(L * w.2))) =
          L ^ 2 * ((1 + w.1 - w.2) * Real.exp (-(L * w.1))) * Real.exp (-(L * w.2)) by ring]
        gcongr
    _ ≤ L ^ 2 * (2 + 4 / L ^ 2) := by rw [mul_one]; gcongr

theorem ch_intervalIntegrable_chP_chPhi {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    IntervalIntegrable (fun u => chP D0 u (chPhi L) z) volume a b := by
  have hm : Measurable fun q : ℝ × (ℝ × ℝ) => chPhi L q.2 :=
    (ch_measurable_chPhi L).comp measurable_snd
  have hsm := ch_stronglyMeasurable_chP hD0 (F := fun _ : ℝ => chPhi L) hm measurable_id z
  have hC : 0 ≤ L ^ 2 * (2 + 4 / L ^ 2) := by positivity
  refine (intervalIntegrable_iff).2 ?_
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, uIoc]; exact measure_Ioc_lt_top⟩
  exact Integrable.of_bound hsm.aestronglyMeasurable _ (ae_of_all _ fun u => by
    rw [Real.norm_eq_abs]; exact ch_abs_chP_le hD0 u hz hC fun w hw => ch_abs_chPhi_le hL hw)

/-- The finite-cutoff identity between two positive times. -/
theorem ch_chP_chHL_sub {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) {L : ℝ} (hL : 0 < L) :
    chP D0 δ (chHL L) z =
      chP D0 t (chHL L) z + D0 / 2 * ∫ u in Ioc δ t, chP D0 u (chPhi L) z := by
  rw [ch_chP_chHL hD0 hz hδ hL, ch_chP_chHL hD0 hz (lt_of_lt_of_le hδ hδt) hL,
    ← intervalIntegral.integral_of_le hδ.le, ← intervalIntegral.integral_of_le (hδ.le.trans hδt),
    ← intervalIntegral.integral_of_le hδt,
    ← intervalIntegral.integral_add_adjacent_intervals
      (ch_intervalIntegrable_chP_chPhi hD0 hz hL 0 δ)
      (ch_intervalIntegrable_chP_chPhi hD0 hz hL δ t)]
  ring

/-!
### The limit `n → ∞`
-/

/-- `L_s = ∫⁻ p_s(z, ·) H`. -/
def chLt (D0 s : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ∫⁻ w', ENNReal.ofReal (exKernel D0 s z w') * ENNReal.ofReal (chHarm w')

theorem ch_ae_ne_corner : ∀ᵐ w' : ℝ × ℝ ∂volume, w' ≠ (0, 0) := by
  have h : (volume : Measure (ℝ × ℝ)) {((0 : ℝ), (0 : ℝ))} = 0 := measure_singleton _
  simpa using measure_eq_zero_iff_ae_notMem.1 h

theorem ch_tendsto_lint {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {s : ℝ}
    (hs : 0 < s) :
    Monotone (fun n : ℕ => ENNReal.ofReal (chP D0 s (chHL ((n : ℝ) + 1)) z)) ∧
      Tendsto (fun n : ℕ => ENNReal.ofReal (chP D0 s (chHL ((n : ℝ) + 1)) z)) atTop
        (𝓝 (chLt D0 s z)) := by
  have hn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) + 1 := fun n => by positivity
  have e : ∀ n : ℕ, ENNReal.ofReal (chP D0 s (chHL ((n : ℝ) + 1)) z) =
      ∫⁻ w', ENNReal.ofReal (exKernel D0 s z w') * ENNReal.ofReal (chHL ((n : ℝ) + 1) w') :=
    fun n => ch_ofReal_chP hD0 hs hz (ch_continuous_chHL _).measurable
      (fun w _ => ch_chHL_nonneg (hn n) w) (fun w hw => ch_abs_chHL_le (hn n) hw)
  simp_rw [e]
  have hpm : Measurable fun w' => ENNReal.ofReal (exKernel D0 s z w') :=
    ((exKernel_measurable hD0).comp (f := fun w' : ℝ × ℝ => (s, z, w'))
      (by fun_prop)).ennreal_ofReal
  have hae : ∀ᵐ w' : ℝ × ℝ ∂volume,
      Monotone (fun n : ℕ => ENNReal.ofReal (exKernel D0 s z w') *
        ENNReal.ofReal (chHL ((n : ℝ) + 1) w')) ∧
      Tendsto (fun n : ℕ => ENNReal.ofReal (exKernel D0 s z w') *
        ENNReal.ofReal (chHL ((n : ℝ) + 1) w')) atTop
        (𝓝 (ENNReal.ofReal (exKernel D0 s z w') * ENNReal.ofReal (chHarm w'))) := by
    filter_upwards [ch_ae_ne_corner] with w' hw'
    by_cases hp : exKernel D0 s z w' = 0
    · simp only [hp, ENNReal.ofReal_zero, zero_mul]
      exact ⟨monotone_const, tendsto_const_nhds⟩
    · obtain ⟨h1, h2, -⟩ := ch_chHL_mono_tendsto (ch_pos_of_mem (ch_mem_of_exKernel_ne_zero hp) hw')
      exact ⟨fun a b hab => mul_le_mul_of_nonneg_left (h1 hab) zero_le,
        ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)⟩
  refine ⟨fun a b hab => lintegral_mono_ae (hae.mono fun w' hw' => hw'.1 hab), ?_⟩
  exact lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hpm.mul (ch_continuous_chHL _).measurable.ennreal_ofReal).aemeasurable)
    (hae.mono fun w' hw' => hw'.1) (hae.mono fun w' hw' => hw'.2)

theorem ch_chP_chPhi_nonneg {D0 : ℝ} (hD0 : 0 < D0) (u L : ℝ) (z : ℝ × ℝ) :
    0 ≤ chP D0 u (chPhi L) z :=
  ch_chP_nonneg hD0 u z fun _ hw => ch_chPhi_nonneg L hw

/-- **Excessiveness at the level of `L_s`**: `L_s ≤ H(z)`. -/
theorem ch_lint_le {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    (hz0 : z ≠ (0, 0)) {s : ℝ} (hs : 0 < s) : chLt D0 s z ≤ ENNReal.ofReal (chHarm z) := by
  refine le_of_tendsto' (ch_tendsto_lint hD0 hz hs).2 fun n => ENNReal.ofReal_le_ofReal ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [ch_chP_chHL hD0 hz hs hn]
  have hI : 0 ≤ ∫ u in Ioc 0 s, chP D0 u (chPhi ((n : ℝ) + 1)) z :=
    setIntegral_nonneg measurableSet_Ioc fun u _ => ch_chP_chPhi_nonneg hD0 u _ z
  have hH := (ch_chHL_mono_tendsto (ch_pos_of_mem hz hz0)).2.2 ((n : ℝ) + 1)
  have : 0 ≤ D0 / 2 * ∫ u in Ioc 0 s, chP D0 u (chPhi ((n : ℝ) + 1)) z := by positivity
  linarith

theorem ch_integrableOn_corner {D0 : ℝ} (hD0 : 0 < D0) {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    (z : ℝ × ℝ) : IntegrableOn (fun s => exKernel D0 s z (0, 0)) (Ioc δ t) := by
  obtain ⟨CX, hCX⟩ := mk_kernelX_bdd_of_isCompact hD0 (isCompact_Icc : IsCompact (Icc δ t))
    (fun r hr => by rw [mem_Icc] at hr; rw [mem_Ioi]; linarith [hr.1])
  have : IsFiniteMeasure (volume.restrict (Ioc δ t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hm : Measurable fun s => exKernel D0 s z (0, 0) :=
    (exKernel_measurable hD0).comp (f := fun s : ℝ => (s, z, ((0 : ℝ), (0 : ℝ)))) (by fun_prop)
  refine Integrable.of_bound hm.aestronglyMeasurable (CX * skSupY D0 δ) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (exKernel_nonneg hD0 _ _ _), exKernel_eq]
  exact mul_le_mul (hCX s (Ioc_subset_Icc_self hs) _ _) (sk_kernelY_le hD0 hδ hs.1.le _ _)
    (sk_kernelY_nonneg hD0 _ _ _) ((mk_kernelX_nonneg hD0 _ _ _).trans (hCX s
      (Ioc_subset_Icc_self hs) z.1 0))

/-- **Step 3**: `L_δ = L_t + (D₀/2)∫⁻_{(δ,t]} p_s(z,(0,0)) ds` for `0 < δ ≤ t`. -/
theorem ch_lint_sub {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {δ t : ℝ}
    (hδ : 0 < δ) (hδt : δ ≤ t) :
    chLt D0 δ z = chLt D0 t z + ENNReal.ofReal (D0 / 2) *
      ∫⁻ s in Ioc δ t, ENNReal.ofReal (exKernel D0 s z (0, 0)) := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hc : 0 ≤ D0 / 2 := by positivity
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have e : ∀ n : ℕ, ENNReal.ofReal (chP D0 δ (chHL ((n : ℝ) + 1)) z) =
      ENNReal.ofReal (chP D0 t (chHL ((n : ℝ) + 1)) z) + ENNReal.ofReal (D0 / 2) *
        ENNReal.ofReal (∫ u in Ioc δ t, chP D0 u (chPhi ((n : ℝ) + 1)) z) := fun n => by
    rw [ch_chP_chHL_sub hD0 hz hδ hδt (hn n), ENNReal.ofReal_add
      (ch_chP_nonneg hD0 t z fun w _ => ch_chHL_nonneg (hn n).le w)
      (mul_nonneg hc (setIntegral_nonneg measurableSet_Ioc fun u _ =>
        ch_chP_chPhi_nonneg hD0 u _ z)), ENNReal.ofReal_mul hc]
  have hR : Tendsto (fun n : ℕ => ENNReal.ofReal (chP D0 t (chHL ((n : ℝ) + 1)) z) +
      ENNReal.ofReal (D0 / 2) *
        ENNReal.ofReal (∫ u in Ioc δ t, chP D0 u (chPhi ((n : ℝ) + 1)) z)) atTop
      (𝓝 (chLt D0 t z + ENNReal.ofReal (D0 / 2) *
        ENNReal.ofReal (∫ s in Ioc δ t, exKernel D0 s z (0, 0)))) :=
    (ch_tendsto_lint hD0 hz ht).2.add (ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_ofReal (ch_tendsto_setIntegral_chPhi hD0 hδ t hz))
      (Or.inr ENNReal.ofReal_ne_top))
  have h := tendsto_nhds_unique (ch_tendsto_lint hD0 hz hδ).2 (hR.congr fun n => (e n).symm)
  rw [h, ofReal_integral_eq_lintegral_ofReal (ch_integrableOn_corner hD0 hδ t z)
    (ae_of_all _ fun s => exKernel_nonneg hD0 _ _ _)]

/-- **Step 4**: `L_{t/(k+2)} → H(z)`. -/
theorem ch_lint_tendsto {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    (hz0 : z ≠ (0, 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k : ℕ => chLt D0 (t / ((k : ℝ) + 2)) z) atTop
      (𝓝 (ENNReal.ofReal (chHarm z))) := by
  have hk : ∀ k : ℕ, 0 < t / ((k : ℝ) + 2) := fun k => by positivity
  have hδ : Tendsto (fun k : ℕ => t / ((k : ℝ) + 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hk⟩
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  obtain ⟨-, hHt, -⟩ := ch_chHL_mono_tendsto (ch_pos_of_mem hz hz0)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
    Eventually.of_forall fun k => lt_of_le_of_lt (ch_lint_le hD0 hz hz0 (hk k)) ha⟩
  obtain ⟨m, hm⟩ := ((tendsto_order.1 hHt).1 a ha).exists
  have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hAI := ENNReal.tendsto_ofReal ((ch_tendsto_chP hD0 hz (ch_continuous_chHL _).measurable
    (ch_continuous_chHL ((m : ℝ) + 1)).continuousOn
    (fun w hw => ch_abs_chHL_le hm0 hw)).comp hδ)
  filter_upwards [(tendsto_order.1 hAI).1 a hm] with k hk'
  exact lt_of_lt_of_le hk' ((ch_tendsto_lint hD0 hz (hk k)).1.ge_of_tendsto
    (ch_tendsto_lint hD0 hz (hk k)).2 m)

/-!
### The corner heat identity
-/

/-- **The corner heat identity** at `D₀ > 0`. -/
theorem ch_cornerHeatIdentity {D0 : ℝ} (hD0 : 0 < D0) : ChLbkCornerHeatIdentity D0 := by
  intro z hz hz0 t ht
  set K : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (exKernel D0 s z (0, 0))
  have hKm : Measurable K :=
    ((exKernel_measurable hD0).comp (f := fun s : ℝ => (s, z, ((0 : ℝ), (0 : ℝ))))
      (by fun_prop)).ennreal_ofReal
  set δ : ℕ → ℝ := fun k => t / ((k : ℝ) + 2)
  have hk : ∀ k, 0 < δ k := fun k => by positivity
  have hkt : ∀ k, δ k ≤ t := fun k =>
    div_le_self ht.le (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
  have hanti : Antitone δ := fun a b hab =>
    div_le_div_of_nonneg_left ht.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 2)
  -- continuity from below of `∫⁻_{(δ_k, t]} K`
  set ν := volume.withDensity K
  have hmono : Monotone fun k => Ioc (δ k) t := fun a b hab => Ioc_subset_Ioc_left (hanti hab)
  have hU : ⋃ k, Ioc (δ k) t = Ioc 0 t := by
    ext s
    simp only [mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨k, h1, h2⟩; exact ⟨(hk k).trans h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨k, hk'⟩ := exists_nat_gt (t / s)
      refine ⟨k, ?_, h2⟩
      show t / ((k : ℝ) + 2) < s
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ h1] at hk'
      nlinarith
  have hJ : Tendsto (fun k => ∫⁻ s in Ioc (δ k) t, K s) atTop (𝓝 (∫⁻ s in Ioc 0 t, K s)) := by
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hU] at h
    simp only [Function.comp_def, ν, withDensity_apply _ measurableSet_Ioc] at h
    exact h
  have hL := (tendsto_const_nhds (x := chLt D0 t z)).add
    (ENNReal.Tendsto.const_mul hJ (Or.inr (ENNReal.ofReal_ne_top (r := D0 / 2))))
  have h := tendsto_nhds_unique (ch_lint_tendsto hD0 hz hz0 ht)
    (hL.congr fun k => (ch_lint_sub hD0 hz (hk k) (hkt k)).symm)
  exact h.symm

/-- **The corner heat identity** `ChLbkCornerHeatIdentity D0` holds for every `D₀ > 0`. -/
theorem chLbkCornerHeatIdentity : ∀ D0 : ℝ, 0 < D0 → ChLbkCornerHeatIdentity D0 :=
  fun _ hD0 => ch_cornerHeatIdentity hD0

/-- **Excessiveness**: `P_tH(z) ≤ H(z)` for `z` in the strip off the corner, `t > 0`. -/
theorem ch_excessive {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    (hz0 : z ≠ (0, 0)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ w', ENNReal.ofReal (exKernel D0 t z w') * ENNReal.ofReal (chHarm w') ≤
      ENNReal.ofReal (chHarm z) :=
  ch_lint_le hD0 hz hz0 ht

theorem ch_lintegral_harm_lt_top {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    (hz0 : z ≠ (0, 0)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ w', ENNReal.ofReal (exKernel D0 t z w') * ENNReal.ofReal (chHarm w') < ⊤ :=
  lt_of_le_of_lt (ch_excessive hD0 hz hz0 ht) ENNReal.ofReal_lt_top

theorem ch_lintegral_corner_lt_top {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    (hz0 : z ≠ (0, 0)) {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Ioc 0 t, ENNReal.ofReal (exKernel D0 s z (0, 0)) < ⊤ := by
  have h := ch_cornerHeatIdentity hD0 z hz hz0 t ht
  have hc : ENNReal.ofReal (D0 / 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h1 : ENNReal.ofReal (D0 / 2) * ∫⁻ s in Ioc 0 t, ENNReal.ofReal (exKernel D0 s z (0, 0)) <
      ⊤ := lt_of_le_of_lt (h ▸ le_add_self) ENNReal.ofReal_lt_top
  rcases ENNReal.mul_lt_top_iff.1 h1 with ⟨-, h2⟩ | h2 | h2
  · exact h2
  · exact absurd h2 hc
  · rw [h2]; exact ENNReal.zero_lt_top

end BlockBand.Diffusion
