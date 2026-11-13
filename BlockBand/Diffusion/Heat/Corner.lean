module

public import BlockBand.Diffusion.Heat.Lambda

/-!
# The approximate corner delta: `P_s φ_L(z) → p_s(z, (0,0))`

`φ_L(x', y') = L²(1+x'-y')e^{-L(x'+y')}` splits into products of the one-dimensional weights
`a₀(u) = Le^{-Lu}`, `a₁(u) = Lue^{-Lu}`: `φ_L = a₀⊗a₀ + a₁⊗a₀ - a₀⊗a₁` (`ch_chPhi_eq`), so by the
product structure of `exKernel`, `P_sφ_L(z) = A₀B₀ + A₁B₀ - A₀B₁` with
`A_i = ∫ pX_s(x,x')a_i(x')dx'`, `B_i = ∫ pY_s(y,y')a_i(y')dy'` (`ch_chP_chPhi_eq`).

**One-dimensional boundary approximate identity** (`ch_tendsto_integral_chA0`,
`ch_abs_integral_chA1_le`): for `k` measurable, bounded by `M`, vanishing on `(-∞, 0)` and
continuous within `[0, ∞)` at `0`: `∫ k a₀ → k(0)` as `L → ∞` (substitution `x' = v/L` and
dominated convergence against `Me^{-v}`), `|∫ k a₀| ≤ M`, `|∫ k a₁| ≤ M/L`.

**Headlines.**
* `ch_tendsto_chP_chPhi`: for `s > 0`, `z ∈ exBaseStrip`,
  `P_s φ_{n+1}(z) → p_s(z, (0,0))` (`k = pX_s(x,·)`, `pY_s(y,·)`: committed continuity, bounds).
* `ch_abs_chP_chPhi_le`: `|P_s φ_L(z)| ≤ C` uniformly in `s ∈ [δ, t]`, `L ≥ 1` (committed
  on-diagonal bounds `mk_kernelX_bdd_of_isCompact`, `sk_kernelY_le`).
* `ch_tendsto_setIntegral_chPhi`: `∫_{(δ,t]} P_sφ_{n+1}(z) ds → ∫_{(δ,t]} p_s(z,(0,0)) ds`
  for `δ > 0` (dominated convergence in `s`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-- `a₀(u) = L e^{-Lu}`. -/
def chA0 (L u : ℝ) : ℝ := L * Real.exp (-(L * u))

/-- `a₁(u) = L u e^{-Lu}`. -/
def chA1 (L u : ℝ) : ℝ := L * u * Real.exp (-(L * u))

theorem ch_chPhi_eq (L : ℝ) (w : ℝ × ℝ) :
    chPhi L w = chA0 L w.1 * chA0 L w.2 + chA1 L w.1 * chA0 L w.2 - chA0 L w.1 * chA1 L w.2 := by
  unfold chPhi chA0 chA1
  rw [show -(L * (w.1 + w.2)) = -(L * w.1) + -(L * w.2) by ring, Real.exp_add]
  ring

theorem ch_measurable_chA0 (L : ℝ) : Measurable (chA0 L) := by unfold chA0; fun_prop
theorem ch_measurable_chA1 (L : ℝ) : Measurable (chA1 L) := by unfold chA1; fun_prop

theorem ch_abs_chA0_le {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) : |chA0 L u| ≤ L := by
  unfold chA0
  rw [abs_of_pos (by positivity)]
  have : Real.exp (-(L * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  nlinarith

theorem ch_abs_chA1_le {L u : ℝ} (hL : 0 < L) (hu : 0 ≤ u) : |chA1 L u| ≤ 1 := by
  unfold chA1
  have hv : 0 ≤ L * u := mul_nonneg hL.le hu
  rw [abs_of_nonneg (by positivity), Real.exp_neg, ← div_eq_mul_inv,
    div_le_one (Real.exp_pos _)]
  linarith [Real.add_one_le_exp (L * u)]

/-!
### One-dimensional boundary approximate identity
-/

section OneDim

variable {k : ℝ → ℝ} {M : ℝ}

theorem ch_integrable_mul_of_zero {a : ℝ → ℝ} (hk : Integrable k) (hk0 : ∀ x < 0, k x = 0)
    (ha : Measurable a) {C : ℝ} (haC : ∀ x, 0 ≤ x → |a x| ≤ C) :
    Integrable fun x => k x * a x := by
  refine (hk.norm.mul_const C).mono' (hk.aestronglyMeasurable.mul ha.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  rcases lt_or_ge x 0 with hx | hx
  · simp [hk0 x hx]
  · exact mul_le_mul_of_nonneg_left (haC x hx) (abs_nonneg _)

theorem ch_integral_eq_Ioi (hk0 : ∀ x < 0, k x = 0) (a : ℝ → ℝ) :
    ∫ x, k x * a x = ∫ x in Ioi 0, k x * a x := by
  rw [← integral_Ici_eq_integral_Ioi, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp [hk0 x (not_le.1 hx)]

theorem ch_integral_chA0_eq (hk0 : ∀ x < 0, k x = 0) {L : ℝ} (hL : 0 < L) :
    ∫ x, k x * chA0 L x = ∫ v in Ioi 0, k (v / L) * Real.exp (-v) := by
  rw [ch_integral_eq_Ioi hk0]
  have h := integral_comp_mul_left_Ioi (fun v => k (v / L) * Real.exp (-v)) 0 hL
  simp only [mul_zero, smul_eq_mul] at h
  have e : ∀ x, k (L * x / L) * Real.exp (-(L * x)) = L⁻¹ * (k x * chA0 L x) := fun x => by
    rw [mul_div_cancel_left₀ _ hL.ne', chA0]
    field_simp
  simp_rw [e] at h
  rw [integral_const_mul] at h
  exact mul_left_cancel₀ (inv_ne_zero hL.ne') h

theorem ch_integral_chA1_eq (hk0 : ∀ x < 0, k x = 0) {L : ℝ} (hL : 0 < L) :
    ∫ x, k x * chA1 L x = L⁻¹ * ∫ v in Ioi 0, k (v / L) * (v * Real.exp (-v)) := by
  rw [ch_integral_eq_Ioi hk0]
  have h := integral_comp_mul_left_Ioi (fun v => k (v / L) * (v * Real.exp (-v))) 0 hL
  simp only [mul_zero, smul_eq_mul] at h
  have e : ∀ x, k (L * x / L) * (L * x * Real.exp (-(L * x))) = k x * chA1 L x := fun x => by
    rw [mul_div_cancel_left₀ _ hL.ne', chA1]
  simp_rw [e] at h
  exact h

theorem ch_integrableOn_exp_neg : IntegrableOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
  simpa using exp_neg_integrableOn_Ioi 0 (one_pos : (0 : ℝ) < 1)

theorem ch_integral_mul_exp_neg : ∫ v in Ioi (0 : ℝ), v * Real.exp (-v) = 1 := by
  rw [← Real.Gamma_two, Real.Gamma_eq_integral (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  norm_num [mul_comm]

theorem ch_integrableOn_mul_exp_neg : IntegrableOn (fun v : ℝ => v * Real.exp (-v)) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)).congr_fun (fun v _ => ?_)
    measurableSet_Ioi
  norm_num [mul_comm]

theorem ch_abs_integral_chA0_le (hk0 : ∀ x < 0, k x = 0)
    (hM : ∀ x, |k x| ≤ M) {L : ℝ} (hL : 0 < L) : |∫ x, k x * chA0 L x| ≤ M := by
  rw [ch_integral_chA0_eq hk0 hL]
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0))
    (f := fun v => k (v / L) * Real.exp (-v)) (ch_integrableOn_exp_neg.const_mul M)
    (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le)
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one, Real.norm_eq_abs] at h
  exact h

theorem ch_abs_integral_chA1_le (hk0 : ∀ x < 0, k x = 0)
    (hM : ∀ x, |k x| ≤ M) {L : ℝ} (hL : 0 < L) : |∫ x, k x * chA1 L x| ≤ L⁻¹ * M := by
  rw [ch_integral_chA1_eq hk0 hL, abs_mul, abs_of_pos (inv_pos.2 hL)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hL).le
  have h := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi 0))
    (f := fun v => k (v / L) * (v * Real.exp (-v))) (ch_integrableOn_mul_exp_neg.const_mul M)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : 0 ≤ v * Real.exp (-v) := mul_nonneg (le_of_lt hv) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv']
      exact mul_le_mul_of_nonneg_right (hM _) hv')
  rw [integral_const_mul, ch_integral_mul_exp_neg, mul_one, Real.norm_eq_abs] at h
  exact h

theorem ch_tendsto_integral_chA0 (hk : Measurable k) (hk0 : ∀ x < 0, k x = 0)
    (hkc : ContinuousWithinAt k (Ici 0) 0) (hM : ∀ x, |k x| ≤ M) :
    Tendsto (fun n : ℕ => ∫ x, k x * chA0 ((n : ℝ) + 1) x) atTop (𝓝 (k 0)) := by
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  simp_rw [ch_integral_chA0_eq hk0 (hn _)]
  have hlim : ∫ v in Ioi (0 : ℝ), k 0 * Real.exp (-v) = k 0 := by
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun v => M * Real.exp (-v))
    (fun n => ((hk.comp (measurable_id.div_const _)).mul
      (by fun_prop : Measurable fun v : ℝ => Real.exp (-v))).aestronglyMeasurable)
    (ch_integrableOn_exp_neg.const_mul M) (fun n => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hM _) (Real.exp_pos _).le) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  refine Tendsto.mul_const _ ?_
  have h1 : Tendsto (fun n : ℕ => v / ((n : ℝ) + 1)) atTop (𝓝[Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul v
      simpa [div_eq_mul_inv] using this
    · exact div_nonneg (le_of_lt hv) (hn n).le
  exact hkc.tendsto.comp h1

end OneDim

/-!
### The product decomposition of `P_s φ_L`
-/

theorem ch_kX_props {D0 : ℝ} (hD0 : 0 < D0) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Measurable (mkKernelX D0 s x) ∧ (∀ x' < 0, mkKernelX D0 s x x' = 0) ∧
      ContinuousWithinAt (mkKernelX D0 s x) (Ici 0) 0 := by
  refine ⟨mk_kernelX_measurable_snd D0 s x, fun x' hx' => ?_,
    mk_kernelX_continuousOn hD0 hs x 0 (mem_Ici.2 le_rfl)⟩
  simp [mkKernelX, not_le.2 hx']

theorem ch_kY_props {D0 : ℝ} (hD0 : 0 < D0) {s : ℝ} (hs : 0 < s) {y : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) :
    Measurable (skKernelY D0 s y) ∧ (∀ y' < 0, skKernelY D0 s y y' = 0) ∧
      ContinuousWithinAt (skKernelY D0 s y) (Ici 0) 0 := by
  refine ⟨sk_kernelY_measurable_right hD0 s y, fun y' hy' => ?_, ?_⟩
  · exact sk_kernelY_of_notMem_right _ fun h => by linarith [h.1]
  · exact (sk_kernelY_continuousOn hD0 hs hy 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE zero_lt_one)

/-- `P_s φ_L(z) = A₀B₀ + A₁B₀ - A₀B₁`. -/
theorem ch_chP_chPhi_eq {D0 : ℝ} (hD0 : 0 < D0) {s : ℝ} (hs : 0 < s) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) {L : ℝ} (hL : 0 < L) :
    chP D0 s (chPhi L) z =
      (∫ x', mkKernelX D0 s z.1 x' * chA0 L x') * (∫ y', skKernelY D0 s z.2 y' * chA0 L y') +
      (∫ x', mkKernelX D0 s z.1 x' * chA1 L x') * (∫ y', skKernelY D0 s z.2 y' * chA0 L y') -
      (∫ x', mkKernelX D0 s z.1 x' * chA0 L x') * (∫ y', skKernelY D0 s z.2 y' * chA1 L y') := by
  obtain ⟨hXm, hX0, -⟩ := ch_kX_props hD0 hs z.1
  obtain ⟨hYm, hY0, -⟩ := ch_kY_props hD0 hs hz.2
  have iX0 := ch_integrable_mul_of_zero (mk_integrable_kernelX hD0 hs hz.1) hX0
    (ch_measurable_chA0 L) fun u hu => ch_abs_chA0_le hL hu
  have iX1 := ch_integrable_mul_of_zero (mk_integrable_kernelX hD0 hs hz.1) hX0
    (ch_measurable_chA1 L) fun u hu => ch_abs_chA1_le hL hu
  have iY0 := ch_integrable_mul_of_zero (sk_integrable_kernelY hD0 s z.2) hY0
    (ch_measurable_chA0 L) fun u hu => ch_abs_chA0_le hL hu
  have iY1 := ch_integrable_mul_of_zero (sk_integrable_kernelY hD0 s z.2) hY0
    (ch_measurable_chA1 L) fun u hu => ch_abs_chA1_le hL hu
  have e : (fun w : ℝ × ℝ => exKernel D0 s z w * chPhi L w) = fun w =>
      (mkKernelX D0 s z.1 w.1 * chA0 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2) +
      (mkKernelX D0 s z.1 w.1 * chA1 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2) -
      (mkKernelX D0 s z.1 w.1 * chA0 L w.1) * (skKernelY D0 s z.2 w.2 * chA1 L w.2) := by
    funext w; rw [exKernel_eq, ch_chPhi_eq]; ring
  have j1 : Integrable (fun w : ℝ × ℝ =>
      (mkKernelX D0 s z.1 w.1 * chA0 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2))
      (volume.prod volume) := iX0.mul_prod iY0
  have j2 : Integrable (fun w : ℝ × ℝ =>
      (mkKernelX D0 s z.1 w.1 * chA1 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2))
      (volume.prod volume) := iX1.mul_prod iY0
  have j3 : Integrable (fun w : ℝ × ℝ =>
      (mkKernelX D0 s z.1 w.1 * chA0 L w.1) * (skKernelY D0 s z.2 w.2 * chA1 L w.2))
      (volume.prod volume) := iX0.mul_prod iY1
  have j12 : Integrable (fun w : ℝ × ℝ =>
      (mkKernelX D0 s z.1 w.1 * chA0 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2) +
      (mkKernelX D0 s z.1 w.1 * chA1 L w.1) * (skKernelY D0 s z.2 w.2 * chA0 L w.2))
      (volume.prod volume) := j1.add j2
  unfold chP
  rw [e, Measure.volume_eq_prod, integral_sub j12 j3, integral_add j1 j2,
    integral_prod_mul (fun x' => mkKernelX D0 s z.1 x' * chA0 L x')
      (fun y' => skKernelY D0 s z.2 y' * chA0 L y'),
    integral_prod_mul (fun x' => mkKernelX D0 s z.1 x' * chA1 L x')
      (fun y' => skKernelY D0 s z.2 y' * chA0 L y'),
    integral_prod_mul (fun x' => mkKernelX D0 s z.1 x' * chA0 L x')
      (fun y' => skKernelY D0 s z.2 y' * chA1 L y')]

/-- **The approximate corner delta**: `P_s φ_{n+1}(z) → p_s(z, (0,0))`. -/
theorem ch_tendsto_chP_chPhi {D0 : ℝ} (hD0 : 0 < D0) {s : ℝ} (hs : 0 < s) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) :
    Tendsto (fun n : ℕ => chP D0 s (chPhi ((n : ℝ) + 1)) z) atTop
      (𝓝 (exKernel D0 s z (0, 0))) := by
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  obtain ⟨hXm, hX0, hXc⟩ := ch_kX_props hD0 hs z.1
  obtain ⟨hYm, hY0, hYc⟩ := ch_kY_props hD0 hs hz.2
  obtain ⟨CX, hCX⟩ := mk_kernelX_bdd_of_isCompact hD0 (isCompact_Icc : IsCompact (Icc s s))
    (fun r hr => by rw [mem_Icc] at hr; rw [mem_Ioi]; linarith [hr.1])
  have hMX : ∀ x', |mkKernelX D0 s z.1 x'| ≤ CX := fun x' => by
    rw [abs_of_nonneg (mk_kernelX_nonneg hD0 _ _ _)]; exact hCX s ⟨le_rfl, le_rfl⟩ _ _
  have hMY : ∀ y', |skKernelY D0 s z.2 y'| ≤ skSupY D0 s := fun y' => by
    rw [abs_of_nonneg (sk_kernelY_nonneg hD0 _ _ _)]; exact sk_kernelY_le hD0 hs le_rfl _ _
  have tA0 := ch_tendsto_integral_chA0 hXm hX0 hXc hMX
  have tB0 := ch_tendsto_integral_chA0 hYm hY0 hYc hMY
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have tA1 : Tendsto (fun n : ℕ => ∫ x', mkKernelX D0 s z.1 x' * chA1 ((n : ℝ) + 1) x') atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hinv.mul_const CX)
    rw [Real.norm_eq_abs]; exact ch_abs_integral_chA1_le hX0 hMX (hn n)
  have tB1 : Tendsto (fun n : ℕ => ∫ y', skKernelY D0 s z.2 y' * chA1 ((n : ℝ) + 1) y') atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (by simpa using hinv.mul_const (skSupY D0 s))
    rw [Real.norm_eq_abs]; exact ch_abs_integral_chA1_le hY0 hMY (hn n)
  have hlim := ((tA0.mul tB0).add (tA1.mul tB0)).sub (tA0.mul tB1)
  simp only [zero_mul, mul_zero, add_zero, sub_zero] at hlim
  rw [exKernel_eq]
  exact hlim.congr fun n => (ch_chP_chPhi_eq hD0 hs hz (hn n)).symm

/-- **Uniform bound** of `P_s φ_L(z)` for `s ∈ [δ, t]`, `L ≥ 1`. -/
theorem ch_abs_chP_chPhi_le {D0 : ℝ} (hD0 : 0 < D0) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) :
    ∃ C : ℝ, ∀ s ∈ Icc δ t, ∀ L : ℝ, 1 ≤ L → |chP D0 s (chPhi L) z| ≤ C := by
  obtain ⟨CX, hCX⟩ := mk_kernelX_bdd_of_isCompact hD0 (isCompact_Icc : IsCompact (Icc δ t))
    (fun r hr => by rw [mem_Icc] at hr; rw [mem_Ioi]; linarith [hr.1])
  set CY := skSupY D0 δ
  refine ⟨3 * max CX 0 * CY, fun s hs L hL => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le hδ hs.1
  have hL0 : 0 < L := by linarith
  obtain ⟨hXm, hX0, -⟩ := ch_kX_props hD0 hs0 z.1
  obtain ⟨hYm, hY0, -⟩ := ch_kY_props hD0 hs0 hz.2
  have hMX : ∀ x', |mkKernelX D0 s z.1 x'| ≤ max CX 0 := fun x' => by
    rw [abs_of_nonneg (mk_kernelX_nonneg hD0 _ _ _)]
    exact (hCX s hs _ _).trans (le_max_left _ _)
  have hMY : ∀ y', |skKernelY D0 s z.2 y'| ≤ CY := fun y' => by
    rw [abs_of_nonneg (sk_kernelY_nonneg hD0 _ _ _)]; exact sk_kernelY_le hD0 hδ hs.1 _ _
  have hCY : 0 ≤ CY := sk_supY_nonneg D0 δ
  have hCX : 0 ≤ max CX 0 := le_max_right _ _
  have hLi : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have a0 := ch_abs_integral_chA0_le hX0 hMX hL0
  have a1 := (ch_abs_integral_chA1_le hX0 hMX hL0).trans
    (mul_le_of_le_one_left hCX hLi)
  have b0 := ch_abs_integral_chA0_le hY0 hMY hL0
  have b1 := (ch_abs_integral_chA1_le hY0 hMY hL0).trans (mul_le_of_le_one_left hCY hLi)
  rw [ch_chP_chPhi_eq hD0 hs0 hz hL0]
  set A0 := ∫ x', mkKernelX D0 s z.1 x' * chA0 L x'
  set A1 := ∫ x', mkKernelX D0 s z.1 x' * chA1 L x'
  set B0 := ∫ y', skKernelY D0 s z.2 y' * chA0 L y'
  set B1 := ∫ y', skKernelY D0 s z.2 y' * chA1 L y'
  calc |A0 * B0 + A1 * B0 - A0 * B1| ≤ |A0 * B0 + A1 * B0| + |A0 * B1| := abs_sub _ _
    _ ≤ |A0 * B0| + |A1 * B0| + |A0 * B1| := by gcongr; exact abs_add_le _ _
    _ = |A0| * |B0| + |A1| * |B0| + |A0| * |B1| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ max CX 0 * CY + max CX 0 * CY + max CX 0 * CY := by gcongr
    _ = 3 * max CX 0 * CY := by ring

theorem ch_measurable_chPhi (L : ℝ) : Measurable (chPhi L) := by unfold chPhi; fun_prop

/-- **Dominated convergence in `s`** on `(δ, t]`, `δ > 0`. -/
theorem ch_tendsto_setIntegral_chPhi {D0 : ℝ} (hD0 : 0 < D0) {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) :
    Tendsto (fun n : ℕ => ∫ s in Ioc δ t, chP D0 s (chPhi ((n : ℝ) + 1)) z) atTop
      (𝓝 (∫ s in Ioc δ t, exKernel D0 s z (0, 0))) := by
  obtain ⟨C, hC⟩ := ch_abs_chP_chPhi_le hD0 hδ t hz
  have : IsFiniteMeasure (volume.restrict (Ioc δ t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
    (integrable_const C) (fun n => ?_) ?_
  · have hm : Measurable fun q : ℝ × (ℝ × ℝ) => chPhi ((n : ℝ) + 1) q.2 :=
      (ch_measurable_chPhi _).comp measurable_snd
    exact (ch_stronglyMeasurable_chP hD0 (F := fun _ : ℝ => chPhi ((n : ℝ) + 1))
      hm measurable_id z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs]
    exact hC s (Ioc_subset_Icc_self hs) _ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ch_tendsto_chP_chPhi hD0 (lt_trans hδ hs.1) hz

end BlockBand.Diffusion
