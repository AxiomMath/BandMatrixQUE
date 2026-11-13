module

public import BlockBand.Diffusion.Heat.Forward

/-!
# The `l`-integrated forward equation: the corner identity at finite cutoff

**Headline (`ch_chP_chHL`).** For `D₀ > 0`, `z ∈ exBaseStrip`, `t > 0`, `L > 0`:
`P_t H_L(z) = H_L(z) - (D₀/2)∫_{(0,t]} P_u φ_L(z) du`, where `H_L = ∫_0^L e^{-l(x+y)} dl`
(`chHL`) and `φ_L = L²(1+x-y)e^{-L(x+y)}` (`chPhi`).

Proof: integrate the forward equation `ch_chP_chExp` over `l ∈ (0, L]`; Fubini (all integrands
bounded on the strip: `|e_l| ≤ 1`, `|𝒟₀e_l| ≤ (D₀/2)(3L+4)`); and the exact `l`-integral
`∫_0^L 𝒟₀e_l dl = -(D₀/2)φ_L` (`ch_integral_chGen`: `𝒟₀e_l = -(D₀/2)∂_l[l²(1+x-y)e^{-l(x+y)}]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

theorem ch_ae_fst_mem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite ν] {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ q ∂((μ.restrict s).prod ν), q.1 ∈ s := by
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := μ.restrict s) (ν := ν)
    (hs.preimage measurable_fst)).2
  exact h ((ae_restrict_mem hs).mono fun x hx => ae_of_all _ fun _ => hx)

theorem ch_ae_snd_mem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite ν] {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ q ∂(μ.prod (ν.restrict s)), q.2 ∈ s := by
  have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := μ) (ν := ν.restrict s)
    (hs.preimage measurable_snd)).2
  exact h (ae_of_all _ fun _ => ae_restrict_mem hs)

/-- Fubini for `P_t` against a parameter integral over a set of finite measure. -/
theorem ch_chP_setIntegral {D0 : ℝ} (hD0 : 0 < D0) {t : ℝ} (ht : 0 < t) {z : ℝ × ℝ}
    (hz : z ∈ exBaseStrip) {F : ℝ → ℝ × ℝ → ℝ} (hF : Measurable (Function.uncurry F))
    {S : Set ℝ} (hS : MeasurableSet S) (hSf : volume S < ∞) {C : ℝ}
    (hC : ∀ l ∈ S, ∀ w ∈ exBaseStrip, |F l w| ≤ C) :
    chP D0 t (fun z' => ∫ l in S, F l z') z = ∫ l in S, chP D0 t (F l) z := by
  have : IsFiniteMeasure (volume.restrict S) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hp := ch_integrable_exKernel hD0 ht hz
  unfold chP
  simp_rw [← integral_const_mul]
  refine integral_integral_swap (f := fun z' l => exKernel D0 t z z' * F l z') ?_
  have hm : Measurable fun q : (ℝ × ℝ) × ℝ => exKernel D0 t z q.1 * F q.2 q.1 :=
    ((exKernel_measurable hD0).comp (f := fun q : (ℝ × ℝ) × ℝ => (t, z, q.1))
      (by fun_prop)).mul (hF.comp (measurable_snd.prodMk measurable_fst))
  refine (hp.mul_prod (integrable_const C)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ch_ae_snd_mem (μ := (volume : Measure (ℝ × ℝ))) hS] with q hq
  rw [Real.norm_eq_abs]
  exact ch_abs_exKernel_mul_le hD0 t z (hC q.2 hq) q.1

/-- The exact `l`-integral of the generator: `∫_0^L 𝒟₀e_l dl = -(D₀/2)φ_L`. -/
theorem ch_integral_chGen (D0 : ℝ) {L : ℝ} (hL : 0 ≤ L) (w : ℝ × ℝ) :
    ∫ l in Ioc 0 L, chGen D0 l w = -(D0 / 2) * chPhi L w := by
  set a := 1 + w.1 - w.2
  set s := w.1 + w.2
  have hd : ∀ l : ℝ, HasDerivAt (fun l => -(D0 / 2) * (a * l ^ 2 * Real.exp (-(l * s))))
      (chGen D0 l w) l := fun l => by
    have h1 : HasDerivAt (fun l => -(l * s)) (-s) l :=
      (hasDerivAt_mul_const (-s)).congr_of_eventuallyEq (Eventually.of_forall fun y => by ring)
    have h2 := (((hasDerivAt_pow 2 l).const_mul a).mul h1.exp).const_mul (-(D0 / 2))
    refine h2.congr_deriv ?_
    simp only [chGen, a, s]
    push_cast
    ring
  rw [← intervalIntegral.integral_of_le hL, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun l _ => hd l) ((ch_continuous_chGen_l D0 w).intervalIntegrable _ _)]
  simp only [chPhi, a, s]
  ring_nf
where
  ch_continuous_chGen_l (D0 : ℝ) (w : ℝ × ℝ) : Continuous fun l => chGen D0 l w := by
    unfold chGen; fun_prop

theorem ch_measurable_chGen_uncurry (D0 : ℝ) :
    Measurable (Function.uncurry fun (l : ℝ) (w : ℝ × ℝ) => chGen D0 l w) := by
  have : Continuous fun q : ℝ × (ℝ × ℝ) => chGen D0 q.1 q.2 := by unfold chGen; fun_prop
  exact this.measurable

theorem ch_measurable_chExp_uncurry :
    Measurable (Function.uncurry fun (l : ℝ) (w : ℝ × ℝ) => chExp l w) := by
  have : Continuous fun q : ℝ × (ℝ × ℝ) => chExp q.1 q.2 := by unfold chExp; fun_prop
  exact this.measurable

/-- **The corner identity at finite cutoff `L`.** -/
theorem ch_chP_chHL {D0 : ℝ} (hD0 : 0 < D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {t : ℝ}
    (ht : 0 < t) {L : ℝ} (hL : 0 < L) :
    chP D0 t (chHL L) z = chHL L z - D0 / 2 * ∫ u in Ioc 0 t, chP D0 u (chPhi L) z := by
  have hfinL : volume (Ioc (0 : ℝ) L) < ∞ := measure_Ioc_lt_top
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  set CG := D0 / 2 * (3 * L + 4)
  have hCG : ∀ l ∈ Ioc (0 : ℝ) L, ∀ w ∈ exBaseStrip, |chGen D0 l w| ≤ CG := fun l hl w hw =>
    (ch_abs_chGen_le hD0 hl.1.le hw).trans (by
      have : 0 ≤ D0 / 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith [hl.2]) this)
  have hCG0 : 0 ≤ CG := by positivity
  -- Step 1: `P_t H_L = ∫_0^L P_t e_l dl`
  have hHL : chHL L = fun z' => ∫ l in Ioc 0 L, chExp l z' := by
    funext z'; exact intervalIntegral.integral_of_le hL.le
  have s1 : chP D0 t (chHL L) z = ∫ l in Ioc 0 L, chP D0 t (chExp l) z := by
    rw [hHL]
    exact ch_chP_setIntegral hD0 ht hz ch_measurable_chExp_uncurry measurableSet_Ioc hfinL
      fun l hl w hw => ch_abs_chExp_le hl.1.le hw
  -- Step 2: insert the forward equation
  have hmGu : StronglyMeasurable fun q : ℝ × ℝ => chP D0 q.2 (chGen D0 q.1) z :=
    ch_stronglyMeasurable_chP hD0 (F := fun q : ℝ × ℝ => chGen D0 q.1)
      ((ch_measurable_chGen_uncurry D0).comp (measurable_fst.fst.prodMk measurable_snd))
      measurable_snd z
  have hbd : ∀ l ∈ Ioc (0 : ℝ) L, ∀ u, |chP D0 u (chGen D0 l) z| ≤ CG := fun l hl u =>
    ch_abs_chP_le hD0 u hz hCG0 (hCG l hl)
  have hint2 : IntegrableOn (fun l => ∫ u in Ioc 0 t, chP D0 u (chGen D0 l) z) (Ioc 0 L) := by
    refine Integrable.of_bound (hmGu.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) t))).aestronglyMeasurable (CG * t) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) t)
      (f := fun u => chP D0 u (chGen D0 l) z) (C := CG) measure_Ioc_lt_top
      (fun u _ => by rw [Real.norm_eq_abs]; exact hbd l hl u)
    simpa [Real.volume_real_Ioc_of_le ht.le] using this
  have hint1 : IntegrableOn (fun l => chExp l z) (Ioc 0 L) := by
    have hc : Continuous fun l => chExp l z := by unfold chExp; fun_prop
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have s2 : ∫ l in Ioc 0 L, chP D0 t (chExp l) z =
      ∫ l in Ioc 0 L, (chExp l z + ∫ u in Ioc 0 t, chP D0 u (chGen D0 l) z) :=
    setIntegral_congr_fun measurableSet_Ioc fun l hl => ch_chP_chExp hD0 hz ht hl.1
  -- Step 3: swap `l` and `u`
  have s3 : ∫ l in Ioc 0 L, (∫ u in Ioc 0 t, chP D0 u (chGen D0 l) z) =
      ∫ u in Ioc 0 t, (∫ l in Ioc 0 L, chP D0 u (chGen D0 l) z) := by
    refine integral_integral_swap (f := fun l u => chP D0 u (chGen D0 l) z) ?_
    refine Integrable.of_bound hmGu.aestronglyMeasurable CG ?_
    filter_upwards [ch_ae_fst_mem (ν := volume.restrict (Ioc (0 : ℝ) t)) measurableSet_Ioc]
      with q hq
    rw [Real.norm_eq_abs]
    exact hbd q.1 hq q.2
  -- Step 4: the exact `l`-integral inside `P_u`
  have s4 : ∫ u in Ioc 0 t, (∫ l in Ioc 0 L, chP D0 u (chGen D0 l) z) =
      ∫ u in Ioc 0 t, -(D0 / 2) * chP D0 u (chPhi L) z := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [← ch_chP_setIntegral hD0 hu.1 hz (ch_measurable_chGen_uncurry D0) measurableSet_Ioc
      hfinL hCG]
    simp_rw [ch_integral_chGen D0 hL.le]
    unfold chP
    rw [← integral_const_mul]
    congr 1
    funext z'
    ring
  have hHLz : chHL L z = ∫ l in Ioc 0 L, chExp l z := intervalIntegral.integral_of_le hL.le
  rw [s1, s2, integral_add hint1 hint2, ← hHLz, s3, s4, integral_const_mul]
  ring

end BlockBand.Diffusion
