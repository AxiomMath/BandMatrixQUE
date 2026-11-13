module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Gronwall
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# An abstract Gronwall estimate

Setting: a probability space `(Ω, P)`, horizon `T`, Lebesgue measure on `(0, T]`, squared
Euclidean norms in `ℝ≥0∞`. **`lintegral_sq_le_gronwall_abs`**: let `D` have a jointly measurable
version `D'`, and `D_t = ∫_{(0,t]} β + M_t` a.s. (coordinatewise, `t ≤ T`) with `β` bounded
measurable and martingale parts `M` satisfying the isometry bound
`E |M^i_t|² ≤ E ∫_{(0,t]} q_i` for measurable `q_i ≥ 0`, bounded a.s. on `(0, T]`. If a.s. on
`(0, T]`, `|β|² + ∑ q ≤ L (|D'|² + ε)` with `E ∫_{(0,T]} ε ≤ δ`, then
`E |D_t|² ≤ gronCI T L · δ` (the proof follows `Uniqueness.lintegral_sq_le_gronwall`; here the integrator enters only through the isometry bound).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Squared sums `∑_i ‖β_i‖² + ∑_i q_i`. -/
def coefSqA (β : Fin d → ℝ × Ω → ℝ) (q : Fin d → ℝ × Ω → ℝ≥0∞) (p : ℝ × Ω) : ℝ≥0∞ :=
  (∑ i, ‖β i p‖ₑ ^ 2) + ∑ i, q i p

omit [IsProbabilityMeasure P] in
/-- **One step**: `E|D_t|² ≤ 2 (T + 1) E ∫_{(0,t]} (|β|² + ∑ q)`. -/
theorem lintegral_sq_le_coefSqA {T : ℝ≥0}
    {D : ℝ≥0 → Ω → Fin d → ℝ} {β : Fin d → ℝ × Ω → ℝ} (hβ : ∀ i, Measurable (β i))
    {Mβ : ℝ} (hβb : ∀ i p, |β i p| ≤ Mβ) {M : Fin d → Ω → ℝ}
    (hMm : ∀ i, AEMeasurable (M i) P) {q : Fin d → ℝ × Ω → ℝ≥0∞} (hq : ∀ i, Measurable (q i))
    {t : ℝ≥0} (htT : t ≤ T)
    (hiso : ∀ i, ∫⁻ ω, ‖M i ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, q i (r, ω)) ∂P)
    (hrep : ∀ i, ∀ᵐ ω ∂P, D t ω i = (∫ r in Ioc (0 : ℝ) t, β i (r, ω)) + M i ω) :
    ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P ≤
      2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSqA β q (r, ω)) ∂P := by
  have hβr : ∀ i ω, IntegrableOn (fun r => β i (r, ω)) (Ioc (0 : ℝ) t) := fun i ω =>
    Measure.integrableOn_of_bounded (M := Mβ) (by simp)
      ((hβ i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hβb i _)
  have hβr' : ∀ i ω, Measurable fun r => ‖β i (r, ω)‖ₑ ^ 2 := fun i ω =>
    ((hβ i).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2
  have hqr : ∀ i ω, Measurable fun r => q i (r, ω) := fun i ω =>
    (hq i).comp (measurable_id.prodMk measurable_const)
  have hqs : ∀ i, Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, q i (r, ω) :=
    fun i => Measurable.lintegral_prod_left' (hq i)
  have hMs : ∀ i, AEMeasurable (fun ω => ‖M i ω‖ₑ ^ 2) P := fun i =>
    (hMm i).enorm.pow_const 2
  have h1 : ∀ᵐ ω ∂P, ∑ i, ‖D t ω i‖ₑ ^ 2 ≤
      2 * ENNReal.ofReal T * (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) +
        2 * ∑ i, ‖M i ω‖ₑ ^ 2 := by
    filter_upwards [ae_all_iff.2 hrep] with ω hω
    rw [lintegral_finsetSum' _ fun i _ => (hβr' i ω).aemeasurable,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hω i]
    refine (NativeSDE.enorm_sq_add_le _ _).trans (add_le_add ?_ le_rfl)
    have hcs := NativeSDE.enorm_sq_integral_sub_le (hβr i ω) (integrableOn_zero)
      (h := fun r => ‖β i (r, ω)‖ₑ) (fun r _ => by simp)
      (((hβ i).comp (measurable_id.prodMk measurable_const)).enorm.aemeasurable)
    simp only [integral_zero, sub_zero] at hcs
    rw [mul_assoc]
    refine mul_le_mul_right ?_ 2
    exact hcs.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (NNReal.coe_le_coe.2 htT)) _)
  have hβm : Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2 :=
    Measurable.lintegral_prod_left' (Finset.measurable_sum _ fun i _ =>
      ((hβ i).enorm.pow_const 2))
  calc ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (2 * ENNReal.ofReal T * (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) +
          2 * ∑ i, ‖M i ω‖ₑ ^ 2) ∂P := lintegral_mono_ae h1
    _ = 2 * ENNReal.ofReal T * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * ∑ i, ∫⁻ ω, ‖M i ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left' ((hβm.const_mul (2 * ENNReal.ofReal T)).aemeasurable)
          (fun ω => 2 * ∑ i, ‖M i ω‖ₑ ^ 2), lintegral_const_mul'' _ hβm.aemeasurable,
          lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun i _ => hMs i),
          lintegral_finsetSum' _ fun i _ => hMs i]
    _ ≤ 2 * ENNReal.ofReal T * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * ∑ i, ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, q i (r, ω)) ∂P := by
        exact add_le_add le_rfl (mul_le_mul_right (Finset.sum_le_sum fun i _ => hiso i) 2)
    _ = 2 * ENNReal.ofReal T * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, q i (r, ω)) ∂P := by
        congr 2
        rw [← lintegral_finsetSum' _ fun i _ => (hqs i).aemeasurable]
        refine lintegral_congr fun ω => ?_
        rw [lintegral_finsetSum' _ fun i _ => (hqr i ω).aemeasurable]
    _ ≤ 2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * (ENNReal.ofReal T + 1) *
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, q i (r, ω)) ∂P := by
        gcongr
        · exact le_self_add
        · calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * (ENNReal.ofReal T + 1) := by gcongr; exact le_add_self
    _ = 2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSqA β q (r, ω)) ∂P := by
        rw [← mul_add, ← lintegral_add_left' hβm.aemeasurable]
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_add_left' (Finset.measurable_sum _ fun i _ => hβr' i ω).aemeasurable]
        rfl

/-- The Gronwall constant `K e^{K T}`, `K = 2 (T + 1) L` (integrated error form). -/
def gronCI (T L : ℝ≥0) : ℝ := 2 * (T + 1) * L * Real.exp (2 * (T + 1) * L * T)

theorem gronCI_nonneg (T L : ℝ≥0) : 0 ≤ gronCI T L := by unfold gronCI; positivity

/-- **The Gronwall estimate** (see the module docstring). -/
theorem lintegral_sq_le_gronwall_abs {T : ℝ≥0}
    {D : ℝ≥0 → Ω → Fin d → ℝ} {D' : ℝ × Ω → Fin d → ℝ} (hD' : Measurable D')
    (hDD : ∀ s : ℝ≥0, s ≤ T → ∀ᵐ ω ∂P, D s ω = D' ((s : ℝ), ω))
    {β : Fin d → ℝ × Ω → ℝ} (hβ : ∀ i, Measurable (β i)) {Mβ : ℝ} (hβb : ∀ i p, |β i p| ≤ Mβ)
    {M : Fin d → ℝ≥0 → Ω → ℝ} (hMm : ∀ i t, AEMeasurable (M i t) P)
    {q : Fin d → ℝ × Ω → ℝ≥0∞} (hq : ∀ i, Measurable (q i)) {Cq : ℝ≥0∞} (hCq : Cq ≠ ⊤)
    (hqb : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) T, ∀ i, q i (r, ω) ≤ Cq)
    (hiso : ∀ t ≤ T, ∀ i, ∫⁻ ω, ‖M i t ω‖ₑ ^ 2 ∂P ≤
      ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, q i (r, ω)) ∂P)
    (hrep : ∀ t ≤ T, ∀ i, ∀ᵐ ω ∂P, D t ω i = (∫ r in Ioc (0 : ℝ) t, β i (r, ω)) + M i t ω)
    {ε : ℝ × Ω → ℝ≥0∞} (hε : Measurable ε) {δ : ℝ≥0∞} (hδt : δ ≠ ⊤)
    (hδ : ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) T, ε (r, ω)) ∂P ≤ δ) {L : ℝ≥0}
    (hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) T,
      coefSqA β q (r, ω) ≤ L * ((∑ i, ‖D' (r, ω) i‖ₑ ^ 2) + ε (r, ω))) :
    ∀ t ≤ T, ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (gronCI T L) * δ := by
  set Ψ : ℝ → ℝ≥0∞ := fun r => ∫⁻ ω, ∑ i, ‖D' (r, ω) i‖ₑ ^ 2 ∂P
  have hFm : Measurable fun p : ℝ × Ω => ∑ i, ‖D' p i‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hD').enorm.pow_const 2
  have hΨm : Measurable Ψ := hFm.lintegral_prod_right'
  have hΨD : ∀ s : ℝ≥0, s ≤ T → ∫⁻ ω, ∑ i, ‖D s ω i‖ₑ ^ 2 ∂P = Ψ s := fun s hs =>
    lintegral_congr_ae (by filter_upwards [hDD s hs] with ω hω; rw [hω])
  set K : ℝ≥0∞ := 2 * (ENNReal.ofReal T + 1)
  have hK : K ≠ ⊤ := by simp [K, ENNReal.mul_eq_top]
  -- a priori bound
  set Cc := (∑ _i : Fin d, ENNReal.ofReal (Mβ ^ 2)) + ∑ _i : Fin d, Cq
  have hCc : Cc ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top,
    ENNReal.sum_ne_top.2 fun _ _ => hCq⟩
  have hstep1 := fun (t : ℝ≥0) (ht : t ≤ T) => lintegral_sq_le_coefSqA hβ hβb (hMm · t) hq ht
    (hiso t ht) (fun i => hrep t ht i)
  have hcb : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) T, coefSqA β q (r, ω) ≤ Cc := by
    filter_upwards [hqb] with ω hω r hr
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => hω r hr i)
    rw [enorm_sq_eq_ofReal]
    have h2 : β i (r, ω) ^ 2 ≤ Mβ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hβb i _) 2
    exact ENNReal.ofReal_le_ofReal h2
  have hbd : ∀ t : ℝ≥0, t ≤ T → Ψ t ≤ K * (ENNReal.ofReal T * Cc) := fun t ht => by
    rw [← hΨD t ht]
    refine (hstep1 t ht).trans ?_
    gcongr
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSqA β q (r, ω)) ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal T * Cc ∂P := lintegral_mono_ae <| by
          filter_upwards [hcb] with ω hω
          calc ∫⁻ r in Ioc (0 : ℝ) t, coefSqA β q (r, ω) ≤ ∫⁻ _r in Ioc (0 : ℝ) t, Cc :=
                setLIntegral_mono' measurableSet_Ioc fun r hr =>
                  hω r ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 ht)⟩
            _ = ENNReal.ofReal t * Cc := by rw [lintegral_const]; simp [mul_comm]
            _ ≤ ENNReal.ofReal T * Cc := by gcongr
      _ = ENNReal.ofReal T * Cc := by simp
  set Mb := K * (ENNReal.ofReal T * Cc)
  have hMb : Mb ≠ ⊤ := by simp [Mb, ENNReal.mul_eq_top, hK, hCc]
  -- the recursive inequality
  have hstep : ∀ t : ℝ≥0, t ≤ T → Ψ t ≤
      K * L * ((∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + δ) := fun t ht => by
    rw [← hΨD t ht]
    refine (hstep1 t ht).trans ?_
    rw [mul_assoc K]
    refine mul_le_mul_right ?_ K
    have hεm : Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, ε (r, ω) := hε.lintegral_prod_left'
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSqA β q (r, ω)) ∂P
        ≤ ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, L * ((∑ i, ‖D' (r, ω) i‖ₑ ^ 2) + ε (r, ω))) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbound] with ω hω
          exact setLIntegral_mono' measurableSet_Ioc fun r hr =>
            hω r ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 ht)⟩
      _ = L * ((∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖D' (r, ω) i‖ₑ ^ 2) ∂P) +
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ε (r, ω)) ∂P) := by
          rw [← lintegral_add_right' _ hεm.aemeasurable, ← lintegral_const_mul' _ _
            ENNReal.coe_ne_top]
          refine lintegral_congr fun ω => ?_
          have hεr : Measurable fun r => ε (r, ω) := hε.comp (measurable_id.prodMk measurable_const)
          rw [← lintegral_add_right' _ hεr.aemeasurable, ← lintegral_const_mul' _ _
            ENNReal.coe_ne_top]
      _ = L * ((∫⁻ r in Ioc (0 : ℝ) t, Ψ r) +
            ∫⁻ r in Ioc (0 : ℝ) t, (∫⁻ ω, ε (r, ω) ∂P)) := by
          rw [lintegral_lintegral_swap (f := fun ω r => ∑ i, ‖D' (r, ω) i‖ₑ ^ 2)
            (hFm.comp measurable_swap).aemeasurable,
            lintegral_lintegral_swap (f := fun ω r => ε (r, ω)) (hε.comp measurable_swap).aemeasurable]
      _ ≤ L * ((∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + δ) := by
          gcongr
          calc ∫⁻ r in Ioc (0 : ℝ) t, (∫⁻ ω, ε (r, ω) ∂P)
              ≤ ∫⁻ r in Ioc (0 : ℝ) T, (∫⁻ ω, ε (r, ω) ∂P) :=
                lintegral_mono_set (Ioc_subset_Ioc le_rfl (NNReal.coe_le_coe.2 ht))
            _ = ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) T, ε (r, ω)) ∂P :=
                (lintegral_lintegral_swap (f := fun ω r => ε (r, ω))
                  (hε.comp measurable_swap).aemeasurable).symm
            _ ≤ δ := hδ
  -- real Gronwall
  set u : ℝ → ℝ := fun r => (Ψ r).toReal
  have hΨT : ∀ r ∈ Icc (0 : ℝ) T, Ψ r ≤ Mb := fun r hr => by
    have := hbd r.toNNReal (by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2)
    rwa [Real.coe_toNNReal _ hr.1] at this
  have hu0 : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ u r := fun r _ => ENNReal.toReal_nonneg
  have hint : IntervalIntegrable u volume 0 T := by
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le T.coe_nonneg]
    refine Measure.integrableOn_of_bounded (M := Mb.toReal) (by simp)
      hΨm.ennreal_toReal.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hMb (hΨT r hr)
  set KL : ℝ := 2 * (T + 1) * L
  have hKL : (K * L).toReal = KL := by
    simp only [K, KL, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.one_ne_top,
      ENNReal.toReal_ofReal T.coe_nonneg, ENNReal.toReal_one]
  have hKL0 : 0 ≤ KL := by positivity
  have hrec : ∀ t ∈ Icc (0 : ℝ) T, u t ≤ KL * δ.toReal + KL * ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    have h1 := hstep t.toNNReal (by rw [Real.toNNReal_le_iff_le_coe]; exact ht.2)
    rw [Real.coe_toNNReal _ ht.1] at h1
    have hfin1 : (∫⁻ r in Ioc (0 : ℝ) t, Ψ r) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _r in Ioc (0 : ℝ) t, Mb) ?_
        (setLIntegral_mono' measurableSet_Ioc fun r hr => hΨT r ⟨hr.1.le, hr.2.trans ht.2⟩)
      rw [lintegral_const]; exact ENNReal.mul_ne_top hMb (by simp)
    have hfin2 : (∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + δ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hfin1, hδt⟩
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK
      ENNReal.coe_ne_top) hfin2) h1
    rw [ENNReal.toReal_mul, hKL, ENNReal.toReal_add hfin1 hδt,
      ← integral_toReal hΨm.aemeasurable.restrict] at h2
    · rw [intervalIntegral.integral_of_le ht.1]
      calc u t ≤ KL * ((∫ r in Ioc (0 : ℝ) t, u r) + δ.toReal) := h2
        _ = KL * δ.toReal + KL * ∫ r in Ioc (0 : ℝ) t, u r := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hΨT r ⟨hr.1.le, hr.2.trans ht.2⟩).trans_lt (lt_top_iff_ne_top.2 hMb)
  intro t ht
  have hg := SDE.gronwall_integral hKL0 hu0 hint hrec t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  rw [hΨD t ht, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hMb
    (hΨT t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩)),
    ← ENNReal.ofReal_toReal hδt, ← ENNReal.ofReal_mul (gronCI_nonneg T L)]
  refine ENNReal.ofReal_le_ofReal (hg.trans ?_)
  unfold gronCI
  have he : Real.exp (KL * t) ≤ Real.exp (2 * (T + 1) * L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hKL0)
  have hδ0 : 0 ≤ δ.toReal := ENNReal.toReal_nonneg
  calc KL * δ.toReal * Real.exp (KL * t) ≤ KL * δ.toReal * Real.exp (2 * (T + 1) * L * T) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 2 * (T + 1) * L * Real.exp (2 * (T + 1) * L * T) * δ.toReal := by ring

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
