module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.BrownianTools
public import BlockBand.SourceProcess.Stochastic.SDE.NativeEstimates
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gronwall estimate for the general integral against a Brownian motion

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion with
its integrator `hB.isL2IntegratorVec` (identity density), horizon `T`, Lebesgue measure on
`(0, T]`, squared Euclidean norms `∑_i ‖·‖ₑ²` on `ℝ^d` (in `ℝ≥0∞`).

**`lintegral_sq_le_gronwall`**: let `D` be a process with a jointly measurable version `D̃`
(`D_s = D̃(s, ·)` a.s. for `s ≤ T`) and, for every `t ≤ T`,
`D_t = ∫_{(0,t]} β(r) dr + ∫_0^t γ dB` a.s. coordinatewise, with `β` bounded measurable and `γ`
bounded predictable. If a.s., for all `r ∈ (0, T]`,
`|β(r)|² + |γ(r)|² ≤ L (|D̃(r)|² + ε(r))` with `∫ ε(r) dP ≤ δ` on `(0,T]`, then
`E |D_t|² ≤ C(T, L) δ` for `t ≤ T`, `C(T,L) = K T e^{K T}`, `K = 2 (T + 1) L`.
Steps: `(a + b)² ≤ 2a² + 2b²`, Cauchy–Schwarz for the drift, the isometry
(`integral_sq_vecCont`), Tonelli, and the real integral Gronwall inequality
(`SDE.gronwall_integral`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ}

theorem enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- The martingale part in `ℝ≥0∞`: `E ‖∫_0^t γ dB‖² = E ∫_{(0,t]} ∑_k ‖γ_k‖²`. -/
theorem lintegral_sq_vecCont (hB : IsFiltrationBrownian P 𝓕 B) {T : ℝ≥0}
    {f : Fin d → ℝ × Ω → ℝ} (hf : ∀ k, IsBddPred 𝓕 (f k)) {t : ℝ≥0} (htT : t ≤ T) :
    haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
    ∫⁻ ω, ‖hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hf k)) t ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ k, ‖f k (r, ω)‖ₑ ^ 2) ∂P := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set M := hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hf k)) t
  have hM : MemLp M 2 P := (hB.isL2IntegratorVec.vecCont_spec T _).2.1 t
  have hbd : ∀ k, ∃ C, ∀ p, |f k p| ≤ C := fun k => ⟨(hf k).bdd.choose, (hf k).bdd.choose_spec.2⟩
  choose C hC using hbd
  have hmeas : ∀ k, Measurable (f k) := fun k =>
    ((hf k).sm.mono (predictableSpace_le _)).measurable
  have hin : ∀ ω, IntegrableOn (fun r => ∑ k, f k (r, ω) ^ 2) (Ioc (0 : ℝ) t) := fun ω => by
    refine Measure.integrableOn_of_bounded (M := ∑ k, C k ^ 2) (by simp)
      (Finset.measurable_sum _ fun k _ => ((hmeas k).comp (measurable_id.prodMk
        measurable_const)).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_le_sum fun k _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC k _) 2
  have hint : Integrable (fun ω => ∫ r in Ioc (0 : ℝ) t, ∑ k, f k (r, ω) ^ 2) P := by
    have := integral_sq_vecCont hB hf htT
    refine Integrable.of_bound (C := t * ∑ k, C k ^ 2) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (StronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) t))
        (f := fun p : ℝ × Ω => ∑ k, f k p ^ 2)
        (Measurable.stronglyMeasurable
          (Finset.measurable_sum _ fun k _ => (hmeas k).pow_const 2))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun r _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)]
      calc ∫ r in Ioc (0 : ℝ) t, ∑ k, f k (r, ω) ^ 2 ≤ ∫ _r in Ioc (0 : ℝ) t, ∑ k, C k ^ 2 :=
            setIntegral_mono_on (hin ω) (by simp) measurableSet_Ioc fun r _ =>
              Finset.sum_le_sum fun k _ => by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC k _) 2
        _ = t * ∑ k, C k ^ 2 := by simp
  have e1 : ∫⁻ ω, ‖M ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, M ω ^ 2 ∂P) := by
    simp_rw [enorm_sq_eq_ofReal]
    rw [ofReal_integral_eq_lintegral_ofReal hM.integrable_sq
      (Eventually.of_forall fun _ => sq_nonneg _)]
  rw [e1, integral_sq_vecCont hB hf htT, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Ioc fun r _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hin ω) (Eventually.of_forall fun r =>
    Finset.sum_nonneg fun k _ => sq_nonneg _)]
  refine lintegral_congr fun r => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
  simp_rw [enorm_sq_eq_ofReal]

/-- Squared sums `∑_i ‖β_i‖² + ∑_{ik} ‖γ_{ik}‖²` of the coefficients. -/
def coefSq (β : Fin d → ℝ × Ω → ℝ) (γ : Fin d → Fin d → ℝ × Ω → ℝ) (p : ℝ × Ω) : ℝ≥0∞ :=
  (∑ i, ‖β i p‖ₑ ^ 2) + ∑ i, ∑ k, ‖γ i k p‖ₑ ^ 2

/-- **One step**: `E|D_t|² ≤ 2 (T + 1) E ∫_{(0,t]} (|β|² + |γ|²)`. -/
theorem lintegral_sq_le_coefSq (hB : IsFiltrationBrownian P 𝓕 B) {T : ℝ≥0}
    {D : ℝ≥0 → Ω → Fin d → ℝ} {β : Fin d → ℝ × Ω → ℝ} (hβ : ∀ i, Measurable (β i))
    {Mβ : ℝ} (hβb : ∀ i p, |β i p| ≤ Mβ)
    {γ : Fin d → Fin d → ℝ × Ω → ℝ} (hγ : ∀ i k, IsBddPred 𝓕 (γ i k)) {t : ℝ≥0} (htT : t ≤ T)
    (hrep : haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
      ∀ i, ∀ᵐ ω ∂P, D t ω i = (∫ r in Ioc (0 : ℝ) t, β i (r, ω)) +
        hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hγ i k)) t ω) :
    ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P ≤
      2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSq β γ (r, ω)) ∂P := by
  have := hB.isL2IntegratorVec.isFiniteMeasure_bar T
  set M : Fin d → Ω → ℝ := fun i => hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hγ i k)) t
  have hM : ∀ i, MemLp (M i) 2 P := fun i => (hB.isL2IntegratorVec.vecCont_spec T _).2.1 t
  have hγm : ∀ i k, Measurable (γ i k) := fun i k =>
    ((hγ i k).sm.mono (predictableSpace_le _)).measurable
  have hβr : ∀ i ω, IntegrableOn (fun r => β i (r, ω)) (Ioc (0 : ℝ) t) := fun i ω =>
    Measure.integrableOn_of_bounded (M := Mβ) (by simp)
      ((hβ i).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hβb i _)
  have hβr' : ∀ i ω, Measurable fun r => ‖β i (r, ω)‖ₑ ^ 2 := fun i ω =>
    ((hβ i).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2
  have hγr' : ∀ i k ω, Measurable fun r => ‖γ i k (r, ω)‖ₑ ^ 2 := fun i k ω =>
    ((hγm i k).comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2
  have hγs : ∀ i, Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, ∑ k, ‖γ i k (r, ω)‖ₑ ^ 2 :=
    fun i => Measurable.lintegral_prod_left' (Finset.measurable_sum _ fun k _ =>
      ((hγm i k).enorm.pow_const 2))
  have hMs : ∀ i, AEMeasurable (fun ω => ‖M i ω‖ₑ ^ 2) P := fun i =>
    (hM i).aestronglyMeasurable.enorm.pow_const 2
  -- pointwise bound
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
  -- integrate
  have hmart : ∀ i, ∫⁻ ω, ‖M i ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ k, ‖γ i k (r, ω)‖ₑ ^ 2) ∂P := fun i =>
    lintegral_sq_vecCont hB (hγ i) htT
  have hβm : Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2 :=
    Measurable.lintegral_prod_left' (Finset.measurable_sum _ fun i _ =>
      ((hβ i).enorm.pow_const 2))
  calc ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (2 * ENNReal.ofReal T * (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) +
          2 * ∑ i, ‖M i ω‖ₑ ^ 2) ∂P := lintegral_mono_ae h1
    _ = 2 * ENNReal.ofReal T * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * ∑ i, ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ k, ‖γ i k (r, ω)‖ₑ ^ 2) ∂P := by
        rw [lintegral_add_left' ((hβm.const_mul (2 * ENNReal.ofReal T)).aemeasurable)
          (fun ω => 2 * ∑ i, ‖M i ω‖ₑ ^ 2), lintegral_const_mul'' _ hβm.aemeasurable,
          lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ fun i _ => hMs i),
          lintegral_finsetSum' _ fun i _ => hMs i]
        simp_rw [hmart]
    _ = 2 * ENNReal.ofReal T * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ∑ k, ‖γ i k (r, ω)‖ₑ ^ 2) ∂P := by
        congr 2
        rw [← lintegral_finsetSum' _ fun i _ => (hγs i).aemeasurable]
        refine lintegral_congr fun ω => ?_
        rw [lintegral_finsetSum' _ fun i _ => (Finset.measurable_sum _ fun k _ =>
          hγr' i k ω).aemeasurable]
    _ ≤ 2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ‖β i (r, ω)‖ₑ ^ 2) ∂P +
          2 * (ENNReal.ofReal T + 1) *
            ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, ∑ i, ∑ k, ‖γ i k (r, ω)‖ₑ ^ 2) ∂P := by
        gcongr
        · exact le_self_add
        · calc (2 : ℝ≥0∞) = 2 * 1 := (mul_one 2).symm
            _ ≤ 2 * (ENNReal.ofReal T + 1) := by gcongr; exact le_add_self
    _ = 2 * (ENNReal.ofReal T + 1) * ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSq β γ (r, ω)) ∂P := by
        rw [← mul_add, ← lintegral_add_left' hβm.aemeasurable]
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_add_left' (Finset.measurable_sum _ fun i _ => hβr' i ω).aemeasurable]
        rfl

/-- The Gronwall constant `K T e^{K T}`, `K = 2 (T + 1) L`. -/
def gronC (T L : ℝ≥0) : ℝ := 2 * (T + 1) * L * T * Real.exp (2 * (T + 1) * L * T)

theorem gronC_nonneg (T L : ℝ≥0) : 0 ≤ gronC T L := by unfold gronC; positivity

omit mΩ in
theorem coefSq_le {β : Fin d → ℝ × Ω → ℝ} {Mβ : ℝ} (hβb : ∀ i p, |β i p| ≤ Mβ)
    {γ : Fin d → Fin d → ℝ × Ω → ℝ} {C : Fin d → Fin d → ℝ} (hγb : ∀ i k p, |γ i k p| ≤ C i k)
    (p : ℝ × Ω) : coefSq β γ p ≤
      (∑ _i : Fin d, ENNReal.ofReal (Mβ ^ 2)) + ∑ i, ∑ k, ENNReal.ofReal (C i k ^ 2) := by
  unfold coefSq
  have h : ∀ (x M : ℝ), |x| ≤ M → ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (M ^ 2) := fun x M hx => by
    rw [enorm_sq_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  exact add_le_add (Finset.sum_le_sum fun i _ => h _ _ (hβb i p))
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h _ _ (hγb i k p))

/-- **The Gronwall estimate** (see the module docstring). -/
theorem lintegral_sq_le_gronwall (hB : IsFiltrationBrownian P 𝓕 B) {T : ℝ≥0}
    {D : ℝ≥0 → Ω → Fin d → ℝ} {D' : ℝ × Ω → Fin d → ℝ} (hD' : Measurable D')
    (hDD : ∀ s : ℝ≥0, s ≤ T → ∀ᵐ ω ∂P, D s ω = D' ((s : ℝ), ω))
    {β : Fin d → ℝ × Ω → ℝ} (hβ : ∀ i, Measurable (β i)) {Mβ : ℝ} (hβb : ∀ i p, |β i p| ≤ Mβ)
    {γ : Fin d → Fin d → ℝ × Ω → ℝ} (hγ : ∀ i k, IsBddPred 𝓕 (γ i k))
    (hrep : haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar T
      ∀ t ≤ T, ∀ i, ∀ᵐ ω ∂P, D t ω i = (∫ r in Ioc (0 : ℝ) t, β i (r, ω)) +
        hB.isL2IntegratorVec.vecCont T (fun k => bpL2 _ (hγ i k)) t ω)
    {ε : ℝ × Ω → ℝ≥0∞} (hε : Measurable ε) {δ : ℝ≥0∞} (hδt : δ ≠ ⊤)
    (hδ : ∀ r ∈ Ioc (0 : ℝ) T, ∫⁻ ω, ε (r, ω) ∂P ≤ δ) {L : ℝ≥0}
    (hbound : ∀ᵐ ω ∂P, ∀ r ∈ Ioc (0 : ℝ) T,
      coefSq β γ (r, ω) ≤ L * ((∑ i, ‖D' (r, ω) i‖ₑ ^ 2) + ε (r, ω))) :
    ∀ t ≤ T, ∫⁻ ω, ∑ i, ‖D t ω i‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (gronC T L) * δ := by
  set Ψ : ℝ → ℝ≥0∞ := fun r => ∫⁻ ω, ∑ i, ‖D' (r, ω) i‖ₑ ^ 2 ∂P
  have hFm : Measurable fun p : ℝ × Ω => ∑ i, ‖D' p i‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hD').enorm.pow_const 2
  have hΨm : Measurable Ψ := hFm.lintegral_prod_right'
  have hΨD : ∀ s : ℝ≥0, s ≤ T → ∫⁻ ω, ∑ i, ‖D s ω i‖ₑ ^ 2 ∂P = Ψ s := fun s hs =>
    lintegral_congr_ae (by filter_upwards [hDD s hs] with ω hω; rw [hω])
  set K : ℝ≥0∞ := 2 * (ENNReal.ofReal T + 1)
  have hK : K ≠ ⊤ := by simp [K, ENNReal.mul_eq_top]
  -- a priori bound
  choose C hC using fun i k => (hγ i k).bdd
  set Cc := (∑ _i : Fin d, ENNReal.ofReal (Mβ ^ 2)) + ∑ i, ∑ k, ENNReal.ofReal (C i k ^ 2)
  have hCc : Cc ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top,
    ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top⟩
  have hstep1 := fun (t : ℝ≥0) (ht : t ≤ T) => lintegral_sq_le_coefSq hB hβ hβb hγ ht
    (fun i => hrep t ht i)
  have hbd : ∀ t : ℝ≥0, t ≤ T → Ψ t ≤ K * (ENNReal.ofReal T * Cc) := fun t ht => by
    rw [← hΨD t ht]
    refine (hstep1 t ht).trans ?_
    gcongr
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSq β γ (r, ω)) ∂P
        ≤ ∫⁻ _ω, ENNReal.ofReal T * Cc ∂P := lintegral_mono fun ω => by
          calc ∫⁻ r in Ioc (0 : ℝ) t, coefSq β γ (r, ω) ≤ ∫⁻ _r in Ioc (0 : ℝ) t, Cc :=
                lintegral_mono fun r => coefSq_le hβb (fun i k => (hC i k).2) _
            _ = ENNReal.ofReal t * Cc := by rw [lintegral_const]; simp [mul_comm]
            _ ≤ ENNReal.ofReal T * Cc := by gcongr
      _ = ENNReal.ofReal T * Cc := by simp
  set Mb := K * (ENNReal.ofReal T * Cc)
  have hMb : Mb ≠ ⊤ := by simp [Mb, ENNReal.mul_eq_top, hK, hCc]
  -- the recursive inequality
  have hstep : ∀ t : ℝ≥0, t ≤ T → Ψ t ≤
      K * L * ((∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + ENNReal.ofReal t * δ) := fun t ht => by
    rw [← hΨD t ht]
    refine (hstep1 t ht).trans ?_
    rw [mul_assoc K]
    refine mul_le_mul_right ?_ K
    have hεm : Measurable fun ω => ∫⁻ r in Ioc (0 : ℝ) t, ε (r, ω) := hε.lintegral_prod_left'
    calc ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) t, coefSq β γ (r, ω)) ∂P
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
      _ ≤ L * ((∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + ENNReal.ofReal t * δ) := by
          gcongr
          calc ∫⁻ r in Ioc (0 : ℝ) t, (∫⁻ ω, ε (r, ω) ∂P) ≤ ∫⁻ _r in Ioc (0 : ℝ) t, δ :=
                setLIntegral_mono' measurableSet_Ioc fun r hr =>
                  hδ r ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 ht)⟩
            _ = ENNReal.ofReal t * δ := by rw [lintegral_const]; simp [mul_comm]
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
  have hrec : ∀ t ∈ Icc (0 : ℝ) T, u t ≤ KL * T * δ.toReal + KL * ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    have h1 := hstep t.toNNReal (by rw [Real.toNNReal_le_iff_le_coe]; exact ht.2)
    rw [Real.coe_toNNReal _ ht.1] at h1
    have hfin1 : (∫⁻ r in Ioc (0 : ℝ) t, Ψ r) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _r in Ioc (0 : ℝ) t, Mb) ?_
        (setLIntegral_mono' measurableSet_Ioc fun r hr => hΨT r ⟨hr.1.le, hr.2.trans ht.2⟩)
      rw [lintegral_const]; exact ENNReal.mul_ne_top hMb (by simp)
    have hfin2 : (∫⁻ r in Ioc (0 : ℝ) t, Ψ r) + ENNReal.ofReal t * δ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hfin1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδt⟩
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK
      ENNReal.coe_ne_top) hfin2) h1
    rw [ENNReal.toReal_mul, hKL, ENNReal.toReal_add hfin1 (ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top hδt), ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1,
      ← integral_toReal hΨm.aemeasurable.restrict] at h2
    · rw [intervalIntegral.integral_of_le ht.1]
      have : KL * (t * δ.toReal) ≤ KL * T * δ.toReal := by
        rw [← mul_assoc]; gcongr; exact ht.2
      calc u t ≤ KL * ((∫ r in Ioc (0 : ℝ) t, u r) + t * δ.toReal) := h2
        _ ≤ KL * T * δ.toReal + KL * ∫ r in Ioc (0 : ℝ) t, u r := by nlinarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hΨT r ⟨hr.1.le, hr.2.trans ht.2⟩).trans_lt (lt_top_iff_ne_top.2 hMb)
  intro t ht
  have hg := SDE.gronwall_integral hKL0 hu0 hint hrec t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  rw [hΨD t ht, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top hMb
    (hΨT t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩)),
    ← ENNReal.ofReal_toReal hδt, ← ENNReal.ofReal_mul (gronC_nonneg T L)]
  refine ENNReal.ofReal_le_ofReal (hg.trans ?_)
  unfold gronC
  have he : Real.exp (KL * t) ≤ Real.exp (2 * (T + 1) * L * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 ht) hKL0)
  have hδ0 : 0 ≤ δ.toReal := ENNReal.toReal_nonneg
  calc KL * T * δ.toReal * Real.exp (KL * t) ≤ KL * T * δ.toReal * Real.exp (2 * (T + 1) * L * T) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = 2 * (T + 1) * L * T * Real.exp (2 * (T + 1) * L * T) * δ.toReal := by ring

end BlockBand.SourceProcess.Stochastic.Uniqueness
