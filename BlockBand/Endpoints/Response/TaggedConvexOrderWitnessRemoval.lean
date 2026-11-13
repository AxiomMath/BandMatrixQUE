module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessProbe

/-!
# Stop removal for the explicit witness (item (e)) and the stopped remainder input

Step 3 of the proof of the tagged convex-order theorem: the estimate is first used before a
trace stop, and the stop is then removed by the full-source stops lemma.

**Results.**
* `tcw_offStop_tag`: on the path, the off-stop part of the partial remainder sum is
  `≤ (4 + (n-a)W⁻¹κ) E[1{σ_K ≤ n} c_m max_{a≤i≤n}(Tr Q_{i;k})^m]` (telescoping,
  `|H_l| ≤ κF_l`, the dimension-free probe moment).
* `tcwRemainderCoreFixed_of_stopped`: `TcwRemainderCoreFixed` from `FullSourceMomentsContract`,
  `FullSourceStopsContract` (`supMoments`, `tail`), `ConditionalBlockGUECount`, the
  deterministic `TcwNuclearNormMeasurable`, and the stopped remainder
  `TcwStoppedRemainderCoreFixed`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-- **The off-stop part on the path**: for `a ≤ n`, with `S = c_m max_{a≤i≤n}(Tr Q_i)^m`
and `κ = (D₀/2)|m(m-1)|`,
`|Σ_{a≤l<n} E[1{σ_K ≤ l} r_l]| ≤ (4 + (n-a)W⁻¹κ) E[1{σ_K ≤ n} S]`. -/
theorem tcw_offStop_tag (hCount : ConditionalBlockGUECount) (hNuc : TcwNuclearNormMeasurable)
    {b e : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W)
    {k a n m : ℕ} {K ε : ℝ} (han : a ≤ n) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ (l : ℕ) (ω : GrowthPath W),
      Integrable (fun h => lmf_tagResponseClock b e W l k (ω, h) ^ m)
        (circularVectorLaw (Fin 2 × Fin W)) ∧
      0 ≤ tcw_F b e W l k m ω ∧ tcw_F b e W l k m ω ≤ c * (tco_tagQ b e W l k ω).trace.re ^ m)
    (hmom : ∀ l, a ≤ l → l ≤ n →
      Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b) ∧
      Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2)) (probedClockLaw W b))
    (hSint : Integrable (fun ω => (Icc a n).sup' (nonempty_Icc.2 han)
      (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)) (growthPathLaw W b)) :
    |∑ l ∈ Ico a n, ∫ ω, (tcw_alive b e W k K ε l)ᶜ.indicator (tcw_rem b e W l k m) ω
        ∂growthPathLaw W b| ≤
      (4 + (n - a : ℕ) * (W : ℝ)⁻¹ * (transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)|)) *
        ∫ ω, (tcw_alive b e W k K ε n)ᶜ.indicator 1 ω *
          (c * (Icc a n).sup' (nonempty_Icc.2 han)
            (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)) ∂growthPathLaw W b := by
  set cf : ℕ → GrowthPath W → ℝ := fun l => (tcw_alive b e W k K ε l)ᶜ.indicator 1
  set S : GrowthPath W → ℝ := fun ω => c * (Icc a n).sup' (nonempty_Icc.2 han)
    (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)
  have hD : 0 ≤ transportD0 b e / 2 := by have := transportD0_pos hb he1 he2; positivity
  have e1 : ∀ l, ∫ ω, (tcw_alive b e W k K ε l)ᶜ.indicator (tcw_rem b e W l k m) ω
      ∂growthPathLaw W b = ∫ ω, cf l ω * (tcw_F b e W (l + 1) k m ω - tcw_F b e W l k m ω -
        (W : ℝ)⁻¹ * tcw_H b e W l k m ω) ∂growthPathLaw W b := by
    intro l
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ (tcw_alive b e W k K ε l)ᶜ
    · simp only [cf, Set.indicator_of_mem hω, Pi.one_apply, one_mul]; rfl
    · simp only [cf, Set.indicator_of_notMem hω, zero_mul]
  rw [sum_congr rfl fun l _ => e1 l]
  have hcf0 : ∀ l ω, 0 ≤ cf l ω := fun l ω => by
    simp only [cf]; by_cases hω : ω ∈ (tcw_alive b e W k K ε l)ᶜ
    · rw [Set.indicator_of_mem hω]; norm_num
    · rw [Set.indicator_of_notMem hω]
  have hcf1 : ∀ l ω, cf l ω ≤ 1 := fun l ω => by
    simp only [cf]; by_cases hω : ω ∈ (tcw_alive b e W k K ε l)ᶜ
    · rw [Set.indicator_of_mem hω]; norm_num
    · rw [Set.indicator_of_notMem hω]; norm_num
  have hmono : ∀ ω, Monotone (fun l => cf l ω) := fun ω =>
    monotone_nat_of_le_succ fun l => Set.indicator_le_indicator_of_subset
      (Set.compl_subset_compl.2 (tcw_alive_succ_subset l)) (fun _ => zero_le_one) ω
  have hcm : ∀ l, AEStronglyMeasurable (cf l) (growthPathLaw W b) := fun l =>
    (measurable_const.indicator (tcw_measurableSet_alive hNuc b e W k K ε l).compl)
      |>.aestronglyMeasurable
  have hSle : ∀ ω i, a ≤ i → i ≤ n → c * (tco_tagQ b e W i k ω).trace.re ^ m ≤ S ω :=
    fun ω i h1 h2 => mul_le_mul_of_nonneg_left
      (le_sup' (fun i => (tco_tagQ b e W i k ω).trace.re ^ m) (mem_Icc.2 ⟨h1, h2⟩)) hc0
  refine tcw_offStop_bound (growthPathLaw W b) (fun l => tcw_F b e W l k m)
    (fun l => tcw_H b e W l k m) cf S han (inv_nonneg.2 (Nat.cast_nonneg W)) hcf0 hcf1 hmono hcm
    (fun i h1 h2 => tcw_integrable_F (hmom i h1 h2).1)
    (fun l h1 h2 => tcw_integrable_H hCount hb1 he1 he2 hW l k m (hmom l h1 h2.le).2)
    (hSint.const_mul c) (Eventually.of_forall fun ω i h1 h2 => ?_) ?_
  · rw [abs_of_nonneg (hc i ω).2.1]
    exact (hc i ω).2.2.trans (hSle ω i h1 h2)
  · have hall := ae_all_iff.2 fun l => tcw_abs_H_le hCount hb hb1 he1 he2 hW l k m (hc l)
    filter_upwards [hall] with ω hω l h1 h2
    refine (hω l).trans ?_
    exact mul_le_mul_of_nonneg_left ((hc l ω).2.2.trans (hSle ω l h1 h2.le))
      (mul_nonneg hD (abs_nonneg _))

/-- `x^{2m} ≤ 1 + x^{2m+1}` for `x ≥ 0`. -/
theorem tcw_pow_le_one_add {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ^ (2 * m) ≤ 1 + x ^ (2 * m + 1) := by
  rcases le_or_gt x 1 with h | h
  · have := pow_le_one₀ hx h (n := 2 * m)
    have : 0 ≤ x ^ (2 * m + 1) := pow_nonneg hx _
    linarith
  · have : x ^ (2 * m) ≤ x ^ (2 * m + 1) := pow_le_pow_right₀ h.le (Nat.le_succ _)
    linarith

theorem tcw_sourceTrace_tag (b e : ℝ) (W k i : ℕ) (ω : GrowthPath W) :
    sourceTrace b e (tcw_tagFamily k) tcw_noInterval W i ω (Sum.inl 0) =
      (tco_tagQ b e W i k ω).trace.re := by
  simp only [sourceTrace, sourceLetter, Sum.elim_inl, letterMatrix, tco_tagQ, trace_smul,
    smul_eq_mul, Complex.real_smul]
  rw [Complex.ofReal_inv, Complex.ofReal_natCast]

/-- **The squared maximum against `supMoments`**: for `[a,n] ⊆ [εW, TW]`,
`(max_{a≤i≤n}(Tr Q_i)^m)² ≤ 1 + (sup_{εW≤j≤TW} Tr Q_j)^{2m+1}` (as extended reals). -/
theorem tcw_sup_sq_le {b e : ℝ} {W k a n m : ℕ} {ε T : ℝ} (han : a ≤ n) (ha : ε * W ≤ a)
    (hn : (n : ℝ) ≤ T * W) (ω : GrowthPath W) :
    ENNReal.ofReal (((Icc a n).sup' (nonempty_Icc.2 han)
        (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)) ^ 2) ≤
      1 + (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
        ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W j ω (Sum.inl 0)‖ₑ) ^
          ((2 * m + 1 : ℕ) : ℝ) := by
  obtain ⟨i, hi, hmax⟩ := exists_mem_eq_sup' (nonempty_Icc.2 han)
    (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)
  obtain ⟨hi1, hi2⟩ := mem_Icc.1 hi
  rw [hmax]
  set x := (tco_tagQ b e W i k ω).trace.re
  have hx : 0 ≤ x := tco_trace_tagQ_nonneg b e W i k ω
  rw [← pow_mul, mul_comm m 2]
  calc ENNReal.ofReal (x ^ (2 * m)) ≤ ENNReal.ofReal (1 + x ^ (2 * m + 1)) :=
        ENNReal.ofReal_le_ofReal (tcw_pow_le_one_add hx m)
    _ = 1 + ENNReal.ofReal x ^ (2 * m + 1) := by
        rw [ENNReal.ofReal_add zero_le_one (pow_nonneg hx _), ENNReal.ofReal_one,
          ENNReal.ofReal_pow hx]
    _ ≤ _ := by
        rw [ENNReal.rpow_natCast]
        gcongr
        have hle : ENNReal.ofReal x =
            ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W i ω (Sum.inl 0)‖ₑ := by
          rw [tcw_sourceTrace_tag, Real.enorm_eq_ofReal hx]
        rw [hle]
        refine le_iSup₂_of_le (f := fun (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W) =>
          ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W j ω (Sum.inl 0)‖ₑ) i
          ⟨ha.trans (by exact_mod_cast hi1), (by exact_mod_cast hi2 : (i : ℝ) ≤ n).trans hn⟩
          le_rfl

/-- **The off-stop part at one width, quantitatively**: for `εW ≤ a ≤ n ≤ TW`, any `L > 0`, the
`supMoments` bound `E(sup_{εW≤j≤TW} Tr Q_j)^{2m+1} ≤ C_s` and the tail bound
`P{∃ εW ≤ j ≤ TW, load_j > K} ≤ β`:
`|Σ_{a≤l<n} E[1{σ_K ≤ l} r_l]| ≤ (4 + Tκ)(Lβ + c_m²(1 + C_s⁺)/L)`. -/
theorem tcw_offStop_total (hCount : ConditionalBlockGUECount) (hNuc : TcwNuclearNormMeasurable)
    {b e : ℝ} (hb : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W)
    {k a n m : ℕ} {K ε T : ℝ} (han : a ≤ n) (ha : ε * W ≤ a) (hn : (n : ℝ) ≤ T * W)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ (l : ℕ) (ω : GrowthPath W),
      Integrable (fun h => lmf_tagResponseClock b e W l k (ω, h) ^ m)
        (circularVectorLaw (Fin 2 × Fin W)) ∧
      0 ≤ tcw_F b e W l k m ω ∧ tcw_F b e W l k m ω ≤ c * (tco_tagQ b e W l k ω).trace.re ^ m)
    (hmom : ∀ l, a ≤ l → l ≤ n →
      Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b) ∧
      Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2)) (probedClockLaw W b))
    {Cs : ℝ} (hCs : ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
        ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W j ω (Sum.inl 0)‖ₑ) ^
          ((2 * m + 1 : ℕ) : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal Cs)
    {β : ℝ} (hβ : 0 ≤ β) (hbad : growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
      K < traceLoad b e (tcw_tagFamily k) tcw_noInterval W j ω} ≤ ENNReal.ofReal β)
    {L : ℝ} (hL : 0 < L) :
    |∑ l ∈ Ico a n, ∫ ω, (tcw_alive b e W k K ε l)ᶜ.indicator (tcw_rem b e W l k m) ω
        ∂growthPathLaw W b| ≤
      (4 + T * (transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)|)) *
        (L * β + c ^ 2 * (1 + max Cs 0) / L) := by
  have hP := tco_isProbabilityMeasure_growthPathLaw W b
  set μ := growthPathLaw W b
  set Smax : GrowthPath W → ℝ := fun ω => (Icc a n).sup' (nonempty_Icc.2 han)
    (fun i => (tco_tagQ b e W i k ω).trace.re ^ m)
  set κ := transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)|
  have hκ : 0 ≤ κ := by have := transportD0_pos hb he1 he2; positivity
  have hSm : Measurable Smax := by
    have := Finset.measurable_sup' (nonempty_Icc.2 han)
      (f := fun i ω => (tco_tagQ b e W i k ω).trace.re ^ m) fun i _ =>
      (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
        (tcw_measurable_tagQ b e W i k))).pow_const m
    convert! this using 1
    ext ω
    simp [Smax, Finset.sup'_apply]
  have hS0 : ∀ ω, 0 ≤ Smax ω := fun ω =>
    (pow_nonneg (tco_trace_tagQ_nonneg b e W a k ω) m).trans
      (le_sup' (fun i => (tco_tagQ b e W i k ω).trace.re ^ m) (mem_Icc.2 ⟨le_rfl, han⟩))
  -- the squared maximum
  have hS2 : Integrable (fun ω => Smax ω ^ 2) μ ∧ ∫ ω, Smax ω ^ 2 ∂μ ≤ 1 + max Cs 0 := by
    refine integrable_and_integral_le_of_lintegral (hSm.pow_const 2) (fun ω => sq_nonneg _)
      (by positivity) ?_
    calc ∫⁻ ω, ENNReal.ofReal (Smax ω ^ 2) ∂μ
        ≤ ∫⁻ ω, (1 + (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
            ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W j ω (Sum.inl 0)‖ₑ) ^
              ((2 * m + 1 : ℕ) : ℝ)) ∂μ := lintegral_mono fun ω => tcw_sup_sq_le han ha hn ω
      _ = 1 + ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
            ‖sourceTrace b e (tcw_tagFamily k) tcw_noInterval W j ω (Sum.inl 0)‖ₑ) ^
              ((2 * m + 1 : ℕ) : ℝ) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]
      _ ≤ 1 + ENNReal.ofReal Cs := by gcongr
      _ ≤ ENNReal.ofReal (1 + max Cs 0) := by
          rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one]
          gcongr
          exact le_max_left _ _
  have hSint : Integrable Smax μ := by
    refine (hS2.1.add (integrable_const 1)).mono' hSm.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 ω)]
    show Smax ω ≤ Smax ω ^ 2 + 1
    nlinarith [hS0 ω]
  have h1 := tcw_offStop_tag (K := K) (ε := ε) hCount hNuc hb hb1 he1 he2 hW han hc0 hc hmom hSint
  -- the dead set at `n`
  set D := (tcw_alive b e W k K ε n)ᶜ
  have hDm : MeasurableSet D := (tcw_measurableSet_alive hNuc b e W k K ε n).compl
  have hDμ : (μ D).toReal ≤ β := by
    refine ENNReal.toReal_le_of_le_ofReal hβ ((measure_mono fun ω hω => ?_).trans hbad)
    have hω' : ¬ ∀ i ≤ n,
        ¬ (ε * W ≤ i ∧ K < traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω) := by
      intro h; exact hω (tcw_mem_alive_iff.2 h)
    push Not at hω'
    obtain ⟨i, hi, hi1, hi2⟩ := hω'
    exact ⟨i, hi1, (by exact_mod_cast hi : (i : ℝ) ≤ n).trans hn, hi2⟩
  -- `E[1_D cS] ≤ L P(D) + c² E Smax²/L`
  have hind : ∀ ω, D.indicator (1 : GrowthPath W → ℝ) ω * (c * Smax ω) ≤
      L * D.indicator 1 ω + (c * Smax ω) ^ 2 / L := by
    intro ω
    have h0 : 0 ≤ D.indicator (1 : GrowthPath W → ℝ) ω := by
      by_cases h : ω ∈ D
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]
    have h1' : D.indicator (1 : GrowthPath W → ℝ) ω ≤ 1 := by
      by_cases h : ω ∈ D
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    exact tcw_mul_le_split h0 h1' (mul_nonneg hc0 (hS0 ω)) hL
  have hiD : Integrable (D.indicator (1 : GrowthPath W → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hDm
  have hE : ∫ ω, D.indicator (1 : GrowthPath W → ℝ) ω * (c * Smax ω) ∂μ ≤
      L * β + c ^ 2 * (1 + max Cs 0) / L := by
    have hsq : Integrable (fun ω => (c * Smax ω) ^ 2 / L) μ := by
      refine (hS2.1.const_mul (c ^ 2 / L)).congr (Eventually.of_forall fun ω => ?_)
      simp only; ring
    refine (integral_mono_of_nonneg ?_ ((hiD.const_mul L).add hsq)
      (Eventually.of_forall hind)).trans ?_
    · exact Eventually.of_forall fun ω => mul_nonneg (by
        by_cases h : ω ∈ D
        · rw [Set.indicator_of_mem h]; norm_num
        · rw [Set.indicator_of_notMem h]) (mul_nonneg hc0 (hS0 ω))
    simp only [Pi.add_apply]
    rw [integral_add (hiD.const_mul L) hsq, integral_const_mul, integral_indicator_one hDm]
    have e2 : ∫ ω, (c * Smax ω) ^ 2 / L ∂μ = c ^ 2 / L * ∫ ω, Smax ω ^ 2 ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
    rw [e2]
    have hc2 : 0 ≤ c ^ 2 / L := by positivity
    have := mul_le_mul_of_nonneg_left hS2.2 hc2
    have h3 : L * μ.real D ≤ L * β := mul_le_mul_of_nonneg_left hDμ hL.le
    calc L * μ.real D + c ^ 2 / L * ∫ ω, Smax ω ^ 2 ∂μ ≤ L * β + c ^ 2 / L * (1 + max Cs 0) :=
          add_le_add h3 this
      _ = L * β + c ^ 2 * (1 + max Cs 0) / L := by ring
  -- the prefactor
  have hpre : (4 + (n - a : ℕ) * (W : ℝ)⁻¹ * κ) ≤ 4 + T * κ := by
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have : ((n - a : ℕ) : ℝ) * (W : ℝ)⁻¹ ≤ T := by
      rw [← div_eq_mul_inv, div_le_iff₀ hW']
      calc ((n - a : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n a
        _ ≤ T * W := hn
    nlinarith
  have hEn : 0 ≤ ∫ ω, D.indicator (1 : GrowthPath W → ℝ) ω * (c * Smax ω) ∂μ :=
    integral_nonneg fun ω => mul_nonneg (by
      by_cases h : ω ∈ D
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]) (mul_nonneg hc0 (hS0 ω))
  have hpos : 0 ≤ 4 + T * κ := by
    have : 0 ≤ 4 + (n - a : ℕ) * (W : ℝ)⁻¹ * κ := by positivity
    linarith
  calc _ ≤ (4 + (n - a : ℕ) * (W : ℝ)⁻¹ * κ) *
        ∫ ω, D.indicator (1 : GrowthPath W → ℝ) ω * (c * Smax ω) ∂μ := h1
    _ ≤ (4 + T * κ) * ∫ ω, D.indicator (1 : GrowthPath W → ℝ) ω * (c * Smax ω) ∂μ :=
        mul_le_mul_of_nonneg_right hpre hEn
    _ ≤ (4 + T * κ) * (L * β + c ^ 2 * (1 + max Cs 0) / L) :=
        mul_le_mul_of_nonneg_left hE hpos

/-!
## The stopped remainder input and the stop removal
-/

/-- **Stopped remainder input along one tagged sequence** (the estimate before a trace stop). For
every degree `M`, `δ > 0` and stop level `K > 0`, eventually in `j`: for every `m ≤ M` and every
partial range `k+1 ≤ l' ≤ n`, `|Σ_{k+1≤l<l'} E[1{l < σ_K} r_l(m)]| ≤ δ`, where
`r_l(m) = tcw_rem` is the one-step remainder of the monomial `X^m` at a fixed path
(`E_h Z_{l+1}^m - E_h Z_l^m - W⁻¹(D₀/2)m(m-1)E_h[X^{m-2}(v*Pv)(v*P'v)]`), and `σ_K` is the trace
stop of the one-tag family at level `K`, from `εW`, `ε = s/2` (`tcw_alive`).

*Why strictly smaller than `TcwRemainderAlong`.* It concerns the same explicit remainder, but
only on the survival events `{l < σ_K}`, on which every trace load is `≤ K`. The removal of the
stop (the telescoping of the off-stop increments, `|d_l| ≤ c_mW⁻¹X^m`, the dimension-free probe
moment, `FullSourceStopsContract.supMoments` and `.tail`) is proved here
(`tcwRemainderCoreFixed_of_stopped`). What is left is the stopped estimate that
`ContractingWordsContract.summed` provides once three non-estimate inputs are supplied:
(a) the complex Wick formula writing `E_h Z^m` as the ordinary trace polynomial
`Σ_{π∈S_m} Π_cycles Tr Q^{|c|}` in the tag words; (b) the identity
`polyValue(wordGenerator Φ_m) = (D₀/2)m(m-1)E_h[X^{m-2}(v*Pv)(v*P'v)]` (`pairTerm` with
`P' = P + J`); (d) adaptedness `{l < σ_K} ∈ growthSigma W l` (so that
`E[1_A ΔF] = E[1_A E_l[1_A ΔF]]`). No new analytic bound is needed beyond `summed`. -/
def TcwStoppedRemainderAlong (b : ℝ) {s τ E : ℝ} (σ : TcoTagSequence s τ E) : Prop :=
  ∀ (M : ℕ) (δ K : ℝ), 0 < δ → 0 < K → ∀ᶠ j in atTop, ∀ m ≤ M, ∀ l', σ.k j + 1 ≤ l' →
    l' ≤ σ.n j →
    |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b (σ.energy j) (σ.W j) (σ.k j) K (s / 2) l).indicator
      (tcw_rem b (σ.energy j) (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| ≤ δ

/-- **Stopped remainder input at fixed energy**: `TcwStoppedRemainderAlong` along every tagged
sequence at the constant energy `E`. -/
def TcwStoppedRemainderCoreFixed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s τ : ℝ, 0 < s →
    ∀ σ : TcoTagSequence s τ E, (∀ j, σ.energy j = E) → TcwStoppedRemainderAlong b σ

/-- **Stop removal (item (e))**: `TcwRemainderCoreFixed` from `FullSourceMomentsContract` and
`FullSourceStopsContract` (`supMoments`, `tail`), `ConditionalBlockGUECount`, the isolated
deterministic `TcwNuclearNormMeasurable` and the isolated stopped input
`TcwStoppedRemainderCoreFixed`. -/
theorem tcwRemainderCoreFixed_of_stopped (hMom : FullSourceMomentsContract)
    (hStops : FullSourceStopsContract) (hCount : ConditionalBlockGUECount)
    (hNuc : TcwNuclearNormMeasurable) (hSt : TcwStoppedRemainderCoreFixed) :
    TcwRemainderCoreFixed := by
  intro b hb hb' E hE1 hE2 s τ hs σ hσ M δ hδ
  have hsτ := tco_tagSequence_s_le σ
  have hε : 0 < s / 2 := by linarith
  have hεT : s / 2 < τ + 1 := by linarith
  have hq : IsIntervalTests tcw_noInterval := fun a => a.elim0
  suffices H : ∀ m ∈ range (M + 1), ∀ᶠ j in atTop, ∀ l', σ.k j + 1 ≤ l' → l' ≤ σ.n j →
      |∑ l ∈ Ico (σ.k j + 1) l',
        (tcs_monoErr b (σ.energy j) (transportD0 b E) (σ.W j) l (σ.k j) m -
          tcw_deficit b (σ.energy j) (σ.W j) l (σ.k j) m)| ≤ δ by
    filter_upwards [(eventually_all_finset _).2 H] with j hj m hm l' h1 h2
    exact hj m (by simp; omega) l' h1 h2
  intro m hmM
  have hmM' : m ≤ M := by simp at hmM; omega
  obtain ⟨c, hc0, hc⟩ := tcw_F_bound m
  have hD0 := transportD0_pos hb hE1 hE2
  set κ : ℝ := transportD0 b E / 2 * |(m : ℝ) * ((m : ℝ) - 1)|
  have hκ : 0 ≤ κ := by positivity
  set K₁ : ℝ := 4 + (τ + 1) * κ
  have hK₁ : 0 < K₁ := by
    have : 0 ≤ (τ + 1) * κ := mul_nonneg (by linarith) hκ
    linarith
  obtain ⟨Cs, W₀s, hCs⟩ := hStops.supMoments b hb hb' E hE1 hE2 1 0 tcw_noInterval hq (s / 2)
    (τ + 1) ((2 * m + 1 : ℕ) : ℝ) hε hεT (by positivity)
  obtain ⟨Ct, hCt⟩ := hStops.tail b hb hb' E hE1 hE2 1 0 tcw_noInterval hq (s / 2) (τ + 1) hε hεT
  set Is : ℝ := 1 + max Cs 0
  have hIs : 0 < Is := by have := le_max_right Cs 0; simp only [Is]; linarith
  set L : ℝ := 4 * K₁ * (c ^ 2 * Is) / δ + 1
  have hL : 0 < L := by positivity
  set Kc : ℝ := 4 * K₁ * L * (|Ct| + 1) / δ + 1
  have hKc : 0 < Kc := by positivity
  set β : ℝ := (|Ct| + 1) / Kc
  have hβ : 0 ≤ β := by positivity
  have htail : ∀ᶠ W : ℕ in atTop, (⨆ k' : Fin 1 → ℕ, growthPathLaw W b {ω | ∃ j : ℕ,
      s / 2 * W ≤ j ∧ (j : ℝ) ≤ (τ + 1) * W ∧ Kc < traceLoad b E k' tcw_noInterval W j ω}) <
        ENNReal.ofReal β := by
    refine eventually_lt_of_limsup_lt ((hCt Kc hKc).trans_lt ?_)
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact div_lt_div_of_pos_right ((le_abs_self Ct).trans_lt (lt_add_one _)) hKc
  choose Cf hCf using tcc_momentsAlong_fixed hMom hb hb' hE1 hE2 σ hσ
  have hmomE : ∀ᶠ j in atTop, ∀ p ∈ range (m + 3), ∀ l, σ.k j < l → l ≤ σ.n j →
      ∫⁻ x, ENNReal.ofReal (x ^ (2 * p)) ∂tcc_law b (σ.energy j) (σ.W j) l (σ.k j) ≤
        ENNReal.ofReal (Cf p) :=
    (eventually_all_finset _).2 fun p _ => hCf p
  have htag : ∀ᶠ j in atTop, s / 2 * (σ.W j : ℝ) ≤ σ.k j := by
    filter_upwards [σ.tag_tendsto.eventually (lt_mem_nhds (show s / 2 < s by linarith))] with j hj
    have hW : (0 : ℝ) < σ.W j := by exact_mod_cast σ.W_pos j
    rw [lt_div_iff₀ hW] at hj
    exact hj.le
  filter_upwards [hSt b hb hb' E hE1 hE2 s τ hs σ hσ M (δ / 2) Kc (half_pos hδ) hKc, hmomE,
    tcc_eventually_len σ W₀s, htag, σ.width_tendsto.eventually htail] with j hStj hmj hlen hkj htj
  intro l' h1 h2
  have he := hσ j
  rw [he] at hStj hmj ⊢
  have hWpos := σ.W_pos j
  have hint : ∀ l, σ.k j + 1 ≤ l → l ≤ σ.n j → ∀ p ≤ m + 2, Integrable
      (fun x => lmf_tagResponseClock b E (σ.W j) l (σ.k j) x ^ p) (probedClockLaw (σ.W j) b) :=
    fun l hl1 hl2 p hp => tcw_integrable_tagClock_pow (hmj p (by simp; omega) l (by omega) hl2)
  -- the remainder as a path expectation, split at the stop
  have hsplit : ∀ l ∈ Ico (σ.k j + 1) l',
      tcs_monoErr b E (transportD0 b E) (σ.W j) l (σ.k j) m -
          tcw_deficit b E (σ.W j) l (σ.k j) m =
        ∫ ω, (tcw_alive b E (σ.W j) (σ.k j) Kc (s / 2) l).indicator
            (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b +
          ∫ ω, (tcw_alive b E (σ.W j) (σ.k j) Kc (s / 2) l)ᶜ.indicator
            (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b := by
    intro l hl
    obtain ⟨hl1, hl2⟩ := mem_Ico.1 hl
    rw [tcw_remainder_eq hCount hb' hE1 hE2 hWpos l (σ.k j) m
      (hint (l + 1) (by omega) (by omega) m (by omega)) (hint l (by omega) (by omega) m (by omega))
      (hint l (by omega) (by omega) (m - 2 + 2) (by omega))]
    have hr : Integrable (tcw_rem b E (σ.W j) l (σ.k j) m) (growthPathLaw (σ.W j) b) :=
      ((tcw_integrable_F (hint (l + 1) (by omega) (by omega) m (by omega))).sub
        (tcw_integrable_F (hint l (by omega) (by omega) m (by omega)))).sub
        ((tcw_integrable_H hCount hb' hE1 hE2 hWpos l (σ.k j) m
          (hint l (by omega) (by omega) (m - 2 + 2) (by omega))).const_mul _)
    have hA := tcw_measurableSet_alive hNuc b E (σ.W j) (σ.k j) Kc (s / 2) l
    rw [← integral_add (hr.indicator hA) (hr.indicator hA.compl)]
    exact integral_congr_ae (Eventually.of_forall fun ω =>
      (Set.indicator_self_add_compl_apply _ _ ω).symm)
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have hstop := hStj m hmM' l' h1 h2
  have hoff := tcw_offStop_total (K := Kc) (ε := s / 2) (T := τ + 1) hCount hNuc hb hb' hE1 hE2
    hWpos (k := σ.k j) (m := m) h1 (by push_cast; linarith) ((by exact_mod_cast h2 :
      (l' : ℝ) ≤ σ.n j).trans hlen.2) hc0 (fun l ω => hc b E (σ.W j) l (σ.k j) ω)
    (fun l hl1 hl2 => ⟨hint l hl1 (hl2.trans h2) m (by omega),
      hint l hl1 (hl2.trans h2) (m - 2 + 2) (by omega)⟩)
    (hCs (σ.W j) hlen.1 (tcw_tagFamily (σ.k j)) (Sum.inl 0)) hβ
    ((le_iSup (fun k' : Fin 1 → ℕ => growthPathLaw (σ.W j) b {ω | ∃ j' : ℕ,
      s / 2 * (σ.W j : ℝ) ≤ j' ∧ (j' : ℝ) ≤ (τ + 1) * σ.W j ∧
        Kc < traceLoad b E k' tcw_noInterval (σ.W j) j' ω}) (tcw_tagFamily (σ.k j))).trans
      htj.le) hL
  -- the two smallness conditions
  have hq1 : K₁ * (c ^ 2 * Is / L) ≤ δ / 4 := by
    rw [show K₁ * (c ^ 2 * Is / L) = K₁ * (c ^ 2 * Is) / L by ring, div_le_iff₀ hL]
    have : δ / 4 * L = K₁ * (c ^ 2 * Is) + δ / 4 := by
      simp only [L]; field_simp; try ring
    have : 0 ≤ K₁ * (c ^ 2 * Is) := by positivity
    nlinarith
  have hq2 : K₁ * (L * β) ≤ δ / 4 := by
    simp only [β]
    rw [show K₁ * (L * ((|Ct| + 1) / Kc)) = K₁ * L * (|Ct| + 1) / Kc by ring, div_le_iff₀ hKc]
    have : δ / 4 * Kc = K₁ * L * (|Ct| + 1) + δ / 4 := by
      simp only [Kc]; field_simp; try ring
    have : 0 ≤ K₁ * L * (|Ct| + 1) := by positivity
    nlinarith
  calc _ ≤ |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b E (σ.W j) (σ.k j) Kc (s / 2) l).indicator
          (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| +
        |∑ l ∈ Ico (σ.k j + 1) l', ∫ ω, (tcw_alive b E (σ.W j) (σ.k j) Kc (s / 2) l)ᶜ.indicator
          (tcw_rem b E (σ.W j) l (σ.k j) m) ω ∂growthPathLaw (σ.W j) b| := abs_add_le _ _
    _ ≤ δ / 2 + K₁ * (L * β + c ^ 2 * Is / L) := add_le_add hstop hoff
    _ ≤ δ := by nlinarith

/-- `TcoTagComparisonCoreFixed` from `FullSourceMomentsContract`, `TagBirthValueContract`,
`FullSourceStopsContract`, `ConditionalBlockGUECount`, the isolated deterministic
`TcwNuclearNormMeasurable` and the isolated stopped input `TcwStoppedRemainderCoreFixed`. -/
theorem tcoTagComparisonCoreFixed_of_stopped (hMom : FullSourceMomentsContract)
    (hBirth : TagBirthValueContract) (hStops : FullSourceStopsContract)
    (hCount : ConditionalBlockGUECount) (hNuc : TcwNuclearNormMeasurable)
    (hSt : TcwStoppedRemainderCoreFixed) : TcoTagComparisonCoreFixed :=
  tcoTagComparisonCoreFixed_of_remainder hMom hBirth hCount
    (tcwRemainderCoreFixed_of_stopped hMom hStops hCount hNuc hSt)

end BlockBand.Endpoints
