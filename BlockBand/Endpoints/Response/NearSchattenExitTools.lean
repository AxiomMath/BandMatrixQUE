module

public import BlockBand.Endpoints.Response.NearSchattenStopped

/-!
# Tools for the exit and stop removal of the near-Schatten stopped energy

Part of the proof of the near-Schatten decay theorem: on a trace stop, the fixed clock/current
moments remove the stops.

* `nsx_wordValue_clockWord_one`: the word identity `Tr(QP) = Tr A` for the clock word.
* `nsxSupQ`: `sup_{εW ≤ j ≤ TW} Tr Q_j` in the exact form of
  `FullSourceStopsContract.supMoments`; its measurability and `Tr A_j ≤ nsxSupQ`.
* `nsx_lintegral_indicator_le`, `nsx_lintegral_tail_le`: `E[1_B Y] ≤ M P(B) + E[Y; Y > M]` and
  `E[Y; Y > M] ≤ E[Y²]/M` on `ℝ≥0∞` (no measurability of `Y`).
* `nsx_eventually_dead_le`: attainment of the `traceStop` infimum and `tail`: for every
  `ρ > 0` there is `K₀` with `P(σ_K ≤ j₂) ≤ ρ` for all `K ≥ K₀` and all large `W`.
* `nsx_eventually_jump_le`: the one-step form of `FullSourceGeneratorContract.tight` for
  the word `Tr(QP)`: `P(∃ j ∈ [j₁, j₂), |Tr(QP)_{j+1} - Tr(QP)_j| > 1) → 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## The clock word `Tr(QP)`
-/

/-- **The word identity** `Tr(QP) = Tr A` for the clock word `QP`. -/
theorem nsx_wordValue_clockWord_one (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (j : ℕ) (ω : GrowthPath W)
    (κ : Fin 0 → ℕ) :
    wordValue b E κ (fun _ => q) W j ω (clockWord 1) = (nearClock b E W j q ω).trace := by
  rw [ns_wordValue_clockWord_eq b E q W j ω κ le_rfl, pow_one]

theorem nsx_measurable_trA (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) :
    Measurable (fun ω : GrowthPath W => (nearClock b E W j q ω).trace.re) := by
  have h := Complex.measurable_re.comp
    (nss_measurable_wordValue b E (noTags W) (fun _ => q) W j (clockWord 1))
  convert h using 1
  funext ω
  simp only [Function.comp_apply, nsx_wordValue_clockWord_one]

theorem nsx_ordinary_clockWord_one : IsOrdinaryWord (clockWord 1) := by
  refine ⟨by simp [clockWord], fun x hx => ?_⟩
  simp only [clockWord, List.replicate_one, List.mem_singleton] at hx
  rw [hx]; right; rfl

/-!
## The supremum of the clock
-/

/-- `sup_{εW ≤ j ≤ TW} Tr Q_j` in `ℝ≥0∞`, the form of `supMoments`. -/
def nsxSupQ (b E : ℝ) (q : ℝ → ℝ) (ε T : ℝ) (W : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W),
    ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W j ω (Sum.inr 0)‖ₑ

theorem nsx_sourceTrace_eq (b E : ℝ) (q : ℝ → ℝ) {W : ℕ} (j : ℕ) (ω : GrowthPath W) :
    sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W j ω (Sum.inr 0) =
      (intervalSource b E W j q ω).trace.re := by
  simp [sourceTrace, sourceLetter, letterMatrix]

theorem nsx_measurable_supQ (b E : ℝ) (q : ℝ → ℝ) (ε T : ℝ) (W : ℕ) :
    Measurable (nsxSupQ b E q ε T W) := by
  unfold nsxSupQ
  refine Measurable.iSup fun j => Measurable.iSup fun _ => ?_
  simp_rw [nsx_sourceTrace_eq]
  exact (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (nss_measurable_intervalSource b E W j q))).enorm

/-- `Tr A_j ≤ sup Tr Q` on the window. -/
theorem nsx_trA_le_supQ (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {ε T : ℝ} {W j : ℕ}
    (hj1 : ε * W ≤ j) (hj2 : (j : ℝ) ≤ T * W) (ω : GrowthPath W) :
    ENNReal.ofReal (nearClock b E W j q ω).trace.re ≤ nsxSupQ b E q ε T W ω := by
  have hA := trace_nearClock_le b E W j q hq ω
  refine (ENNReal.ofReal_le_ofReal hA.2).trans ?_
  have e : ENNReal.ofReal (intervalSource b E W j q ω).trace.re =
      ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W j ω (Sum.inr 0)‖ₑ := by
    rw [nsx_sourceTrace_eq, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (trace_intervalSource_re_nonneg b E W j q hq ω)]
  rw [e]
  exact le_iSup₂ (f := fun (i : ℕ) (_ : ε * W ≤ i ∧ (i : ℝ) ≤ T * W) =>
    ‖sourceTrace b E (noTags W) (fun _ : Fin 1 => q) W i ω (Sum.inr 0)‖ₑ) j ⟨hj1, hj2⟩

/-!
## Uniform integrability on `ℝ≥0∞`
-/

/-- `E[1_B Y] ≤ M P(B) + E[Y; Y > M]`. -/
theorem nsx_lintegral_indicator_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : Set Ω} (hB : MeasurableSet B) (Y : Ω → ℝ≥0∞) (M : ℝ≥0∞) :
    ∫⁻ ω, B.indicator Y ω ∂μ ≤ M * μ B + ∫⁻ ω, {ω | M < Y ω}.indicator Y ω ∂μ := by
  calc ∫⁻ ω, B.indicator Y ω ∂μ ≤ ∫⁻ ω, (B.indicator (fun _ => M) ω +
        {ω | M < Y ω}.indicator Y ω) ∂μ := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ B
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
          by_cases hY : M < Y ω
          · rw [Set.indicator_of_mem (show ω ∈ {ω | M < Y ω} from hY)]; exact le_add_self
          · rw [Set.indicator_of_notMem (show ω ∉ {ω | M < Y ω} from hY)]
            simpa using not_lt.1 hY
        · rw [Set.indicator_of_notMem hω]; exact zero_le
    _ = M * μ B + ∫⁻ ω, {ω | M < Y ω}.indicator Y ω ∂μ := by
        rw [lintegral_add_left (measurable_const.indicator hB), lintegral_indicator_const hB]

/-- `E[Y; Y > M] ≤ E[Y²] / M` for `0 < M < ∞`. -/
theorem nsx_lintegral_tail_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Y : Ω → ℝ≥0∞) {M : ℝ≥0∞} (hM : M ≠ 0) :
    ∫⁻ ω, {ω | M < Y ω}.indicator Y ω ∂μ ≤ (∫⁻ ω, Y ω * Y ω ∂μ) * M⁻¹ := by
  rw [← lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hM)]
  refine lintegral_mono fun ω => ?_
  by_cases hY : M < Y ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | M < Y ω} from hY), mul_assoc]
    have hMt : M ≠ ⊤ := ne_top_of_lt hY
    have h1 : 1 ≤ Y ω * M⁻¹ := by
      calc (1 : ℝ≥0∞) = M * M⁻¹ := (ENNReal.mul_inv_cancel hM hMt).symm
        _ ≤ Y ω * M⁻¹ := by gcongr
    calc Y ω = Y ω * 1 := (mul_one _).symm
      _ ≤ Y ω * (Y ω * M⁻¹) := by gcongr
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | M < Y ω} from hY)]; exact zero_le

/-!
## The stop tail
-/

/-- **Attainment of the trace stop**: `σ_K ≤ j₂` gives a length `εW ≤ i ≤ j₂` with trace load
`> K`. -/
theorem nsx_dead_subset (b E : ℝ) (q : ℝ → ℝ) (K u₁ u₂ : ℝ) (hu₂ : 0 ≤ u₂) (W : ℕ) :
    (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ ⊆ {ω | ∃ j : ℕ, u₁ / 2 * W ≤ j ∧
      (j : ℝ) ≤ (u₂ + 1) * W ∧ K < traceLoad b E (noTags W) (fun _ : Fin 1 => q) W j ω} := by
  intro ω hω
  rw [Set.mem_compl_iff, tcw_mem_alive_iff] at hω
  push Not at hω
  obtain ⟨i, hi, h1, h2⟩ := hω
  refine ⟨i, h1, ?_, h2⟩
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : (i : ℝ) ≤ W * u₂ :=
    (Nat.cast_le.2 hi).trans (Nat.floor_le (mul_nonneg hW hu₂))
  nlinarith

/-- **The stop is late with high probability** (`tail`, attained `traceStop`). -/
theorem nsx_eventually_dead_le (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hIT : IsIntervalTests (fun _ : Fin 1 => q)) {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      growthPathLaw W b (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ ≤ ENNReal.ofReal ρ := by
  obtain ⟨C, hC⟩ := hStops.tail b hb hb1 E hE hE' 0 1 (fun _ => q) hIT (u₁ / 2) (u₂ + 1)
    (by positivity) (by linarith)
  refine ⟨(|C| + 1) / ρ, by positivity, fun K hK => ?_⟩
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hlt : ENNReal.ofReal (C / K) < ENNReal.ofReal ρ := by
    rw [ENNReal.ofReal_lt_ofReal_iff hρ, div_lt_iff₀ hK0]
    rw [div_le_iff₀ hρ] at hK
    have := le_abs_self C
    nlinarith
  filter_upwards [eventually_lt_of_limsup_lt ((hC K hK0).trans_lt hlt)] with W hW
  refine le_trans ?_ hW.le
  refine (measure_mono (nsx_dead_subset b E q K u₁ u₂ (by linarith) W)).trans ?_
  exact le_iSup (f := fun k : Fin 0 → ℕ => growthPathLaw W b {ω | ∃ j : ℕ, u₁ / 2 * W ≤ j ∧
    (j : ℝ) ≤ (u₂ + 1) * W ∧ K < traceLoad b E k (fun _ : Fin 1 => q) W j ω}) (noTags W)

/-!
## One-step jumps of `Tr(QP)`
-/

/-- The event that one step `j₁ ≤ j < j₂` of the word `Tr(QP)` jumps by more than `1`. -/
def nsxJump (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (W : ℕ) : Set (GrowthPath W) :=
  ⋃ j ∈ Finset.Ico ⌊(W : ℝ) * u₁⌋₊ ⌊(W : ℝ) * u₂⌋₊, {ω | 1 <
    ‖wordValue b E (noTags W) (fun _ : Fin 1 => q) W (j + 1) ω (clockWord 1) -
      wordValue b E (noTags W) (fun _ : Fin 1 => q) W j ω (clockWord 1)‖}

theorem nsx_measurableSet_jump (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) (W : ℕ) :
    MeasurableSet (nsxJump b E q u₁ u₂ W) := by
  refine Finset.measurableSet_biUnion _ fun j _ => measurableSet_lt measurable_const ?_
  exact ((nss_measurable_wordValue b E _ _ W (j + 1) _).sub
    (nss_measurable_wordValue b E _ _ W j _)).norm

/-- Off the jump event, one step of `Tr A` moves by at most `1`. -/
theorem nsx_trA_step_le (b E : ℝ) (q : ℝ → ℝ) (u₁ u₂ : ℝ) {W j : ℕ} {ω : GrowthPath W}
    (hω : ω ∉ nsxJump b E q u₁ u₂ W) (hj1 : ⌊(W : ℝ) * u₁⌋₊ ≤ j) (hj2 : j < ⌊(W : ℝ) * u₂⌋₊) :
    (nearClock b E W (j + 1) q ω).trace.re ≤ (nearClock b E W j q ω).trace.re + 1 := by
  have h : ¬ 1 < ‖wordValue b E (noTags W) (fun _ : Fin 1 => q) W (j + 1) ω (clockWord 1) -
      wordValue b E (noTags W) (fun _ : Fin 1 => q) W j ω (clockWord 1)‖ := fun h =>
    hω (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨hj1, hj2⟩)) h)
  rw [not_lt, nsx_wordValue_clockWord_one, nsx_wordValue_clockWord_one] at h
  have := (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re] at this
  linarith [le_abs_self ((nearClock b E W (j + 1) q ω).trace.re -
    (nearClock b E W j q ω).trace.re)]

/-- With the injection ending at time `0`, the source vanishes at every positive width. -/
theorem nsx_wordValue_eq_zero_of_origin {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q)
    (h0 : t₁ + R = 0) (b E : ℝ) {W : ℕ} (hW : 0 < W) (j : ℕ) (ω : GrowthPath W) :
    wordValue b E (noTags W) (fun _ : Fin 1 => q) W j ω (clockWord 1) = 0 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hQ : intervalSource b E W j q ω = 0 := by
    unfold intervalSource
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : q (((k + 1 : ℕ) : ℝ) / W) = 0 := hq.2.2.2.1.2.1 _ fun h => by
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / W := by positivity
      linarith [h.2]
    rw [hk]; simp
  rw [nsx_wordValue_clockWord_one]
  simp [nearClock, hQ, portBlock, Matrix.trace]

/-- **One-step form of `tight`** for the word `Tr(QP)`: the probability of a jump `> 1` on
`[j₁, j₂)` tends to `0`. -/
theorem nsx_eventually_jump_le (hGen : FullSourceGeneratorContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ} (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ᶠ W : ℕ in atTop, growthPathLaw W b (nsxJump b E q u₁ u₂ W) ≤ ENNReal.ofReal ρ := by
  have ht0 : 0 ≤ t₁ + R := add_nonneg hq.1 hq.2.1
  rcases ht0.lt_or_eq with ht0 | ht0
  · obtain ⟨δt, hδt, W₀, hW₀⟩ := (hGen.tight b hb hb1 E hE hE' (t₁ + R) ht0 0 1 (fun _ => q)
      (fun _ => ⟨t₁, hq.2.2.2.1⟩) noTags (Eventually.of_forall fun W a => a.elim0)
      (clockWord 1) nsx_ordinary_clockWord_one (t₁ + R) (u₂ + 1) le_rfl (by linarith)).2
      1 ρ one_pos hρ
    filter_upwards [eventually_ge_atTop W₀, eventually_ge_atTop ⌈1 / δt⌉₊,
      eventually_ge_atTop ⌈1 / (u₁ - (t₁ + R))⌉₊, eventually_gt_atTop 0] with W h1 h2 h3 h4
    refine (measure_mono ?_).trans (hW₀ W h1)
    have hW' : (0 : ℝ) < W := by exact_mod_cast h4
    have h2' : 1 / δt ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast h2)
    have h3' : 1 / (u₁ - (t₁ + R)) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast h3)
    rw [div_le_iff₀ hδt] at h2'
    rw [div_le_iff₀ (by linarith)] at h3'
    intro ω hω
    simp only [nsxJump, Set.mem_iUnion, Finset.mem_Ico, Set.mem_ofPred_eq] at hω
    obtain ⟨j, ⟨hj1, hj2⟩, hjump⟩ := hω
    have hj1' : (W : ℝ) * u₁ < (j : ℝ) + 1 :=
      (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.add_le_add_right hj1 1)
    have hj2' : ((j + 1 : ℕ) : ℝ) ≤ W * u₂ :=
      (Nat.cast_le.2 hj2).trans (Nat.floor_le (mul_nonneg hW'.le (by linarith)))
    push_cast at hj2'
    have e1 : ⌊(W : ℝ) * (((j + 1 : ℕ) : ℝ) / W)⌋₊ = j + 1 := by
      rw [mul_div_cancel₀ _ hW'.ne']; exact Nat.floor_natCast _
    have e2 : ⌊(W : ℝ) * ((j : ℝ) / W)⌋₊ = j := by
      rw [mul_div_cancel₀ _ hW'.ne']; exact Nat.floor_natCast _
    have hlo : t₁ + R ≤ (j : ℝ) / W := by rw [le_div_iff₀ hW']; nlinarith
    refine ⟨((j + 1 : ℕ) : ℝ) / W, ⟨?_, ?_⟩, (j : ℝ) / W, ⟨hlo, ?_⟩, ?_, ?_⟩
    · refine hlo.trans (div_le_div_of_nonneg_right ?_ hW'.le); push_cast; linarith
    · rw [div_le_iff₀ hW']; push_cast; nlinarith
    · rw [div_le_iff₀ hW']; nlinarith
    · rw [← sub_div, abs_div, abs_of_pos hW', div_le_iff₀ hW']; push_cast
      rw [show (j : ℝ) + 1 - j = 1 by ring, abs_one]; linarith
    · rw [e1, e2]; exact hjump
  · filter_upwards [eventually_gt_atTop 0] with W hW
    have : nsxJump b E q u₁ u₂ W = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
      simp only [nsxJump, Set.mem_iUnion, Set.mem_ofPred_eq] at hω
      obtain ⟨j, -, hjump⟩ := hω
      rw [nsx_wordValue_eq_zero_of_origin hq ht0.symm b E hW,
        nsx_wordValue_eq_zero_of_origin hq ht0.symm b E hW] at hjump
      norm_num at hjump
    rw [this, measure_empty]; exact zero_le

/-!
## Uniform integrability against small events
-/

/-- **Uniform integrability on small events**: a uniformly integrable family `Y_W`
(`∀ η, ∃ M, E[Y_W; Y_W > M] ≤ η` for large `W`) has `E[1_B Y_W] ≤ θ` on every event of
probability `≤ ρ(θ)`, for large `W`. -/
theorem nsx_ui_core {b : ℝ} (Y : (W : ℕ) → GrowthPath W → ℝ≥0∞)
    (hUI : ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < Y W ω}.indicator (Y W) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal η)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ B : Set (GrowthPath W), MeasurableSet B →
      growthPathLaw W b B ≤ ENNReal.ofReal ρ →
        ∫⁻ ω, B.indicator (Y W) ω ∂growthPathLaw W b ≤ ENNReal.ofReal θ := by
  obtain ⟨M, W₀, hM⟩ := hUI (θ / 2) (by positivity)
  refine ⟨θ / (2 * (|M| + 1)), by positivity, W₀, fun W hW B hB hBρ => ?_⟩
  have hρ : |M| * (θ / (2 * (|M| + 1))) ≤ θ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [abs_nonneg M]
  calc ∫⁻ ω, B.indicator (Y W) ω ∂growthPathLaw W b
      ≤ ENNReal.ofReal M * growthPathLaw W b B +
          ∫⁻ ω, {ω | ENNReal.ofReal M < Y W ω}.indicator (Y W) ω ∂growthPathLaw W b :=
        nsx_lintegral_indicator_le hB _ _
    _ ≤ ENNReal.ofReal |M| * ENNReal.ofReal (θ / (2 * (|M| + 1))) + ENNReal.ofReal (θ / 2) := by
        gcongr
        · exact le_abs_self M
        · exact hM W hW
    _ = ENNReal.ofReal (|M| * (θ / (2 * (|M| + 1))) + θ / 2) := by
        rw [← ENNReal.ofReal_mul (abs_nonneg M), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal θ := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Second moments give uniform integrability.** -/
theorem nsx_ui_of_moment {b : ℝ} (Z : (W : ℕ) → GrowthPath W → ℝ≥0∞)
    (hmom : ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, Z W ω * Z W ω ∂growthPathLaw W b ≤ ENNReal.ofReal C) :
    ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < Z W ω}.indicator (Z W) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal η := by
  intro η hη
  obtain ⟨C, W₀, hC⟩ := hmom
  have hM : 0 < (|C| + 1) / η := by positivity
  refine ⟨(|C| + 1) / η, W₀, fun W hW => ?_⟩
  calc _ ≤ (∫⁻ ω, Z W ω * Z W ω ∂growthPathLaw W b) * (ENNReal.ofReal ((|C| + 1) / η))⁻¹ :=
        nsx_lintegral_tail_le _ (ENNReal.ofReal_pos.2 hM).ne'
    _ ≤ ENNReal.ofReal |C| * ENNReal.ofReal (((|C| + 1) / η)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos hM]
        gcongr
        exact (hC W hW).trans (ENNReal.ofReal_le_ofReal (le_abs_self C))
    _ = ENNReal.ofReal (|C| * ((|C| + 1) / η)⁻¹) := (ENNReal.ofReal_mul (abs_nonneg C)).symm
    _ ≤ ENNReal.ofReal η := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_div, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]

/-- **Moments of the clock supremum** (`supMoments` at `p = 2(n+1)`). -/
theorem nsx_supQ_moment (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hIT : IsIntervalTests (fun _ : Fin 1 => q)) {ε T : ℝ} (hε : 0 < ε) (hεT : ε < T) (n : ℕ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, nsxSupQ b E q ε T W ω ^ (n + 1) * nsxSupQ b E q ε T W ω ^ (n + 1)
        ∂growthPathLaw W b ≤ ENNReal.ofReal C := by
  obtain ⟨C, W₀, hC⟩ := hStops.supMoments b hb hb1 E hE hE' 0 1 (fun _ => q) hIT ε T
    (((n + 1 + (n + 1) : ℕ) : ℝ)) hε hεT (by positivity)
  refine ⟨C, W₀, fun W hW => ?_⟩
  have h := hC W hW (noTags W) (Sum.inr 0)
  simp only [ENNReal.rpow_natCast] at h
  simp only [← pow_add]
  exact h

/-- **A uniformly integrable family is small after the stop, for large `K`** (`tail`). -/
theorem nsx_dead_small (hStops : FullSourceStopsContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {q : ℝ → ℝ}
    (hIT : IsIntervalTests (fun _ : Fin 1 => q)) {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu : u₁ ≤ u₂)
    (Y : (W : ℕ) → GrowthPath W → ℝ≥0∞)
    (hUI : ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < Y W ω}.indicator (Y W) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal η)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ W : ℕ in atTop,
      ∫⁻ ω, (nsfAlive b E q K u₁ W ⌊(W : ℝ) * u₂⌋₊)ᶜ.indicator (Y W) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal θ := by
  obtain ⟨ρ, hρ, W₀, hW₀⟩ := nsx_ui_core Y hUI hθ
  obtain ⟨K₀, hK₀, hK⟩ := nsx_eventually_dead_le hStops hb hb1 hE hE' hIT hu₁ hu hρ
  refine ⟨K₀, hK₀, fun K hKK => ?_⟩
  filter_upwards [hK K hKK, eventually_ge_atTop W₀] with W hW hW'
  exact hW₀ W hW' _ (nss_measurableSet_alive b E (noTags W) q K (u₁ / 2) W _).compl hW

/-- **A uniformly integrable family is small on the jump event** (`tight`). -/
theorem nsx_jump_small (hGen : FullSourceGeneratorContract) {b E : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) {u₁ u₂ : ℝ} (hu₁ : t₁ + R < u₁) (hu : u₁ ≤ u₂)
    (Y : (W : ℕ) → GrowthPath W → ℝ≥0∞)
    (hUI : ∀ η : ℝ, 0 < η → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∫⁻ ω, {ω | ENNReal.ofReal M < Y W ω}.indicator (Y W) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal η)
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ W : ℕ in atTop,
      ∫⁻ ω, (nsxJump b E q u₁ u₂ W).indicator (Y W) ω ∂growthPathLaw W b ≤ ENNReal.ofReal θ := by
  obtain ⟨ρ, hρ, W₀, hW₀⟩ := nsx_ui_core Y hUI hθ
  filter_upwards [nsx_eventually_jump_le hGen hb hb1 hE hE' hq hu₁ hu hρ,
    eventually_ge_atTop W₀] with W hW hW'
  exact hW₀ W hW' _ (nsx_measurableSet_jump b E q u₁ u₂ W) hW

end BlockBand.Endpoints
