module

public import BlockBand.SourceProcess.FullSourceStops.Ville
public import BlockBand.SourceProcess.FullSourceStops.StepOn
public import BlockBand.SourceProcess.FullSourceStops.SupTools
public import BlockBand.SourceProcess.FullSource.TagBulk

/-!
# The supremum of one tag at one width

The tag `k` with weight exponent `2n`. `Y_i = 1_{G_{k+1+i}}(1 + Kδ_{k+1+i})t_{k+1+i}^{2n}` is a
weighted supermartingale against past events (`stopped_tag_step_on`), so `ville` bounds its
running maximum. On the stop `G = G_N` the `2n`-th power of `sup_{j ≤ N} t_j` is below that
maximum, so `4^i P(G, sup t^n ≥ 2^i) ≤ A` and the dyadic lemma gives `E[1_G sup t^n] ≤ 1 + 4A`.
Off the stop, Cauchy–Schwarz with `sup^{2n} ≤ Σ_j t_j^{2n}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped ENNReal

variable {W : ℕ}

/-- The stopped weights of the tag `k`, indexed from its birth length `k+1`. -/
def stoppedWeight (b E : ℝ) (W k m : ℕ) (K d : ℝ) (i : ℕ) : GrowthPath W → ℝ≥0∞ :=
  (stopEv b E W k d (k + 1 + i)).indicator (tagWeight b E W k m K (k + 1 + i))

theorem measurable_stoppedWeight (b E : ℝ) (k m : ℕ) (K d : ℝ) (i : ℕ) :
    Measurable (stoppedWeight b E W k m K d i) :=
  (measurable_tagWeight b E k m K _).indicator (measurableSet_stopEv b E k d _)

theorem stoppedWeight_apply (b E : ℝ) (k m : ℕ) (K d : ℝ) (i : ℕ) (ω : GrowthPath W) :
    stoppedWeight b E W k m K d i ω = (stopPast b E W k d (k + 1 + i)).indicator
      (tagPsi b E W (k + 1 + i) k m K) (pastCoords W (k + 1 + i) ω) := by
  rw [stoppedWeight, stopEv_eq, tagWeight_eq]
  by_cases h : pastCoords W (k + 1 + i) ω ∈ stopPast b E W k d (k + 1 + i)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.mp h'))]

/-- The no-hit event of the stopped weights is a past event. -/
theorem noHit_stoppedWeight (b E : ℝ) (k m : ℕ) (K d : ℝ) (lam : ℝ≥0∞) (i : ℕ) :
    ∃ B : Set (PastSample W (k + 1 + i)), MeasurableSet B ∧
      noHit (stoppedWeight b E W k m K d) lam i = pastCoords W (k + 1 + i) ⁻¹' B := by
  refine ⟨{p | ∀ i' (h : i' ≤ i), (stopPast b E W k d (k + 1 + i')).indicator
      (tagPsi b E W (k + 1 + i') k m K) (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) <
        lam}, ?_, ?_⟩
  · have : {p : PastSample W (k + 1 + i) | ∀ i' (h : i' ≤ i), (stopPast b E W k d (k + 1 + i')).indicator
        (tagPsi b E W (k + 1 + i') k m K) (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) <
          lam} = ⋂ i', ⋂ (h : i' ≤ i), {p | (stopPast b E W k d (k + 1 + i')).indicator
        (tagPsi b E W (k + 1 + i') k m K) (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) <
          lam} := by ext p; simp
    rw [this]
    exact MeasurableSet.iInter fun i' => MeasurableSet.iInter fun h => measurableSet_lt
      ((((measurable_tagPsi b E _ k m K).indicator (measurableSet_stopPast b E k d _))).comp
        (measurable_restrictPast _)) measurable_const
  · ext ω
    simp only [noHit, Set.mem_preimage, stoppedWeight_apply]
    rfl

/-- **The stopped weights are a weighted supermartingale against their no-hit events.** -/
theorem stoppedWeight_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {m k : ℕ} (hW : 1 ≤ W) (hm : 2 ≤ m)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W m Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lcoef Ca m ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca m * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (lam : ℝ≥0∞) (i : ℕ) :
    ∫⁻ ω, (noHit (stoppedWeight b E W k m K d) lam i).indicator
        (stoppedWeight b E W k m K d (i + 1)) ω ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaW K Cm Ca C₂ Cn Cf CN m / W) *
        ∫⁻ ω, (noHit (stoppedWeight b E W k m K d) lam i).indicator
          (stoppedWeight b E W k m K d i) ω ∂growthPathLaw W b := by
  obtain ⟨B, hB, hBe⟩ := noHit_stoppedWeight (W := W) b E k m K d lam i
  rw [hBe]
  simp only [stoppedWeight, Set.indicator_indicator]
  exact stopped_tag_step_on hb0 hb hE1 hE2 (j := k + 1 + i) hW hm (by omega) hL hCa hC₂ hCn hCN
    hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hdd₀ hB

/-- The finite supremum `sup_{j ≤ N} t_j` of the tag `k`. -/
def tagSup (b E : ℝ) (W k N : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ⨆ (j : ℕ) (_ : j ≤ N), ENNReal.ofReal (tagMass b E W j k ω)

theorem measurable_tagSup (b E : ℝ) (k N : ℕ) : Measurable (tagSup b E W k N) :=
  Measurable.iSup fun j => Measurable.iSup_Prop _ (measurable_tagMass b E j k).ennreal_ofReal

theorem alphaW_nonneg {K Cm Ca C₂ Cn Cf CN : ℝ} (hK : 0 ≤ K) (hCm : 0 ≤ Cm) (hCa : 0 ≤ Ca)
    (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (m : ℕ) : 0 ≤ alphaW K Cm Ca C₂ Cn Cf CN m := by
  have h1 := acoef_nonneg (C₂ := C₂) hCa hCn m
  have h2 := lcoef_nonneg hCa m
  have h3 : 0 ≤ Cf ^ 2 + CN ^ (2 * (2 * m)) := by positivity
  simp only [alphaW]; positivity

/-- **On the stop**: `E[1_G (sup_{j ≤ N} t_j)^n] ≤ 1 + 4A`, `A = e^{αR}(1 + Kd)B_{2n}`. -/
theorem lintegral_good_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {n k : ℕ} (hW : 1 ≤ W) (hn : 1 ≤ n)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ}
    (hL : TagLayerBounds b E W (2 * n) Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lcoef Ca (2 * n) ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca (2 * n) * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (hd0 : 0 ≤ d)
    {N : ℕ} {R : ℝ} (hNR : (N : ℝ) ≤ R * W) {Bm : ℝ}
    (hbm : ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ (2 * n)) ∂growthPathLaw W b ≤
      ENNReal.ofReal Bm) :
    ∫⁻ ω, (stopEv b E W k d N).indicator (fun ω => tagSup b E W k N ω ^ n) ω ∂growthPathLaw W b ≤
      1 + 4 * ENNReal.ofReal
        (Real.exp (alphaW K Cm Ca C₂ Cn Cf CN (2 * n) * R) * ((1 + K * d) * Bm)) := by
  set μ := growthPathLaw W b
  set α := alphaW K Cm Ca C₂ Cn Cf CN (2 * n)
  have hα : 0 ≤ α := alphaW_nonneg hK hCm hCa hCn hCN _
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hn0 : n ≠ 0 := by omega
  by_cases hNk : N < k + 1
  · have h0 : ∀ ω, tagSup b E W k N ω = 0 := fun ω => by
      refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
      rw [tagMass_eq_zero_of_le b E (by omega) ω, ENNReal.ofReal_zero]
    simp only [h0, zero_pow hn0, Set.indicator_zero, lintegral_zero]
    exact bot_le
  obtain ⟨N', rfl⟩ : ∃ N', N = k + 1 + N' := ⟨N - (k + 1), by omega⟩
  set Y := stoppedWeight b E W k (2 * n) K d
  set c := ENNReal.ofReal (1 + α / W)
  have hc : 1 ≤ c := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  have hcN : c ^ N' ≤ ENNReal.ofReal (Real.exp (α * R)) := by
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal (one_add_pow_le_exp hα N' hW0 ?_)
    have : (N' : ℝ) ≤ ((k + 1 + N' : ℕ) : ℝ) := by exact_mod_cast (by omega : N' ≤ k + 1 + N')
    linarith
  have hY0 : ∫⁻ ω, Y 0 ω ∂μ ≤ ENNReal.ofReal ((1 + K * d) * Bm) := by
    have hpt : ∀ ω, Y 0 ω ≤ ENNReal.ofReal (1 + K * d) *
        ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ (2 * n)) := by
      intro ω
      simp only [Y, stoppedWeight, Nat.add_zero]
      by_cases hω : ω ∈ stopEv b E W k d (k + 1)
      · rw [Set.indicator_of_mem hω, tagWeight, ← ENNReal.ofReal_mul (by nlinarith [mul_nonneg hK hd0])]
        have hδ := hω (k + 1) le_rfl le_rfl
        have ht := pow_nonneg (tagMass_nonneg b E (k + 1) k ω) (2 * n)
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by nlinarith) ht)
      · rw [Set.indicator_of_notMem hω]; exact bot_le
    calc ∫⁻ ω, Y 0 ω ∂μ ≤ ∫⁻ ω, ENNReal.ofReal (1 + K * d) *
          ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ (2 * n)) ∂μ := lintegral_mono hpt
      _ = ENNReal.ofReal (1 + K * d) *
          ∫⁻ ω, ENNReal.ofReal (tagMass b E W (k + 1) k ω ^ (2 * n)) ∂μ :=
          lintegral_const_mul _ ((measurable_tagMass b E _ k).pow_const _).ennreal_ofReal
      _ ≤ ENNReal.ofReal (1 + K * d) * ENNReal.ofReal Bm := by gcongr
      _ = ENNReal.ofReal ((1 + K * d) * Bm) := by
          rw [ENNReal.ofReal_mul (by nlinarith [mul_nonneg hK hd0])]
  have hX : Measurable ((stopEv b E W k d (k + 1 + N')).indicator
      fun ω => tagSup b E W k (k + 1 + N') ω ^ n) :=
    ((measurable_tagSup b E k _).pow_const n).indicator (measurableSet_stopEv b E k d _)
  refine lintegral_le_of_dyadic_tail μ hX _ fun i => ?_
  have h2pos : (0 : ℝ≥0∞) < 2 ^ i := pos_iff_ne_zero.mpr (pow_ne_zero _ two_ne_zero)
  have h4pos : (0 : ℝ≥0∞) < 4 ^ i := pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  have hsub : {ω | (2 : ℝ≥0∞) ^ i ≤ (stopEv b E W k d (k + 1 + N')).indicator
      (fun ω => tagSup b E W k (k + 1 + N') ω ^ n) ω} ⊆ (noHit Y (4 ^ i) N')ᶜ := by
    intro ω hω
    have hG : ω ∈ stopEv b E W k d (k + 1 + N') := by
      by_contra h
      have hω' : (2 : ℝ≥0∞) ^ i ≤ 0 := by
        have := hω; simp only [Set.mem_ofPred_eq, Set.indicator_of_notMem h] at this; exact this
      exact absurd hω' (not_le.mpr h2pos)
    have hω1 : (2 : ℝ≥0∞) ^ i ≤ tagSup b E W k (k + 1 + N') ω ^ n := by
      have := hω; simp only [Set.mem_ofPred_eq, Set.indicator_of_mem hG] at this; exact this
    have h4 : (4 : ℝ≥0∞) ^ i ≤ tagSup b E W k (k + 1 + N') ω ^ (2 * n) := by
      have e : (4 : ℝ≥0∞) ^ i = ((2 : ℝ≥0∞) ^ i) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [e, mul_comm, pow_mul]
      exact pow_le_pow_left₀ bot_le hω1 2
    obtain ⟨j, hjN, hj⟩ := exists_le_pow_of_le_iSup_pow
      (fun j => ENNReal.ofReal (tagMass b E W j k ω)) _ (2 * n) (by omega) h4pos h4
    have hkj : k + 1 ≤ j := by
      by_contra h
      rw [tagMass_eq_zero_of_le b E (by omega) ω, ENNReal.ofReal_zero, zero_pow (by omega)] at hj
      exact absurd hj (not_le.mpr h4pos)
    obtain ⟨i', rfl⟩ : ∃ i', j = k + 1 + i' := ⟨j - (k + 1), by omega⟩
    rw [compl_noHit]
    refine ⟨i', by omega, hj.trans ?_⟩
    have hmem : ω ∈ stopEv b E W k d (k + 1 + i') := fun l h1 h2 => hG l h1 (by omega)
    simp only [Y, stoppedWeight]
    rw [Set.indicator_of_mem hmem, tagWeight,
      ← ENNReal.ofReal_pow (tagMass_nonneg b E (k + 1 + i') k ω)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hδ : 0 ≤ pathDelta b E W (k + 1 + i') ω := norm_nonneg _
    have ht := pow_nonneg (tagMass_nonneg b E (k + 1 + i') k ω) (2 * n)
    nlinarith [mul_nonneg (mul_nonneg hK hδ) ht]
  show _ ≤ ENNReal.ofReal (Real.exp (α * R) * ((1 + K * d) * Bm))
  calc (4 : ℝ≥0∞) ^ i * μ {ω | (2 : ℝ≥0∞) ^ i ≤ (stopEv b E W k d (k + 1 + N')).indicator
        (fun ω => tagSup b E W k (k + 1 + N') ω ^ n) ω}
      ≤ 4 ^ i * μ (noHit Y (4 ^ i) N')ᶜ := by gcongr
    _ ≤ c ^ N' * ∫⁻ ω, Y 0 ω ∂μ :=
        ville μ (measurable_stoppedWeight b E k (2 * n) K d) _ c hc
          (stoppedWeight_step hb0 hb hE1 hE2 hW (by omega) hL hCa hC₂ hCn hCN hCf hCm hK hρ0
            hρ1 hKL hd1 hρLd hdd₀ _) N'
    _ ≤ ENNReal.ofReal (Real.exp (α * R)) * ENNReal.ofReal ((1 + K * d) * Bm) := by gcongr
    _ = ENNReal.ofReal (Real.exp (α * R) * ((1 + K * d) * Bm)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

/-- **Off the stop**: Cauchy–Schwarz with `sup^{2n} ≤ Σ_{j ≤ N} t_j^{2n}`. -/
theorem lintegral_bad_le (b E : ℝ) (k N n : ℕ) (hn : 1 ≤ n) (d : ℝ) {Mc P : ℝ}
    (hmom : ∀ j, j ≤ N → ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω) ^ (2 * n)
      ∂growthPathLaw W b ≤ ENNReal.ofReal Mc)
    (hP : growthPathLaw W b (stopEv b E W k d N)ᶜ ≤ ENNReal.ofReal P) :
    ∫⁻ ω, (stopEv b E W k d N)ᶜ.indicator (fun ω => tagSup b E W k N ω ^ n) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (((N : ℝ) + 1) * Mc) ^ (1 / 2 : ℝ) * ENNReal.ofReal P ^ (1 / 2 : ℝ) := by
  refine (lintegral_compl_indicator_le _ (measurableSet_stopEv b E k d N)
    ((measurable_tagSup b E k N).pow_const n)).trans ?_
  gcongr
  calc ∫⁻ ω, (tagSup b E W k N ω ^ n) ^ 2 ∂growthPathLaw W b
      ≤ ∫⁻ ω, ∑ j ∈ Finset.range (N + 1), ENNReal.ofReal (tagMass b E W j k ω) ^ (2 * n)
          ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [← pow_mul, mul_comm]
        exact iSup_pow_le_sum _ N (2 * n) (by omega)
    _ = ∑ j ∈ Finset.range (N + 1), ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω) ^ (2 * n)
          ∂growthPathLaw W b :=
        lintegral_finsetSum _ fun j _ => ((measurable_tagMass b E j k).ennreal_ofReal).pow_const _
    _ ≤ ∑ _j ∈ Finset.range (N + 1), ENNReal.ofReal Mc :=
        Finset.sum_le_sum fun j hj => hmom j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ENNReal.ofReal (((N : ℝ) + 1) * Mc) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
        push_cast; rfl

end BlockBand.SourceProcess.FullSourceStops
