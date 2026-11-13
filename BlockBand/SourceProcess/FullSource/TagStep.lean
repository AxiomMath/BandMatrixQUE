module

public import BlockBand.SourceProcess.FullSource.TagPath

/-!
# One stopped step of the weighted tag recursion

`stopped_tag_step`: for `j ≥ k+1`, `E[1_{G_{j+1}}Z_{j+1}] ≤ (1 + α/W) E[1_{G_j}Z_j]`. The proof
combines the almost-sure transport (`ae_tagResponse_succ_full`), the scalar step (`ae_pathX_succ`
and the mean step on `δ_j ≤ d ≤ d₀`) and the Fubini step `lintegral_indicator_step` with the
one-layer `weighted_layer_step`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem tagMass_eq_past (b E : ℝ) (j k : ℕ) (ω : GrowthPath W) :
    tagMass b E W j k ω = (W : ℝ)⁻¹ * ((pastS b E W j k (pastCoords W j ω))ᴴ *
      pastS b E W j k (pastCoords W j ω)).trace.re := by
  rw [tagMass, tagResponse_eq_factor]

theorem pathDelta_eq_past (b E : ℝ) (j : ℕ) (ω : GrowthPath W) :
    pathDelta b E W j ω = jetDistance0 b E (nearSchur (boundaryZ b E)
      (pastXX E W j (pastCoords W j ω))) := by
  rw [pathDelta, pathX_eq_past]

/-- The weight as a function of the past: `Z_j = tagPsi ∘ pastCoords`. -/
def tagPsi (b E : ℝ) (W j k n : ℕ) (K : ℝ) (p : PastSample W j) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p))) *
    ((W : ℝ)⁻¹ * ((pastS b E W j k p)ᴴ * pastS b E W j k p).trace.re) ^ n)

theorem measurable_tagPsi (b E : ℝ) (j k n : ℕ) (K : ℝ) : Measurable (tagPsi b E W j k n K) := by
  have hX := measurable_nearSchur_comp (boundaryZ b E) (measurable_pastXX (W := W) E j)
  have hS := measurable_pastS (W := W) b E j k
  have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
  unfold tagPsi
  refine ((measurable_const.add (measurable_const.mul
    ((measurable_jetDistance0 b E).comp hX))).mul ((measurable_const.mul ?_).pow_const n)).ennreal_ofReal
  simp only [Matrix.trace, Matrix.diag]
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hT.eval_matrix)

theorem tagWeight_eq (b E : ℝ) (k n : ℕ) (K : ℝ) (j : ℕ) :
    tagWeight b E W k n K j = tagPsi b E W j k n K ∘ pastCoords W j := by
  funext ω; simp only [tagWeight, tagPsi, Function.comp, tagMass_eq_past, pathDelta_eq_past]

theorem measurable_tagWeight (b E : ℝ) (k n : ℕ) (K : ℝ) (j : ℕ) :
    Measurable (tagWeight b E W k n K j) := by
  rw [tagWeight_eq]; exact (measurable_tagPsi b E j k n K).comp (measurable_pastCoords W j)

/-- **One stopped step of the weighted tag recursion.** -/
theorem stopped_tag_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {n k j : ℕ} (hW : 1 ≤ W) (hn : 2 ≤ n) (hkj : k + 1 ≤ j)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W n Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lcoef Ca n ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lcoef Ca n * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) :
    ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (tagWeight b E W k n K (j + 1)) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaW K Cm Ca C₂ Cn Cf CN n / W) *
        ∫⁻ ω, (stopEv b E W k d j).indicator (tagWeight b E W k n K j) ω ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set α := alphaW K Cm Ca C₂ Cn Cf CN n
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hα : 0 ≤ α := by
    have := lcoef_nonneg hCa n; have := acoef_nonneg (C₂ := C₂) hCa hCn n
    simp only [α, alphaW]; positivity
  set Ψ : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (1 + α / W) *
    tagPsi b E W j k n K p with hΨ
  have hmΨ : Measurable Ψ := measurable_const.mul (measurable_tagPsi b E j k n K)
  -- shrink the event
  have h1 : ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (tagWeight b E W k n K (j + 1)) ω ∂μ ≤
      ∫⁻ ω, (stopEv b E W k d j).indicator (tagWeight b E W k n K (j + 1)) ω ∂μ :=
    lintegral_mono fun ω => Set.indicator_le_indicator_of_subset
      (stopEv_succ_subset b E k d j) (fun _ => zero_le) ω
  refine h1.trans ?_
  rw [stopEv_eq]
  -- Fubini
  have hZ : ∀ᵐ ω ∂μ, pastCoords W j ω ∈ stopPast b E W k d j →
      tagWeight b E W k n K (j + 1) ω ≤ tagPhi b E W j k n K ρ Cm
        (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_tagResponse_succ_full hb0 hb hE1 hE2 hW, ae_pathX_succ hb hE1 hE2 hW,
      ae_growth_isHermitian W b] with ω h1 h2 h3 hG
    have hG' : ω ∈ stopEv b E W k d j := by rw [stopEv_eq]; exact hG
    have hp : pastCoords W j ω ∈ hermPast W j := fun l => h3 l
    set p := pastCoords W j ω
    set X := nearSchur (boundaryZ b E) (pastXX E W j p)
    have hXp : (passiveY X).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have hδj : jetDistance0 b E X ≤ d := by
      have := hG' j hkj le_rfl; rwa [pathDelta_eq_past] at this
    -- the transported tag
    have ht : tagMass b E W (j + 1) k ω = tagPlus b E (pastXX E W j p) (pastS b E W j k p)
        (freshSample W j ω) := by
      rw [tagMass, h1 j (by omega) k (by omega), tagResponse_eq_factor, transportN, pastXX_eq,
        tagPlus, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rfl
    -- the scalar step
    have hδ : pathDelta b E W (j + 1) ω ≤ ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 +
        freshXi b E X (freshSample W j ω) := by
      rw [pathDelta, h2 j (by omega), jetDistance0_freshSchur, pathX_eq_past]
      have hm := hL.meanStep X hXp (hδj.trans hdd₀)
      have := norm_sub_le (freshPortTrace b E X (freshSample W j ω) -
        ∫ f, freshPortTrace b E X f ∂freshLaw W b)
        (matchedA E - ∫ f, freshPortTrace b E X f ∂freshLaw W b)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (matchedA E)] at this
      simp only [freshXi]
      linarith
    rw [tagWeight, tagPhi, ht]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (pow_nonneg (tagPlus_nonneg _ _ _ _ _) n))
    have := mul_le_mul_of_nonneg_left hδ hK
    linarith
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ stopPast b E W k d j →
      ∫⁻ f, tagPhi b E W j k n K ρ Cm (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp hG
    have hXX := pastXX_isHermitian E hp
    have hδ : jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)) ≤ d := by
      have := hG j le_rfl hkj
      rwa [show restrictPast le_rfl p = p from rfl, pastX_zero_eq] at this
    have hXp : (passiveY (nearSchur (boundaryZ b E) (pastXX E W j p))).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have h := weighted_layer_step (pastXX E W j p) (pastS b E W j k p) hn hW1 hCa hC₂ hCn hCN
      hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hδ (hL.mean _ hXX) (hL.fl₂ _ hXX (hδ.trans hdd₀))
      (hL.fln _ hXX (hδ.trans hdd₀))
      (hL.N₂ _ hXX) (hL.N _ hXX) (hL.xi _ hXp)
    refine h.trans (le_of_eq ?_)
    simp only [Ψ, tagPsi]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hstepI := lintegral_indicator_step (μ := μ) (μP := pastLaw W j b) (ν := freshLaw W b)
    (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) (measurableSet_stopPast b E k d j)
    (measurable_tagPhi b E j k n K ρ Cm) hmΨ hZ hstep
  refine hstepI.trans (le_of_eq ?_)
  rw [← lintegral_const_mul _ ((measurable_tagWeight b E k n K j).indicator
    ((measurableSet_stopPast b E k d j).preimage (measurable_pastCoords W j)))]
  congr 1; funext ω
  by_cases hω : ω ∈ pastCoords W j ⁻¹' stopPast b E W k d j
  · simp only [Set.indicator_of_mem hω, Ψ, tagWeight_eq, Function.comp]
  · simp only [Set.indicator_of_notMem hω, mul_zero]

end BlockBand.SourceProcess.FullSource
