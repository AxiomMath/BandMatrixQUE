module

public import BlockBand.SourceProcess.FullSource.SqPath

/-!
# One stopped step of the weighted tag-square recursion

`stopped_sq_step`: for `j ≥ k+1`,
`E[1_{G_{j+1}}Z^h_{j+1}] ≤ (1 + α/W)E[1_{G_j}Z^h_j] + D E t_j²`, by the pattern of
`stopped_tag_step` (transport `ae_tagResponse_succ_full`, scalar step `ae_pathX_succ` with the
mean step on `δ_j ≤ d ≤ d₀`, Fubini `lintegral_indicator_step`) and the one-layer
`sq_weighted_layer_step`. The one-layer inputs are `TagLayerBounds` at `n = 2`.
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

/-- **One stopped step of the weighted tag-square recursion.** -/
theorem stopped_sq_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k j : ℕ} (hW : 1 ≤ W) (hkj : k + 1 ≤ j)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : lsq Ca ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * lsq Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) :
    ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (sqWeight b E W k K (j + 1)) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaSq K Cm Ca Cf CN / W) *
        ∫⁻ ω, (stopEv b E W k d j).indicator (sqWeight b E W k K j) ω ∂growthPathLaw W b +
      ENNReal.ofReal (dsq K Cm C₂ ρ) *
        ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω ^ 2) ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set α := alphaSq K Cm Ca Cf CN
  set D := dsq K Cm C₂ ρ
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hα : 0 ≤ α := alphaSq_nonneg hK hCm hCa hCN
  have hD : 0 ≤ D := by simp only [D, dsq]; positivity
  set τ : PastSample W j → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (((W : ℝ)⁻¹ * ((pastS b E W j k p)ᴴ * pastS b E W j k p).trace.re) ^ 2)
  have hmτ : Measurable τ := by
    have hS := measurable_pastS (W := W) b E j k
    have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
    refine ((measurable_const.mul ?_).pow_const 2).ennreal_ofReal
    simp only [Matrix.trace, Matrix.diag]
    exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hT.eval_matrix)
  set Ψ : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (1 + α / W) *
    sqPsi b E W j k K p + ENNReal.ofReal D * τ p with hΨ
  have hmΨ : Measurable Ψ :=
    (measurable_const.mul (measurable_sqPsi b E j k K)).add (measurable_const.mul hmτ)
  -- shrink the event
  have h1 : ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (sqWeight b E W k K (j + 1)) ω ∂μ ≤
      ∫⁻ ω, (stopEv b E W k d j).indicator (sqWeight b E W k K (j + 1)) ω ∂μ :=
    lintegral_mono fun ω => Set.indicator_le_indicator_of_subset
      (stopEv_succ_subset b E k d j) (fun _ => zero_le) ω
  refine h1.trans ?_
  rw [stopEv_eq]
  -- Fubini
  have hZ : ∀ᵐ ω ∂μ, pastCoords W j ω ∈ stopPast b E W k d j →
      sqWeight b E W k K (j + 1) ω ≤ sqPhi b E W j k K ρ Cm
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
    -- the transported tag square
    have ht : tagSq b E W (j + 1) k ω = sqPlus b E (pastXX E W j p) (pastS b E W j k p)
        (freshSample W j ω) := by
      have hY : tagResponse b E W (j + 1) k ω =
          (pastS b E W j k p * freshTransport b E (pastXX E W j p) (freshSample W j ω))ᴴ *
            (pastS b E W j k p * freshTransport b E (pastXX E W j p) (freshSample W j ω)) := by
        rw [h1 j (by omega) k (by omega), tagResponse_eq_factor, transportN, pastXX_eq,
          Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rfl
      rw [tagSq, hY]; rfl
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
    rw [sqWeight, sqPhi, ht]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sqOf_nonneg _ _))
    have := mul_le_mul_of_nonneg_left hδ hK
    linarith
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ stopPast b E W k d j →
      ∫⁻ f, sqPhi b E W j k K ρ Cm (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp hG
    have hXX := pastXX_isHermitian E hp
    have hδ : jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)) ≤ d := by
      have := hG j le_rfl hkj
      rwa [show restrictPast le_rfl p = p from rfl, pastX_zero_eq] at this
    have hXp : (passiveY (nearSchur (boundaryZ b E) (pastXX E W j p))).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have h := sq_weighted_layer_step (pastXX E W j p) (pastS b E W j k p) hW1 hCa hC₂ hCN
      hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hδ (hL.mean _ hXX) (hL.fl₂ _ hXX (hδ.trans hdd₀))
      (hL.N₂ _ hXX) (hL.N _ hXX) (hL.xi _ hXp)
    refine h.trans (le_of_eq ?_)
    have hδ0 : 0 ≤ jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)) := norm_nonneg _
    have hq : 0 ≤ (1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p))) *
        sqOf W (pastS b E W j k p) := mul_nonneg (by positivity) (sqOf_nonneg _ _)
    simp only [Ψ, sqPsi, τ]
    rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hq) (mul_nonneg hD (sq_nonneg _)),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hD]
  have hstepI := lintegral_indicator_step (μ := μ) (μP := pastLaw W j b) (ν := freshLaw W b)
    (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) (measurableSet_stopPast b E k d j)
    (measurable_sqPhi b E j k K ρ Cm) hmΨ hZ hstep
  refine hstepI.trans ?_
  have hmA : MeasurableSet (pastCoords W j ⁻¹' stopPast b E W k d j) :=
    (measurableSet_stopPast b E k d j).preimage (measurable_pastCoords W j)
  have hle : ∀ ω, (pastCoords W j ⁻¹' stopPast b E W k d j).indicator (fun ω => Ψ (pastCoords W j ω)) ω ≤
      ENNReal.ofReal (1 + α / W) *
        (pastCoords W j ⁻¹' stopPast b E W k d j).indicator (sqWeight b E W k K j) ω +
      ENNReal.ofReal D * ENNReal.ofReal (tagMass b E W j k ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ pastCoords W j ⁻¹' stopPast b E W k d j
    · simp only [Set.indicator_of_mem hω, Ψ, τ, sqWeight_eq, Function.comp, tagMass_eq_past]
      exact le_rfl
    · simp only [Set.indicator_of_notMem hω, mul_zero, zero_add]; exact zero_le
  refine (lintegral_mono hle).trans (le_of_eq ?_)
  rw [lintegral_add_left (((measurable_sqWeight b E k K j).indicator hmA).const_mul _),
    lintegral_const_mul _ ((measurable_sqWeight b E k K j).indicator hmA),
    lintegral_const_mul _ ((measurable_tagMass b E j k).pow_const 2).ennreal_ofReal]

end BlockBand.SourceProcess.FullSource
