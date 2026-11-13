module

public import BlockBand.SourceProcess.SmallLeak.GrowthStep

/-!
# The stopped step of the weighted omitted flux

`flux_stopped_step`: `E[1_{G_{j+1}} Z_{j+1}] ≤ (1 + α/W) E[1_{G_j} Z_j]` on the δ-stop
`G_j = stopEv k d j` (the proof of `stopped_current_step_on`, with `flux_weighted_step`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **One stopped step of the weighted omitted flux.** -/
theorem flux_stopped_step {b E h s : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {k j : ℕ} (hkj : k + 1 ≤ j) (hj1 : 1 ≤ j)
    (hsj : ⌊(W : ℝ) * s⌋₊ ≤ j)
    {Ca C₂ Cn CN₂ CN Cf Cm ρ d₀ : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    {Cm' : ℝ} (hΔb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      (∀ x y, Integrable (fun f => freshDelta b E X f x y) (freshLaw W b)) ∧
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          Cm' * (jetDistance0 b E X + (W : ℝ)⁻¹))
    {CD : ℝ} (hCD : 0 ≤ CD) (hΔ4 : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      MomBd (freshLaw W b) (fun f => ‖freshDelta b E X f‖) ((4 : ℕ) : ℝ) CD)
    (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm) {K d : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hLa : 0 ≤ Cm' / etaZ b E) (hKL : Cm' / etaZ b E ≤ K * (1 - ρ) / 2) (hd1 : d ≤ 1)
    (hρLd : ρ * (Cm' / etaZ b E) * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) :
    ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (fluxWeight b E h s K W (j + 1)) ω
        ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaG K Cm (Cm' / etaZ b E) Cf ((1 + CD / (2 * etaZ b E)) ^ 4) / W) *
        ∫⁻ ω, (stopEv b E W k d j).indicator (fluxWeight b E h s K W j) ω ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set η := etaZ b E
  have hη : 0 < η := boundaryZ_im_pos (by linarith) hE1 hE2
  set La := Cm' / η
  set α := alphaG K Cm La Cf ((1 + CD / (2 * η)) ^ 4)
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hα : 0 ≤ α := alphaG_nonneg hK hCm hLa (by positivity)
  set Ψ : PastSample W j → ℝ≥0∞ := fun p => ENNReal.ofReal (1 + α / W) * fluxPsi b E h s K W j p
  have hmΨ : Measurable Ψ := by
    refine Measurable.const_mul ?_ _
    exact ((measurable_const.add (measurable_const.mul ((measurable_jetDistance0 b E).comp
      (measurable_nearSchur_comp (boundaryZ b E) (measurable_pastXX E j))))).mul
      (measurable_fluxPast b E h s j)).ennreal_ofReal
  have h1 : ∫⁻ ω, (stopEv b E W k d (j + 1)).indicator (fluxWeight b E h s K W (j + 1)) ω ∂μ ≤
      ∫⁻ ω, (stopEv b E W k d j).indicator (fluxWeight b E h s K W (j + 1)) ω ∂μ :=
    lintegral_mono fun ω => Set.indicator_le_indicator_of_subset
      (stopEv_succ_subset b E k d j) (fun _ => zero_le) ω
  refine h1.trans ?_
  rw [stopEv_eq]
  -- the joint positivity of the next flux
  set S : Set (PastSample W j × LayerSample W .oneBlockOnePort) :=
    {q | 0 ≤ fluxNext b E (pastXX E W j q.1) (omittedPast b E h s W j q.1) q.2}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (measurable_fluxNext_comp b E ((measurable_pastXX E j).comp measurable_fst)
      ((measurable_omittedPast b E h s j).comp measurable_fst) measurable_snd)
  have hsucc := ae_omittedFlux_succ (h := h) (s := s) hb0 hb hE1 hE2 hW hj1 hsj
  have hposP : ∀ᵐ p ∂pastLaw W j b, ∀ᵐ f ∂freshLaw W b, (p, f) ∈ S := by
    refine ae_ae_of_ae_pair (measurable_pastCoords W j) (measurable_freshSample W j)
      (growthPathLaw_map_past_fresh W j b) hS ?_
    filter_upwards [hsucc] with ω hω
    show 0 ≤ _
    rw [← hω]; exact omittedFlux_nonneg _ _ _ _ _ _ _
  have hZ : ∀ᵐ ω ∂μ, pastCoords W j ω ∈ stopPast b E W k d j →
      fluxWeight b E h s K W (j + 1) ω ≤
        fluxPhi b E h s K ρ Cm W j (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_pathX_succ hb hE1 hE2 hW, ae_growth_isHermitian W b, hsucc]
      with ω h2 h3 hω hG
    have hG' : ω ∈ stopEv b E W k d j := by rw [stopEv_eq]; exact hG
    have hp : pastCoords W j ω ∈ hermPast W j := fun l => h3 l
    set p := pastCoords W j ω
    set X := nearSchur (boundaryZ b E) (pastXX E W j p)
    have hXp : (passiveY X).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have hδj : jetDistance0 b E X ≤ d := by
      have := hG' j hkj le_rfl; rwa [pathDelta_eq_past] at this
    have hδ : pathDelta b E W (j + 1) ω ≤ ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 +
        freshXi b E X (freshSample W j ω) := by
      rw [pathDelta, h2 j hj1, jetDistance0_freshSchur, pathX_eq_past]
      have hm := hL.meanStep X hXp (hδj.trans hdd₀)
      have := norm_sub_le (freshPortTrace b E X (freshSample W j ω) -
        ∫ f, freshPortTrace b E X f ∂freshLaw W b)
        (matchedA E - ∫ f, freshPortTrace b E X f ∂freshLaw W b)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (matchedA E)] at this
      simp only [freshXi]
      linarith
    have hg0 := omittedFlux_nonneg b E h s W (j + 1) ω
    rw [fluxWeight, fluxPhi, ← hω, max_eq_left hg0]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hg0)
    have := mul_le_mul_of_nonneg_left hδ hK
    linarith
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ stopPast b E W k d j →
      ∫⁻ f, fluxPhi b E h s K ρ Cm W j (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b, hposP] with p hp hpos hGB
    have hXX := pastXX_isHermitian E hp
    set X := nearSchur (boundaryZ b E) (pastXX E W j p)
    have hδ : jetDistance0 b E X ≤ d := by
      have := hGB j le_rfl hkj
      rwa [show restrictPast le_rfl p = p from rfl, pastX_zero_eq] at this
    have hXp : (passiveY X).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    obtain ⟨hΔi, hmean⟩ := hΔb X hXp
    have h4 := delta_four (ν := freshLaw W b) hCD hη (fun f => norm_nonneg (freshDelta b E X f))
      (hΔ4 X hXp)
    have hmean' : ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ / η ≤
        La * (jetDistance0 b E X + (W : ℝ)⁻¹) := by
      rw [div_le_iff₀ hη]
      calc _ ≤ Cm' * (jetDistance0 b E X + (W : ℝ)⁻¹) := hmean
        _ = La * (jetDistance0 b E X + (W : ℝ)⁻¹) * η := by
          simp only [La]; field_simp
    have hmΔ : Measurable (freshDelta b E X) :=
      measurable_freshDelta_comp b E (X := fun _ => X) measurable_const measurable_id
    have h := flux_weighted_step hη hXX (omittedPast_conjTranspose b E h s j p) hW1 hΔi hmΔ hLa
      hmean' (by positivity) h4.1 h4.2 hpos hCf (hL.xi X hXp) hK hρ0 hρ1 hCm hKL hd1 hρLd hδ
    refine h.trans (le_of_eq ?_)
    simp only [Ψ, fluxPsi]
    rw [← ENNReal.ofReal_mul (by have := hα; positivity)]
    rfl
  have hstepI := lintegral_indicator_step (μ := μ) (μP := pastLaw W j b) (ν := freshLaw W b)
    (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) (measurableSet_stopPast b E k d j)
    (measurable_fluxPhi b E h s K ρ Cm j) hmΨ hZ hstep
  refine hstepI.trans (le_of_eq ?_)
  rw [← lintegral_const_mul _ ((measurable_fluxWeight b E h s K j).indicator
    ((measurableSet_stopPast b E k d j).preimage (measurable_pastCoords W j)))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_omittedFlux_eq_past (h := h) (s := s) (E := E) hb hW hsj] with ω hω
  by_cases hm : ω ∈ pastCoords W j ⁻¹' stopPast b E W k d j
  · simp only [Set.indicator_of_mem hm, Ψ, fluxPsi, fluxWeight, pathDelta_eq_past, hω]
  · simp only [Set.indicator_of_notMem hm, mul_zero]

end BlockBand.SourceProcess.SmallLeak
