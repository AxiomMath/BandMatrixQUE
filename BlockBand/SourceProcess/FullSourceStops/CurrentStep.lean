module

public import BlockBand.SourceProcess.FullSourceStops.CurrentPast
public import BlockBand.SourceProcess.FullSourceStops.CurrentLayer
public import BlockBand.SourceProcess.FullSourceStops.Ville
public import BlockBand.SourceProcess.FullSource.TagFinal

/-!
# The stopped first-moment supermartingale of the current carrier

`curWeight b E W k K i = (1 + Kδ_{k+1+i}) W⁻¹Re Tr H_i` (carrier `H_i` of `CurrentPast`).
* `stopped_current_step_on`: for every measurable past event `B` at length `j = k+1+i`,
  `E[1_B 1_{G_{j+1}} Z_{i+1}] ≤ (1 + α₁/W) E[1_B 1_{G_j} Z_i]` (the proof of
  `stopped_tag_step_on`, with `current_layer_step` in place of `weighted_layer_step`);
* `curStopped`, `noHit_curStopped`, `curStopped_step`: the stopped weights form a weighted
  supermartingale against their no-hit events, as `ville` consumes.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PathScalar BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- The weight `Z_i = (1 + Kδ_{k+1+i}) W⁻¹Re Tr H_i`. -/
def curWeight (b E : ℝ) (W k : ℕ) (K : ℝ) (i : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * pathDelta b E W (k + 1 + i) ω) *
    ((W : ℝ)⁻¹ * (carrier b E W k i ω).trace.re))

/-- The weight as a function of the past. -/
def curPsi (b E : ℝ) (W k : ℕ) (K : ℝ) (i : ℕ) (p : PastSample W (k + 1 + i)) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) p))) *
    ((W : ℝ)⁻¹ * (carrierPast b E W k i p).trace.re))

theorem measurable_trace_re {α n : Type*} [MeasurableSpace α] [Fintype n]
    {M : α → Matrix n n ℂ} (hM : Measurable M) : Measurable fun a => (M a).trace.re := by
  simp only [Matrix.trace, Matrix.diag]
  exact Complex.measurable_re.comp (Finset.measurable_sum _ fun i _ => hM.eval_matrix)

theorem measurable_curPsi (b E : ℝ) (k : ℕ) (K : ℝ) (i : ℕ) :
    Measurable (curPsi b E W k K i) := by
  have hX := measurable_nearSchur_comp (boundaryZ b E) (measurable_pastXX (W := W) E (k + 1 + i))
  exact ((measurable_const.add (measurable_const.mul ((measurable_jetDistance0 b E).comp hX))).mul
    (measurable_const.mul (measurable_trace_re (measurable_carrierPast b E k i)))).ennreal_ofReal

theorem curWeight_eq (b E : ℝ) (k : ℕ) (K : ℝ) (i : ℕ) :
    curWeight b E W k K i = curPsi b E W k K i ∘ pastCoords W (k + 1 + i) := by
  funext ω
  simp only [curWeight, curPsi, Function.comp, pathDelta_eq_past, carrier_eq_past]

theorem measurable_curWeight (b E : ℝ) (k : ℕ) (K : ℝ) (i : ℕ) :
    Measurable (curWeight b E W k K i) := by
  rw [curWeight_eq]; exact (measurable_curPsi b E k K i).comp (measurable_pastCoords W _)

/-- The fresh integrand of the weighted step at past `p`. -/
def curPhi (b E : ℝ) (W k : ℕ) (K ρ Cm : ℝ) (i : ℕ)
    (q : PastSample W (k + 1 + i) × LayerSample W .oneBlockOnePort) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E
      (nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) q.1)) + Cm / (W : ℝ) ^ 2 +
      freshXi b E (nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) q.1)) q.2)) *
    carPlus b E (pastXX E W (k + 1 + i) q.1) (carrierPast b E W k i q.1) q.2)

theorem measurable_curPhi (b E : ℝ) (k : ℕ) (K ρ Cm : ℝ) (i : ℕ) :
    Measurable (curPhi b E W k K ρ Cm i) := by
  set j := k + 1 + i
  have hXX : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      pastXX E W j q.1 := (measurable_pastXX E j).comp measurable_fst
  have hX := measurable_nearSchur_comp (boundaryZ b E) hXX
  have hδ := (measurable_jetDistance0 b E).comp hX
  have hF : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    measurable_freshPortTrace_comp b E hX measurable_snd
  have hI : Measurable fun p : PastSample W j =>
      ∫ f, freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j p)) f ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hξ : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    (hF.sub (hI.comp measurable_fst)).norm
  have hN := measurable_freshTransport_comp b E hXX measurable_snd
  have hH : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      carrierPast b E W k i q.1 := (measurable_carrierPast b E k i).comp measurable_fst
  have hT := measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hN)
    hH) hN
  have ht : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      carPlus b E (pastXX E W j q.1) (carrierPast b E W k i q.1) q.2 :=
    measurable_const.mul (measurable_trace_re hT)
  unfold curPhi
  exact ((measurable_const.add (measurable_const.mul (((measurable_const.mul hδ).add
    measurable_const).add hξ))).mul ht).ennreal_ofReal

/-- **One stopped step of the carrier against a past event `B`.** -/
theorem stopped_current_step_on {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k i : ℕ} (hW : 1 ≤ W)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : Ca ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀)
    {B : Set (PastSample W (k + 1 + i))} (hB : MeasurableSet B) :
    ∫⁻ ω, (pastCoords W (k + 1 + i) ⁻¹' B ∩ stopEv b E W k d (k + 1 + i + 1)).indicator
        (curWeight b E W k K (i + 1)) ω ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaOne K Cm Ca Cf CN / W) *
        ∫⁻ ω, (pastCoords W (k + 1 + i) ⁻¹' B ∩ stopEv b E W k d (k + 1 + i)).indicator
          (curWeight b E W k K i) ω ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  set α := alphaOne K Cm Ca Cf CN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hα : 0 ≤ α := alphaOne_nonneg hK hCm hCa hCN
  set Ψ : PastSample W (k + 1 + i) → ℝ≥0∞ := fun p => ENNReal.ofReal (1 + α / W) * curPsi b E W k K i p
    with hΨ
  have hmΨ : Measurable Ψ := measurable_const.mul (measurable_curPsi b E k K i)
  have h1 : ∫⁻ ω, (pastCoords W (k + 1 + i) ⁻¹' B ∩ stopEv b E W k d ((k + 1 + i) + 1)).indicator
        (curWeight b E W k K (i + 1)) ω ∂μ ≤
      ∫⁻ ω, (pastCoords W (k + 1 + i) ⁻¹' B ∩ stopEv b E W k d (k + 1 + i)).indicator
        (curWeight b E W k K (i + 1)) ω ∂μ :=
    lintegral_mono fun ω => Set.indicator_le_indicator_of_subset
      (Set.inter_subset_inter_right _ (stopEv_succ_subset b E k d (k + 1 + i))) (fun _ => zero_le) ω
  refine h1.trans ?_
  have hG : pastCoords W (k + 1 + i) ⁻¹' B ∩ stopEv b E W k d (k + 1 + i) =
      pastCoords W (k + 1 + i) ⁻¹' (stopPast b E W k d (k + 1 + i) ∩ B) := by
    rw [stopEv_eq, Set.preimage_inter, Set.inter_comm]
  rw [hG]
  have hZ : ∀ᵐ ω ∂μ, pastCoords W (k + 1 + i) ω ∈ stopPast b E W k d (k + 1 + i) ∩ B →
      curWeight b E W k K (i + 1) ω ≤ curPhi b E W k K ρ Cm i
        (pastCoords W (k + 1 + i) ω, freshSample W (k + 1 + i) ω) := by
    filter_upwards [ae_pathX_succ hb hE1 hE2 hW, ae_growth_isHermitian W b] with ω h2 h3 hG
    have hG' : ω ∈ stopEv b E W k d (k + 1 + i) := by rw [stopEv_eq]; exact hG.1
    have hp : pastCoords W (k + 1 + i) ω ∈ hermPast W (k + 1 + i) := fun l => h3 l
    set p := pastCoords W (k + 1 + i) ω
    set X := nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) p)
    have hXp : (passiveY X).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have hδj : jetDistance0 b E X ≤ d := by
      have := hG' (k + 1 + i) (by omega) le_rfl; rwa [pathDelta_eq_past] at this
    have ht : (W : ℝ)⁻¹ * (carrier b E W k (i + 1) ω).trace.re =
        carPlus b E (pastXX E W (k + 1 + i) p) (carrierPast b E W k i p) (freshSample W (k + 1 + i) ω) := by
      simp only [carrier, carPlus, carrier_eq_past b E k i ω, transportN, pastXX_eq]
      rfl
    have hδ : pathDelta b E W ((k + 1 + i) + 1) ω ≤ ρ * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 +
        freshXi b E X (freshSample W (k + 1 + i) ω) := by
      rw [pathDelta, h2 (k + 1 + i) (by omega), jetDistance0_freshSchur, pathX_eq_past]
      have hm := hL.meanStep X hXp (hδj.trans hdd₀)
      have := norm_sub_le (freshPortTrace b E X (freshSample W (k + 1 + i) ω) -
        ∫ f, freshPortTrace b E X f ∂freshLaw W b)
        (matchedA E - ∫ f, freshPortTrace b E X f ∂freshLaw W b)
      rw [sub_sub_sub_cancel_right, norm_sub_rev (matchedA E)] at this
      simp only [freshXi]
      linarith
    rw [curWeight, curPhi, show k + 1 + (i + 1) = (k + 1 + i) + 1 by omega, ht]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_
      (carPlus_nonneg _ _ _ (carrierPast_posSemidef b E k i _) _))
    have := mul_le_mul_of_nonneg_left hδ hK
    linarith
  have hstep : ∀ᵐ p ∂pastLaw W (k + 1 + i) b, p ∈ stopPast b E W k d (k + 1 + i) ∩ B →
      ∫⁻ f, curPhi b E W k K ρ Cm i (p, f) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W (k + 1 + i) b] with p hp hGB
    have hXX := pastXX_isHermitian E hp
    have hδ : jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) p)) ≤ d := by
      have := hGB.1 (k + 1 + i) le_rfl (by omega)
      rwa [show restrictPast le_rfl p = p from rfl, pastX_zero_eq] at this
    have hXp : (passiveY (nearSchur (boundaryZ b E) (pastXX E W (k + 1 + i) p))).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    have hN4 : eLpNorm (fun ω => ‖freshTransport b E (pastXX E W (k + 1 + i) p) ω‖)
        (ENNReal.ofReal ((2 * (2 * 1) : ℕ) : ℝ)) (freshLaw W b) ≤ ENNReal.ofReal CN :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by norm_num))).trans
        (hL.N _ hXX)
    have h := current_layer_step (pastXX E W (k + 1 + i) p) (carrierPast b E W k i p)
      (carrierPast_posSemidef b E k i p) hW1 hCa hC₂ hCN hCf hCm hK hρ0 hρ1 hKL hd1 hρLd hδ
      (hL.mean _ hXX) (hL.fl₂ _ hXX (hδ.trans hdd₀)) (hL.N₂ _ hXX) hN4 (hL.xi _ hXp)
    refine h.trans (le_of_eq ?_)
    simp only [Ψ, curPsi]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hstepI := lintegral_indicator_step (μ := μ) (μP := pastLaw W (k + 1 + i) b) (ν := freshLaw W b)
    (measurable_pastCoords W (k + 1 + i)) (measurable_freshSample W (k + 1 + i))
    (growthPathLaw_map_past_fresh W (k + 1 + i) b) ((measurableSet_stopPast b E k d (k + 1 + i)).inter hB)
    (measurable_curPhi b E k K ρ Cm i) hmΨ hZ hstep
  refine hstepI.trans (le_of_eq ?_)
  rw [← lintegral_const_mul _ ((measurable_curWeight b E k K i).indicator
    (((measurableSet_stopPast b E k d (k + 1 + i)).inter hB).preimage (measurable_pastCoords W (k + 1 + i))))]
  congr 1; funext ω
  by_cases hω : ω ∈ pastCoords W (k + 1 + i) ⁻¹' (stopPast b E W k d (k + 1 + i) ∩ B)
  · simp only [Set.indicator_of_mem hω, Ψ, curWeight_eq, Function.comp]
  · simp only [Set.indicator_of_notMem hω, mul_zero]

/-!
## The stopped weights
-/

/-- The stopped weights `Y_i = 1_{G_{k+1+i}} Z_i`. -/
def curStopped (b E : ℝ) (W k : ℕ) (K d : ℝ) (i : ℕ) : GrowthPath W → ℝ≥0∞ :=
  (stopEv b E W k d (k + 1 + i)).indicator (curWeight b E W k K i)

theorem measurable_curStopped (b E : ℝ) (k : ℕ) (K d : ℝ) (i : ℕ) :
    Measurable (curStopped b E W k K d i) :=
  (measurable_curWeight b E k K i).indicator (measurableSet_stopEv b E k d _)

theorem curStopped_apply (b E : ℝ) (k : ℕ) (K d : ℝ) (i : ℕ) (ω : GrowthPath W) :
    curStopped b E W k K d i ω = (stopPast b E W k d (k + 1 + i)).indicator
      (curPsi b E W k K i) (pastCoords W (k + 1 + i) ω) := by
  rw [curStopped, stopEv_eq, curWeight_eq]
  by_cases h : pastCoords W (k + 1 + i) ω ∈ stopPast b E W k d (k + 1 + i)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.mp h'))]

theorem noHit_curStopped (b E : ℝ) (k : ℕ) (K d : ℝ) (lam : ℝ≥0∞) (i : ℕ) :
    ∃ B : Set (PastSample W (k + 1 + i)), MeasurableSet B ∧
      noHit (curStopped b E W k K d) lam i = pastCoords W (k + 1 + i) ⁻¹' B := by
  refine ⟨{p | ∀ i' (h : i' ≤ i), (stopPast b E W k d (k + 1 + i')).indicator
      (curPsi b E W k K i') (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) < lam},
    ?_, ?_⟩
  · have : {p : PastSample W (k + 1 + i) | ∀ i' (h : i' ≤ i), (stopPast b E W k d (k + 1 + i')).indicator
        (curPsi b E W k K i') (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) < lam} =
        ⋂ i', ⋂ (h : i' ≤ i), {p | (stopPast b E W k d (k + 1 + i')).indicator
          (curPsi b E W k K i') (restrictPast (show k + 1 + i' ≤ k + 1 + i by omega) p) < lam} := by
      ext p; simp
    rw [this]
    exact MeasurableSet.iInter fun i' => MeasurableSet.iInter fun h => measurableSet_lt
      (((measurable_curPsi b E k K i').indicator (measurableSet_stopPast b E k d _)).comp
        (measurable_restrictPast _)) measurable_const
  · ext ω
    simp only [noHit, Set.mem_preimage, curStopped_apply]
    rfl

/-- **The stopped weights are a weighted supermartingale against their no-hit events.** -/
theorem curStopped_step {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    {k : ℕ} (hW : 1 ≤ W)
    {Ca C₂ Cn CN₂ CN Cf Cm K ρ d₀ d : ℝ} (hL : TagLayerBounds b E W 2 Ca C₂ Cn CN₂ CN Cf Cm ρ d₀)
    (hCa : 0 ≤ Ca) (hC₂ : 0 ≤ C₂) (hCN : 0 ≤ CN) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cm)
    (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hKL : Ca ≤ K * (1 - ρ) / 2)
    (hd1 : d ≤ 1) (hρLd : ρ * Ca * d ≤ (1 - ρ) / 2) (hdd₀ : d ≤ d₀) (lam : ℝ≥0∞) (i : ℕ) :
    ∫⁻ ω, (noHit (curStopped b E W k K d) lam i).indicator
        (curStopped b E W k K d (i + 1)) ω ∂growthPathLaw W b ≤
      ENNReal.ofReal (1 + alphaOne K Cm Ca Cf CN / W) *
        ∫⁻ ω, (noHit (curStopped b E W k K d) lam i).indicator
          (curStopped b E W k K d i) ω ∂growthPathLaw W b := by
  obtain ⟨B, hB, hBe⟩ := noHit_curStopped (W := W) b E k K d lam i
  rw [hBe]
  simp only [curStopped, Set.indicator_indicator]
  exact stopped_current_step_on hb hE1 hE2 (i := i) hW hL hCa hC₂ hCN hCf hCm hK hρ0 hρ1 hKL hd1
    hρLd hdd₀ hB

end BlockBand.SourceProcess.FullSourceStops
