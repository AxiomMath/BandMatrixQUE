module

public import BlockBand.Endpoints.Clock.BUniformDeterministicStep
public import BlockBand.Endpoints.Clock.MovingEnergyRuledHyps

/-!
# The open-inputs lemma, uniformly in `b`: one fresh layer, the entrance, the clock mean

The radius `ε` of `OpenInputsMomentsBulk` must not depend on `b`, while the energy-uniform chain
(`OpenInputsEnergyUniform*`) fixes `b` first. This file supplies the pieces of that chain whose
constants enter `ε`, with exactly those constants chosen before `b`, for `b ∈ Icc β (1/2-β)`,
`0 < β < 1/4`, `E ∈ bulkInterval κ`, `0 < κ ≤ 1`:
* `oneStepFacts_unifB`: `OneStepFacts` (`one_step`) with the radius `r₀` (and `q`, `Cst`) from the
  deterministic `step_bound_unifB`, before `b`; the constants `C₀, a₀` of `CavityMeanStatement`
  after `b`;
* `delta_next_unifB`: the scalar step `delta_next` with `r₀, q` before `b` and `C₂, Cn, W₀`
  after `b`;
* `entrance_bound_unifB`: the entrance bound (`entrance_bound_unif`) with `J, ε, a, K, W₀` before
  `b`, from the `zeParam`-uniform clauses of the zero-entrance lemma (`ZeroEntranceStatement`) at
  `kappaBulkB β κ`;
* `onePortClockMeanB`: the clock-mean clause of `OnePortWeighted` (the weighted-layer lemma, read
  for one block) with `dstar, C, W₀` before `b`, from the field `weightedLayerClockMean` of
  `LayersBUniformHyp`, through the block embedding.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof CavityMeanProb ZeroEntranceProb

/-- **One fresh layer, uniformly in `b ∈ Icc β (1/2-β)` and `E ∈ bulkInterval κ`**: the
conclusion `OneStepFacts` of `OpenInputsProof.one_step` with `r₀, q, Cst` chosen before `b`
(`step_bound_unifB`) and `C₀, a₀` (from the cavity-mean lemma) after `b`. -/
theorem oneStepFacts_unifB (hQ : CavityMeanStatement) {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) :
    ∃ r₀ q Cst : ℝ, 0 < r₀ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∃ C₀ a₀ : ℝ,
      ∀ E ∈ bulkInterval κ, OneStepFacts b E r₀ q Cst C₀ a₀ := by
  have hκ4 : κ < 4 := by linarith
  obtain ⟨r₀, q, Cst, hr₀, hq0, hq1, hCst, hstep⟩ := step_bound_unifB β κ hβ hκ hκ1
  refine ⟨r₀, q, Cst, hr₀, fun b hb => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨⟨a₀, C₀, ha₀, hC₀, h0⟩, h1⟩ := hQ b hb0 hb1 (etaLow b κ) 3 (etaLow_pos hb1 hκ hκ4)
  obtain ⟨a₁, C₁, ha₁, h1⟩ := h1 1
  refine ⟨max C₀ (max C₁ 0), min a₀ a₁, fun E hEκ => ?_⟩
  have hCm0 : 0 ≤ max C₀ (max C₁ 0) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨hr₀, hq0, hq1, hCst, hCm0, lt_min ha₀ ha₁, ?_⟩
  have hzpos : 0 < (boundaryZ b E).im := im_pos_of_bulk hb1 hκ hκ4 hEκ
  have hzη := etaLow_le_im hb1 hκ hEκ
  have hz3 := norm_boundaryZ_le3 hb0 hb1 hκ hEκ
  intro W hW X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean0, hfl0⟩ := h0 W hW X hX E (boundaryZ b E) hzη hz3
  obtain ⟨hmean1, hfl1⟩ := h1 W hW X hX E (boundaryZ b E) hzη hz3
  simp only [iteratedDeriv_one] at hmean1 hfl1
  have hmono : ∀ c : ℝ, c ≤ max C₀ (max C₁ 0) → ∀ p : ℝ, 0 ≤ p →
      ENNReal.ofReal (c * Real.sqrt p / W) ≤
        ENNReal.ofReal (max C₀ (max C₁ 0) * Real.sqrt p / W) := by
    intro c hc p _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  refine ⟨fun p hp2 hpa => ⟨?_, ?_⟩, fun hδ y => ⟨?_, fun s hs => ?_⟩⟩
  · have hpa0 : p ≤ a₀ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hWr.le)
    refine (eLpNorm_mono (measurable_freshNoise0 b E X).aestronglyMeasurable
      fun y => (norm_norm _).le).trans ?_
    exact (hfl0 p hp2 hpa0).trans (hmono C₀ (le_max_left _ _) p (by linarith))
  · have hpa1 : p ≤ a₁ * W := hpa.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hWr.le)
    refine (eLpNorm_mono (aesm_freshNoise1 b E hX hzpos) fun y => (norm_norm _).le).trans ?_
    exact (hfl1 p hp2 hpa1).trans
      (hmono C₁ ((le_max_left _ _).trans (le_max_right _ _)) p (by linarith))
  · obtain ⟨hsc, -⟩ := hstep b hb E hEκ hW X hX hδ
    rw [jetDistance0_freshSchur]
    have htri := norm_sub_le_norm_sub_add_norm_sub (cavityHplus E X (boundaryZ b E) y)
      (∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) (matchedA E)
    have htri2 := norm_sub_le_norm_sub_add_norm_sub
      (∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) (cavityU X b E (boundaryZ b E))
      (matchedA E)
    have hm : ‖(∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b) -
        cavityU X b E (boundaryZ b E)‖ ≤ max C₀ (max C₁ 0) / (W : ℝ) ^ 2 :=
      hmean0.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
    have : freshNoise0 b E X y = ‖cavityHplus E X (boundaryZ b E) y -
        ∫ y', cavityHplus E X (boundaryZ b E) y' ∂freshLaw W b‖ := rfl
    linarith
  · obtain ⟨-, hj⟩ := hstep b hb E hEκ hW X hX hδ
    rw [jetDistance1_freshSchur]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E))
      (∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b) s
    have htri2 := norm_sub_le_norm_sub_add_norm_sub
      (∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b)
      (deriv (cavityU X b E) (boundaryZ b E)) s
    have hm : ‖(∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b) -
        deriv (cavityU X b E) (boundaryZ b E)‖ ≤ max C₀ (max C₁ 0) / (W : ℝ) ^ 2 :=
      hmean1.trans (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _))
        (by positivity))
    have : freshNoise1 b E X y = ‖deriv (fun ζ => cavityHplus E X ζ y) (boundaryZ b E) -
        ∫ y', deriv (fun ζ => cavityHplus E X ζ y') (boundaryZ b E) ∂freshLaw W b‖ := rfl
    have := hj s hs
    linarith

/-- **The scalar step at the next layer, uniformly in `b ∈ Icc β (1/2-β)` and
`E ∈ bulkInterval κ`** (`OpenInputsProof.delta_next`): the radius `r₀` and the contraction
factor `q` are chosen before `b` (`step_bound_unifB`); `C₂, Cn, W₀` (from
the cavity-mean lemma) after `b`. -/
theorem delta_next_unifB (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract)
    {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ r₀ q : ℝ, 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∃ (C₂ Cn : ℝ) (W₀ : ℕ), 0 ≤ C₂ ∧ 0 ≤ Cn ∧
      ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        (jetDistance0 b E X ≤ r₀ → ∀ ω, jetDistance0 b E (freshSchur E X ω) ≤
          q * jetDistance0 b E X + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω) ∧
        ∫⁻ ω, ENNReal.ofReal (portNoise b E X ω ^ 2) ∂freshLaw W b ≤
          ENNReal.ofReal (Cn / (W : ℝ) ^ 2) := by
  have hκ4 : κ < 4 := by linarith
  obtain ⟨r₀, q, Cs, hr₀, hq0, hq1, -, hstep⟩ := step_bound_unifB β κ hβ hκ hκ1
  refine ⟨r₀, q, hr₀, hq0, hq1, fun b hb => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨⟨a₀, C, ha₀, hC, hcm⟩, -⟩ := cavityMean_of hGA hTM b hb0 hb1 (etaLow b κ) 3
    (etaLow_pos hb1 hκ hκ4)
  refine ⟨C, 2 * C ^ 2, ⌈2 / a₀⌉₊, hC.le, by positivity, ?_⟩
  intro W hW hW₀ E hEκ X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean, hfl⟩ := hcm W hW X hX E (boundaryZ b E) (etaLow_le_im hb1 hκ hEκ)
    (norm_boundaryZ_le3 hb0 hb1 hκ hEκ)
  refine ⟨fun hδ ω => ?_, ?_⟩
  · have hsc := (hstep b hb E hEκ hW X hX hδ).1
    have e : jetDistance0 b E (freshSchur E X ω) =
        ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e]
    have htri : ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ ≤ portNoise b E X ω +
        ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) -
          cavityU X b E (boundaryZ b E)‖ +
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ := by
      unfold portNoise
      refine (norm_sub_le_norm_sub_add_norm_sub _
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) _).trans ?_
      have := norm_sub_le_norm_sub_add_norm_sub
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (cavityU X b E (boundaryZ b E))
        (matchedA E)
      linarith
    have : ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) -
        cavityU X b E (boundaryZ b E)‖ ≤ C / (W : ℝ) ^ 2 := hmean
    linarith
  · have h2W : (2 : ℝ) ≤ a₀ * W := by
      have h := (Nat.le_ceil (2 / a₀)).trans (by exact_mod_cast hW₀ : ((⌈2 / a₀⌉₊ : ℕ) : ℝ) ≤ W)
      rw [div_le_iff₀ ha₀] at h; linarith
    have h2 := hfl 2 le_rfl h2W
    rw [ENNReal.ofReal_ofNat] at h2
    have h2' : eLpNorm (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤
        ENNReal.ofReal (C * Real.sqrt 2 / W) := by
      simpa using h2
    have hm : AEStronglyMeasurable (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (freshLaw W b) :=
      ((meas_cavityHplus (E := E) X (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
    have h := lintegral_ofReal_pow_le (by norm_num) hm (by positivity) h2'
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring

/-- **The entrance, uniformly in `b ∈ Icc β (1/2-β)` and `E ∈ bulkInterval κ`**
(`entrance_bound_unif` with `J, ε, a, K, W₀` depending only on `(β, κ, r)`): the
zero-entrance lemma clauses are uniform on `zeParam κ' b e`, and `kappaBulkB β κ`
covers every such `(b, E)` (`zeParam_bulkB`). -/
theorem entrance_bound_unifB (hZ : ZeroEntranceStatement) {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hκ4 : κ < 4) {r : ℝ} (hr : 0 < r) :
    ∃ (J : ℕ) (ε a K : ℝ) (W₀ : ℕ), 0 < ε ∧ 0 < a ∧ 0 ≤ K ∧
      ∀ b ∈ Set.Icc β (1 / 2 - β), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
        ∀ D : Matrix (Fin W) (Fin W) ℂ, D.IsHermitian → ‖D‖ ≤ ε →
        ∀ P : ℝ, 2 ≤ P → P ≤ a * W →
          oneEndedLaw W b J {ω | r < chainD0 b E D J ω} ≤
            ENNReal.ofReal ((K * Real.sqrt P / W) ^ P) := by
  obtain ⟨μ, -, hseed, hfix⟩ := hZ
  obtain ⟨hκ', hpar⟩ := zeParam_bulkB hβ hκ hκ4
  obtain ⟨Cs, cs, hCs, hcs, hseed'⟩ := hseed (kappaBulkB β κ) hκ'
  have hlim : Tendsto (fun J : ℕ => Cs * Real.exp (-cs * J)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun J : ℕ => -cs * (J : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hcs)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul Cs
    simpa [Function.comp_def] using h2
  obtain ⟨J, hJ⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))).exists
  obtain ⟨a, C, W₀, ha, hC, hfixJ⟩ := hfix (kappaBulkB β κ) hκ' J
  refine ⟨J, r / (4 * C), a, 4 * C / r, max W₀ (⌈4 * C / r⌉₊ + 1), by positivity, ha,
    by positivity, ?_⟩
  intro b hb W hW E hEκ D hD hDε P hP2 hPa
  have hW0 : W₀ ≤ W := (le_max_left _ _).trans hW
  have hW1 : ⌈4 * C / r⌉₊ + 1 ≤ W := (le_max_right _ _).trans hW
  have hWr : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le
      (Nat.succ_pos _) hW1))
    linarith
  have hCW : C / W ≤ r / 4 := by
    have h1 : 4 * C / r < W := by
      have := Nat.le_ceil (4 * C / r)
      have h2 : ((⌈4 * C / r⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW1
      push_cast at h2; linarith
    rw [div_lt_iff₀ hr] at h1
    rw [div_le_iff₀ hWr]; linarith
  obtain ⟨hmean, -, hconc, hpert⟩ := hfixJ W hW0 b E (hpar b hb E hEκ)
  obtain ⟨h1, -⟩ := hconc D hD P hP2 hPa
  obtain ⟨h2, -⟩ := hpert (r / (4 * C)) D hD hDε
  have h3 := hseed' b E J (hpar b hb E hEκ)
  have hCε : C * (r / (4 * C)) = r / 4 := by field_simp
  set Z := ∫ ω', zeTrace E D J (boundaryZ b E) ω' ∂oneEndedLaw W b J with hZdef
  have hsub : {ω | r < chainD0 b E D J ω} ⊆
      {ω | r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖} := by
    intro ω hω
    have hω' : r < chainD0 b E D J ω := hω
    show r / 4 ≤ ‖zeTrace E D J (boundaryZ b E) ω - Z‖
    have e : chainD0 b E D J ω = ‖zeTrace E D J (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e] at hω'
    set h := zeTrace E D J (boundaryZ b E) ω
    set Z0 := ∫ ω', zeTrace E (0 : Matrix (Fin W) (Fin W) ℂ) J (boundaryZ b E) ω'
      ∂oneEndedLaw W b J
    set G := stieltjesG (μ b E J) (boundaryZ b E)
    have t1 := norm_sub_le_norm_sub_add_norm_sub h Z (matchedA E)
    have t2 := norm_sub_le_norm_sub_add_norm_sub Z Z0 (matchedA E)
    have t3 := norm_sub_le_norm_sub_add_norm_sub Z0 G (matchedA E)
    have hs : Cs * Real.exp (-cs * J) < r / 4 := hJ
    linarith
  refine (measure_mono hsub).trans ?_
  have hB0 : 0 ≤ C * Real.sqrt P / W := by positivity
  have hm : AEStronglyMeasurable (fun ω => zeTrace E D J (boundaryZ b E) ω - Z)
      (oneEndedLaw W b J) :=
    ((measurable_zeTrace E D J (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
  have hN : eLpNorm (fun ω => ‖zeTrace E D J (boundaryZ b E) ω - Z‖) (ENNReal.ofReal P)
      (oneEndedLaw W b J) ≤ ENNReal.ofReal (C * Real.sqrt P / W) := by
    rw [eLpNorm_norm _ hm]; exact h1
  refine (measure_ge_le_of_eLpNorm (by positivity) (by linarith) hB0 hN).trans
    (le_of_eq (congrArg ENNReal.ofReal ?_))
  congr 1
  field_simp

open Embed in

/-- **The clock-mean clause of `OnePortWeighted`, uniformly in `b ∈ Icc β (1/2-β)`**:
`dstar, C, W₀` depend only on `(β, κ)`. Proved from the field `weightedLayerClockMean` of
`LayersBUniformHyp` through the block embedding (the first half of `onePortWeighted_of`), and from
`GaussianAbsorptionContract` (almost-sure invertibility at fixed `b` only).
-/
theorem onePortClockMeanB (hB : LayersBUniformHyp) (hGA : GaussianAbsorptionContract)
    {β : ℝ} (hβ : 0 < β) (hβ4 : β < 1 / 4) {κ : ℝ} (hκ : 0 < κ) :
    ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
        jetDistance0 b E X ≤ dstar → ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef →
          Integrable (clockT b E X Y) (freshLaw W b) ∧
          ∫ ω, clockT b E X Y ω ∂freshLaw W b ≤
            (1 + C * jetDistance0 b E X + C / (W : ℝ) ^ 2) * clockU Y := by
  obtain ⟨dstar, C, W₀, hd, h⟩ := hB.weightedLayerClockMean β hβ hβ4 κ hκ
  refine ⟨dstar, C, W₀, hd, ?_⟩
  intro b hb W hW hW₀ X hX E hE hδ Y hY
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  have hb1' : b < 1 := by linarith
  have hu2 : (W : ℝ)⁻¹ * ((sel W)ᴴ * Y * sel W).trace.re = clockU Y := by
    rw [trace_Y2]; rfl
  have hint : ∫ ω, clockT b E X Y ω ∂freshLaw W b =
      ∫ ω, clockT b E X Y (proj 0 ω) ∂layerLaw W b .separate := by
    have hmp := measurePreserving_proj W b 0
    rw [show freshLaw W b = layerLaw W b .oneBlockOnePort from rfl, ← hmp.map_eq,
      integral_map hmp.measurable.aemeasurable
      (measurable_clockT b E X Y).aestronglyMeasurable]
  have hcm := h b hb W hW hW₀ (bd2 fun _ => X) (bd2_isHermitian hX) E hE
    (by rw [matchedDistance_eq b E hb1' hκ hE hX]; exact hδ) ((sel W)ᴴ * Y * sel W)
    (hY.conjTranspose_mul_mul_same _)
  dsimp only at hcm
  obtain ⟨hI, hle⟩ := hcm
  have hae := ae_clock_eq hGA hb0 hb1 hκ hW hX hE Y
  have hmp := measurePreserving_proj W b 0
  refine ⟨?_, ?_⟩
  · exact (hmp.integrable_comp (measurable_clockT b E X Y).aestronglyMeasurable).mp
      (hI.congr hae)
  · rw [hint, show (fun ω => clockT b E X Y (proj 0 ω)) = clockT b E X Y ∘ proj 0 from rfl,
      ← integral_congr_ae hae]
    rw [matchedDistance_eq b E hb1' hκ hE hX, hu2] at hle
    exact hle

end MovingEnergy

end BlockBand.Endpoints.Clock
