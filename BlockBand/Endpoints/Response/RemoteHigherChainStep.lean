module

public import BlockBand.Endpoints.Response.RemoteHigherChainWeight
public import BlockBand.Endpoints.Response.RemoteHigherNearDefs

/-!
# The higher one-step clock inequality from the one-layer inequality

* `rhc_retainedNext`, `rhc_concavityMoment`, `rhc_forcingMoment`: the moments of the step,
  `E[1_{D_j}(1 + Kδ₀)H_p(A_{j+1})^r]`, `E[1_{D_j} H_p^{r+1}/γ^p]`, `E[|g|^{(r+1)(1-p)}γ^{pr}]`.
* `RhcHigherOneStep`: the weighted higher one-step inequality (the `r`-analogue of
  `ClockFractionalOneStep`), proved in `rhcHigherOneStep_of_oneLayer`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.Inputs

variable {W : ℕ}

/-- The retained next higher clock `E[1_{D_j}(1 + Kδ₀) H_p(A_{j+1})^r]` (old-length jet domain). -/
def rhc_retainedNext (K b E p r : ℝ) (s : ℂ) (d : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
    (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω ^ r)) ω ∂growthPathLaw W b

/-- The retained higher concavity term `E[1_D H_p^{r+1}/γ^p]`. -/
def rhc_concavityMoment (b E p r : ℝ) (s : ℂ) (d : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
    (ce_fracClock b E p W j q ω ^ (r + 1) / ce_clockTrace b E W j q ω ^ p)) ω ∂growthPathLaw W b

/-- The higher forcing `E[|g|^{(r+1)(1-p)} γ^{pr}]`. -/
def rhc_forcingMoment (b E p r : ℝ) (W j : ℕ) (q : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ ((r + 1) * (1 - p)) *
    ce_clockTrace b E W j q ω ^ (p * r)) ∂growthPathLaw W b

/-- The weighted higher one-step inequality (the higher logistic inequality times the weight,
integrated over the jet domain `D_j` of the old path): the `r`-analogue of
`ClockFractionalOneStep`, with `y_j = rhn_weightedHigherMoment`:
`E[1_{D_j} y'_{j+1}] + (c/W) E[1_{D_j} H_p^{r+1}/γ^p] ≤ (1 + C/W) y_j
  + (C/W) E[|g|^{(r+1)(1-p)}γ^{pr}] + e(W)`. Proved in `rhcHigherOneStep_of_oneLayer`. -/
def RhcHigherOneStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ (K C c d : ℝ) (s : ℂ), 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ IsStationaryJet b E s ∧
        ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j →
            j < travelLength W t₁ R s₂ →
            rhc_retainedNext K b E p r s d W j q +
                ENNReal.ofReal (c / W) * rhc_concavityMoment b E p r s d W j q ≤
              ENNReal.ofReal (1 + C / W) * rhn_weightedHigherMoment K b E p r W j q +
                ENNReal.ofReal (C / W) * rhc_forcingMoment b E p r W j q + ENNReal.ofReal (e W)

/-- The retained next higher integrand through the insertion: on the good events, the
length-`(j+1)` weighted higher clock of `insert(ω, ν)` on `D_j` is the higher one-layer value of
`(X_j(ω), A_j(ω), ν)`. -/
theorem rhc_retained_integrand_eq {K b E p r : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {j : ℕ} (hj : 1 ≤ j) {q : ℝ → ℝ} (hq : q (((j + 1 : ℕ) : ℝ) / W) = 0) (s : ℂ) (d : ℝ)
    (z : GrowthPath W × LayerSample W .oneBlockOnePort)
    (hg : cec_good E W j (cec_insert j z)) (hg' : cec_good E W (j + 1) (cec_insert j z))
    (hM : IsUnit (fullPathMatrix b E W j (cec_insert j z)).det)
    (hM' : IsUnit (fullPathMatrix b E W (j + 1) (cec_insert j z)).det) :
    (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
        (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω ^ r)) (cec_insert j z) =
      (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
        (rhc_oneLayerValue K b E p r (pathX b E W j ω) (nearClock b E W j q ω) z.2)) z.1 := by
  by_cases hz : z.1 ∈ ce_jetDomain b E s d W j
  · rw [Set.indicator_of_mem ((cec_jetDomain_insert b E s d j z).2 hz),
      Set.indicator_of_mem hz]
    congr 1
    unfold ce_weight ce_jet0 ce_fracClock rhc_oneLayerValue cec_freshJet0 jetDistance0
    rw [cec_passiveResolvent_succ hb hE1 hE2 hj hg hg' hM hM',
      cec_nearClock_succ hb hE1 hE2 hj hg hM hM' hq, cec_pathX_insert, cec_nearClock_insert,
      cec_fresh_insert]
  · rw [Set.indicator_of_notMem (fun h => hz ((cec_jetDomain_insert b E s d j z).1 h)),
      Set.indicator_of_notMem hz]

/-- **`RhcHigherOneStep` from the higher one-layer inequality.** Hypotheses:
`ConditionalBlockGUECount` and `ClockHigherOneLayer`.
-/
theorem rhcHigherOneStep_of_oneLayer (hCount : ConditionalBlockGUECount)
    (hOne : ClockHigherOneLayer) : RhcHigherOneStep := by
  intro b hb hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  obtain ⟨K, C, c, d, s, hK, hC, hc, hd, hs, hsrc⟩ :=
    hOne b hb hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  refine ⟨K, C, c, d, s, hK, hC, hc, hd, hs, fun t₁ R q hq => ?_⟩
  obtain ⟨e, he, W₀, hW₀⟩ := hsrc t₁ R q hq
  refine ⟨e, he, max W₀ (⌈1 / s₀⌉₊ + 1), fun W hW j hj0 hj1 => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hWs : (⌈1 / s₀⌉₊ + 1 : ℕ) ≤ W := le_trans (le_max_right _ _) hW
  have hTR : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  have hWpos' : (1 : ℝ) / s₀ < W := by
    have h1 := Nat.le_ceil (1 / s₀)
    have h2 : ((⌈1 / s₀⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hWs
    push_cast at h2; linarith
  have hWpos : 0 < W := by
    have : (0 : ℝ) < W := lt_trans (by positivity) hWpos'
    exact_mod_cast this
  have hWR : (0 : ℝ) < W := by exact_mod_cast hWpos
  have hWs₀ : 1 < (W : ℝ) * s₀ := by
    rw [div_lt_iff₀ hs₀] at hWpos'; linarith
  -- `1 ≤ j` and the new block carries no tag weight
  have hj : 1 ≤ j := by
    refine le_trans ?_ hj0
    unfold travelLength
    rw [Nat.one_le_floor_iff]
    nlinarith
  have hqj : q (((j + 1 : ℕ) : ℝ) / W) = 0 := by
    refine hq.2.2.2.1.2.1 _ fun hmem => ?_
    have hlt : (W : ℝ) * (t₁ + R + s₀) < ((j + 1 : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((W : ℝ) * (t₁ + R + s₀))
      have hj0' : ((travelLength W t₁ R s₀ : ℕ) : ℝ) ≤ j := by exact_mod_cast hj0
      unfold travelLength at hj0'
      push_cast; linarith
    have hle := hmem.2
    rw [div_le_iff₀ hWR] at hle
    nlinarith
  -- the good events
  have hgood : ∀ᵐ ω' ∂growthPathLaw W b, cec_good E W j ω' ∧ cec_good E W (j + 1) ω' ∧
      IsUnit (fullPathMatrix b E W j ω').det ∧ IsUnit (fullPathMatrix b E W (j + 1) ω').det := by
    filter_upwards [cec_ae_good (E := E) hCount hb' hWpos j,
      cec_ae_good (E := E) hCount hb' hWpos (j + 1),
      rv_ae_isUnit_fullPathMatrix hCount hb' hE hE' hWpos j,
      rv_ae_isUnit_fullPathMatrix hCount hb' hE hE' hWpos (j + 1)] with ω' h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hb1 : b < 1 := by linarith
  have hMP := cec_insert_measurePreserving W b j
  have hz := hMP.quasiMeasurePreserving.ae hgood
  have : SFinite (layerLaw W b .oneBlockOnePort) := by unfold layerLaw; infer_instance
  set D := ce_jetDomain b E s d W j
  set G : GrowthPath W → ℝ≥0∞ := fun ω => ∫⁻ ν, ENNReal.ofReal
    (rhc_oneLayerValue K b E p r (pathX b E W j ω) (nearClock b E W j q ω) ν) ∂freshLaw W b
  -- the retained next moment through the insertion identity
  have hret : rhc_retainedNext K b E p r s d W j q ≤ ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b := by
    unfold rhc_retainedNext
    calc _ = ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal
            (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω ^ r)) ω
          ∂((growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort)).map (cec_insert j) := by
          rw [hMP.map_eq]
      _ ≤ ∫⁻ z, D.indicator (fun ω => ENNReal.ofReal
            (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω ^ r)) (cec_insert j z)
          ∂(growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort) :=
          lintegral_map_le _ hMP.measurable.aemeasurable
      _ = ∫⁻ z, D.indicator (fun ω => ENNReal.ofReal
            (rhc_oneLayerValue K b E p r (pathX b E W j ω) (nearClock b E W j q ω) z.2)) z.1
          ∂(growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hz] with z hz
          exact rhc_retained_integrand_eq hb1 hE hE' hj hqj s d z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
      _ ≤ ∫⁻ ω, ∫⁻ ν, D.indicator (fun ω => ENNReal.ofReal
            (rhc_oneLayerValue K b E p r (pathX b E W j ω) (nearClock b E W j q ω) ν)) ω
          ∂layerLaw W b .oneBlockOnePort ∂growthPathLaw W b := lintegral_prod_le _
      _ = ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ D
          · simp only [Set.indicator_of_mem hω, G, freshLaw]
          · simp only [Set.indicator_of_notMem hω, lintegral_const, zero_mul]
  -- the pointwise inequality, extended by zero off `D`
  set u : GrowthPath W → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r)
  set v : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (|pathConductance b E W j ω| ^ ((r + 1) * (1 - p)) * ce_clockTrace b E W j q ω ^ (p * r))
  set h2 : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (ce_fracClock b E p W j q ω ^ (r + 1) / ce_clockTrace b E W j q ω ^ p)
  have hv : Measurable v := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact (ce_measurable_conductance b E W j).abs.pow_const _
    · exact (ns_measurable_trace_nearClock b E W j q).pow_const _
  have hpt : ∀ᵐ ω ∂growthPathLaw W b,
      D.indicator G ω + ENNReal.ofReal (c / W) * D.indicator h2 ω ≤
        ENNReal.ofReal (1 + C / W) * u ω + (ENNReal.ofReal (C / W) * v ω + ENNReal.ofReal (e W)) := by
    filter_upwards [hW₀ W hW0 j hj0 hj1] with ω hω
    by_cases hD : ω ∈ D
    · rw [Set.indicator_of_mem hD, Set.indicator_of_mem hD, ← add_assoc]
      exact hω hD
    · rw [Set.indicator_of_notMem hD, Set.indicator_of_notMem hD, mul_zero, add_zero]
      exact bot_le
  -- integrate
  have hfin1 : ENNReal.ofReal (1 + C / W) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin2 : ENNReal.ofReal (C / W) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfin3 : ENNReal.ofReal (c / W) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hprob : IsProbabilityMeasure (growthPathLaw W b) := by
    unfold growthPathLaw; infer_instance
  calc rhc_retainedNext K b E p r s d W j q +
        ENNReal.ofReal (c / W) * rhc_concavityMoment b E p r s d W j q
      ≤ ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b +
          ∫⁻ ω, ENNReal.ofReal (c / W) * D.indicator h2 ω ∂growthPathLaw W b := by
        rw [lintegral_const_mul' _ _ hfin3]
        exact add_le_add_left hret _
    _ ≤ ∫⁻ ω, (D.indicator G ω + ENNReal.ofReal (c / W) * D.indicator h2 ω) ∂growthPathLaw W b :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (1 + C / W) * u ω +
          (ENNReal.ofReal (C / W) * v ω + ENNReal.ofReal (e W))) ∂growthPathLaw W b :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (1 + C / W) * rhn_weightedHigherMoment K b E p r W j q +
          ENNReal.ofReal (C / W) * rhc_forcingMoment b E p r W j q + ENNReal.ofReal (e W) := by
        have hg : Measurable fun ω => ENNReal.ofReal (C / W) * v ω + ENNReal.ofReal (e W) :=
          (hv.const_mul _).add measurable_const
        rw [lintegral_add_right _ hg,
          lintegral_const_mul' _ _ hfin1, lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ hfin2, lintegral_const, measure_univ, mul_one, ← add_assoc]
        rfl

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.LayersOnePort in

/-- **`RhcHigherOneStep` from the one-port contracts and `OnePortJetContraction`** (the higher
one-step of the remote higher-order theorem). Hypotheses: `ConditionalBlockGUECount`,
`TransmissionLawContract`, `PassiveCovarianceContract`, `PassiveSourceMixingContract`,
`OnePortPassiveMeanContract`, `OnePortOperatorMomentsContract` and `OnePortJetContraction`: the
inputs of the `r = 1` chain `clockFractionalEntrance_of_onePort'` except
`EdgeClockMomentsContract` and `TransmissionLengthUniformContract`, which enter only the
expectation recursion. The `r = 1` one-layer logistic inequality is
`clockLayerLogistic_of_jensenGap (clockLayerJensenGap_of_taylor … fractionalTraceJensenGap_holds …)`.
-/
theorem rhcHigherOneStep_of_onePort (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hJet : OnePortJetContraction) : RhcHigherOneStep :=
  rhcHigherOneStep_of_oneLayer hCount
    (clockHigherOneLayer_of hTL
      (clockLayerHigherLogistic_of
        (clockLayerLogistic_of_jensenGap
          (clockLayerJensenGap_of_taylor hPC hTL hPSM fractionalTraceJensenGap_holds
            (onePortPassiveMean_of_contract hPM) (onePortOperatorMoments_of_contract hOM))
          (onePortPassiveMean_of_contract hPM))
        (onePortPassiveMean_of_contract hPM) (onePortOperatorMoments_of_contract hOM) hPSM)
      (onePortOperatorMoments_of_contract hOM) hJet)

end BlockBand.Endpoints
