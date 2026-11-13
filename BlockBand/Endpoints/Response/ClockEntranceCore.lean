module

public import BlockBand.Endpoints.Response.ClockEntranceCoreLaw
public import BlockBand.Endpoints.Response.ClockEntranceStep
public import BlockBand.Endpoints.Response.NearSchattenUpper

/-!
# The one-step clock inequality from a one-layer conditional inequality

Part of the clock fractional-entrance lemma: a reduction of the open `ClockFractionalOneStep`.

* `ClockFractionalOneLayer` — **isolated input** (a named `Prop`): the *conditional* one-step
  clock fractional logistic inequality multiplied by the weight, stated pointwise in the old path
  (a.e. on the scalar-jet domain `D_j`) as an integral over the **fresh one-port layer law**
  `freshLaw W b = layerLaw W b .oneBlockOnePort` only, with the old data `X_j = pathX j`,
  `A_j = nearClock j` held fixed:
  `E_ν[(1 + Kδ₀(X_+)) H_p(L*A_jL)] + (c/W) H_p²/γ^p ≤ (1 + C/W)(1 + Kδ₀) H_p
    + (C/W) g^{2(1-p)}γ^p + e(W)`,
  `L = freshL b E X_j ν`, `δ₀(X_+) = ‖W⁻¹ Tr 𝒢_{port,port}(X_j, ν) - a‖`.
* `clockFractionalEntrance_of_oneLayer` — `ClockFractionalEntranceContract` from
  `EdgeClockMomentsContract`, `TransmissionLengthUniformContract`, `ConditionalBlockGUECount` and
  `ClockFractionalOneLayer` (through `clockFractionalEntrance_of_oneStep`).
* `clockFractionalOneStep_of_oneLayer` — `ClockFractionalOneStep` from
  `ConditionalBlockGUECount` and the isolated `ClockFractionalOneLayer`. Proved here:
  - the propagation step: a.s. `A_{j+1} = L*A_jL` and `(z - X_{j+1})⁻¹ = 𝒢_{port,port}` along
    `growthPathLaw` (`cec_nearClock_succ`, `cec_passiveResolvent_succ`; invertibility from
    `cec_ae_good` and `rv_ae_isUnit_fullPathMatrix`, both through
    `ConditionalBlockGUECount`), for `j ≥ 1` past the source (`q((j+1)/W) = 0`);
  - the product structure (`cec_insert_measurePreserving`) and Tonelli in the lower-integral
    form (`lintegral_map_le`, `lintegral_prod_le`, no measurability of `H_p` needed);
  - the invariance of the old-path quantities under the insertion;
  - the integration of the pointwise inequality over `D_j` (the forcing integrand is measurable:
    `ce_measurable_conductance`, `ns_measurable_trace_nearClock`).
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

/-!
## Vocabulary of the one-layer step
-/

/-- `δ₀` of the new near self-energy read from the fresh layer:
`‖W⁻¹ Tr 𝒢_{port,port}(X, ν) - a‖` (equal to `δ₀(X_{j+1})` a.s., `cec_passiveResolvent_succ`). -/
def cec_freshJet0 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ν : LayerSample W .oneBlockOnePort) :
    ℝ :=
  ‖(W : ℂ)⁻¹ * (cec_freshPortBlock b E X ν).trace - matchedA E‖

/-- The one-layer integrand `(1 + K δ_{0,+}) H_p(L*AL)`, `L = freshL b E X ν`. -/
def cec_oneLayerValue (K b E p : ℝ) (X A : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) : ℝ :=
  (1 + K * cec_freshJet0 b E X ν) * fracTrace p ((freshL b E X ν)ᴴ * A * freshL b E X ν)

/-- **Isolated input: the conditional one-layer weighted fractional clock inequality** (the clock
fractional logistic inequality times the weight `1 + K_p δ_{0,+}`), pointwise in the old path:
for `growthPathLaw`-a.e. old sample `ω` in the scalar-jet domain `D_j`, the expectation over the
fresh one-port layer `ν ~ freshLaw W b` (`= layerLaw W b .oneBlockOnePort`) with the old data
`X_j = pathX j ω`, `A_j = nearClock j ω` held fixed satisfies
`E_ν[(1 + Kδ₀(X_+)) H_p(L*A_jL)] + (c/W) H_p²/γ^p ≤ (1 + C/W)(1 + Kδ₀)H_p + (C/W) g^{2(1-p)}γ^p
  + e(W)`.
Same quantifiers, constants and jet domain as `ClockFractionalOneStep`.

Its derivation in the paper is the analytic core: in an `A`-eigenbasis retain `T_ii ≤ 1/2`
(at most `2g` discarded, discarded sum `≤ (2g)^{1-p}γ^p`); the clock covariance gap from
`PassiveCovarianceContract` with `TransmissionLawContract.jetGap` (`σ₊ > |σ₋|`); the event
`‖LL*‖ ≤ K`; the integral Hessian `TransmissionLawContract.fractionalHessian` for
`B = A^{1/2}LL*A^{1/2}`; and three one-port inputs: (a) the passive mean
`E_ν LL* ⪯ (1 + Cδ₀ + CW⁻²)I`, (b) operator-norm moments of `freshL`, (c) the predictable
contraction of `1 + Kδ_{0,+}` with the centered jet correlation.

It is strictly smaller than `ClockFractionalOneStep`: it is the one-step inequality with the
growth dynamics already solved, referring only to the old data `(X_j, A_j)` at a fixed old sample
and to the explicit fresh-layer functions `freshL`, `freshLayer` integrated against the
fresh-layer law. `ClockFractionalOneStep` instead integrates the length-`(j+1)` clock of the
whole path; passing from this `Prop` to it needs the propagation identity `A_{j+1} = L*A_jL`, the
identification of `δ₀(X_{j+1})` with the fresh port block, their almost-sure invertibility
(`ConditionalBlockGUECount`), the product structure of `growthPathLaw` and Tonelli, all proved in
`clockFractionalOneStep_of_oneLayer`. No path quantity at length `j + 1` occurs here. -/
def ClockFractionalOneLayer : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ s₀ s₂ : ℝ, 0 < s₀ → s₀ ≤ s₂ →
      ∃ (K C c d : ℝ) (s : ℂ), 0 ≤ K ∧ 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ IsStationaryJet b E s ∧
        ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
          ∃ e : ℕ → ℝ, Tendsto (fun W : ℕ => (W : ℝ) ^ 2 * e W) atTop (𝓝 0) ∧
          ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, travelLength W t₁ R s₀ ≤ j →
            j < travelLength W t₁ R s₂ →
            ∀ᵐ ω ∂growthPathLaw W b, ω ∈ ce_jetDomain b E s d W j →
              ∫⁻ ν, ENNReal.ofReal (cec_oneLayerValue K b E p (pathX b E W j ω)
                  (nearClock b E W j q ω) ν) ∂freshLaw W b +
                ENNReal.ofReal (c / W) * ENNReal.ofReal
                  (ce_fracClock b E p W j q ω ^ 2 / ce_clockTrace b E W j q ω ^ p) ≤
              ENNReal.ofReal (1 + C / W) *
                  ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω) +
                ENNReal.ofReal (C / W) * ENNReal.ofReal (|pathConductance b E W j ω| ^ (2 * (1 - p)) *
                  ce_clockTrace b E W j q ω ^ p) + ENNReal.ofReal (e W)

/-!
## Invariance of the old path under the insertion
-/

theorem cec_pathX_insert (b E : ℝ) (j : ℕ) (z : GrowthPath W × LayerSample W .oneBlockOnePort) :
    pathX b E W j (cec_insert j z) = pathX b E W j z.1 := by
  simp only [pathX, pathNearSchur, cec_pathAt_insert]

theorem cec_pathConductance_insert (b E : ℝ) (j : ℕ)
    (z : GrowthPath W × LayerSample W .oneBlockOnePort) :
    pathConductance b E W j (cec_insert j z) = pathConductance b E W j z.1 := by
  simp only [pathConductance, pathTransmission, pathNearSchur, cec_pathAt_insert]

theorem cec_nearClock_insert (b E : ℝ) (j : ℕ) (q : ℝ → ℝ)
    (z : GrowthPath W × LayerSample W .oneBlockOnePort) :
    nearClock b E W j q (cec_insert j z) = nearClock b E W j q z.1 := by
  simp only [nearClock, intervalSource, tagResponse, boundaryToInterior, fullInverse,
    fullPathMatrix, cec_pathAt_insert]

theorem cec_jetDomain_insert (b E : ℝ) (s : ℂ) (d : ℝ) (j : ℕ)
    (z : GrowthPath W × LayerSample W .oneBlockOnePort) :
    cec_insert j z ∈ ce_jetDomain b E s d W j ↔ z.1 ∈ ce_jetDomain b E s d W j := by
  unfold ce_jetDomain ce_jet0 ce_jet1
  simp only [Set.mem_ofPred_eq, cec_pathX_insert, cec_pathConductance_insert]

/-- **The retained next integrand through the insertion**: on the good events, the length-`(j+1)`
weighted clock of `insert(ω, ν)` on `D_j` is the one-layer value of `(X_j(ω), A_j(ω), ν)`. -/
theorem cec_retained_integrand_eq {K b E p : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {j : ℕ} (hj : 1 ≤ j) {q : ℝ → ℝ} (hq : q (((j + 1 : ℕ) : ℝ) / W) = 0) (s : ℂ) (d : ℝ)
    (z : GrowthPath W × LayerSample W .oneBlockOnePort)
    (hg : cec_good E W j (cec_insert j z)) (hg' : cec_good E W (j + 1) (cec_insert j z))
    (hM : IsUnit (fullPathMatrix b E W j (cec_insert j z)).det)
    (hM' : IsUnit (fullPathMatrix b E W (j + 1) (cec_insert j z)).det) :
    (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
        (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω)) (cec_insert j z) =
      (ce_jetDomain b E s d W j).indicator (fun ω => ENNReal.ofReal
        (cec_oneLayerValue K b E p (pathX b E W j ω) (nearClock b E W j q ω) z.2)) z.1 := by
  by_cases hz : z.1 ∈ ce_jetDomain b E s d W j
  · rw [Set.indicator_of_mem ((cec_jetDomain_insert b E s d j z).2 hz),
      Set.indicator_of_mem hz]
    congr 1
    unfold ce_weight ce_jet0 ce_fracClock cec_oneLayerValue cec_freshJet0 jetDistance0
    rw [cec_passiveResolvent_succ hb hE1 hE2 hj hg hg' hM hM',
      cec_nearClock_succ hb hE1 hE2 hj hg hM hM' hq, cec_pathX_insert, cec_nearClock_insert,
      cec_fresh_insert]
  · rw [Set.indicator_of_notMem (fun h => hz ((cec_jetDomain_insert b E s d j z).1 h)),
      Set.indicator_of_notMem hz]

/-!
## The reduction
-/

/-- **`ClockFractionalOneStep` from the one-layer conditional inequality.** Hypotheses:
`ConditionalBlockGUECount` (almost-sure invertibility in the propagation step) and the isolated
`ClockFractionalOneLayer`. -/
theorem clockFractionalOneStep_of_oneLayer (hCount : ConditionalBlockGUECount)
    (hOne : ClockFractionalOneLayer) : ClockFractionalOneStep := by
  intro b hb hb' E hE hE' p hp hp' s₀ s₂ hs₀ hs₀₂
  obtain ⟨K, C, c, d, s, hK, hC, hc, hd, hs, hsrc⟩ := hOne b hb hb' E hE hE' p hp hp' s₀ s₂ hs₀ hs₀₂
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
    (cec_oneLayerValue K b E p (pathX b E W j ω) (nearClock b E W j q ω) ν) ∂freshLaw W b
  -- the retained next moment through item (d)
  have hret : ce_retainedNext K b E p s d W j q ≤ ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b := by
    unfold ce_retainedNext
    calc _ = ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal
            (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω)) ω
          ∂((growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort)).map (cec_insert j) := by
          rw [hMP.map_eq]
      _ ≤ ∫⁻ z, D.indicator (fun ω => ENNReal.ofReal
            (ce_weight K b E W (j + 1) ω * ce_fracClock b E p W (j + 1) q ω)) (cec_insert j z)
          ∂(growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort) :=
          lintegral_map_le _ hMP.measurable.aemeasurable
      _ = ∫⁻ z, D.indicator (fun ω => ENNReal.ofReal
            (cec_oneLayerValue K b E p (pathX b E W j ω) (nearClock b E W j q ω) z.2)) z.1
          ∂(growthPathLaw W b).prod (layerLaw W b .oneBlockOnePort) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hz] with z hz
          exact cec_retained_integrand_eq hb1 hE hE' hj hqj s d z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
      _ ≤ ∫⁻ ω, ∫⁻ ν, D.indicator (fun ω => ENNReal.ofReal
            (cec_oneLayerValue K b E p (pathX b E W j ω) (nearClock b E W j q ω) ν)) ω
          ∂layerLaw W b .oneBlockOnePort ∂growthPathLaw W b := lintegral_prod_le _
      _ = ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b := by
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ D
          · simp only [Set.indicator_of_mem hω, G, freshLaw]
          · simp only [Set.indicator_of_notMem hω, lintegral_const, zero_mul]
  -- the pointwise inequality, extended by zero off `D`
  set u : GrowthPath W → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω)
  set v : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (|pathConductance b E W j ω| ^ (2 * (1 - p)) * ce_clockTrace b E W j q ω ^ p)
  set h2 : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (ce_fracClock b E p W j q ω ^ 2 / ce_clockTrace b E W j q ω ^ p)
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
  calc ce_retainedNext K b E p s d W j q + ENNReal.ofReal (c / W) * ce_concavityMoment b E p s d W j q
      ≤ ∫⁻ ω, D.indicator G ω ∂growthPathLaw W b +
          ∫⁻ ω, ENNReal.ofReal (c / W) * D.indicator h2 ω ∂growthPathLaw W b := by
        rw [lintegral_const_mul' _ _ hfin3]
        exact add_le_add_left hret _
    _ ≤ ∫⁻ ω, (D.indicator G ω + ENNReal.ofReal (c / W) * D.indicator h2 ω) ∂growthPathLaw W b :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (1 + C / W) * u ω +
          (ENNReal.ofReal (C / W) * v ω + ENNReal.ofReal (e W))) ∂growthPathLaw W b :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (1 + C / W) * ce_weightedMoment K b E p W j q +
          ENNReal.ofReal (C / W) * ce_forcingMoment b E p W j q + ENNReal.ofReal (e W) := by
        have hg : Measurable fun ω => ENNReal.ofReal (C / W) * v ω + ENNReal.ofReal (e W) :=
          (hv.const_mul _).add measurable_const
        rw [lintegral_add_right _ hg,
          lintegral_const_mul' _ _ hfin1, lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ hfin2, lintegral_const, measure_univ, mul_one, ← add_assoc]
        rfl

/-- **`ClockFractionalEntranceContract` from the one-layer input**: compose
`clockFractionalOneStep_of_oneLayer` with `clockFractionalEntrance_of_oneStep`. Hypotheses:
`EdgeClockMomentsContract`, `TransmissionLengthUniformContract`, `ConditionalBlockGUECount`, and
the isolated `ClockFractionalOneLayer`. -/
theorem clockFractionalEntrance_of_oneLayer (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hOne : ClockFractionalOneLayer) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_oneStep hECM hTLU (clockFractionalOneStep_of_oneLayer hCount hOne)

end BlockBand.Endpoints
