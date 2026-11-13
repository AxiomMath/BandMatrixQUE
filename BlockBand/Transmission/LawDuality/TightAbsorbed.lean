module

public import BlockBand.Transmission.LawDuality.ModulusZero
public import BlockBand.Transmission.LawDuality.BorelGiry
public import Mathlib.Analysis.Matrix.Order

/-!
# The trace modulus for every absorption profile, from absorbed power-sum tightness

The `κ ≡ 0` case (`transmissionTraceModulus_zero`) follows from `hTG.tight` only. Its proof
uses two facts: `tight` for the
power sums, and the bridge `∫ s^j dμ_W(t) = Tr T_{⌊Wt⌋}^{j+1}`. The bridge holds for every
`κ ≥ 0` (`ae_integral_pow_transmissionProcess`, since `0 ⪯ T^κ ⪯ I`). So the proof is
rewritten here for an arbitrary `κ ≥ 0` with the `tight` clause *for that `κ`* as hypothesis
(`PowerTightAt b E κ`). At `κ ≡ 0` this is exactly `hTG.tight` (`powerTightAt_zero`).

* `absorbedPowerTrace b E κ W k t = Re Tr (T^κ_{⌊Wt⌋})^k`; `PowerTightAt`; `AbsorbedPowerTight`.
* `measurable_pathTransmission`, `measurable_of_moments`, **`aemeasurable_transmissionProcess`**
  (the finite-`W` trace-measure process is a.e.-measurable for the Giry σ-algebra, every `κ ≥ 0`).
* **`traceModulus_of_powerTightAt`**: `PowerTightAt b E κ` ⇒ the modulus clause for `κ`.
* **`transmissionTraceModulus_of_tight`**: `hTG ∧ AbsorbedPowerTight → TransmissionTraceModulus`;
  `transmissionTraceModulusAbsorbed_of`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal ComplexOrder

/-- `P^κ_k(t) = Re Tr (T^κ_{⌊Wt⌋})^k`, the power sums of the absorbed path. -/
def absorbedPowerTrace (b E : ℝ) (κ : ℝ → ℝ) (W k : ℕ) (t : ℝ) (ω : GrowthPath W) : ℝ :=
  ((pathTransmission b E κ W ⌊(W : ℝ) * t⌋₊ ω) ^ k).trace.re

/-- **The `tight` clause of the transmission generator theorem for the path with profile `κ`**
(`TransmissionGeneratorContract.tight` at fixed `b, E`, with `powerTrace` replaced by
`absorbedPowerTrace … κ`): one-time tightness and the `[ε, T]` modulus of `P^κ_k`. -/
def PowerTightAt (b E : ℝ) (κ : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
    (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | M < |absorbedPowerTrace b E κ W k ε ω|} ≤ ENNReal.ofReal θ) ∧
    (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |absorbedPowerTrace b E κ W k t ω - absorbedPowerTrace b E κ W k t' ω|} ≤
        ENNReal.ofReal θ)

/-- **Tightness of the absorbed power sums**, for every admissible profile `κ ≠ 0` (one-time
tightness and the `[ε,T]` sup-modulus of `Tr (T^κ_{⌊Wt⌋})^k`). Proved from the input hypotheses
as `Absorbed.absorbedPowerTight_holds`. -/
def AbsorbedPowerTight : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    κ ≠ (fun _ => 0) → PowerTightAt b E κ

/-- At `κ ≡ 0`, `PowerTightAt` is the `hTG.tight`. -/
theorem powerTightAt_zero (hTG : TransmissionGeneratorContract) {b : ℝ} (hb : 0 < b)
    (hb2 : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) : PowerTightAt b E (fun _ => 0) :=
  hTG.tight b hb hb2 E hE1 hE2

theorem powerTightAt_of (hTG : TransmissionGeneratorContract) (hAbs : AbsorbedPowerTight)
    {b : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) : PowerTightAt b E κ := by
  by_cases h0 : κ = fun _ => 0
  · subst h0; exact powerTightAt_zero hTG hb hb2 hE1 hE2
  · exact hAbs b hb hb2 E hE1 hE2 κ hκ h0

/-!
## Measurability of the finite-`W` trace-measure process
-/

variable {W : ℕ}

theorem measurable_pathTransmission (b E : ℝ) (κ : ℝ → ℝ) (r : ℕ) :
    Measurable (pathTransmission b E κ W r) := by
  have hc : Continuous fun Q : Matrix (Fin W) (Fin W) ℂ => (((4 * etaZ b E : ℝ)) : ℂ) • Q :=
    continuous_const_smul _
  exact hc.measurable.comp ((SourceMixing.mu_measurable_passiveQ b E).comp
    ((Bridge.pathNearSchur_adapted b E κ W r).mono (Generator.growthSigma_le W r) le_rfl))

/-- A map into `FiniteMeasure [0,1]` is measurable as soon as all its moments are. -/
theorem measurable_of_moments {α : Type*} [MeasurableSpace α] {ν : α → FiniteMeasure unitInterval}
    (h : ∀ j, Measurable fun a => moment j (ν a)) : Measurable ν := by
  have hm : Measurable (momentVec ∘ ν) := measurable_pi_iff.2 h
  refine measurable_of_isOpen fun U hU => ?_
  obtain ⟨V, hV, rfl⟩ := isInducing_momentVec.isOpen_iff.1 hU
  exact hm hV.measurableSet

open scoped Classical in
/-- The clamped trace measure: `traceMeasure T` on `{0 ⪯ T ⪯ I}`, `0` elsewhere. -/
def clampedTraceMeasure (T : Matrix (Fin W) (Fin W) ℂ) : FiniteMeasure unitInterval :=
  if T.PosSemidef ∧ (1 - T).PosSemidef then traceMeasure T else 0

theorem measurableSet_unitBox :
    MeasurableSet {T : Matrix (Fin W) (Fin W) ℂ | T.PosSemidef ∧ (1 - T).PosSemidef} :=
  (Matrix.posSemidef_is_closed.measurableSet).inter
    ((Matrix.posSemidef_is_closed.preimage (continuous_const.sub continuous_id)).measurableSet)

theorem measurable_clampedTraceMeasure :
    Measurable (clampedTraceMeasure (W := W)) := by
  classical
  refine measurable_of_moments fun j => ?_
  have e : (fun T : Matrix (Fin W) (Fin W) ℂ => moment j (clampedTraceMeasure T)) =
      {T : Matrix (Fin W) (Fin W) ℂ | T.PosSemidef ∧ (1 - T).PosSemidef}.piecewise
        (fun T => (T ^ (j + 1)).trace.re) (fun _ => 0) := by
    funext T
    by_cases hT : T.PosSemidef ∧ (1 - T).PosSemidef
    · have hm : T ∈ {T : Matrix (Fin W) (Fin W) ℂ | T.PosSemidef ∧ (1 - T).PosSemidef} := hT
      rw [Set.piecewise_eq_of_mem _ _ _ hm, clampedTraceMeasure, ite_eq_left hT, moment]
      exact integral_pow_traceMeasure hT.1 hT.2 j
    · have hm : T ∉ {T : Matrix (Fin W) (Fin W) ℂ | T.PosSemidef ∧ (1 - T).PosSemidef} := hT
      rw [Set.piecewise_eq_of_notMem _ _ _ hm, clampedTraceMeasure,
        ite_eq_right hT, moment]
      simp
  rw [e]
  refine Measurable.piecewise measurableSet_unitBox ?_ measurable_const
  exact (Complex.continuous_re.comp (continuous_id.pow (j + 1)).matrix_trace).measurable

/-- **The finite-`W` trace-measure process is a.e.-measurable** (Giry σ-algebra), every
`κ ≥ 0`, every `t`. -/
theorem aemeasurable_transmissionProcess {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s)
    (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (t : ℝ) :
    AEMeasurable (transmissionProcess b E κ W t) (growthPathLaw W b) := by
  refine ⟨fun ω => clampedTraceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * t⌋₊ ω),
    measurable_clampedTraceMeasure.comp (measurable_pathTransmission b E κ _), ?_⟩
  filter_upwards [Bridge.ae_passiveSample W hκ hb hE1 hE2] with ω hω
  rw [clampedTraceMeasure, ite_eq_left ⟨Bridge.pathTransmission_posSemidef hω _,
    Bridge.one_sub_pathTransmission_posSemidef b E κ W _ ω⟩]
  rfl

/-!
## The modulus from `PowerTightAt`
-/

/-- The power-sum bridge for the path with profile `κ ≥ 0`. -/
theorem ae_moment_eq_absorbedPowerTrace {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (t : ℝ),
      moment j (transmissionProcess b E κ W t ω) = absorbedPowerTrace b E κ W (j + 1) t ω :=
  ae_integral_pow_transmissionProcess hκ hb hE1 hE2

/-- **The modulus clause for the path with profile `κ ≥ 0`, from `PowerTightAt b E κ`** (the
proof of `transmissionTraceModulus_zero`, with `κ` general). -/
theorem traceModulus_of_powerTightAt {b E : ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) (hPT : PowerTightAt b E κ) {ε T : ℝ} (hε : 0 < ε)
    (f : C(unitInterval, ℝ)) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |∫ x, f x ∂(transmissionProcess b E κ W t ω : Measure unitInterval) -
          ∫ x, f x ∂(transmissionProcess b E κ W t' ω : Measure unitInterval)|} ≤
        ENNReal.ofReal θ := by
  rcases le_or_gt T ε with hT | hT
  · refine ⟨1, one_pos, 0, fun W _ => le_trans (measure_mono (t := ∅) ?_) (by simp)⟩
    rintro ω ⟨t, ht, t', ht', -, hlt⟩
    have h1 : t = ε := le_antisymm (ht.2.trans hT) ht.1
    have h2 : t' = ε := le_antisymm (ht'.2.trans hT) ht'.1
    subst h1 h2
    simp at hlt
    linarith
  obtain ⟨hTi1, hMod1⟩ := hPT 1 le_rfl ε T hε hT
  obtain ⟨M, Wa, hM⟩ := hTi1 (θ / 4) (by positivity)
  obtain ⟨δ1, hδ1, Wb, hB⟩ := hMod1 1 (θ / 4) one_pos (by positivity)
  set n : ℕ := ⌈(T - ε) / δ1⌉₊ with hn_def
  set M' : ℝ := |M| + n with hM'_def
  have hM'0 : 0 ≤ M' := by positivity
  set η' : ℝ := η / (4 * (M' + 1)) with hη'_def
  have hη'0 : 0 < η' := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f η' hη'0
  set d := p.natDegree
  set C : ℝ := ∑ i ∈ Finset.range (d + 1), |p.coeff i| + 1 with hC_def
  have hC0 : 0 < C := by positivity
  have hmod := fun i : ℕ => (hPT (i + 1) (by omega) ε T hε hT).2
    (η / (2 * C)) (θ / (2 * (d + 1))) (by positivity) (by positivity)
  choose δs hδs Ws hWs using hmod
  have hne : (Finset.range (d + 1)).Nonempty := ⟨0, by simp⟩
  set δ := min δ1 ((Finset.range (d + 1)).inf' hne δs) with hδ_def
  have hδ0 : 0 < δ := lt_min hδ1 ((Finset.lt_inf'_iff hne).2 fun i _ => hδs i)
  refine ⟨δ, hδ0, max (max Wa Wb) ((Finset.range (d + 1)).sup Ws), fun W hW => ?_⟩
  have hWa : Wa ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWb : Wb ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hWi : ∀ i ∈ Finset.range (d + 1), Ws i ≤ W := fun i hi =>
    (Finset.le_sup (f := Ws) hi).trans ((le_max_right _ _).trans hW)
  set μW := transmissionProcess b E κ W
  let PT : ℕ → ℝ → GrowthPath W → ℝ := fun k t ω => absorbedPowerTrace b E κ W k t ω
  let N : Set (GrowthPath W) :=
    {ω | ¬ ∀ (j : ℕ) (t : ℝ), moment j (μW t ω) = PT (j + 1) t ω}
  let A : Set (GrowthPath W) := {ω | M < |PT 1 ε ω|}
  let B : Set (GrowthPath W) := {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ1 ∧
    1 < |PT 1 t ω - PT 1 t' ω|}
  let Cs : ℕ → Set (GrowthPath W) := fun i => {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T,
    |t - t'| ≤ δs i ∧ η / (2 * C) < |PT (i + 1) t ω - PT (i + 1) t' ω|}
  have hN : growthPathLaw W b N = 0 :=
    ae_iff.1 (ae_moment_eq_absorbedPowerTrace hκ hb hE1 hE2)
  have hsub : {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
      η < |∫ x, f x ∂(μW t ω : Measure unitInterval) - ∫ x, f x ∂(μW t' ω : Measure unitInterval)|}
      ⊆ N ∪ A ∪ B ∪ ⋃ i ∈ Finset.range (d + 1), Cs i := by
    rintro ω ⟨t, ht, t', ht', htt, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨⟨hNω, hAω⟩, hBω⟩, hCω⟩ := hcon
    have hG : ∀ (j : ℕ) (t : ℝ), moment j (μW t ω) = PT (j + 1) t ω := by
      simpa [N] using hNω
    have hA' : |PT 1 ε ω| ≤ M := by simpa [A] using hAω
    have hB' : ∀ u ∈ Icc ε T, ∀ u' ∈ Icc ε T, |u - u'| ≤ δ1 → |PT 1 u ω - PT 1 u' ω| ≤ 1 :=
      fun u hu u' hu' huu => not_lt.1 fun h => hBω ⟨u, hu, u', hu', huu, h⟩
    have hC' : ∀ i ∈ Finset.range (d + 1), |PT (i + 1) t ω - PT (i + 1) t' ω| ≤ η / (2 * C) :=
      fun i hi => not_lt.1 fun h => hCω i hi ⟨t, ht, t', ht',
        htt.trans ((min_le_right _ _).trans (Finset.inf'_le δs hi)), h⟩
    have hmass : ∀ u ∈ Icc ε T, (μW u ω : Measure unitInterval).real univ ≤ M' := by
      intro u hu
      have hch := abs_sub_le_nat_of_modulus (g := fun u => PT 1 u ω) hδ1 hB' n u hu (by
        have : (T - ε) / δ1 ≤ n := Nat.le_ceil _
        rw [div_le_iff₀ hδ1] at this
        linarith [hu.2])
      rw [real_univ_eq_moment_zero, hG 0 u]
      have := abs_sub_abs_le_abs_sub (PT 1 u ω) (PT 1 ε ω)
      have := le_abs_self (PT 1 u ω)
      have := le_abs_self M
      linarith
    have happ := fun u => abs_integral_sub_poly_le (μW u ω) hp
    have hdiff : |∑ i ∈ Finset.range (d + 1), p.coeff i * moment i (μW t ω) -
        ∑ i ∈ Finset.range (d + 1), p.coeff i * moment i (μW t' ω)| ≤
        (∑ i ∈ Finset.range (d + 1), |p.coeff i|) * (η / (2 * C)) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
      rw [← mul_sub, abs_mul, hG i t, hG i t']
      exact mul_le_mul_of_nonneg_left (hC' i hi) (abs_nonneg _)
    have hS : (∑ i ∈ Finset.range (d + 1), |p.coeff i|) * (η / (2 * C)) < η / 2 := by
      rw [show η / 2 = C * (η / (2 * C)) by field_simp]
      exact mul_lt_mul_of_pos_right (by rw [hC_def]; linarith) (by positivity)
    have hm1 := hmass t ht
    have hm2 := hmass t' ht'
    have hη'M : η' * M' ≤ η / 4 := by
      rw [hη'_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h1 := happ t
    have h2 := happ t'
    have h3 : η' * (μW t ω : Measure unitInterval).real univ ≤ η' * M' :=
      mul_le_mul_of_nonneg_left hm1 hη'0.le
    have h4 : η' * (μW t' ω : Measure unitInterval).real univ ≤ η' * M' :=
      mul_le_mul_of_nonneg_left hm2 hη'0.le
    have key := abs_sub_le (∫ x, f x ∂(μW t ω : Measure unitInterval))
      (∑ i ∈ Finset.range (d + 1), p.coeff i * moment i (μW t ω))
      (∫ x, f x ∂(μW t' ω : Measure unitInterval))
    have key2 := abs_sub_le (∑ i ∈ Finset.range (d + 1), p.coeff i * moment i (μW t ω))
      (∑ i ∈ Finset.range (d + 1), p.coeff i * moment i (μW t' ω))
      (∫ x, f x ∂(μW t' ω : Measure unitInterval))
    rw [abs_sub_comm] at h2
    linarith
  calc growthPathLaw W b _ ≤ growthPathLaw W b (N ∪ A ∪ B ∪ ⋃ i ∈ Finset.range (d + 1), Cs i) :=
        measure_mono hsub
    _ ≤ growthPathLaw W b N + growthPathLaw W b A + growthPathLaw W b B +
          ∑ i ∈ Finset.range (d + 1), growthPathLaw W b (Cs i) := by
        refine (measure_union_le _ _).trans (add_le_add ?_ (measure_biUnion_finset_le _ _))
        exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (θ / 4) + ENNReal.ofReal (θ / 4) +
          ∑ i ∈ Finset.range (d + 1), ENNReal.ofReal (θ / (2 * (d + 1))) := by
        gcongr with i hi
        · exact hN.le
        · exact hM W hWa
        · exact hB W hWb
        · exact hWs i W (hWi i hi)
    _ = ENNReal.ofReal θ := by
        rw [zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp
        ring

/-- **`TransmissionTraceModulusAbsorbed` from `AbsorbedPowerTight`.** -/
theorem transmissionTraceModulusAbsorbed_of (hAbs : AbsorbedPowerTight) :
    TransmissionTraceModulusAbsorbed :=
  fun b hb hb2 E hE1 hE2 κ hκ h0 _ _ hε f _ _ hη hθ =>
    traceModulus_of_powerTightAt hκ.2.1 (by linarith) hE1 hE2 (hAbs b hb hb2 E hE1 hE2 κ hκ h0)
      hε f hη hθ

/-- **`TransmissionTraceModulus` for every profile, from `hTG` and the absorbed tightness.** -/
theorem transmissionTraceModulus_of_tight (hTG : TransmissionGeneratorContract)
    (hAbs : AbsorbedPowerTight) : TransmissionTraceModulus :=
  transmissionTraceModulus_of hTG (transmissionTraceModulusAbsorbed_of hAbs)

end BlockBand.Transmission.LawDuality
