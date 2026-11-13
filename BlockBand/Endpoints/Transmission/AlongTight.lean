module

public import BlockBand.Endpoints.Transmission.AlongTightPower
public import BlockBand.Endpoints.Transmission.AlongDefs
public import BlockBand.Transmission.LawDuality.SubLimitExists

/-!
# Tightness and the modulus along moving energies

Part of the transmission law theorem: tightness from the polynomial tests and conductance
moments, along moving energies.

Fix `0 < b < 1/2`, `-2 < E < 2`, an admissible profile `κ` (including `κ ≡ 0`) and a moving
energy `e` with `IsMovingEnergy E Ce e`. The width-`W` process is
`transmissionProcess b (e W) κ W`.

* `traceModulus_of_powerTightAlong`: `traceModulus_of_powerTightAt` (polynomial approximation)
  along `e`, assuming only that `e W ∈ (-2, 2)` for large `W`.
* **`modulus_along hMT hGA hLp`**: the `modulus` clause of
  `TransmissionUniform.IsTransmissionLimitAlong b e κ P μ`, exactly as stated there.
* `subLimitExists_of_powerTightAlong`: `subLimitExists_of_powerTightAt` along `e`; the first
  widths, where `e W` may leave `(-2, 2)`, are dropped by shifting the subsequence.
* **`subLimitExists_along hMT hGA hLp`**: every `ns → ∞` has a strictly increasing refinement
  `ms` with an along sub-limit `IsTransmissionSubLimitAlong b e κ (ns ∘ ms) P μ`.

Inputs: `MatchedTracesContract`, `GaussianAbsorptionContract`, `GaussianLpGradient`
(`GaussianPoincare` is not needed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Transmission

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.LawFinite BlockBand.Transmission.LawDuality
open BlockBand.Transmission.LawDuality.SubLimit
open scoped NNReal ENNReal

/-- **The modulus clause along `e`, from `PowerTightAlong b e κ`** (`traceModulus_of_powerTightAt`
with the width-`W` energy `e W`; `e W ∈ (-2, 2)` is needed only for `W ≥ W₁`). -/
theorem traceModulus_of_powerTightAlong {b : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s)
    (hb : b < 1) {W₁ : ℕ} (hW₁ : ∀ W : ℕ, W₁ ≤ W → -2 < e W ∧ e W < 2)
    (hPT : PowerTightAlong b e κ) {ε T : ℝ} (hε : 0 < ε)
    (f : C(unitInterval, ℝ)) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |∫ x, f x ∂(transmissionProcess b (e W) κ W t ω : Measure unitInterval) -
          ∫ x, f x ∂(transmissionProcess b (e W) κ W t' ω : Measure unitInterval)|} ≤
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
  refine ⟨δ, hδ0, max (max (max Wa Wb) ((Finset.range (d + 1)).sup Ws)) W₁, fun W hW' => ?_⟩
  have hW : max (max Wa Wb) ((Finset.range (d + 1)).sup Ws) ≤ W := le_of_max_le_left hW'
  obtain ⟨hE1, hE2⟩ := hW₁ W (le_of_max_le_right hW')
  have hWa : Wa ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW)
  have hWb : Wb ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW)
  have hWi : ∀ i ∈ Finset.range (d + 1), Ws i ≤ W := fun i hi =>
    (Finset.le_sup (f := Ws) hi).trans ((le_max_right _ _).trans hW)
  set μW := transmissionProcess b (e W) κ W
  let PT : ℕ → ℝ → GrowthPath W → ℝ := fun k t ω => absorbedPowerTrace b (e W) κ W k t ω
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

/-- Along a moving energy around a bulk `E`, `e W ∈ (-2, 2)` for `W ≥ windowWidth`. -/
theorem along_bounds {E Ce : ℝ} {e : ℕ → ℝ} (hE1 : -2 < E) (hE2 : E < 2)
    (he : IsMovingEnergy E Ce e) :
    ∀ W : ℕ, EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce ≤ W → -2 < e W ∧ e W < 2 :=
  fun _ hW => Generator.bulk_bounds' (by have := (Generator.mem_bulk_min hE1 hE2).1; positivity)
    (Generator.along_mem_bulk hE1 hE2 he hW)

/-- **The `modulus` clause of `IsTransmissionLimitAlong b e κ P μ`** (exactly as stated), for every
admissible profile `κ` and every moving energy `e` around a bulk `E`, from `hMT, hGA, hLp`. -/
theorem modulus_along (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E)
    (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) :
    ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |∫ x, f x ∂(transmissionProcess b (e W) κ W t ω : Measure unitInterval) -
            ∫ x, f x ∂(transmissionProcess b (e W) κ W t' ω : Measure unitInterval)|} ≤
          ENNReal.ofReal θ :=
  fun _ _ hε f _ _ hη hθ => traceModulus_of_powerTightAlong hκ.2.1 (by linarith)
    (along_bounds hE1 hE2 he) (powerTightAlong_holds hMT hGA hLp hb0 hb hE1 hE2 he hκ) hε f hη hθ

/-- **Along sub-limits exist, from `PowerTightAlong b e κ`** (`subLimitExists_of_powerTightAt`
along `e`; `e W ∈ (-2, 2)` is needed only for `W ≥ W₁`). -/
theorem subLimitExists_of_powerTightAlong {b : ℝ} {e : ℕ → ℝ} {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s)
    (hb : b < 1) {W₁ : ℕ} (hW₁ : ∀ W : ℕ, W₁ ≤ W → -2 < e W ∧ e W < 2)
    (hPT : PowerTightAlong b e κ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionSubLimitAlong b e κ (ns ∘ ms) P μ := by
  obtain ⟨N, hN⟩ := eventually_le_of_tendsto hns W₁
  set ns' : ℕ → ℕ := fun n => ns (n + N) with hns'_def
  have hns' : Tendsto ns' atTop atTop := hns.comp (tendsto_add_atTop_nat N)
  have hE' : ∀ n, -2 < e (ns' n) ∧ e (ns' n) < 2 := fun n => hW₁ _ (hN _ (by omega))
  have hT : OneTimeTight (fun n => growthPathLaw (ns' n) b)
      (fun n => transmissionProcess b (e (ns' n)) κ (ns' n)) := by
    intro t ht θ hθ
    obtain ⟨M, W₀, hM⟩ := (hPT 1 le_rfl t (t + 1) ht (by linarith)).1 θ hθ
    obtain ⟨N', hN'⟩ := eventually_le_of_tendsto hns' W₀
    refine ⟨M, N', fun n hn => ?_⟩
    have hnull := ae_iff.1 (ae_moment_eq_absorbedPowerTrace (W := ns' n) hκ hb (hE' n).1 (hE' n).2)
    refine (measure_mono (t := {ω | M < |absorbedPowerTrace b (e (ns' n)) κ (ns' n) 1 t ω|} ∪
      {ω | ¬ ∀ (j : ℕ) (t : ℝ), moment j (transmissionProcess b (e (ns' n)) κ (ns' n) t ω) =
        absorbedPowerTrace b (e (ns' n)) κ (ns' n) (j + 1) t ω}) fun ω hω => ?_).trans
      ((measure_union_le _ _).trans (by rw [hnull, add_zero]; exact hM _ (hN' n hn)))
    by_cases hg : ∀ (j : ℕ) (t : ℝ), moment j (transmissionProcess b (e (ns' n)) κ (ns' n) t ω) =
        absorbedPowerTrace b (e (ns' n)) κ (ns' n) (j + 1) t ω
    · left
      have h : M < moment 0 (transmissionProcess b (e (ns' n)) κ (ns' n) t ω) := hω
      rw [hg 0 t] at h
      exact lt_of_lt_of_le h (le_abs_self _)
    · exact Or.inr hg
  have hM : MomentModulus (fun n => growthPathLaw (ns' n) b)
      (fun n => transmissionProcess b (e (ns' n)) κ (ns' n)) := by
    intro ε T hε j η θ hη hθ
    obtain ⟨δ, hδ, W₀, hW⟩ := traceModulus_of_powerTightAlong hκ hb hW₁ hPT (T := T) hε
      ⟨fun s : unitInterval => (s : ℝ) ^ j, continuous_subtype_val.pow j⟩ hη hθ
    obtain ⟨N', hN'⟩ := eventually_le_of_tendsto hns' W₀
    exact ⟨δ, hδ, N', fun n hn => hW (ns' n) (hN' n hn)⟩
  obtain ⟨ms, hms, P, μ, hP, hmeas, hcont, hfdd⟩ := exists_subLimit
    (Ps := fun n => growthPathLaw (ns' n) b)
    (X := fun n => transmissionProcess b (e (ns' n)) κ (ns' n))
    (fun n t _ => aemeasurable_transmissionProcess hκ hb (hE' n).1 (hE' n).2 t) hT hM
  exact ⟨fun n => ms n + N, fun _ _ h => Nat.add_lt_add_right (hms h) N,
    ℕ → FiniteMeasure unitInterval, inferInstance, P, μ, ⟨hP, hmeas, hcont, hfdd⟩⟩

/-- **Every `ns → ∞` has a strictly increasing refinement `ms` along which the processes at
energies `e W` have a sub-limit** (`IsTransmissionSubLimitAlong b e κ (ns ∘ ms) P μ`), for every
admissible profile `κ` and every moving energy `e` around a bulk `E`, from `hMT, hGA, hLp`. -/
theorem subLimitExists_along (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E)
    (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e) {κ : ℝ → ℝ}
    (hκ : IsAbsorptionProfile κ) :
    ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionSubLimitAlong b e κ (ns ∘ ms) P μ :=
  fun _ hns => subLimitExists_of_powerTightAlong hκ.2.1 (by linarith) (along_bounds hE1 hE2 he)
    (powerTightAlong_holds hMT hGA hLp hb0 hb hE1 hE2 he hκ) hns

end BlockBand.Endpoints.Transmission
