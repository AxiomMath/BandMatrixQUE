module

public import BlockBand.Transmission.LawDuality.PowerBridge
public import BlockBand.Transmission.LawDuality.Sigma

/-!
# The finite-`W` trace modulus for `κ ≡ 0` from the transmission generator theorem

Proof by polynomial approximation. On the full-measure set where
`∫ s^j dμ_W(t) = P_{j+1}(t)` for all `j, t` (`PowerBridge`), for a polynomial `q` with
`‖f - q‖_∞ ≤ η'` one has `|∫ f dμ_t - ∫ q dμ_t| ≤ η'·P_1(t)`; so the `f`-modulus is bounded by
the moduli of finitely many `P_k` plus `η'(P_1(t) + P_1(t'))`. The mass `sup_{[ε,T]} P_1` is
bounded in probability by tightness of `P_1(ε)` and a chaining of the `P_1` modulus.

* `abs_sub_le_nat_of_modulus`: deterministic chaining.
* `abs_integral_sub_poly_le`: `|∫ f dν - Σ_i c_i m_i(ν)| ≤ η'·ν[0,1]`.
* **`transmissionTraceModulus_zero`**: the `κ ≡ 0` case of `TransmissionTraceModulus`, from
  `hTG.tight` only.
* `TransmissionTraceModulusAbsorbed` (the statement restricted to `κ ≠ 0`) and
  **`transmissionTraceModulus_of`**: `hTG ∧ TransmissionTraceModulusAbsorbed →
  TransmissionTraceModulus`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped NNReal ENNReal

/-- **Chaining**: a `1`-modulus at scale `δ` on `[a, b]` gives `|g t - g a| ≤ n` whenever
`t - a ≤ nδ`. -/
theorem abs_sub_le_nat_of_modulus {g : ℝ → ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, |t - t'| ≤ δ → |g t - g t'| ≤ 1) :
    ∀ n : ℕ, ∀ t ∈ Icc a b, t - a ≤ n * δ → |g t - g a| ≤ n := by
  intro n
  induction n with
  | zero =>
    intro t ht h0
    have : t = a := by simp only [CharP.cast_eq_zero, zero_mul] at h0; linarith [ht.1]
    simp [this]
  | succ n ih =>
    intro t ht hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    by_cases hc : t - a ≤ δ
    · have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
      have := h t ht a ha (by rw [abs_of_nonneg (by linarith [ht.1])]; exact hc)
      push_cast; linarith
    · replace hc := not_le.1 hc
      have ht' : t - δ ∈ Icc a b := ⟨by linarith, by linarith [ht.2]⟩
      have h1 := h t ht (t - δ) ht' (by rw [show t - (t - δ) = δ by ring, abs_of_pos hδ])
      have h2 := ih (t - δ) ht' (by push_cast at hn; linarith)
      calc |g t - g a| ≤ |g t - g (t - δ)| + |g (t - δ) - g a| := abs_sub_le _ _ _
        _ ≤ 1 + n := add_le_add h1 h2
        _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Polynomial approximation inside a finite measure**: `|∫ f dν - ∫ q dν| ≤ η·ν[0,1]`, with
`∫ q dν` written through the moments. -/
theorem abs_integral_sub_poly_le (ν : FiniteMeasure unitInterval) {f : C(unitInterval, ℝ)}
    {p : Polynomial ℝ} {η : ℝ} (hp : ‖p.toContinuousMapOn (Icc (0 : ℝ) 1) - f‖ < η) :
    |∫ s, f s ∂(ν : Measure unitInterval) -
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * moment i ν| ≤
      η * (ν : Measure unitInterval).real univ := by
  rw [← integral_polynomial_eq]
  have hpi : Integrable (fun t : unitInterval => p.eval (t : ℝ)) (ν : Measure unitInterval) :=
    (BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn (Set.Icc 0 1))).integrable _
  have hfi : Integrable (fun t : unitInterval => f t) (ν : Measure unitInterval) :=
    (BoundedContinuousFunction.mkOfCompact f).integrable _
  rw [← integral_sub hfi hpi, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun t => ?_)
  have := ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn (Set.Icc 0 1) - f) t
  rw [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
    Polynomial.toContinuousMap_apply, norm_sub_rev] at this
  exact this.trans hp.le

/-- The power-sum bridge for the homogeneous path, in `powerTrace` form. -/
theorem ae_moment_eq_powerTrace {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (W : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (t : ℝ),
      moment j (transmissionProcess b E (fun _ => 0) W t ω) = Internal.Contracts.TransmissionStatements.powerTrace b E W (j + 1) t ω :=
  ae_integral_pow_transmissionProcess (fun _ => le_rfl) hb hE1 hE2

theorem real_univ_eq_moment_zero (ν : FiniteMeasure unitInterval) :
    (ν : Measure unitInterval).real univ = moment 0 ν := by
  simp [moment]

/-- **The `κ ≡ 0` case of `TransmissionTraceModulus`**, from the `tight` clause of
`TransmissionGeneratorContract`.
-/
theorem transmissionTraceModulus_zero (hTG : TransmissionGeneratorContract) {b : ℝ} (hb : 0 < b)
    (hb2 : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {ε T : ℝ} (hε : 0 < ε)
    (f : C(unitInterval, ℝ)) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |∫ x, f x ∂(transmissionProcess b E (fun _ => 0) W t ω : Measure unitInterval) -
          ∫ x, f x ∂(transmissionProcess b E (fun _ => 0) W t' ω : Measure unitInterval)|} ≤
        ENNReal.ofReal θ := by
  rcases le_or_gt T ε with hT | hT
  · refine ⟨1, one_pos, 0, fun W _ => le_trans (measure_mono (t := ∅) ?_) (by simp)⟩
    rintro ω ⟨t, ht, t', ht', -, hlt⟩
    have h1 : t = ε := le_antisymm (ht.2.trans hT) ht.1
    have h2 : t' = ε := le_antisymm (ht'.2.trans hT) ht'.1
    subst h1 h2
    simp at hlt
    linarith
  obtain ⟨hTi1, hMod1⟩ := hTG.tight b hb hb2 E hE1 hE2 1 le_rfl ε T hε hT
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
  have hmod := fun i : ℕ => (hTG.tight b hb hb2 E hE1 hE2 (i + 1) (by omega) ε T hε hT).2
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
  set μW := transmissionProcess b E (fun _ => 0) W
  let PT : ℕ → ℝ → GrowthPath W → ℝ := fun k t ω => Internal.Contracts.TransmissionStatements.powerTrace b E W k t ω
  let N : Set (GrowthPath W) :=
    {ω | ¬ ∀ (j : ℕ) (t : ℝ), moment j (μW t ω) = PT (j + 1) t ω}
  let A : Set (GrowthPath W) := {ω | M < |PT 1 ε ω|}
  let B : Set (GrowthPath W) := {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ1 ∧
    1 < |PT 1 t ω - PT 1 t' ω|}
  let Cs : ℕ → Set (GrowthPath W) := fun i => {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T,
    |t - t'| ≤ δs i ∧ η / (2 * C) < |PT (i + 1) t ω - PT (i + 1) t' ω|}
  have hN : growthPathLaw W b N = 0 :=
    ae_iff.1 (ae_moment_eq_powerTrace (by linarith) hE1 hE2 W)
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
    -- mass bound on `[ε, T]`
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

/-- **The `κ ≡ 0` instance of `TransmissionTraceModulus`**, in its quantifier order. -/
theorem transmissionTraceModulus_zero' (hTG : TransmissionGeneratorContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |∫ x, f x ∂(transmissionProcess b E (fun _ => 0) W t ω : Measure unitInterval) -
            ∫ x, f x ∂(transmissionProcess b E (fun _ => 0) W t' ω : Measure unitInterval)|} ≤
          ENNReal.ofReal θ :=
  fun _ hb hb2 _ hE1 hE2 _ _ hε f _ _ hη hθ =>
    transmissionTraceModulus_zero hTG hb hb2 hE1 hE2 hε f hη hθ

/-- **The absorbed part of `TransmissionTraceModulus`**: its statement restricted to absorbed
profiles `κ ≠ 0` (otherwise identical). -/
def TransmissionTraceModulusAbsorbed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    κ ≠ (fun _ => 0) →
    ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |∫ x, f x ∂(transmissionProcess b E κ W t ω : Measure unitInterval) -
            ∫ x, f x ∂(transmissionProcess b E κ W t' ω : Measure unitInterval)|} ≤
          ENNReal.ofReal θ

/-- **`TransmissionTraceModulus` from `hTG` and its absorbed part.** -/
theorem transmissionTraceModulus_of (hTG : TransmissionGeneratorContract)
    (hAbs : TransmissionTraceModulusAbsorbed) : TransmissionTraceModulus := by
  intro b hb hb2 E hE1 hE2 κ hκ
  by_cases h0 : κ = fun _ => 0
  · subst h0
    exact transmissionTraceModulus_zero' hTG b hb hb2 E hE1 hE2
  · exact hAbs b hb hb2 E hE1 hE2 κ hκ h0

end BlockBand.Transmission.LawDuality
