module

public import BlockBand.Endpoints.Response.RemoteHigherNear
public import BlockBand.Endpoints.Response.RemoteHigherWindowContracts

/-!
# Near-clock higher decay at general lengths (fixed energy)

This file proves `RhwNearHigherLimsupDecayLength` (`rhw_nearHigherLimsupDecay_length`):
`RhNearHigherLimsupDecay` with the length `⌊W(t₁+R+s)⌋` replaced by any `m_W` with
`m_W/W → t₁ + R + s`. The ingredients are a Slutsky lemma, convergence of clock moments at moving
lengths, the upper passage of `H_p^r` along an arbitrary length sequence and the higher trace
bound at every length `≤ TW`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Polynomial Filter Topology Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## Slutsky
-/

/-- Slutsky: if `E Ψ(V_n) → L`, `(V_n)` is tight and `V'_n - V_n → 0` in probability, then
`E Ψ(V'_n) → L` (bounded continuous `Ψ`). -/
theorem rhw_tendsto_integral_of_close {d : ℕ} {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (μ : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (μ n)] (V V' : ∀ n, Ωn n → (Fin d → ℂ))
    (hV : ∀ n, Measurable (V n)) (hV' : ∀ n, Measurable (V' n))
    (Ψ : BoundedContinuousFunction (Fin d → ℂ) ℝ) {L : ℝ}
    (hlim : Tendsto (fun n => ∫ ω, Ψ (V n ω) ∂μ n) atTop (𝓝 L))
    (htight : ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, ∀ᶠ n in atTop, μ n {ω | M < ‖V n ω‖} ≤ ENNReal.ofReal θ)
    (hclose : ∀ ρ θ : ℝ, 0 < ρ → 0 < θ →
      ∀ᶠ n in atTop, μ n {ω | ρ < ‖V' n ω - V n ω‖} ≤ ENNReal.ofReal θ) :
    Tendsto (fun n => ∫ ω, Ψ (V' n ω) ∂μ n) atTop (𝓝 L) := by
  set B := ‖Ψ‖
  have hB : 0 ≤ B := norm_nonneg _
  have hΨb : ∀ x, |Ψ x| ≤ B := fun x => by
    rw [← Real.norm_eq_abs]; exact Ψ.norm_coe_le_norm x
  have hint : ∀ n (f : Ωn n → Fin d → ℂ), Measurable f → Integrable (fun ω => Ψ (f ω)) (μ n) :=
    fun n f hf => Integrable.of_bound (Ψ.continuous.measurable.comp hf).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hΨb _)
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      |∫ ω, Ψ (V' n ω) ∂μ n - ∫ ω, Ψ (V n ω) ∂μ n| ≤ ε := by
    intro ε hε
    set θ := ε / (8 * (B + 1))
    have hθ : 0 < θ := by positivity
    obtain ⟨M, hM⟩ := htight θ hθ
    have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) (|M| + 1)) := isCompact_closedBall _ _
    obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous Ψ.continuous.continuousOn) (ε / 2) (by positivity)
    set ρ := min (δ / 2) 1
    have hρ : 0 < ρ := lt_min (by positivity) one_pos
    filter_upwards [hM, hclose ρ θ hρ hθ] with n h1 h2
    set A₁ := {ω | M < ‖V n ω‖}
    set A₂ := {ω | ρ < ‖V' n ω - V n ω‖}
    have hA₁ : MeasurableSet A₁ := measurableSet_lt measurable_const (hV n).norm
    have hA₂ : MeasurableSet A₂ := measurableSet_lt measurable_const ((hV' n).sub (hV n)).norm
    have hpt : ∀ ω, |Ψ (V' n ω) - Ψ (V n ω)| ≤ ε / 2 + 2 * B * (A₁ ∪ A₂).indicator 1 ω := by
      intro ω
      by_cases hω : ω ∈ A₁ ∪ A₂
      · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        have := abs_sub (Ψ (V' n ω)) (Ψ (V n ω))
        linarith [hΨb (V' n ω), hΨb (V n ω)]
      · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
        simp only [Set.mem_union, not_or, A₁, A₂, Set.mem_ofPred_eq, not_lt] at hω
        have hx : V n ω ∈ Metric.closedBall (0 : Fin d → ℂ) (|M| + 1) := by
          rw [Metric.mem_closedBall, dist_zero_right]; linarith [le_abs_self M]
        have hy : V' n ω ∈ Metric.closedBall (0 : Fin d → ℂ) (|M| + 1) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have := norm_sub_norm_le (V' n ω) (V n ω)
          linarith [le_abs_self M, min_le_right (δ / 2) 1]
        have hd : dist (V' n ω) (V n ω) < δ := by
          rw [dist_eq_norm]; linarith [min_le_left (δ / 2) 1]
        have := huc _ hy _ hx hd
        rw [Real.dist_eq] at this
        exact this.le
    have hInd2 : Integrable (fun ω => 2 * B * (A₁ ∪ A₂).indicator 1 ω) (μ n) := by
      have := ((integrable_const (1 : ℝ)).indicator (hA₁.union hA₂) (μ := μ n)).const_mul (2 * B)
      exact this
    have hmeasI : Integrable (fun ω => ε / 2 + 2 * B * (A₁ ∪ A₂).indicator 1 ω) (μ n) :=
      (integrable_const _).add hInd2
    have hgint : ∫ ω, (ε / 2 + 2 * B * (A₁ ∪ A₂).indicator 1 ω) ∂μ n =
        ε / 2 + 2 * B * (μ n (A₁ ∪ A₂)).toReal := by
      rw [integral_add (integrable_const _) hInd2, integral_const, integral_const_mul,
        integral_indicator_one (hA₁.union hA₂)]
      simp [measureReal_def]
    rw [← integral_sub (hint n _ (hV' n)) (hint n _ (hV n))]
    refine (abs_integral_le_integral_abs).trans ?_
    refine (integral_mono ((hint n _ (hV' n)).sub (hint n _ (hV n))).abs hmeasI hpt).trans ?_
    rw [hgint]
    have hU : (μ n (A₁ ∪ A₂)).toReal ≤ 2 * θ := by
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      refine (measure_union_le _ _).trans ?_
      calc μ n A₁ + μ n A₂ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ := add_le_add h1 h2
        _ = ENNReal.ofReal (2 * θ) := by rw [← ENNReal.ofReal_add hθ.le hθ.le]; ring_nf
    have : 2 * B * (2 * θ) ≤ ε / 2 := by
      simp only [θ]
      rw [show 2 * B * (2 * (ε / (8 * (B + 1)))) = ε / 2 * (B / (B + 1)) by field_simp; ring]
      have : B / (B + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    nlinarith
  have hdiff : Tendsto (fun n => ∫ ω, Ψ (V' n ω) ∂μ n - ∫ ω, Ψ (V n ω) ∂μ n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [key (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq, sub_zero]
    linarith
  have := hlim.add hdiff
  simp only [add_sub_cancel, add_zero] at this
  exact this

/-!
## Convergence of the clock moments at moving lengths
-/

/-- The clock moments at moving lengths converge to the critical limit at `u`. -/
theorem rhw_conv_moving_length (hGen : FullSourceGeneratorContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {t₁ R : ℝ} {q : ℝ → ℝ}
    (hq : IsUnitSource t₁ R q) (hpos : 0 < t₁ + R) {u : ℝ} (hu : t₁ + R < u) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q (t₁ + R) P Z φ) {ℓ : ℕ → ℕ}
    (hℓ : Tendsto (fun W : ℕ => (ℓ W : ℝ) / W) atTop (𝓝 u)) (md : ℕ)
    (Ψ : BoundedContinuousFunction (Fin (md + 1) → ℂ) ℝ) :
    Tendsto (fun n => ∫ ω, Ψ (fun l : Fin (md + 1) =>
        ((nearClock b E (φ n) (ℓ (φ n)) q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw (φ n) b)
      atTop (𝓝 (∫ ω, Ψ (nsClockVec Z md u ω) ∂P)) := by
  have : ∀ n, IsProbabilityMeasure (growthPathLaw (φ n) b) := fun n =>
    isProbabilityMeasure_growthPathLaw _ b
  have hsrc : ∀ a : Fin 1, ∃ s : ℝ, IsSourceTest s (t₁ + R) ((fun _ => q) a) :=
    fun _ => ⟨t₁, hq.2.2.2.1⟩
  have hk : ∀ᶠ W in atTop, ∀ a : Fin 0, ((noTags W a + 1 : ℕ) : ℝ) ≤ W * (t₁ + R) :=
    Eventually.of_forall fun _ a => a.elim0
  have hword : ∀ l : Fin (md + 1), IsOrdinaryWord (clockWord ((l : ℕ) + 1)) := fun l =>
    ns_isOrdinaryWord_clockWord (by omega)
  have hwv : ∀ (W j : ℕ) (ω : GrowthPath W) (l : Fin (md + 1)),
      wordValue b E (noTags W) (fun _ => q) W j ω (clockWord ((l : ℕ) + 1)) =
        ((nearClock b E W j q ω) ^ ((l : ℕ) + 1)).trace := fun W j ω l =>
    ns_wordValue_clockWord_eq b E q W j ω _ (by omega)
  set V : ∀ n, GrowthPath (φ n) → (Fin (md + 1) → ℂ) := fun n ω l =>
    ((nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace
  set V' : ∀ n, GrowthPath (φ n) → (Fin (md + 1) → ℂ) := fun n ω l =>
    ((nearClock b E (φ n) (ℓ (φ n)) q ω) ^ ((l : ℕ) + 1)).trace
  have hlim : Tendsto (fun n => ∫ ω, Ψ (V n ω) ∂growthPathLaw (φ n) b) atTop
      (𝓝 (∫ ω, Ψ (nsClockVec Z md u ω) ∂P)) := by
    have h := hfdd (md + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨hword l, hu.le⟩) Ψ
    refine h.congr fun n => ?_
    congr 1
    funext ω
    congr 1
    funext l
    exact hwv _ _ ω l
  refine rhw_tendsto_integral_of_close (fun n => growthPathLaw (φ n) b) V V'
    (fun n => ns_measurable_clockMoments b E _ _ q md)
    (fun n => ns_measurable_clockMoments b E _ _ q md) Ψ hlim ?_ ?_
  · -- tightness at `u`
    intro θ hθ
    have hθ' : 0 < θ / (md + 1) := by positivity
    have hT : ∀ l : Fin (md + 1), ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | M < ‖wordValue b E (noTags W) (fun _ => q) W ⌊(W : ℝ) * u⌋₊ ω
          (clockWord ((l : ℕ) + 1))‖} ≤ ENNReal.ofReal (θ / (md + 1)) := fun l =>
      ((hGen.tight b hb hb' E hE1 hE2 (t₁ + R) hpos 0 1 (fun _ => q) hsrc noTags hk _ (hword l)
        u (u + 1) hu.le (by linarith)).1 _ hθ')
    choose M W₀ hMW using hT
    refine ⟨∑ l, |M l|, ?_⟩
    have hev : ∀ᶠ n in atTop, ∀ l : Fin (md + 1), W₀ l ≤ φ n :=
      eventually_all.mpr fun l => hφ.tendsto_atTop.eventually_ge_atTop _
    filter_upwards [hev] with n hn
    have hsub : {ω | ∑ l, |M l| < ‖V n ω‖} ⊆ ⋃ l, {ω | M l < ‖wordValue b E (noTags (φ n))
        (fun _ => q) (φ n) ⌊(φ n : ℝ) * u⌋₊ ω (clockWord ((l : ℕ) + 1))‖} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hc
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hc
      have : ‖V n ω‖ ≤ ∑ l, |M l| := by
        refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)).mpr
          fun l => ?_
        have h1 := hc l
        rw [hwv] at h1
        refine h1.trans ((le_abs_self _).trans ?_)
        exact Finset.single_le_sum (f := fun l => |M l|) (fun l _ => abs_nonneg _)
          (Finset.mem_univ l)
      linarith
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    calc ∑ l, growthPathLaw (φ n) b {ω | M l < ‖wordValue b E (noTags (φ n)) (fun _ => q) (φ n)
          ⌊(φ n : ℝ) * u⌋₊ ω (clockWord ((l : ℕ) + 1))‖}
        ≤ ∑ _l : Fin (md + 1), ENNReal.ofReal (θ / (md + 1)) :=
          Finset.sum_le_sum fun l _ => hMW l _ (hn l)
      _ = ENNReal.ofReal θ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; field_simp
  · -- closeness: the sup-modulus
    intro ρ θ hρ hθ
    have hθ' : 0 < θ / (md + 1) := by positivity
    have hT : ∀ l : Fin (md + 1), ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc (t₁ + R) (u + 1), ∃ t' ∈ Set.Icc (t₁ + R) (u + 1),
          |t - t'| ≤ δ ∧ ρ < ‖wordValue b E (noTags W) (fun _ => q) W ⌊(W : ℝ) * t⌋₊ ω
            (clockWord ((l : ℕ) + 1)) - wordValue b E (noTags W) (fun _ => q) W
              ⌊(W : ℝ) * t'⌋₊ ω (clockWord ((l : ℕ) + 1))‖} ≤ ENNReal.ofReal (θ / (md + 1)) :=
      fun l => (hGen.tight b hb hb' E hE1 hE2 (t₁ + R) hpos 0 1 (fun _ => q) hsrc noTags hk _
        (hword l) (t₁ + R) (u + 1) le_rfl (by linarith)).2 ρ _ hρ hθ'
    choose δ hδ W₀ hW₀ using hT
    have hev1 : ∀ᶠ n in atTop, ∀ l : Fin (md + 1), W₀ l ≤ φ n :=
      eventually_all.mpr fun l => hφ.tendsto_atTop.eventually_ge_atTop _
    have hℓφ := hℓ.comp hφ.tendsto_atTop
    have hev2 : ∀ᶠ n in atTop, ∀ l : Fin (md + 1), |(ℓ (φ n) : ℝ) / (φ n) - u| ≤ δ l :=
      eventually_all.mpr fun l => (Metric.tendsto_nhds.mp hℓφ (δ l) (hδ l)).mono fun n hn => by
        rw [Real.dist_eq] at hn; exact hn.le
    have hev3 : ∀ᶠ n in atTop, (ℓ (φ n) : ℝ) / (φ n) ∈ Set.Icc (t₁ + R) (u + 1) :=
      hℓφ.eventually (Icc_mem_nhds hu (by linarith))
    have hev4 : ∀ᶠ n in atTop, 1 ≤ φ n := hφ.tendsto_atTop.eventually_ge_atTop 1
    filter_upwards [hev1, hev2, hev3, hev4] with n h1 h2 h3 h4
    have hW0 : ((φ n : ℕ) : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast h4
      linarith
    have hfl : ⌊((φ n : ℕ) : ℝ) * ((ℓ (φ n) : ℝ) / (φ n))⌋₊ = ℓ (φ n) := by
      rw [mul_div_cancel₀ _ hW0, Nat.floor_natCast]
    have hsub : {ω | ρ < ‖V' n ω - V n ω‖} ⊆ ⋃ l, {ω | ∃ t ∈ Set.Icc (t₁ + R) (u + 1),
        ∃ t' ∈ Set.Icc (t₁ + R) (u + 1), |t - t'| ≤ δ l ∧ ρ < ‖wordValue b E (noTags (φ n))
          (fun _ => q) (φ n) ⌊((φ n : ℕ) : ℝ) * t⌋₊ ω (clockWord ((l : ℕ) + 1)) -
            wordValue b E (noTags (φ n)) (fun _ => q) (φ n) ⌊((φ n : ℕ) : ℝ) * t'⌋₊ ω
              (clockWord ((l : ℕ) + 1))‖} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_contra hc
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hc
      have : ‖V' n ω - V n ω‖ ≤ ρ := by
        refine (pi_norm_le_iff_of_nonneg hρ.le).mpr fun l => ?_
        have h := hc l _ h3 u ⟨hu.le, by linarith⟩ (h2 l)
        rw [hfl, hwv, hwv] at h
        simpa [V, V'] using h
      linarith
    refine (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans ?_)
    calc _ ≤ ∑ _l : Fin (md + 1), ENNReal.ofReal (θ / (md + 1)) :=
          Finset.sum_le_sum fun l _ => hW₀ l _ (h1 l)
      _ = ENNReal.ofReal θ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; field_simp

/-!
## The upper passage at an arbitrary length sequence
-/

/-- Upper passage of `H_p^r` along an arbitrary length sequence `ℓ`: `rhn_limsup_fracTrace_rpow_le`
with `⌊Wu⌋` replaced by `ℓ W` (the convergence of the tests along `ℓ` is the hypothesis
`hconv`). -/
theorem rhw_limsup_fracTrace_rpow_le_len {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {u : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (ℓ : ℕ → ℕ)
    (hconv : ∀ (md : ℕ) (Ψ : BoundedContinuousFunction (Fin (md + 1) → ℂ) ℝ),
      Tendsto (fun n => ∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ n) (ℓ (φ n)) q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw (φ n) b)
        atTop (𝓝 (∫ ω, Ψ (nsClockVec Z md u ω) ∂P)))
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p p₀ r : ℝ} (hp₀ : 0 < p₀)
    (hp₀p : p₀ < p) (hp1 : p < 1) (hr : 1 ≤ r) {C₀ C₂ : ℝ}
    (hH0 : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p₀ (nearClock b E W (ℓ W) q ω)) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₀)
    (hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nearClock b E W (ℓ W) q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₂) :
    limsup (fun n => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ n) (ℓ (φ n)) q ω)) ^ r ∂growthPathLaw (φ n) b)
        atTop ≤ 3 ^ r * (2 ^ (r - 1) * ∫⁻ ω, limitFracTrace p (μ ω) ^ r ∂P) := by
  have hp : 0 < p := hp₀.trans hp₀p
  have hr0 : 0 < r := by linarith
  have h3top : (3 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le (by simp)
  have h2top : (2 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  set L := limsup (fun n => ∫⁻ ω, ENNReal.ofReal
    (fracTrace p (nearClock b E (φ n) (ℓ (φ n)) q ω)) ^ r ∂growthPathLaw (φ n) b) atTop
  set Hl := ∫⁻ ω, limitFracTrace p (μ ω) ^ r ∂P
  -- the bound at cutoff `a = ε_m` and polynomial level `K`
  have key : ∀ m K : ℕ, L ≤ 3 ^ r * (ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) ^ r *
      ENNReal.ofReal C₀ +
      2 ^ (r - 1) * (Hl + ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)) ^ r) +
      ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)) ^ r * ENNReal.ofReal C₂) := by
    intro m K
    set a := nsEps m with ha
    have ha0 : 0 < a := ns_eps_pos m
    set c := nsCutKernel a (p - 1) with hcdef
    have hc : Continuous c := ns_continuous_cutKernel ha0
    have hc0 : ∀ x, 0 ≤ c x := ns_cutKernel_nonneg ha0
    set B := a ^ (p - 1) with hB
    have hcB : ∀ x, c x ≤ B := ns_cutKernel_le ha0 (by linarith)
    have hB0 : 0 ≤ B := Real.rpow_nonneg ha0.le _
    set Kr : ℝ := (K : ℝ) + 2 with hKr
    have hKr2 : 2 ≤ Kr := by rw [hKr]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    set δ : ℝ := 1 / Kr ^ 2 with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [hδ, div_le_one (by positivity)]; nlinarith
    obtain ⟨π, hπ⟩ := exists_polynomial_near_of_continuousOn 0 Kr c hc.continuousOn δ
      (by positivity)
    have happ : ∀ x ∈ Icc 0 Kr, |π.eval x - c x| ≤ δ := fun x hx => (hπ x hx).le
    set md := π.natDegree
    set M := B * Kr + 2 * Kr with hM
    have hM0 : 0 ≤ M := by positivity
    set Ψ := rhn_powTestBCF π md 1 δ Kr M hM0 r hr0.le
    have hΨapp : ∀ z, Ψ z = nsTestFun π md 1 δ Kr M z ^ r := fun z => rfl
    have hΨ0 : ∀ z, 0 ≤ Ψ z := fun z => rhn_powTestBCF_nonneg _ _ _ _ _ _ _ _ _ z
    have hΨle : ∀ z, Ψ z ≤ M ^ r := fun z => rhn_powTestBCF_le _ _ _ _ _ _ _ _ _ z
    -- finite width: pointwise bound and integration
    have hfin : ∀ W : ℕ, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W (ℓ W) q ω)) ^ r ∂growthPathLaw W b ≤
        3 ^ r * (ENNReal.ofReal (2 * a ^ (p - p₀)) ^ r * ∫⁻ ω, ENNReal.ofReal
          (fracTrace p₀ (nearClock b E W (ℓ W) q ω)) ^ r ∂growthPathLaw W b +
        ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E W (ℓ W) q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw W b) +
        ENNReal.ofReal (B / (Kr - 1)) ^ r * ∫⁻ ω, ENNReal.ofReal
          ((nearClock b E W (ℓ W) q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b) := by
      intro W
      have := isProbabilityMeasure_growthPathLaw W b
      set A := fun ω => nearClock b E W (ℓ W) q ω
      have hmΨ : Measurable fun ω => Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace) :=
        Ψ.continuous.measurable.comp (ns_measurable_clockMoments b E W _ q md)
      have hint : Integrable (fun ω => Ψ (fun l : Fin (md + 1) =>
          ((A ω) ^ ((l : ℕ) + 1)).trace)) (growthPathLaw W b) :=
        Integrable.of_bound hmΨ.aestronglyMeasurable (M ^ r) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 _)]
          exact hΨle _)
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hΨ0 _)]
      set F₁ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (2 * a ^ (p - p₀)) ^ r * ENNReal.ofReal (fracTrace p₀ (A ω)) ^ r
      set F₂ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace))
      set F₃ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (B / (Kr - 1)) ^ r * ENNReal.ofReal ((A ω).trace.re ^ 2) ^ r
      have hF₂ : Measurable F₂ := ENNReal.measurable_ofReal.comp hmΨ
      have hF₃ : Measurable F₃ := ((ENNReal.measurable_ofReal.comp
          ((ns_measurable_trace_nearClock b E W _ q).pow_const 2)).pow_const r).const_mul _
      calc ∫⁻ ω, ENNReal.ofReal (fracTrace p (A ω)) ^ r ∂growthPathLaw W b
          ≤ ∫⁻ ω, 3 ^ r * (F₁ ω + F₂ ω + F₃ ω) ∂growthPathLaw W b := by
            refine lintegral_mono fun ω => ?_
            have hApsd := ns_nearClock_posSemidef b E W (ℓ W) q hq ω
            have h1 := ns_fracTrace_le_small_add hApsd ha0 (p := p)
            have h2 := smallChannelPower_le_rpow_mul_fracTrace ha0.le hp hp₀p.le (A ω)
            have h3 := ns_clockSum_le_testFun_upper π le_rfl hc0 hcB hδ0 hδ1 hKr2 le_rfl happ
              hApsd
            have hf0 := fracTrace_nonneg p₀ (A ω)
            have ht0 := ns_testFun_nonneg π md 1 δ Kr hM0 (fun l => (A ω ^ ((l : ℕ) + 1)).trace)
            have hK1 : 0 < Kr - 1 := by linarith
            have hreal : fracTrace p (A ω) ≤ 2 * a ^ (p - p₀) * fracTrace p₀ (A ω) +
                nsTestFun π md 1 δ Kr M (fun l => (A ω ^ ((l : ℕ) + 1)).trace) +
                B / (Kr - 1) * (A ω).trace.re ^ 2 := by
              have : a ^ (p - p₀) * fracTrace p₀ (A ω) ≤
                  2 * a ^ (p - p₀) * fracTrace p₀ (A ω) := by
                have : 0 ≤ a ^ (p - p₀) * fracTrace p₀ (A ω) :=
                  mul_nonneg (Real.rpow_nonneg ha0.le _) hf0
                linarith
              have h4 : B * (A ω).trace.re ^ 2 / (Kr - 1) =
                  B / (Kr - 1) * (A ω).trace.re ^ 2 := by ring
              linarith
            have hsplit : ENNReal.ofReal (fracTrace p (A ω)) ≤
                ENNReal.ofReal (2 * a ^ (p - p₀)) * ENNReal.ofReal (fracTrace p₀ (A ω)) +
                ENNReal.ofReal (nsTestFun π md 1 δ Kr M (fun l => (A ω ^ ((l : ℕ) + 1)).trace)) +
                ENNReal.ofReal (B / (Kr - 1)) * ENNReal.ofReal ((A ω).trace.re ^ 2) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_add (by positivity) ht0,
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              exact ENNReal.ofReal_le_ofReal hreal
            refine (ENNReal.rpow_le_rpow hsplit hr0.le).trans ?_
            refine (rhn_rpow_add3_le _ _ _ hr0.le).trans (le_of_eq ?_)
            simp only [F₁, F₂, F₃]
            rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
              ENNReal.ofReal_rpow_of_nonneg ht0 hr0.le, hΨapp]
        _ = 3 ^ r * (∫⁻ ω, F₁ ω ∂growthPathLaw W b + ∫⁻ ω, F₂ ω ∂growthPathLaw W b +
              ∫⁻ ω, F₃ ω ∂growthPathLaw W b) := by
            rw [lintegral_const_mul' _ _ h3top, lintegral_add_right _ hF₃,
              lintegral_add_right _ hF₂]
        _ = _ := by
            simp only [F₁, F₃]
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le
                ENNReal.ofReal_ne_top),
              lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le
                ENNReal.ofReal_ne_top)]
    -- along the subsequence
    have hlimΨ := hconv md Ψ
    set X := ENNReal.ofReal (2 * a ^ (p - p₀)) ^ r * ENNReal.ofReal C₀
    set Y := ENNReal.ofReal (B / (Kr - 1)) ^ r * ENNReal.ofReal C₂
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ k) (ℓ (φ k)) q ω)) ^ r
          ∂growthPathLaw (φ k) b ≤
        3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) (ℓ (φ k)) q ω) ^ ((l : ℕ) + 1)).trace)
            ∂growthPathLaw (φ k) b) + Y) := by
      filter_upwards [hφ.tendsto_atTop.eventually hH0, hφ.tendsto_atTop.eventually hUI]
        with k h0 h2
      refine (hfin (φ k)).trans ?_
      exact mul_le_mul_right (add_le_add (add_le_add (mul_le_mul_right h0 _) le_rfl)
        (mul_le_mul_right h2 _)) _
    have hlim : Tendsto (fun k => 3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
        ((nearClock b E (φ k) (ℓ (φ k)) q ω) ^ ((l : ℕ) + 1)).trace)
          ∂growthPathLaw (φ k) b) + Y)) atTop
        (𝓝 (3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y))) :=
      ENNReal.Tendsto.const_mul
        ((tendsto_const_nhds.add (ENNReal.tendsto_ofReal hlimΨ)).add tendsto_const_nhds)
        (Or.inr h3top)
    have hL : L ≤ 3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y) :=
      (limsup_le_limsup hev).trans_eq hlim.limsup_eq
    -- the limit side
    have hmV : Measurable fun ω => Ψ (nsClockVec Z md u ω) :=
      Ψ.continuous.measurable.comp (ns_measurable_clockVec hmeas md)
    have hintZ : Integrable (fun ω => Ψ (nsClockVec Z md u ω)) P :=
      Integrable.of_bound hmV.aestronglyMeasurable (M ^ r) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 _)]
        exact hΨle _)
    have hZ : ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) ≤
        2 ^ (r - 1) * (Hl + ENNReal.ofReal (2 * δ * Kr) ^ r) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintZ (Eventually.of_forall fun ω => hΨ0 _)]
      calc ∫⁻ ω, ENNReal.ofReal (Ψ (nsClockVec Z md u ω)) ∂P
          ≤ ∫⁻ ω, 2 ^ (r - 1) * (limitFracTrace p (μ ω) ^ r +
              ENNReal.ofReal (2 * δ * Kr) ^ r) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hμ] with ω hω
            rw [hΨapp]
            have h1 := ns_testFun_upper_le hω hc hc0 π (m := md) le_rfl hδ0 (by linarith) hM0
              happ
            have hI0 : 0 ≤ ∫ x, c x ∂μ ω := integral_nonneg hc0
            have ht0 := ns_testFun_nonneg π md 1 δ Kr hM0 (nsClockVec Z md u ω)
            calc ENNReal.ofReal (nsTestFun π md 1 δ Kr M (nsClockVec Z md u ω) ^ r)
                = ENNReal.ofReal (nsTestFun π md 1 δ Kr M (nsClockVec Z md u ω)) ^ r :=
                  (ENNReal.ofReal_rpow_of_nonneg ht0 hr0.le).symm
              _ ≤ ENNReal.ofReal (∫ x, c x ∂μ ω + 2 * δ * Kr) ^ r :=
                  ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) hr0.le
              _ = (ENNReal.ofReal (∫ x, c x ∂μ ω) + ENNReal.ofReal (2 * δ * Kr)) ^ r := by
                  rw [ENNReal.ofReal_add hI0 (by positivity)]
              _ ≤ (limitFracTrace p (μ ω) + ENNReal.ofReal (2 * δ * Kr)) ^ r := by
                  gcongr
                  exact ns_ofReal_integral_cutKernel_le hω ha0 hp1
              _ ≤ _ := ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
        _ = 2 ^ (r - 1) * (Hl + ENNReal.ofReal (2 * δ * Kr) ^ r) := by
            rw [lintegral_const_mul' _ _ h2top, lintegral_add_right _ measurable_const,
              lintegral_const, measure_univ, mul_one]
    calc L ≤ 3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y) := hL
      _ ≤ 3 ^ r * (X + 2 ^ (r - 1) * (Hl + ENNReal.ofReal (2 * δ * Kr) ^ r) + Y) := by gcongr
  -- `K → ∞`, then `m → ∞`
  have hstep1 : ∀ m : ℕ, L ≤ 3 ^ r * (ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) ^ r *
      ENNReal.ofReal C₀ + 2 ^ (r - 1) * Hl) := by
    intro m
    have hδK : Tendsto (fun K : ℕ =>
        ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)) ^ r) atTop (𝓝 0) := by
      have h0 : Tendsto (fun K : ℕ => ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) *
          ((K : ℝ) + 2))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine ENNReal.tendsto_ofReal ?_
        have h1 : Tendsto (fun K : ℕ => (K : ℝ) + 2) atTop atTop :=
          tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
        have h : Tendsto (fun K : ℕ => (2 : ℝ) * ((K : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
          simpa using h1.inv_tendsto_atTop.const_mul (2 : ℝ)
        refine h.congr' (Eventually.of_forall fun K => ?_)
        have : (0 : ℝ) < (K : ℝ) + 2 := by positivity
        field_simp
      simpa [ENNReal.zero_rpow_of_pos hr0] using h0.ennrpow_const r
    have hBK : Tendsto (fun K : ℕ => ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)) ^ r *
        ENNReal.ofReal C₂) atTop (𝓝 0) := by
      have h : Tendsto (fun K : ℕ => ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)))
          atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine ENNReal.tendsto_ofReal ?_
        have : Tendsto (fun K : ℕ => nsEps m ^ (p - 1) * (1 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (nsEps m ^ (p - 1))
        refine this.congr' (Eventually.of_forall fun K => ?_)
        simp only
        ring
      have h' : Tendsto (fun K : ℕ =>
          ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)) ^ r) atTop (𝓝 0) := by
        simpa [ENNReal.zero_rpow_of_pos hr0] using h.ennrpow_const r
      simpa using ENNReal.Tendsto.mul_const h' (Or.inr ENNReal.ofReal_ne_top)
    have hin := ((tendsto_const_nhds (x := ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) ^ r *
      ENNReal.ofReal C₀)).add (ENNReal.Tendsto.const_mul
        ((tendsto_const_nhds (x := Hl)).add hδK) (Or.inr h2top))).add hBK
    have hlim := ENNReal.Tendsto.const_mul hin (Or.inr h3top)
    simp only [add_zero] at hlim
    exact ge_of_tendsto' hlim (key m)
  have hlim := ENNReal.Tendsto.const_mul
    ((ENNReal.Tendsto.mul_const (b := ENNReal.ofReal C₀) (rhn_tendsto_regError_rpow hp₀p hr0)
      (Or.inr ENNReal.ofReal_ne_top)).add (tendsto_const_nhds (x := 2 ^ (r - 1) * Hl)))
    (Or.inr h3top)
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto' hlim hstep1

/-!
## The higher trace bound at every length `≤ TW`
-/

/-- `E ((Tr A)²)^r ≤ C₂` at every length `j ≤ TW` (the committed `rhn_trace_sq_rpow_bound`
with `⌊Wu⌋` replaced by any `j ≤ TW`), from the `FullSourceMomentsContract.clock`.
-/
theorem rhw_trace_sq_rpow_bound_len (hM : FullSourceMomentsContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (T : ℝ) {r : ℝ} (hr : 1 / 2 ≤ r) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) →
      ∫⁻ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ 2) ^ r
        ∂growthPathLaw W b ≤ ENNReal.ofReal C₂ := by
  have h2r : 1 ≤ 2 * r := by linarith
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨C, W₀, hC⟩ := hM.clock b hb hb' E hE hE' T (2 * r) h2r
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set T' := max T 0
  refine ⟨(C' * (T' + 1)) ^ (2 * r), max W₀ 1, fun W hW j hj q hq0 hq1 => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hjle : (j : ℝ) ≤ T' * W := hj.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0.le)
  have hcl := hC W (le_of_max_le_left hW) j hj
  set Y := fun ω => (boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω with hY
  set f : GrowthPath W → ℝ := fun ω => (W : ℝ)⁻¹ * (Y ω).trace.re with hf
  have hYpsd : ∀ ω, (Y ω).PosSemidef := fun ω => posSemidef_conjTranspose_mul_self _
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    mul_nonneg (by positivity) (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).1
  have hfun : (fun ω => (W : ℂ)⁻¹ * (Y ω).trace) = fun ω => ((f ω : ℝ) : ℂ) := by
    funext ω
    have him := (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).2
    simp only [hf, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    congr 1
    exact Complex.ext rfl (by simp [← him])
  rw [hfun] at hcl
  have hcl' : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) (ENNReal.ofReal (2 * r)) (growthPathLaw W b) ≤
      ENNReal.ofReal (C' * ((j : ℝ) + 1)) :=
    hcl.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hmom := indicator_moment_le_of_eLpNorm hf0 h2r hcl'
  have hpt : ∀ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ 2) ^ r ≤
      ENNReal.ofReal ((W : ℝ)⁻¹ ^ (2 * r)) * ENNReal.ofReal (f ω ^ (2 * r)) := by
    intro ω
    have h0 := (trace_nearClock_le b E W j q hq0 ω).1
    have h1 := ns_trace_nearClock_le_clock b E W j hq0 hq1 ω
    have hle : (nearClock b E W j q ω).trace.re ≤ (W : ℝ)⁻¹ * f ω := by
      simp only [hf]; rw [← mul_assoc, ← sq, inv_pow]; exact h1
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hr0,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : (nearClock b E W j q ω).trace.re ^ 2 = (nearClock b E W j q ω).trace.re ^ (2 : ℝ) :=
      (Real.rpow_two _).symm
    rw [hsq, ← Real.rpow_mul h0, ← Real.mul_rpow (by positivity) (hf0 ω)]
    exact Real.rpow_le_rpow h0 hle (by linarith)
  calc ∫⁻ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ ^ (2 * r)) * ENNReal.ofReal (f ω ^ (2 * r))
          ∂growthPathLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal ((W : ℝ)⁻¹ ^ (2 * r)) *
          ∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * r)) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((W : ℝ)⁻¹ ^ (2 * r)) *
          ENNReal.ofReal ((C' * ((j : ℝ) + 1)) ^ (2 * r)) := by gcongr
    _ = ENNReal.ofReal ((C' * (((j : ℝ) + 1) / W)) ^ (2 * r)) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
          ← Real.mul_rpow (by positivity) (by positivity)]
        congr 2; field_simp
    _ ≤ ENNReal.ofReal ((C' * (T' + 1)) ^ (2 * r)) := by
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left ?_ hC'0) (by linarith))
        rw [div_le_iff₀ hW0]; nlinarith

/-!
## The decay at general lengths
-/

/-- `RhNearHigherLimsupDecay` at general lengths (fixed energy): the length `⌊W(t₁+R+s)⌋` is
replaced by any `m_W` with `m_W/W → t₁ + R + s`, with the explicit rate `c = D₀ r p (1 - rp)/2`
(`D₀ = transportD0 b E`); `C` is chosen before the source, `t₁`, the travel time and the length
sequence. Proved in `rhw_nearHigherLimsupDecay_length`. -/
def RhwNearHigherLimsupDecayLength : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p r : ℝ, 0 < p → p < 1 → 1 ≤ r → p * r < 1 →
      ∃ C : ℝ, ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q → ∀ s : ℝ, 1 ≤ s →
        ∀ m : ℕ → ℕ, IsWindowLength (t₁ + R + s) m →
          limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
              (fracTrace p (nearClock b E W (m W) q ω)) ^ r ∂growthPathLaw W b) atTop ≤
            ENNReal.ofReal (C * Real.exp (-(transportD0 b E * r * p * (1 - r * p) / 2 * s)))

/-- **The near-clock higher decay at general lengths**, with the constants of the committed
`rhn_nearHigherLimsupDecay` (`c = D₀rp(1-rp)/2`).
Hypotheses as there:
`RhnHigherLater`,
`RhHigherLimitDecay`, the `FullSourceGeneratorContract` (`moments`, `tight`) and
`NsCriticalClockLimitsExist`.
-/
theorem rhw_nearHigherLimsupDecay_length (hLater : RhnHigherLater) (hL : RhHigherLimitDecay)
    (hGen : FullSourceGeneratorContract) (hEx : NsCriticalClockLimitsExist) :
    RhwNearHigherLimsupDecayLength := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr
  have hr0 : 0 < r := by linarith
  set κ := transportD0 b E * r * p * (1 - r * p) / 2 with hκ
  have hκ0 : 0 < κ := by
    have := ns_transportD0_pos hb hE hE'
    have : 0 < 1 - r * p := by linarith [mul_comm p r]
    positivity
  obtain ⟨C₁, hC₁⟩ := hLater b hb hb' E hE hE' p r hp hp1 hr hpr 1 1 one_pos le_rfl
  set K₃ : ℝ := (3 : ℝ) ^ r * (2 : ℝ) ^ (r - 1) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  refine ⟨K₃ * max C₁ 0 * Real.exp κ, fun t₁ R q hq s hs m hm => ?_⟩
  have ht₀ : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  rcases ht₀.eq_or_lt with h0 | hpos
  · have hev : (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W (m W) q ω)) ^ r ∂growthPathLaw W b)
        =ᶠ[atTop] fun _ => 0 :=
      eventually_atTop.2 ⟨1, fun W hW =>
        rhn_lintegral_rpow_eq_zero_of_origin hp hr0 hq h0.symm hW _⟩
    rw [limsup_congr hev, limsup_const]
    exact zero_le
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c', hc'1, hc'2⟩ := exists_between hlt
  have hfreq : ∃ᶠ W in atTop, c' < ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b E W (m W) q ω)) ^ r ∂growthPathLaw W b :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hc'2
  obtain ⟨ψ, hψ, hψc⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨φ, hφ, Ω, _, P, Z, μ, hWL, hfdd, hμ⟩ := hEx b hb hb' E hE hE' t₁ R q hq hpos ψ hψ
  have hP := hWL.prob
  have hqnn := ns_isUnitSource_nonneg hq
  have hq1 : ∀ x, q x ≤ 1 := hq.2.2.2.2
  have hmeas : ∀ u, t₁ + R ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) := fun u hu k hk =>
    hWL.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  have hmono := hψ.comp hφ
  -- the travel times of the lengths `m W`
  set sW : ℕ → ℝ := fun W => (m W : ℝ) / W - t₁ - R with hsW
  have hsWt : Tendsto sW atTop (𝓝 s) := by
    have := (hm.sub_const t₁).sub_const R
    rwa [show t₁ + R + s - t₁ - R = s by ring] at this
  have hsWin : ∀ᶠ W : ℕ in atTop, sW W ∈ Set.Icc (s / 2) (s + 1) :=
    hsWt.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have htrav : ∀ᶠ W : ℕ in atTop, travelLength W t₁ R (sW W) = m W := by
    filter_upwards [eventually_ge_atTop 1] with W hW
    have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
    have hW0 : (W : ℝ) ≠ 0 := by linarith
    unfold travelLength
    rw [show t₁ + R + sW W = (m W : ℝ) / W by simp only [hsW]; ring, mul_div_cancel₀ _ hW0,
      Nat.floor_natCast]
  have hmT : ∀ᶠ W : ℕ in atTop, (m W : ℝ) ≤ (t₁ + R + s + 1) * W := by
    have hev := hm.eventually (gt_mem_nhds (show t₁ + R + s < t₁ + R + s + 1 by linarith))
    filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1
    have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
    rw [div_lt_iff₀ hW0] at hW
    linarith
  -- the upper passage at travel time `s`, along the lengths `m`
  set p₀ := p / 2 with hp₀
  have hp₀0 : 0 < p₀ := by positivity
  have hp₀p : p₀ < p := by linarith
  have hp₀r : p₀ * r < 1 := by
    have : p₀ * r = p * r / 2 := by rw [hp₀]; ring
    rw [this]; linarith
  obtain ⟨C₀, hC₀⟩ := hLater b hb hb' E hE hE' p₀ r hp₀0 (by linarith) hr hp₀r (s / 2) (s + 1)
    (by linarith) (by linarith)
  obtain ⟨W₀, hW₀⟩ := hC₀ t₁ R q hq
  obtain ⟨C₂, W₂, hC₂⟩ := rhw_trace_sq_rpow_bound_len hGen.moments hb hb' hE hE'
    (t₁ + R + s + 1) (r := r) (by linarith)
  have hus : t₁ + R < t₁ + R + s := by linarith
  have hupper := rhw_limsup_fracTrace_rpow_le_len hqnn (hmeas _ hus.le) hmono m
    (rhw_conv_moving_length hGen hb hb' hE hE' hq hpos hus hmono hfdd hm) (hμ _ hus.le) hp₀0
    hp₀p hp1 hr (C₀ := C₀) (C₂ := C₂)
    (by
      filter_upwards [hsWin, htrav, eventually_ge_atTop W₀] with W h1 h2 h3
      have h := hW₀ W h3 (sW W) h1
      rwa [h2] at h)
    (by
      filter_upwards [hmT, eventually_ge_atTop W₂] with W h1 h2
      exact hC₂ W h2 (m W) h1 q hqnn hq1)
  -- the lower bound `c' ≤ limsup` along the subsequence
  have hlow : c' ≤ limsup (fun n => ∫⁻ ω, ENNReal.ofReal
      (fracTrace p (nearClock b E ((ψ ∘ φ) n) (m ((ψ ∘ φ) n)) q ω)) ^ r
        ∂growthPathLaw ((ψ ∘ φ) n) b) atTop :=
    le_limsup_of_frequently_le (Frequently.of_forall fun n => (hψc (φ n)).le)
      (by isBoundedDefault)
  -- the limiting decay from travel time `1` to `s`
  have hdec := hL b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq Ω _ P Z hWL μ hμ 1 (s - 1)
    one_pos (by linarith)
  have hts : t₁ + R + 1 + (s - 1) = t₁ + R + s := by ring
  rw [hts] at hdec
  -- the finite-width bound at travel time `1`, passed to the limit
  obtain ⟨W₁, hW₁⟩ := hC₁ t₁ R q hq
  have h1 : t₁ + R ≤ t₁ + R + 1 := by linarith
  have hent := rhn_lintegral_limitFracTrace_rpow_le hqnn h1 (hmeas _ h1) hmono hfdd (hμ _ h1) hp
    hp1 hr0 (C := ENNReal.ofReal C₁) (eventually_atTop.2 ⟨W₁, fun W hW => by
      have h := hW₁ W hW 1 ⟨le_rfl, le_rfl⟩
      unfold travelLength at h
      exact h⟩)
  -- the chain of inequalities
  have hexp : Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2)) =
      Real.exp κ * Real.exp (-(κ * s)) := by
    rw [← Real.exp_add, hκ]; ring_nf
  have h3 : (3 : ℝ≥0∞) ^ r * 2 ^ (r - 1) = ENNReal.ofReal K₃ := by
    rw [hK₃, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hr0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
    norm_num
  have hfinal : c' ≤ ENNReal.ofReal (K₃ * max C₁ 0 * Real.exp κ * Real.exp (-(κ * s))) := by
    calc c' ≤ _ := hlow
      _ ≤ 3 ^ r * (2 ^ (r - 1) * ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s) ω) ^ r ∂P) := hupper
      _ ≤ 3 ^ r * (2 ^ (r - 1) * (ENNReal.ofReal
            (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2))) *
            ENNReal.ofReal (max C₁ 0))) := by
          gcongr
          refine hdec.trans ?_
          gcongr
          exact hent.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal K₃ * (ENNReal.ofReal
            (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * (s - 1) / 2))) *
            ENNReal.ofReal (max C₁ 0)) := by rw [← h3]; ring
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hK₃0, hexp]
          ring_nf
  exact absurd (hc'1.trans_le hfinal) (lt_irrefl _)

end BlockBand.Endpoints
