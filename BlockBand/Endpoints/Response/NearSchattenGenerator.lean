module

public import BlockBand.Endpoints.Response.NearSchattenGeneratorMatrix

/-!
# The integrated regularized generator inequality at critical limits

This file proves `NsRegularizedLimitGenerator` (`nsg_regularizedLimitGenerator`) from its
finite-width form `NsgFiniteTraceGenerator`: the trace generator of `Tr f_ε(A)` at finite width,
integrated in time with the stops removed, asymptotically as `W → ∞`:
`E Tr f_ε(A_{⌊Wu₂⌋}) + ∫_{u₁}^{u₂} E[-𝒢_ε(⌊Wu⌋)] du ≤ E Tr f_ε(A_{⌊Wu₁⌋}) + o(1)`, where
`𝒢_ε = nsgGenExpr` is the spectral right side of the Schatten trace generator at the path.
The finite-width statement comes from polynomial approximation through three derivatives on a trace
stop, removal of the stops by the fixed clock/current moments, and the evaluation of the word
generator on clock words.

* `nsg_lintegral_le_of_eventually_along`, `nsg_lintegral_le_liminf`: lower (Fatou) passage of
  clock integrals along the subsequence of a critical limit, in `liminf` form.
* `nsg_limsup_clockSum_le`: upper passage of bounded continuous clock integrals.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Polynomial Filter Topology Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- The finite-width integrated trace generator of `Tr f_ε(A)`.
Fixed `0 < b < 1/2`, bulk `E`, `0 < p < 1`, a unit source `IsUnitSource t₁ R q`, `ε > 0` and
times `t₁ + R < u₁ ≤ u₂` after the injection; for every `θ > 0`, for all large widths `W`:
`E Tr f_ε(A_{⌊Wu₂⌋}) + ∫_{u₁}^{u₂} E[-𝒢_ε(⌊Wu⌋)] du ≤ E Tr f_ε(A_{⌊Wu₁⌋}) + θ`
(`A = nearClock`, `Tr f_ε(A) = Σ_i λ_i · f_ε(λ_i)/λ_i = nsClockSum nsRegKernel`,
`𝒢_ε = nsgGenExpr`, the spectral right side of the Schatten trace generator; `-𝒢_ε ≥ 0` a.s.).

It is a finite-width statement and asserts no sign or dissipation (the bound
`-𝒢_ε ≥ κ Σλ²(λ+ε)^{p-2}` is `nsg_ae_genExpr_le`) and no passage to critical limits (proved in
`nsg_regularizedLimitGenerator`). -/
def NsgFiniteTraceGenerator : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ ε : ℝ, 0 < ε → ∀ u₁ u₂ : ℝ, t₁ + R < u₁ → u₁ ≤ u₂ → ∀ θ : ℝ, 0 < θ →
      ∀ᶠ W : ℕ in atTop,
        ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw W b +
          ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, ENNReal.ofReal
            (-nsgGenExpr b E p ε q W ⌊(W : ℝ) * u⌋₊ ω) ∂growthPathLaw W b ≤
        ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
            (nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω)) ∂growthPathLaw W b + ENNReal.ofReal θ

/-!
## Lower passage in `liminf` form
-/

/-- Lower passage along the subsequence: the analogue of `ns_lintegral_le_of_eventually` with the
finite-width bound required only along `φ`. -/
theorem nsg_lintegral_le_of_eventually_along {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) {C : ℝ≥0∞}
    (hbound : ∀ᶠ n : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, c x ∂μ ω) ∂P ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  set Kr : ℕ → ℝ := fun K => (K : ℝ) + 2 with hKr
  set δ : ℕ → ℝ := fun K => 1 / ((K : ℝ) + 1) with hδ
  have hKr0 : ∀ K, 0 ≤ Kr K := fun K => by positivity
  set m : ℕ → ℕ := fun K => (nsPoly c hc K).natDegree with hm
  set Ψ : (K : ℕ) → BoundedContinuousFunction (Fin (m K + 1) → ℂ) ℝ :=
    fun K => nsTestBCF (nsPoly c hc K) (m K) (-1) (δ K) (Kr K) (Kr K) (hKr0 K) with hΨ
  have hΨapp : ∀ K z, Ψ K z = nsTestFun (nsPoly c hc K) (m K) (-1) (δ K) (Kr K) (Kr K) z :=
    fun K z => rfl
  -- the limit expectations of the tests are bounded by `C`
  have hA : ∀ K, ∫ ω, Ψ K (nsClockVec Z (m K) u ω) ∂P ≤ C.toReal := by
    intro K
    have hlim := hfdd (m K + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) (Ψ K)
    refine le_of_tendsto hlim (hbound.mono fun k hk => ?_)
    refine ns_integral_le_toReal (fun ω => ns_testFun_nonneg _ _ _ _ _ (hKr0 K) _)
      (fun ω => ?_) hC hk
    have hvec : (fun l : Fin (m K + 1) => wordValue b E (noTags (φ k)) (fun _ => q) (φ k)
        ⌊(φ k : ℝ) * u⌋₊ ω (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (m K + 1) => ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    show nsTestFun _ _ _ _ _ _ _ ≤ _
    rw [hvec]
    exact ns_testFun_lower_le _ le_rfl (fun x _ => hc0 x) (hKr0 K) (ns_poly_spec c hc K)
      (ns_nearClock_posSemidef b E _ _ q hq ω)
  -- the same in `ℝ≥0∞`
  have hmeasV : ∀ K, Measurable fun ω => Ψ K (nsClockVec Z (m K) u ω) := fun K =>
    (Ψ K).continuous.measurable.comp (ns_measurable_clockVec hmeas (m K))
  have hB : ∀ K, ∫⁻ ω, ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) ∂P ≤ C := by
    intro K
    have hint : Integrable (fun ω => Ψ K (nsClockVec Z (m K) u ω)) P :=
      Integrable.of_bound (hmeasV K).aestronglyMeasurable (Kr K) (Eventually.of_forall fun ω => by
        rw [hΨapp, Real.norm_eq_abs, abs_of_nonneg (ns_testFun_nonneg _ _ _ _ _ (hKr0 K) _)]
        exact ns_testFun_le _ _ _ _ _ (hKr0 K) _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => by
        show 0 ≤ Ψ K (nsClockVec Z (m K) u ω)
        rw [hΨapp]; exact ns_testFun_nonneg _ _ _ _ _ (hKr0 K) _)]
    exact (ENNReal.ofReal_le_ofReal (hA K)).trans (ENNReal.ofReal_toReal hC).le
  -- Fatou in `K`
  have hC' : ∫⁻ ω, liminf (fun K => ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω))) atTop ∂P ≤ C :=
    (lintegral_liminf_le fun K => ENNReal.measurable_ofReal.comp (hmeasV K)).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hB))
  -- a.s. the tests converge up to `∫ c dμ_u`
  refine le_trans (lintegral_mono_ae ?_) hC'
  filter_upwards [hμ] with ω hω
  set M := (Z (clockWord 1) u ω).re
  set I := ∫ x, c x ∂μ ω
  have hM0 : 0 ≤ M := by
    have h1 := ns_clockMeasure_real_univ hω
    have h2 : 0 ≤ (μ ω).real univ := measureReal_nonneg
    linarith
  have hKr : Tendsto Kr atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ K in atTop, M ≤ Kr K - 1 ∧ I ≤ Kr K :=
    ((hKr.eventually_ge_atTop (M + 1)).and (hKr.eventually_ge_atTop I)).mono fun K hK =>
      ⟨by linarith [hK.1], hK.2⟩
  have hlow : ∀ᶠ K in atTop, ENNReal.ofReal (I - 2 * δ K * M) ≤
      ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) := by
    filter_upwards [hev] with K hK
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hΨapp]
    have h := ns_testFun_lower_ge hω hc (nsPoly c hc K) (m := m K) le_rfl (M := Kr K)
      (ns_poly_spec c hc K) hK.1
    have hδ0 : 0 ≤ 2 * δ K * M := by positivity
    rw [min_eq_right (by linarith [hK.2])] at h
    exact h
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun K => ENNReal.ofReal (I - 2 * δ K * M)) atTop (𝓝 (ENNReal.ofReal I)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := ((hδlim.const_mul 2).mul_const M).const_sub I
    simpa using this
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hlow

/-- Lower passage, `liminf` form: `E ∫ c dμ_u ≤ liminf_n E Σ_i λ_i c(λ_i)` along `φ`. -/
theorem nsg_lintegral_le_liminf {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, c x ∂μ ω) ∂P ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun C hC => ?_
  obtain ⟨ψ, hψ, hψC⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hC)
  have hfdd' : NsFddAlong b E q t₀ P Z (φ ∘ ψ) := fun m ws ts h Ψ =>
    (hfdd m ws ts h Ψ).comp hψ.tendsto_atTop
  exact nsg_lintegral_le_of_eventually_along hq hu hmeas hfdd' hμ hc hc0
    (Eventually.of_forall fun n => (hψC n).le)

/-- `liminf a + liminf c ≤ M` when eventually `a + c ≤ M` (`ℝ≥0∞`). -/
theorem nsg_liminf_add_le {a c : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (h : ∀ᶠ n in atTop, a n + c n ≤ M) :
    liminf a atTop + liminf c atTop ≤ M := by
  have hA : liminf a atTop ≤ M :=
    liminf_le_of_frequently_le' (h.mono fun n hn => le_trans le_self_add hn).frequently
  have hC : liminf c atTop ≤ M :=
    liminf_le_of_frequently_le' (h.mono fun n hn => le_trans le_add_self hn).frequently
  rcases eq_or_ne (liminf a atTop) 0 with h0 | h0
  · rw [h0, zero_add]; exact hC
  rcases eq_or_ne (liminf c atTop) 0 with h1 | h1
  · rw [h1, add_zero]; exact hA
  refine le_of_forall_lt fun x hx => ?_
  obtain ⟨y, hy, z, hz, hxyz⟩ := ENNReal.exists_lt_add_of_lt_add hx h0 h1
  obtain ⟨n, hn, hyn, hzn⟩ :=
    (h.and ((eventually_lt_of_lt_liminf hy).and (eventually_lt_of_lt_liminf hz))).exists
  exact hxyz.trans_le ((add_le_add hyn.le hzn.le).trans hn)

/-!
## Upper passage of bounded clock integrals
-/

/-- Upper passage of a bounded continuous clock integral. Along the subsequence of a critical
word limit, at a time `u ≥ t₀` with a.s. clock measures: for continuous `0 ≤ c ≤ B` and
eventually `E (Tr A)² ≤ C₂`, `limsup_n E Σ_i λ_i c(λ_i) ≤ E ∫ c dμ_u`. -/
theorem nsg_limsup_clockSum_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) {B : ℝ} (hcB : ∀ x, c x ≤ B) {C₂ : ℝ}
    (hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ∂growthPathLaw W b ≤
          ENNReal.ofReal C₂) :
    limsup (fun n => ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b) atTop ≤
      ∫⁻ ω, ENNReal.ofReal (∫ x, c x ∂μ ω) ∂P := by
  set L := limsup (fun n => ∫⁻ ω, ENNReal.ofReal
    (nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b) atTop
  set Hl := ∫⁻ ω, ENNReal.ofReal (∫ x, c x ∂μ ω) ∂P
  have hB0 : 0 ≤ B := (hc0 0).trans (hcB 0)
  have key : ∀ K : ℕ, L ≤ Hl + ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)) +
      ENNReal.ofReal (B / ((K : ℝ) + 2 - 1)) * ENNReal.ofReal C₂ := by
    intro K
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
    set Ψ := nsTestBCF π md 1 δ Kr M hM0
    have hΨapp : ∀ z, Ψ z = nsTestFun π md 1 δ Kr M z := fun z => rfl
    have hfin : ∀ W : ℕ, ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b ≤
        ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw W b) +
        ENNReal.ofReal (B / (Kr - 1)) * ∫⁻ ω, ENNReal.ofReal
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ∂growthPathLaw W b := by
      intro W
      have := isProbabilityMeasure_growthPathLaw W b
      set A := fun ω => nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω
      have hmΨ : Measurable fun ω => Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace) :=
        Ψ.continuous.measurable.comp (ns_measurable_clockMoments b E W _ q md)
      have hint : Integrable (fun ω => Ψ (fun l : Fin (md + 1) =>
          ((A ω) ^ ((l : ℕ) + 1)).trace)) (growthPathLaw W b) :=
        Integrable.of_bound hmΨ.aestronglyMeasurable M (Eventually.of_forall fun ω => by
          rw [hΨapp, Real.norm_eq_abs, abs_of_nonneg (ns_testFun_nonneg _ _ _ _ _ hM0 _)]
          exact ns_testFun_le _ _ _ _ _ hM0 _)
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => by
        show 0 ≤ Ψ _
        rw [hΨapp]; exact ns_testFun_nonneg _ _ _ _ _ hM0 _)]
      set F₂ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace))
      set F₃ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (B / (Kr - 1)) * ENNReal.ofReal ((A ω).trace.re ^ 2)
      have hF₃ : Measurable F₃ := (ENNReal.measurable_ofReal.comp
          ((ns_measurable_trace_nearClock b E W _ q).pow_const 2)).const_mul _
      calc ∫⁻ ω, ENNReal.ofReal (nsClockSum c (A ω)) ∂growthPathLaw W b
          ≤ ∫⁻ ω, (F₂ ω + F₃ ω) ∂growthPathLaw W b := by
            refine lintegral_mono fun ω => ?_
            have hApsd := ns_nearClock_posSemidef b E W ⌊(W : ℝ) * u⌋₊ q hq ω
            have h3 := ns_clockSum_le_testFun_upper π le_rfl hc0 hcB hδ0 hδ1 hKr2 le_rfl happ
              hApsd
            have ht0 := ns_testFun_nonneg π md 1 δ Kr hM0 (fun l => (A ω ^ ((l : ℕ) + 1)).trace)
            have hK1 : 0 < Kr - 1 := by linarith
            have h4 : B * (A ω).trace.re ^ 2 / (Kr - 1) = B / (Kr - 1) * (A ω).trace.re ^ 2 := by
              ring
            simp only [F₂, F₃]
            rw [hΨapp, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add ht0 (by positivity)]
            exact ENNReal.ofReal_le_ofReal (by linarith)
        _ = ∫⁻ ω, F₂ ω ∂growthPathLaw W b + ∫⁻ ω, F₃ ω ∂growthPathLaw W b :=
            lintegral_add_right _ hF₃
        _ = _ := by
            simp only [F₃]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hvec : ∀ k : ℕ, ∀ ω : GrowthPath (φ k), (fun l : Fin (md + 1) =>
        wordValue b E (noTags (φ k)) (fun _ => q) (φ k) ⌊(φ k : ℝ) * u⌋₊ ω
          (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (md + 1) => ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      fun k ω => funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    have hlimΨ := hfdd (md + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) Ψ
    simp_rw [hvec] at hlimΨ
    set Y := ENNReal.ofReal (B / (Kr - 1)) * ENNReal.ofReal C₂
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ k) b ≤
        ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
            ∂growthPathLaw (φ k) b) + Y := by
      filter_upwards [hφ.tendsto_atTop.eventually hUI] with k h2
      refine (hfin (φ k)).trans ?_
      gcongr
      exact mul_le_mul_right h2 _
    have hlim : Tendsto (fun k => ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
        ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
          ∂growthPathLaw (φ k) b) + Y) atTop
        (𝓝 (ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y)) :=
      (ENNReal.tendsto_ofReal hlimΨ).add tendsto_const_nhds
    have hL : L ≤ ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y :=
      (limsup_le_limsup hev).trans_eq hlim.limsup_eq
    have hmV : Measurable fun ω => Ψ (nsClockVec Z md u ω) :=
      Ψ.continuous.measurable.comp (ns_measurable_clockVec hmeas md)
    have hintZ : Integrable (fun ω => Ψ (nsClockVec Z md u ω)) P :=
      Integrable.of_bound hmV.aestronglyMeasurable M (Eventually.of_forall fun ω => by
        rw [hΨapp, Real.norm_eq_abs, abs_of_nonneg (ns_testFun_nonneg _ _ _ _ _ hM0 _)]
        exact ns_testFun_le _ _ _ _ _ hM0 _)
    have hZ : ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) ≤
        Hl + ENNReal.ofReal (2 * δ * Kr) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintZ (Eventually.of_forall fun ω => by
        show 0 ≤ Ψ _
        rw [hΨapp]; exact ns_testFun_nonneg _ _ _ _ _ hM0 _)]
      calc ∫⁻ ω, ENNReal.ofReal (Ψ (nsClockVec Z md u ω)) ∂P
          ≤ ∫⁻ ω, (ENNReal.ofReal (∫ x, c x ∂μ ω) + ENNReal.ofReal (2 * δ * Kr)) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hμ] with ω hω
            rw [hΨapp]
            have h1 := ns_testFun_upper_le hω hc hc0 π (m := md) le_rfl hδ0 (by linarith) hM0 happ
            have hI0 : 0 ≤ ∫ x, c x ∂μ ω := integral_nonneg hc0
            calc ENNReal.ofReal (nsTestFun π md 1 δ Kr M (nsClockVec Z md u ω))
                ≤ ENNReal.ofReal (∫ x, c x ∂μ ω + 2 * δ * Kr) := ENNReal.ofReal_le_ofReal h1
              _ = ENNReal.ofReal (∫ x, c x ∂μ ω) + ENNReal.ofReal (2 * δ * Kr) :=
                  ENNReal.ofReal_add hI0 (by positivity)
        _ = Hl + ENNReal.ofReal (2 * δ * Kr) := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    calc L ≤ ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y := hL
      _ ≤ Hl + ENNReal.ofReal (2 * δ * Kr) + Y := by gcongr
  have hδK : Tendsto (fun K : ℕ => ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)))
      atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Tendsto (fun K : ℕ => (K : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h : Tendsto (fun K : ℕ => (2 : ℝ) * ((K : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
      simpa using h1.inv_tendsto_atTop.const_mul (2 : ℝ)
    refine h.congr' (Eventually.of_forall fun K => ?_)
    have : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    field_simp
  have hBK : Tendsto (fun K : ℕ => ENNReal.ofReal (B / ((K : ℝ) + 2 - 1)) *
      ENNReal.ofReal C₂) atTop (𝓝 0) := by
    have h : Tendsto (fun K : ℕ => ENNReal.ofReal (B / ((K : ℝ) + 2 - 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      have : Tendsto (fun K : ℕ => B * (1 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
      refine this.congr' (Eventually.of_forall fun K => ?_)
      simp only
      ring
    simpa using ENNReal.Tendsto.mul_const h (Or.inr ENNReal.ofReal_ne_top)
  have hlim := ((tendsto_const_nhds (x := Hl)).add hδK).add hBK
  simp only [add_zero] at hlim
  exact ge_of_tendsto' hlim key

/-!
## Assembly
-/

theorem nsg_clockSum_const_mul {n : Type*} [Fintype n] [DecidableEq n] (κ : ℝ) (c : ℝ → ℝ)
    (A : Matrix n n ℂ) : nsClockSum (fun x => κ * c x) A = κ * nsClockSum c A := by
  unfold nsClockSum
  rw [← Multiset.sum_map_mul_left]
  congr 1
  exact Multiset.map_congr rfl fun z _ => by ring

/-- `f_ε(x)/x ≤ p ε^{p-1}` (the regularized kernel is bounded). -/
theorem nsg_regKernel_le {p ε : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (x : ℝ) :
    nsRegKernel p ε x ≤ p * ε ^ (p - 1) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [ns_regKernel_of_nonpos hε hx]
  · rw [ns_regKernel_of_pos hx, div_le_iff₀ hx]
    exact ns_shiftPow_sub_le hp0 hp1 hε hx.le

theorem nsg_measurable_floor_comp (g : ℕ → ℝ≥0∞) (W : ℕ) :
    Measurable fun u : ℝ => g ⌊(W : ℝ) * u⌋₊ :=
  (measurable_from_nat (f := g)).comp (Nat.measurable_floor.comp (measurable_const_mul _))

/-- **`NsRegularizedLimitGenerator` from the isolated finite-width trace generator**.
Inputs: the isolated
`NsgFiniteTraceGenerator`; the `ConditionalBlockGUECount` (a.s. unitarity of `𝕊`, for
`T_ii ≤ g`); the `FullSourceMomentsContract` (the second moment of `Tr A` for the upper
passage at `u₁`).
-/
theorem nsg_regularizedLimitGenerator (hFin : NsgFiniteTraceGenerator)
    (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hMom : FullSourceMomentsContract) : NsRegularizedLimitGenerator := by
  intro b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hZ μ hμ ε hε u₁ u₂ hu₁ hu₁₂
  have := hZ.prob
  obtain ⟨φ, hφ, hfdd⟩ := ns_fdd_of_isWordLimit hZ
  have hq0 : ∀ x, 0 ≤ q x := hq.2.2.2.1.1
  have hq1 : ∀ x, q x ≤ 1 := hq.2.2.2.2
  have hR0 : 0 ≤ t₁ + R := by linarith [hq.1, hq.2.1]
  set κ := nsDecayRate b E p with hκdef
  have hκ : 0 ≤ κ := ns_decayRate_nonneg hb hE hE' hp hp1
  set cD : ℝ → ℝ := fun x => κ * nsDissKernel p ε x with hcDdef
  have hcD : Continuous cD := continuous_const.mul (ns_continuous_dissKernel hε)
  have hcD0 : ∀ x, 0 ≤ cD x := fun x => mul_nonneg hκ (ns_dissKernel_nonneg hε x)
  have hmeasu : ∀ u, t₁ + R ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) :=
    fun u hu k hk => hZ.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
    (nearClock b E (φ n) ⌊(φ n : ℝ) * u₂⌋₊ q ω)) ∂growthPathLaw (φ n) b with ha
  set cc : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, ENNReal.ofReal (nsClockSum (nsRegKernel p ε)
    (nearClock b E (φ n) ⌊(φ n : ℝ) * u₁⌋₊ q ω)) ∂growthPathLaw (φ n) b with hcc
  set G : ℕ → ℕ → ℝ≥0∞ := fun n j => ∫⁻ ω, ENNReal.ofReal (nsClockSum cD
    (nearClock b E (φ n) j q ω)) ∂growthPathLaw (φ n) b with hG
  set d : ℕ → ℝ≥0∞ := fun n => ∫⁻ u in Icc u₁ u₂, G n ⌊(φ n : ℝ) * u⌋₊ with hd
  -- the finite-width inequality along `φ`, through the dissipation bound
  have hstep1 : ∀ θ : ℝ, 0 < θ → ∀ᶠ n in atTop, a n + d n ≤ cc n + ENNReal.ofReal θ := by
    intro θ hθ
    have h := hφ.tendsto_atTop.eventually
      (hFin b hb hb' E hE hE' p hp hp1 t₁ R q hq ε hε u₁ u₂ hu₁ hu₁₂ θ hθ)
    filter_upwards [h, hφ.tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn hWpos
    refine le_trans (add_le_add le_rfl ?_) hn
    refine lintegral_mono fun u => lintegral_mono_ae ?_
    filter_upwards [nsg_ae_genExpr_le hCount hb hb' hE hE' hp.le hp1.le hε hq0 hWpos
      ⌊(φ n : ℝ) * u⌋₊] with ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hcDdef, nsg_clockSum_const_mul]
    linarith
  -- lower passage at `u₂`
  have hA : ∫⁻ ω, nsRegTrace p ε (μ u₂ ω) ∂P ≤ liminf a atTop := by
    have h := nsg_lintegral_le_liminf hq0 (show t₁ + R ≤ u₂ by linarith)
      (hmeasu u₂ (by linarith)) hfdd (hμ u₂ (by linarith)) (ns_continuous_regKernel hε)
      (ns_regKernel_nonneg hp.le hε)
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) h
    filter_upwards [hμ u₂ (by linarith)] with ω hω
    exact ns_regTrace_eq hω hp.le hε
  -- lower passage in time (Fatou in `u`)
  have hD : ENNReal.ofReal κ * ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, nsDissTrace p ε (μ u ω) ∂P ≤
      liminf d atTop := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ u in Icc u₁ u₂, ENNReal.ofReal κ * ∫⁻ ω, nsDissTrace p ε (μ u ω) ∂P
        ≤ ∫⁻ u in Icc u₁ u₂, liminf (fun n => G n ⌊(φ n : ℝ) * u⌋₊) atTop := by
          refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
          have hu0 : t₁ + R ≤ u := by linarith [hu.1]
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine le_trans (le_of_eq (lintegral_congr_ae ?_))
            (nsg_lintegral_le_liminf hq0 hu0 (hmeasu u hu0) hfdd (hμ u hu0) hcD hcD0)
          filter_upwards [hμ u hu0] with ω hω
          rw [ns_dissTrace_eq hω hε, ← ENNReal.ofReal_mul hκ, hcDdef, integral_const_mul]
      _ ≤ liminf d atTop :=
          lintegral_liminf_le' fun n => (nsg_measurable_floor_comp (G n) (φ n)).aemeasurable
  -- upper passage at `u₁`
  obtain ⟨C₂, W₀, hC₂⟩ := ns_trace_sq_bound hMom hb hb' hE hE' (u := u₁) (by linarith)
  have hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
      ((nearClock b E W ⌊(W : ℝ) * u₁⌋₊ q ω).trace.re ^ 2) ∂growthPathLaw W b ≤
        ENNReal.ofReal C₂ := eventually_atTop.2 ⟨W₀, fun W hW => hC₂ W hW q hq0 hq1⟩
  have hC : limsup cc atTop ≤ ∫⁻ ω, nsRegTrace p ε (μ u₁ ω) ∂P := by
    have h := nsg_limsup_clockSum_le hq0 (show t₁ + R ≤ u₁ by linarith)
      (hmeasu u₁ (by linarith)) hφ hfdd (hμ u₁ (by linarith)) (ns_continuous_regKernel hε)
      (ns_regKernel_nonneg hp.le hε) (nsg_regKernel_le hp.le hp1.le hε) hUI
    refine h.trans (le_of_eq (lintegral_congr_ae ?_))
    filter_upwards [hμ u₁ (by linarith)] with ω hω
    exact (ns_regTrace_eq hω hp.le hε).symm
  -- combine
  set Cl := ∫⁻ ω, nsRegTrace p ε (μ u₁ ω) ∂P
  refine ENNReal.le_of_forall_pos_le_add fun θ hθ hClt => ?_
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  have hlt : limsup cc atTop < Cl + ENNReal.ofReal (θ / 2) :=
    hC.trans_lt (ENNReal.lt_add_right hClt.ne (by simpa using hθ2))
  have hev : ∀ᶠ n in atTop, a n + d n ≤ Cl + ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) := by
    filter_upwards [hstep1 (θ / 2) hθ2, eventually_lt_of_limsup_lt hlt] with n h1 h2
    exact h1.trans (add_le_add h2.le le_rfl)
  have hsum := nsg_liminf_add_le hev
  have hθe : ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) = (θ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_add hθ2.le hθ2.le, add_halves, ENNReal.ofReal_coe_nnreal]
  rw [add_assoc, hθe] at hsum
  exact (add_le_add hA hD).trans hsum

end BlockBand.Endpoints
