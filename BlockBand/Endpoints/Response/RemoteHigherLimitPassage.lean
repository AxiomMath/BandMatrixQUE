module

public import BlockBand.Endpoints.Response.NearSchattenGenerator
public import BlockBand.Endpoints.Response.RemoteHigherNearPassage
public import BlockBand.Endpoints.Response.RemoteHigherLimitScalar

/-!
# Passing nonlinear clock functionals between finite width and critical limits

Along the subsequence `φ` of a joint critical word limit (one-source family, source `q ≥ 0`), at
a time `u ≥ t₀` with a.s. clock measures `μ_u`:

* `rhl_lintegral_pair_le_liminf` (lower, Fatou direction): for continuous `c₁, c₂ ≥ 0` and a
  jointly continuous `G ≥ 0` nondecreasing in each argument on `[0, ∞)`,
  `E G(∫c₁ dμ_u, ∫c₂ dμ_u) ≤ liminf_n E G(Σ_i λ_i c₁(λ_i), Σ_i λ_i c₂(λ_i))`. Mechanism: the
  bounded continuous tests `G(Ψ₁,Ψ₂)` of the committed lower tests `Ψ_k = nsTestFun … (-1) …`
  (which are `≤ Σ_i λ_i c_k(λ_i)` at finite width), Fatou in the polynomial level, and the
  continuity of `G`. Used with `G(a,b) = (a+δ)^r` and `G(a,b) = κ(a+δ)^{r-1}b`.
* `rhl_limsup_rpow_clockSum_le` (upper, **constant one**): for continuous `0 ≤ c ≤ B`, `δ ≥ 0`,
  `r ≥ 1` and eventually `E ((Tr A)²)^r ≤ C₂`,
  `limsup_n E (Σ_i λ_i c(λ_i) + δ)^r ≤ E (∫ c dμ_u + δ)^r`. Mechanism: the committed split
  `Σ λc(λ) ≤ Ψ⁺ + B (Tr A)²/(K-1)`, the weighted convexity
  `(x+y)^r ≤ (1-τ)^{1-r}x^r + τ^{1-r}y^r` (`rhl_add_rpow_le_real`) twice, the bounded
  continuous test `(Ψ⁺+δ)^r`, the limit-side bound `Ψ⁺(Z) ≤ ∫ c dμ + 2/K`, then `K → ∞` and
  `τ ↓ 0`. The constant one is needed: the passage feeds the right side of an integrated
  inequality that is then iterated by Gronwall.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Polynomial Filter Topology Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- A continuous function with values in `[0, B]` as a bounded continuous function. -/
def rhlBCF {m : ℕ} (F : (Fin (m + 1) → ℂ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hFB : ∀ z, F z ≤ B) : BoundedContinuousFunction (Fin (m + 1) → ℂ) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ B fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have := hF0 x
    have := hF0 y
    have := hFB x
    have := hFB y
    rw [abs_le]; constructor <;> linarith

theorem rhl_BCF_apply {m : ℕ} (F : (Fin (m + 1) → ℂ) → ℝ) (hF : Continuous F) (B : ℝ)
    (hF0 : ∀ z, 0 ≤ F z) (hFB : ∀ z, F z ≤ B) (z : Fin (m + 1) → ℂ) :
    rhlBCF F hF B hF0 hFB z = F z := rfl

/-!
## Lower passage of a monotone functional of two clock integrals
-/

/-- **Lower passage along the subsequence** for `G(∫c₁, ∫c₂)` (finite-width bound required
only along `φ`). -/
theorem rhl_lintegral_pair_le_of_eventually_along {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {t₀ u : ℝ} (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c₁ c₂ : ℝ → ℝ} (hc₁ : Continuous c₁) (hc₁0 : ∀ x, 0 ≤ c₁ x) (hc₂ : Continuous c₂)
    (hc₂0 : ∀ x, 0 ≤ c₂ x) {G : ℝ → ℝ → ℝ} (hG : Continuous fun z : ℝ × ℝ => G z.1 z.2)
    (hG0 : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ G a b)
    (hGm : ∀ a a' b b', 0 ≤ a → a ≤ a' → 0 ≤ b → b ≤ b' → G a b ≤ G a' b') {C : ℝ≥0∞}
    (hbound : ∀ᶠ n : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (G (nsClockSum c₁ (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω))
          (nsClockSum c₂ (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω))) ∂growthPathLaw (φ n) b ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (G (∫ x, c₁ x ∂μ ω) (∫ x, c₂ x ∂μ ω)) ∂P ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  set Kr : ℕ → ℝ := fun K => (K : ℝ) + 2 with hKr
  set δ : ℕ → ℝ := fun K => 1 / ((K : ℝ) + 1) with hδ
  have hKr0 : ∀ K, 0 ≤ Kr K := fun K => by positivity
  set m : ℕ → ℕ := fun K => max (nsPoly c₁ hc₁ K).natDegree (nsPoly c₂ hc₂ K).natDegree with hm
  set T₁ : (K : ℕ) → (Fin (m K + 1) → ℂ) → ℝ :=
    fun K => nsTestFun (nsPoly c₁ hc₁ K) (m K) (-1) (δ K) (Kr K) (Kr K) with hT₁
  set T₂ : (K : ℕ) → (Fin (m K + 1) → ℂ) → ℝ :=
    fun K => nsTestFun (nsPoly c₂ hc₂ K) (m K) (-1) (δ K) (Kr K) (Kr K) with hT₂
  have hT₁0 : ∀ K z, 0 ≤ T₁ K z := fun K z => ns_testFun_nonneg _ _ _ _ _ (hKr0 K) z
  have hT₂0 : ∀ K z, 0 ≤ T₂ K z := fun K z => ns_testFun_nonneg _ _ _ _ _ (hKr0 K) z
  have hT₁le : ∀ K z, T₁ K z ≤ Kr K := fun K z => ns_testFun_le _ _ _ _ _ (hKr0 K) z
  have hT₂le : ∀ K z, T₂ K z ≤ Kr K := fun K z => ns_testFun_le _ _ _ _ _ (hKr0 K) z
  set F : (K : ℕ) → (Fin (m K + 1) → ℂ) → ℝ := fun K z => G (T₁ K z) (T₂ K z) with hFdef
  have hFc : ∀ K, Continuous (F K) := fun K =>
    hG.comp ((ns_continuous_testFun _ _ _ _ _ _).prodMk (ns_continuous_testFun _ _ _ _ _ _))
  have hF0 : ∀ K z, 0 ≤ F K z := fun K z => hG0 _ _ (hT₁0 K z) (hT₂0 K z)
  have hFle : ∀ K z, F K z ≤ G (Kr K) (Kr K) := fun K z =>
    hGm _ _ _ _ (hT₁0 K z) (hT₁le K z) (hT₂0 K z) (hT₂le K z)
  set Ψ : (K : ℕ) → BoundedContinuousFunction (Fin (m K + 1) → ℂ) ℝ :=
    fun K => rhlBCF (F K) (hFc K) (G (Kr K) (Kr K)) (hF0 K) (hFle K) with hΨ
  have hΨapp : ∀ K z, Ψ K z = F K z := fun K z => rfl
  -- Step A: the limit expectations of the tests are bounded by `C`
  have hA : ∀ K, ∫ ω, Ψ K (nsClockVec Z (m K) u ω) ∂P ≤ C.toReal := by
    intro K
    have hlim := hfdd (m K + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) (Ψ K)
    refine le_of_tendsto hlim (hbound.mono fun k hk => ?_)
    refine ns_integral_le_toReal (fun ω => hF0 K _) (fun ω => ?_) hC hk
    have hvec : (fun l : Fin (m K + 1) => wordValue b E (noTags (φ k)) (fun _ => q) (φ k)
        ⌊(φ k : ℝ) * u⌋₊ ω (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (m K + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    show Ψ K _ ≤ _
    rw [hΨapp, hvec]
    have hApsd := ns_nearClock_posSemidef b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q hq ω
    exact hGm _ _ _ _ (hT₁0 K _)
      (ns_testFun_lower_le _ (le_max_left _ _) (fun x _ => hc₁0 x) (hKr0 K)
        (ns_poly_spec c₁ hc₁ K) hApsd) (hT₂0 K _)
      (ns_testFun_lower_le _ (le_max_right _ _) (fun x _ => hc₂0 x) (hKr0 K)
        (ns_poly_spec c₂ hc₂ K) hApsd)
  -- Step B: the same in `ℝ≥0∞`
  have hmeasV : ∀ K, Measurable fun ω => Ψ K (nsClockVec Z (m K) u ω) := fun K =>
    (Ψ K).continuous.measurable.comp (ns_measurable_clockVec hmeas (m K))
  have hB : ∀ K, ∫⁻ ω, ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) ∂P ≤ C := by
    intro K
    have hint : Integrable (fun ω => Ψ K (nsClockVec Z (m K) u ω)) P :=
      Integrable.of_bound (hmeasV K).aestronglyMeasurable (G (Kr K) (Kr K))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (abs_of_nonneg (hF0 K _)).trans_le (hFle K _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hF0 K _)]
    exact (ENNReal.ofReal_le_ofReal (hA K)).trans (ENNReal.ofReal_toReal hC).le
  -- Step C: Fatou in `K`
  have hC' : ∫⁻ ω, liminf (fun K => ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω))) atTop ∂P ≤
      C :=
    (lintegral_liminf_le fun K => ENNReal.measurable_ofReal.comp (hmeasV K)).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hB))
  -- Step D: a.s. the tests converge up to `G(∫ c₁ dμ_u, ∫ c₂ dμ_u)`
  refine le_trans (lintegral_mono_ae ?_) hC'
  filter_upwards [hμ] with ω hω
  set M := (Z (clockWord 1) u ω).re
  set I₁ := ∫ x, c₁ x ∂μ ω
  set I₂ := ∫ x, c₂ x ∂μ ω
  have hI₁0 : 0 ≤ I₁ := integral_nonneg hc₁0
  have hI₂0 : 0 ≤ I₂ := integral_nonneg hc₂0
  have hM0 : 0 ≤ M := by
    have h1 := ns_clockMeasure_real_univ hω
    have h2 : 0 ≤ (μ ω).real univ := measureReal_nonneg
    linarith
  have hKrt : Tendsto Kr atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ K in atTop, M ≤ Kr K - 1 ∧ I₁ ≤ Kr K ∧ I₂ ≤ Kr K :=
    ((hKrt.eventually_ge_atTop (M + 1)).and ((hKrt.eventually_ge_atTop I₁).and
      (hKrt.eventually_ge_atTop I₂))).mono fun K hK => ⟨by linarith [hK.1], hK.2.1, hK.2.2⟩
  have hlow : ∀ᶠ K in atTop, ENNReal.ofReal (G (max (I₁ - 2 * δ K * M) 0)
      (max (I₂ - 2 * δ K * M) 0)) ≤ ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) := by
    filter_upwards [hev] with K hK
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hΨapp]
    have hδ0 : 0 ≤ 2 * δ K * M := by positivity
    have h1 := ns_testFun_lower_ge hω hc₁ (nsPoly c₁ hc₁ K) (m := m K) (le_max_left _ _)
      (M := Kr K) (ns_poly_spec c₁ hc₁ K) hK.1
    have h2 := ns_testFun_lower_ge hω hc₂ (nsPoly c₂ hc₂ K) (m := m K) (le_max_right _ _)
      (M := Kr K) (ns_poly_spec c₂ hc₂ K) hK.1
    rw [min_eq_right (by linarith [hK.2.1])] at h1
    rw [min_eq_right (by linarith [hK.2.2])] at h2
    exact hGm _ _ _ _ (le_max_right _ _) (max_le h1 (hT₁0 K _)) (le_max_right _ _)
      (max_le h2 (hT₂0 K _))
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmx : ∀ I : ℝ, 0 ≤ I → Tendsto (fun K => max (I - 2 * δ K * M) 0) atTop (𝓝 I) := by
    intro I hI
    have h1 : Tendsto (fun K => I - 2 * δ K * M) atTop (𝓝 I) := by
      have := ((hδlim.const_mul 2).mul_const M).const_sub I
      simpa using this
    have h2 := h1.max (tendsto_const_nhds (x := (0 : ℝ)))
    rwa [max_eq_left hI] at h2
  have hlim : Tendsto (fun K => ENNReal.ofReal (G (max (I₁ - 2 * δ K * M) 0)
      (max (I₂ - 2 * δ K * M) 0))) atTop (𝓝 (ENNReal.ofReal (G I₁ I₂))) :=
    ENNReal.tendsto_ofReal (((hG.tendsto (I₁, I₂))).comp
      ((hmx I₁ hI₁0).prodMk_nhds (hmx I₂ hI₂0)))
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hlow

/-- **Lower passage, `liminf` form.** `E G(∫c₁ dμ_u, ∫c₂ dμ_u) ≤ liminf_n E G(Σc₁, Σc₂)` along
`φ`. -/
theorem rhl_lintegral_pair_le_liminf {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {t₀ u : ℝ} (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c₁ c₂ : ℝ → ℝ} (hc₁ : Continuous c₁) (hc₁0 : ∀ x, 0 ≤ c₁ x) (hc₂ : Continuous c₂)
    (hc₂0 : ∀ x, 0 ≤ c₂ x) {G : ℝ → ℝ → ℝ} (hG : Continuous fun z : ℝ × ℝ => G z.1 z.2)
    (hG0 : ∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ G a b)
    (hGm : ∀ a a' b b', 0 ≤ a → a ≤ a' → 0 ≤ b → b ≤ b' → G a b ≤ G a' b') :
    ∫⁻ ω, ENNReal.ofReal (G (∫ x, c₁ x ∂μ ω) (∫ x, c₂ x ∂μ ω)) ∂P ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal
        (G (nsClockSum c₁ (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω))
          (nsClockSum c₂ (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω))) ∂growthPathLaw (φ n) b)
        atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun C hC => ?_
  obtain ⟨ψ, hψ, hψC⟩ :=
    extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hC)
  have hfdd' : NsFddAlong b E q t₀ P Z (φ ∘ ψ) := fun m ws ts h Ψ =>
    (hfdd m ws ts h Ψ).comp hψ.tendsto_atTop
  exact rhl_lintegral_pair_le_of_eventually_along hq hu hmeas hfdd' hμ hc₁ hc₁0 hc₂ hc₂0 hG hG0
    hGm (Eventually.of_forall fun n => (hψC n).le)

/-!
## Sharp upper passage of `(Σ_i λ_i c(λ_i) + δ)^r`
-/

theorem rhl_tendsto_ofReal_inv_K {B : ℝ} :
    Tendsto (fun K : ℕ => ENNReal.ofReal (B / ((K : ℝ) + 2 - 1))) atTop (𝓝 0) := by
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  have : Tendsto (fun K : ℕ => B * (1 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
  refine this.congr' (Eventually.of_forall fun K => ?_)
  simp only
  ring

/-- **Sharp upper passage** (constant one). Along the subsequence of a critical word limit, at a
time `u ≥ t₀` with a.s. clock measures: for continuous `0 ≤ c ≤ B`, `δ ≥ 0`, `r ≥ 1` and
eventually `E ((Tr A)²)^r ≤ C₂` at length `⌊Wu⌋`,
`limsup_n E (Σ_i λ_i c(λ_i) + δ)^r ≤ E (∫ c dμ_u + δ)^r`. -/
theorem rhl_limsup_rpow_clockSum_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) {B : ℝ} (hcB : ∀ x, c x ≤ B)
    {δ : ℝ} (hδ : 0 ≤ δ) {r : ℝ} (hr : 1 ≤ r) {C₂ : ℝ}
    (hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₂) :
    limsup (fun n => ∫⁻ ω, ENNReal.ofReal
        ((nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω) + δ) ^ r)
          ∂growthPathLaw (φ n) b) atTop ≤
      ∫⁻ ω, ENNReal.ofReal ((∫ x, c x ∂μ ω + δ) ^ r) ∂P := by
  set L := limsup (fun n => ∫⁻ ω, ENNReal.ofReal
    ((nsClockSum c (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω) + δ) ^ r)
      ∂growthPathLaw (φ n) b) atTop
  set Hl := ∫⁻ ω, ENNReal.ofReal ((∫ x, c x ∂μ ω + δ) ^ r) ∂P
  have hr0 : 0 ≤ r := by linarith
  have hB0 : 0 ≤ B := (hc0 0).trans (hcB 0)
  rcases eq_or_ne Hl ⊤ with hHl | hHl
  · rw [hHl]; exact le_top
  refine rhl_le_of_weighted r hHl fun τ hτ hτ1 => ?_
  set wa : ℝ := (1 - τ) ^ (1 - r) with hwa
  set wb : ℝ := τ ^ (1 - r) with hwb
  have hwa0 : 0 ≤ wa := Real.rpow_nonneg (by linarith) _
  have hwb0 : 0 ≤ wb := Real.rpow_nonneg hτ.le _
  -- the bound at polynomial level `K`
  have key : ∀ K : ℕ, L ≤ ENNReal.ofReal wa * (ENNReal.ofReal wa * Hl + ENNReal.ofReal wb *
      ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)) ^ r) +
      ENNReal.ofReal wb * (ENNReal.ofReal (B / ((K : ℝ) + 2 - 1)) ^ r * ENNReal.ofReal C₂) := by
    intro K
    set Kr : ℝ := (K : ℝ) + 2 with hKr
    have hKr2 : 2 ≤ Kr := by rw [hKr]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
    set δ' : ℝ := 1 / Kr ^ 2 with hδ'
    have hδ'0 : 0 ≤ δ' := by positivity
    have hδ'1 : δ' ≤ 1 := by
      rw [hδ', div_le_one (by positivity)]; nlinarith
    obtain ⟨π, hπ⟩ := exists_polynomial_near_of_continuousOn 0 Kr c hc.continuousOn δ'
      (by positivity)
    have happ : ∀ x ∈ Icc 0 Kr, |π.eval x - c x| ≤ δ' := fun x hx => (hπ x hx).le
    set md := π.natDegree
    set M := B * Kr + 2 * Kr with hM
    have hM0 : 0 ≤ M := by positivity
    set T : (Fin (md + 1) → ℂ) → ℝ := nsTestFun π md 1 δ' Kr M with hT
    have hT0 : ∀ z, 0 ≤ T z := fun z => ns_testFun_nonneg _ _ _ _ _ hM0 z
    have hTle : ∀ z, T z ≤ M := fun z => ns_testFun_le _ _ _ _ _ hM0 z
    set Fz : (Fin (md + 1) → ℂ) → ℝ := fun z => (T z + δ) ^ r with hFz
    have hFc : Continuous Fz :=
      ((ns_continuous_testFun π md 1 δ' Kr M).add continuous_const).rpow_const
        fun _ => Or.inr hr0
    have hF0 : ∀ z, 0 ≤ Fz z := fun z => Real.rpow_nonneg (by linarith [hT0 z]) _
    have hFle : ∀ z, Fz z ≤ (M + δ) ^ r := fun z =>
      Real.rpow_le_rpow (by linarith [hT0 z]) (by linarith [hTle z]) hr0
    set Ψ := rhlBCF Fz hFc ((M + δ) ^ r) hF0 hFle with hΨ
    have hΨapp : ∀ z, Ψ z = (T z + δ) ^ r := fun z => rfl
    set Y := ENNReal.ofReal wb * (ENNReal.ofReal (B / (Kr - 1)) ^ r * ENNReal.ofReal C₂)
    -- finite width
    have hfin : ∀ W : ℕ, ∫⁻ ω, ENNReal.ofReal
        ((nsClockSum c (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω) + δ) ^ r) ∂growthPathLaw W b ≤
        ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw W b) +
        ENNReal.ofReal wb * (ENNReal.ofReal (B / (Kr - 1)) ^ r * ∫⁻ ω, ENNReal.ofReal
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b) := by
      intro W
      have := isProbabilityMeasure_growthPathLaw W b
      set A := fun ω => nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω
      have hmΨ : Measurable fun ω => Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace) :=
        Ψ.continuous.measurable.comp (ns_measurable_clockMoments b E W _ q md)
      have hint : Integrable (fun ω => Ψ (fun l : Fin (md + 1) =>
          ((A ω) ^ ((l : ℕ) + 1)).trace)) (growthPathLaw W b) :=
        Integrable.of_bound hmΨ.aestronglyMeasurable ((M + δ) ^ r)
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs]; exact (abs_of_nonneg (hF0 _)).trans_le (hFle _))
      rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hF0 _)]
      set F₂ : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal wa *
        ENNReal.ofReal (Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace))
      set F₃ : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal wb *
        (ENNReal.ofReal (B / (Kr - 1)) ^ r * ENNReal.ofReal ((A ω).trace.re ^ 2) ^ r)
      have hF₃ : Measurable F₃ := by
        have h1 : Measurable fun ω => ENNReal.ofReal ((A ω).trace.re ^ 2) ^ r :=
          (ENNReal.measurable_ofReal.comp
            ((ns_measurable_trace_nearClock b E W _ q).pow_const 2)).pow_const r
        exact (h1.const_mul _).const_mul _
      calc ∫⁻ ω, ENNReal.ofReal ((nsClockSum c (A ω) + δ) ^ r) ∂growthPathLaw W b
          ≤ ∫⁻ ω, (F₂ ω + F₃ ω) ∂growthPathLaw W b := by
            refine lintegral_mono fun ω => ?_
            have hApsd := ns_nearClock_posSemidef b E W ⌊(W : ℝ) * u⌋₊ q hq ω
            have h3 : nsClockSum c (A ω) ≤ T (fun l => (A ω ^ ((l : ℕ) + 1)).trace) +
                B * (A ω).trace.re ^ 2 / (Kr - 1) :=
              ns_clockSum_le_testFun_upper π le_rfl hc0 hcB hδ'0 hδ'1 hKr2 le_rfl happ hApsd
            have hS0 := ns_clockSum_nonneg (fun x _ => hc0 x) hApsd
            have hT0' := hT0 (fun l => (A ω ^ ((l : ℕ) + 1)).trace)
            have hK1 : 0 < Kr - 1 := by linarith
            set y : ℝ := B / (Kr - 1) * (A ω).trace.re ^ 2 with hy
            have hy0 : 0 ≤ y := by positivity
            have h4 : nsClockSum c (A ω) + δ ≤
                (T (fun l => (A ω ^ ((l : ℕ) + 1)).trace) + δ) + y := by
              have : B * (A ω).trace.re ^ 2 / (Kr - 1) = y := by rw [hy]; ring
              linarith
            have h5 := rhl_add_rpow_le_real (x := T (fun l => (A ω ^ ((l : ℕ) + 1)).trace) + δ)
              (by linarith) hy0 hr hτ hτ1
            have h6 : (nsClockSum c (A ω) + δ) ^ r ≤
                wa * (T (fun l => (A ω ^ ((l : ℕ) + 1)).trace) + δ) ^ r + wb * y ^ r :=
              (Real.rpow_le_rpow (by linarith) h4 hr0).trans h5
            simp only [F₂, F₃]
            rw [hΨapp]
            refine (ENNReal.ofReal_le_ofReal h6).trans_eq ?_
            have hB1 : 0 ≤ B / (Kr - 1) := div_nonneg hB0 hK1.le
            rw [ENNReal.ofReal_add (mul_nonneg hwa0 (Real.rpow_nonneg (by linarith) _))
                (mul_nonneg hwb0 (Real.rpow_nonneg hy0 _)), ENNReal.ofReal_mul hwa0,
              ENNReal.ofReal_mul hwb0, hy, Real.mul_rpow hB1 (sq_nonneg _),
              ENNReal.ofReal_mul (Real.rpow_nonneg hB1 _),
              ENNReal.ofReal_rpow_of_nonneg hB1 hr0, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) hr0]
        _ = ∫⁻ ω, F₂ ω ∂growthPathLaw W b + ∫⁻ ω, F₃ ω ∂growthPathLaw W b :=
            lintegral_add_right _ hF₃
        _ = _ := by
            simp only [F₂, F₃]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0 ENNReal.ofReal_ne_top)]
    have hvec : ∀ k : ℕ, ∀ ω : GrowthPath (φ k), (fun l : Fin (md + 1) =>
        wordValue b E (noTags (φ k)) (fun _ => q) (φ k) ⌊(φ k : ℝ) * u⌋₊ ω
          (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (md + 1) => ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      fun k ω => funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    have hlimΨ := hfdd (md + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) Ψ
    simp_rw [hvec] at hlimΨ
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nsClockSum c (nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) + δ) ^ r)
          ∂growthPathLaw (φ k) b ≤
        ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
            ∂growthPathLaw (φ k) b) + Y := by
      filter_upwards [hφ.tendsto_atTop.eventually hUI] with k h2
      refine (hfin (φ k)).trans ?_
      exact add_le_add le_rfl (mul_le_mul_right (mul_le_mul_right h2 _) _)
    have hlim : Tendsto (fun k => ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ
        (fun l : Fin (md + 1) => ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
          ∂growthPathLaw (φ k) b) + Y) atTop
        (𝓝 (ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y)) :=
      (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hlimΨ)
        (Or.inr ENNReal.ofReal_ne_top)).add tendsto_const_nhds
    have hL : L ≤ ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y :=
      (limsup_le_limsup hev).trans_eq hlim.limsup_eq
    have hmV : Measurable fun ω => Ψ (nsClockVec Z md u ω) :=
      Ψ.continuous.measurable.comp (ns_measurable_clockVec hmeas md)
    have hintZ : Integrable (fun ω => Ψ (nsClockVec Z md u ω)) P :=
      Integrable.of_bound hmV.aestronglyMeasurable ((M + δ) ^ r)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs]; exact (abs_of_nonneg (hF0 _)).trans_le (hFle _))
    have hZ : ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) ≤
        ENNReal.ofReal wa * Hl + ENNReal.ofReal wb * ENNReal.ofReal (2 * δ' * Kr) ^ r := by
      rw [ofReal_integral_eq_lintegral_ofReal hintZ (Eventually.of_forall fun ω => hF0 _)]
      calc ∫⁻ ω, ENNReal.ofReal (Ψ (nsClockVec Z md u ω)) ∂P
          ≤ ∫⁻ ω, (ENNReal.ofReal wa * ENNReal.ofReal ((∫ x, c x ∂μ ω + δ) ^ r) +
              ENNReal.ofReal wb * ENNReal.ofReal (2 * δ' * Kr) ^ r) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hμ] with ω hω
            rw [hΨapp]
            have h1 := ns_testFun_upper_le hω hc hc0 π (m := md) le_rfl hδ'0 (by linarith) hM0
              happ
            have hI0 : 0 ≤ ∫ x, c x ∂μ ω := integral_nonneg hc0
            have hη : 0 ≤ 2 * δ' * Kr := by positivity
            have h2 : (T (nsClockVec Z md u ω) + δ) ^ r ≤
                wa * (∫ x, c x ∂μ ω + δ) ^ r + wb * (2 * δ' * Kr) ^ r := by
              refine (Real.rpow_le_rpow (by linarith [hT0 (nsClockVec Z md u ω)])
                (show T (nsClockVec Z md u ω) + δ ≤ (∫ x, c x ∂μ ω + δ) + 2 * δ' * Kr by
                  linarith) hr0).trans ?_
              exact rhl_add_rpow_le_real (by linarith) hη hr hτ hτ1
            refine (ENNReal.ofReal_le_ofReal h2).trans_eq ?_
            rw [ENNReal.ofReal_add (mul_nonneg hwa0 (Real.rpow_nonneg (by linarith) _))
                (mul_nonneg hwb0 (Real.rpow_nonneg hη _)), ENNReal.ofReal_mul hwa0,
              ENNReal.ofReal_mul hwb0, ENNReal.ofReal_rpow_of_nonneg hη hr0]
        _ = ENNReal.ofReal wa * Hl + ENNReal.ofReal wb * ENNReal.ofReal (2 * δ' * Kr) ^ r := by
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const, measure_univ, mul_one]
    calc L ≤ ENNReal.ofReal wa * ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y := hL
      _ ≤ ENNReal.ofReal wa * (ENNReal.ofReal wa * Hl +
            ENNReal.ofReal wb * ENNReal.ofReal (2 * δ' * Kr) ^ r) + Y := by gcongr
  -- `K → ∞`
  have hδK : Tendsto (fun K : ℕ => ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)) ^ r)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun K : ℕ => ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2)))
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
    have h2 := h0.ennrpow_const r
    rwa [ENNReal.zero_rpow_of_pos (by linarith)] at h2
  have hBK : Tendsto (fun K : ℕ => ENNReal.ofReal (B / ((K : ℝ) + 2 - 1)) ^ r *
      ENNReal.ofReal C₂) atTop (𝓝 0) := by
    have h2 := (rhl_tendsto_ofReal_inv_K (B := B)).ennrpow_const r
    rw [ENNReal.zero_rpow_of_pos (by linarith)] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr ENNReal.ofReal_ne_top)
  have hlim := (ENNReal.Tendsto.const_mul ((tendsto_const_nhds
      (x := ENNReal.ofReal wa * Hl)).add (ENNReal.Tendsto.const_mul hδK
        (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal wb)))
      (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal wa)).add
    (ENNReal.Tendsto.const_mul hBK (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal wb))
  simp only [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim key

end BlockBand.Endpoints
