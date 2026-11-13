module

public import BlockBand.Endpoints.Response.NearSchattenUpper
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Passing higher fractional clock moments `E H_p^r` to critical limits

Part of the proof of the remote higher-moment theorem: for singular powers, use the
smaller-power entrance and a slightly larger moment `r' > r` with `pr' < 1`; they pay
respectively the small eigenvalues and uniform integrability. The `r`-th power analogue of the
passages of the near-Schatten decay theorem.

Along the subsequence of a joint critical word limit (one-source family, source `q ≥ 0`), at a
time `u ≥ t₀` with a.s. clock measures `μ_u`:

* `rhn_lintegral_limitFracTrace_rpow_le` (lower, Fatou direction): if eventually
  `E (Tr A^p)^r ≤ C` at length `⌊Wu⌋`, then `E H_p(μ_u)^r ≤ C` (`r > 0`). Mechanism: the bounded
  continuous tests `Ψ_K^r` (`Ψ_K` the lower tests `nsTestFun … (-1) …`, which are
  `≤ Σ_i λ_i c(λ_i)` at finite width), Fatou in `K`, and the cut kernels `(max x ε_m)^{p-1}`.
* `rhn_limsup_fracTrace_rpow_le` (upper): if eventually `E (Tr A^{p₀})^r ≤ C₀` (`p₀ < p`, the
  smaller-power entrance) and `E (Tr A)^{2r} ≤ C₂` (the higher trace bound, here from
  `FullSourceMomentsContract.clock`, `rhn_trace_sq_rpow_bound`), then
  `limsup E (Tr A^p)^r ≤ 3^r 2^{r-1} E H_p(μ_u)^r` (`r ≥ 1`). Mechanism: the pointwise split
  `Tr A^p ≤ a^{p-p₀} Tr A^{p₀} + Ψ⁺(moments) + B (Tr A)²/(K-1)` raised to the power `r` with
  `(x+y+z)^r ≤ 3^r(x^r+y^r+z^r)`, the bounded continuous test `(Ψ⁺)^r`, the limit-side bound
  `Ψ⁺(Z) ≤ ∫ c dμ + 2δK` with `(x+y)^r ≤ 2^{r-1}(x^r+y^r)`, then `K → ∞`, `a ↓ 0`. The constant
  `3^r 2^{r-1}` is harmless for the exponential bounds this feeds (only the rate matters).
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
## Elementary power inequalities and the power tests
-/

/-- `(x + y + z)^r ≤ 3^r (x^r + y^r + z^r)` in `ℝ≥0∞` (`r ≥ 0`). -/
theorem rhn_rpow_add3_le (x y z : ℝ≥0∞) {r : ℝ} (hr : 0 ≤ r) :
    (x + y + z) ^ r ≤ 3 ^ r * (x ^ r + y ^ r + z ^ r) := by
  set m := max (max x y) z with hm
  have hx : x ≤ m := (le_max_left x y).trans (le_max_left _ _)
  have hy : y ≤ m := (le_max_right x y).trans (le_max_left _ _)
  have hz : z ≤ m := le_max_right _ _
  have hsum : x + y + z ≤ 3 * m := by
    calc x + y + z ≤ m + m + m := add_le_add (add_le_add hx hy) hz
      _ = 3 * m := by ring
  have hmr : m ^ r ≤ x ^ r + y ^ r + z ^ r := by
    rcases max_choice (max x y) z with h | h
    · rw [hm, h]
      rcases max_choice x y with h' | h'
      · rw [h']; exact le_self_add.trans le_self_add
      · rw [h']; exact le_add_self.trans le_self_add
    · rw [hm, h]; exact le_add_self
  calc (x + y + z) ^ r ≤ (3 * m) ^ r := ENNReal.rpow_le_rpow hsum hr
    _ = 3 ^ r * m ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr
    _ ≤ 3 ^ r * (x ^ r + y ^ r + z ^ r) := by gcongr

/-- The power test `(nsTestFun π m σ δ K M)^r` as a bounded continuous function (`M, r ≥ 0`). -/
def rhn_powTestBCF (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 ≤ r) :
    BoundedContinuousFunction (Fin (m + 1) → ℂ) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => nsTestFun π m σ δ K M z ^ r,
      (ns_continuous_testFun π m σ δ K M).rpow_const fun _ => Or.inr hr⟩ (M ^ r)
    fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 := Real.rpow_nonneg (ns_testFun_nonneg π m σ δ K hM x) r
      have h2 := Real.rpow_nonneg (ns_testFun_nonneg π m σ δ K hM y) r
      have h3 := Real.rpow_le_rpow (ns_testFun_nonneg π m σ δ K hM x)
        (ns_testFun_le π m σ δ K hM x) hr
      have h4 := Real.rpow_le_rpow (ns_testFun_nonneg π m σ δ K hM y)
        (ns_testFun_le π m σ δ K hM y) hr
      rw [abs_le]; constructor <;> linarith

theorem rhn_powTestBCF_apply (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 ≤ r)
    (z : Fin (m + 1) → ℂ) : rhn_powTestBCF π m σ δ K M hM r hr z = nsTestFun π m σ δ K M z ^ r :=
  rfl

theorem rhn_powTestBCF_nonneg (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 ≤ r)
    (z : Fin (m + 1) → ℂ) : 0 ≤ rhn_powTestBCF π m σ δ K M hM r hr z :=
  Real.rpow_nonneg (ns_testFun_nonneg π m σ δ K hM z) r

theorem rhn_powTestBCF_le (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) (r : ℝ) (hr : 0 ≤ r)
    (z : Fin (m + 1) → ℂ) : rhn_powTestBCF π m σ δ K M hM r hr z ≤ M ^ r :=
  Real.rpow_le_rpow (ns_testFun_nonneg π m σ δ K hM z) (ns_testFun_le π m σ δ K hM z) hr

/-!
## Lower passage
-/

/-- **Lower passage of powers of clock integrals to a critical limit.** Along the subsequence of
a joint critical word limit, at a time `u ≥ t₀` with a.s. clock measures `μ_u`: if eventually
`E (Σ_i λ_i c(λ_i))^r ≤ C` for the near clock at length `⌊Wu⌋` (`c ≥ 0` continuous, `r > 0`),
then `E (∫ c dμ_u)^r ≤ C`. -/
theorem rhn_lintegral_rpow_le_of_eventually {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {t₀ u : ℝ} (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) {r : ℝ} (hr : 0 < r) {C : ℝ≥0∞}
    (hbound : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω) ^ r) ∂growthPathLaw W b ≤ C) :
    ∫⁻ ω, ENNReal.ofReal ((∫ x, c x ∂μ ω) ^ r) ∂P ≤ C := by
  rcases eq_or_ne C ⊤ with rfl | hC
  · exact le_top
  set Kr : ℕ → ℝ := fun K => (K : ℝ) + 2 with hKr
  set δ : ℕ → ℝ := fun K => 1 / ((K : ℝ) + 1) with hδ
  have hKr0 : ∀ K, 0 ≤ Kr K := fun K => by positivity
  set m : ℕ → ℕ := fun K => (nsPoly c hc K).natDegree with hm
  set Ψ : (K : ℕ) → BoundedContinuousFunction (Fin (m K + 1) → ℂ) ℝ :=
    fun K => rhn_powTestBCF (nsPoly c hc K) (m K) (-1) (δ K) (Kr K) (Kr K) (hKr0 K) r hr.le
    with hΨ
  have hΨapp : ∀ K z, Ψ K z =
      nsTestFun (nsPoly c hc K) (m K) (-1) (δ K) (Kr K) (Kr K) z ^ r := fun K z => rfl
  have hΨ0 : ∀ K z, 0 ≤ Ψ K z := fun K z => rhn_powTestBCF_nonneg _ _ _ _ _ _ _ _ _ z
  have hΨle : ∀ K z, Ψ K z ≤ Kr K ^ r := fun K z => rhn_powTestBCF_le _ _ _ _ _ _ _ _ _ z
  -- Step A: the limit expectations of the tests are bounded by `C`
  have hA : ∀ K, ∫ ω, Ψ K (nsClockVec Z (m K) u ω) ∂P ≤ C.toReal := by
    intro K
    have hlim := hfdd (m K + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) (Ψ K)
    refine le_of_tendsto hlim ((hφ.tendsto_atTop.eventually hbound).mono fun k hk => ?_)
    refine ns_integral_le_toReal (fun ω => hΨ0 K _) (fun ω => ?_) hC hk
    have hvec : (fun l : Fin (m K + 1) => wordValue b E (noTags (φ k)) (fun _ => q) (φ k)
        ⌊(φ k : ℝ) * u⌋₊ ω (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (m K + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    show Ψ K _ ≤ _
    rw [hΨapp, hvec]
    exact Real.rpow_le_rpow (ns_testFun_nonneg _ _ _ _ _ (hKr0 K) _)
      (ns_testFun_lower_le _ le_rfl (fun x _ => hc0 x) (hKr0 K) (ns_poly_spec c hc K)
        (ns_nearClock_posSemidef b E _ _ q hq ω)) hr.le
  -- Step B: the same in `ℝ≥0∞`
  have hmeasV : ∀ K, Measurable fun ω => Ψ K (nsClockVec Z (m K) u ω) := fun K =>
    (Ψ K).continuous.measurable.comp (ns_measurable_clockVec hmeas (m K))
  have hB : ∀ K, ∫⁻ ω, ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) ∂P ≤ C := by
    intro K
    have hint : Integrable (fun ω => Ψ K (nsClockVec Z (m K) u ω)) P :=
      Integrable.of_bound (hmeasV K).aestronglyMeasurable (Kr K ^ r)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 K _)]
          exact hΨle K _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hΨ0 K _)]
    exact (ENNReal.ofReal_le_ofReal (hA K)).trans (ENNReal.ofReal_toReal hC).le
  -- Step C: Fatou in `K`
  have hC' : ∫⁻ ω, liminf (fun K => ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω))) atTop ∂P ≤
      C :=
    (lintegral_liminf_le fun K => ENNReal.measurable_ofReal.comp (hmeasV K)).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hB))
  -- Step D: a.s. the tests converge up to `(∫ c dμ_u)^r`
  refine le_trans (lintegral_mono_ae ?_) hC'
  filter_upwards [hμ] with ω hω
  set M := (Z (clockWord 1) u ω).re
  set I := ∫ x, c x ∂μ ω
  have hI0 : 0 ≤ I := integral_nonneg hc0
  have hM0 : 0 ≤ M := by
    have h1 := ns_clockMeasure_real_univ hω
    have h2 : 0 ≤ (μ ω).real univ := measureReal_nonneg
    linarith
  have hKrt : Tendsto Kr atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ K in atTop, M ≤ Kr K - 1 ∧ I ≤ Kr K :=
    ((hKrt.eventually_ge_atTop (M + 1)).and (hKrt.eventually_ge_atTop I)).mono fun K hK =>
      ⟨by linarith [hK.1], hK.2⟩
  have hlow : ∀ᶠ K in atTop, ENNReal.ofReal (max (I - 2 * δ K * M) 0 ^ r) ≤
      ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω)) := by
    filter_upwards [hev] with K hK
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hΨapp]
    have h := ns_testFun_lower_ge hω hc (nsPoly c hc K) (m := m K) le_rfl (M := Kr K)
      (ns_poly_spec c hc K) hK.1
    have hδ0 : 0 ≤ 2 * δ K * M := by positivity
    rw [min_eq_right (by linarith [hK.2])] at h
    have ht0 := ns_testFun_nonneg (nsPoly c hc K) (m K) (-1) (δ K) (Kr K) (hKr0 K)
      (nsClockVec Z (m K) u ω)
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le h ht0) hr.le
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun K => ENNReal.ofReal (max (I - 2 * δ K * M) 0 ^ r)) atTop
      (𝓝 (ENNReal.ofReal (I ^ r))) := by
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Tendsto (fun K => I - 2 * δ K * M) atTop (𝓝 I) := by
      have := ((hδlim.const_mul 2).mul_const M).const_sub I
      simpa using this
    have h2 := (h1.max (tendsto_const_nhds (x := (0 : ℝ)))).rpow_const (p := r) (Or.inr hr.le)
    rwa [max_eq_left hI0] at h2
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hlow

/-- **Lower passage of `H_p^r`** (`0 < p < 1`, `r > 0`): along the subsequence of a critical
word limit, at a time `u ≥ t₀` with a.s. clock measures, if eventually `E (Tr A^p)^r ≤ C` at
length `⌊Wu⌋`, then `E H_p(μ_u)^r ≤ C`. -/
theorem rhn_lintegral_limitFracTrace_rpow_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {t₀ u : ℝ} (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ClockWord → ℝ → Ω → ℂ}
    (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p r : ℝ} (hp : 0 < p)
    (hp1 : p < 1) (hr : 0 < r) {C : ℝ≥0∞}
    (hbound : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw W b ≤ C) :
    ∫⁻ ω, limitFracTrace p (μ ω) ^ r ∂P ≤ C := by
  set X : ℕ → Ω → ℝ≥0∞ := fun m ω =>
    ENNReal.ofReal (∫ x, nsCutKernel (nsEps m) (p - 1) x ∂μ ω) with hX
  have hXr : ∀ m ω, X m ω ^ r = ENNReal.ofReal ((∫ x, nsCutKernel (nsEps m) (p - 1) x ∂μ ω) ^ r) :=
    fun m ω => ENNReal.ofReal_rpow_of_nonneg
      (integral_nonneg (ns_cutKernel_nonneg (ns_eps_pos m))) hr.le
  have hm : ∀ m, ∫⁻ ω, X m ω ^ r ∂P ≤ C := by
    intro m
    simp_rw [hXr]
    refine rhn_lintegral_rpow_le_of_eventually hq hu hmeas hφ hfdd hμ
      (ns_continuous_cutKernel (ns_eps_pos m)) (ns_cutKernel_nonneg (ns_eps_pos m)) hr ?_
    filter_upwards [hbound] with W hW
    refine le_trans (lintegral_mono fun ω => ?_) hW
    have hA := ns_nearClock_posSemidef b E W ⌊(W : ℝ) * u⌋₊ q hq ω
    rw [ENNReal.ofReal_rpow_of_nonneg (fracTrace_nonneg _ _) hr.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
      (ns_clockSum_nonneg (fun x _ => ns_cutKernel_nonneg (ns_eps_pos m) x) hA)
      (ns_clockSum_cutKernel_le hA hp hp1) hr.le)
  have hae : ∀ m, AEMeasurable (fun ω => X m ω ^ r) P := fun m =>
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (ns_aemeasurable_integral_clock hmeas hμ
        (ns_continuous_cutKernel (ns_eps_pos m)))).pow_const r
  calc ∫⁻ ω, limitFracTrace p (μ ω) ^ r ∂P
      ≤ ∫⁻ ω, liminf (fun m => X m ω ^ r) atTop ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hμ] with ω hω
        have h := ns_limitFracTrace_le_liminf hω hp1
        have hmono := ENNReal.monotone_rpow_of_nonneg hr.le
        calc limitFracTrace p (μ ω) ^ r ≤ (liminf (fun m => X m ω) atTop) ^ r := hmono h
          _ = liminf (fun m => X m ω ^ r) atTop :=
              hmono.map_liminf_of_continuousAt (fun m => X m ω)
                ENNReal.continuous_rpow_const.continuousAt
    _ ≤ liminf (fun m => ∫⁻ ω, X m ω ^ r ∂P) atTop := lintegral_liminf_le' hae
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hm)

/-!
## The higher trace bound
-/

/-- **`E (Tr A)^{2r}` bound** from `FullSourceMomentsContract.clock` (exponent `2r`): at a fixed
time `u ≥ 0` there are `C₂`, `W₀` with `E ((Tr A)²)^r ≤ C₂` at length `⌊Wu⌋` for `W ≥ W₀` and
every test `0 ≤ q ≤ 1` (`r ≥ 1/2`). -/
theorem rhn_trace_sq_rpow_bound (hM : FullSourceMomentsContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {u : ℝ} (hu : 0 ≤ u) {r : ℝ}
    (hr : 1 / 2 ≤ r) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) →
      ∫⁻ ω, ENNReal.ofReal ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ^ r
        ∂growthPathLaw W b ≤ ENNReal.ofReal C₂ := by
  have h2r : 1 ≤ 2 * r := by linarith
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨C, W₀, hC⟩ := hM.clock b hb hb' E hE hE' u (2 * r) h2r
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine ⟨(C' * (u + 1)) ^ (2 * r), max W₀ 1, fun W hW q hq0 hq1 => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  set j := ⌊(W : ℝ) * u⌋₊ with hj
  have hjle : (j : ℝ) ≤ (W : ℝ) * u := Nat.floor_le (by positivity)
  have hcl := hC W (le_of_max_le_left hW) j (by linarith)
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
    _ ≤ ENNReal.ofReal ((C' * (u + 1)) ^ (2 * r)) := by
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left ?_ hC'0) (by linarith))
        rw [div_le_iff₀ hW0]; nlinarith

/-!
## Upper passage
-/

/-- `ofReal (2 ε_m^{p-p₀})^r → 0` (`p₀ < p`, `r > 0`). -/
theorem rhn_tendsto_regError_rpow {p p₀ r : ℝ} (hp₀p : p₀ < p) (hr : 0 < r) :
    Tendsto (fun m => ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) ^ r) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => nsEps m ^ (p - p₀)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (p - p₀) (Or.inr (by linarith))).tendsto).comp
      (tendsto_nhdsWithin_iff.1 ns_tendsto_eps).1
    rw [Real.zero_rpow (by linarith)] at this
    exact this
  have h2 : Tendsto (fun m => ENNReal.ofReal (2 * nsEps m ^ (p - p₀))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (by simpa using h1.const_mul 2)
  simpa [ENNReal.zero_rpow_of_pos hr] using h2.ennrpow_const r

/-- **Upper passage of `H_p^r` to a critical limit.** Along the subsequence
of a joint critical word limit (one-source family, `q ≥ 0`), at a time `u ≥ t₀` with a.s. clock
measures `μ_u`: if eventually `E (Tr A^{p₀})^r ≤ C₀` (`0 < p₀ < p < 1`, `r ≥ 1`) and
`E ((Tr A)²)^r ≤ C₂` at length `⌊Wu⌋`, then
`limsup_n E (Tr A^p)^r ≤ 3^r 2^{r-1} E H_p(μ_u)^r`. -/
theorem rhn_limsup_fracTrace_rpow_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p p₀ r : ℝ} (hp₀ : 0 < p₀)
    (hp₀p : p₀ < p) (hp1 : p < 1) (hr : 1 ≤ r) {C₀ C₂ : ℝ}
    (hH0 : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p₀ (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₀)
    (hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₂) :
    limsup (fun n => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw (φ n) b)
        atTop ≤ 3 ^ r * (2 ^ (r - 1) * ∫⁻ ω, limitFracTrace p (μ ω) ^ r ∂P) := by
  have hp : 0 < p := hp₀.trans hp₀p
  have hr0 : 0 < r := by linarith
  have h3top : (3 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr0.le (by simp)
  have h2top : (2 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  set L := limsup (fun n => ∫⁻ ω, ENNReal.ofReal
    (fracTrace p (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw (φ n) b) atTop
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
        (fracTrace p (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw W b ≤
        3 ^ r * (ENNReal.ofReal (2 * a ^ (p - p₀)) ^ r * ∫⁻ ω, ENNReal.ofReal
          (fracTrace p₀ (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ^ r ∂growthPathLaw W b +
        ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace) ∂growthPathLaw W b) +
        ENNReal.ofReal (B / (Kr - 1)) ^ r * ∫⁻ ω, ENNReal.ofReal
          ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ^ r ∂growthPathLaw W b) := by
      intro W
      have := isProbabilityMeasure_growthPathLaw W b
      set A := fun ω => nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω
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
            have hApsd := ns_nearClock_posSemidef b E W ⌊(W : ℝ) * u⌋₊ q hq ω
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
    have hvec : ∀ k : ℕ, ∀ ω : GrowthPath (φ k), (fun l : Fin (md + 1) =>
        wordValue b E (noTags (φ k)) (fun _ => q) (φ k) ⌊(φ k : ℝ) * u⌋₊ ω
          (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      fun k ω => funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    have hlimΨ := hfdd (md + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) Ψ
    simp_rw [hvec] at hlimΨ
    set X := ENNReal.ofReal (2 * a ^ (p - p₀)) ^ r * ENNReal.ofReal C₀
    set Y := ENNReal.ofReal (B / (Kr - 1)) ^ r * ENNReal.ofReal C₂
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω)) ^ r
          ∂growthPathLaw (φ k) b ≤
        3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
            ∂growthPathLaw (φ k) b) + Y) := by
      filter_upwards [hφ.tendsto_atTop.eventually hH0, hφ.tendsto_atTop.eventually hUI]
        with k h0 h2
      refine (hfin (φ k)).trans ?_
      exact mul_le_mul_right (add_le_add (add_le_add (mul_le_mul_right h0 _) le_rfl)
        (mul_le_mul_right h2 _)) _
    have hlim : Tendsto (fun k => 3 ^ r * (X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
        ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
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

end BlockBand.Endpoints
