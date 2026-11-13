module

public import BlockBand.Endpoints.Response.NearSchattenClock

/-!
# Passing clock integrals to critical limits (lower direction)

Along the subsequence `φ` of a joint critical word limit `(P, Z)` of the one-source family,
the clock measures `μ_u` at a time `u ≥ t₀` inherit finite-width bounds in the lower
(Fatou) direction:

* `ns_lintegral_le_of_eventually`: for a continuous `c ≥ 0`, if eventually
  `E Σ_i λ_i c(λ_i) ≤ C` at width `W` and length `⌊Wu⌋`, then `E ∫ c dμ_u ≤ C`.
  Mechanism: the bounded continuous test
  `Ψ_K(z) = min(K, max(0, Σ_l π_l Re z_l - δ_K Re z_0)) · χ_K(Re z_0)` of the word values
  `z_l = Tr (QP)^{l+1}` (`π` a Weierstrass approximation of `c` on `[0, K]` within `δ_K`,
  `χ_K` a cutoff of `Tr A` at `K`) is pointwise `≤ Σ_i λ_i c(λ_i)` at finite width; the `fdd`
  clause passes `E Ψ_K` to the limit; on the limit side `Ψ_K(Z) → ∫ c dμ_u` a.s. (support of
  `μ_u` in `[0, Re Z_{QP}]`, moments `Re Z_{(QP)^k}`), and Fatou in `K` concludes.
* `ns_aemeasurable_integral_clock`: `ω ↦ ∫ c dμ_u(ω)` is a.e.-measurable (a.e. limit of the
  measurable polynomial moments), although the family `μ` is arbitrary.
* `ns_lintegral_limitFracTrace_le`: the same for `H_r = limitFracTrace r` (`0 < r < 1`), from
  eventual bounds on `E Tr A^r`, through the cut kernels `(max x ε_m)^{r-1} ↑ x^{r-1}`.
No moment problem is solved: `μ_u` is given (hypothesis `IsClockMeasure`, a.s.).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Polynomial Filter Topology Set
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- `2 ε_n^{p-p₀} C₀ → 0`. -/
theorem ns_tendsto_regError {p p₀ : ℝ} (hp₀p : p₀ < p) (C₀ : ℝ≥0∞) (hC₀ : C₀ ≠ ⊤) :
    Tendsto (fun n => ENNReal.ofReal (2 * nsEps n ^ (p - p₀)) * C₀) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => nsEps n ^ (p - p₀)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 (p - p₀) (Or.inr (by linarith))).tendsto).comp
      (tendsto_nhdsWithin_iff.1 ns_tendsto_eps).1
    rw [Real.zero_rpow (by linarith)] at this
    exact this
  have h2 : Tendsto (fun n => ENNReal.ofReal (2 * nsEps n ^ (p - p₀))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (by simpa using h1.const_mul 2)
  simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hC₀)

/-!
## fdd convergence along a fixed subsequence
-/

/-- The `fdd` clause of `IsWordLimit` (one-source family, no tags) along a fixed sequence `φ`. -/
def NsFddAlong (b E : ℝ) (q : ℝ → ℝ) (t₀ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ClockWord → ℝ → Ω → ℂ) (φ : ℕ → ℕ) : Prop :=
  ∀ (m : ℕ) (ws : Fin m → ClockWord) (ts : Fin m → ℝ),
    (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ ts l) → ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
      Tendsto (fun n => ∫ ω, Ψ (fun l =>
          wordValue b E (noTags (φ n)) (fun _ => q) (φ n) ⌊(φ n : ℝ) * ts l⌋₊ ω (ws l))
          ∂growthPathLaw (φ n) b) atTop (𝓝 (∫ ω, Ψ (fun l => Z (ws l) (ts l) ω) ∂P))

theorem ns_fdd_of_isWordLimit {b E : ℝ} {q : ℝ → ℝ} {t₀ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ClockWord → ℝ → Ω → ℂ}
    (h : IsWordLimit b E noTags (fun _ => q) t₀ P Z) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ NsFddAlong b E q t₀ P Z φ :=
  h.fdd

theorem ns_isOrdinaryWord_clockWord {k : ℕ} (hk : 1 ≤ k) : IsOrdinaryWord (clockWord k) := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold clockWord
    intro h
    have := congrArg List.length h
    simp at this
    omega
  · unfold clockWord at hx
    rw [(List.eq_of_mem_replicate hx)]
    exact Or.inr rfl

/-!
## The bounded continuous tests
-/

/-- Continuous cutoff: `1` on `(-∞, K-1]`, `0` on `[K, ∞)`. -/
def nsCutoff (K y : ℝ) : ℝ := max 0 (min 1 (K - y))

theorem ns_continuous_cutoff (K : ℝ) : Continuous (nsCutoff K) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_id))

theorem ns_cutoff_nonneg (K y : ℝ) : 0 ≤ nsCutoff K y := le_max_left _ _

theorem ns_cutoff_le_one (K y : ℝ) : nsCutoff K y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ns_cutoff_eq_zero {K y : ℝ} (h : K ≤ y) : nsCutoff K y = 0 :=
  max_eq_left ((min_le_right _ _).trans (by linarith))

theorem ns_cutoff_eq_one {K y : ℝ} (h : y ≤ K - 1) : nsCutoff K y = 1 := by
  unfold nsCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- The test `min(M, max(0, Σ_l π_l Re z_l + σ δ Re z_0)) · χ_K(Re z_0)`. -/
def nsTestFun (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (z : Fin (m + 1) → ℂ) : ℝ :=
  min M (max 0 (nsPolyMoment π m z + σ * δ * (z 0).re)) * nsCutoff K (z 0).re

theorem ns_continuous_testFun (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) :
    Continuous (nsTestFun π m σ δ K M) := by
  unfold nsTestFun
  have h0 : Continuous fun z : Fin (m + 1) → ℂ => (z 0).re :=
    Complex.continuous_re.comp (continuous_apply 0)
  exact (continuous_const.min (continuous_const.max
    ((ns_continuous_polyMoment π m).add (continuous_const.mul h0)))).mul
    ((ns_continuous_cutoff K).comp h0)

theorem ns_testFun_nonneg (π : ℝ[X]) (m : ℕ) (σ δ K : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (z : Fin (m + 1) → ℂ) : 0 ≤ nsTestFun π m σ δ K M z :=
  mul_nonneg (le_min hM (le_max_left _ _)) (ns_cutoff_nonneg _ _)

theorem ns_testFun_le (π : ℝ[X]) (m : ℕ) (σ δ K : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (z : Fin (m + 1) → ℂ) : nsTestFun π m σ δ K M z ≤ M := by
  unfold nsTestFun
  have h1 := ns_cutoff_le_one K (z 0).re
  have h2 := ns_cutoff_nonneg K (z 0).re
  have h3 : min M (max 0 (nsPolyMoment π m z + σ * δ * (z 0).re)) ≤ M := min_le_left _ _
  have h4 : 0 ≤ min M (max 0 (nsPolyMoment π m z + σ * δ * (z 0).re)) :=
    le_min hM (le_max_left _ _)
  nlinarith

/-- The test as a bounded continuous function (`M ≥ 0`). -/
def nsTestBCF (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) :
    BoundedContinuousFunction (Fin (m + 1) → ℂ) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨nsTestFun π m σ δ K M, ns_continuous_testFun π m σ δ K M⟩ M
    fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := ns_testFun_nonneg π m σ δ K hM x
      have := ns_testFun_nonneg π m σ δ K hM y
      have := ns_testFun_le π m σ δ K hM x
      have := ns_testFun_le π m σ δ K hM y
      rw [abs_le]; constructor <;> linarith

theorem ns_testBCF_apply (π : ℝ[X]) (m : ℕ) (σ δ K M : ℝ) (hM : 0 ≤ M) (z : Fin (m + 1) → ℂ) :
    nsTestBCF π m σ δ K M hM z = nsTestFun π m σ δ K M z := rfl

/-!
## Finite-width side
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lower test at finite width.** If `|π - c| ≤ δ` on `[0, K]` (`deg π ≤ m`, `c ≥ 0` on
`[0,∞)`), then the lower test of the moments of `A ⪰ 0` is at most `Σ_i λ_i c(λ_i)`. -/
theorem ns_testFun_lower_le (π : ℝ[X]) {m : ℕ} (hm : π.natDegree ≤ m) {c : ℝ → ℝ}
    (hc0 : ∀ x, 0 ≤ x → 0 ≤ c x) {δ K M : ℝ} (hM : 0 ≤ M)
    (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    nsTestFun π m (-1) δ K M (fun l => (A ^ ((l : ℕ) + 1)).trace) ≤ nsClockSum c A := by
  have hS := ns_clockSum_nonneg hc0 hA
  have h0 : ((fun l : Fin (m + 1) => (A ^ ((l : ℕ) + 1)).trace) 0).re = A.trace.re := by simp
  unfold nsTestFun
  rw [h0]
  rcases le_or_gt K A.trace.re with hK | hK
  · rw [ns_cutoff_eq_zero hK, mul_zero]; exact hS
  · have happ' := ns_clockSum_sub_poly_le hA hK.le happ
    rw [ns_polyMoment_trace hA.isHermitian π hm]
    have hX : max 0 (∑ i, hA.isHermitian.eigenvalues i * π.eval (hA.isHermitian.eigenvalues i) +
        -1 * δ * A.trace.re) ≤ nsClockSum c A := by
      refine max_le hS ?_
      have := (abs_le.1 happ').1
      linarith
    have h1 := ns_cutoff_le_one K A.trace.re
    have h2 := ns_cutoff_nonneg K A.trace.re
    have h3 := min_le_right M (max 0 (∑ i, hA.isHermitian.eigenvalues i *
      π.eval (hA.isHermitian.eigenvalues i) + -1 * δ * A.trace.re))
    have h4 : 0 ≤ min M (max 0 (∑ i, hA.isHermitian.eigenvalues i *
        π.eval (hA.isHermitian.eigenvalues i) + -1 * δ * A.trace.re)) :=
      le_min hM (le_max_left _ _)
    nlinarith

theorem ns_nearClock_posSemidef (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (ω : GrowthPath W) : (nearClock b E W j q ω).PosSemidef := by
  unfold nearClock
  rw [ns_portBlock_eq]
  exact (intervalSource_posSemidef b E W j q hq ω).conjTranspose_mul_mul_same _

/-!
## Limit side
-/

section Limit

variable {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω} {μ : Measure ℝ}

/-- The vector of clock-word values `(Z_{(QP)^{l+1}}(u))_{l ≤ m}`. -/
def nsClockVec (Z : ClockWord → ℝ → Ω → ℂ) (m : ℕ) (u : ℝ) (ω : Ω) : Fin (m + 1) → ℂ :=
  fun l => Z (clockWord ((l : ℕ) + 1)) u ω

/-- **Lower test on the limit side.** For a clock measure with `Re Z_{QP} ≤ K - 1` and
`|π - c| ≤ δ` on `[0, K]`: `min(M, ∫ c dμ - 2δ Re Z_{QP}) ≤ Ψ(Z)`. -/
theorem ns_testFun_lower_ge (h : IsClockMeasure Z u ω μ) {c : ℝ → ℝ} (hc : Continuous c)
    (π : ℝ[X]) {m : ℕ} (hm : π.natDegree ≤ m) {δ K M : ℝ}
    (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ) (hK : (Z (clockWord 1) u ω).re ≤ K - 1) :
    min M (∫ x, c x ∂μ - 2 * δ * (Z (clockWord 1) u ω).re) ≤
      nsTestFun π m (-1) δ K M (nsClockVec Z m u ω) := by
  have h0 : (nsClockVec Z m u ω 0).re = (Z (clockWord 1) u ω).re := rfl
  unfold nsTestFun
  rw [h0, ns_cutoff_eq_one hK, mul_one]
  have hI := ns_integral_poly_clockMeasure h π hm
  have happ' := ns_integral_sub_poly_le h hc (by linarith) happ
  have : ∫ x, c x ∂μ - 2 * δ * (Z (clockWord 1) u ω).re ≤
      nsPolyMoment π m (nsClockVec Z m u ω) + -1 * δ * (Z (clockWord 1) u ω).re := by
    have := (abs_le.1 happ').2
    unfold nsClockVec
    rw [← hI]
    linarith
  exact min_le_min le_rfl (this.trans (le_max_right _ _))

theorem ns_measurable_clockVec [MeasurableSpace Ω]
    (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u)) (m : ℕ) :
    Measurable (nsClockVec Z m u) :=
  measurable_pi_iff.mpr fun l => hmeas _ (by omega)

end Limit

/-!
## Integrals of bounded tests
-/

theorem ns_integral_le_toReal {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (h : ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≤ C) : ∫ x, f x ∂ν ≤ C.toReal := by
  by_cases hi : Integrable f ν
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hi.aestronglyMeasurable]
    exact ENNReal.toReal_mono hC
      ((lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hfg x)).trans h)
  · rw [integral_undef hi]; exact ENNReal.toReal_nonneg

/-- Weierstrass approximants of a continuous `c` on `[0, K+2]` within `1/(K+1)`. -/
theorem ns_exists_poly (c : ℝ → ℝ) (hc : Continuous c) (K : ℕ) :
    ∃ π : ℝ[X], ∀ x ∈ Icc (0 : ℝ) ((K : ℝ) + 2), |π.eval x - c x| ≤ 1 / ((K : ℝ) + 1) := by
  obtain ⟨π, hπ⟩ := exists_polynomial_near_of_continuousOn 0 ((K : ℝ) + 2) c hc.continuousOn
    (1 / ((K : ℝ) + 1)) (by positivity)
  exact ⟨π, fun x hx => (hπ x hx).le⟩

/-- The chosen approximant. -/
def nsPoly (c : ℝ → ℝ) (hc : Continuous c) (K : ℕ) : ℝ[X] := (ns_exists_poly c hc K).choose

theorem ns_poly_spec (c : ℝ → ℝ) (hc : Continuous c) (K : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) ((K : ℝ) + 2), |(nsPoly c hc K).eval x - c x| ≤ 1 / ((K : ℝ) + 1) :=
  (ns_exists_poly c hc K).choose_spec

/-!
## The lower passage
-/

/-- **Lower passage of clock integrals to a critical limit.** Along the subsequence of a joint
critical word limit (one-source family, source `q ≥ 0`), at a time `u ≥ t₀` with a.s. clock
measures `μ_u`: if eventually `E Σ_i λ_i c(λ_i) ≤ C` for the near clock at length `⌊Wu⌋`
(`c ≥ 0` continuous), then `E ∫ c dμ_u ≤ C`. -/
theorem ns_lintegral_le_of_eventually {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω))
    {c : ℝ → ℝ} (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) {C : ℝ≥0∞}
    (hbound : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (nsClockSum c (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b ≤ C) :
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
  -- Step A: the limit expectations of the tests are bounded by `C`
  have hA : ∀ K, ∫ ω, Ψ K (nsClockVec Z (m K) u ω) ∂P ≤ C.toReal := by
    intro K
    have hlim := hfdd (m K + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) (Ψ K)
    refine le_of_tendsto hlim ((hφ.tendsto_atTop.eventually hbound).mono fun k hk => ?_)
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
  -- Step B: the same in `ℝ≥0∞`
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
  -- Step C: Fatou in `K`
  have hC' : ∫⁻ ω, liminf (fun K => ENNReal.ofReal (Ψ K (nsClockVec Z (m K) u ω))) atTop ∂P ≤ C :=
    (lintegral_liminf_le fun K => ENNReal.measurable_ofReal.comp (hmeasV K)).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hB))
  -- Step D: a.s. the tests converge up to `∫ c dμ_u`
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

/-!
## Measurability of clock integrals
-/

/-- **`ω ↦ ∫ c dμ_u(ω)` is a.e.-measurable** for continuous `c` and a.s. clock measures: it is the
a.e. limit of the measurable polynomial moments `Σ_l π^K_l Re Z_{(QP)^{l+1}}(u)`. -/
theorem ns_aemeasurable_integral_clock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {c : ℝ → ℝ}
    (hc : Continuous c) : AEMeasurable (fun ω => ∫ x, c x ∂μ ω) P := by
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun K ω =>
      nsPolyMoment (nsPoly c hc K) (nsPoly c hc K).natDegree
        (nsClockVec Z (nsPoly c hc K).natDegree u ω))
    (fun K => ((ns_continuous_polyMoment _ _).measurable.comp
      (ns_measurable_clockVec hmeas _)).aemeasurable) ?_
  filter_upwards [hμ] with ω hω
  set M := (Z (clockWord 1) u ω).re
  have hKr : Tendsto (fun K : ℕ => (K : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ K : ℕ in atTop, ‖nsPolyMoment (nsPoly c hc K) (nsPoly c hc K).natDegree
      (nsClockVec Z (nsPoly c hc K).natDegree u ω) - ∫ x, c x ∂μ ω‖ ≤ 1 / ((K : ℝ) + 1) * M := by
    filter_upwards [hKr.eventually_ge_atTop M] with K hK
    have h := ns_integral_sub_poly_le hω hc hK (ns_poly_spec c hc K)
    rw [ns_integral_poly_clockMeasure hω _ le_rfl] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have h0 : Tendsto (fun K : ℕ => 1 / ((K : ℝ) + 1) * M) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const M
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' hev h0)

/-!
## Lower passage of the fractional trace
-/

variable {n : Type*} [Fintype n] [DecidableEq n] in
/-- `Σ_i λ_i (max λ_i a)^{r-1} ≤ Tr A^r` (`A ⪰ 0`, `r > 0`, `a > 0`). -/
theorem ns_clockSum_cutKernel_le {A : Matrix n n ℂ} (hA : A.PosSemidef) {a r : ℝ} (hr : 0 < r)
    (hr1 : r < 1) : nsClockSum (nsCutKernel a (r - 1)) A ≤ fracTrace r A := by
  rw [ns_clockSum_eq _ hA.isHermitian, fracTrace_eq_sum_eigenvalues_of_posSemidef hA]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := hA.eigenvalues_nonneg i
  rcases h0.eq_or_lt with h | h
  · rw [← h, zero_mul, Real.zero_rpow hr.ne']
  · have := ns_cutKernel_le_rpow (a := a) h (by linarith : r - 1 ≤ 0)
    calc hA.isHermitian.eigenvalues i * nsCutKernel a (r - 1) (hA.isHermitian.eigenvalues i)
        ≤ hA.isHermitian.eigenvalues i * hA.isHermitian.eigenvalues i ^ (r - 1) := by gcongr
      _ = hA.isHermitian.eigenvalues i ^ r := by
          rw [mul_comm, ← Real.rpow_add_one h.ne']; ring_nf

/-- In `ℝ≥0∞`, `H_r(μ) ≤ liminf_m ∫ (max x ε_m)^{r-1} dμ` for a clock measure (`r < 1`). -/
theorem ns_limitFracTrace_le_liminf {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω}
    {μ : Measure ℝ} (h : IsClockMeasure Z u ω μ) {r : ℝ} (hr1 : r < 1) :
    limitFracTrace r μ ≤
      liminf (fun m => ENNReal.ofReal (∫ x, nsCutKernel (nsEps m) (r - 1) x ∂μ)) atTop := by
  unfold limitFracTrace
  have hlim : ∀ x, ENNReal.ofReal x ^ (r - 1) =
      liminf (fun m => ENNReal.ofReal (nsCutKernel (nsEps m) (r - 1) x)) atTop := fun x =>
    ((ns_tendsto_cutKernel (by linarith) x).liminf_eq).symm
  simp_rw [hlim]
  refine (lintegral_liminf_le fun m => ENNReal.measurable_ofReal.comp
    (ns_continuous_cutKernel (ns_eps_pos m)).measurable).trans (le_of_eq ?_)
  congr 1
  funext m
  rw [ofReal_integral_eq_lintegral_ofReal
    (ns_clockMeasure_integrable h (ns_continuous_cutKernel (ns_eps_pos m)))
    (Eventually.of_forall fun x => ns_cutKernel_nonneg (ns_eps_pos m) x)]
  rfl

/-- **Lower passage of `H_r`** (`0 < r < 1`): along the subsequence of a critical word limit, at a
time `u ≥ t₀` with a.s. clock measures, if eventually `E Tr A^r ≤ C` at length `⌊Wu⌋`, then
`E H_r(μ_u) ≤ C` (`H_r = limitFracTrace r`). -/
theorem ns_lintegral_limitFracTrace_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1) {C : ℝ≥0∞}
    (hbound : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace r (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b ≤ C) :
    ∫⁻ ω, limitFracTrace r (μ ω) ∂P ≤ C := by
  have hm : ∀ m, ∫⁻ ω, ENNReal.ofReal (∫ x, nsCutKernel (nsEps m) (r - 1) x ∂μ ω) ∂P ≤ C := by
    intro m
    refine ns_lintegral_le_of_eventually hq hu hmeas hφ hfdd hμ
      (ns_continuous_cutKernel (ns_eps_pos m)) (ns_cutKernel_nonneg (ns_eps_pos m)) ?_
    filter_upwards [hbound] with W hW
    refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) hW
    exact ns_clockSum_cutKernel_le (ns_nearClock_posSemidef b E _ _ q hq ω) hr hr1
  have hae : ∀ m, AEMeasurable
      (fun ω => ENNReal.ofReal (∫ x, nsCutKernel (nsEps m) (r - 1) x ∂μ ω)) P := fun m =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (ns_aemeasurable_integral_clock hmeas hμ (ns_continuous_cutKernel (ns_eps_pos m)))
  calc ∫⁻ ω, limitFracTrace r (μ ω) ∂P
      ≤ ∫⁻ ω, liminf (fun m => ENNReal.ofReal
          (∫ x, nsCutKernel (nsEps m) (r - 1) x ∂μ ω)) atTop ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hμ] with ω hω
        exact ns_limitFracTrace_le_liminf hω hr1
    _ ≤ liminf (fun m => ∫⁻ ω, ENNReal.ofReal
          (∫ x, nsCutKernel (nsEps m) (r - 1) x ∂μ ω) ∂P) atTop := lintegral_liminf_le' hae
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall hm)

end BlockBand.Endpoints
