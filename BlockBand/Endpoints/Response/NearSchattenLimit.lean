module

public import BlockBand.Endpoints.Response.NearSchattenDefs
public import BlockBand.Endpoints.Response.NearSchattenPassage
public import BlockBand.Endpoints.Response.NearSchattenGronwall

/-!
# Strict homogeneous Schatten decay in the critical limit

This file proves the `limitDecay` clause of `NearSchattenDecayContract` (`ns_limitDecay`) from the
finite fractional entrance and `NsRegularizedLimitGenerator`. The hypotheses are
`ClockFractionalEntranceContract` (only its `later` clause is used, at the smaller power
`p₀ = p/2`) and `NsRegularizedLimitGenerator`. The proof has four steps.

1. Entrance class: `later` bounds `E Tr A^{p₀}` on the travel interval `[s, s+t]`,
   uniformly for `W ≥ W₀`; the lower passage `ns_lintegral_limitFracTrace_le` transfers it to
   `E H_{p₀}(μ_u) ≤ C₀` for every `u` in the interval.
2. Regularization error (`ns_ennreal_regKernel_le`):
   `Tr f_ε(A) ≤ Σ λ²(λ+ε)^{p-2} + 2ε^{p-p₀} H_{p₀}`, hence `Y_ε ≤ X_ε + 2ε^{p-p₀}C₀`.
3. Gronwall (`ns_gronwall`) with the integrated regularized generator inequality:
   `E Tr f_ε(A_{s+t}) ≤ e^{-κt} E Tr f_ε(A_s) + 2ε^{p-p₀}C₀ ≤ e^{-κt} E H_p(s) + 2ε^{p-p₀}C₀`.
4. `ε ↓ 0`: Fatou in `x` (`f_ε(x)/x → x^{p-1}`, `= ∞` at the zero-eigenvalue
   dust) and in `ω` (a.e.-measurability of the clock integrals) gives `E H_p(s+t)` on the left.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-!
## Per-sample comparisons of the regularized traces
-/

section Sample

variable {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω} {μ : Measure ℝ}

/-- `Tr f_ε ≤ Σ λ²(λ+ε)^{p-2} + 2ε^{p-p₀} H_{p₀}` for any measure (kernel form of the power
regularization bound). -/
theorem ns_regTrace_le {p p₀ ε : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ < p) (hp1 : p < 1) (hε : 0 < ε)
    (μ : Measure ℝ) :
    nsRegTrace p ε μ ≤ nsDissTrace p ε μ +
      ENNReal.ofReal (2 * ε ^ (p - p₀)) * limitFracTrace p₀ μ := by
  unfold nsRegTrace nsDissTrace limitFracTrace
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left (f := fun x => ENNReal.ofReal (nsDissKernel p ε x))
      (ENNReal.measurable_ofReal.comp (ns_continuous_dissKernel hε).measurable)]
  exact lintegral_mono fun x => ns_ennreal_regKernel_le hp₀ hp₀p hp1 hε x

/-- `Tr f_ε ≤ H_p` (`(x+ε)^p - ε^p ≤ x^p`). -/
theorem ns_regTrace_le_limitFracTrace {p ε : ℝ} (hp : 0 < p) (hp1 : p < 1) (hε : 0 < ε)
    (μ : Measure ℝ) : nsRegTrace p ε μ ≤ limitFracTrace p μ := by
  unfold nsRegTrace limitFracTrace
  refine lintegral_mono fun x => ?_
  rcases le_or_gt x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.zero_rpow_of_neg (by linarith)]; exact le_top
  · rw [ENNReal.ofReal_rpow_of_pos hx]
    exact ENNReal.ofReal_le_ofReal (ns_regKernel_le_rpow hp.le hp1.le hε hx)

/-- `H_p(μ) ≤ liminf_n Tr f_{ε_n}` (Fatou in `x`, pointwise limit of the kernels). -/
theorem ns_limitFracTrace_le_liminf_regTrace {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (μ : Measure ℝ) :
    limitFracTrace p μ ≤ liminf (fun n => nsRegTrace p (nsEps n) μ) atTop := by
  unfold limitFracTrace nsRegTrace
  have hlim : ∀ x, ENNReal.ofReal x ^ (p - 1) =
      liminf (fun n => ENNReal.ofReal (nsRegKernel p (nsEps n) x)) atTop := fun x =>
    ((ns_tendsto_regKernel hp hp1 x).liminf_eq).symm
  simp_rw [hlim]
  exact lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
    (ns_continuous_regKernel (ns_eps_pos n)).measurable

/-- For a clock measure, `Tr f_ε = ofReal ∫ f_ε(x)/x dμ` (integrable bounded kernel). -/
theorem ns_regTrace_eq (h : IsClockMeasure Z u ω μ) {p ε : ℝ} (hp : 0 ≤ p) (hε : 0 < ε) :
    nsRegTrace p ε μ = ENNReal.ofReal (∫ x, nsRegKernel p ε x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (ns_clockMeasure_integrable h (ns_continuous_regKernel hε))
    (Eventually.of_forall fun x => ns_regKernel_nonneg hp hε x)]
  rfl

theorem ns_dissTrace_eq (h : IsClockMeasure Z u ω μ) {p ε : ℝ} (hε : 0 < ε) :
    nsDissTrace p ε μ = ENNReal.ofReal (∫ x, nsDissKernel p ε x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (ns_clockMeasure_integrable h (ns_continuous_dissKernel hε))
    (Eventually.of_forall fun x => ns_dissKernel_nonneg hε x)]
  rfl

end Sample

/-!
## a.e.-measurability in the sample
-/

theorem ns_aemeasurable_regTrace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p ε : ℝ} (hp : 0 ≤ p)
    (hε : 0 < ε) : AEMeasurable (fun ω => nsRegTrace p ε (μ ω)) P := by
  refine (ENNReal.measurable_ofReal.comp_aemeasurable
    (ns_aemeasurable_integral_clock hmeas hμ (ns_continuous_regKernel (p := p) hε))).congr ?_
  filter_upwards [hμ] with ω hω
  exact (ns_regTrace_eq hω hp hε).symm

theorem ns_aemeasurable_dissTrace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p ε : ℝ}
    (hε : 0 < ε) : AEMeasurable (fun ω => nsDissTrace p ε (μ ω)) P := by
  refine (ENNReal.measurable_ofReal.comp_aemeasurable
    (ns_aemeasurable_integral_clock hmeas hμ (ns_continuous_dissKernel (p := p) hε))).congr ?_
  filter_upwards [hμ] with ω hω
  exact (ns_dissTrace_eq hω hε).symm

/-!
## Bookkeeping
-/

theorem ns_transportD0_pos {b E : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) :
    0 < transportD0 b E := by
  unfold transportD0
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem ns_decayRate_nonneg {b E p : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp : 0 < p)
    (hp1 : p < 1) : 0 ≤ nsDecayRate b E p := by
  unfold nsDecayRate
  have := ns_transportD0_pos hb hE hE'
  have : 0 < 1 - p := by linarith
  positivity

theorem ns_travelLength_eq (W : ℕ) (t₁ R u : ℝ) :
    travelLength W t₁ R (u - (t₁ + R)) = ⌊(W : ℝ) * u⌋₊ := by
  unfold travelLength; congr 2; ring

theorem ns_isUnitSource_nonneg {t₁ R : ℝ} {q : ℝ → ℝ} (hq : IsUnitSource t₁ R q) :
    ∀ x, 0 ≤ q x := hq.2.2.2.1.1

/-!
## `limitDecay`
-/

/-- **Decay at critical limits**: the `limitDecay` field of `NearSchattenDecayContract`, from
`ClockFractionalEntranceContract` and `NsRegularizedLimitGenerator`: for every critical limit of the clock of a unit source (joint
critical word limit with a.s. clock measures), every travel time `s > 0` after the last
injection and every `t ≥ 0`, `E H_p(s+t) ≤ e^{-Dp(1-p)t/2} E H_p(s)`.
-/
theorem ns_limitDecay (hEnt : ClockFractionalEntranceContract)
    (hRG : NsRegularizedLimitGenerator) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∀ (t₁ R : ℝ) (q : ℝ → ℝ), IsUnitSource t₁ R q →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ClockWord → ℝ → Ω → ℂ),
      IsWordLimit b E noTags (fun _ => q) (t₁ + R) P Z →
    ∀ μ : ℝ → Ω → Measure ℝ, (∀ t : ℝ, t₁ + R ≤ t → ∀ᵐ ω ∂P, IsClockMeasure Z t ω (μ t ω)) →
    ∀ s t : ℝ, 0 < s → 0 ≤ t →
      ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s + t) ω) ∂P ≤
        ENNReal.ofReal (Real.exp (-(transportD0 b E * p * (1 - p) * t / 2))) *
          ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s) ω) ∂P := by
  intro b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hWL μ hμ s t hs ht
  have hP := hWL.prob
  set t₀ := t₁ + R with ht₀
  set u₀ := t₀ + s with hu₀
  set T' := u₀ + t with hT'
  set p₀ := p / 2 with hp₀
  have hp₀0 : 0 < p₀ := by positivity
  have hp₀p : p₀ < p := by linarith
  have hp₀1 : p₀ < 1 := by linarith
  have hqnn := ns_isUnitSource_nonneg hq
  have hmeas : ∀ u, t₀ ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) := fun u hu k hk =>
    hWL.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  obtain ⟨φ, hφ, hfdd⟩ := ns_fdd_of_isWordLimit hWL
  -- the entrance class: `E H_{p₀}(μ_u) ≤ C₀` on `[u₀, T']`
  obtain ⟨C₀, hC₀⟩ := hEnt.later b hb hb' E hE hE' p₀ hp₀0 hp₀1 s (s + t) hs (by linarith)
  obtain ⟨W₀, hW₀⟩ := hC₀ t₁ R q hq
  have hH0 : ∀ u ∈ Icc u₀ T', ∫⁻ ω, limitFracTrace p₀ (μ u ω) ∂P ≤ ENNReal.ofReal C₀ := by
    intro u hu
    have htu : t₀ ≤ u := by linarith [hu.1]
    refine ns_lintegral_limitFracTrace_le hqnn htu (hmeas u htu) hφ hfdd (hμ u htu) hp₀0 hp₀1
      (eventually_atTop.2 ⟨W₀, fun W hW => ?_⟩)
    have h := hW₀ W hW (u - t₀) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    unfold clockFracMoment at h
    rwa [ns_travelLength_eq] at h
  -- Gronwall at each `ε_n`
  set κ := nsDecayRate b E p with hκ
  have hκ0 : 0 ≤ κ := ns_decayRate_nonneg hb hE hE' hp hp1
  set c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * nsEps n ^ (p - p₀)) * ENNReal.ofReal C₀
    with hc
  have hgron : ∀ n, ∫⁻ ω, nsRegTrace p (nsEps n) (μ T' ω) ∂P ≤
      ENNReal.ofReal (Real.exp (-(κ * (T' - u₀)))) *
        ∫⁻ ω, nsRegTrace p (nsEps n) (μ u₀ ω) ∂P + c n := by
    intro n
    have hε := ns_eps_pos n
    refine ns_gronwall (Y := fun u => ∫⁻ ω, nsRegTrace p (nsEps n) (μ u ω) ∂P)
      (X := fun u => ∫⁻ ω, nsDissTrace p (nsEps n) (μ u ω) ∂P) (a := u₀) (b := T') (c := c n)
      (by linarith) hκ0 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ?_ ?_
    · intro u₁ u₂ h1 h2 _
      exact hRG b hb hb' E hE hE' p hp hp1 t₁ R q hq Ω _ P Z hWL μ hμ (nsEps n) hε u₁ u₂
        (by linarith) h2
    · intro u hu
      have htu : t₀ ≤ u := by linarith [hu.1]
      calc ∫⁻ ω, nsRegTrace p (nsEps n) (μ u ω) ∂P
          ≤ ∫⁻ ω, (nsDissTrace p (nsEps n) (μ u ω) +
              ENNReal.ofReal (2 * nsEps n ^ (p - p₀)) * limitFracTrace p₀ (μ u ω)) ∂P :=
            lintegral_mono fun ω => ns_regTrace_le hp₀0 hp₀p hp1 hε _
        _ = ∫⁻ ω, nsDissTrace p (nsEps n) (μ u ω) ∂P +
              ENNReal.ofReal (2 * nsEps n ^ (p - p₀)) * ∫⁻ ω, limitFracTrace p₀ (μ u ω) ∂P := by
            rw [lintegral_add_left' (ns_aemeasurable_dissTrace (hmeas u htu) (hμ u htu) hε),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := by
            gcongr
            exact mul_le_mul_right (hH0 u hu) _
  -- `ε ↓ 0`
  have hTu : T' - u₀ = t := by rw [hT']; ring
  have hexp : Real.exp (-(κ * (T' - u₀))) = Real.exp (-(transportD0 b E * p * (1 - p) * t / 2)) := by
    rw [hTu, hκ, nsDecayRate]; ring_nf
  rw [hexp] at hgron
  set e := ENNReal.ofReal (Real.exp (-(transportD0 b E * p * (1 - p) * t / 2)))
  set H := ∫⁻ ω, limitFracTrace p (μ u₀ ω) ∂P
  have hup : ∀ n, ∫⁻ ω, nsRegTrace p (nsEps n) (μ T' ω) ∂P ≤ e * H + c n := fun n =>
    (hgron n).trans (by
      gcongr
      exact lintegral_mono fun ω => ns_regTrace_le_limitFracTrace hp hp1 (ns_eps_pos n) _)
  have hT0 : t₀ ≤ T' := by linarith
  have hlimc : Tendsto (fun n => e * H + c n) atTop (𝓝 (e * H)) := by
    have h := (tendsto_const_nhds (x := e * H)).add
      (ns_tendsto_regError hp₀p (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top)
    rw [add_zero] at h
    exact h
  calc ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s + t) ω) ∂P
      ≤ ∫⁻ ω, liminf (fun n => nsRegTrace p (nsEps n) (μ T' ω)) atTop ∂P :=
        lintegral_mono fun ω => ns_limitFracTrace_le_liminf_regTrace hp hp1 _
    _ ≤ liminf (fun n => ∫⁻ ω, nsRegTrace p (nsEps n) (μ T' ω) ∂P) atTop :=
        lintegral_liminf_le' fun n =>
          ns_aemeasurable_regTrace (hmeas T' hT0) (hμ T' hT0) hp.le (ns_eps_pos n)
    _ ≤ liminf (fun n => e * H + c n) atTop := liminf_le_liminf (Eventually.of_forall hup)
    _ = e * H := hlimc.liminf_eq

end BlockBand.Endpoints
