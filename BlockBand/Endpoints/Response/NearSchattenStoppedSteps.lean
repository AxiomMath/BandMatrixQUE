module

public import BlockBand.Endpoints.Response.NearSchattenStoppedTelescope

/-!
# One-step inputs of the stopped energy inequality

* `nss_integrable_polyValue_clockPoly`: `Φ_π(A_j)` is integrable once `E (Tr Q_j)^{N+1} < ∞`
  (`|Σ_i π(λ_i)| ≤ Σ_r|a_r| (1 + (Tr Q)^{N+1})`, `Tr A ≤ Tr Q`).
* `nss_preStop_abstract`, `nss_preStop_key`: the integrability and truncation bounds for one step
  before the stop.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Integrability of the clock polynomial
-/

theorem nss_sum_pow_le {ι : Type*} [Fintype ι] {lam : ι → ℝ} (h0 : ∀ i, 0 ≤ lam i) (k : ℕ) :
    ∑ i, lam i ^ (k + 1) ≤ (∑ i, lam i) ^ (k + 1) := by
  calc ∑ i, lam i ^ (k + 1) = ∑ i, lam i * lam i ^ k := by
        refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i, lam i * (∑ i, lam i) ^ k := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h0 i)
          (Finset.single_le_sum (f := lam) (fun j _ => h0 j) (Finset.mem_univ i)) k) (h0 i)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem nss_abs_sum_polyFun_le {ι : Type*} [Fintype ι] (a : ℕ → ℝ) (N : ℕ) {lam : ι → ℝ}
    (h0 : ∀ i, 0 ≤ lam i) {T : ℝ} (hT : ∑ i, lam i ≤ T) :
    |∑ i, nsfPolyFun a N (lam i)| ≤ (∑ r ∈ range N, |a r|) * (1 + T ^ (N + 1)) := by
  have hS0 : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => h0 i
  have hT0 : 0 ≤ T := hS0.trans hT
  have e : ∑ i, nsfPolyFun a N (lam i) = ∑ r ∈ range N, a r * ∑ i, lam i ^ (r + 1) := by
    unfold nsfPolyFun
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [e, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (h0 i) _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (nss_sum_pow_le h0 r).trans ((pow_le_pow_left₀ hS0 hT _).trans ?_)
  rcases le_or_gt T 1 with h | h
  · have := pow_le_one₀ hT0 h (n := r + 1)
    have : 0 ≤ T ^ (N + 1) := pow_nonneg hT0 _
    linarith
  · have := pow_le_pow_right₀ h.le (show r + 1 ≤ N + 1 by have := Finset.mem_range.1 hr; omega)
    linarith

/-- `Φ_π(A_j)` is integrable when `E (Tr Q_j)^{N+1} < ∞`. -/
theorem nss_integrable_polyValue_clockPoly (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (κ : Fin 0 → ℕ) (a : ℕ → ℝ) (N : ℕ) {j : ℕ}
    (hmom : ∫⁻ ω, ‖(intervalSource b E W j q ω).trace.re‖ₑ ^ (((N + 1 : ℕ) : ℝ))
      ∂growthPathLaw W b ≠ ⊤) :
    Integrable (fun ω => polyValue b E κ (fun _ => q) W j ω (nsfClockPoly a N))
      (growthPathLaw W b) := by
  set x : GrowthPath W → ℝ := fun ω => (intervalSource b E W j q ω).trace.re
  have hxm : Measurable x := Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (nss_measurable_intervalSource b E W j q))
  have hpow : Integrable (fun ω => x ω ^ (N + 1)) (growthPathLaw W b) := by
    refine ⟨(hxm.pow_const _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : (fun ω => ‖x ω ^ (N + 1)‖ₑ) = fun ω => ‖x ω‖ₑ ^ (((N + 1 : ℕ) : ℝ)) := by
      funext ω; rw [enorm_pow, ENNReal.rpow_natCast]
    rw [this]
    exact lt_top_iff_ne_top.2 hmom
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  refine (((integrable_const 1).add hpow).const_mul (∑ r ∈ range N, |a r|)).mono'
    (nss_measurable_polyValue b E κ _ W j _).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  rw [nsf_polyValue_clockPoly_path b E hq W j ω κ a N, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  exact nss_abs_sum_polyFun_le a N (fun i => hpsd.eigenvalues_nonneg i)
    (hsum.trans_le (trace_nearClock_le b E W j q hq ω).2)

/-!
## The stopped integrand before the stop
-/

/-- One pre-stop step, abstract form. If on `A`, a.s., `‖G‖ ≤ C₀ + c` and
`0 ≤ -Re G + c ≤ C₀ + 2c`, then `1_A G` is integrable and `E[1_A(-Re G)⁺] ≤ r` with
`0 ≤ r ≤ -E[1_A Re G] + c` and `r ≤ C₀ + 2c`. -/
theorem nss_preStop_abstract {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) {G : Ω → ℂ} (hGm : Measurable G)
    {c C₀ : ℝ} (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀)
    (hkey : ∀ᵐ ω ∂μ, ω ∈ A → ‖G ω‖ ≤ C₀ + c ∧ 0 ≤ -(G ω).re + c ∧ -(G ω).re + c ≤ C₀ + 2 * c) :
    Integrable (A.indicator G) μ ∧ ∃ r : ℝ, 0 ≤ r ∧
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (-(G ω).re)) ω ∂μ ≤ ENNReal.ofReal r ∧
      r ≤ -∫ ω, A.indicator (fun ω => (G ω).re) ω ∂μ + c ∧ r ≤ C₀ + 2 * c := by
  have hI : Integrable (A.indicator G) μ := by
    refine (integrable_const (C₀ + c)).mono' (hGm.indicator hA).aestronglyMeasurable ?_
    filter_upwards [hkey] with ω h
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]; exact (h hω).1
    · rw [Set.indicator_of_notMem hω, norm_zero]; linarith
  have hIr : Integrable (A.indicator fun ω => -(G ω).re) μ := by
    refine hI.re.neg.congr (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  set h := A.indicator (fun ω => -(G ω).re + c)
  have hhI : Integrable h μ := by
    refine (hIr.add ((integrable_const c).indicator hA)).congr (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ A
    · simp [h, Set.indicator_of_mem hω]
    · simp [h, Set.indicator_of_notMem hω]
  have hh0 : 0 ≤ᵐ[μ] h := by
    filter_upwards [hkey] with ω hk
    by_cases hω : ω ∈ A
    · simp only [h, Set.indicator_of_mem hω, Pi.zero_apply]; exact (hk hω).2.1
    · simp [h, Set.indicator_of_notMem hω]
  refine ⟨hI, ∫ ω, h ω ∂μ, integral_nonneg_of_ae hh0, ?_, ?_, ?_⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hhI hh0]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ A
    · simp only [h, Set.indicator_of_mem hω]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · simp [h, Set.indicator_of_notMem hω]
  · have hle : ∫ ω, h ω ∂μ ≤ ∫ ω, (A.indicator (fun ω => -(G ω).re) ω + c) ∂μ := by
      refine integral_mono hhI (hIr.add (integrable_const c)) fun ω => ?_
      by_cases hω : ω ∈ A
      · simp [h, Set.indicator_of_mem hω]
      · simp [h, Set.indicator_of_notMem hω, hc]
    rw [integral_add hIr (integrable_const c), integral_const, probReal_univ, one_smul] at hle
    have hneg : ∫ ω, A.indicator (fun ω => -(G ω).re) ω ∂μ =
        -∫ ω, A.indicator (fun ω => (G ω).re) ω ∂μ := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [hneg] at hle
    exact hle
  · have hle : ∫ ω, h ω ∂μ ≤ ∫ _ω, (C₀ + 2 * c) ∂μ := by
      refine integral_mono_ae hhI (integrable_const _) ?_
      filter_upwards [hkey] with ω hk
      by_cases hω : ω ∈ A
      · simp only [h, Set.indicator_of_mem hω]; exact (hk hω).2.2
      · simp only [h, Set.indicator_of_notMem hω]; linarith
    rwa [integral_const, probReal_univ, one_smul] at hle

/-- The pre-stop key bounds at a path with unitary `𝕊`, on the stop, after the injection:
`‖𝒜Φ_π‖ ≤ C_εK² + cδ` and `0 ≤ -Re 𝒜Φ_π + cδ ≤ C_εK² + 2cδ` (from the reverse bridge and the
size of the regularized generator). -/
theorem nss_preStop_key {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ}
    {N : ℕ} (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    (κ : Fin 0 → ℕ) {j : ℕ} {ω : GrowthPath W}
    (halive : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    ‖polyValue b E κ (fun _ => q) W j ω (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))‖ ≤
        transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2) +
          transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) ∧
      0 ≤ -(polyValue b E κ (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re +
          transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) ∧
      -(polyValue b E κ (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re +
          transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) ≤
        transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2) +
          2 * (transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2)) := by
  have hbr := abs_le.1 (nss_abs_polyGen_sub_genExpr_le hb hE hE' hq h1 h2 κ halive hj hS hqt)
  have hG0 := nss_genExpr_nonpos hb hE hE' hp0 hp1 hε hq hS
  have hGC := abs_le.1 (nss_abs_genExpr_le_alive hb hE hE' hp0 hp1 hε hq κ halive hj hS)
  have hn : ‖polyValue b E κ (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))‖ =
      |(polyValue b E κ (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re| := by
    rw [nsf_polyValue_wordGenerator_path b E hq W j ω κ a N hqt, Complex.norm_real,
      Complex.ofReal_re, Real.norm_eq_abs]
  rw [hn]
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

end BlockBand.Endpoints
