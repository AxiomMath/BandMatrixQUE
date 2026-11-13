module

public import BlockBand.Endpoints.Response.RemoteHigherFiniteBridge

/-!
# One-step inputs of the stopped higher energy inequality

**Proved here.**
* `rhf_rhlGenExpr_nonpos`: `rhlGenExpr ≤ 0` when `𝕊` is unitary (`pr < 1`).
* `rhf_abs_rhlGenExpr_le_alive`: `|rhlGenExpr| ≤ C₀ = B(C₁ + C₂/2)` on the stop.
* `rhf_preStop_key`: on the stop, after the injection: `‖𝒜 G(Φ_π)‖ ≤ C₀ + c`,
  `0 ≤ -Re 𝒜 G(Φ_π) + c ≤ C₀ + 2c` and `-rhlGenExpr ≤ -Re 𝒜 G(Φ_π) + c`, `c = δκ`.
* `rhf_preStop_abstract`: the abstract one-step bound
  `E[(-X)⁺] ≤ r + E[1_{Aᶜ}(-X)⁺]` with `0 ≤ r ≤ -E[1_A Re G] + c`, `r ≤ C₀ + 2c`.
* `rhf_abs_eval_le`, `rhf_integrable_polyValue_composite`: `G(Φ_π)(A_j)` is integrable once
  `E (Tr Q_j)^{(N+1)(d+1)} < ∞`.
* `rhf_startValue_le`: `E[1_A Re G(Φ_π)(A_j)] ≤ E(H_ε(A_j)+ε^p)^r + δ(BK+1)` (values only).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset Polynomial
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Sign and size of the chain-rule generator
-/

/-- `rhlGenExpr ≤ 0` at a path with unitary `𝕊`. -/
theorem rhf_rhlGenExpr_nonpos {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r) (hpr : p * r < 1) (hε : 0 < ε) {q : ℝ → ℝ}
    (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    rhlGenExpr b E p r ε q W j ω ≤ 0 := by
  refine (rhl_genExpr_le hb hE hE' hp0 hp1 hr hε hq hS).trans ?_
  have hrate : 0 ≤ rhlDecayRate b E p r := by
    unfold rhlDecayRate
    have := (ns_transportD0_pos hb hE hE').le
    have : 0 ≤ 1 - r * p := by linarith [mul_comm p r]
    have : 0 ≤ r := by linarith
    positivity
  have hc : 0 ≤ nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) :=
    ns_clockSum_nonneg (fun x _ => by
      unfold nsDissKernel
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
      (ns_nearClock_posSemidef b E W j q hq ω)
  have hH := Real.rpow_nonneg (rhl_shiftTrace_pos (b := b) (E := E) (W := W) (j := j) hp0 hε
    hq ω).le (r - 1)
  nlinarith [mul_nonneg hH hc]

/-- `|rhlGenExpr| ≤ C₀` on the stop. -/
theorem rhf_abs_rhlGenExpr_le_alive {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' : ℝ}
    {j : ℕ} {ω : GrowthPath W}
    (halive : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    |rhlGenExpr b E p r ε q W j ω| ≤ rhfC0 b E p r ε K := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  obtain ⟨-, -, -, hA⟩ := nsf_alive_bounds (noTags W) hq halive hj hS
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hK : 0 ≤ K := hA0.trans hA
  have hD := (ns_transportD0_pos hb hE hE').le
  obtain ⟨hH0, hHle⟩ := rhf_clockSum_regKernel_bounds hp0 hp1 hε hpsd
  have hM1 : 0 ≤ p * ε ^ (p - 1) := mul_nonneg hp0 (Real.rpow_nonneg hε.le _)
  have hHR : nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) ∈ rhfRange p ε K := by
    have hεp := Real.rpow_pos_of_pos hε p
    refine rhf_mem_range_of hp0 hε (by linarith) ?_
    have := hHle.trans (mul_le_mul_of_nonneg_left hA hM1)
    linarith
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hlam : ∀ i, hpsd.1.eigenvalues i ∈ Icc 0 (K + 1) := fun i =>
    ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
  have hsq : (∑ i, hpsd.1.eigenvalues i) ^ 2 ≤ K ^ 2 := by
    rw [hsum]; exact pow_le_pow_left₀ hA0 hA 2
  have hΓf : |rhlBracketExpr b E p ε q W j ω| ≤ rhfC2 b E p ε K := by
    rw [rhf_rhlBracketExpr_eq]
    unfold rhfBracketExpr
    rw [dite_eq_left hpsd.1]
    refine (rhf_abs_specBracket_le hD hlam (fun i => nsg_frameDiag_nonneg _ _ i)
      (fun i => nsg_frameDiag_le_one hS hV i)
      (fun x hx => nss_abs_deriv_le hp0 hp1 hε hx.1)).trans ?_
    unfold rhfC2
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have h𝒢f : |nsgGenExpr b E p ε q W j ω| ≤ rhfC1 b E p ε K :=
    nss_abs_genExpr_le_alive hb hE hE' hp0 hp1 hε hq (noTags W) halive hj hS
  have h1 := rhf_abs_H1_le (r := r) hε hHR
  have h2 := rhf_abs_H2_le (r := r) hε hHR
  rw [rhf_rhlGenExpr_eq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
  unfold rhfC0
  have e1 := mul_le_mul h1 h𝒢f (abs_nonneg _) hB
  have e2 := mul_le_mul h2 hΓf (abs_nonneg _) hB
  nlinarith

/-- **The pre-stop key bounds** (the `r`-analogue of `nss_preStop_key`). -/
theorem rhf_preStop_key {b E p r ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hr : 1 ≤ r) (hpr : p * r < 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ} {G : ℝ[X]}
    (hπ0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hπ1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (hπ2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    (hG1 : ∀ y ∈ rhfRange p ε K, |(derivative G).eval y - rhfH1 (ε ^ p) r y| ≤ δ)
    (hG2 : ∀ y ∈ rhfRange p ε K, |(derivative (derivative G)).eval y - rhfH2 (ε ^ p) r y| ≤ δ)
    (hδ1 : δ ≤ 1) (hδK : δ * (K + 1) ≤ ε ^ p / 2) {j : ℕ} {ω : GrowthPath W}
    (halive : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    ‖polyValue b E (noTags W) (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t (rhfComposite a N G))‖ ≤
        rhfC0 b E p r ε K + δ * rhfKappa b E p r ε K ∧
      0 ≤ -(polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhfComposite a N G))).re +
          δ * rhfKappa b E p r ε K ∧
      -(polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhfComposite a N G))).re +
          δ * rhfKappa b E p r ε K ≤ rhfC0 b E p r ε K + 2 * (δ * rhfKappa b E p r ε K) ∧
      -rhlGenExpr b E p r ε q W j ω ≤
        -(polyValue b E (noTags W) (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (rhfComposite a N G))).re +
          δ * rhfKappa b E p r ε K := by
  have hbr := abs_le.1 (rhf_abs_polyGen_sub_rhlGenExpr_le hb hE hE' hp0 hp1 hε hq hπ0 hπ1 hπ2
    hG1 hG2 hδ1 hδK halive hj hS hqt)
  have hG0 := rhf_rhlGenExpr_nonpos hb hE hE' hp0 hp1 hr hpr hε hq hS
  have hGC := abs_le.1 (rhf_abs_rhlGenExpr_le_alive (r := r) hb hE hE' hp0 hp1 hε hq halive hj hS)
  have hn : ‖polyValue b E (noTags W) (fun _ => q) W j ω
      (wordGenerator b E (fun _ => q) t (rhfComposite a N G))‖ =
      |(polyValue b E (noTags W) (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t (rhfComposite a N G))).re| := by
    rw [rhf_polyValue_wordGenerator_composite_path b E hq a N W j ω G hqt, Complex.norm_real,
      Complex.ofReal_re, Real.norm_eq_abs]
  rw [hn]
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith, by linarith, by linarith⟩

/-!
## The abstract pre-stop step
-/

/-- **One pre-stop step, abstract form** (variant of `nss_preStop_abstract` with a separate
dissipation `X`): if on `A`, a.s., `‖G‖ ≤ C₀ + c`, `0 ≤ -Re G + c ≤ C₀ + 2c` and
`-X ≤ -Re G + c`, then `1_A G` is integrable and `E[(-X)⁺] ≤ r + E[1_{Aᶜ}(-X)⁺]` with
`0 ≤ r ≤ -E[1_A Re G] + c` and `r ≤ C₀ + 2c`. -/
theorem rhf_preStop_abstract {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) {G : Ω → ℂ} (hGm : Measurable G)
    {X : Ω → ℝ} {c C₀ : ℝ} (hc : 0 ≤ c) (hC₀ : 0 ≤ C₀)
    (hkey : ∀ᵐ ω ∂μ, ω ∈ A → ‖G ω‖ ≤ C₀ + c ∧ 0 ≤ -(G ω).re + c ∧
      -(G ω).re + c ≤ C₀ + 2 * c ∧ -X ω ≤ -(G ω).re + c) :
    Integrable (A.indicator G) μ ∧ ∃ r : ℝ, 0 ≤ r ∧
      ∫⁻ ω, ENNReal.ofReal (-X ω) ∂μ ≤
        ENNReal.ofReal r + ∫⁻ ω, Aᶜ.indicator (fun ω => ENNReal.ofReal (-X ω)) ω ∂μ ∧
      r ≤ -∫ ω, A.indicator (fun ω => (G ω).re) ω ∂μ + c ∧ r ≤ C₀ + 2 * c := by
  obtain ⟨hI, -⟩ := nss_preStop_abstract hA hGm hc hC₀
    (hkey.mono fun ω h hω => ⟨(h hω).1, (h hω).2.1, (h hω).2.2.1⟩)
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
  have hhm : Measurable fun ω => ENNReal.ofReal (h ω) :=
    ENNReal.measurable_ofReal.comp ((((Complex.measurable_re.comp hGm).neg).add
      measurable_const).indicator hA)
  refine ⟨hI, ∫ ω, h ω ∂μ, integral_nonneg_of_ae hh0, ?_, ?_, ?_⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hhI hh0, ← lintegral_add_left hhm]
    refine lintegral_mono_ae ?_
    filter_upwards [hkey] with ω hk
    by_cases hω : ω ∈ A
    · simp only [h, Set.indicator_of_mem hω, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω),
        add_zero]
      exact ENNReal.ofReal_le_ofReal (hk hω).2.2.2
    · simp only [h, Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω),
        ENNReal.ofReal_zero, zero_add, le_refl]
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
      · simp only [h, Set.indicator_of_mem hω]; exact (hk hω).2.2.1
      · simp only [h, Set.indicator_of_notMem hω]; linarith
    rwa [integral_const, probReal_univ, one_smul] at hle

/-!
## Integrability of the composite
-/

theorem rhf_pow_le_one_add {T : ℝ} (hT : 0 ≤ T) (k : ℕ) : max 1 T ^ k ≤ 1 + T ^ k := by
  rcases le_total T 1 with h | h
  · rw [max_eq_left h, one_pow]; have := pow_nonneg hT k; linarith
  · rw [max_eq_right h]; linarith

/-- `|G(y)| ≤ (Σ_i |g_i|)(2S+1)^d (1 + T^{(N+1)(d+1)})` when `|y| ≤ S(1 + T^{N+1})`. -/
theorem rhf_abs_eval_le (G : ℝ[X]) {y S T : ℝ} (N : ℕ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hy : |y| ≤ S * (1 + T ^ (N + 1))) :
    |G.eval y| ≤ (∑ i ∈ range (G.natDegree + 1), |G.coeff i|) * (2 * S + 1) ^ G.natDegree *
      (1 + T ^ ((N + 1) * (G.natDegree + 1))) := by
  set m := max 1 T
  set d := G.natDegree
  have hm1 : 1 ≤ m := le_max_left _ _
  have hTm : T ≤ m := le_max_right _ _
  have hy' : |y| ≤ (2 * S + 1) * m ^ (N + 1) := by
    have h1 : 1 + T ^ (N + 1) ≤ 2 * m ^ (N + 1) := by
      have := one_le_pow₀ hm1 (n := N + 1)
      have := pow_le_pow_left₀ hT hTm (N + 1)
      linarith
    have h2 : 0 ≤ m ^ (N + 1) := pow_nonneg (by linarith) _
    nlinarith
  have hpow : ∀ i ≤ d, |y| ^ i ≤ (2 * S + 1) ^ d * m ^ ((N + 1) * d) := by
    intro i hi
    have hb : 1 ≤ (2 * S + 1) * m ^ (N + 1) := by
      have := one_le_pow₀ hm1 (n := N + 1); nlinarith
    calc |y| ^ i ≤ ((2 * S + 1) * m ^ (N + 1)) ^ i := pow_le_pow_left₀ (abs_nonneg _) hy' i
      _ ≤ ((2 * S + 1) * m ^ (N + 1)) ^ d := pow_le_pow_right₀ hb hi
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm (N + 1)]
  have hmM : m ^ ((N + 1) * d) ≤ 1 + T ^ ((N + 1) * (d + 1)) :=
    (pow_le_pow_right₀ hm1 (Nat.mul_le_mul_left _ (Nat.le_succ d))).trans
      (rhf_pow_le_one_add hT _)
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [abs_mul, abs_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |y| ^ i ≤ (2 * S + 1) ^ d * m ^ ((N + 1) * d) := hpow i hi'
    _ ≤ (2 * S + 1) ^ d * (1 + T ^ ((N + 1) * (d + 1))) :=
        mul_le_mul_of_nonneg_left hmM (pow_nonneg (by linarith) _)

/-- `G(Φ_π)(A_j)` is integrable when `E (Tr Q_j)^{(N+1)(d+1)} < ∞`. -/
theorem rhf_integrable_polyValue_composite (b E : ℝ) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (a : ℕ → ℝ) (N : ℕ) (G : ℝ[X]) {j : ℕ}
    (hmom : ∫⁻ ω, ‖(intervalSource b E W j q ω).trace.re‖ₑ ^
      ((((N + 1) * (G.natDegree + 1) : ℕ) : ℝ)) ∂growthPathLaw W b ≠ ⊤) :
    Integrable (fun ω => polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G))
      (growthPathLaw W b) := by
  set M := (N + 1) * (G.natDegree + 1)
  set x : GrowthPath W → ℝ := fun ω => (intervalSource b E W j q ω).trace.re
  have hxm : Measurable x := Complex.measurable_re.comp
    ((continuous_id.matrix_trace).measurable.comp (nss_measurable_intervalSource b E W j q))
  have hpow : Integrable (fun ω => x ω ^ M) (growthPathLaw W b) := by
    refine ⟨(hxm.pow_const _).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : (fun ω => ‖x ω ^ M‖ₑ) = fun ω => ‖x ω‖ₑ ^ ((M : ℕ) : ℝ) := by
      funext ω; rw [enorm_pow, ENNReal.rpow_natCast]
    rw [this]
    exact lt_top_iff_ne_top.2 hmom
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  set S := ∑ r ∈ range N, |a r|
  have hS : 0 ≤ S := Finset.sum_nonneg fun r _ => abs_nonneg _
  refine (((integrable_const 1).add hpow).const_mul
    ((∑ i ∈ range (G.natDegree + 1), |G.coeff i|) * (2 * S + 1) ^ G.natDegree)).mono'
    (nss_measurable_polyValue b E (noTags W) _ W j _).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  rw [rhf_polyValue_composite b E hq a N W j ω G, Complex.norm_real, Real.norm_eq_abs]
  have hsum : ∑ i, hpsd.1.eigenvalues i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp
  have hΨ : rhfClockVal b E q a N W j ω = ∑ i, nsfPolyFun a N (hpsd.1.eigenvalues i) := by
    unfold rhfClockVal
    rw [nsf_polyValue_clockPoly_path b E hq W j ω (noTags W) a N, Complex.ofReal_re]
  have hy := nss_abs_sum_polyFun_le a N (fun i => hpsd.eigenvalues_nonneg i)
    (hsum.trans_le (trace_nearClock_le b E W j q hq ω).2)
  rw [← hΨ] at hy
  have hT0 : 0 ≤ x ω := trace_intervalSource_re_nonneg b E W j q hq ω
  exact (rhf_abs_eval_le G N hS hT0 hy).trans_eq (by simp only [Pi.add_apply, M, x])

/-!
## The start value
-/

/-- **The start value** on `{σ > j}`: `E[1_A Re G(Φ_π)(A_j)] ≤ E(H_ε(A_j)+ε^p)^r + δ(BK+1)`. -/
theorem rhf_startValue_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount)
    {b E p r ε : ℝ} (hb1 : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    {G : ℝ[X]} (hπ0 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyFun a N x - nsfRegFun p ε x| ≤ δ * x)
    (hG0 : ∀ y ∈ rhfRange p ε K, |G.eval y - rhfH (ε ^ p) r y| ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : δ * (K + 1) ≤ ε ^ p / 2) {W : ℕ} (hW : 0 < W) {j : ℕ} (hj : ε' * W ≤ j)
    (hI : Integrable ((alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j).indicator
      fun ω => (polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G)).re)
        (growthPathLaw W b)) :
    ENNReal.ofReal (∫ ω, (alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j).indicator
        (fun ω => (polyValue b E (noTags W) (fun _ => q) W j ω (rhfComposite a N G)).re) ω
          ∂growthPathLaw W b) ≤
      ∫⁻ ω, ENNReal.ofReal ((nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) + ε ^ p) ^ r)
          ∂growthPathLaw W b + ENNReal.ofReal (δ * (rhfB p r ε K * K + 1)) := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  obtain ⟨he, hPt, -⟩ := nss_integral_indicator_eq hI
  rw [he]
  refine (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans ?_
  rw [ENNReal.ofReal_toReal hPt]
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal ((nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω) +
          ε ^ p) ^ r) + ENNReal.ofReal (δ * (rhfB p r ε K * K + 1))) ∂growthPathLaw W b := by
        refine lintegral_mono_ae ?_
        filter_upwards [nsg_ae_scattering_unitary hCount hb1 hE hE' hW j] with ω hS
        by_cases hal : ω ∈ alive b E (noTags W) (fun _ : Fin 1 => q) K ε' W j
        · rw [Set.indicator_of_mem hal]
          refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
          obtain ⟨hK, -, hdK, hΨR, hHR, -⟩ :=
            rhf_path_ranges hp0 hp1 hε hq hπ0 hδ1 hδK hal hj hS
          rw [rhf_polyValue_composite b E hq a N W j ω G, Complex.ofReal_re]
          have h1 := (abs_le.1 (hG0 _ hΨR)).2
          have h2 := (abs_le.1 (rhf_abs_H_sub_le (r := r) hε hΨR hHR)).2
          have hB := rhf_B_nonneg (p := p) (r := r) (K := K) hε
          have h3 : rhfB p r ε K * |rhfClockVal b E q a N W j ω -
              nsClockSum (nsRegKernel p ε) (nearClock b E W j q ω)| ≤
              rhfB p r ε K * (δ * K) := mul_le_mul_of_nonneg_left hdK hB
          unfold rhfH at h1 h2
          nlinarith
        · rw [Set.indicator_of_notMem hal]; exact zero_le
    _ = _ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

end BlockBand.Endpoints
