module

public import BlockBand.Endpoints.Response.NearSchattenPassage
public import BlockBand.Endpoints.Response.PassDerivative

/-!
# Passing `H_p` to critical limits (upper direction, eigenvalue cutoffs)

`ns_limsup_fracTrace_le`: along the subsequence of a critical word limit with a.s. clock
measures at a time `u`, if eventually `E Tr A^{p₀} ≤ C₀` (`p₀ < p`, the smaller power) and
`E (Tr A)² ≤ C₂` (the higher trace bound), then `limsup E Tr A^p ≤ E H_p(μ_u)`.

Mechanism. For a cutoff `a > 0`: `Tr A^p ≤ Σ_{λ ≤ a} λ^p + Σ_i λ_i (max λ_i a)^{p-1}`; the small
channels are `≤ a^{p-p₀} Tr A^{p₀}` (the pointwise small-channel bound); the kernel
`(max x a)^{p-1} ≤ a^{p-1}` is bounded continuous, and its clock integral passes to the limit
through the upper test `min(M, max(0, Σ_l π_l Re z_l + δ Re z_0)) χ_K(Re z_0)` up to the large-trace
remainder `a^{p-1} E[(Tr A)²]/(K-1)`. Letting `K → ∞`, then `a ↓ 0`, gives the claim.
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
## Measurability at finite width
-/

theorem ns_continuous_toBlocks₁₂ {m n : Type*} :
    Continuous (fun M : Matrix (m ⊕ n) (m ⊕ n) ℂ => M.toBlocks₁₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inl i))

theorem ns_measurable_tagResponse (b E : ℝ) (W n k : ℕ) :
    Measurable (fun ω : GrowthPath W => tagResponse b E W n k ω) := by
  have hF : Measurable (fun ω : GrowthPath W => fullInverse b E W n ω) :=
    passDeriv_measurable_inv.comp (measurable_fullPathMatrix b E W n)
  have hc : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (G.toBlocks₁₂)ᴴ * tagProjection W n k * G.toBlocks₁₂) :=
    ((ns_continuous_toBlocks₁₂.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      ns_continuous_toBlocks₁₂
  exact hc.measurable.comp hF

theorem ns_measurable_nearClock (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => nearClock b E W j q ω) := by
  have hQ : Measurable (fun ω : GrowthPath W => intervalSource b E W j q ω) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    simp only [intervalSource, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun k _ => measurable_const.mul
      ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp
        (ns_measurable_tagResponse b E W j k)))
  have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => portBlock M 0 0) :=
    continuous_pi fun x => continuous_pi fun y => (continuous_apply (0, y)).comp
      (continuous_apply (0, x))
  exact hc.measurable.comp hQ

theorem ns_measurable_clockMoments (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) (m : ℕ) :
    Measurable (fun ω : GrowthPath W => fun l : Fin (m + 1) =>
      ((nearClock b E W j q ω) ^ ((l : ℕ) + 1)).trace) := by
  refine measurable_pi_iff.mpr fun l => ?_
  exact ((continuous_id.pow _).matrix_trace).measurable.comp (ns_measurable_nearClock b E W j q)

theorem ns_measurable_trace_nearClock (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => (nearClock b E W j q ω).trace.re) :=
  Complex.continuous_re.measurable.comp
    ((continuous_id.matrix_trace).measurable.comp (ns_measurable_nearClock b E W j q))

/-!
## The second moment of the clock
-/

theorem ns_sum_tagProjection (W n : ℕ) :
    ∑ k ∈ Finset.range n, tagProjection W n k = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  unfold tagProjection
  simp only [diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [one_apply_eq, ite_true]
    have hx := x.1.isLt
    rw [Finset.sum_eq_single (n - 1 - x.1.val)]
    · have hc : n - 1 - x.1.val < n ∧ x.1.val = n - 1 - (n - 1 - x.1.val) :=
        ⟨by omega, by omega⟩
      exact ite_eq_left_of_eq_true _ _ (eq_true hc)
    · intro k hk hne
      have : ¬ (k < n ∧ x.1.val = n - 1 - k) := by
        rintro ⟨_, h⟩
        exact hne (by rw [Finset.mem_range] at hk; omega)
      exact ite_eq_right_of_eq_false _ _ (eq_false this)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · simp [hxy, one_apply_ne hxy]

/-- `Σ_k Re Tr Y_{n;k} = Re Tr 𝒰*𝒰`. -/
theorem ns_sum_trace_tagResponse (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    ∑ k ∈ Finset.range n, (tagResponse b E W n k ω).trace.re =
      ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace.re := by
  rw [← Complex.re_sum, ← trace_sum]
  congr 2
  unfold tagResponse
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, ns_sum_tagProjection, Matrix.mul_one]

/-- `Tr A ≤ W⁻² Re Tr 𝒰*𝒰` for `0 ≤ q ≤ 1`. -/
theorem ns_trace_nearClock_le_clock (b E : ℝ) (W n : ℕ) {q : ℝ → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∀ x, q x ≤ 1) (ω : GrowthPath W) :
    (nearClock b E W n q ω).trace.re ≤ ((W : ℝ) ^ 2)⁻¹ *
      ((boundaryToInterior b E W n ω)ᴴ * boundaryToInterior b E W n ω).trace.re := by
  refine (trace_nearClock_le b E W n q hq0 ω).2.trans ?_
  rw [trace_intervalSource, Complex.ofReal_re, ← ns_sum_trace_tagResponse, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hY : 0 ≤ (tagResponse b E W n k ω).trace.re :=
    (Complex.nonneg_iff.mp (tagResponse_posSemidef b E W n k ω).trace_nonneg).1
  rw [div_eq_mul_inv, mul_comm (q _)]
  have := hq1 (((k + 1 : ℕ) : ℝ) / W)
  have hW : 0 ≤ ((W : ℝ) ^ 2)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hW]

/-- **Second moment of the near clock** from the `FullSourceMomentsContract.clock`
(`p = 2`): at a fixed time `u ≥ 0` there are `C₂`, `W₀` with `E (Tr A)² ≤ C₂` at length `⌊Wu⌋`
for `W ≥ W₀` and every test `0 ≤ q ≤ 1`.
-/
theorem ns_trace_sq_bound (hM : FullSourceMomentsContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E) (hE' : E < 2) {u : ℝ} (hu : 0 ≤ u) :
    ∃ (C₂ : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) →
      ∫⁻ ω, ENNReal.ofReal ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2)
        ∂growthPathLaw W b ≤ ENNReal.ofReal C₂ := by
  obtain ⟨C, W₀, hC⟩ := hM.clock b hb hb' E hE hE' u 2 (by norm_num)
  refine ⟨C ^ 2 * (u + 1) ^ 2, max W₀ 1, fun W hW q hq0 hq1 => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  set j := ⌊(W : ℝ) * u⌋₊ with hj
  have hjle : (j : ℝ) ≤ (W : ℝ) * u := Nat.floor_le (by positivity)
  have hcl := hC W (le_of_max_le_left hW) j (by linarith)
  set Y := fun ω => (boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω with hY
  set f : GrowthPath W → ℝ := fun ω => (W : ℝ)⁻¹ * (Y ω).trace.re with hf
  have hYpsd : ∀ ω, (Y ω).PosSemidef := fun ω =>
    posSemidef_conjTranspose_mul_self _
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    mul_nonneg (by positivity) (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).1
  have hfun : (fun ω => (W : ℂ)⁻¹ * (Y ω).trace) = fun ω => ((f ω : ℝ) : ℂ) := by
    funext ω
    have him := (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).2
    simp only [hf, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    congr 1
    exact Complex.ext rfl (by simp [← him])
  rw [hfun] at hcl
  have hmom := indicator_moment_le_of_eLpNorm hf0 (by norm_num : (1 : ℝ) ≤ 2) hcl
  have hpt : ∀ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ 2) ≤
      ENNReal.ofReal ((W : ℝ)⁻¹ ^ 2) * ENNReal.ofReal (f ω ^ (2 : ℝ)) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := ns_trace_nearClock_le_clock b E W j hq0 hq1 ω
    have h0 := (trace_nearClock_le b E W j q hq0 ω).1
    have : (nearClock b E W j q ω).trace.re ≤ (W : ℝ)⁻¹ * f ω := by
      simp only [hf]; rw [← mul_assoc, ← sq, inv_pow]; exact h1
    calc (nearClock b E W j q ω).trace.re ^ 2 ≤ ((W : ℝ)⁻¹ * f ω) ^ 2 := by gcongr
      _ = (W : ℝ)⁻¹ ^ 2 * f ω ^ 2 := by ring
  calc ∫⁻ ω, ENNReal.ofReal ((nearClock b E W j q ω).trace.re ^ 2) ∂growthPathLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal ((W : ℝ)⁻¹ ^ 2) * ENNReal.ofReal (f ω ^ (2 : ℝ))
          ∂growthPathLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal ((W : ℝ)⁻¹ ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (f ω ^ (2 : ℝ)) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((W : ℝ)⁻¹ ^ 2) * ENNReal.ofReal ((C * ((j : ℝ) + 1)) ^ (2 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (C ^ 2 * (((j : ℝ) + 1) / W) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_two]
        congr 1; field_simp
    _ ≤ ENNReal.ofReal (C ^ 2 * (u + 1) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
        have h1 : ((j : ℝ) + 1) / W ≤ u + 1 := by
          rw [div_le_iff₀ hW0]; nlinarith
        have h2 : 0 ≤ ((j : ℝ) + 1) / W := by positivity
        nlinarith

/-!
## Eigenvalue cutoffs at finite width
-/

section Finite

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Small/large split: `Tr A^p ≤ Σ_{λ ≤ a} λ^p + Σ_i λ_i (max λ_i a)^{p-1}` (`A ⪰ 0`, `a > 0`). -/
theorem ns_fracTrace_le_small_add {A : Matrix n n ℂ} (hA : A.PosSemidef) {a p : ℝ} (ha : 0 < a) :
    fracTrace p A ≤ smallChannelPower a p A + nsClockSum (nsCutKernel a (p - 1)) A := by
  classical
  rw [fracTrace_eq_sum_eigenvalues_of_posSemidef hA, smallChannelPower_eq_sum_eigenvalues hA.isHermitian,
    ns_clockSum_eq _ hA.isHermitian, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set x := hA.isHermitian.eigenvalues i
  have hx0 : 0 ≤ x := hA.eigenvalues_nonneg i
  have hc : 0 ≤ nsCutKernel a (p - 1) x := ns_cutKernel_nonneg ha x
  by_cases hxa : x ≤ a
  · simp only [hxa, ↓reduceIte, max_eq_left hx0]
    have := mul_nonneg hx0 hc
    linarith
  · simp only [hxa, ↓reduceIte, zero_add]
    have hxa' : a < x := lt_of_not_ge hxa
    have hxpos : 0 < x := ha.trans hxa'
    rw [nsCutKernel, max_eq_left hxa'.le, mul_comm, ← Real.rpow_add_one hxpos.ne']
    ring_nf; exact le_rfl

/-- Upper test at finite width. If `0 ≤ c ≤ B`, `|π - c| ≤ δ ≤ 1` on `[0, K]`, `K ≥ 2` and
`M ≥ BK + 2K`, then `Σ_i λ_i c(λ_i) ≤ Ψ⁺(moments) + B (Tr A)²/(K - 1)` (`A ⪰ 0`). -/
theorem ns_clockSum_le_testFun_upper (π : ℝ[X]) {m : ℕ} (hm : π.natDegree ≤ m) {c : ℝ → ℝ}
    (hc0 : ∀ x, 0 ≤ c x) {B δ K M : ℝ} (hcB : ∀ x, c x ≤ B) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hK : 2 ≤ K) (hM : B * K + 2 * K ≤ M) (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    nsClockSum c A ≤ nsTestFun π m 1 δ K M (fun l => (A ^ ((l : ℕ) + 1)).trace) +
      B * A.trace.re ^ 2 / (K - 1) := by
  have hT0 : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hS := ns_clockSum_nonneg (fun x _ => hc0 x) hA
  have hB0 : 0 ≤ B := (hc0 0).trans (hcB 0)
  have hM0 : 0 ≤ M := by nlinarith
  have hTest := ns_testFun_nonneg π m 1 δ K hM0 (fun l => (A ^ ((l : ℕ) + 1)).trace)
  have hSB : nsClockSum c A ≤ B * A.trace.re := by
    rw [ns_clockSum_eq c hA.isHermitian, trace_re_eq_sum_eigenvalues hA.isHermitian, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left (hcB _) (hA.eigenvalues_nonneg i)
  have hK1 : 0 < K - 1 := by linarith
  rcases le_or_gt A.trace.re (K - 1) with hT | hT
  · have h0 : ((fun l : Fin (m + 1) => (A ^ ((l : ℕ) + 1)).trace) 0).re = A.trace.re := by simp
    have hrem : 0 ≤ B * A.trace.re ^ 2 / (K - 1) := by positivity
    suffices nsClockSum c A ≤ nsTestFun π m 1 δ K M (fun l => (A ^ ((l : ℕ) + 1)).trace) by
      linarith
    unfold nsTestFun
    rw [h0, ns_cutoff_eq_one hT, mul_one, ns_polyMoment_trace hA.isHermitian π hm]
    have happ' := ns_clockSum_sub_poly_le hA (by linarith) happ
    have hlo := (abs_le.1 happ').2
    have hhi := (abs_le.1 happ').1
    have hX : nsClockSum c A ≤ ∑ i, hA.isHermitian.eigenvalues i *
        π.eval (hA.isHermitian.eigenvalues i) + 1 * δ * A.trace.re := by linarith
    have hXM : ∑ i, hA.isHermitian.eigenvalues i * π.eval (hA.isHermitian.eigenvalues i) +
        1 * δ * A.trace.re ≤ M := by
      have h2 : δ * A.trace.re ≤ K := by nlinarith
      have h3 : B * A.trace.re ≤ B * K := mul_le_mul_of_nonneg_left (by linarith) hB0
      linarith
    rw [min_eq_right ((max_le (by linarith) hXM))]
    exact hX.trans (le_max_right _ _)
  · have : B * A.trace.re ≤ B * A.trace.re ^ 2 / (K - 1) := by
      rw [le_div_iff₀ hK1]
      have : A.trace.re * (K - 1) ≤ A.trace.re ^ 2 := by nlinarith
      nlinarith
    linarith

end Finite

/-- Upper test on the limit side. For a clock measure, `0 ≤ c`, `|π - c| ≤ δ` on `[0, K]`,
`0 ≤ δ`, `0 ≤ K`: `Ψ⁺(Z) ≤ ∫ c dμ + 2δK`. -/
theorem ns_testFun_upper_le {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ} {ω : Ω}
    {μ : Measure ℝ} (h : IsClockMeasure Z u ω μ) {c : ℝ → ℝ} (hc : Continuous c)
    (hc0 : ∀ x, 0 ≤ c x) (π : ℝ[X]) {m : ℕ} (hm : π.natDegree ≤ m) {δ K M : ℝ} (hδ0 : 0 ≤ δ)
    (hK0 : 0 ≤ K) (hM0 : 0 ≤ M) (happ : ∀ x ∈ Icc 0 K, |π.eval x - c x| ≤ δ) :
    nsTestFun π m 1 δ K M (nsClockVec Z m u ω) ≤ ∫ x, c x ∂μ + 2 * δ * K := by
  have hI0 : 0 ≤ ∫ x, c x ∂μ := integral_nonneg hc0
  have hr : 0 ≤ 2 * δ * K := by positivity
  have h0 : (nsClockVec Z m u ω 0).re = (Z (clockWord 1) u ω).re := rfl
  have hZ0 : 0 ≤ (Z (clockWord 1) u ω).re := by
    have h1 := ns_clockMeasure_real_univ h
    have h2 : 0 ≤ μ.real univ := measureReal_nonneg
    linarith
  unfold nsTestFun
  rw [h0]
  rcases le_or_gt K (Z (clockWord 1) u ω).re with hK | hK
  · rw [ns_cutoff_eq_zero hK, mul_zero]; linarith
  · have happ' := ns_integral_sub_poly_le h hc hK.le happ
    have hI := ns_integral_poly_clockMeasure h π hm
    have hX : nsPolyMoment π m (nsClockVec Z m u ω) + 1 * δ * (Z (clockWord 1) u ω).re ≤
        ∫ x, c x ∂μ + 2 * δ * K := by
      have := (abs_le.1 happ').1
      unfold nsClockVec
      rw [← hI]
      nlinarith
    have h1 := ns_cutoff_le_one K (Z (clockWord 1) u ω).re
    have h2 := ns_cutoff_nonneg K (Z (clockWord 1) u ω).re
    have h3 : min M (max 0 (nsPolyMoment π m (nsClockVec Z m u ω) +
        1 * δ * (Z (clockWord 1) u ω).re)) ≤ ∫ x, c x ∂μ + 2 * δ * K :=
      (min_le_right _ _).trans (max_le (by linarith) hX)
    have h4 : 0 ≤ min M (max 0 (nsPolyMoment π m (nsClockVec Z m u ω) +
        1 * δ * (Z (clockWord 1) u ω).re)) := le_min hM0 (le_max_left _ _)
    nlinarith

/-- `ofReal ∫ (max x a)^{p-1} dμ ≤ H_p(μ)` for a clock measure (`a > 0`, `p < 1`). -/
theorem ns_ofReal_integral_cutKernel_le {Ω : Type*} {Z : ClockWord → ℝ → Ω → ℂ} {u : ℝ}
    {ω : Ω} {μ : Measure ℝ} (h : IsClockMeasure Z u ω μ) {a p : ℝ} (ha : 0 < a) (hp1 : p < 1) :
    ENNReal.ofReal (∫ x, nsCutKernel a (p - 1) x ∂μ) ≤ limitFracTrace p μ := by
  rw [ofReal_integral_eq_lintegral_ofReal (ns_clockMeasure_integrable h (ns_continuous_cutKernel ha))
    (Eventually.of_forall fun x => ns_cutKernel_nonneg ha x)]
  unfold limitFracTrace
  refine lintegral_mono fun x => ?_
  rcases le_or_gt x 0 with hx | hx
  · rw [ENNReal.ofReal_of_nonpos hx, ENNReal.zero_rpow_of_neg (by linarith)]; exact le_top
  · rw [ENNReal.ofReal_rpow_of_pos hx]
    exact ENNReal.ofReal_le_ofReal (ns_cutKernel_le_rpow hx (by linarith))

/-!
## The upper passage
-/

/-- Upper passage of `H_p` to a critical limit. Along the subsequence of a joint critical word
limit (one-source family, `q ≥ 0`), at a time `u ≥ t₀` with a.s. clock measures `μ_u`: if
eventually `E Tr A^{p₀} ≤ C₀` (`0 < p₀ < p < 1`) and `E (Tr A)² ≤ C₂` at length `⌊Wu⌋`, then
`limsup_n E Tr A^p ≤ E H_p(μ_u)`. -/
theorem ns_limsup_fracTrace_le {b E : ℝ} {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {t₀ u : ℝ}
    (hu : t₀ ≤ u) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ClockWord → ℝ → Ω → ℂ} (hmeas : ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) (hfdd : NsFddAlong b E q t₀ P Z φ)
    {μ : Ω → Measure ℝ} (hμ : ∀ᵐ ω ∂P, IsClockMeasure Z u ω (μ ω)) {p p₀ : ℝ} (hp₀ : 0 < p₀)
    (hp₀p : p₀ < p) (hp1 : p < 1) {C₀ C₂ : ℝ}
    (hH0 : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p₀ (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b ≤ ENNReal.ofReal C₀)
    (hUI : ∀ᶠ W : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
        ((nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω).trace.re ^ 2) ∂growthPathLaw W b ≤
          ENNReal.ofReal C₂) :
    limsup (fun n => ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b) atTop ≤
      ∫⁻ ω, limitFracTrace p (μ ω) ∂P := by
  have hp : 0 < p := hp₀.trans hp₀p
  set L := limsup (fun n => ∫⁻ ω, ENNReal.ofReal
    (fracTrace p (nearClock b E (φ n) ⌊(φ n : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ n) b) atTop
  set Hl := ∫⁻ ω, limitFracTrace p (μ ω) ∂P
  -- the bound at cutoff `a = ε_m` and polynomial level `K`
  have key : ∀ m K : ℕ, L ≤ ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) * ENNReal.ofReal C₀ +
      (Hl + ENNReal.ofReal (2 * (1 / ((K : ℝ) + 2) ^ 2) * ((K : ℝ) + 2))) +
      ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)) * ENNReal.ofReal C₂ := by
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
    set Ψ := nsTestBCF π md 1 δ Kr M hM0
    have hΨapp : ∀ z, Ψ z = nsTestFun π md 1 δ Kr M z := fun z => rfl
    -- finite width: pointwise bound and integration
    have hfin : ∀ W : ℕ, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b ≤
        ENNReal.ofReal (2 * a ^ (p - p₀)) * ∫⁻ ω, ENNReal.ofReal
          (fracTrace p₀ (nearClock b E W ⌊(W : ℝ) * u⌋₊ q ω)) ∂growthPathLaw W b +
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
      set F₁ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (2 * a ^ (p - p₀)) * ENNReal.ofReal (fracTrace p₀ (A ω))
      set F₂ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (Ψ (fun l : Fin (md + 1) => ((A ω) ^ ((l : ℕ) + 1)).trace))
      set F₃ : GrowthPath W → ℝ≥0∞ := fun ω =>
        ENNReal.ofReal (B / (Kr - 1)) * ENNReal.ofReal ((A ω).trace.re ^ 2)
      have hF₂ : Measurable F₂ := ENNReal.measurable_ofReal.comp hmΨ
      have hF₃ : Measurable F₃ := (ENNReal.measurable_ofReal.comp
          ((ns_measurable_trace_nearClock b E W _ q).pow_const 2)).const_mul _
      calc ∫⁻ ω, ENNReal.ofReal (fracTrace p (A ω)) ∂growthPathLaw W b
          ≤ ∫⁻ ω, (F₁ ω + F₂ ω + F₃ ω) ∂growthPathLaw W b := by
            refine lintegral_mono fun ω => ?_
            have hApsd := ns_nearClock_posSemidef b E W ⌊(W : ℝ) * u⌋₊ q hq ω
            have h1 := ns_fracTrace_le_small_add hApsd ha0 (p := p)
            have h2 := smallChannelPower_le_rpow_mul_fracTrace ha0.le hp hp₀p.le (A ω)
            have h3 := ns_clockSum_le_testFun_upper π le_rfl hc0 hcB hδ0 hδ1 hKr2 le_rfl happ hApsd
            have hf0 := fracTrace_nonneg p₀ (A ω)
            have ht0 := ns_testFun_nonneg π md 1 δ Kr hM0 (fun l => (A ω ^ ((l : ℕ) + 1)).trace)
            have hK1 : 0 < Kr - 1 := by linarith
            have hreal : fracTrace p (A ω) ≤ 2 * a ^ (p - p₀) * fracTrace p₀ (A ω) +
                nsTestFun π md 1 δ Kr M (fun l => (A ω ^ ((l : ℕ) + 1)).trace) +
                B / (Kr - 1) * (A ω).trace.re ^ 2 := by
              have : a ^ (p - p₀) * fracTrace p₀ (A ω) ≤ 2 * a ^ (p - p₀) * fracTrace p₀ (A ω) := by
                have : 0 ≤ a ^ (p - p₀) * fracTrace p₀ (A ω) :=
                  mul_nonneg (Real.rpow_nonneg ha0.le _) hf0
                linarith
              have h4 : B * (A ω).trace.re ^ 2 / (Kr - 1) = B / (Kr - 1) * (A ω).trace.re ^ 2 := by
                ring
              linarith
            simp only [F₁, F₂, F₃]
            rw [hΨapp, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) ht0, ← ENNReal.ofReal_add (by positivity)
                (by positivity)]
            exact ENNReal.ofReal_le_ofReal hreal
        _ = ∫⁻ ω, F₁ ω ∂growthPathLaw W b + ∫⁻ ω, F₂ ω ∂growthPathLaw W b +
              ∫⁻ ω, F₃ ω ∂growthPathLaw W b := by
            rw [lintegral_add_right _ hF₃, lintegral_add_right _ hF₂]
        _ = _ := by
            simp only [F₁, F₃]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- along the subsequence
    have hvec : ∀ k : ℕ, ∀ ω : GrowthPath (φ k), (fun l : Fin (md + 1) =>
        wordValue b E (noTags (φ k)) (fun _ => q) (φ k) ⌊(φ k : ℝ) * u⌋₊ ω
          (clockWord ((l : ℕ) + 1))) =
        fun l : Fin (md + 1) => ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace :=
      fun k ω => funext fun l => ns_wordValue_clockWord_eq b E q _ _ ω _ (by omega)
    have hlimΨ := hfdd (md + 1) (fun l => clockWord ((l : ℕ) + 1)) (fun _ => u)
      (fun l => ⟨ns_isOrdinaryWord_clockWord (by omega), hu⟩) Ψ
    simp_rw [hvec] at hlimΨ
    set X := ENNReal.ofReal (2 * a ^ (p - p₀)) * ENNReal.ofReal C₀
    set Y := ENNReal.ofReal (B / (Kr - 1)) * ENNReal.ofReal C₂
    have hev : ∀ᶠ k in atTop, ∫⁻ ω, ENNReal.ofReal
        (fracTrace p (nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω)) ∂growthPathLaw (φ k) b ≤
        X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
          ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
            ∂growthPathLaw (φ k) b) + Y := by
      filter_upwards [hφ.tendsto_atTop.eventually hH0, hφ.tendsto_atTop.eventually hUI]
        with k h0 h2
      refine (hfin (φ k)).trans ?_
      gcongr
      · exact mul_le_mul_right h0 _
      · exact mul_le_mul_right h2 _
    have hlim : Tendsto (fun k => X + ENNReal.ofReal (∫ ω, Ψ (fun l : Fin (md + 1) =>
        ((nearClock b E (φ k) ⌊(φ k : ℝ) * u⌋₊ q ω) ^ ((l : ℕ) + 1)).trace)
          ∂growthPathLaw (φ k) b) + Y) atTop
        (𝓝 (X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y)) :=
      (tendsto_const_nhds.add (ENNReal.tendsto_ofReal hlimΨ)).add tendsto_const_nhds
    have hL : L ≤ X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y :=
      (limsup_le_limsup hev).trans_eq hlim.limsup_eq
    -- the limit side
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
          ≤ ∫⁻ ω, (limitFracTrace p (μ ω) + ENNReal.ofReal (2 * δ * Kr)) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hμ] with ω hω
            rw [hΨapp]
            have h1 := ns_testFun_upper_le hω hc hc0 π (m := md) le_rfl hδ0 (by linarith) hM0 happ
            have hI0 : 0 ≤ ∫ x, c x ∂μ ω := integral_nonneg hc0
            calc ENNReal.ofReal (nsTestFun π md 1 δ Kr M (nsClockVec Z md u ω))
                ≤ ENNReal.ofReal (∫ x, c x ∂μ ω + 2 * δ * Kr) := ENNReal.ofReal_le_ofReal h1
              _ = ENNReal.ofReal (∫ x, c x ∂μ ω) + ENNReal.ofReal (2 * δ * Kr) :=
                  ENNReal.ofReal_add hI0 (by positivity)
              _ ≤ _ := by
                  gcongr
                  exact ns_ofReal_integral_cutKernel_le hω ha0 hp1
        _ = Hl + ENNReal.ofReal (2 * δ * Kr) := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    calc L ≤ X + ENNReal.ofReal (∫ ω, Ψ (nsClockVec Z md u ω) ∂P) + Y := hL
      _ ≤ X + (Hl + ENNReal.ofReal (2 * δ * Kr)) + Y := by gcongr
  -- `K → ∞`, then `m → ∞`
  have hstep1 : ∀ m : ℕ, L ≤ ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) * ENNReal.ofReal C₀ + Hl := by
    intro m
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
    have hBK : Tendsto (fun K : ℕ => ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1)) *
        ENNReal.ofReal C₂) atTop (𝓝 0) := by
      have h : Tendsto (fun K : ℕ => ENNReal.ofReal (nsEps m ^ (p - 1) / ((K : ℝ) + 2 - 1))) atTop
          (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine ENNReal.tendsto_ofReal ?_
        have : Tendsto (fun K : ℕ => nsEps m ^ (p - 1) * (1 / ((K : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (nsEps m ^ (p - 1))
        refine this.congr' (Eventually.of_forall fun K => ?_)
        simp only
        ring
      simpa using ENNReal.Tendsto.mul_const h (Or.inr ENNReal.ofReal_ne_top)
    have hlim := ((tendsto_const_nhds (x := ENNReal.ofReal (2 * nsEps m ^ (p - p₀)) *
      ENNReal.ofReal C₀)).add ((tendsto_const_nhds (x := Hl)).add hδK)).add hBK
    simp only [add_zero] at hlim
    exact ge_of_tendsto' hlim (key m)
  have hlim := (ns_tendsto_regError hp₀p (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top).add
    (tendsto_const_nhds (x := Hl))
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hstep1

end BlockBand.Endpoints
