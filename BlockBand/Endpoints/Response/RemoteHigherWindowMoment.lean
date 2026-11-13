module

public import BlockBand.Endpoints.Response.RemoteHigherWindowBound

/-!
# The window transfer of fractional clock moments, uniform form

* `rhw_window_poly_bound` — a priori polynomial bound `E_e H_p^s ≤ C W^s` (`s ≥ 1`) at window
  energies, every length `m ≤ TW` and every source `0 ≤ q ≤ 1`, from
  `FullSourceMomentsEnergyUniformContract.clock`.
* `rhw_window_moment_bound` — **the window transfer**: `C₁` before `T`; then for all large `W`,
  every `|e - E| ≤ K/W²`, every `1 ≤ m ≤ TW` and every `0 ≤ q ≤ 1`,
  `E_e H_p^r ≤ C₁ (E_E H_p^{ra})^{1/a} + 1/W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Internal.Contracts.Endpoints (nearClock)
open scoped ENNReal NNReal ComplexOrder

/-- **A priori polynomial bound at window energies.** -/
theorem rhw_window_poly_bound (hU : FullSourceMomentsEnergyUniformContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {K : ℝ} {p s : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hs : 1 ≤ s) (T : ℝ) :
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, |e - E| ≤ K / (W : ℝ) ^ 2 →
      ∀ m : ℕ, (m : ℝ) ≤ T * W → ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) →
        ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ s ∂growthPathLaw W b ≤
          ENNReal.ofReal (C * (W : ℝ) ^ s) := by
  set κI := min (E + 2) (2 - E) with hκI
  have hκ : 0 < κI := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval κI := ⟨by simp only [hκI]; linarith [min_le_left (E + 2) (2 - E)],
    by simp only [hκI]; linarith [min_le_right (E + 2) (2 - E)]⟩
  obtain ⟨C, W₀, hC⟩ := hU.clock b hb hb' κI K T s hκ hs
  set C' := max C 0
  set T' := max T 0
  refine ⟨2 ^ (s - 1) * (1 + (C' * (T' + 1)) ^ s), max W₀ 1, fun W hW e he m hm q hq0 hq1 => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_of_max_le_right hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hcl := hC W (le_of_max_le_left hW) E hEb e he m hm
  set Y := fun ω => (boundaryToInterior b e W m ω)ᴴ * boundaryToInterior b e W m ω
  set f : GrowthPath W → ℝ := fun ω => (W : ℝ)⁻¹ * (Y ω).trace.re
  have hYpsd : ∀ ω, (Y ω).PosSemidef := fun ω => posSemidef_conjTranspose_mul_self _
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω =>
    mul_nonneg (by positivity) (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).1
  have hfun : (fun ω => (W : ℂ)⁻¹ * (Y ω).trace) = fun ω => ((f ω : ℝ) : ℂ) := by
    funext ω
    have him := (Complex.nonneg_iff.mp (hYpsd ω).trace_nonneg).2
    simp only [f, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    congr 1
    exact Complex.ext rfl (by simp [← him])
  rw [hfun] at hcl
  have hcl' : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) (ENNReal.ofReal s) (growthPathLaw W b) ≤
      ENNReal.ofReal (C' * (T' + 1) * W) := by
    refine hcl.trans (ENNReal.ofReal_le_ofReal ?_)
    have hm' : (m : ℝ) ≤ T' * W := hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      hW0.le)
    have : (m : ℝ) + 1 ≤ (T' + 1) * W := by nlinarith
    calc C * ((m : ℝ) + 1) ≤ C' * ((m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C' * ((T' + 1) * W) := mul_le_mul_of_nonneg_left this (le_max_right _ _)
      _ = _ := by ring
  have hmom := indicator_moment_le_of_eLpNorm hf0 hs hcl'
  -- pointwise: `H_p ≤ W + f`
  have hpt : ∀ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ s ≤
      2 ^ (s - 1) * (ENNReal.ofReal ((W : ℝ) ^ s) + ENNReal.ofReal (f ω ^ s)) := by
    intro ω
    have hA := ns_nearClock_posSemidef b e W m q hq0 ω
    have htr := ns_trace_nearClock_le_clock b e W m hq0 hq1 ω
    have htr0 := (trace_nearClock_le b e W m q hq0 ω).1
    have h1 := fracTrace_le_card_rpow_mul_trace_rpow hA hp hp1
    rw [Fintype.card_fin] at h1
    have hWp : (W : ℝ) ^ (1 - p) ≤ W := by
      calc (W : ℝ) ^ (1 - p) ≤ (W : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = W := Real.rpow_one _
    have hxp : (nearClock b e W m q ω).trace.re ^ p ≤ 1 + (nearClock b e W m q ω).trace.re := by
      rcases le_or_gt (nearClock b e W m q ω).trace.re 1 with h | h
      · have := Real.rpow_le_one htr0 h hp.le; linarith
      · have := Real.rpow_le_self_of_one_le h.le hp1; linarith
    have htrf : (nearClock b e W m q ω).trace.re ≤ f ω / W := by
      have : f ω / W = ((W : ℝ) ^ 2)⁻¹ * (Y ω).trace.re := by simp only [f]; field_simp
      rw [this]; exact htr
    have hH : fracTrace p (nearClock b e W m q ω) ≤ W + f ω := by
      calc fracTrace p (nearClock b e W m q ω) ≤ (W : ℝ) ^ (1 - p) *
            (nearClock b e W m q ω).trace.re ^ p := h1
        _ ≤ W * (1 + f ω / W) := by
            gcongr
            exact hxp.trans (by linarith)
        _ = W + f ω := by field_simp
    calc ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ s
        ≤ (ENNReal.ofReal W + ENNReal.ofReal (f ω)) ^ s := by
          gcongr
          rw [← ENNReal.ofReal_add hW0.le (hf0 ω)]
          exact ENNReal.ofReal_le_ofReal hH
      _ ≤ 2 ^ (s - 1) * (ENNReal.ofReal W ^ s + ENNReal.ofReal (f ω) ^ s) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hs
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg hW0.le hs0,
            ENNReal.ofReal_rpow_of_nonneg (hf0 ω) hs0]
  have : IsProbabilityMeasure (growthPathLaw W b) := isProbabilityMeasure_growthPathLaw W b
  calc ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ s ∂growthPathLaw W b
      ≤ ∫⁻ ω, 2 ^ (s - 1) * (ENNReal.ofReal ((W : ℝ) ^ s) + ENNReal.ofReal (f ω ^ s))
          ∂growthPathLaw W b := lintegral_mono hpt
    _ = 2 ^ (s - 1) * (ENNReal.ofReal ((W : ℝ) ^ s) +
          ∫⁻ ω, ENNReal.ofReal (f ω ^ s) ∂growthPathLaw W b) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 2 ^ (s - 1) * (ENNReal.ofReal ((W : ℝ) ^ s) +
          ENNReal.ofReal ((C' * (T' + 1) * W) ^ s)) := by gcongr
    _ = ENNReal.ofReal (2 ^ (s - 1) * (1 + (C' * (T' + 1)) ^ s) * (W : ℝ) ^ s) := by
        have hC0 : 0 ≤ C' * (T' + 1) := mul_nonneg (le_max_right _ _) (by positivity)
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
          ENNReal.ofReal_rpow_of_pos (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow hC0 hW0.le]
        congr 1
        ring

/-- **The window transfer of `E H_p^r`** (uniform form). -/
theorem rhw_window_moment_bound (hU : FullSourceMomentsEnergyUniformContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {K : ℝ} (hK : 0 ≤ K)
    {p r : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hr : 1 ≤ r) {a a' : ℝ} (ha : a.HolderConjugate a') :
    ∃ C₁ : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, |e - E| ≤ K / (W : ℝ) ^ 2 →
      ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ T * W → ∀ q : ℝ → ℝ, (∀ x, 0 ≤ q x) → (∀ x, q x ≤ 1) →
        ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ r ∂growthPathLaw W b ≤
          ENNReal.ofReal C₁ * (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^
              (r * a) ∂growthPathLaw W b) ^ (1 / a) + ENNReal.ofReal (1 / W) := by
  have ha0 : 0 < a := ha.pos
  have hr0 : 0 < r := by linarith
  obtain ⟨C₁, hC₁, hcon⟩ := rhw_window_consts b hb hb' hE1 hE2 hK ha
  refine ⟨C₁ * 2 ^ (p * r), fun T => ?_⟩
  obtain ⟨W₁, hW₁⟩ := hcon T
  obtain ⟨C₂, W₂, hC₂⟩ := rhw_window_poly_bound hU hb hb' hE1 hE2 (K := K) hp hp1
    (s := 2 * r) (by linarith) T
  obtain ⟨W₃, hW₃⟩ := eventually_atTop.mp (rhw_eventually_poly_exp_le C₂ (2 * r))
  refine ⟨max (max W₁ W₂) (max W₃ 1), fun W hW e he m hm1 hm q hq0 hq1 => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW1' : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1'
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨⟨he1, he2⟩, hκ, hpn, hK1⟩ := hW₁ W hW1 e he m hm
  have hmain := rhw_window_moment_le hW1' hm1 hb hb' hE1 hE2 he1 he2 hq0 hp hr0 ha hκ
    (M := 6 * b * W)
  refine hmain.trans (add_le_add ?_ ?_)
  · -- the good event
    have hpn0 : 0 ≤ Complex.normSq (rhwP b E e) := Complex.normSq_nonneg _
    have hfac : (ENNReal.ofReal (Complex.normSq (rhwP b E e) ^ p) ^ (r * a)) ^ (1 / a) ≤
        ENNReal.ofReal (2 ^ (p * r)) := by
      rw [← ENNReal.rpow_mul, show r * a * (1 / a) = r by field_simp,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hpn0 _) hr0.le, ← Real.rpow_mul hpn0]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hpn0 hpn (by positivity))
    calc rhwBlockConst W m b (e - E) (rhwAlpha b E e) (6 * b * W) a' *
          rhwScaleConst W (rhwLam b E e) a' *
          (ENNReal.ofReal (Complex.normSq (rhwP b E e) ^ p) ^ (r * a) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^ (r * a)
              ∂growthPathLaw W b) ^ (1 / a)
        = rhwBlockConst W m b (e - E) (rhwAlpha b E e) (6 * b * W) a' *
          rhwScaleConst W (rhwLam b E e) a' *
          ((ENNReal.ofReal (Complex.normSq (rhwP b E e) ^ p) ^ (r * a)) ^ (1 / a) *
            (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^ (r * a)
              ∂growthPathLaw W b) ^ (1 / a)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (2 ^ (p * r)) *
            (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^ (r * a)
              ∂growthPathLaw W b) ^ (1 / a)) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁]
  · -- the bad event
    have hM : -(6 * b * W / (2 * (b / W))) = -(3 * (W : ℝ) ^ 2) := by
      field_simp; ring
    rw [hM]
    have hpoly := hC₂ W hW2 e he m hm q hq0 hq1
    have h4 := rhw_four_pow_le W
    have hev := hW₃ W hW3
    calc (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ (2 * r)
          ∂growthPathLaw W b) ^ (1 / 2 : ℝ) *
          (4 ^ (W * W) * ENNReal.ofReal (Real.exp (-(3 * (W : ℝ) ^ 2)))) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (C₂ * (W : ℝ) ^ (2 * r)) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.exp (-((W : ℝ) ^ 2))) ^ (1 / 2 : ℝ) := by gcongr
      _ = ENNReal.ofReal (C₂ * (W : ℝ) ^ (2 * r) * Real.exp (-((W : ℝ) ^ 2))) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (1 / (W : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal (1 / W) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, Real.sqrt_sq hW0.le, one_div]

end BlockBand.Endpoints
