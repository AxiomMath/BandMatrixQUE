module

public import BlockBand.Endpoints.Response.RemoteHigherWindowClock

/-!
# The window transfer with uniform constants

The transfer of clock moments from the energy `E` to an energy `e` in the window
`|e - E| ≤ K/W²` (`rhw_window_moment_le`) involves a Gaussian likelihood ratio, a Ginibre
rescaling and a bad-event remainder. This file bounds these constants uniformly on the window
(`rhw_window_consts`), together with the real inequalities used for them.
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

/-!
## Real inequalities
-/

theorem rhw_neg_log_one_add_le {x : ℝ} (hx : |x| ≤ 1 / 2) : -Real.log (1 + x) ≤ 2 * |x| := by
  have h1 : 0 < 1 + x := by linarith [neg_abs_le x]
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : x / (1 + x) ≥ -(2 * |x|) := by
    have hx' : -(1 / 2) ≤ x := by linarith [neg_abs_le x]
    rcases le_or_gt 0 x with h | h
    · have : 0 ≤ x / (1 + x) := div_nonneg h h1.le
      linarith [abs_nonneg x]
    · rw [abs_of_neg h, ge_iff_le, le_div_iff₀ h1]
      nlinarith
  have h4 : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  linarith

/-- The Ginibre rescaling base: `λ^{-a'}(1 - a'(1 - λ⁻²))^{-1/2} ≤ e^{3a'ε}` when
`|λ² - 1| ≤ ε ≤ 1/(4a')`. -/
theorem rhw_scaleBase_le {lam a' ε : ℝ} (hlam : 0 < lam) (ha' : 1 ≤ a')
    (hε : |lam ^ 2 - 1| ≤ ε) (hε1 : ε ≤ 1 / (4 * a')) :
    0 < 1 - a' * (1 - (lam ^ 2)⁻¹) ∧
      lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (3 * a' * ε) := by
  set x := lam ^ 2 - 1 with hx
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hε
  have h4a : 1 / (4 * a') ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hxq : |x| ≤ 1 / 4 := hε.trans (hε1.trans h4a)
  have hl2 : lam ^ 2 = 1 + x := by rw [hx]; ring
  have h1x : 3 / 4 ≤ 1 + x := by linarith [neg_abs_le x]
  have hinv : 1 - (lam ^ 2)⁻¹ = x / (1 + x) := by rw [hl2]; field_simp; ring
  set y := -(a' * (x / (1 + x))) with hy
  have hκ : 1 - a' * (1 - (lam ^ 2)⁻¹) = 1 + y := by rw [hinv, hy]; ring
  have hya : |y| ≤ 2 * a' * |x| := by
    rw [hy, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < a'), abs_div,
      abs_of_pos (by linarith : (0 : ℝ) < 1 + x)]
    have : |x| / (1 + x) ≤ 2 * |x| := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg x]
    calc a' * (|x| / (1 + x)) ≤ a' * (2 * |x|) := by gcongr
      _ = 2 * a' * |x| := by ring
  have hy2 : |y| ≤ 1 / 2 := by
    refine hya.trans ?_
    have : 2 * a' * |x| ≤ 2 * a' * (1 / (4 * a')) := by gcongr; exact hε.trans hε1
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have hκpos : 0 < 1 + y := by linarith [neg_abs_le y]
  refine ⟨hκ ▸ hκpos, ?_⟩
  rw [hκ, Real.rpow_def_of_pos hlam, Real.rpow_def_of_pos hκpos, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log lam = Real.log (1 + x) / 2 := by
    rw [← hl2, Real.log_pow]; push_cast; ring
  have hA := rhw_neg_log_one_add_le (x := x) (hxq.trans (by norm_num))
  have hB := rhw_neg_log_one_add_le hy2
  rw [hlog]
  have hxe : |x| ≤ ε := hε
  nlinarith [abs_nonneg x, abs_nonneg y]

theorem rhw_scaleConst_le {W : ℕ} {lam a' ε : ℝ} (hlam : 0 < lam) (ha' : 1 ≤ a')
    (hε : |lam ^ 2 - 1| ≤ ε) (hε1 : ε ≤ 1 / (4 * a')) :
    rhwScaleConst W lam a' ≤ ENNReal.ofReal (Real.exp (12 * (W : ℝ) ^ 2 * ε)) := by
  obtain ⟨-, hB⟩ := rhw_scaleBase_le hlam ha' hε hε1
  have ha0 : 0 < a' := by linarith
  unfold rhwScaleConst
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc (ENNReal.ofReal (lam ^ (-a') * (1 - a' * (1 - (lam ^ 2)⁻¹)) ^ (-(1 / 2 : ℝ))) ^
        (2 * (W * (W * 2)))) ^ (1 / a')
      ≤ (ENNReal.ofReal (Real.exp (3 * a' * ε)) ^ (2 * (W * (W * 2)))) ^ (1 / a') := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (12 * (W : ℝ) ^ 2 * ε)) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul]
        congr 2
        push_cast
        field_simp
        ring

/-- `4^{W²} e^{-3W²} ≤ e^{-W²}`. -/
theorem rhw_four_pow_le (W : ℕ) :
    (4 : ℝ≥0∞) ^ (W * W) * ENNReal.ofReal (Real.exp (-(3 * (W : ℝ) ^ 2))) ≤
      ENNReal.ofReal (Real.exp (-((W : ℝ) ^ 2))) := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hc : (4 : ℝ≥0∞) ^ (W * W) = ENNReal.ofReal ((4 : ℝ) ^ (W * W)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [hc, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (4 : ℝ) ^ (W * W) * Real.exp (-(3 * (W : ℝ) ^ 2))
      ≤ Real.exp 2 ^ (W * W) * Real.exp (-(3 * (W : ℝ) ^ 2)) := by gcongr
    _ = Real.exp (-((W : ℝ) ^ 2)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring

/-- `C W^k (e^{-W²}) ≤ 1/W²` for all large `W`. -/
theorem rhw_eventually_poly_exp_le (C k : ℝ) :
    ∀ᶠ W : ℕ in atTop, C * (W : ℝ) ^ k * Real.exp (-((W : ℝ) ^ 2)) ≤ 1 / (W : ℝ) ^ 2 := by
  set n : ℕ := ⌈k⌉₊ + 2 with hn
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    ((tendsto_pow_atTop (two_ne_zero)).comp tendsto_natCast_atTop_atTop)
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (max C 0 + 1) by positivity))
  filter_upwards [hev, eventually_ge_atTop 1] with W hW hW1
  simp only [Function.comp_apply] at hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have hpow : (W : ℝ) ^ k * (W : ℝ) ^ 2 ≤ ((W : ℝ) ^ 2) ^ n := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hW0]
    refine Real.rpow_le_rpow_of_exponent_le hW1' ?_
    have := Nat.le_ceil k
    push_cast [hn]
    linarith
  have he : 0 < Real.exp (-((W : ℝ) ^ 2)) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity)]
  have hC : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
  have h1 : ((W : ℝ) ^ 2) ^ n * Real.exp (-((W : ℝ) ^ 2)) * (max C 0 + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hW; linarith
  calc C * (W : ℝ) ^ k * Real.exp (-((W : ℝ) ^ 2)) * (W : ℝ) ^ 2
      ≤ (max C 0 + 1) * ((W : ℝ) ^ k * (W : ℝ) ^ 2) * Real.exp (-((W : ℝ) ^ 2)) := by
        have : 0 ≤ (W : ℝ) ^ k * (W : ℝ) ^ 2 := by positivity
        nlinarith [mul_nonneg this he.le]
    _ ≤ (max C 0 + 1) * ((W : ℝ) ^ 2) ^ n * Real.exp (-((W : ℝ) ^ 2)) := by
        gcongr
    _ ≤ 1 := by linarith

/-!
## Uniform constants on the window
-/

/-- The likelihood constants are uniformly bounded on the window. -/
theorem rhw_window_consts (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E)
    (hE2 : E < 2) {K : ℝ} (hK : 0 ≤ K) {a a' : ℝ} (ha : a.HolderConjugate a') :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ,
      |e - E| ≤ K / (W : ℝ) ^ 2 → ∀ m : ℕ, (m : ℝ) ≤ T * W →
        (-2 < e ∧ e < 2) ∧ 0 < 1 - a' * (1 - (rhwLam b E e ^ 2)⁻¹) ∧
          Complex.normSq (rhwP b E e) ≤ 2 ∧
          rhwBlockConst W m b (e - E) (rhwAlpha b E e) (6 * b * W) a' *
            rhwScaleConst W (rhwLam b E e) a' ≤ ENNReal.ofReal C₁ := by
  have hb1 : b < 1 := by linarith
  have ha' : 1 < a' := ha.symm.lt
  obtain ⟨L, η, hL, hη, hlip⟩ := rhw_params_lipschitz b hb1 hE1 hE2
  -- continuity of `|p|²` at `E`
  have hcont := ((Complex.continuous_normSq.continuousAt).comp
    (rhw_continuousAt_p b hb1 hE1 hE2))
  have hpE : Complex.normSq (rhwP b E E) = 1 := by rw [rhw_p_self b hb1 hE1 hE2]; simp
  obtain ⟨η₂, hη₂, hp2⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
  refine ⟨2 * Real.exp (12 * L * K), by positivity, fun T => ?_⟩
  set T' := max T 0
  set D := (a' - 1) * (2 * T' * K ^ 2 + 4 * L ^ 2 * K ^ 2 * (6 * b) ^ 2) / (2 * (1 - 2 * b))
  have hKW : Tendsto (fun W : ℕ => K / (W : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := K)).div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  have hDW : Tendsto (fun W : ℕ => D / (W : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := D)).div_atTop tendsto_natCast_atTop_atTop
  have hev := ((hKW.eventually (gt_mem_nhds (lt_min hη hη₂))).and
    ((hKW.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * a') / (L + 1) by positivity))).and
      ((hDW.eventually (gt_mem_nhds (Real.log_pos one_lt_two))).and
        (eventually_ge_atTop 1))))
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp hev
  refine ⟨W₀, fun W hW e he m hm => ?_⟩
  obtain ⟨h1, h2, h3, hW1⟩ := hW₀ W hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have heη : |e - E| < η := he.trans_lt (h1.trans_le (min_le_left _ _))
  have heη₂ : |e - E| < η₂ := he.trans_lt (h1.trans_le (min_le_right _ _))
  obtain ⟨⟨he1, he2⟩, hlam2, halpha⟩ := hlip e heη
  have hlampos := rhw_lam_pos hb1 hE1 hE2 he1 he2
  have hlsq := rhw_lam_sq hb1 hE1 hE2 he1 he2
  set ε := L * (K / (W : ℝ) ^ 2)
  have hεdef : |rhwLam b E e ^ 2 - 1| ≤ ε := by
    rw [hlsq]; exact hlam2.trans (mul_le_mul_of_nonneg_left he hL)
  have hε1 : ε ≤ 1 / (4 * a') := by
    have : K / (W : ℝ) ^ 2 * (L + 1) < 1 / (4 * a') := by
      rw [lt_div_iff₀ (by positivity)] at h2; linarith
    have hK0 : 0 ≤ K / (W : ℝ) ^ 2 := by positivity
    nlinarith
  obtain ⟨hκ, -⟩ := rhw_scaleBase_le hlampos ha'.le hεdef hε1
  refine ⟨⟨he1, he2⟩, hκ, ?_, ?_⟩
  · have := hp2 (show dist e E < η₂ by rwa [Real.dist_eq])
    simp only [Function.comp_apply, Real.dist_eq, hpE] at this
    linarith [abs_lt.mp this]
  · have hsc := rhw_scaleConst_le (W := W) hlampos ha'.le hεdef hε1
    have hεW : 12 * (W : ℝ) ^ 2 * ε = 12 * L * K := by
      simp only [ε]; field_simp
    rw [hεW] at hsc
    have hblk : rhwBlockConst W m b (e - E) (rhwAlpha b E e) (6 * b * W) a' ≤
        ENNReal.ofReal 2 := by
      unfold rhwBlockConst
      refine ENNReal.ofReal_le_ofReal ?_
      have hδ2 : (e - E) ^ 2 ≤ K ^ 2 / (W : ℝ) ^ 4 := by
        rw [← sq_abs, show (W : ℝ) ^ 4 = ((W : ℝ) ^ 2) ^ 2 by ring, ← div_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) he 2
      have hα2 : rhwAlpha b E e ^ 2 ≤ L ^ 2 * K ^ 2 / (W : ℝ) ^ 4 := by
        rw [← sq_abs, show L ^ 2 * K ^ 2 / (W : ℝ) ^ 4 = (L * (K / (W : ℝ) ^ 2)) ^ 2 by
          rw [mul_pow, div_pow]; ring]
        exact pow_le_pow_left₀ (abs_nonneg _) (halpha.trans
          (mul_le_mul_of_nonneg_left he hL)) 2
      have hmT : (m : ℝ) ≤ T' * W := hm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        hW0.le)
      have hT' : 0 ≤ T' := le_max_right _ _
      have h12 : 0 < 1 - 2 * b := by linarith
      have hkey : (a' - 1) * (2 * m * W * (e - E) ^ 2 + 4 * rhwAlpha b E e ^ 2 *
          (6 * b * W) ^ 2) / (2 * ((1 - 2 * b) / W)) ≤ D / W := by
        rw [div_le_div_iff₀ (by positivity) hW0]
        have hA : 2 * m * W * (e - E) ^ 2 ≤ 2 * T' * K ^ 2 / W ^ 2 := by
          have : 2 * (m : ℝ) * W * (e - E) ^ 2 ≤ 2 * (T' * W) * W * (K ^ 2 / (W : ℝ) ^ 4) := by
            gcongr
          refine this.trans (le_of_eq ?_)
          field_simp
        have hB : 4 * rhwAlpha b E e ^ 2 * (6 * b * W) ^ 2 ≤
            4 * L ^ 2 * K ^ 2 * (6 * b) ^ 2 / W ^ 2 := by
          have : 4 * rhwAlpha b E e ^ 2 * (6 * b * W) ^ 2 ≤
              4 * (L ^ 2 * K ^ 2 / (W : ℝ) ^ 4) * (6 * b * W) ^ 2 := by gcongr
          refine this.trans (le_of_eq ?_)
          field_simp
        have hsum : 2 * m * W * (e - E) ^ 2 + 4 * rhwAlpha b E e ^ 2 * (6 * b * W) ^ 2 ≤
            (2 * T' * K ^ 2 + 4 * L ^ 2 * K ^ 2 * (6 * b) ^ 2) / W ^ 2 := by
          rw [add_div]; linarith
        have ha1 : 0 ≤ a' - 1 := by linarith
        calc (a' - 1) * (2 * m * W * (e - E) ^ 2 + 4 * rhwAlpha b E e ^ 2 * (6 * b * W) ^ 2) *
              W ≤ (a' - 1) * ((2 * T' * K ^ 2 + 4 * L ^ 2 * K ^ 2 * (6 * b) ^ 2) / W ^ 2) * W := by
                gcongr
          _ = D * (2 * ((1 - 2 * b) / W)) := by
                simp only [D]; field_simp
      exact (Real.exp_le_exp.mpr (hkey.trans h3.le)).trans (Real.exp_log (by norm_num)).le
    calc rhwBlockConst W m b (e - E) (rhwAlpha b E e) (6 * b * W) a' *
          rhwScaleConst W (rhwLam b E e) a'
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (12 * L * K)) := by gcongr
      _ = ENNReal.ofReal (2 * Real.exp (12 * L * K)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]

end BlockBand.Endpoints
