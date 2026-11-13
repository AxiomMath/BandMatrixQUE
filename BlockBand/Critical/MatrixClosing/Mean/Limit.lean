module

public import BlockBand.Critical.Collar.Density.RegularWindow

/-!
# Matrix closing, mean clause: the Poisson integration and the limits

Deterministic real analysis (Lebesgue measure on `ℝ`).

* `lintegral_cauchyKernel_two_sided_enn`: for `ρ : ℝ → ℝ≥0∞` with
  `ofReal(c - A) ≤ ρ ≤ ofReal(c + A)` on `|x| ≤ σ` and `∫P₁ρ ≤ T`:
  `c - A - ν(1+σ⁻²)c ≤ ∫P_νρ ≤ c + A + ν(1+σ⁻²)T` (`P_ν ≤ ν(1+σ⁻²)P₁` off the window).
* `tendsto_of_window_bound`: `|a_N - L| ≤ K(x_N + Bσ + y_N(1+σ⁻²))` for all `σ ∈ (0, s₀]`
  eventually, `x_N, y_N → 0`, imply `a_N → L`.
* `polVec`, `entry_eq_polarization`: `M_ij = ¼Σ_k conj(i^k)(e_i + i^k e_j)*M(e_i + i^k e_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix Filter Topology
open BlockBand.Critical.WeightedDensity
open scoped ENNReal

theorem cauchyKernel_neg (ε x : ℝ) : cauchyKernel ε (-x) = cauchyKernel ε x := by
  simp [cauchyKernel]

theorem lintegral_ofReal_cauchyKernel' {ν : ℝ} (hν : 0 < ν) :
    ∫⁻ x, ENNReal.ofReal (cauchyKernel ν x) = 1 := by
  have h := Collar.Density.lintegral_ofReal_cauchyKernel hν
  simpa [zero_sub, cauchyKernel_neg] using h

/-- **Two-sided Cauchy average of an extended-real window estimate.** If
`ofReal(c - A) ≤ ρ(x) ≤ ofReal(c + A)` for `|x| ≤ σ` and `∫P₁ρ ≤ T`, then for `ν > 0`
`c - A - ν(1+σ⁻²)c ≤ ∫P_νρ ≤ c + A + ν(1+σ⁻²)T`. -/
theorem lintegral_cauchyKernel_two_sided_enn {ρ : ℝ → ℝ≥0∞} {c A σ ν T : ℝ} (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hσ : 0 < σ) (hν : 0 < ν) (hT0 : 0 ≤ T)
    (hwin : ∀ x, |x| ≤ σ → ENNReal.ofReal (c - A) ≤ ρ x ∧ ρ x ≤ ENNReal.ofReal (c + A))
    (hT : ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 x) * ρ x ≤ ENNReal.ofReal T) :
    ENNReal.ofReal (c - A - ν * (1 + σ⁻¹ ^ 2) * c) ≤
        ∫⁻ x, ENNReal.ofReal (cauchyKernel ν x) * ρ x ∧
      ∫⁻ x, ENNReal.ofReal (cauchyKernel ν x) * ρ x ≤
        ENNReal.ofReal (c + A + ν * (1 + σ⁻¹ ^ 2) * T) := by
  set k := ν * (1 + σ⁻¹ ^ 2) with hkdef
  have hk0 : 0 ≤ k := by positivity
  have hP0 : ∀ ε x, 0 < ε → 0 ≤ cauchyKernel ε x := fun ε x h => cauchyKernel_nonneg h.le x
  have hmP : ∀ ε, 0 < ε → Measurable fun x : ℝ => ENNReal.ofReal (cauchyKernel ε x) :=
    fun ε hε => ((continuous_cauchyKernel hε).measurable).ennreal_ofReal
  constructor
  · have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ν x) * ENNReal.ofReal (c - A) ≤
        ENNReal.ofReal (cauchyKernel ν x) * ρ x +
          ENNReal.ofReal (cauchyKernel 1 x) * ENNReal.ofReal (k * c) := by
      intro x
      by_cases hx : |x| ≤ σ
      · exact le_add_right (mul_le_mul' le_rfl (hwin x hx).1)
      · push Not at hx
        have ht := Collar.Density.cauchyKernel_le_tail hν hσ (x := x) hx.le
        refine le_add_left ?_
        rw [← ENNReal.ofReal_mul (hP0 ν x hν), ← ENNReal.ofReal_mul (hP0 1 x one_pos)]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases le_or_gt (c - A) 0 with h | h
        · have : cauchyKernel ν x * (c - A) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hP0 ν x hν) h
          have : 0 ≤ cauchyKernel 1 x * (k * c) := by
            have := hP0 1 x one_pos; positivity
          linarith
        · calc cauchyKernel ν x * (c - A) ≤ cauchyKernel ν x * c :=
                mul_le_mul_of_nonneg_left (by linarith) (hP0 ν x hν)
            _ ≤ k * cauchyKernel 1 x * c := mul_le_mul_of_nonneg_right ht hc
            _ = _ := by ring
    have hint := lintegral_mono (μ := volume) hpt
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel' hν, one_mul,
      lintegral_add_right _ ((hmP 1 one_pos).mul_const _),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel' one_pos,
      one_mul] at hint
    rw [ENNReal.ofReal_sub _ (by positivity)]
    exact tsub_le_iff_right.2 hint
  · have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ν x) * ρ x ≤
        ENNReal.ofReal (cauchyKernel ν x) * ENNReal.ofReal (c + A) +
          ENNReal.ofReal k * (ENNReal.ofReal (cauchyKernel 1 x) * ρ x) := by
      intro x
      by_cases hx : |x| ≤ σ
      · exact le_add_right (mul_le_mul' le_rfl (hwin x hx).2)
      · push Not at hx
        have ht := Collar.Density.cauchyKernel_le_tail hν hσ (x := x) hx.le
        refine le_add_left ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk0]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht) le_rfl
    calc ∫⁻ x, ENNReal.ofReal (cauchyKernel ν x) * ρ x
        ≤ ∫⁻ x, (ENNReal.ofReal (cauchyKernel ν x) * ENNReal.ofReal (c + A) +
            ENNReal.ofReal k * (ENNReal.ofReal (cauchyKernel 1 x) * ρ x)) := lintegral_mono hpt
      _ = ENNReal.ofReal (c + A) + ENNReal.ofReal k *
            ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 x) * ρ x := by
          rw [lintegral_add_left ((hmP ν hν).mul_const _),
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_cauchyKernel' hν,
            one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (c + A) + ENNReal.ofReal k * ENNReal.ofReal T := by gcongr
      _ ≤ ENNReal.ofReal (c + A + k * T) := by
          rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_add (by linarith) (by positivity)]

/-- **The window limit.** If `|a_N - L| ≤ K(x_N + Bσ + y_N(1 + σ⁻²))` eventually, for every
`σ ∈ (0, s₀]`, with `x_N, y_N → 0`, then `a_N → L` (first `W → ∞`, then `σ ↓ 0`). -/
theorem tendsto_of_window_bound {a x y : ℕ → ℝ} {L K B s₀ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hs₀ : 0 < s₀) (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto y atTop (𝓝 0))
    (hbound : ∀ᶠ N in atTop, ∀ σ, 0 < σ → σ ≤ s₀ →
      |a N - L| ≤ K * (x N + B * σ + y N * (1 + σ⁻¹ ^ 2))) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set σ : ℝ := min s₀ (ε / (4 * (K + 1) * (B + 1))) with hσdef
  have hσ : 0 < σ := lt_min hs₀ (by positivity)
  have hσs : σ ≤ s₀ := min_le_left _ _
  set k : ℝ := 1 + σ⁻¹ ^ 2
  have hk : 0 < k := by positivity
  have hx' := hx.eventually (Metric.ball_mem_nhds 0 (by positivity :
    0 < ε / (4 * (K + 1))))
  have hy' := hy.eventually (Metric.ball_mem_nhds 0 (by positivity :
    0 < ε / (4 * (K + 1) * k)))
  filter_upwards [hbound, hx', hy'] with N hN hxN hyN
  rw [Real.dist_eq]
  have h := hN σ hσ hσs
  simp only [Real.dist_eq, sub_zero] at hxN hyN
  have h1 : K * x N ≤ K * (ε / (4 * (K + 1))) :=
    mul_le_mul_of_nonneg_left (le_of_lt (lt_of_le_of_lt (le_abs_self _) hxN)) hK
  have h1' : K * (ε / (4 * (K + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : K * (B * σ) ≤ ε / 4 := by
    have hσle : σ ≤ ε / (4 * (K + 1) * (B + 1)) := min_le_right _ _
    have : K * (B * σ) ≤ (K + 1) * (B + 1) * σ := by
      have : K * B ≤ (K + 1) * (B + 1) := by nlinarith
      nlinarith
    have h3 : (K + 1) * (B + 1) * σ ≤ (K + 1) * (B + 1) * (ε / (4 * (K + 1) * (B + 1))) :=
      mul_le_mul_of_nonneg_left hσle (by positivity)
    have h4 : (K + 1) * (B + 1) * (ε / (4 * (K + 1) * (B + 1))) = ε / 4 := by
      field_simp
    linarith
  have h3 : K * (y N * k) ≤ ε / 4 := by
    have hyk : y N * k ≤ ε / (4 * (K + 1) * k) * k :=
      mul_le_mul_of_nonneg_right (le_of_lt (lt_of_le_of_lt (le_abs_self _) hyN)) hk.le
    have h5 : ε / (4 * (K + 1) * k) * k = ε / (4 * (K + 1)) := by field_simp
    have h6 : K * (ε / (4 * (K + 1))) ≤ ε / 4 := h1'
    calc K * (y N * k) ≤ K * (ε / (4 * (K + 1))) := by
          rw [← h5]; exact mul_le_mul_of_nonneg_left hyk hK
      _ ≤ ε / 4 := h6
  have : K * (x N + B * σ + y N * k) = K * x N + K * (B * σ) + K * (y N * k) := by ring
  linarith

/-!
## Polarization of matrix entries
-/

/-- The polarization vectors `e_i + i^k e_j`, `k < 4`. -/
def polVec {r : ℕ} (i j : Fin r) (k : Fin 4) : Fin r → ℂ :=
  Pi.single i 1 + (Complex.I ^ (k : ℕ)) • Pi.single j 1

theorem quad_single_add_smul {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (c : ℂ) :
    star (Pi.single i 1 + c • Pi.single j 1 : Fin r → ℂ) ⬝ᵥ
        (M *ᵥ (Pi.single i 1 + c • Pi.single j 1)) =
      M i i + c * M i j + star c * M j i + star c * c * M j j := by
  simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, Pi.star_single, star_one, single_dotProduct,
    mulVec_single_one, smul_eq_mul, one_mul, Matrix.col_apply]
  ring

/-- **Polarization**: `M_ij = ¼ Σ_k conj(i^k) (e_i + i^k e_j)*M(e_i + i^k e_j)`. -/
theorem entry_eq_polarization {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    M i j = (1 / 4 : ℂ) * ∑ k : Fin 4, star (Complex.I ^ (k : ℕ)) *
      (star (polVec i j k) ⬝ᵥ (M *ᵥ polVec i j k)) := by
  simp only [polVec, quad_single_add_smul, Fin.sum_univ_four]
  have e0 : Complex.I ^ ((0 : Fin 4) : ℕ) = 1 := by simp
  have e1 : Complex.I ^ ((1 : Fin 4) : ℕ) = Complex.I := by simp
  have e2 : Complex.I ^ ((2 : Fin 4) : ℕ) = -1 := by
    rw [show ((2 : Fin 4) : ℕ) = 2 from rfl, Complex.I_sq]
  have e3 : Complex.I ^ ((3 : Fin 4) : ℕ) = -Complex.I := by
    rw [show ((3 : Fin 4) : ℕ) = 3 from rfl, pow_succ, Complex.I_sq]; ring
  have sI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  rw [e0, e1, e2, e3]
  simp only [star_one, star_neg, sI, neg_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

end BlockBand.Critical.MatrixClosing.Mean
