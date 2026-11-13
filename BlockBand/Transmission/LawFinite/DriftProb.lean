module

public import BlockBand.Transmission.LawFinite.Interface
public import BlockBand.Transmission.SourceMixing.MassPath

/-!
# The bounded reciprocal of a concentrated variable

* `recipK_le_taylor`: for `m > 0`, every real `x`:
  `r_K(x) ≤ m⁻¹ - (x - m)/m² + 2(x - m)²/m³ + K⁻¹1{x < m/2}`
  (on `x ≥ m/2`: `1/x = 1/m - (x-m)/m² + (x-m)²/(m²x)`; on `x < m/2`: `r_K ≤ K⁻¹`);
* **`integral_recipK_le`**: for `x ≥ 0` with mean `m > 0`, `‖x - m‖₂ ≤ σ₂`, `‖x - m‖_N ≤ σ_N`:
  `E r_K(x) ≤ m⁻¹ + 2σ₂²/m³ + K⁻¹(2σ_N/m)^N` (Taylor on `|x - m| ≤ m/2`; the linear term has
  mean zero; Chebyshev for the complement).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory
open scoped ENNReal

theorem recipK_le_inv (K x : ℝ) : recipK K x ≤ x⁻¹ := min_le_left _ _

theorem recipK_le_inv_K (K x : ℝ) : recipK K x ≤ K⁻¹ := min_le_right _ _

/-- **Pointwise Taylor bound for `r_K`.** -/
theorem recipK_le_taylor {K m : ℝ} (hm : 0 < m) (x : ℝ) :
    recipK K x ≤ m⁻¹ - (x - m) / m ^ 2 + 2 * (x - m) ^ 2 / m ^ 3 +
      Set.indicator {y : ℝ | y < m / 2} (fun _ => K⁻¹) x := by
  by_cases hx : x < m / 2
  · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | y < m / 2} from hx)]
    have h1 : 0 ≤ -(x - m) / m ^ 2 := div_nonneg (by linarith) (by positivity)
    have h2 : 0 ≤ 2 * (x - m) ^ 2 / m ^ 3 := by positivity
    have h3 : 0 < m⁻¹ := inv_pos.mpr hm
    have := recipK_le_inv_K K x
    rw [neg_div] at h1
    linarith
  · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | y < m / 2} from hx), add_zero]
    push Not at hx
    have hx0 : 0 < x := by linarith
    refine (recipK_le_inv K x).trans ?_
    have e : x⁻¹ = m⁻¹ - (x - m) / m ^ 2 + (x - m) ^ 2 / (m ^ 2 * x) := by
      field_simp; ring
    rw [e]
    have : (x - m) ^ 2 / (m ^ 2 * x) ≤ 2 * (x - m) ^ 2 / m ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hs : 0 ≤ (x - m) ^ 2 := sq_nonneg _
      have : m ^ 3 ≤ 2 * (m ^ 2 * x) := by nlinarith
      nlinarith
    linarith

theorem measurable_recipK (K : ℝ) : Measurable (recipK K) :=
  (measurable_id.inv).min measurable_const

/-- **`E r_K(x)` for a concentrated nonnegative variable.** -/
theorem integral_recipK_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : Ω → ℝ} (hx : Measurable x) (hx0 : ∀ ω, 0 ≤ x ω)
    {K m σ₂ σN : ℝ} {N : ℕ} (hN : 1 ≤ N) (hK : 0 < K) (hm : 0 < m) (hσ₂ : 0 ≤ σ₂)
    (hσN : 0 ≤ σN) (hmean : ∫ ω, x ω ∂μ = m)
    (h2 : eLpNorm (fun ω => x ω - m) 2 μ ≤ ENNReal.ofReal σ₂)
    (hNn : eLpNorm (fun ω => x ω - m) N μ ≤ ENNReal.ofReal σN) :
    ∫ ω, recipK K (x ω) ∂μ ≤ m⁻¹ + 2 * σ₂ ^ 2 / m ^ 3 + K⁻¹ * (2 * σN / m) ^ N := by
  set S : Set Ω := {ω | x ω < m / 2}
  have hS : MeasurableSet S := measurableSet_lt hx measurable_const
  have hmem2 : MemLp (fun ω => x ω - m) 2 μ := h2.trans_lt ENNReal.ofReal_lt_top
  have hd : Integrable (fun ω => x ω - m) μ := hmem2.integrable one_le_two
  have hxi : Integrable x μ := by
    exact (hd.add (integrable_const m)).congr (Filter.Eventually.of_forall fun ω => by simp)
  have hsq : Integrable (fun ω => (x ω - m) ^ 2) μ := hmem2.integrable_sq
  -- `g ≤ h`
  have hg : Integrable (fun ω => recipK K (x ω)) μ := by
    refine Integrable.mono' (integrable_const K⁻¹)
      ((measurable_recipK K).comp hx).aestronglyMeasurable (Filter.Eventually.of_forall
      fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, recipK_le_inv_K K (x ω)⟩
    have : 0 ≤ recipK K (x ω) := le_min (inv_nonneg.mpr (hx0 ω)) (inv_nonneg.mpr hK.le)
    have : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
    linarith
  have hI : Integrable (S.indicator fun _ => K⁻¹) μ := (integrable_const _).indicator hS
  have i0 : Integrable (fun _ : Ω => m⁻¹) μ := integrable_const _
  have i1 : Integrable (fun ω => (x ω - m) / m ^ 2) μ := hd.div_const _
  have i2 : Integrable (fun ω => 2 * (x ω - m) ^ 2 / m ^ 3) μ := (hsq.const_mul 2).div_const _
  have i01 : Integrable (fun ω => m⁻¹ - (x ω - m) / m ^ 2) μ := i0.sub i1
  have i012 : Integrable (fun ω => m⁻¹ - (x ω - m) / m ^ 2 + 2 * (x ω - m) ^ 2 / m ^ 3) μ :=
    i01.add i2
  have hh : Integrable (fun ω => m⁻¹ - (x ω - m) / m ^ 2 + 2 * (x ω - m) ^ 2 / m ^ 3 +
      S.indicator (fun _ => K⁻¹) ω) μ := i012.add hI
  have hle := integral_mono hg hh fun ω => by
    have := recipK_le_taylor (K := K) hm (x ω)
    simpa [S, Set.indicator] using this
  refine hle.trans ?_
  -- the integral of `h`
  rw [integral_add i012 hI, integral_add i01 i2, integral_sub i0 i1, integral_div, integral_div,
    integral_const_mul, integral_sub hxi (integrable_const m), integral_const, integral_const,
    hmean, integral_indicator_const _ hS]
  simp only [probReal_univ, smul_eq_mul, one_mul, sub_self, zero_div, sub_zero]
  -- variance
  have hvar : ∫ ω, (x ω - m) ^ 2 ∂μ ≤ σ₂ ^ 2 := by
    have h' : eLpNorm (fun ω => |x ω - m|) (ENNReal.ofReal ((2 : ℕ) : ℝ)) μ ≤
        ENNReal.ofReal σ₂ := by
      rw [ENNReal.ofReal_natCast]
      refine le_trans (le_of_eq ?_) h2
      have e : (fun ω => |x ω - m|) = fun ω => ‖x ω - m‖ := by
        funext ω; rw [Real.norm_eq_abs]
      rw [e, eLpNorm_norm]
      · norm_num
      · exact (hx.sub measurable_const).aestronglyMeasurable
    have := SourceMixing.mp_integral_pow_le (μ := μ) (Filter.Eventually.of_forall
      fun ω => abs_nonneg (x ω - m)) 2 (by norm_num) hσ₂ h'
    simpa [sq_abs] using this
  -- Chebyshev
  have hcheb : μ.real S ≤ (2 * σN / m) ^ N := by
    have hsub : S ⊆ {ω | ENNReal.ofReal (m / 2) ≤ ‖x ω - m‖ₑ} := by
      intro ω hω
      simp only [S, Set.mem_ofPred_eq] at hω ⊢
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (by rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith)
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hc := mul_meas_ge_le_pow_eLpNorm' μ hN0 (ENNReal.natCast_ne_top N)
      (f := fun ω => x ω - m) (ENNReal.ofReal (m / 2))
    simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at hc
    have hc0 : ENNReal.ofReal (m / 2) ^ N * μ S ≤
        ENNReal.ofReal (m / 2) ^ N * μ {ω | ENNReal.ofReal (m / 2) ≤ ‖x ω - m‖ₑ} := by
      gcongr
    have hc1 : eLpNorm (fun ω => x ω - m) N μ ^ N ≤ ENNReal.ofReal σN ^ N := by gcongr
    have hc' : ENNReal.ofReal (m / 2) ^ N * μ S ≤ ENNReal.ofReal σN ^ N :=
      hc0.trans (hc.trans hc1)
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow hσN] at hc'
    have hm2 : 0 < (m / 2) ^ N := by positivity
    have hS' : μ S ≤ ENNReal.ofReal (σN ^ N / (m / 2) ^ N) := by
      rw [ENNReal.ofReal_div_of_pos hm2]
      exact ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hm2).ne')
        (Or.inl ENNReal.ofReal_ne_top) |>.mpr (by rwa [mul_comm])
    have e : σN ^ N / (m / 2) ^ N = (2 * σN / m) ^ N := by
      rw [← div_pow]; congr 1; field_simp
    rw [e] at hS'
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hS'
  have hK0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
  have h3 : 2 * (∫ ω, (x ω - m) ^ 2 ∂μ) / m ^ 3 ≤ 2 * σ₂ ^ 2 / m ^ 3 := by
    have := mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 2)
    exact div_le_div_of_nonneg_right this (by positivity)
  have h4 : μ.real S * K⁻¹ ≤ K⁻¹ * (2 * σN / m) ^ N := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hcheb hK0
  linarith

end BlockBand.Transmission.LawFinite
