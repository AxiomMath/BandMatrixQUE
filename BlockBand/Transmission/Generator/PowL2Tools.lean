module

public import BlockBand.Transmission.Generator.DriftOne

/-!
# `L²` tools for the `k ≥ 2` drift error

* `amgm4`: `xyzw ≤ x⁴ + y⁴ + z⁴ + w⁴` (`x, y, z, w ≥ 0`);
* `eLpNorm_two_le_sqrt`: `∫f² ≤ A`, `f² ∈ L¹` ⇒ `‖f‖₂ ≤ √A`;
* `shifted_moment`: `‖f‖_n ≤ σ/c` (`f ≥ 0`) ⇒ `(cf + 1)ⁿ ∈ L¹`, `∫(cf + 1)ⁿ ≤ 2ⁿ(σⁿ + 1)`;
* **`l2_prod4`**: `|Z| ≤ K·xyzw/s³ + Δv/s²` a.s., with eighth moments of `x, y, z, w` and the
  second moment of `v`, gives `‖Z‖₂ ≤ K√(M_x+M_y+M_z+M_w)/s³ + Δ√M_v/s²` (Minkowski + `amgm4`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter
open BlockBand.Transmission.SourceMixing
open scoped ENNReal NNReal

theorem amgm4 {x y z w : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    x * y * z * w ≤ x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 := by
  have h1 : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
  have h2 : z * w ≤ (z ^ 2 + w ^ 2) / 2 := by nlinarith [sq_nonneg (z - w)]
  have h3 : x * y * (z * w) ≤ (x ^ 2 + y ^ 2) / 2 * ((z ^ 2 + w ^ 2) / 2) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : (x ^ 2 + y ^ 2) / 2 * ((z ^ 2 + w ^ 2) / 2) ≤
      ((x ^ 2 + y ^ 2) ^ 2 + (z ^ 2 + w ^ 2) ^ 2) / 8 := by
    nlinarith [sq_nonneg ((x ^ 2 + y ^ 2) - (z ^ 2 + w ^ 2))]
  have h5 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  have h6 : (z ^ 2 + w ^ 2) ^ 2 ≤ 2 * (z ^ 4 + w ^ 4) := by nlinarith [sq_nonneg (z ^ 2 - w ^ 2)]
  have h7 : 0 ≤ x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 := by positivity
  rw [show x * y * z * w = x * y * (z * w) by ring]
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem eLpNorm_two_le_sqrt {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hi : Integrable (fun ω => f ω ^ 2) μ) {A : ℝ} (hI : ∫ ω, f ω ^ 2 ∂μ ≤ A) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt A) := by
  have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf).mpr hi
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2]
  have heq : ∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ = ∫ ω, f ω ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun ω => by
      show ‖f ω‖ ^ (2 : ℝ) = f ω ^ 2
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs])
  rw [heq]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hI

/-- **Shifted moments from an `L^n` bound.** -/
theorem shifted_moment {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hf0 : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (n : ℕ) (hn : 1 ≤ n) {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (h : eLpNorm f (ENNReal.ofReal (n : ℝ)) μ ≤ ENNReal.ofReal (σ / c)) :
    Integrable (fun ω => (c * f ω + 1) ^ n) μ ∧
      ∫ ω, (c * f ω + 1) ^ n ∂μ ≤ 2 ^ n * (σ ^ n + 1) := by
  have hmem : MemLp f n μ := by
    have h' := h
    rw [ENNReal.ofReal_natCast] at h'
    exact h'.trans_lt ENNReal.ofReal_lt_top
  have hcf : MemLp (fun ω => c * f ω) n μ := hmem.const_mul c
  have hi : Integrable (fun ω => ‖c * f ω‖ ^ n) μ := hcf.integrable_norm_pow'
  have hi' : Integrable (fun ω => (c * f ω) ^ n) μ := by
    refine hi.congr ?_
    filter_upwards [hf0] with ω h0
    rw [Real.norm_of_nonneg (by positivity)]
  have hdom : Integrable (fun ω => 2 ^ n * ((c * f ω) ^ n + 1)) μ :=
    (hi'.add (integrable_const 1)).const_mul _
  have hm : AEStronglyMeasurable (fun ω => (c * f ω + 1) ^ n) μ :=
    ((hf.const_mul c).add aestronglyMeasurable_const).pow n
  have hpt : ∀ᵐ ω ∂μ, (c * f ω + 1) ^ n ≤ 2 ^ n * ((c * f ω) ^ n + 1) := by
    filter_upwards [hf0] with ω h0 using pow_add_one_le (by positivity) n
  have hI : Integrable (fun ω => (c * f ω + 1) ^ n) μ := by
    refine Integrable.mono' hdom hm ?_
    filter_upwards [hf0, hpt] with ω h0 h1
    rw [Real.norm_of_nonneg (by positivity)]; exact h1
  refine ⟨hI, ?_⟩
  have hmom := moment_scaled hf0 n hn hσ hc h
  calc ∫ ω, (c * f ω + 1) ^ n ∂μ ≤ ∫ ω, 2 ^ n * ((c * f ω) ^ n + 1) ∂μ :=
        integral_mono_ae hI hdom hpt
    _ = 2 ^ n * (∫ ω, (c * f ω) ^ n ∂μ + 1) := by
        rw [integral_const_mul, integral_add hi' (integrable_const 1)]; simp
    _ ≤ 2 ^ n * (σ ^ n + 1) := by gcongr

omit [IsProbabilityMeasure μ] in
/-- **`L²` bound from a four-factor product.** -/
theorem l2_prod4 {Z x y z w v : Ω → ℝ} (hZ : AEStronglyMeasurable Z μ)
    (hx : AEStronglyMeasurable x μ) (hy : AEStronglyMeasurable y μ)
    (hz : AEStronglyMeasurable z μ) (hw : AEStronglyMeasurable w μ)
    (hv : AEStronglyMeasurable v μ) (hx0 : ∀ᵐ ω ∂μ, 0 ≤ x ω) (hy0 : ∀ᵐ ω ∂μ, 0 ≤ y ω)
    (hz0 : ∀ᵐ ω ∂μ, 0 ≤ z ω) (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) {K Δ s Mx My Mz Mw Mv : ℝ}
    (hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (hs : 0 < s)
    (hZb : ∀ᵐ ω ∂μ, |Z ω| ≤ K * (x ω * y ω * z ω * w ω) / s ^ 3 + Δ * v ω / s ^ 2)
    (ix : Integrable (fun ω => x ω ^ 8) μ) (iy : Integrable (fun ω => y ω ^ 8) μ)
    (iz : Integrable (fun ω => z ω ^ 8) μ) (iw : Integrable (fun ω => w ω ^ 8) μ)
    (iv : Integrable (fun ω => v ω ^ 2) μ)
    (mx : ∫ ω, x ω ^ 8 ∂μ ≤ Mx) (my : ∫ ω, y ω ^ 8 ∂μ ≤ My) (mz : ∫ ω, z ω ^ 8 ∂μ ≤ Mz)
    (mw : ∫ ω, w ω ^ 8 ∂μ ≤ Mw) (mv : ∫ ω, v ω ^ 2 ∂μ ≤ Mv) :
    eLpNorm Z 2 μ ≤ ENNReal.ofReal (K * Real.sqrt (Mx + My + Mz + Mw) / s ^ 3 +
      Δ * Real.sqrt Mv / s ^ 2) := by
  set P : Ω → ℝ := fun ω => x ω * y ω * z ω * w ω
  set f₁ : Ω → ℝ := fun ω => K * P ω / s ^ 3
  set f₂ : Ω → ℝ := fun ω => Δ * v ω / s ^ 2
  have hP : AEStronglyMeasurable P μ := ((hx.mul hy).mul hz).mul hw
  have h1m : AEStronglyMeasurable f₁ μ := by
    have := (hP.const_mul K).mul_const (s ^ 3)⁻¹
    simpa only [f₁, div_eq_mul_inv] using this
  have h2m : AEStronglyMeasurable f₂ μ := by
    have := (hv.const_mul Δ).mul_const (s ^ 2)⁻¹
    simpa only [f₂, div_eq_mul_inv] using this
  have i2' : Integrable (fun ω => x ω ^ 8 + y ω ^ 8) μ := ix.add iy
  have i3' : Integrable (fun ω => x ω ^ 8 + y ω ^ 8 + z ω ^ 8) μ := i2'.add iz
  have hS : Integrable (fun ω => x ω ^ 8 + y ω ^ 8 + z ω ^ 8 + w ω ^ 8) μ := i3'.add iw
  have hP2 : ∀ᵐ ω ∂μ, P ω ^ 2 ≤ x ω ^ 8 + y ω ^ 8 + z ω ^ 8 + w ω ^ 8 := by
    filter_upwards [hx0, hy0, hz0, hw0] with ω a b c d
    have := amgm4 (sq_nonneg (x ω)) (sq_nonneg (y ω)) (sq_nonneg (z ω)) (sq_nonneg (w ω))
    simp only [P]
    calc (x ω * y ω * z ω * w ω) ^ 2 = x ω ^ 2 * y ω ^ 2 * z ω ^ 2 * w ω ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have iP : Integrable (fun ω => P ω ^ 2) μ := by
    refine Integrable.mono' hS (hP.pow 2) ?_
    filter_upwards [hP2] with ω h
    rw [Real.norm_of_nonneg (sq_nonneg _)]; exact h
  have hc1 : 0 ≤ K ^ 2 / s ^ 6 := by positivity
  have e1 : ∀ ω, f₁ ω ^ 2 = K ^ 2 / s ^ 6 * P ω ^ 2 := fun ω => by
    simp only [f₁]; field_simp
  have e2 : ∀ ω, f₂ ω ^ 2 = Δ ^ 2 / s ^ 4 * v ω ^ 2 := fun ω => by
    simp only [f₂]; field_simp
  have i1 : Integrable (fun ω => f₁ ω ^ 2) μ := by
    simp only [e1]; exact iP.const_mul _
  have i2 : Integrable (fun ω => f₂ ω ^ 2) μ := by
    simp only [e2]; exact iv.const_mul _
  have hMx : ∫ ω, P ω ^ 2 ∂μ ≤ Mx + My + Mz + Mw := by
    refine (integral_mono_ae iP hS hP2).trans ?_
    rw [integral_add i3' iw, integral_add i2' iz, integral_add ix iy]
    linarith
  have b1 : eLpNorm f₁ 2 μ ≤ ENNReal.ofReal (K * Real.sqrt (Mx + My + Mz + Mw) / s ^ 3) := by
    have hM0 : 0 ≤ Mx + My + Mz + Mw :=
      (integral_nonneg fun ω => sq_nonneg (P ω)).trans hMx
    refine (eLpNorm_two_le_sqrt h1m i1 (A := K ^ 2 / s ^ 6 * (Mx + My + Mz + Mw)) ?_).trans
      (le_of_eq ?_)
    · simp only [e1]; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hMx hc1
    · congr 1
      rw [Real.sqrt_mul hc1, Real.sqrt_div (sq_nonneg K), Real.sqrt_sq hK,
        show s ^ 6 = (s ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      ring
  have b2 : eLpNorm f₂ 2 μ ≤ ENNReal.ofReal (Δ * Real.sqrt Mv / s ^ 2) := by
    have hc2 : 0 ≤ Δ ^ 2 / s ^ 4 := by positivity
    refine (eLpNorm_two_le_sqrt h2m i2 (A := Δ ^ 2 / s ^ 4 * Mv) ?_).trans (le_of_eq ?_)
    · simp only [e2]; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left mv hc2
    · congr 1
      rw [Real.sqrt_mul hc2, Real.sqrt_div (sq_nonneg Δ), Real.sqrt_sq hΔ,
        show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      ring
  have hZF : eLpNorm Z 2 μ ≤ eLpNorm (f₁ + f₂) 2 μ := by
    refine eLpNorm_mono_ae hZ ?_
    filter_upwards [hZb, hx0, hy0, hz0, hw0] with ω h a b c d
    rw [Real.norm_eq_abs]
    refine h.trans (le_trans (le_of_eq rfl) (le_abs_self _))
  refine hZF.trans ((eLpNorm_add_le (by norm_num)).trans ?_)
  refine (add_le_add b1 b2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end BlockBand.Transmission.Generator
