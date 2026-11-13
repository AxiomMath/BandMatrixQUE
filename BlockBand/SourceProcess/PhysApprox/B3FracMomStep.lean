module

public import BlockBand.SourceProcess.PhysApprox.B3FracMomLift
public import BlockBand.Transmission.SourceMixing.Fluctuation

/-!
# The fresh-layer fourth-power step on regular states

* the tangent bound `0 ≤ P' ≤ P + κ Σ_i w_i (Re Z_ii - 1)` (`layer_pointwise`, gap dropped,
  `ae_stepFrac_eq`);
* `X = C e P + κ L_c`, `L_c = Σ_i w_i Re u_i*(U - Ū)u_i` (centred), so that `P' ≤ P + X` with
  `E X = C e P` (diagonal `meanForm_bulk`);
* `E L_c² ≤ P²C₂²/W`, `E L_c⁴ ≤ P⁴C₄⁴/W²` (`oneStepFluctuation_holds` at `p = 2, 4` and weighted
  Cauchy–Schwarz);
* the lift `lift_four_expand`, and the first-moment gap of `layerStep_bulk`.

**`step4_onDomain`**: `E P'⁴ ≤ P⁴ + (4Ce + 17C²e² + 24C⁴e⁴ + 17κ²C₂²/W + 24κ⁴C₄⁴/W²)P⁴
- (c/8W)P³ℓ²` on regular states.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.FracMom

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.FractionalBulk BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem bilinear_sub_re (u : Fin W → ℂ) (A B : Matrix (Fin W) (Fin W) ℂ) :
    (bilinear u (A - B) u).re = (bilinear u A u).re - (bilinear u B u).re := by
  simp [bilinear, Matrix.sub_mulVec, dotProduct_sub]

/-- Even moments of the real part from an `L^n` bound. -/
theorem re_pow_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℂ} (hf : Measurable f) {n : ℕ} (hn : 1 ≤ n) (he : Even n) {C : ℝ} (hC : 0 ≤ C)
    (h : eLpNorm f (ENNReal.ofReal n) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => (f ω).re ^ n) μ ∧ ∫ ω, (f ω).re ^ n ∂μ ≤ C ^ n := by
  obtain ⟨hi, hb⟩ := powN_of_eLpNorm (f := fun ω => ‖f ω‖) hf.norm.aestronglyMeasurable
    (fun _ => norm_nonneg _) hn hC (by rwa [eLpNorm_norm _ hf.aestronglyMeasurable])
  have hpt : ∀ ω, (f ω).re ^ n ≤ ‖f ω‖ ^ n := fun ω => by
    rw [← he.pow_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) n
  have hint : Integrable (fun ω => (f ω).re ^ n) μ :=
    Integrable.mono' hi ((Complex.measurable_re.comp hf).pow_const n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (he.pow_nonneg _)]; exact hpt ω)
  exact ⟨hint, (integral_mono hint hi hpt).trans hb⟩

/-- Linearity of the integral of a five-term bound. -/
theorem integral_lin4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f₁ f₂ f₃ f₄ : Ω → ℝ} (a₀ a₁ a₂ a₃ a₄ : ℝ) (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ)
    (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ) :
    ∫ ω, (a₀ + a₁ * f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω + a₄ * f₄ ω) ∂μ =
      a₀ + a₁ * (∫ ω, f₁ ω ∂μ) + a₂ * (∫ ω, f₂ ω ∂μ) + a₃ * (∫ ω, f₃ ω ∂μ) +
        a₄ * (∫ ω, f₄ ω ∂μ) := by
  have i1 := h₁.const_mul a₁
  have i2 := h₂.const_mul a₂
  have i3 := h₃.const_mul a₃
  have i4 := h₄.const_mul a₄
  have j1 : Integrable (fun ω => a₀ + a₁ * f₁ ω) μ := (integrable_const a₀).add i1
  have j2 : Integrable (fun ω => a₀ + a₁ * f₁ ω + a₂ * f₂ ω) μ := j1.add i2
  have j3 : Integrable (fun ω => a₀ + a₁ * f₁ ω + a₂ * f₂ ω + a₃ * f₃ ω) μ := j2.add i3
  rw [integral_add j3 i4, integral_add j2 i3, integral_add j1 i2,
    integral_add (integrable_const a₀) i1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const]
  simp

theorem div_sqrt_pow_two {C Wr : ℝ} (hW : 0 ≤ Wr) : (C / Real.sqrt Wr) ^ 2 = C ^ 2 / Wr := by
  rw [div_pow, Real.sq_sqrt hW]

theorem div_sqrt_pow_four {C Wr : ℝ} (hW : 0 ≤ Wr) : (C / Real.sqrt Wr) ^ 4 = C ^ 4 / Wr ^ 2 := by
  rw [div_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul (Real.sqrt Wr), Real.sq_sqrt hW]

/-- The centred fluctuation `L_c = Σ_i t_i^α Re u_i*(U - Ū)u_i` of one fresh layer. -/
def fracLc (α b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {T : Matrix (Fin W) (Fin W) ℂ}
    (hT : T.PosSemidef) (y : LayerSample W .oneBlockOnePort) : ℝ :=
  ∑ i, ts_lam hT i ^ α * (bilinear (ts_vec hT i)
    (freshU b E X y - matrixExpect (freshLaw W b) (freshU b E X)) (ts_vec hT i)).re

set_option maxHeartbeats 1000000 in
/-- **Moments of `L_c`**: centred, `E L_c² ≤ P²C₂²/W`, `E L_c⁴ ≤ P⁴C₄⁴/W²`. -/
theorem fracLc_moments {α b E : ℝ} (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) {Cf2 Cf4 : ℝ} (hCf2 : 0 ≤ Cf2)
    (hCf4 : 0 ≤ Cf4) (hU : ∀ x y, Integrable (fun ω => freshU b E X ω x y) (freshLaw W b))
    (hfl2 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf2 / Real.sqrt W * vecNorm u * vecNorm v))
    (hfl4 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 4) (freshLaw W b) ≤
      ENNReal.ofReal (Cf4 / Real.sqrt W * vecNorm u * vecNorm v)) :
    Integrable (fracLc α b E X hT) (freshLaw W b) ∧ ∫ y, fracLc α b E X hT y ∂freshLaw W b = 0 ∧
      Integrable (fun y => fracLc α b E X hT y ^ 2) (freshLaw W b) ∧
      ∫ y, fracLc α b E X hT y ^ 2 ∂freshLaw W b ≤ (∑ i, ts_lam hT i ^ α) ^ 2 * (Cf2 ^ 2 / W) ∧
      Integrable (fun y => fracLc α b E X hT y ^ 4) (freshLaw W b) ∧
      ∫ y, fracLc α b E X hT y ^ 4 ∂freshLaw W b ≤
        (∑ i, ts_lam hT i ^ α) ^ 4 * (Cf4 ^ 4 / W ^ 2) := by
  set ν := freshLaw W b
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWp : (0 : ℝ) < W := by linarith
  set EU := matrixExpect ν (freshU b E X)
  set w : Fin W → ℝ := fun i => ts_lam hT i ^ α with hwdef
  have hw0 : ∀ i, 0 ≤ w i := fun i => Real.rpow_nonneg (ts_lam_nonneg hT i) α
  set P := ∑ i, w i with hPdef
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => hw0 i
  set Y : Fin W → LayerSample W .oneBlockOnePort → ℝ :=
    fun i y => (bilinear (ts_vec hT i) (freshU b E X y - EU) (ts_vec hT i)).re with hYdef
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    Complex.measurable_re.comp (measurable_bilinear_centered b E X EU _ _)
  have hLcdef : fracLc α b E X hT = fun y => ∑ i, w i * Y i y := rfl
  rw [hLcdef]
  have hLcm : Measurable fun y => ∑ i, w i * Y i y :=
    Finset.measurable_sum _ fun i _ => (hYm i).const_mul _
  have hY2 : ∀ i, Integrable (fun y => Y i y ^ 2) ν ∧
      ∫ y, Y i y ^ 2 ∂ν ≤ (Cf2 / Real.sqrt W) ^ 2 :=
    fun i => re_pow_moment (measurable_bilinear_centered b E X EU _ _) (by norm_num)
      (by norm_num) (by positivity) (by
        have h := hfl2 (ts_vec hT i) (ts_vec hT i)
        rw [ts_vecNorm, mul_one, mul_one] at h
        simpa using h)
  have hY4 : ∀ i, Integrable (fun y => Y i y ^ 4) ν ∧
      ∫ y, Y i y ^ 4 ∂ν ≤ (Cf4 / Real.sqrt W) ^ 4 :=
    fun i => re_pow_moment (measurable_bilinear_centered b E X EU _ _) (by norm_num)
      (by decide) (by positivity) (by
        have h := hfl4 (ts_vec hT i) (ts_vec hT i)
        rw [ts_vecNorm, mul_one, mul_one] at h
        simpa using h)
  have hZi : ∀ i, Integrable (fun y => (bilinear (ts_vec hT i) (freshU b E X y)
      (ts_vec hT i)).re) ν := fun i => (integrable_bilinear_of hU _ _).re
  have hYeq : ∀ i y, Y i y = (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re -
      (bilinear (ts_vec hT i) EU (ts_vec hT i)).re := fun i y => bilinear_sub_re _ _ _
  have hYi : ∀ i, Integrable (Y i) ν := fun i =>
    ((hZi i).sub (integrable_const _)).congr (Filter.Eventually.of_forall fun y => (hYeq i y).symm)
  have hY0 : ∀ i, ∫ y, Y i y ∂ν = 0 := fun i => by
    simp_rw [hYeq i]
    rw [integral_sub (hZi i) (integrable_const _), integral_const, integral_re_bilinear hT hU i]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    exact sub_self _
  have hLci : Integrable (fun y => ∑ i, w i * Y i y) ν :=
    integrable_finsetSum _ fun i _ => (hYi i).const_mul _
  have hLc0 : ∫ y, ∑ i, w i * Y i y ∂ν = 0 := by
    rw [integral_finsetSum _ fun i _ => (hYi i).const_mul _]
    simp [integral_const_mul, hY0]
  have hQ2i : Integrable (fun y => ∑ i, w i * Y i y ^ 2) ν :=
    integrable_finsetSum _ fun i _ => (hY2 i).1.const_mul _
  have hQ4i : Integrable (fun y => ∑ i, w i * Y i y ^ 4) ν :=
    integrable_finsetSum _ fun i _ => (hY4 i).1.const_mul _
  have hLc2pt : ∀ y, (∑ i, w i * Y i y) ^ 2 ≤ P * ∑ i, w i * Y i y ^ 2 := fun y =>
    sq_wsum_le _ w (fun i => Y i y) hw0
  have hLc4pt : ∀ y, (∑ i, w i * Y i y) ^ 4 ≤ P ^ 3 * ∑ i, w i * Y i y ^ 4 := fun y =>
    pow_four_wsum_le _ w (fun i => Y i y) hw0
  have hLc2i : Integrable (fun y => (∑ i, w i * Y i y) ^ 2) ν :=
    Integrable.mono' (hQ2i.const_mul P) (hLcm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hLc2pt y)
  have hLc4i : Integrable (fun y => (∑ i, w i * Y i y) ^ 4) ν :=
    Integrable.mono' (hQ4i.const_mul (P ^ 3)) (hLcm.pow_const 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hLc4pt y)
  refine ⟨hLci, hLc0, hLc2i, ?_, hLc4i, ?_⟩
  · calc ∫ y, (∑ i, w i * Y i y) ^ 2 ∂ν ≤ ∫ y, P * ∑ i, w i * Y i y ^ 2 ∂ν :=
          integral_mono hLc2i (hQ2i.const_mul P) hLc2pt
      _ = P * ∑ i, w i * ∫ y, Y i y ^ 2 ∂ν := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (hY2 i).1.const_mul _]
          simp [integral_const_mul]
      _ ≤ P * ∑ i, w i * (Cf2 / Real.sqrt W) ^ 2 := by
          gcongr with i
          · exact hw0 i
          · exact (hY2 i).2
      _ = P ^ 2 * (Cf2 ^ 2 / W) := by
          rw [← Finset.sum_mul, div_sqrt_pow_two hWp.le]; ring
  · calc ∫ y, (∑ i, w i * Y i y) ^ 4 ∂ν ≤ ∫ y, P ^ 3 * ∑ i, w i * Y i y ^ 4 ∂ν :=
          integral_mono hLc4i (hQ4i.const_mul _) hLc4pt
      _ = P ^ 3 * ∑ i, w i * ∫ y, Y i y ^ 4 ∂ν := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (hY4 i).1.const_mul _]
          simp [integral_const_mul]
      _ ≤ P ^ 3 * ∑ i, w i * (Cf4 / Real.sqrt W) ^ 4 := by
          gcongr with i
          · exact hw0 i
          · exact (hY4 i).2
      _ = P ^ 4 * (Cf4 ^ 4 / W ^ 2) := by
          rw [← Finset.sum_mul, div_sqrt_pow_four hWp.le]; ring

/-- **The tangent bound**: a.s. `P' ≤ P + (C e P + κ L_c)`. -/
theorem stepFrac_le_tangent {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) (hT : (passiveTransmission b E X).PosSemidef)
    {Cm C : ℝ} (hCm : cP α * jP α * Cm ≤ C)
    (hmean : ∀ v : Fin W → ℂ, vecNorm v = 1 →
      (bilinear v (matrixExpect (freshLaw W b) (freshU b E X)) v).re ≤
        1 + Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) :
    ∀ᵐ y ∂freshLaw W b, stepFrac α b E X y ≤ fracTrace α (passiveTransmission b E X) +
      (C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * fracTrace α (passiveTransmission b E X) +
        cP α * jP α * fracLc α b E X hT y) := by
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 with hedef
  have he0 : 0 ≤ e := add_nonneg (norm_nonneg _) (by positivity)
  set EU := matrixExpect (freshLaw W b) (freshU b E X)
  have hPeq := fracTrace_eq_sum_ts hT α
  set P := fracTrace α (passiveTransmission b E X)
  have hP0 : 0 ≤ P := fracTrace_nonneg' _ _
  have hκ0 : 0 ≤ cP α * jP α := mul_nonneg (cP_pos hα0 hα1).le (jP_nonneg α)
  have hw0 : ∀ i, 0 ≤ ts_lam hT i ^ α := fun i => Real.rpow_nonneg (ts_lam_nonneg hT i) α
  have hmsum : ∑ i, ts_lam hT i ^ α * ((bilinear (ts_vec hT i) EU (ts_vec hT i)).re - 1) ≤
      Cm * e * P := by
    rw [hPeq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hmean (ts_vec hT i) (ts_vecNorm hT i)
    have h' : (bilinear (ts_vec hT i) EU (ts_vec hT i)).re - 1 ≤ Cm * e := by linarith
    calc ts_lam hT i ^ α * ((bilinear (ts_vec hT i) EU (ts_vec hT i)).re - 1) ≤
          ts_lam hT i ^ α * (Cm * e) := mul_le_mul_of_nonneg_left h' (hw0 i)
      _ = Cm * e * ts_lam hT i ^ α := by ring
  have hκC : cP α * jP α * (Cm * e * P) ≤ C * e * P := by
    have := mul_le_mul_of_nonneg_right hCm (mul_nonneg he0 hP0)
    linarith
  have hmsum' := mul_le_mul_of_nonneg_left hmsum hκ0
  filter_upwards [ae_stepFrac_eq hα0 hα1 hb0 hb hW h1 h2 hX hT] with y hy
  have hlp := layer_pointwise hα0 hα1 hT hT1 b E X y
  have hgap : 0 ≤ ∑ i, ∑ j, gapG α hT b E X i j y :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => gapG_nonneg α hT b E X i j y
  have hcP : 0 ≤ cP α / 27 := (div_pos (cP_pos hα0 hα1) (by norm_num)).le
  have hsum : ∑ i, ts_lam hT i ^ α *
      ((bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re - 1) =
      fracLc α b E X hT y +
        ∑ i, ts_lam hT i ^ α * ((bilinear (ts_vec hT i) EU (ts_vec hT i)).re - 1) := by
    rw [fracLc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bilinear_sub_re]; ring
  rw [hy]
  refine hlp.trans ?_
  rw [hsum, ← hPeq]
  linarith [mul_nonneg hcP hgap]

/-- **The integrated lift** (abstract): from `0 ≤ S ≤ P + (CeP + κL)` a.s., `E L = 0`,
`E L² ≤ P²A₂`, `E L⁴ ≤ P⁴A₄` and `E S ≤ (1 + Ce)P - (c/W)ℓ²`. -/
theorem step4_integrate {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {S L : Ω → ℝ} {P C e κ cl ℓ Wr A₂ A₄ : ℝ} (hP0 : 0 ≤ P)
    (hS0 : ∀ y, 0 ≤ S y) (hSi : Integrable S ν) (hS4i : Integrable (fun y => S y ^ 4) ν)
    (hLi : Integrable L ν) (hL0 : ∫ y, L y ∂ν = 0) (hL2i : Integrable (fun y => L y ^ 2) ν)
    (hL2 : ∫ y, L y ^ 2 ∂ν ≤ P ^ 2 * A₂) (hL4i : Integrable (fun y => L y ^ 4) ν)
    (hL4 : ∫ y, L y ^ 4 ∂ν ≤ P ^ 4 * A₄) (hpt : ∀ᵐ y ∂ν, S y ≤ P + (C * e * P + κ * L y))
    (hstep : ∫ y, S y ∂ν ≤ (1 + C * e) * P - cl / Wr * ℓ ^ 2) :
    ∫ y, S y ^ 4 ∂ν ≤ P ^ 4 + (4 * C * e + 17 * C ^ 2 * e ^ 2 + 24 * C ^ 4 * e ^ 4 +
      17 * κ ^ 2 * A₂ + 24 * κ ^ 4 * A₄) * P ^ 4 - cl / (8 * Wr) * P ^ 3 * ℓ ^ 2 := by
  have hfin : ∀ᵐ y ∂ν, S y ^ 4 ≤ (7 / 8 * P ^ 4 + 31 / 8 * P ^ 3 * (C * e * P) +
      17 * P ^ 2 * (C * e * P) ^ 2 + 24 * (C * e * P) ^ 4) + 31 / 8 * P ^ 3 * κ * L y +
      17 * P ^ 2 * κ ^ 2 * L y ^ 2 + 24 * κ ^ 4 * L y ^ 4 + 1 / 8 * P ^ 3 * S y := by
    filter_upwards [hpt] with y hy
    have hl := lift_four_expand hP0 (hS0 y) hy
    have hx2 : (C * e * P + κ * L y) ^ 2 ≤ 2 * (C * e * P) ^ 2 + 2 * (κ ^ 2 * L y ^ 2) := by
      nlinarith [sq_nonneg (C * e * P - κ * L y)]
    have hx4 : (C * e * P + κ * L y) ^ 4 ≤ 8 * ((C * e * P) ^ 4 + κ ^ 4 * L y ^ 4) := by
      have h := pow4_add_le (C * e * P) (κ * L y)
      have e4 : (κ * L y) ^ 4 = κ ^ 4 * L y ^ 4 := mul_pow _ _ _
      rw [e4] at h
      exact h
    have k2 := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 17 / 2 * P ^ 2)
    have k4 := mul_le_mul_of_nonneg_left hx4 (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have hRi : Integrable (fun y => (7 / 8 * P ^ 4 + 31 / 8 * P ^ 3 * (C * e * P) +
      17 * P ^ 2 * (C * e * P) ^ 2 + 24 * (C * e * P) ^ 4) + 31 / 8 * P ^ 3 * κ * L y +
      17 * P ^ 2 * κ ^ 2 * L y ^ 2 + 24 * κ ^ 4 * L y ^ 4 + 1 / 8 * P ^ 3 * S y) ν :=
    (((((integrable_const _).add (hLi.const_mul _)).add (hL2i.const_mul _)).add
      (hL4i.const_mul _)).add (hSi.const_mul _))
  have hle := integral_mono_ae hS4i hRi hfin
  rw [integral_lin4 _ _ _ _ _ hLi hL2i hL4i hSi, hL0] at hle
  have k1 := mul_le_mul_of_nonneg_left hL2 (by positivity : (0 : ℝ) ≤ 17 * P ^ 2 * κ ^ 2)
  have k2 := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ 24 * κ ^ 4)
  have k3 := mul_le_mul_of_nonneg_left hstep (by positivity : (0 : ℝ) ≤ 1 / 8 * P ^ 3)
  have e1 : (7 / 8 * P ^ 4 + 31 / 8 * P ^ 3 * (C * e * P) + 17 * P ^ 2 * (C * e * P) ^ 2 +
      24 * (C * e * P) ^ 4) + 17 * P ^ 2 * κ ^ 2 * (P ^ 2 * A₂) + 24 * κ ^ 4 * (P ^ 4 * A₄) +
      1 / 8 * P ^ 3 * ((1 + C * e) * P - cl / Wr * ℓ ^ 2) =
      P ^ 4 + (4 * C * e + 17 * C ^ 2 * e ^ 2 + 24 * C ^ 4 * e ^ 4 + 17 * κ ^ 2 * A₂ +
        24 * κ ^ 4 * A₄) * P ^ 4 - cl / (8 * Wr) * P ^ 3 * ℓ ^ 2 := by ring
  rw [← e1]
  linarith

/-- **The fourth-power step on regular states** (the fractional moment step at `q = 4`). -/
theorem step4_onDomain {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : (passiveY X).PosSemidef) {Cm Cl cl C Cf2 Cf4 : ℝ}
    (hCm : cP α * jP α * Cm ≤ C) (hCl : Cl ≤ C) (hCf2 : 0 ≤ Cf2) (hCf4 : 0 ≤ Cf4)
    (hU : ∀ x y, Integrable (fun ω => freshU b E X ω x y) (freshLaw W b))
    (hmean : ∀ v : Fin W → ℂ, vecNorm v = 1 →
      (bilinear v (matrixExpect (freshLaw W b) (freshU b E X)) v).re ≤
        1 + Cm * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2))
    (hstep : ∫ y, stepFrac α b E X y ∂freshLaw W b ≤
      (1 + Cl * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * fracTrace α (passiveTransmission b E X) -
        cl / W * lowFrac α (passiveTransmission b E X) ^ 2)
    (hfl2 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal (Cf2 / Real.sqrt W * vecNorm u * vecNorm v))
    (hfl4 : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (freshU b E X ω -
        matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal 4) (freshLaw W b) ≤
      ENNReal.ofReal (Cf4 / Real.sqrt W * vecNorm u * vecNorm v)) :
    ∫ y, stepFrac α b E X y ^ 4 ∂freshLaw W b ≤
      fracTrace α (passiveTransmission b E X) ^ 4 +
        (4 * C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) +
          17 * C ^ 2 * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 2 +
          24 * C ^ 4 * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 4 +
          17 * (cP α * jP α) ^ 2 * (Cf2 ^ 2 / W) + 24 * (cP α * jP α) ^ 4 * (Cf4 ^ 4 / W ^ 2)) *
          fracTrace α (passiveTransmission b E X) ^ 4 -
        cl / (8 * W) * fracTrace α (passiveTransmission b E X) ^ 3 *
          lowFrac α (passiveTransmission b E X) ^ 2 := by
  have hT := passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hX
  obtain ⟨hLci, hLc0, hLc2i, hLc2, hLc4i, hLc4⟩ :=
    fracLc_moments (α := α) hW hT hCf2 hCf4 hU hfl2 hfl4
  have hPeq := fracTrace_eq_sum_ts hT α
  rw [← hPeq] at hLc2 hLc4
  have hpt := stepFrac_le_tangent hα0 hα1 hb0 hb h1 h2 hW hX hT hCm hmean
  have he0 : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 := add_nonneg (norm_nonneg _) (by positivity)
  have hP0 : 0 ≤ fracTrace α (passiveTransmission b E X) := fracTrace_nonneg' _ _
  have hSm : Measurable fun y => stepFrac α b E X y := by
    have h := (measurable_stepFrac (W := W) α b E).comp (measurable_prodMk_left (x := X))
    exact h
  have hS0 : ∀ y, 0 ≤ stepFrac α b E X y := fun y => stepFrac_nonneg _ _ _ _ _
  have hSW : ∀ y, stepFrac α b E X y ≤ W := fun y => stepFrac_le _ _ _ _ _
  have hSi : Integrable (fun y => stepFrac α b E X y) (freshLaw W b) :=
    Integrable.of_bound hSm.aestronglyMeasurable W
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hS0 y)]; exact hSW y)
  have hS4i : Integrable (fun y => stepFrac α b E X y ^ 4) (freshLaw W b) :=
    Integrable.of_bound (hSm.pow_const 4).aestronglyMeasurable ((W : ℝ) ^ 4)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (pow_nonneg (hS0 y) 4)]
        exact pow_le_pow_left₀ (hS0 y) (hSW y) 4)
  have hstep' : ∫ y, stepFrac α b E X y ∂freshLaw W b ≤
      (1 + C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) * fracTrace α (passiveTransmission b E X) -
        cl / W * lowFrac α (passiveTransmission b E X) ^ 2 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl he0) hP0
    linarith
  exact step4_integrate (S := fun y => stepFrac α b E X y) (L := fracLc α b E X hT)
    (P := fracTrace α (passiveTransmission b E X)) (C := C)
    (e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) (κ := cP α * jP α) (cl := cl)
    (ℓ := lowFrac α (passiveTransmission b E X)) (Wr := W) (A₂ := Cf2 ^ 2 / W)
    (A₄ := Cf4 ^ 4 / W ^ 2) hP0 hS0 hSi hS4i hLci hLc0 hLc2i hLc2 hLc4i hLc4
    hpt hstep'

end BlockBand.SourceProcess.PhysApprox.B3.FracMom
