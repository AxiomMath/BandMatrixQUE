module

public import BlockBand.Critical.Herglotz.ProductMoments
public import BlockBand.Critical.Herglotz.GaussianQuad

/-!
# Smooth cutoffs of the canonical quadratic form and its `L²` estimate at `iY`

The smooth cutoff of the quadratic form of the canonical series is
`S_L(z) = v^* 𝖢_r^{(L)}(z) v = π⁻¹ Σ_j χ_L(x_j) |v^* g_j|² / (x_j - z)`, with
`χ_L(x) = max(0, min(1, L + 1 - |x|))` (`= 1` on `[-L, L]`, `= 0` off `(-L-1, L+1)`).
Law: `Ξ` a decorated sine process (`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`,
Lebesgue measure in `x`; `‖v‖² = Σ_i |v_i|²` (Euclidean).

* `smoothCutoff`, `poissonKernel` (`Y / (π (x² + Y²))`, total mass `1`).
* `smoothQuadCauchy ξ L v z = ∫ χ_L(x) π⁻¹ |v^* g|² (x - z)⁻¹ dξ`.
* `smoothQuadCauchy_L2` — for `Y > 0` and every `L ≥ 0`: a.s. integrability and
  `E |S_L(iY) - i ‖v‖²|² ≤ 4 (π Y)⁻¹ ∫ |v^* g|⁴ dγ + ‖v‖⁴ (1 - ∫ χ_L P_Y)²`, where `P_Y` is the
  Poisson kernel; `tendsto_integral_smoothCutoff_mul_poissonKernel`: `∫ χ_L P_Y → 1`
  as `L → ∞`. Hence `lim_{Y→∞} limsup_{L→∞} E |S_L(iY) - i ‖v‖²|² = 0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

/-!
## The cutoff
-/

/-- `χ_L(x) = max(0, min(1, L + 1 - |x|))`. -/
def smoothCutoff (L x : ℝ) : ℝ := max 0 (min 1 (L + 1 - |x|))

theorem smoothCutoff_nonneg (L x : ℝ) : 0 ≤ smoothCutoff L x := le_max_left _ _

theorem smoothCutoff_le_one (L x : ℝ) : smoothCutoff L x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_smoothCutoff (L : ℝ) : Continuous (smoothCutoff L) := by
  unfold smoothCutoff
  exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem smoothCutoff_neg (L x : ℝ) : smoothCutoff L (-x) = smoothCutoff L x := by
  simp [smoothCutoff]

theorem smoothCutoff_eq_one {L x : ℝ} (h : |x| ≤ L) : smoothCutoff L x = 1 := by
  unfold smoothCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem smoothCutoff_eq_zero {L x : ℝ} (h : L + 1 ≤ |x|) : smoothCutoff L x = 0 := by
  unfold smoothCutoff
  rw [max_eq_left]
  exact min_le_of_right_le (by linarith)

theorem hasCompactSupport_smoothCutoff (L : ℝ) : HasCompactSupport (smoothCutoff L) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (L + 1)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact smoothCutoff_eq_zero hx.le

theorem smoothCutoff_mono {L L' : ℝ} (h : L ≤ L') (x : ℝ) :
    smoothCutoff L x ≤ smoothCutoff L' x :=
  max_le_max le_rfl (min_le_min le_rfl (by linarith))

/-- `χ_L(x) → 1` as `L → ∞`. -/
theorem tendsto_smoothCutoff (x : ℝ) :
    Tendsto (fun L : ℝ => smoothCutoff L x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' ((eventually_ge_atTop |x|).mono fun _ hL =>
    (smoothCutoff_eq_one hL).symm)

/-!
## The Poisson kernel
-/

/-- Poisson kernel of the upper half-plane at `iY`: `P_Y(x) = Y / (π (x² + Y²))`. -/
def poissonKernel (Y x : ℝ) : ℝ := Y / (Real.pi * (x ^ 2 + Y ^ 2))

theorem poissonKernel_eq_cauchyPDFReal {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    poissonKernel Y x = ProbabilityTheory.cauchyPDFReal 0 Y.toNNReal x := by
  rw [ProbabilityTheory.cauchyPDFReal_def, Real.coe_toNNReal _ hY.le]
  simp only [poissonKernel, sub_zero]
  field_simp

theorem integrable_poissonKernel {Y : ℝ} (hY : 0 < Y) : Integrable (poissonKernel Y) := by
  have : poissonKernel Y = ProbabilityTheory.cauchyPDFReal 0 Y.toNNReal :=
    funext (poissonKernel_eq_cauchyPDFReal hY)
  rw [this]
  exact ProbabilityTheory.integrable_cauchyPDFReal 0

theorem integral_poissonKernel {Y : ℝ} (hY : 0 < Y) : ∫ x, poissonKernel Y x = 1 := by
  have : poissonKernel Y = ProbabilityTheory.cauchyPDFReal 0 Y.toNNReal :=
    funext (poissonKernel_eq_cauchyPDFReal hY)
  rw [this]
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one 0 (Real.toNNReal_pos.2 hY).ne'

theorem poissonKernel_nonneg {Y : ℝ} (hY : 0 < Y) (x : ℝ) : 0 ≤ poissonKernel Y x := by
  unfold poissonKernel; positivity

theorem continuous_poissonKernel {Y : ℝ} (hY : 0 < Y) : Continuous (poissonKernel Y) := by
  unfold poissonKernel
  refine continuous_const.div (continuous_const.mul ((continuous_pow 2).add continuous_const))
    fun x => ?_
  have : 0 < x ^ 2 + Y ^ 2 := by positivity
  positivity

/-- `∫ χ_L P_Y → 1` as `L → ∞` (dominated convergence, `χ_L P_Y ≤ P_Y`). -/
theorem tendsto_integral_smoothCutoff_mul_poissonKernel {Y : ℝ} (hY : 0 < Y) :
    Tendsto (fun L : ℝ => ∫ x, smoothCutoff L x * poissonKernel Y x) atTop (𝓝 1) := by
  rw [← integral_poissonKernel hY]
  refine tendsto_integral_filter_of_dominated_convergence (poissonKernel Y)
    (Eventually.of_forall fun L =>
      ((continuous_smoothCutoff L).mul (continuous_poissonKernel hY)).aestronglyMeasurable)
    (Eventually.of_forall fun L => Eventually.of_forall fun x => ?_)
    (integrable_poissonKernel hY) (Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (smoothCutoff_nonneg L x)
      (poissonKernel_nonneg hY x))]
    exact mul_le_of_le_one_left (poissonKernel_nonneg hY x) (smoothCutoff_le_one L x)
  · simpa using (tendsto_smoothCutoff x).mul_const (poissonKernel Y x)

/-!
## The smooth cutoff of the canonical quadratic form
-/

variable {r : ℕ}

/-- `S_L(z) = v^* 𝖢_r^{(L)}(z) v = ∫ χ_L(x) π⁻¹ |v^* g|² (x - z)⁻¹ dξ(x, g)` (smooth cutoff of
the quadratic form of the canonical Cauchy series; Lean's `0⁻¹ = 0` at a real pole). -/
def smoothQuadCauchy (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (L : ℝ) (v : Fin r → ℂ)
    (z : ℂ) : ℂ :=
  ∫ p, ((smoothCutoff L p.1 * quadMark v p.2 / Real.pi : ℝ) : ℂ) * ((p.1 : ℂ) - z)⁻¹
    ∂ξ.measure

/-- Real-part weight `χ_L(x) x / (π (x² + Y²))`. -/
def cutoffReWeight (L Y x : ℝ) : ℝ := smoothCutoff L x * (x / (Real.pi * (x ^ 2 + Y ^ 2)))

/-- Imaginary-part weight `χ_L(x) Y / (π (x² + Y²)) = χ_L P_Y`. -/
def cutoffImWeight (L Y x : ℝ) : ℝ := smoothCutoff L x * poissonKernel Y x

theorem smoothQuadCauchy_integrand_eq {Y : ℝ} (hY : 0 < Y) (L : ℝ) (v : Fin r → ℂ)
    (p : ℝ × (Fin r → ℂ)) :
    ((smoothCutoff L p.1 * quadMark v p.2 / Real.pi : ℝ) : ℂ) * ((p.1 : ℂ) - Y * Complex.I)⁻¹ =
      ((cutoffReWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ) +
        ((cutoffImWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ) * Complex.I := by
  have hpos : 0 < p.1 ^ 2 + Y ^ 2 := by positivity
  have hne : ((p.1 : ℂ) - Y * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hinv : ((p.1 : ℂ) - Y * Complex.I)⁻¹ =
      ((p.1 / (p.1 ^ 2 + Y ^ 2) : ℝ) : ℂ) + ((Y / (p.1 ^ 2 + Y ^ 2) : ℝ) : ℂ) * Complex.I := by
    set a := p.1 / (p.1 ^ 2 + Y ^ 2) with ha
    set b := Y / (p.1 ^ 2 + Y ^ 2) with hb
    have k1 : p.1 * a + Y * b = 1 := by rw [ha, hb]; field_simp
    have k2 : p.1 * b - Y * a = 0 := by rw [ha, hb]; field_simp; ring
    refine inv_eq_of_mul_eq_one_right ?_
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
        Complex.I_im, Complex.one_re]
      linarith
    · simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
        Complex.I_im, Complex.one_im]
      linarith
  rw [hinv]
  simp only [cutoffReWeight, cutoffImWeight, poissonKernel]
  push_cast
  field_simp

theorem cutoffReWeight_neg (L Y x : ℝ) : cutoffReWeight L Y (-x) = -cutoffReWeight L Y x := by
  simp only [cutoffReWeight, smoothCutoff_neg, neg_sq]
  ring

theorem continuous_cutoffReWeight (L : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (cutoffReWeight L Y) := by
  unfold cutoffReWeight
  refine (continuous_smoothCutoff L).mul (continuous_id.div (continuous_const.mul
    ((continuous_pow 2).add continuous_const)) fun x => ?_)
  have : 0 < x ^ 2 + Y ^ 2 := by positivity
  positivity

theorem continuous_cutoffImWeight (L : ℝ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (cutoffImWeight L Y) :=
  (continuous_smoothCutoff L).mul (continuous_poissonKernel hY)

theorem hasCompactSupport_cutoffReWeight (L Y : ℝ) : HasCompactSupport (cutoffReWeight L Y) :=
  (hasCompactSupport_smoothCutoff L).mul_right

theorem hasCompactSupport_cutoffImWeight (L Y : ℝ) : HasCompactSupport (cutoffImWeight L Y) :=
  (hasCompactSupport_smoothCutoff L).mul_right

theorem hasCompactSupport_sq {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport fun x => f x ^ 2 :=
  HasCompactSupport.intro hf fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]

theorem integral_cutoffReWeight (L Y : ℝ) : ∫ x, cutoffReWeight L Y x = 0 := by
  have h := integral_neg_eq_self (cutoffReWeight L Y) volume
  simp_rw [cutoffReWeight_neg, integral_neg] at h
  linarith

/-- Both weights satisfy `w² ≤ (π Y)⁻¹ P_Y`. -/
theorem sq_cutoffWeight_le {L Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    cutoffReWeight L Y x ^ 2 ≤ (Real.pi * Y)⁻¹ * poissonKernel Y x ∧
      cutoffImWeight L Y x ^ 2 ≤ (Real.pi * Y)⁻¹ * poissonKernel Y x := by
  have hc0 := smoothCutoff_nonneg L x
  have hc1 := smoothCutoff_le_one L x
  have hχ : smoothCutoff L x ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 < x ^ 2 + Y ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hrhs : (Real.pi * Y)⁻¹ * poissonKernel Y x = 1 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2)) := by
    unfold poissonKernel; field_simp
  rw [hrhs]
  constructor
  · unfold cutoffReWeight
    rw [mul_pow, div_pow, mul_pow]
    calc smoothCutoff L x ^ 2 * (x ^ 2 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2) ^ 2))
        ≤ 1 * (x ^ 2 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right hχ (by positivity)
      _ ≤ 1 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2)) := by
          rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg Y, mul_pos (pow_pos hpi 2) hpos]
  · unfold cutoffImWeight poissonKernel
    rw [mul_pow, div_pow, mul_pow]
    calc smoothCutoff L x ^ 2 * (Y ^ 2 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2) ^ 2))
        ≤ 1 * (Y ^ 2 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_right hχ (by positivity)
      _ ≤ 1 / (Real.pi ^ 2 * (x ^ 2 + Y ^ 2)) := by
          rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg x, mul_pos (pow_pos hpi 2) hpos]

theorem integral_sq_cutoffWeight_le {L Y : ℝ} (hY : 0 < Y) :
    ∫ x, cutoffReWeight L Y x ^ 2 ≤ (Real.pi * Y)⁻¹ ∧
      ∫ x, cutoffImWeight L Y x ^ 2 ≤ (Real.pi * Y)⁻¹ := by
  have hb : ∫ x, (Real.pi * Y)⁻¹ * poissonKernel Y x = (Real.pi * Y)⁻¹ := by
    rw [integral_const_mul, integral_poissonKernel hY, mul_one]
  have hi : Integrable fun x => (Real.pi * Y)⁻¹ * poissonKernel Y x :=
    (integrable_poissonKernel hY).const_mul _
  constructor
  · rw [← hb]
    exact integral_mono (((continuous_cutoffReWeight L hY).pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_cutoffReWeight L Y))) hi fun x => (sq_cutoffWeight_le hY x).1
  · rw [← hb]
    exact integral_mono (((continuous_cutoffImWeight L hY).pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_sq (hasCompactSupport_cutoffImWeight L Y))) hi fun x => (sq_cutoffWeight_le hY x).2

theorem norm_sq_ofReal_add_mul_I_sub (a b c : ℝ) :
    ‖((a : ℂ) + (b : ℂ) * Complex.I) - (c : ℂ) * Complex.I‖ ^ 2 = a ^ 2 + (b - c) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **`L²` estimate for the smooth cutoff of the canonical quadratic form at `iY`.**
Law: `Ξ` decorated sine on `(Ω, P)` (`IsDecoratedSineProcess`; `γ = circularVectorLaw (Fin r)`).
For `Y > 0`, every `L : ℝ` and `v ∈ ℂ^r`, with `‖v‖² = Σ_i |v_i|²` and
`S(ω) = smoothQuadCauchy (Ξ ω) L v (iY)`: almost surely the integrand is `Ξ(ω)`-integrable,
`S` is a.e. strongly measurable, `|S - i‖v‖²|²` is integrable and
`E |S - i ‖v‖²|² ≤ 4 (π Y)⁻¹ ∫ |v^* g|⁴ dγ + ‖v‖⁴ (1 - ∫ χ_L P_Y)²`.
Proof:
`Re S`, `Im S` are product statistics with weights `cutoffReWeight` (odd, mean `0`) and
`cutoffImWeight`;
`signedProductTest_variance` and `w² ≤ (π Y)⁻¹ P_Y`.
-/
theorem smoothQuadCauchy_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {Y : ℝ} (hY : 0 < Y) (L : ℝ) (v : Fin r → ℂ) :
    (∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) =>
      ((smoothCutoff L p.1 * quadMark v p.2 / Real.pi : ℝ) : ℂ) * ((p.1 : ℂ) - Y * Complex.I)⁻¹)
      (Ξ ω).measure) ∧
    AEStronglyMeasurable (fun ω => smoothQuadCauchy (Ξ ω) L v (Y * Complex.I)) P ∧
    Integrable (fun ω => ‖smoothQuadCauchy (Ξ ω) L v (Y * Complex.I) -
      ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) * Complex.I‖ ^ 2) P ∧
    ∫ ω, ‖smoothQuadCauchy (Ξ ω) L v (Y * Complex.I) -
      ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) * Complex.I‖ ^ 2 ∂P ≤
      4 * (Real.pi * Y)⁻¹ * (∫ g, quadMark v g ^ 2 ∂circularVectorLaw (Fin r)) +
        (∑ i, ‖v i‖ ^ 2) ^ 2 * (1 - ∫ x, cutoffImWeight L Y x) ^ 2 := by
  have := h.prob
  set γ := circularVectorLaw (Fin r) with hγ
  set s : ℝ := ∑ i, ‖v i‖ ^ 2 with hs
  have hc : ∫ g, quadMark v g ∂γ = s := integral_quadMark v
  obtain ⟨aeR, iR, ER, iVR, VR⟩ := signedProductTest_variance h (continuous_cutoffReWeight L hY)
    (hasCompactSupport_cutoffReWeight L Y) (continuous_quadMark v) (quadMark_nonneg v)
    (integrable_quadMark_sq v)
  obtain ⟨aeI, iI, EI, iVI, VI⟩ := signedProductTest_variance h (continuous_cutoffImWeight L hY)
    (hasCompactSupport_cutoffImWeight L Y) (continuous_quadMark v) (quadMark_nonneg v)
    (integrable_quadMark_sq v)
  rw [integral_cutoffReWeight, zero_mul] at ER
  simp only [integral_cutoffReWeight, zero_mul, sub_zero] at iVR VR
  rw [hc] at EI iVI VI
  set XR := fun ω => ∫ p, cutoffReWeight L Y p.1 * quadMark v p.2 ∂(Ξ ω).measure with hXR
  set XI := fun ω => ∫ p, cutoffImWeight L Y p.1 * quadMark v p.2 ∂(Ξ ω).measure with hXI
  set m := (∫ x, cutoffImWeight L Y x) * s with hm
  have hfun : (fun p : ℝ × (Fin r → ℂ) =>
      ((smoothCutoff L p.1 * quadMark v p.2 / Real.pi : ℝ) : ℂ) * ((p.1 : ℂ) - Y * Complex.I)⁻¹)
      = fun p => ((cutoffReWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ) +
        ((cutoffImWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ) * Complex.I :=
    funext (smoothQuadCauchy_integrand_eq hY L v)
  have hae : ∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) =>
      ((smoothCutoff L p.1 * quadMark v p.2 / Real.pi : ℝ) : ℂ) * ((p.1 : ℂ) - Y * Complex.I)⁻¹)
      (Ξ ω).measure ∧
      smoothQuadCauchy (Ξ ω) L v (Y * Complex.I) = (XR ω : ℂ) + (XI ω : ℂ) * Complex.I := by
    filter_upwards [aeR, aeI] with ω hR hI
    rw [hfun]
    have hR' : Integrable (fun p : ℝ × (Fin r → ℂ) =>
        ((cutoffReWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ)) (Ξ ω).measure := hR.ofReal
    have hI' : Integrable (fun p : ℝ × (Fin r → ℂ) =>
        ((cutoffImWeight L Y p.1 * quadMark v p.2 : ℝ) : ℂ) * Complex.I) (Ξ ω).measure :=
      (hI.ofReal (𝕜 := ℂ)).mul_const Complex.I
    refine ⟨hR'.add hI', ?_⟩
    unfold smoothQuadCauchy
    rw [hfun, integral_add hR' hI', integral_mul_const, integral_complex_ofReal,
      integral_complex_ofReal]
  have hSeq : (fun ω => smoothQuadCauchy (Ξ ω) L v (Y * Complex.I)) =ᵐ[P]
      fun ω => (XR ω : ℂ) + (XI ω : ℂ) * Complex.I := hae.mono fun ω hω => hω.2
  have hNeq : (fun ω => ‖smoothQuadCauchy (Ξ ω) L v (Y * Complex.I) - (s : ℂ) * Complex.I‖ ^ 2)
      =ᵐ[P] fun ω => XR ω ^ 2 + ((XI ω - m) ^ 2 + 2 * (m - s) * (XI ω - m) + (m - s) ^ 2) := by
    filter_upwards [hSeq] with ω hω
    rw [hω, norm_sq_ofReal_add_mul_I_sub]
    ring
  have hlin : Integrable (fun ω => 2 * (m - s) * (XI ω - m)) P :=
    (iI.sub (integrable_const m)).const_mul _
  have hiN : Integrable (fun ω => XR ω ^ 2 + ((XI ω - m) ^ 2 + 2 * (m - s) * (XI ω - m) +
      (m - s) ^ 2)) P :=
    iVR.add ((iVI.add hlin).add (integrable_const _))
  refine ⟨hae.mono fun ω hω => hω.1, ?_, hiN.congr hNeq.symm, ?_⟩
  · exact ((iR.ofReal (𝕜 := ℂ)).add ((iI.ofReal (𝕜 := ℂ)).mul_const
      Complex.I)).aestronglyMeasurable.congr hSeq.symm
  have hmean : ∫ ω, 2 * (m - s) * (XI ω - m) ∂P = 0 := by
    rw [integral_const_mul, integral_sub iI (integrable_const m), EI, integral_const]
    simp [hm]
  have hb := integral_sq_cutoffWeight_le (L := L) hY
  have hq20 : 0 ≤ ∫ g, quadMark v g ^ 2 ∂γ := integral_nonneg fun g => sq_nonneg _
  have e1 : ∫ ω, (XR ω ^ 2 + ((XI ω - m) ^ 2 + 2 * (m - s) * (XI ω - m) + (m - s) ^ 2)) ∂P =
      ∫ ω, XR ω ^ 2 ∂P + (∫ ω, (XI ω - m) ^ 2 ∂P + ∫ ω, 2 * (m - s) * (XI ω - m) ∂P +
        (m - s) ^ 2) := by
    rw [integral_add (f := fun ω => XR ω ^ 2)
      (g := fun ω => (XI ω - m) ^ 2 + 2 * (m - s) * (XI ω - m) + (m - s) ^ 2) iVR
      ((iVI.add hlin).add (integrable_const _)),
      integral_add (f := fun ω => (XI ω - m) ^ 2 + 2 * (m - s) * (XI ω - m))
      (g := fun _ => (m - s) ^ 2) (iVI.add hlin) (integrable_const _),
      integral_add (f := fun ω => (XI ω - m) ^ 2) (g := fun ω => 2 * (m - s) * (XI ω - m))
      iVI hlin, integral_const]
    simp
  rw [integral_congr_ae hNeq, e1, hmean, add_zero]
  have h1 : 2 * ((∫ x, cutoffReWeight L Y x ^ 2) * ∫ g, quadMark v g ^ 2 ∂γ) ≤
      2 * ((Real.pi * Y)⁻¹ * ∫ g, quadMark v g ^ 2 ∂γ) := by
    gcongr; exact hb.1
  have h2 : 2 * ((∫ x, cutoffImWeight L Y x ^ 2) * ∫ g, quadMark v g ^ 2 ∂γ) ≤
      2 * ((Real.pi * Y)⁻¹ * ∫ g, quadMark v g ^ 2 ∂γ) := by
    gcongr; exact hb.2
  have h3 : (m - s) ^ 2 = s ^ 2 * (1 - ∫ x, cutoffImWeight L Y x) ^ 2 := by rw [hm]; ring
  rw [h3]
  linarith

end BlockBand.Critical.Herglotz
