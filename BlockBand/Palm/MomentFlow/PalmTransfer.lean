module

public import BlockBand.Palm.UnnormalizedMomentTransfer

/-!
# Unnormalized Palm transfer with an energy window

`|E[w X] - a E[w]| ≤ δ E[w] + B W μ(goodᶜ) + B ε' μ(Ω)`

for `0 ≤ w ≤ W`, `w ≤ ε'` off the window, `|E[X|𝓛] - a| ≤ δ` on `good ∩ window`, and the raw bound
`|X - a| ≤ B`. No division by the sector mass `E[w]`. Any finite measure, with the conditional
expectation on an explicit sub-σ-algebra.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory

/-- Pointwise three-region bound. -/
theorem weighted_error_pointwise_window {w F a δ B W ε' : ℝ} (good window : Prop)
    [Decidable good] (hw0 : 0 ≤ w) (hwW : w ≤ W) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hε' : 0 ≤ ε')
    (hgood : good → window → |F - a| ≤ δ) (hoff : ¬ window → w ≤ ε') (hbad : |F - a| ≤ B) :
    |w * (F - a)| ≤ δ * w + (if good then 0 else B * W) + B * ε' := by
  rw [abs_mul, abs_of_nonneg hw0]
  have hBW : 0 ≤ B * W := mul_nonneg hB (hw0.trans hwW)
  have h0 : 0 ≤ δ * w := mul_nonneg hδ hw0
  have h1 : 0 ≤ B * ε' := mul_nonneg hB hε'
  have hwB : w * |F - a| ≤ w * B := mul_le_mul_of_nonneg_left hbad hw0
  by_cases hg : good
  · simp only [hg, ite_true, add_zero]
    by_cases hwin : window
    · have := mul_le_mul_of_nonneg_left (hgood hg hwin) hw0
      nlinarith
    · have hw' := hoff hwin
      have : w * B ≤ ε' * B := mul_le_mul_of_nonneg_right hw' hB
      nlinarith
  · simp only [hg, ite_false]
    have : w * B ≤ W * B := mul_le_mul_of_nonneg_right hwW hB
    nlinarith

/-- Integrated three-region bound for an arbitrary integrand `F`. -/
theorem integral_weighted_error_le_window
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {w F : Ω → ℝ} {good window : Set Ω} (hgoodSet : MeasurableSet good)
    (hw : Integrable w μ) (hwF : Integrable (w * F) μ)
    {a δ B W ε' : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hε' : 0 ≤ ε')
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (hwW : ∀ᵐ ω ∂μ, w ω ≤ W)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ good → ω ∈ window → |F ω - a| ≤ δ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ window → w ω ≤ ε')
    (hbad : ∀ᵐ ω ∂μ, |F ω - a| ≤ B) :
    |(∫ ω, w ω * F ω ∂μ) - a * ∫ ω, w ω ∂μ| ≤
      δ * (∫ ω, w ω ∂μ) + B * W * μ.real goodᶜ + B * ε' * μ.real Set.univ := by
  classical
  have he : Integrable (fun ω => w ω * (F ω - a)) μ := by
    have he0 : Integrable (fun ω => w ω * F ω - w ω * a) μ :=
      (show Integrable (fun ω => w ω * F ω) μ from hwF).sub (hw.mul_const a)
    exact he0.congr (ae_of_all _ fun ω => by ring)
  have hind : Integrable (goodᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hgoodSet.compl
  have hrhs : Integrable (fun ω => δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω +
      B * ε') μ :=
    ((hw.const_mul δ).add (hind.const_mul (B * W))).add (integrable_const _)
  have hpoint : ∀ᵐ ω ∂μ, |w ω * (F ω - a)| ≤
      δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω + B * ε' := by
    filter_upwards [hw0, hwW, hgood, hoff, hbad] with ω h0 hW hg ho hb
    have hh := weighted_error_pointwise_window (ω ∈ good) (ω ∈ window) h0 hW hδ hB hε' hg ho hb
    by_cases hmem : ω ∈ good <;> simpa [hmem] using hh
  calc
    |(∫ ω, w ω * F ω ∂μ) - a * ∫ ω, w ω ∂μ| = |∫ ω, w ω * (F ω - a) ∂μ| := by
      rw [show (fun ω => w ω * (F ω - a)) = (fun ω => w ω * F ω - w ω * a) by ext ω; ring,
        integral_sub (show Integrable (fun ω => w ω * F ω) μ from hwF) (hw.mul_const a),
        integral_mul_const]
      rw [mul_comm a]
    _ ≤ ∫ ω, |w ω * (F ω - a)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω + B * ε' ∂μ :=
      integral_mono_ae he.abs hrhs hpoint
    _ = _ := by
      have i0 : Integrable (fun ω => δ * w ω) μ := hw.const_mul δ
      have i2 : Integrable (fun ω => B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω) μ :=
        hind.const_mul (B * W)
      have i1 : Integrable (fun ω => δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω) μ :=
        i0.add i2
      rw [integral_add i1 (integrable_const (B * ε')), integral_add i0 i2,
        integral_const_mul, integral_const_mul,
        integral_indicator_const 1 hgoodSet.compl, integral_const]
      simp [mul_comm]

/-- **Fresh Palm integration step with an energy window.** In the proof of the fresh Palm theorem:
`X = |√N q*u_ℓ|^{2r}`, `a = r!(q*Γq)^r`, `w` the scalar Palm weight
(`𝓛`-measurable), `good` the good path set of the conditional-moments lemma intersected with
`|g| ≤ N^{-1+ε}/4`, `window = {|ν_ℓ - E| ≤ N^{-1+ε}}`, `ε' = C N e^{-c N^{2ε}}`. -/
theorem conditional_weighted_error_le_window
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {w X : Ω → ℝ} (hwMeas : StronglyMeasurable[m] w)
    (hw : Integrable w μ) (hX : Integrable X μ) (hwX : Integrable (w * X) μ)
    {good window : Set Ω} (hgoodSet : MeasurableSet good)
    {a δ B W ε' : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hε' : 0 ≤ ε')
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (hwW : ∀ᵐ ω ∂μ, w ω ≤ W)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ good → ω ∈ window → |(μ[X | m]) ω - a| ≤ δ)
    (hoff : ∀ᵐ ω ∂μ, ω ∉ window → w ω ≤ ε')
    (hraw : ∀ᵐ ω ∂μ, |X ω - a| ≤ B) :
    |(∫ ω, w ω * X ω ∂μ) - a * ∫ ω, w ω ∂μ| ≤
      δ * (∫ ω, w ω ∂μ) + B * W * μ.real goodᶜ + B * ε' * μ.real Set.univ := by
  obtain ⟨hweighted, hidentity⟩ := BlockBand.Palm.integral_weight_mul_condExp hm hwMeas hX hwX
  rw [← hidentity]
  exact integral_weighted_error_le_window hgoodSet hw hweighted hδ hB hε' hw0 hwW hgood hoff
    (BlockBand.Palm.condExp_error_le_of_rawBound hm hX hraw)

end BlockBand.Palm.MomentFlow
