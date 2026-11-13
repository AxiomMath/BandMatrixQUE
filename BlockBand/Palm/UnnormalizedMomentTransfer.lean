module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

/-!
# Unnormalized weighted conditional-moment error transfer

For a weight `0 ≤ w ≤ W` measurable for a sub-σ-algebra `m`, an error `δ` for `E[X | m]` on a good
event and a global error `B` give `|E[wX] - a E[w]| ≤ δ E[w] + B W μ(goodᶜ)`, with no
lower bound on `E[w]` (`conditional_weighted_error_le`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm

open MeasureTheory

/-- Pull-out and tower identity `E[w E[X | m]] = E[wX]` for an `m`-measurable weight `w`, with
integrability of `w E[X | m]`. -/
theorem integral_weight_mul_condExp
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {w X : Ω → ℝ} (hw : StronglyMeasurable[m] w)
    (hX : Integrable X μ) (hwX : Integrable (w * X) μ) :
    Integrable (w * μ[X | m]) μ ∧
      (∫ ω, w ω * (μ[X | m]) ω ∂μ) = ∫ ω, w ω * X ω ∂μ := by
  have hp := condExp_mul_of_stronglyMeasurable_left hw hwX hX
  refine ⟨integrable_condExp.congr hp, ?_⟩
  calc
    (∫ ω, w ω * (μ[X | m]) ω ∂μ) = ∫ ω, (μ[w * X | m]) ω ∂μ :=
      integral_congr_ae hp.symm
    _ = _ := integral_condExp hm

/-- Pointwise splitting into the good and bad events before integration. -/
theorem weighted_error_pointwise
    {w F a δ B W : ℝ} (good : Prop) [Decidable good]
    (hw0 : 0 ≤ w) (hwW : w ≤ W) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hgood : good → |F - a| ≤ δ) (hbad : |F - a| ≤ B) :
    |w * (F - a)| ≤ δ * w + if good then 0 else B * W := by
  rw [abs_mul, abs_of_nonneg hw0]
  by_cases hg : good
  · simp only [hg, ite_true, add_zero]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hgood hg) hw0
  · simp only [hg, ite_false]
    have h1 : w * |F - a| ≤ w * B := mul_le_mul_of_nonneg_left hbad hw0
    have h2 : w * B ≤ B * W := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hwW hB
    have h3 : 0 ≤ δ * w := mul_nonneg hδ hw0
    linarith

/-- Unnormalized weighted error bound under a finite measure: for any weight `0 ≤ w ≤ W`, a
good-event error `δ` and a global error `B` give `δ Z + B W μ(goodᶜ)`, where `Z = ∫ w`. No
positivity of `Z` is needed. -/
theorem integral_weighted_error_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {w F : Ω → ℝ} {good : Set Ω} (hgoodSet : MeasurableSet good)
    (hw : Integrable w μ) (hwF : Integrable (w * F) μ)
    {a δ B W : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (hwW : ∀ᵐ ω ∂μ, w ω ≤ W)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ good → |F ω - a| ≤ δ)
    (hbad : ∀ᵐ ω ∂μ, |F ω - a| ≤ B) :
    |(∫ ω, w ω * F ω ∂μ) - a * ∫ ω, w ω ∂μ| ≤
      δ * (∫ ω, w ω ∂μ) + B * W * μ.real goodᶜ := by
  classical
  have he : Integrable (fun ω => w ω * (F ω - a)) μ := by
    have he0 : Integrable (fun ω => w ω * F ω - w ω * a) μ :=
      (show Integrable (fun ω => w ω * F ω) μ from hwF).sub (hw.mul_const a)
    exact he0.congr (ae_of_all _ fun ω => by ring)
  have hind : Integrable (goodᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hgoodSet.compl
  have hrhs : Integrable
      (fun ω => δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (hw.const_mul δ).add (hind.const_mul (B * W))
  have hpoint : ∀ᵐ ω ∂μ, |w ω * (F ω - a)| ≤
      δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hw0, hwW, hgood, hbad] with ω h0 hW hg hb
    have hh := weighted_error_pointwise (ω ∈ good) h0 hW hδ hB hg hb
    by_cases hmem : ω ∈ good <;> simpa [hmem] using hh
  calc
    |(∫ ω, w ω * F ω ∂μ) - a * ∫ ω, w ω ∂μ| =
        |∫ ω, w ω * (F ω - a) ∂μ| := by
      rw [show (fun ω => w ω * (F ω - a)) =
        (fun ω => w ω * F ω - w ω * a) by ext ω; ring,
        integral_sub (show Integrable (fun ω => w ω * F ω) μ from hwF)
          (hw.mul_const a), integral_mul_const]
      rw [mul_comm a]
    _ ≤ ∫ ω, |w ω * (F ω - a)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, δ * w ω + B * W * goodᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ :=
      integral_mono_ae he.abs hrhs hpoint
    _ = _ := by
      rw [integral_add (hw.const_mul δ) (hind.const_mul (B * W)),
        integral_const_mul, integral_const_mul,
        integral_indicator_const 1 hgoodSet.compl]
      simp

/-- A deterministic bound on the moment error gives the global conditional error bound (the
bad-path estimate). -/
theorem condExp_error_le_of_rawBound
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {X : Ω → ℝ} (hX : Integrable X μ) {a B : ℝ}
    (hraw : ∀ᵐ ω ∂μ, |X ω - a| ≤ B) :
    ∀ᵐ ω ∂μ, |(μ[X | m]) ω - a| ≤ B := by
  have hlo : (fun _ : Ω => a - B) ≤ᵐ[μ] X := by
    filter_upwards [hraw] with ω hω
    have h := (abs_le.mp hω).1
    linarith
  have hhi : X ≤ᵐ[μ] (fun _ : Ω => a + B) := by
    filter_upwards [hraw] with ω hω
    have h := (abs_le.mp hω).2
    linarith
  have hl := condExp_mono (m := m) (integrable_const (a - B)) hX hlo
  have hh := condExp_mono (m := m) hX (integrable_const (a + B)) hhi
  simp only [condExp_const hm] at hl hh
  filter_upwards [hl, hh] with ω h₁ h₂
  rw [abs_le]
  constructor <;> linarith

/-- The integration step of the fresh Palm theorem: the weighted error transfer with the
conditional expectation `E[X | m]`. It is used with `X = |√N q*u_ℓ|^(2r)`, `a = r!(q*Γq)^r`,
`δ = C_r N^(-κ_r)(q*Γq)^r`; the good-path estimate and the bad-path bound are hypotheses. -/
theorem conditional_weighted_error_le
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {w X : Ω → ℝ} (hwMeas : StronglyMeasurable[m] w)
    (hw : Integrable w μ) (hX : Integrable X μ)
    (hwX : Integrable (w * X) μ)
    {good : Set Ω} (hgoodSet : MeasurableSet good)
    {a δ B W : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (hwW : ∀ᵐ ω ∂μ, w ω ≤ W)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ good → |(μ[X | m]) ω - a| ≤ δ)
    (hbad : ∀ᵐ ω ∂μ, |(μ[X | m]) ω - a| ≤ B) :
    |(∫ ω, w ω * X ω ∂μ) - a * ∫ ω, w ω ∂μ| ≤
      δ * (∫ ω, w ω ∂μ) + B * W * μ.real goodᶜ := by
  obtain ⟨hweighted, hidentity⟩ := integral_weight_mul_condExp hm hwMeas hX hwX
  rw [← hidentity]
  exact integral_weighted_error_le hgoodSet hw hweighted hδ hB hw0 hwW hgood hbad

/-- The unnormalized Palm transfer with the bad-path conditional bound derived from a
deterministic bound on the observable; only the good-path comparison is a hypothesis. -/
theorem conditional_weighted_error_le_of_rawBound
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {w X : Ω → ℝ} (hwMeas : StronglyMeasurable[m] w)
    (hw : Integrable w μ) (hX : Integrable X μ)
    (hwX : Integrable (w * X) μ)
    {good : Set Ω} (hgoodSet : MeasurableSet good)
    {a δ B W : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hw0 : ∀ᵐ ω ∂μ, 0 ≤ w ω) (hwW : ∀ᵐ ω ∂μ, w ω ≤ W)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ good → |(μ[X | m]) ω - a| ≤ δ)
    (hraw : ∀ᵐ ω ∂μ, |X ω - a| ≤ B) :
    |(∫ ω, w ω * X ω ∂μ) - a * ∫ ω, w ω ∂μ| ≤
      δ * (∫ ω, w ω ∂μ) + B * W * μ.real goodᶜ :=
  conditional_weighted_error_le hm hwMeas hw hX hwX hgoodSet hδ hB hw0 hwW hgood
    (condExp_error_le_of_rawBound hm hX hraw)

end BlockBand.Palm
