module

public import BlockBand.Transmission.LawDecay.Coef
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# The one-step Lyapunov inequality in expectation (abstract)

Setting: a probability space `(Ω, μ)`, a sub-σ-algebra `m` (the past `𝓕_r`), an `m`-measurable
state `(x, y)` (`= (g_r, P₂(r))`) and a next state `(x', y')`, both in
`Dom K = {0 ≤ y ≤ x, y ≤ x², x ≤ K}` almost surely. The conditional means of the increments
`h = x' - x`, `k = y' - y` and of `h², hk` are written `e + A` (an error `e` plus the generator
coefficient `A`).

This module provides the conditioning lemma `integral_test_le` for **`step_abstract`**, proved in
the sibling module: if the generator applied to `Φ_ε` (with the coefficients `A₁, A₂, B₁₁, B₁₂`)
is at most `-c(Φ_ε - 2√ε)` almost surely, then
`E Φ_ε(x',y') ≤ E Φ_ε(x,y) - c(E Φ_ε(x,y) - 2√ε) + ε^{-5/2}(E|e₁| + E|e₂| + E|e₁₁| + E|e₁₂|)
  + E[ε^{-7/2}(|h|³ + h²|k|)/6]`.

It is `lyap_step` integrated, with `E[φ·f] = E[φ·E[f ∣ m]]` for the bounded `m`-measurable
coefficients `φ` (`integral_test_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDecay

open MeasureTheory

/-- The almost-sure domain of the state `(g, P₂)`. -/
def Dom (K x y : ℝ) : Prop := 0 ≤ y ∧ y ≤ x ∧ y ≤ x ^ 2 ∧ x ≤ K

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Pull-out with an error bound**: `E[φf] ≤ E[φA] + B·E|e|` if `E[f ∣ m] = e + A`. -/
theorem integral_test_le (hm : m ≤ m₀) {φ f A e : Ω → ℝ} (hφ : Measurable[m] φ) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, |φ ω| ≤ B) (hf : Integrable f μ) (hA : Integrable A μ)
    (he : Integrable e μ) (hc : μ[f | m] = e + A) :
    ∫ ω, φ ω * f ω ∂μ ≤ ∫ ω, φ ω * A ω ∂μ + B * ∫ ω, |e ω| ∂μ := by
  have hφ0 : Measurable φ := hφ.mono hm le_rfl
  have hBn : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ B := hB.mono fun ω h => by simpa [Real.norm_eq_abs] using h
  have h1 : ∫ ω, φ ω * f ω ∂μ = ∫ ω, φ ω * e ω + φ ω * A ω ∂μ := by
    rw [← integral_condExp hm (f := fun ω => φ ω * f ω)]
    refine integral_congr_ae ?_
    have := condExp_stronglyMeasurable_mul_of_bound hm hφ.stronglyMeasurable hf B hBn
    filter_upwards [this] with ω hω
    have e1 : (fun ω => φ ω * f ω) = φ * f := rfl
    rw [e1, hω, Pi.mul_apply, hc, Pi.add_apply, mul_add]
  have hie : Integrable (fun ω => φ ω * e ω) μ := he.bdd_mul hφ0.aestronglyMeasurable hBn
  have hiA : Integrable (fun ω => φ ω * A ω) μ := hA.bdd_mul hφ0.aestronglyMeasurable hBn
  rw [h1, integral_add hie hiA]
  have : ∫ ω, φ ω * e ω ∂μ ≤ B * ∫ ω, |e ω| ∂μ := by
    refine (le_abs_self _).trans ((abs_integral_le_integral_abs).trans ?_)
    rw [← integral_const_mul]
    refine integral_mono_ae hie.abs (he.abs.const_mul B) ?_
    filter_upwards [hB] with ω h
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  linarith

/-- Integrability from measurability and an almost-sure bound. -/
theorem integrable_of_abs_le {f : Ω → ℝ} (hf : Measurable f) {C : ℝ}
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (h.mono fun ω h => by simpa using h)

theorem abs_sub_le_of_dom {K x y x' y' : ℝ} (h : Dom K x y) (h' : Dom K x' y') :
    |x' - x| ≤ K ∧ |y' - y| ≤ K := by
  obtain ⟨a1, a2, -, a4⟩ := h
  obtain ⟨b1, b2, -, b4⟩ := h'
  exact ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩

/-- The pointwise Taylor bound, in the form used below. -/
theorem lyap_step_dom {ε K x y x' y' : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (h : Dom K x y)
    (h' : Dom K x' y') :
    lyap ε x' y' ≤ lyap ε x y + (coefX ε x y * (x' - x) + coefY ε x * (y' - y)) +
      (coefXX ε x y * ((x' - x) * (x' - x)) + coefXY ε x * ((x' - x) * (y' - y))) +
      ε ^ (-7 / 2 : ℝ) * (|x' - x| ^ 3 + (x' - x) ^ 2 * |y' - y|) / 6 := by
  have := lyap_step hε hε1 h.1 h.2.1 h'.1 h'.2.1
  have e1 : coefXX ε x y * (x' - x) ^ 2 = coefXX ε x y * ((x' - x) * (x' - x)) := by ring
  have e2 : coefXY ε x * (x' - x) * (y' - y) = coefXY ε x * ((x' - x) * (y' - y)) := by ring
  linarith

end BlockBand.Transmission.LawDecay
