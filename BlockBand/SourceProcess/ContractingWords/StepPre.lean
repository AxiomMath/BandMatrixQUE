module

public import BlockBand.SourceProcess.ContractingWords.StepTaylor
public import BlockBand.SourceProcess.ContractingWords.SummedTools
public import BlockBand.SourceProcess.FullSourceStops.PolyEval

/-!
# One step of a trace polynomial, abstract setting: bounds and integrability

Pointwise and moment bounds for the increments `Δ_w = x'_w - x_w` and for the Taylor remainder of a
polynomial under a dominating function `M`, together with the measurability facts they need.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter MvPolynomial
open scoped ENNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {σ : Type*} [DecidableEq σ]

/-- `Δ_w = x'_w - x_w`. -/
def incF (x x' : Ω → σ → ℂ) (w : σ) (ω : Ω) : ℂ := x' ω w - x ω w

/-- `(E M^{2n})^{1/2}`. -/
def momT (μ : Measure Ω) (M : Ω → ℝ) (n : ℕ) : ℝ≥0∞ :=
  (∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ)

/-- The a.s. domination of the two evaluation points. -/
def Dominated (μ : Measure Ω) (S : Finset σ) (x x' : Ω → σ → ℂ) (M : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ w ∈ S, ‖x ω w‖ + ‖x' ω w‖ ≤ M ω

omit [DecidableEq σ] in
theorem measurable_eval_pt {x : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (Ψ : MvPolynomial σ ℂ) :
    Measurable[m] fun ω => eval (x ω) Ψ :=
  FullSourceStops.measurable_eval Ψ hx

theorem ae_norm_eval_le {S : Finset σ} {x x' : Ω → σ → ℂ} {M : Ω → ℝ} (hM1 : ∀ ω, 1 ≤ M ω)
    (hb : Dominated μ S x x' M) {Ψ : MvPolynomial σ ℂ} (hΨ : Ψ.vars ⊆ S) {C : ℝ} {N : ℕ}
    (hT : TayBound S Ψ C N) : ∀ᵐ ω ∂μ, ‖eval (x ω) Ψ‖ ≤ C * M ω ^ N := by
  filter_upwards [hb] with ω hω
  exact norm_eval_le_of_tay hΨ hT (hM1 ω) fun w hw => by
    have := norm_nonneg (x' ω w); linarith [hω w hw]

omit [DecidableEq σ] in
theorem ae_norm_incF_le {S : Finset σ} {x x' : Ω → σ → ℂ} {M : Ω → ℝ}
    (hb : Dominated μ S x x' M) : ∀ᵐ ω ∂μ, ∀ w ∈ S, ‖incF x x' w ω‖ ≤ M ω := by
  filter_upwards [hb] with ω hω w hw
  exact (norm_sub_le _ _).trans (by linarith [hω w hw])

theorem ae_norm_taylorRem_le {S : Finset σ} {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S)
    {x x' : Ω → σ → ℂ} {M : Ω → ℝ} (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M) {C : ℝ}
    {N : ℕ} (hT : TayBound S Φ C N) :
    ∀ᵐ ω ∂μ, ‖taylorRem S Φ (x ω) (x' ω)‖ ≤ C * M ω ^ N * (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3 := by
  filter_upwards [hb] with ω hω
  exact norm_taylorRem_le hS hT (hM1 ω) hω

omit [DecidableEq σ] in
theorem sum_cube_le (S : Finset σ) (f : σ → ℝ) (hf : ∀ w, 0 ≤ f w) :
    (∑ w ∈ S, f w) ^ 3 ≤ (S.card : ℝ) ^ 2 * ∑ w ∈ S, f w ^ 3 :=
  pow_sum_le_card_mul_sum_pow (fun w _ => hf w) 2

omit [DecidableEq σ] in
theorem sum_le_card_mul {S : Finset σ} {f : σ → ℝ} {c : ℝ} (h : ∀ w ∈ S, f w ≤ c) :
    ∑ w ∈ S, f w ≤ S.card * c := by
  have := Finset.sum_le_sum h
  simpa [Finset.sum_const, nsmul_eq_mul] using this

/-- The remainder is dominated by a power of `M`. -/
theorem ae_norm_taylorRem_le_pow {S : Finset σ} {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S)
    {x x' : Ω → σ → ℂ} {M : Ω → ℝ} (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M) {C : ℝ}
    {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) :
    ∀ᵐ ω ∂μ, ‖taylorRem S Φ (x ω) (x' ω)‖ ≤ C * (S.card : ℝ) ^ 3 * M ω ^ (N + 3) := by
  filter_upwards [ae_norm_taylorRem_le hS hM1 hb hT, ae_norm_incF_le hb] with ω h1 h2
  have hM0 : 0 ≤ M ω := by linarith [hM1 ω]
  have hs : ∑ w ∈ S, ‖incF x x' w ω‖ ≤ S.card * M ω := sum_le_card_mul h2
  have hs0 : 0 ≤ ∑ w ∈ S, ‖incF x x' w ω‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine h1.trans ?_
  have h3 : (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3 ≤ (S.card * M ω) ^ 3 := pow_le_pow_left₀ hs0 hs 3
  calc C * M ω ^ N * (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3 ≤ C * M ω ^ N * (S.card * M ω) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

omit [DecidableEq σ] in
/-- Measurability of the old coefficients. -/
theorem stronglyMeasurable_coef {x : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (Ψ : MvPolynomial σ ℂ) :
    StronglyMeasurable[m] fun ω => eval (x ω) Ψ :=
  (measurable_eval_pt hx Ψ).stronglyMeasurable

omit [DecidableEq σ] in
theorem aesm_coef (hm : m ≤ mΩ) {x : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (Ψ : MvPolynomial σ ℂ) :
    AEStronglyMeasurable (fun ω => eval (x ω) Ψ) μ :=
  ((stronglyMeasurable_coef hx Ψ).mono hm).aestronglyMeasurable

omit [DecidableEq σ] in
theorem measurable_incF (hm : m ≤ mΩ) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w) (w : σ) :
    Measurable (incF x x' w) :=
  (hx' w).sub ((hx w).mono hm le_rfl)

omit [DecidableEq σ] in
theorem measurable_taylorRem (hm : m ≤ mΩ) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    (S : Finset σ) (Φ : MvPolynomial σ ℂ) :
    Measurable fun ω => taylorRem S Φ (x ω) (x' ω) := by
  have hxm : ∀ w, Measurable fun ω => x ω w := fun w => (hx w).mono hm le_rfl
  have hc : ∀ Ψ : MvPolynomial σ ℂ, Measurable fun ω => eval (x ω) Ψ := fun Ψ =>
    FullSourceStops.measurable_eval Ψ hxm
  unfold taylorRem
  refine (((FullSourceStops.measurable_eval Φ hx').sub (hc Φ)).sub ?_).sub
    (measurable_const.mul ?_)
  · exact Finset.measurable_sum _ fun w _ => (hc _).mul ((hx' w).sub (hxm w))
  · exact Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun v _ =>
      (hc _).mul (((hx' w).sub (hxm w)).mul ((hx' v).sub (hxm v)))

end BlockBand.SourceProcess.ContractingWords
