module

public import BlockBand.SourceProcess.ContractingWords.StepPre

/-!
# One step of a trace polynomial, abstract setting: the conditional expansion

* `indicator_decomp`: `1_AΔΦ = Σ_w ∂_wΦ(x)·1_AΔ_w + Σ_{(w,v)} ½∂_v∂_wΦ(x)·1_AΔ_wΔ_v + 1_AR`;
* `condExp_decomp`: `E[1_AΔΦ | m] = Σ_w ∂_wΦ(x)E[1_AΔ_w|m] + Σ_{(w,v)} ½∂_v∂_wΦ(x)E[1_AΔ_wΔ_v|m]
  + E[1_AR|m]` a.s. (old coefficients pulled out; every product dominated by a power of `M`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter MvPolynomial
open scoped ENNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem sum_pair_half (S : Finset σ) (G : σ → σ → ℂ) (Δ : σ → ℂ) :
    ∑ p ∈ S ×ˢ S, (1 / 2 * G p.1 p.2) * (Δ p.1 * Δ p.2) =
      1 / 2 * ∑ w ∈ S, ∑ v ∈ S, G w v * (Δ w * Δ v) := by
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

omit [DecidableEq σ] in
/-- The exact decomposition of `1_AΔΦ`. -/
theorem indicator_decomp (A : Set Ω) (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x x' : Ω → σ → ℂ) :
    A.indicator (fun ω => eval (x' ω) Φ - eval (x ω) Φ) = fun ω =>
      (∑ w ∈ S, eval (x ω) (pderiv w Φ) * A.indicator (incF x x' w) ω) +
      (∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) *
          A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω) +
      A.indicator (fun ω => taylorRem S Φ (x ω) (x' ω)) ω := by
  funext ω
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω]
    rw [sum_pair_half S (fun w v => eval (x ω) (pderiv v (pderiv w Φ))) fun w => incF x x' w ω]
    simp only [taylorRem, incF]; ring
  · simp [Set.indicator_of_notMem hω]

theorem norm_indicator_le' (A : Set Ω) (f : Ω → ℂ) (ω : Ω) : ‖A.indicator f ω‖ ≤ ‖f ω‖ := by
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, norm_zero]; exact norm_nonneg _

theorem integrable_mul_of_bounds {f g : Ω → ℂ} {M : Ω → ℝ} (hM0 : ∀ ω, 0 ≤ M ω)
    (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {a b : ℝ} {p q : ℕ} (ha : 0 ≤ a)
    (hfb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ a * M ω ^ p) (hgb : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ b * M ω ^ q)
    (hfin : ∫⁻ ω, ENNReal.ofReal (M ω) ^ (p + q) ∂μ ≠ ⊤) :
    Integrable (fun ω => f ω * g ω) μ := by
  refine integrable_of_bound (c := a * b) (n := p + q) (hf.mul hg) hM0 ?_ hfin
  filter_upwards [hfb, hgb] with ω h1 h2
  rw [norm_mul, pow_add]
  calc ‖f ω‖ * ‖g ω‖ ≤ (a * M ω ^ p) * (b * M ω ^ q) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := hM0 ω; positivity)
    _ = _ := by ring

/-- **The conditional expansion of one step.** -/
theorem condExp_decomp (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {S : Finset σ}
    {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    {M : Ω → ℝ} (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M)
    {Cg : σ → ℝ} {Ng : σ → ℕ} (hCg : ∀ w, 0 ≤ Cg w)
    (hTg : ∀ w ∈ S, TayBound S (pderiv w Φ) (Cg w) (Ng w))
    {CG : σ → σ → ℝ} {NG : σ → σ → ℕ} (hCG : ∀ w v, 0 ≤ CG w v)
    (hTG : ∀ w ∈ S, ∀ v ∈ S, TayBound S (pderiv v (pderiv w Φ)) (CG w v) (NG w v))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (M ω) ^ n ∂μ ≠ ⊤)
    (hN1 : ∀ w ∈ S, Ng w + 1 ≤ Nb) (hN2 : ∀ w ∈ S, ∀ v ∈ S, NG w v + 2 ≤ Nb)
    (hN3 : N + 3 ≤ Nb) :
    μ[A.indicator (fun ω => eval (x' ω) Φ - eval (x ω) Φ) | m] =ᵐ[μ] fun ω =>
      (∑ w ∈ S, eval (x ω) (pderiv w Φ) * μ[A.indicator (incF x x' w) | m] ω) +
      (∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) *
          μ[A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) | m] ω) +
      μ[A.indicator (fun ω => taylorRem S Φ (x ω) (x' ω)) | m] ω := by
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by linarith [hM1 ω]
  have hAm : MeasurableSet A := hm _ hA
  have hd1 : ∀ w, (pderiv w Φ).vars ⊆ S := fun w => (vars_pderiv_subset Φ w).trans hS
  have hd2 : ∀ w v, (pderiv v (pderiv w Φ)).vars ⊆ S := fun w v =>
    (vars_pderiv_subset _ v).trans (hd1 w)
  have hΔm := measurable_incF hm hx hx'
  have hΔb := ae_norm_incF_le hb
  -- the factors and their bounds
  have hI1 : ∀ w ∈ S, AEStronglyMeasurable (A.indicator (incF x x' w)) μ := fun w _ =>
    ((hΔm w).indicator hAm).aestronglyMeasurable
  have hB1 : ∀ w ∈ S, ∀ᵐ ω ∂μ, ‖A.indicator (incF x x' w) ω‖ ≤ 1 * M ω ^ 1 := fun w hw => by
    filter_upwards [hΔb] with ω hω
    simpa using (norm_indicator_le' A _ ω).trans (hω w hw)
  have hI2 : ∀ p ∈ S ×ˢ S, AEStronglyMeasurable
      (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) μ := fun p _ =>
    (((hΔm p.1).mul (hΔm p.2)).indicator hAm).aestronglyMeasurable
  have hB2 : ∀ p ∈ S ×ˢ S, ∀ᵐ ω ∂μ,
      ‖(A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω‖ ≤ 1 * M ω ^ 2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    filter_upwards [hΔb] with ω hω
    refine (norm_indicator_le' A _ ω).trans ?_
    rw [norm_mul, one_mul, sq]
    exact mul_le_mul (hω _ h1) (hω _ h2) (norm_nonneg _) (hM0 ω)
  have hc1 : ∀ w ∈ S, Integrable (fun ω => eval (x ω) (pderiv w Φ) *
      A.indicator (incF x x' w) ω) μ := fun w hw =>
    integrable_mul_of_bounds hM0 (aesm_coef hm hx _) (hI1 w hw) (hCg w)
      (ae_norm_eval_le hM1 hb (hd1 w) (hTg w hw)) (hB1 w hw) (hmom _ (hN1 w hw))
  have hc2 : ∀ p ∈ S ×ˢ S, Integrable (fun ω =>
      (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) *
        (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω) μ := by
    intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    refine integrable_mul_of_bounds (p := NG p.1 p.2) hM0
      (aestronglyMeasurable_const.mul (aesm_coef hm hx _)) (hI2 p hp) (hCG p.1 p.2) ?_ (hB2 p hp)
      (hmom _ (hN2 p.1 h1 p.2 h2))
    filter_upwards [ae_norm_eval_le hM1 hb (hd2 p.1 p.2) (hTG p.1 h1 p.2 h2)] with ω hω
    rw [norm_mul]
    have : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
    nlinarith [norm_nonneg (eval (x ω) (pderiv p.2 (pderiv p.1 Φ)))]
  have hf1 : ∀ w ∈ S, Integrable (A.indicator (incF x x' w)) μ := fun w hw =>
    integrable_of_bound (hI1 w hw) hM0 (hB1 w hw) (hmom _ (by omega))
  have hf2 : ∀ p ∈ S ×ˢ S, Integrable
      (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) μ := fun p hp =>
    integrable_of_bound (hI2 p hp) hM0 (hB2 p hp) (hmom _ (by omega))
  have hR : Integrable (A.indicator fun ω => taylorRem S Φ (x ω) (x' ω)) μ := by
    refine integrable_of_bound (c := C * (S.card : ℝ) ^ 3) (n := N + 3)
      (((measurable_taylorRem hm hx hx' S Φ).indicator hAm).aestronglyMeasurable) hM0 ?_
      (hmom _ hN3)
    filter_upwards [ae_norm_taylorRem_le_pow hS hM1 hb hC hT] with ω hω
    exact (norm_indicator_le' A _ ω).trans hω
  -- linearity and pull-out
  set F1 : Ω → ℂ := fun ω => ∑ w ∈ S, eval (x ω) (pderiv w Φ) * A.indicator (incF x x' w) ω
  set F2 : Ω → ℂ := fun ω => ∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) *
    (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω
  have hF1 : Integrable F1 μ := integrable_finsetSum _ hc1
  have hF2 : Integrable F2 μ := integrable_finsetSum _ hc2
  have e : A.indicator (fun ω => eval (x' ω) Φ - eval (x ω) Φ) =
      F1 + F2 + A.indicator fun ω => taylorRem S Φ (x ω) (x' ω) := by
    rw [indicator_decomp A S Φ x x']; rfl
  rw [e]
  have k1 := condExp_sum_mul (μ := μ) (m := m) S (fun w ω => eval (x ω) (pderiv w Φ))
    (fun w => A.indicator (incF x x' w)) (fun w _ => stronglyMeasurable_coef hx _) hc1 hf1
  have k2 := condExp_sum_mul (μ := μ) (m := m) (S ×ˢ S)
    (fun p ω => 1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ)))
    (fun p => A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω)
    (fun p _ => stronglyMeasurable_const.mul (stronglyMeasurable_coef hx _)) hc2 hf2
  filter_upwards [condExp_add (hF1.add hF2) hR m, condExp_add hF1 hF2 m, k1, k2]
    with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.add_apply]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) h3 h4) rfl

end BlockBand.SourceProcess.ContractingWords
