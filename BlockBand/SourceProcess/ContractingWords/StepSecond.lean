module

public import BlockBand.SourceProcess.ContractingWords.StepFirst

/-!
# One step of a trace polynomial, abstract setting: the second increment formula

`second_abstract`: in the setting of `first_abstract`, on an `m`-measurable event `A` the
conditional mean of `(Φ(x') - Φ(x))²` equals `Σ_{w,v} ∂_wΦ(x) ∂_vΦ(x) b_{wv}` in `L¹`, up to the
approximation error of `b_{wv}` and a remainder controlled by the sixth moments of the increments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter MvPolynomial
open scoped ENNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {σ : Type*} [DecidableEq σ]

/-- `Q = (ΔΦ)² - (Σ_w∂_wΦ Δ_w)²`. -/
def sqRem (S : Finset σ) (Φ : MvPolynomial σ ℂ) (x x' : σ → ℂ) : ℂ :=
  (eval x' Φ - eval x Φ) ^ 2 - (∑ w ∈ S, eval x (pderiv w Φ) * (x' w - x w)) ^ 2

omit [DecidableEq σ] in
theorem indicator_decomp_sq (A : Set Ω) (S : Finset σ) (Φ : MvPolynomial σ ℂ)
    (x x' : Ω → σ → ℂ) :
    A.indicator (fun ω => (eval (x' ω) Φ - eval (x ω) Φ) ^ 2) = fun ω =>
      (∑ p ∈ S ×ˢ S, (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) *
          A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω) +
      A.indicator (fun ω => sqRem S Φ (x ω) (x' ω)) ω := by
  funext ω
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, sqRem]
    have e : (∑ w ∈ S, eval (x ω) (pderiv w Φ) * (x' ω w - x ω w)) ^ 2 =
        ∑ p ∈ S ×ˢ S, (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) *
          (incF x x' p.1 ω * incF x x' p.2 ω) := by
      rw [sq, Finset.sum_mul_sum, Finset.sum_product]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by
        simp only [incF]; ring
    rw [e]; ring
  · simp [Set.indicator_of_notMem hω]

omit [DecidableEq σ] in
/-- A general remainder: `‖Rf‖ ≤ KM^n(Σ_w|Δ_w|)³` a.s. gives `‖E[1_ARf|m]‖₁ ≤ K|S|²·|S|m_nδ³`. -/
theorem remGen_bound (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {S : Finset σ}
    {x x' : Ω → σ → ℂ} (hx : ∀ w, Measurable[m] fun ω => x ω w)
    (hx' : ∀ w, Measurable fun ω => x' ω w) {M : Ω → ℝ} (hMm : Measurable M)
    (hM1 : ∀ ω, 1 ≤ M ω) {Rf : Ω → ℂ} (hRf : Measurable Rf) {K : ℝ} {n : ℕ} (hK : 0 ≤ K)
    (hR : ∀ᵐ ω ∂μ, ‖Rf ω‖ ≤ K * M ω ^ n * (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3) {δ : ℝ≥0∞}
    (h3 : ∀ w ∈ S, eLpNorm (A.indicator (incF x x' w)) 6 μ ≤ δ) :
    eLpNorm (fun ω => μ[A.indicator Rf | m] ω) 1 μ ≤
      ENNReal.ofReal (K * (S.card : ℝ) ^ 2) * (S.card * (momT μ M n * δ ^ (3 : ℝ))) := by
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by linarith [hM1 ω]
  have hAm : MeasurableSet A := hm _ hA
  have hΔm := measurable_incF hm hx hx'
  set g : σ → Ω → ℂ := fun w => A.indicator (incF x x' w)
  have hgm : ∀ w, AEStronglyMeasurable (g w) μ := fun w =>
    ((hΔm w).indicator hAm).aestronglyMeasurable
  have hK2 : 0 ≤ K * (S.card : ℝ) ^ 2 := by positivity
  set F : Ω → ℝ := fun ω => ∑ w ∈ S, M ω ^ n * ‖g w ω‖ ^ 3
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun w _ => by
    have := hM0 ω; positivity
  have hpt : ∀ᵐ ω ∂μ, ‖A.indicator Rf ω‖ ≤ ‖(K * (S.card : ℝ) ^ 2) • F ω‖ := by
    filter_upwards [hR] with ω hω
    rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg hK2 (hF0 ω))]
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA]
      refine hω.trans ?_
      have hg : ∀ w, ‖incF x x' w ω‖ = ‖g w ω‖ := fun w => by
        simp only [g, Set.indicator_of_mem hωA]
      simp only [hg]
      have hc := sum_cube_le S (fun w => ‖g w ω‖) fun _ => norm_nonneg _
      calc K * M ω ^ n * (∑ w ∈ S, ‖g w ω‖) ^ 3 ≤
          K * M ω ^ n * ((S.card : ℝ) ^ 2 * ∑ w ∈ S, ‖g w ω‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hc (by have := hM0 ω; positivity)
        _ = K * (S.card : ℝ) ^ 2 * F ω := by
            simp only [F, Finset.mul_sum]; ring_nf
    · rw [Set.indicator_of_notMem hωA, norm_zero]; exact mul_nonneg hK2 (hF0 ω)
  refine (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans
    ((eLpNorm_mono_ae (hRf.indicator hAm).aestronglyMeasurable hpt).trans ?_)
  have hFe : (fun ω => (K * (S.card : ℝ) ^ 2) • F ω) = (K * (S.card : ℝ) ^ 2) • F := rfl
  rw [hFe, eLpNorm_const_smul, Real.enorm_eq_ofReal hK2]
  gcongr
  have hFs : F = ∑ w ∈ S, fun ω => M ω ^ n * ‖g w ω‖ ^ 3 := by
    funext ω; simp [F, Finset.sum_apply]
  rw [hFs]
  refine (eLpNorm_sum_le le_rfl).trans ?_
  have hterm : ∀ w ∈ S, eLpNorm (fun ω => M ω ^ n * ‖g w ω‖ ^ 3) 1 μ ≤
      momT μ M n * δ ^ (3 : ℝ) := fun w hw => by
    refine (eLpNorm_cube_le n (hgm w) hMm.aestronglyMeasurable).trans ?_
    rw [eLpNorm_two_pow M hM0 hMm.aestronglyMeasurable n]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (h3 w hw) (by norm_num)) _
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

theorem ae_norm_coef2_le {S : Finset σ} {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S)
    {x x' : Ω → σ → ℂ} {M : Ω → ℝ} (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M)
    {Cg : σ → ℝ} {Ng : σ → ℕ} (hCg : ∀ w, 0 ≤ Cg w)
    (hTg : ∀ w ∈ S, TayBound S (pderiv w Φ) (Cg w) (Ng w)) {p : σ × σ} (hp : p ∈ S ×ˢ S) :
    ∀ᵐ ω ∂μ, ‖eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)‖ ≤
      (Cg p.1 * Cg p.2) * M ω ^ (Ng p.1 + Ng p.2) := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  have hd1 : ∀ w, (pderiv w Φ).vars ⊆ S := fun w => (vars_pderiv_subset Φ w).trans hS
  filter_upwards [ae_norm_eval_le hM1 hb (hd1 p.1) (hTg p.1 h1),
    ae_norm_eval_le hM1 hb (hd1 p.2) (hTg p.2 h2)] with ω a1 a2
  rw [norm_mul, pow_add]
  calc _ ≤ (Cg p.1 * M ω ^ Ng p.1) * (Cg p.2 * M ω ^ Ng p.2) :=
        mul_le_mul a1 a2 (norm_nonneg _) (by have := hM1 ω; have := hCg p.1; positivity)
    _ = _ := by ring

omit [DecidableEq σ] in
theorem measurable_sqRem (hm : m ≤ mΩ) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    (S : Finset σ) (Φ : MvPolynomial σ ℂ) : Measurable fun ω => sqRem S Φ (x ω) (x' ω) := by
  have hxm : ∀ w, Measurable fun ω => x ω w := fun w => (hx w).mono hm le_rfl
  have hc : ∀ Ψ : MvPolynomial σ ℂ, Measurable fun ω => eval (x ω) Ψ := fun Ψ =>
    FullSourceStops.measurable_eval Ψ hxm
  unfold sqRem
  exact (((FullSourceStops.measurable_eval Φ hx').sub (hc Φ)).pow_const 2).sub
    ((Finset.measurable_sum _ fun w _ => (hc _).mul ((hx' w).sub (hxm w))).pow_const 2)

/-- **The second increment formula, abstract form.** -/
theorem second_abstract (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {S : Finset σ}
    {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    {M : Ω → ℝ} (hMm : Measurable M) (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M)
    {Cg : σ → ℝ} {Ng : σ → ℕ} (hCg : ∀ w, 0 ≤ Cg w)
    (hTg : ∀ w ∈ S, TayBound S (pderiv w Φ) (Cg w) (Ng w))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (M ω) ^ n ∂μ ≠ ⊤)
    (hN1 : ∀ w ∈ S, ∀ v ∈ S, Ng w + Ng v + 2 ≤ Nb) (hN3 : 2 * N + 3 + 3 ≤ Nb)
    (bb : σ × σ → Ω → ℂ) (hbb : ∀ p ∈ S ×ˢ S, AEStronglyMeasurable (bb p) μ) {ε₂ δ : ℝ≥0∞}
    (h2 : ∀ p ∈ S ×ˢ S, eLpNorm (A.indicator fun ω =>
      μ[A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) | m] ω - bb p ω) 2 μ ≤ ε₂)
    (h3 : ∀ w ∈ S, eLpNorm (A.indicator (incF x x' w)) 6 μ ≤ δ) :
    eLpNorm (A.indicator fun ω =>
        μ[A.indicator (fun ω => (eval (x' ω) Φ - eval (x ω) Φ) ^ 2) | m] ω -
          ∑ p ∈ S ×ˢ S, (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) * bb p ω) 1 μ ≤
      (∑ p ∈ S ×ˢ S, ENNReal.ofReal (Cg p.1 * Cg p.2) * momT μ M (Ng p.1 + Ng p.2)) * ε₂ +
        ENNReal.ofReal (3 * C ^ 2 * (1 + S.card) ^ 3 * (S.card : ℝ) ^ 2) *
          (S.card * (momT μ M (2 * N + 3) * δ ^ (3 : ℝ))) := by
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by linarith [hM1 ω]
  have hAm : MeasurableSet A := hm _ hA
  have hΔm := measurable_incF hm hx hx'
  have hΔb := ae_norm_incF_le hb
  have hK : 0 ≤ 3 * C ^ 2 * (1 + (S.card : ℝ)) ^ 3 := by positivity
  have hQb : ∀ᵐ ω ∂μ, ‖sqRem S Φ (x ω) (x' ω)‖ ≤
      3 * C ^ 2 * (1 + S.card) ^ 3 * M ω ^ (2 * N + 3) * (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3 := by
    filter_upwards [hb] with ω hω
    exact norm_sqRem_le hS hC hT (hM1 ω) hω
  have hQm := measurable_sqRem hm hx hx' S Φ
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
  have hgm : ∀ p : σ × σ, AEStronglyMeasurable
      (fun ω => eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) μ := fun p =>
    (aesm_coef hm hx _).mul (aesm_coef hm hx _)
  have hc2 : ∀ p ∈ S ×ˢ S, Integrable (fun ω =>
      (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) *
        (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω) μ := fun p hp =>
    integrable_mul_of_bounds hM0 (hgm p) (hI2 p hp)
      (mul_nonneg (hCg p.1) (hCg p.2)) (ae_norm_coef2_le hS hM1 hb hCg hTg hp) (hB2 p hp)
      (hmom _ (hN1 p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2))
  have hf2 : ∀ p ∈ S ×ˢ S, Integrable
      (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) μ := fun p hp =>
    integrable_of_bound (hI2 p hp) hM0 (hB2 p hp) (hmom _ (by omega))
  have hQi : Integrable (A.indicator fun ω => sqRem S Φ (x ω) (x' ω)) μ := by
    refine integrable_of_bound (c := 3 * C ^ 2 * (1 + S.card) ^ 3 * (S.card : ℝ) ^ 3)
      (n := 2 * N + 3 + 3) ((hQm.indicator hAm).aestronglyMeasurable) hM0 ?_
      (hmom _ hN3)
    filter_upwards [hQb, hΔb] with ω hω h2
    refine (norm_indicator_le' A _ ω).trans (hω.trans ?_)
    have hs : ∑ w ∈ S, ‖incF x x' w ω‖ ≤ S.card * M ω := sum_le_card_mul h2
    have h3' := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hs 3
    calc 3 * C ^ 2 * (1 + S.card) ^ 3 * M ω ^ (2 * N + 3) * (∑ w ∈ S, ‖incF x x' w ω‖) ^ 3
        ≤ 3 * C ^ 2 * (1 + S.card) ^ 3 * M ω ^ (2 * N + 3) * (S.card * M ω) ^ 3 :=
          mul_le_mul_of_nonneg_left h3' (by have := hM0 ω; positivity)
      _ = _ := by ring
  set F2 : Ω → ℂ := fun ω => ∑ p ∈ S ×ˢ S,
    (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) *
      (A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω) ω
  have hF2 : Integrable F2 μ := integrable_finsetSum _ hc2
  have e : A.indicator (fun ω => (eval (x' ω) Φ - eval (x ω) Φ) ^ 2) =
      F2 + A.indicator fun ω => sqRem S Φ (x ω) (x' ω) := by
    rw [indicator_decomp_sq A S Φ x x']; rfl
  have k2 := condExp_sum_mul (μ := μ) (m := m) (S ×ˢ S)
    (fun p ω => eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ))
    (fun p => A.indicator fun ω => incF x x' p.1 ω * incF x x' p.2 ω)
    (fun p _ => (stronglyMeasurable_coef hx _).mul (stronglyMeasurable_coef hx _)) hc2 hf2
  set e2 : σ × σ → Ω → ℂ := fun p => A.indicator fun ω =>
    μ[A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) | m] ω - bb p ω
  set R3 : Ω → ℂ := A.indicator fun ω =>
    μ[A.indicator (fun ω => sqRem S Φ (x ω) (x' ω)) | m] ω
  have hEq : (A.indicator fun ω =>
        μ[A.indicator (fun ω => (eval (x' ω) Φ - eval (x ω) Φ) ^ 2) | m] ω -
          ∑ p ∈ S ×ˢ S, (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) * bb p ω) =ᵐ[μ]
      (fun ω => ∑ p ∈ S ×ˢ S,
        (eval (x ω) (pderiv p.1 Φ) * eval (x ω) (pderiv p.2 Φ)) * e2 p ω) + R3 := by
    rw [e]
    filter_upwards [condExp_add hF2 hQi m, k2] with ω h1 h4
    by_cases hωA : ω ∈ A
    · simp only [Set.indicator_of_mem hωA, Pi.add_apply, e2, R3]
      rw [h1, Pi.add_apply, show μ[F2 | m] ω = _ from h4]
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    · simp [Set.indicator_of_notMem hωA, e2, R3]
  rw [eLpNorm_congr_ae hEq]
  refine (eLpNorm_add_le le_rfl).trans (add_le_add ?_ ?_)
  · refine (eLpNorm_sum_mul_le (S ×ˢ S) _ e2 (fun p _ => hgm p) fun p hp =>
      (((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub (hbb p hp)).indicator
        hAm)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => mul_le_mul' ?_ (h2 p hp)
    exact eLpNorm_two_le_of_bound (hgm p) hM0 hMm.aestronglyMeasurable
      (mul_nonneg (hCg p.1) (hCg p.2)) (ae_norm_coef2_le hS hM1 hb hCg hTg hp)
  · exact (eLpNorm_indicator_le _ hAm.nullMeasurableSet).trans
      (remGen_bound hm hA hx hx' hMm hM1 hQm hK hQb h3)

end BlockBand.SourceProcess.ContractingWords
