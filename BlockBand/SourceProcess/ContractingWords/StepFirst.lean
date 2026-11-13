module

public import BlockBand.SourceProcess.ContractingWords.StepDecomp

/-!
# One step of a trace polynomial, abstract setting: the first increment formula

`first_abstract`: let a polynomial `Φ` be evaluated at `x` and at `x' = x + Δ`, and let `a_w`,
`b_{wv}` approximate the conditional means of `Δ_w` and `Δ_wΔ_v` given `m` in `L²` on an
`m`-measurable event `A`. Then on `A` the conditional mean `E[Φ(x') - Φ(x) | m]` equals
`Σ_w ∂_wΦ(x) a_w + ½ Σ_{w,v} ∂_v∂_wΦ(x) b_{wv}` in `L¹`, up to the two approximation errors and a
remainder controlled by the sixth moments of the increments (`rem_bound`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter MvPolynomial
open scoped ENNReal

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {σ : Type*} [DecidableEq σ]

/-- The remainder term: `‖1_AE[1_AR|m]‖₁ ≤ C|S|²·|S|·m_N·δ³`. -/
theorem rem_bound (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {S : Finset σ}
    {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    {M : Ω → ℝ} (hMm : Measurable M) (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) {δ : ℝ≥0∞}
    (h3 : ∀ w ∈ S, eLpNorm (A.indicator (incF x x' w)) 6 μ ≤ δ) :
    eLpNorm (fun ω => μ[A.indicator (fun ω => taylorRem S Φ (x ω) (x' ω)) | m] ω) 1 μ ≤
      ENNReal.ofReal (C * (S.card : ℝ) ^ 2) * (S.card * (momT μ M N * δ ^ (3 : ℝ))) := by
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by linarith [hM1 ω]
  have hAm : MeasurableSet A := hm _ hA
  have hΔm := measurable_incF hm hx hx'
  set g : σ → Ω → ℂ := fun w => A.indicator (incF x x' w)
  have hgm : ∀ w, AEStronglyMeasurable (g w) μ := fun w =>
    ((hΔm w).indicator hAm).aestronglyMeasurable
  have hK : 0 ≤ C * (S.card : ℝ) ^ 2 := by positivity
  set F : Ω → ℝ := fun ω => ∑ w ∈ S, M ω ^ N * ‖g w ω‖ ^ 3
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => Finset.sum_nonneg fun w _ => by
    have := hM0 ω; positivity
  have hpt : ∀ᵐ ω ∂μ, ‖A.indicator (fun ω => taylorRem S Φ (x ω) (x' ω)) ω‖ ≤
      ‖(C * (S.card : ℝ) ^ 2) • F ω‖ := by
    filter_upwards [ae_norm_taylorRem_le hS hM1 hb hT] with ω hω
    rw [smul_eq_mul, Real.norm_of_nonneg (mul_nonneg hK (hF0 ω))]
    by_cases hωA : ω ∈ A
    · rw [Set.indicator_of_mem hωA]
      refine hω.trans ?_
      have hg : ∀ w, ‖incF x x' w ω‖ = ‖g w ω‖ := fun w => by
        simp only [g, Set.indicator_of_mem hωA]
      simp only [hg]
      have hc := sum_cube_le S (fun w => ‖g w ω‖) fun _ => norm_nonneg _
      have hMN : 0 ≤ M ω ^ N := pow_nonneg (hM0 ω) N
      calc C * M ω ^ N * (∑ w ∈ S, ‖g w ω‖) ^ 3 ≤
          C * M ω ^ N * ((S.card : ℝ) ^ 2 * ∑ w ∈ S, ‖g w ω‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = C * (S.card : ℝ) ^ 2 * F ω := by
            simp only [F, Finset.mul_sum]; ring_nf
    · rw [Set.indicator_of_notMem hωA, norm_zero]; exact mul_nonneg hK (hF0 ω)
  have hRm : AEStronglyMeasurable (A.indicator fun ω => taylorRem S Φ (x ω) (x' ω)) μ :=
    ((measurable_taylorRem hm hx hx' S Φ).indicator hAm).aestronglyMeasurable
  refine (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans ((eLpNorm_mono_ae hRm hpt).trans ?_)
  have hFe : (fun ω => (C * (S.card : ℝ) ^ 2) • F ω) = (C * (S.card : ℝ) ^ 2) • F := rfl
  rw [hFe, eLpNorm_const_smul, Real.enorm_eq_ofReal hK]
  gcongr
  have hFs : F = ∑ w ∈ S, fun ω => M ω ^ N * ‖g w ω‖ ^ 3 := by
    funext ω; simp [F, Finset.sum_apply]
  rw [hFs]
  refine (eLpNorm_sum_le le_rfl).trans ?_
  have hterm : ∀ w ∈ S, eLpNorm (fun ω => M ω ^ N * ‖g w ω‖ ^ 3) 1 μ ≤
      momT μ M N * δ ^ (3 : ℝ) := fun w hw => by
    refine (eLpNorm_cube_le N (hgm w) hMm.aestronglyMeasurable).trans ?_
    rw [eLpNorm_two_pow M hM0 hMm.aestronglyMeasurable N]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (h3 w hw) (by norm_num)) _
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

theorem eLpNorm_coef_le (hm : m ≤ mΩ) {S : Finset σ} {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) {M : Ω → ℝ} (hMm : Measurable M)
    (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M) {Ψ : MvPolynomial σ ℂ} (hΨ : Ψ.vars ⊆ S)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Ψ C N) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    eLpNorm (fun ω => c * eval (x ω) Ψ) 2 μ ≤ ENNReal.ofReal C * momT μ M N := by
  have hM0 : ∀ ω, 0 ≤ M ω := fun ω => by linarith [hM1 ω]
  refine eLpNorm_two_le_of_bound (aestronglyMeasurable_const.mul (aesm_coef hm hx Ψ)) hM0
    hMm.aestronglyMeasurable hC ?_
  filter_upwards [ae_norm_eval_le hM1 hb hΨ hT] with ω hω
  rw [norm_mul]
  nlinarith [norm_nonneg (eval (x ω) Ψ), norm_nonneg c]

/-- **The first increment formula, abstract form.** -/
theorem first_abstract (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[m] A) {S : Finset σ}
    {Φ : MvPolynomial σ ℂ} (hS : Φ.vars ⊆ S) {x x' : Ω → σ → ℂ}
    (hx : ∀ w, Measurable[m] fun ω => x ω w) (hx' : ∀ w, Measurable fun ω => x' ω w)
    {M : Ω → ℝ} (hMm : Measurable M) (hM1 : ∀ ω, 1 ≤ M ω) (hb : Dominated μ S x x' M)
    {Cg : σ → ℝ} {Ng : σ → ℕ} (hCg : ∀ w, 0 ≤ Cg w)
    (hTg : ∀ w ∈ S, TayBound S (pderiv w Φ) (Cg w) (Ng w))
    {CG : σ → σ → ℝ} {NG : σ → σ → ℕ} (hCG : ∀ w v, 0 ≤ CG w v)
    (hTG : ∀ w ∈ S, ∀ v ∈ S, TayBound S (pderiv v (pderiv w Φ)) (CG w v) (NG w v))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hT : TayBound S Φ C N) {Nb : ℕ}
    (hmom : ∀ n ≤ Nb, ∫⁻ ω, ENNReal.ofReal (M ω) ^ n ∂μ ≠ ⊤)
    (hN1 : ∀ w ∈ S, Ng w + 1 ≤ Nb) (hN2 : ∀ w ∈ S, ∀ v ∈ S, NG w v + 2 ≤ Nb)
    (hN3 : N + 3 ≤ Nb)
    (a : σ → Ω → ℂ) (ha : ∀ w ∈ S, AEStronglyMeasurable (a w) μ)
    (bb : σ × σ → Ω → ℂ) (hbb : ∀ p ∈ S ×ˢ S, AEStronglyMeasurable (bb p) μ)
    {ε₁ ε₂ δ : ℝ≥0∞}
    (h1 : ∀ w ∈ S, eLpNorm (A.indicator fun ω =>
      μ[A.indicator (incF x x' w) | m] ω - a w ω) 2 μ ≤ ε₁)
    (h2 : ∀ p ∈ S ×ˢ S, eLpNorm (A.indicator fun ω =>
      μ[A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) | m] ω - bb p ω) 2 μ ≤ ε₂)
    (h3 : ∀ w ∈ S, eLpNorm (A.indicator (incF x x' w)) 6 μ ≤ δ) :
    eLpNorm (A.indicator fun ω =>
        μ[A.indicator (fun ω => eval (x' ω) Φ - eval (x ω) Φ) | m] ω -
          ((∑ w ∈ S, eval (x ω) (pderiv w Φ) * a w ω) +
            ∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) * bb p ω)) 1 μ ≤
      (∑ w ∈ S, ENNReal.ofReal (Cg w) * momT μ M (Ng w)) * ε₁ +
        (∑ p ∈ S ×ˢ S, ENNReal.ofReal (CG p.1 p.2) * momT μ M (NG p.1 p.2)) * ε₂ +
        ENNReal.ofReal (C * (S.card : ℝ) ^ 2) * (S.card * (momT μ M N * δ ^ (3 : ℝ))) := by
  have hAm : MeasurableSet A := hm _ hA
  have hd1 : ∀ w, (pderiv w Φ).vars ⊆ S := fun w => (vars_pderiv_subset Φ w).trans hS
  have hd2 : ∀ w v, (pderiv v (pderiv w Φ)).vars ⊆ S := fun w v =>
    (vars_pderiv_subset _ v).trans (hd1 w)
  have hdec := condExp_decomp hm hA hS hx hx' hM1 hb hCg hTg hCG hTG hC hT hmom hN1 hN2 hN3
  set e1 : σ → Ω → ℂ := fun w => A.indicator fun ω => μ[A.indicator (incF x x' w) | m] ω - a w ω
  set e2 : σ × σ → Ω → ℂ := fun p => A.indicator fun ω =>
    μ[A.indicator (fun ω => incF x x' p.1 ω * incF x x' p.2 ω) | m] ω - bb p ω
  set R3 : Ω → ℂ := A.indicator fun ω =>
    μ[A.indicator (fun ω => taylorRem S Φ (x ω) (x' ω)) | m] ω
  have hEq : (A.indicator fun ω =>
        μ[A.indicator (fun ω => eval (x' ω) Φ - eval (x ω) Φ) | m] ω -
          ((∑ w ∈ S, eval (x ω) (pderiv w Φ) * a w ω) +
            ∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) * bb p ω)) =ᵐ[μ]
      (fun ω => ∑ w ∈ S, eval (x ω) (pderiv w Φ) * e1 w ω) +
        (fun ω => ∑ p ∈ S ×ˢ S, (1 / 2 * eval (x ω) (pderiv p.2 (pderiv p.1 Φ))) * e2 p ω) +
        R3 := by
    filter_upwards [hdec] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [Set.indicator_of_mem hωA, Pi.add_apply, e1, e2, R3, hω, mul_sub,
        Finset.sum_sub_distrib]
      ring
    · simp [Set.indicator_of_notMem hωA, e1, e2, R3]
  rw [eLpNorm_congr_ae hEq]
  refine (eLpNorm_add_le le_rfl).trans (add_le_add ((eLpNorm_add_le le_rfl).trans
    (add_le_add ?_ ?_)) ?_)
  · refine (eLpNorm_sum_mul_le S _ e1 (fun w _ => aesm_coef hm hx _) fun w hw =>
      (((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub (ha w hw)).indicator
        hAm)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun w hw => mul_le_mul' ?_ (h1 w hw)
    simpa using eLpNorm_coef_le hm hx hMm hM1 hb (hd1 w) (hCg w) (hTg w hw) 1 (by simp)
  · refine (eLpNorm_sum_mul_le (S ×ˢ S) _ e2
      (fun p _ => aestronglyMeasurable_const.mul (aesm_coef hm hx _)) fun p hp =>
      (((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable.sub (hbb p hp)).indicator
        hAm)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => mul_le_mul' ?_ (h2 p hp)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact eLpNorm_coef_le hm hx hMm hM1 hb (hd2 p.1 p.2) (hCG p.1 p.2) (hTG p.1 hp1 p.2 hp2)
      (1 / 2) (by norm_num)
  · exact (eLpNorm_indicator_le _ hAm.nullMeasurableSet).trans
      (rem_bound hm hA hS hx hx' hMm hM1 hb hC hT h3)

end BlockBand.SourceProcess.ContractingWords
