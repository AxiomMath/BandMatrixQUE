module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalMomDefs

/-!
# One tested step through the conditional errors

Abstract (probability space `(Ω, μ)`, sub-σ-algebra `m`, a set `A` a.e. equal to an `m`-event):
**`stepCE`**. If on `A` an integrand `X` differs from
`Σ_c a₁_c (δ_c − β¹_c) + Σ_{c,c'} a₂_{cc'} (δ_c δ_{c'} − β²_{cc'})` by at most `R_t`, with
`m`-measurable coefficients bounded by `C_a` and an `m`-measurable test `ψ`, `|ψ| ≤ Φ`, then
`‖∫ 1_A ψ X‖ₑ ≤ Φ C_a (Σ_c e¹_c + Σ_{c,c'} e²_{cc'}) + ∫⁻ 1_A Φ R_t`, where `e¹, e²` are the
conditional errors `∫⁻ ‖1_A (E[1_A δ_c | m] − β¹_c)‖ₑ` and `∫⁻ ‖1_A (E[1_A δ_c δ_{c'} | m] −
β²_{cc'})‖ₑ` (the summands of `b3SummedErr`). Uses the interface pin `CondExpReplace`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

section Abstract

variable {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ι : Type} [Fintype ι]

omit [IsProbabilityMeasure μ] in
theorem integrable_indicator_bdd_mul {A : Set Ω} {g f : Ω → ℂ} (hg : AEStronglyMeasurable g μ)
    {C : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ C) (hf : Integrable (A.indicator f) μ) :
    Integrable (A.indicator fun ω => g ω * f ω) μ := by
  have e : (A.indicator fun ω => g ω * f ω) = fun ω => g ω * A.indicator f ω := by
    funext ω; by_cases h : ω ∈ A <;> simp [h]
  rw [e]
  exact hf.bdd_mul hg (ae_of_all _ hgb)

/-- **One tested step through the conditional errors.** -/
theorem stepCE (hCE : CondExpReplace) (hm : m ≤ mΩ) {A A' : Set Ω} (hA' : MeasurableSet[m] A')
    (hAA : A =ᵐ[μ] A') (δ β1 : ι → Ω → ℂ) (β2 : ι → ι → Ω → ℂ) (a1 : ι → Ω → ℂ)
    (a2 : ι → ι → Ω → ℂ) {Ca : ℝ} (ha1 : ∀ c, StronglyMeasurable[m] (a1 c))
    (ha2 : ∀ c c', StronglyMeasurable[m] (a2 c c')) (ha1b : ∀ c ω, ‖a1 c ω‖ ≤ Ca)
    (ha2b : ∀ c c' ω, ‖a2 c c' ω‖ ≤ Ca) (ψ : Ω → ℝ) (hψ : StronglyMeasurable[m] ψ) {Φ : ℝ}
    (hψb : ∀ ω, ‖ψ ω‖ ≤ Φ) (hδ1 : ∀ c, Integrable (A.indicator (δ c)) μ)
    (hδ2 : ∀ c c', Integrable (A.indicator fun ω => δ c ω * δ c' ω) μ)
    (hβ1 : ∀ c, Integrable (A.indicator (β1 c)) μ)
    (hβ2 : ∀ c c', Integrable (A.indicator (β2 c c')) μ)
    (hβ1m : ∀ c, AEStronglyMeasurable[m] (β1 c) μ)
    (hβ2m : ∀ c c', AEStronglyMeasurable[m] (β2 c c') μ)
    (X : Ω → ℂ) (hX : Integrable (A.indicator X) μ) (Rt : Ω → ℝ)
    (hR : ∀ᵐ ω ∂μ, ω ∈ A → ‖X ω - (∑ c, a1 c ω * (δ c ω - β1 c ω) +
      ∑ c, ∑ c', a2 c c' ω * (δ c ω * δ c' ω - β2 c c' ω))‖ ≤ Rt ω) :
    ‖∫ ω, A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω ∂μ‖ₑ ≤
      ENNReal.ofReal (Φ * Ca) * ((∑ c, ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (δ c) | m] ω - β1 c ω) ω‖ₑ ∂μ) +
        ∑ c, ∑ c', ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => δ c ω * δ c' ω) | m] ω - β2 c c' ω) ω‖ₑ ∂μ) +
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Φ * Rt ω)) ω ∂μ := by
  -- coefficients against the test
  set g1 : ι → Ω → ℂ := fun c ω => (ψ ω : ℂ) * a1 c ω
  set g2 : ι → ι → Ω → ℂ := fun c c' ω => (ψ ω : ℂ) * a2 c c' ω
  have hψc : StronglyMeasurable[m] fun ω => (ψ ω : ℂ) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hψ
  have hg1 : ∀ c, StronglyMeasurable[m] (g1 c) := fun c => hψc.mul (ha1 c)
  have hg2 : ∀ c c', StronglyMeasurable[m] (g2 c c') := fun c c' => hψc.mul (ha2 c c')
  have hΦ : ∀ ω, ‖(ψ ω : ℂ)‖ ≤ Φ := fun ω => by rw [Complex.norm_real]; exact hψb ω
  have hg1b : ∀ c ω, ‖g1 c ω‖ ≤ Φ * Ca := fun c ω => by
    rw [norm_mul]
    exact mul_le_mul (hΦ ω) (ha1b c ω) (norm_nonneg _) ((norm_nonneg _).trans (hΦ ω))
  have hg2b : ∀ c c' ω, ‖g2 c c' ω‖ ≤ Φ * Ca := fun c c' ω => by
    rw [norm_mul]
    exact mul_le_mul (hΦ ω) (ha2b c c' ω) (norm_nonneg _) ((norm_nonneg _).trans (hΦ ω))
  have hg1m : ∀ c, AEStronglyMeasurable (g1 c) μ := fun c => ((hg1 c).mono hm).aestronglyMeasurable
  have hg2m : ∀ c c', AEStronglyMeasurable (g2 c c') μ := fun c c' =>
    ((hg2 c c').mono hm).aestronglyMeasurable
  -- the pieces
  set P1 : ι → Ω → ℂ := fun c => A.indicator fun ω => g1 c ω * δ c ω
  set Q1 : ι → Ω → ℂ := fun c => A.indicator fun ω => g1 c ω * β1 c ω
  set P2 : ι → ι → Ω → ℂ := fun c c' => A.indicator fun ω => g2 c c' ω * (δ c ω * δ c' ω)
  set Q2 : ι → ι → Ω → ℂ := fun c c' => A.indicator fun ω => g2 c c' ω * β2 c c' ω
  have iP1 : ∀ c, Integrable (P1 c) μ := fun c =>
    integrable_indicator_bdd_mul (hg1m c) (hg1b c) (hδ1 c)
  have iQ1 : ∀ c, Integrable (Q1 c) μ := fun c =>
    integrable_indicator_bdd_mul (hg1m c) (hg1b c) (hβ1 c)
  have iP2 : ∀ c c', Integrable (P2 c c') μ := fun c c' =>
    integrable_indicator_bdd_mul (hg2m c c') (hg2b c c') (hδ2 c c')
  have iQ2 : ∀ c c', Integrable (Q2 c c') μ := fun c c' =>
    integrable_indicator_bdd_mul (hg2m c c') (hg2b c c') (hβ2 c c')
  set main : Ω → ℂ := fun ω => ∑ c, (P1 c ω - Q1 c ω) + ∑ c, ∑ c', (P2 c c' ω - Q2 c c' ω)
  have imain : Integrable main μ :=
    (integrable_finsetSum _ fun c _ => (iP1 c).sub (iQ1 c)).add
      (integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
        (iP2 c c').sub (iQ2 c c'))
  have iψX : Integrable (A.indicator fun ω => (ψ ω : ℂ) * X ω) μ :=
    integrable_indicator_bdd_mul (hψc.mono hm).aestronglyMeasurable hΦ hX
  -- the split
  have hsplit : ∫ ω, A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω ∂μ =
      ∫ ω, main ω ∂μ + ∫ ω, (A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω - main ω) ∂μ := by
    calc ∫ ω, A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω ∂μ
        = ∫ ω, (main ω + (A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω - main ω)) ∂μ := by
          congr 1; funext ω; ring
      _ = _ := integral_add imain (iψX.sub imain)
  have i1 : ∀ c, Integrable (fun ω => P1 c ω - Q1 c ω) μ := fun c => (iP1 c).sub (iQ1 c)
  have i2 : ∀ c c', Integrable (fun ω => P2 c c' ω - Q2 c c' ω) μ := fun c c' =>
    (iP2 c c').sub (iQ2 c c')
  have i2' : ∀ c, Integrable (fun ω => ∑ c', (P2 c c' ω - Q2 c c' ω)) μ := fun c =>
    integrable_finsetSum _ fun c' _ => i2 c c'
  have hmain : ∫ ω, main ω ∂μ = ∑ c, ((∫ ω, P1 c ω ∂μ) - ∫ ω, Q1 c ω ∂μ) +
      ∑ c, ∑ c', ((∫ ω, P2 c c' ω ∂μ) - ∫ ω, Q2 c c' ω ∂μ) := by
    calc ∫ ω, main ω ∂μ = (∫ ω, ∑ c, (P1 c ω - Q1 c ω) ∂μ) +
          ∫ ω, ∑ c, ∑ c', (P2 c c' ω - Q2 c c' ω) ∂μ :=
        integral_add (integrable_finsetSum _ fun c _ => i1 c)
          (integrable_finsetSum _ fun c _ => i2' c)
      _ = _ := by
        rw [integral_finsetSum _ fun c _ => i1 c, integral_finsetSum _ fun c _ => i2' c]
        congr 1
        · exact Finset.sum_congr rfl fun c _ => integral_sub (iP1 c) (iQ1 c)
        · refine Finset.sum_congr rfl fun c _ => ?_
          rw [integral_finsetSum _ fun c' _ => i2 c c']
          exact Finset.sum_congr rfl fun c' _ => integral_sub (iP2 c c') (iQ2 c c')
  have e1 : ∀ c, ‖(∫ ω, P1 c ω ∂μ) - ∫ ω, Q1 c ω ∂μ‖ₑ ≤ ENNReal.ofReal (Φ * Ca) *
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator (δ c) | m] ω - β1 c ω) ω‖ₑ ∂μ := fun c =>
    hCE μ m hm A A' hA' hAA (g1 c) (hg1 c) (Φ * Ca) (fun ω _ => hg1b c ω) (δ c) (β1 c) (hδ1 c)
      (hβ1m c)
  have e2 : ∀ c c', ‖(∫ ω, P2 c c' ω ∂μ) - ∫ ω, Q2 c c' ω ∂μ‖ₑ ≤ ENNReal.ofReal (Φ * Ca) *
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator (fun ω => δ c ω * δ c' ω) | m] ω -
        β2 c c' ω) ω‖ₑ ∂μ := fun c c' =>
    hCE μ m hm A A' hA' hAA (g2 c c') (hg2 c c') (Φ * Ca) (fun ω _ => hg2b c c' ω)
      (fun ω => δ c ω * δ c' ω) (β2 c c') (hδ2 c c') (hβ2m c c')
  -- the rest
  have hrest : ‖∫ ω, (A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω - main ω) ∂μ‖ₑ ≤
      ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Φ * Rt ω)) ω ∂μ := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
    filter_upwards [hR] with ω hω
    by_cases hA : ω ∈ A
    · have h1 : ∑ c, (g1 c ω * δ c ω - g1 c ω * β1 c ω) =
          (ψ ω : ℂ) * ∑ c, a1 c ω * (δ c ω - β1 c ω) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by simp only [g1]; ring
      have h2 : ∑ c, ∑ c', (g2 c c' ω * (δ c ω * δ c' ω) - g2 c c' ω * β2 c c' ω) =
          (ψ ω : ℂ) * ∑ c, ∑ c', a2 c c' ω * (δ c ω * δ c' ω - β2 c c' ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c' _ => by simp only [g2]; ring
      have hpt : A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω - main ω =
          (ψ ω : ℂ) * (X ω - (∑ c, a1 c ω * (δ c ω - β1 c ω) +
            ∑ c, ∑ c', a2 c c' ω * (δ c ω * δ c' ω - β2 c c' ω))) := by
        simp only [main, P1, Q1, P2, Q2, Set.indicator_of_mem hA]
        rw [h1, h2]; ring
      rw [hpt, Set.indicator_of_mem hA, ← ofReal_norm, norm_mul]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul (hΦ ω) (hω hA) (norm_nonneg _)
        ((norm_nonneg _).trans (hΦ ω)))
    · have : A.indicator (fun ω => (ψ ω : ℂ) * X ω) ω - main ω = 0 := by
        simp [main, P1, Q1, P2, Q2, Set.indicator_of_notMem hA]
      rw [this, enorm_zero]; exact zero_le
  rw [hsplit, hmain]
  refine (enorm_add_le _ _).trans (add_le_add ?_ hrest)
  refine (enorm_add_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ((enorm_sum_le _ _).trans ?_) ((enorm_sum_le _ _).trans ?_)
  · rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => e1 c
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => (enorm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c' _ => e2 c c'

end Abstract

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
