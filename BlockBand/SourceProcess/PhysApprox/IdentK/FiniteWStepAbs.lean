module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWCond

/-!
# The tested expectation of one Taylor step (abstract)

Measure: a finite measure `μ`; a sub-σ-algebra `m ≤ m0`; an `m`-event `A` (the alive set). After
the Taylor expansion of one step, the tested expectation of the step minus `w · generator` is
bounded by the conditional drift and bracket errors and the remainder.

**`enorm_integral_step_le`**: for basic increments `β`, `m`-measurable jet coefficients `ℓ, q`
bounded by `C`, a bounded `m`-measurable test `g`, a drift vector `d`, a bracket matrix `B`, a
remainder `rem` and a weight `w`,
`‖∫ g 1_A (lin ℓ β + quad q β + rem − w (lin ℓ d + Σ q B))‖ₑ ≤
  C_g C (Σ_i e¹_i + Σ_{i,i'} e²_{ii'}) + C_g ∫⁻ ‖1_A rem‖ₑ`,
with `e¹_i = ∫⁻ ‖1_A (E[1_A β_i | m] − w d_i)‖ₑ` and `e²_{ii'}` the same for `β_i β_{i'}`,
`B_{ii'}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]

/-- The pointwise decomposition of a tested Taylor step. -/
theorem step_decomp (A : Set Ω) (β ℓ d : Ω → ι → ℂ) (q Bm : Ω → ι → ι → ℂ) (rem g : Ω → ℂ)
    (w : ℂ) (ω : Ω) :
    g ω * A.indicator (fun ω => lin (ℓ ω) (β ω) + quad (q ω) (β ω) + rem ω -
        w * (lin (ℓ ω) (d ω) + ∑ i, ∑ i', q ω i i' * Bm ω i i')) ω =
      ∑ i, (g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω -
        g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω) +
      ∑ i, ∑ i', (g ω * q ω i i' * A.indicator (fun ω => β ω i * β ω i') ω -
        g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω) +
      g ω * A.indicator rem ω := by
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, lin, quad, mul_add, mul_sub, mul_sum, sum_sub_distrib]
    have e1 : ∀ i, g ω * (ℓ ω i * β ω i) = g ω * ℓ ω i * β ω i := fun i => by ring
    have e2 : ∀ i, g ω * (w * (ℓ ω i * d ω i)) = g ω * ℓ ω i * (w * d ω i) := fun i => by ring
    have e3 : ∀ i i', g ω * (q ω i i' * (β ω i * β ω i')) = g ω * q ω i i' * (β ω i * β ω i') :=
      fun i i' => by ring
    have e4 : ∀ i i', g ω * (w * (q ω i i' * Bm ω i i')) = g ω * q ω i i' * (w * Bm ω i i') :=
      fun i i' => by ring
    simp only [e1, e2, e3, e4]
    ring
  · simp [Set.indicator_of_notMem hω]

/-- **The tested expectation of one Taylor step.** -/
theorem enorm_integral_step_le [IsFiniteMeasure μ] (hm : m ≤ m0) {A : Set Ω}
    (hA : MeasurableSet[m] A) (β ℓ d : Ω → ι → ℂ) (q Bm : Ω → ι → ι → ℂ) (rem g : Ω → ℂ)
    (w : ℂ) {C Cg : ℝ} (hC : 0 ≤ C) (hCg : 0 ≤ Cg)
    (hℓ : ∀ i, StronglyMeasurable[m] fun ω => ℓ ω i)
    (hq : ∀ i i', StronglyMeasurable[m] fun ω => q ω i i') (hg : StronglyMeasurable[m] g)
    (hℓb : ∀ ω i, ‖ℓ ω i‖ ≤ C) (hqb : ∀ ω i i', ‖q ω i i'‖ ≤ C) (hgb : ∀ ω, ‖g ω‖ ≤ Cg)
    (hβ : ∀ i, Integrable (A.indicator fun ω => β ω i) μ)
    (hββ : ∀ i i', Integrable (A.indicator fun ω => β ω i * β ω i') μ)
    (hd : ∀ i, Integrable (A.indicator fun ω => w * d ω i) μ)
    (hB : ∀ i i', Integrable (A.indicator fun ω => w * Bm ω i i') μ)
    (hrem : Integrable (A.indicator rem) μ) :
    ‖∫ ω, g ω * A.indicator (fun ω => lin (ℓ ω) (β ω) + quad (q ω) (β ω) + rem ω -
        w * (lin (ℓ ω) (d ω) + ∑ i, ∑ i', q ω i i' * Bm ω i i')) ω ∂μ‖ₑ ≤
      ENNReal.ofReal (Cg * C) *
        (∑ i, ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator (fun ω => β ω i) | m] ω -
            w * d ω i) ω‖ₑ ∂μ +
          ∑ i, ∑ i', ∫⁻ ω, ‖A.indicator (fun ω =>
            μ[A.indicator (fun ω => β ω i * β ω i') | m] ω - w * Bm ω i i') ω‖ₑ ∂μ) +
        ENNReal.ofReal Cg * ∫⁻ ω, ‖A.indicator rem ω‖ₑ ∂μ := by
  have hCC : 0 ≤ Cg * C := mul_nonneg hCg hC
  have hgl : ∀ i, StronglyMeasurable[m] fun ω => g ω * ℓ ω i := fun i => hg.mul (hℓ i)
  have hgq : ∀ i i', StronglyMeasurable[m] fun ω => g ω * q ω i i' := fun i i' => hg.mul (hq i i')
  have hglb : ∀ i ω, ‖g ω * ℓ ω i‖ ≤ Cg * C := fun i ω => by
    rw [norm_mul]; exact mul_le_mul (hgb ω) (hℓb ω i) (norm_nonneg _) hCg
  have hgqb : ∀ i i' ω, ‖g ω * q ω i i'‖ ≤ Cg * C := fun i i' ω => by
    rw [norm_mul]; exact mul_le_mul (hgb ω) (hqb ω i i') (norm_nonneg _) hCg
  have i1 : ∀ i, Integrable (fun ω => g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω) μ :=
    fun i => (hβ i).bdd_mul ((hgl i).mono hm).aestronglyMeasurable
      (Eventually.of_forall (hglb i))
  have i2 : ∀ i, Integrable (fun ω => g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω) μ :=
    fun i => (hd i).bdd_mul ((hgl i).mono hm).aestronglyMeasurable
      (Eventually.of_forall (hglb i))
  have i3 : ∀ i i', Integrable (fun ω => g ω * q ω i i' *
      A.indicator (fun ω => β ω i * β ω i') ω) μ :=
    fun i i' => (hββ i i').bdd_mul ((hgq i i').mono hm).aestronglyMeasurable
      (Eventually.of_forall (hgqb i i'))
  have i4 : ∀ i i', Integrable (fun ω => g ω * q ω i i' *
      A.indicator (fun ω => w * Bm ω i i') ω) μ :=
    fun i i' => (hB i i').bdd_mul ((hgq i i').mono hm).aestronglyMeasurable
      (Eventually.of_forall (hgqb i i'))
  have i5 : Integrable (fun ω => g ω * A.indicator rem ω) μ :=
    hrem.bdd_mul (hg.mono hm).aestronglyMeasurable (Eventually.of_forall hgb)
  have i12 : ∀ i, Integrable (fun ω => g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω -
      g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω) μ := fun i => (i1 i).sub (i2 i)
  have i34 : ∀ i i', Integrable (fun ω => g ω * q ω i i' *
      A.indicator (fun ω => β ω i * β ω i') ω -
        g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω) μ :=
    fun i i' => (i3 i i').sub (i4 i i')
  have i34s : ∀ i, Integrable (fun ω => ∑ i', (g ω * q ω i i' *
      A.indicator (fun ω => β ω i * β ω i') ω -
        g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω)) μ :=
    fun i => integrable_finsetSum _ fun i' _ => i34 i i'
  have I1 : Integrable (fun ω => ∑ i, (g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω -
      g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω)) μ :=
    integrable_finsetSum _ fun i _ => (i1 i).sub (i2 i)
  have I2 : Integrable (fun ω => ∑ i, ∑ i', (g ω * q ω i i' *
      A.indicator (fun ω => β ω i * β ω i') ω -
        g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω)) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => (i3 i i').sub (i4 i i')
  have I12 : Integrable (fun ω => ∑ i, (g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω -
      g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω) + ∑ i, ∑ i', (g ω * q ω i i' *
        A.indicator (fun ω => β ω i * β ω i') ω -
          g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω)) μ := I1.add I2
  rw [integral_congr_ae (Eventually.of_forall fun ω => step_decomp A β ℓ d q Bm rem g w ω),
    integral_add I12 i5, integral_add I1 I2,
    integral_finsetSum _ fun i _ => i12 i, integral_finsetSum _ fun i _ => i34s i]
  simp only [fun i => integral_sub (i1 i) (i2 i)]
  have hsum2 : ∀ i, ∫ ω, ∑ i', (g ω * q ω i i' * A.indicator (fun ω => β ω i * β ω i') ω -
      g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω) ∂μ =
        ∑ i', (∫ ω, g ω * q ω i i' * A.indicator (fun ω => β ω i * β ω i') ω ∂μ -
          ∫ ω, g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω ∂μ) := fun i => by
    rw [integral_finsetSum _ fun i' _ => i34 i i']
    exact sum_congr rfl fun i' _ => integral_sub (i3 i i') (i4 i i')
  simp only [hsum2]
  have hr : ‖∫ ω, g ω * A.indicator rem ω ∂μ‖ₑ ≤
      ENNReal.ofReal Cg * ∫⁻ ω, ‖A.indicator rem ω‖ₑ ∂μ := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [enorm_mul]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hgb ω)
  have h1 : ∀ i, ‖∫ ω, g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω ∂μ -
      ∫ ω, g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω ∂μ‖ₑ ≤
        ENNReal.ofReal (Cg * C) * ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => β ω i) | m] ω - w * d ω i) ω‖ₑ ∂μ := fun i =>
    enorm_integral_sub_le_cond hm hA (hβ i) (hd i) (hgl i) (hglb i)
  have h2 : ∀ i i', ‖∫ ω, g ω * q ω i i' * A.indicator (fun ω => β ω i * β ω i') ω ∂μ -
      ∫ ω, g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω ∂μ‖ₑ ≤
        ENNReal.ofReal (Cg * C) * ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => β ω i * β ω i') | m] ω - w * Bm ω i i') ω‖ₑ ∂μ :=
    fun i i' => enorm_integral_sub_le_cond hm hA (hββ i i') (hB i i') (hgq i i') (hgqb i i')
  calc _ ≤ ‖∑ i, (∫ ω, g ω * ℓ ω i * A.indicator (fun ω => β ω i) ω ∂μ -
          ∫ ω, g ω * ℓ ω i * A.indicator (fun ω => w * d ω i) ω ∂μ)‖ₑ +
        ‖∑ i, ∑ i', (∫ ω, g ω * q ω i i' * A.indicator (fun ω => β ω i * β ω i') ω ∂μ -
          ∫ ω, g ω * q ω i i' * A.indicator (fun ω => w * Bm ω i i') ω ∂μ)‖ₑ +
        ‖∫ ω, g ω * A.indicator rem ω ∂μ‖ₑ :=
        (enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _)
    _ ≤ ∑ i, ENNReal.ofReal (Cg * C) * ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => β ω i) | m] ω - w * d ω i) ω‖ₑ ∂μ +
        ∑ i, ∑ i', ENNReal.ofReal (Cg * C) * ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => β ω i * β ω i') | m] ω - w * Bm ω i i') ω‖ₑ ∂μ +
        ENNReal.ofReal Cg * ∫⁻ ω, ‖A.indicator rem ω‖ₑ ∂μ := by
        refine add_le_add (add_le_add ((enorm_sum_le _ _).trans (sum_le_sum fun i _ => h1 i))
          ((enorm_sum_le _ _).trans (sum_le_sum fun i _ =>
            (enorm_sum_le _ _).trans (sum_le_sum fun i' _ => h2 i i')))) hr
    _ = _ := by simp only [mul_add, mul_sum]

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
