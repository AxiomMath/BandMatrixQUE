module

public import BlockBand.SourceProcess.PhysApprox.B3StopTailFixed

/-!
# An abstract second-moment bound

On a probability space with a sub-σ-algebra `m`, a set `A` a.e. equal to an `m`-event `A'`, and
a variable `δ` with `1_A δ conj δ` integrable:
`E[1_A |δ|²] ≤ E|1_A (E[1_A δ conj δ | m] − β)| + C` whenever `‖β‖ ≤ C` on `A`
(`lintegral_indicator_sq_le`). `integrable_indicator_mul_conj`: a finite fourth moment on `A`
gives the integrability.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local.GramMom

open MeasureTheory
open scoped ENNReal ComplexConjugate

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The integral of a stopped `X` is that of its stopped conditional expectation. -/
theorem integral_indicator_condExp [IsFiniteMeasure μ] (hm : m ≤ m0) {A A' : Set Ω}
    (hA' : MeasurableSet[m] A') (hAA : A =ᵐ[μ] A') {X : Ω → ℂ}
    (hX : Integrable (A.indicator X) μ) :
    ∫ ω, A.indicator X ω ∂μ = ∫ ω, A.indicator (μ[A.indicator X | m]) ω ∂μ := by
  have hAA' : A' ∩ A =ᵐ[μ] A :=
    (hAA.symm.inter (Filter.EventuallyEq.refl _ A)).trans (by rw [Set.inter_self])
  have e : A'.indicator (A.indicator X) =ᵐ[μ] A.indicator X := by
    rw [Set.indicator_indicator]
    exact indicator_ae_eq_of_ae_eq_set hAA'
  have h1 : μ[A.indicator X | m] =ᵐ[μ] A'.indicator (μ[A.indicator X | m]) :=
    (condExp_congr_ae e.symm).trans (condExp_indicator hX hA')
  have h2 : A'.indicator (μ[A.indicator X | m]) =ᵐ[μ] A.indicator (μ[A.indicator X | m]) :=
    indicator_ae_eq_of_ae_eq_set hAA.symm
  rw [← integral_condExp hm, integral_congr_ae (h1.trans h2)]

/-- **Replacing the conditional expectation by a coefficient `β` bounded by `C` on `A`.** -/
theorem enorm_integral_indicator_le_add [IsProbabilityMeasure μ] (hm : m ≤ m0) {A A' : Set Ω}
    (hA' : MeasurableSet[m] A') (hAA : A =ᵐ[μ] A') {X : Ω → ℂ}
    (hX : Integrable (A.indicator X) μ) {β : Ω → ℂ} {C : ℝ} (hβ : ∀ ω ∈ A, ‖β ω‖ ≤ C) :
    ‖∫ ω, A.indicator X ω ∂μ‖ₑ ≤
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - β ω) ω‖ₑ ∂μ +
        ENNReal.ofReal C := by
  rw [integral_indicator_condExp hm hA' hAA hX]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ ω, ‖A.indicator (μ[A.indicator X | m]) ω‖ₑ ∂μ
      ≤ ∫⁻ ω, (‖A.indicator (fun ω => μ[A.indicator X | m] ω - β ω) ω‖ₑ +
          ENNReal.ofReal C) ∂μ := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
          calc ‖μ[A.indicator X | m] ω‖ₑ = ‖(μ[A.indicator X | m] ω - β ω) + β ω‖ₑ := by
                rw [sub_add_cancel]
            _ ≤ ‖μ[A.indicator X | m] ω - β ω‖ₑ + ‖β ω‖ₑ := enorm_add_le _ _
            _ ≤ _ := by
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hβ ω hω)
        · rw [Set.indicator_of_notMem hω]
          simp
    _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- `1_A δ conj δ` is the real `1_A |δ|²`. -/
theorem indicator_mul_conj (A : Set Ω) (δ : Ω → ℂ) :
    (A.indicator fun ω => δ ω * conj (δ ω)) =
      fun ω => ((A.indicator (fun ω => ‖δ ω‖ ^ 2) ω : ℝ) : ℂ) := by
  funext ω
  by_cases hω : ω ∈ A
  · simp [hω, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [hω]

theorem sq_le_one_add_pow_four (x : ℝ≥0∞) : x ^ 2 ≤ 1 + x ^ 4 := by
  rcases le_total x 1 with hx | hx
  · exact (pow_le_one₀ zero_le hx).trans le_self_add
  · exact (pow_le_pow_right₀ hx (by norm_num)).trans le_add_self

/-- **A finite fourth moment on `A` makes `1_A δ conj δ` integrable.** -/
theorem integrable_indicator_mul_conj [IsFiniteMeasure μ] {A A' : Set Ω} (hA' : MeasurableSet A')
    (hAA : A =ᵐ[μ] A') {δ : Ω → ℂ} (hδ : Measurable δ)
    (h4 : ∫⁻ ω, A.indicator (fun ω => ‖δ ω‖ₑ ^ 4) ω ∂μ ≠ ∞) :
    Integrable (A.indicator fun ω => δ ω * conj (δ ω)) μ := by
  rw [indicator_mul_conj]
  refine Integrable.ofReal ⟨((hδ.norm.pow_const 2).indicator hA').aestronglyMeasurable.congr
    (indicator_ae_eq_of_ae_eq_set hAA).symm, ?_⟩
  show ∫⁻ ω, ‖A.indicator (fun ω => ‖δ ω‖ ^ 2) ω‖ₑ ∂μ < ∞
  refine lt_of_le_of_lt (b := ∫⁻ ω, (1 + A.indicator (fun ω => ‖δ ω‖ₑ ^ 4) ω) ∂μ)
    (lintegral_mono fun ω => ?_) ?_
  · by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, enorm_pow, enorm_norm]
      exact sq_le_one_add_pow_four _
    · rw [Set.indicator_of_notMem hω]
      simp
  · rw [lintegral_add_left measurable_const, lintegral_const]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.one_lt_top (measure_lt_top _ _),
      h4.lt_top⟩

/-- **The second moment on `A` through the conjugate pair** (`δ' = conj δ`). -/
theorem lintegral_indicator_sq_le [IsProbabilityMeasure μ] (hm : m ≤ m0) {A A' : Set Ω}
    (hA' : MeasurableSet[m] A') (hAA : A =ᵐ[μ] A') {δ δ' : Ω → ℂ}
    (hδ' : ∀ ω, δ' ω = conj (δ ω)) (hX : Integrable (A.indicator fun ω => δ ω * δ' ω) μ)
    {β : Ω → ℂ} {C : ℝ} (hβ : ∀ ω ∈ A, ‖β ω‖ ≤ C) :
    ∫⁻ ω, A.indicator (fun ω => ‖δ ω‖ₑ ^ 2) ω ∂μ ≤
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator (fun ω => δ ω * δ' ω) | m] ω - β ω) ω‖ₑ ∂μ +
        ENNReal.ofReal C := by
  obtain rfl : δ' = fun ω => conj (δ ω) := funext hδ'
  refine le_trans (le_of_eq ?_) (enorm_integral_indicator_le_add hm hA' hAA hX hβ)
  have hg : Integrable (A.indicator fun ω => ‖δ ω‖ ^ 2) μ := by
    have := hX.re
    rw [indicator_mul_conj] at this
    simpa using this
  have hg0 : ∀ ω, 0 ≤ A.indicator (fun ω => ‖δ ω‖ ^ 2) ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
  rw [indicator_mul_conj]
  beta_reduce
  rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg hg0), ofReal_integral_eq_lintegral_ofReal hg
      (Filter.Eventually.of_forall hg0)]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero]

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local.GramMom
