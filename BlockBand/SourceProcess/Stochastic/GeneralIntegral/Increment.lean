module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Setting
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Increment covariances of an `L²` integrator

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, and `h : IsL2Integrator Q 𝓖 N α`
with chosen martingale modification `M = h.mart`.

* `integral_mul_sub_eq_zero`: `E[Z (X_b - X_a)] = 0` for an `L²` martingale `X`, `a ≤ b`, and
  `Z ∈ L²(Q)` that is `𝓖_a`-a.e.-strongly measurable (no boundedness).
* `setIntegral_sq_incr`: `∫_D (M_b - M_a)² dQ = ∫_D ∫_{(a,b]} α dQ` for `D ∈ 𝓖_a`.
* `setIntegral_incr_mul_incr`: for `a₁ ≤ b₁`, `a₂ ≤ b₂` and `D ∈ 𝓖_{a₁ ∨ a₂}`,
  `∫_D (M_{b₁} - M_{a₁})(M_{b₂} - M_{a₂}) dQ = ∫_D ∫_{(a₁ ∨ a₂, b₁ ∧ b₂]} α dQ`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ}

/-- `E[Z (X_b - X_a)] = 0` for an `L²` martingale and `L²`, `𝓖_a`-a.e.-measurable `Z`. -/
theorem integral_mul_sub_eq_zero {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓖 Q) {a b : ℝ≥0}
    (hab : a ≤ b) (hb : MemLp (X b) 2 Q) {Z : Ω → ℝ} (hZ : MemLp Z 2 Q)
    (hZm : AEStronglyMeasurable[𝓖 a] Z Q) :
    ∫ ω, Z ω * (X b ω - X a ω) ∂Q = 0 := by
  have ha : MemLp (X a) 2 Q := (hb.condExp (m := 𝓖 a) one_le_two).ae_eq (hX.condExp_ae_eq hab)
  have hiv : Integrable (fun ω => Z ω * X b ω) Q := hZ.integrable_mul hb
  have hiu : Integrable (fun ω => Z ω * X a ω) Q := hZ.integrable_mul ha
  have h1 : ∫ ω, Z ω * X b ω ∂Q = ∫ ω, Z ω * X a ω ∂Q := by
    rw [← integral_condExp (𝓖.le a) (f := fun ω => Z ω * X b ω)]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_aestronglyMeasurable_left hZm hiv (hX.integrable b),
      hX.condExp_ae_eq hab] with ω h1 h2
    rw [show (fun ω => Z ω * X b ω) = Z * X b from rfl, h1]
    simp [h2]
  simp_rw [mul_sub]
  rw [integral_sub hiv hiu, h1, sub_self]

namespace IsL2Integrator

variable {N α : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure Q] in
theorem mart_incr_memLp (h : IsL2Integrator Q 𝓖 N α) (a b : ℝ≥0) :
    MemLp (fun ω => h.mart b ω - h.mart a ω) 2 Q :=
  (h.mart_memLp b).sub (h.mart_memLp a)

omit [IsFiniteMeasure Q] in
theorem mart_incr_aesm (h : IsL2Integrator Q 𝓖 N α) {a b c : ℝ≥0} (ha : a ≤ c) (hb : b ≤ c) :
    AEStronglyMeasurable[𝓖 c] (fun ω => h.mart b ω - h.mart a ω) Q :=
  (((h.mart_sm b).mono (𝓖.mono hb)).sub ((h.mart_sm a).mono (𝓖.mono ha))).aestronglyMeasurable

/-- Increment orthogonality: `E[Z (M_b - M_a)] = 0` for `Z ∈ L²`, `𝓖_a`-a.e.-measurable. -/
theorem integral_mul_incr_eq_zero (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : Ω → ℝ} (hZ : MemLp Z 2 Q) (hZm : AEStronglyMeasurable[𝓖 a] Z Q) :
    ∫ ω, Z ω * (h.mart b ω - h.mart a ω) ∂Q = 0 :=
  integral_mul_sub_eq_zero h.mart_martingale hab (h.mart_memLp b) hZ hZm

/-- Set-integral form of increment orthogonality, with `Z = 1_D Y`. -/
theorem setIntegral_mul_incr_eq_zero (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b)
    {D : Set Ω} (hD : MeasurableSet[𝓖 a] D) {Y : Ω → ℝ} (hY : MemLp Y 2 Q)
    (hYm : AEStronglyMeasurable[𝓖 a] Y Q) :
    ∫ ω in D, Y ω * (h.mart b ω - h.mart a ω) ∂Q = 0 := by
  rw [← integral_indicator (𝓖.le a D hD)]
  have := h.integral_mul_incr_eq_zero hab (hY.indicator (𝓖.le a D hD).nullMeasurableSet) (by
    refine ⟨D.indicator (hYm.mk Y), hYm.stronglyMeasurable_mk.indicator hD, ?_⟩
    filter_upwards [hYm.ae_eq_mk] with ω hω
    by_cases hωD : ω ∈ D <;> simp [hωD, hω])
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ D <;> simp [hω]

/-- **Bracket of one increment.** `∫_D (M_b - M_a)² = ∫_D ∫_{(a,b]} α` for `D ∈ 𝓖_a`. -/
theorem setIntegral_sq_incr (h : IsL2Integrator Q 𝓖 N α) {a b : ℝ≥0} (hab : a ≤ b)
    {D : Set Ω} (hD : MeasurableSet[𝓖 a] D) :
    ∫ ω in D, (h.mart b ω - h.mart a ω) ^ 2 ∂Q = ∫ ω in D, bracketIntegral α a b ω ∂Q := by
  set M := h.mart
  have hK := h.comp_martingale.setIntegral_eq hab hD
  have hKt (t : ℝ≥0) : h.comp t =ᵐ[Q] fun ω => M t ω ^ 2 - bracketIntegral α 0 t ω := by
    filter_upwards [h.bracketIntegral_zero_ae t] with ω hω
    rw [hω]; ring
  have e1 : ∫ ω in D, (M b ω ^ 2 - bracketIntegral α 0 b ω) ∂Q =
      ∫ ω in D, (M a ω ^ 2 - bracketIntegral α 0 a ω) ∂Q := by
    rw [← setIntegral_congr_ae (𝓖.le a D hD) ((hKt a).mono fun ω h _ => h),
      ← setIntegral_congr_ae (𝓖.le a D hD) ((hKt b).mono fun ω h _ => h)]
    exact hK.symm
  have e2 := h.setIntegral_mul_incr_eq_zero hab hD (h.mart_memLp a)
    (h.mart_sm a).aestronglyMeasurable
  have i1 : Integrable (fun ω => M b ω ^ 2 - bracketIntegral α 0 b ω) Q :=
    (h.mart_memLp b).integrable_sq.sub (h.integrable_bracketIntegral_zero b)
  have i2 : Integrable (fun ω => M a ω ^ 2 - bracketIntegral α 0 a ω) Q :=
    (h.mart_memLp a).integrable_sq.sub (h.integrable_bracketIntegral_zero a)
  have i3 : Integrable (bracketIntegral α a b) Q := h.integrable_bracketIntegral hab
  have i4 : Integrable (fun ω => M a ω * (M b ω - M a ω)) Q :=
    (h.mart_memLp a).integrable_mul (h.mart_incr_memLp a b)
  have i5 : Integrable (fun ω => (M b ω ^ 2 - bracketIntegral α 0 b ω) -
      (M a ω ^ 2 - bracketIntegral α 0 a ω)) Q := i1.sub i2
  have i6 : Integrable (fun ω => (M b ω ^ 2 - bracketIntegral α 0 b ω) -
      (M a ω ^ 2 - bracketIntegral α 0 a ω) + bracketIntegral α a b ω) Q := i5.add i3
  have i7 : Integrable (fun ω => 2 * (M a ω * (M b ω - M a ω))) Q := i4.const_mul 2
  have hexp : ∀ᵐ ω ∂Q, (M b ω - M a ω) ^ 2 =
      ((M b ω ^ 2 - bracketIntegral α 0 b ω) - (M a ω ^ 2 - bracketIntegral α 0 a ω) +
        bracketIntegral α a b ω) - 2 * (M a ω * (M b ω - M a ω)) := by
    filter_upwards [h.bracketIntegral_sub hab] with ω hω
    rw [hω]; ring
  rw [setIntegral_congr_ae (𝓖.le a D hD) (hexp.mono fun ω h _ => h),
    integral_sub i6.integrableOn i7.integrableOn,
    integral_add i5.integrableOn i3.integrableOn,
    integral_sub i1.integrableOn i2.integrableOn, e1, integral_const_mul, e2]
  ring

/-- Two increments from a common left endpoint. -/
theorem setIntegral_incr_mul_incr_same (h : IsL2Integrator Q 𝓖 N α) {a b₁ b₂ : ℝ≥0}
    (h₁ : a ≤ b₁) (h₂ : a ≤ b₂) {D : Set Ω} (hD : MeasurableSet[𝓖 a] D) :
    ∫ ω in D, (h.mart b₁ ω - h.mart a ω) * (h.mart b₂ ω - h.mart a ω) ∂Q =
      ∫ ω in D, bracketIntegral α a (min b₁ b₂) ω ∂Q := by
  wlog hle : b₁ ≤ b₂ generalizing b₁ b₂
  · rw [min_comm, ← this h₂ h₁ (le_of_not_ge hle)]
    simp_rw [mul_comm]
  set M := h.mart
  have hD1 : MeasurableSet[𝓖 b₁] D := 𝓖.mono h₁ D hD
  have e0 := h.setIntegral_mul_incr_eq_zero hle hD1 (h.mart_incr_memLp a b₁)
    (h.mart_incr_aesm h₁ le_rfl)
  have hsplit : (fun ω => (M b₁ ω - M a ω) * (M b₂ ω - M a ω)) =
      fun ω => (M b₁ ω - M a ω) ^ 2 + (M b₁ ω - M a ω) * (M b₂ ω - M b₁ ω) := by
    funext ω; ring
  have i1 : Integrable (fun ω => (M b₁ ω - M a ω) ^ 2) Q := (h.mart_incr_memLp a b₁).integrable_sq
  have i2 : Integrable (fun ω => (M b₁ ω - M a ω) * (M b₂ ω - M b₁ ω)) Q :=
    (h.mart_incr_memLp a b₁).integrable_mul (h.mart_incr_memLp b₁ b₂)
  rw [hsplit, integral_add i1.integrableOn i2.integrableOn,
    e0, add_zero, min_eq_left hle, h.setIntegral_sq_incr h₁ hD]

/-- **Increment covariance.** For `a₁ ≤ b₁`, `a₂ ≤ b₂` and `D ∈ 𝓖_{a₁ ∨ a₂}`:
`∫_D (M_{b₁} - M_{a₁})(M_{b₂} - M_{a₂}) = ∫_D ∫_{(a₁ ∨ a₂, b₁ ∧ b₂]} α`. -/
theorem setIntegral_incr_mul_incr (h : IsL2Integrator Q 𝓖 N α) {a₁ b₁ a₂ b₂ : ℝ≥0}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) {D : Set Ω} (hD : MeasurableSet[𝓖 (max a₁ a₂)] D) :
    ∫ ω in D, (h.mart b₁ ω - h.mart a₁ ω) * (h.mart b₂ ω - h.mart a₂ ω) ∂Q =
      ∫ ω in D, bracketIntegral α (max a₁ a₂) (min b₁ b₂) ω ∂Q := by
  wlog hle : a₁ ≤ a₂ generalizing a₁ b₁ a₂ b₂
  · rw [max_comm, min_comm, ← this h₂ h₁ (by rwa [max_comm]) (le_of_not_ge hle)]
    simp_rw [mul_comm]
  set M := h.mart
  rw [max_eq_right hle] at hD ⊢
  by_cases hb : b₁ ≤ a₂
  · have e0 := h.setIntegral_mul_incr_eq_zero h₂ hD
      (h.mart_incr_memLp a₁ b₁) (h.mart_incr_aesm (h₁.trans hb) hb)
    have he : ∀ ω, bracketIntegral α a₂ (min b₁ b₂) ω = 0 := by
      intro ω
      rw [bracketIntegral, Ioc_eq_empty_of_le (by exact_mod_cast (min_le_left _ _).trans hb),
        Measure.restrict_empty, integral_zero_measure]
    simp only [he, integral_zero]
    exact e0
  · have hlt : a₂ ≤ b₁ := (lt_of_not_ge hb).le
    have e0 := h.setIntegral_mul_incr_eq_zero h₂ hD
      (h.mart_incr_memLp a₁ a₂) (h.mart_incr_aesm hle le_rfl)
    have hsplit : (fun ω => (M b₁ ω - M a₁ ω) * (M b₂ ω - M a₂ ω)) =
        fun ω => (M a₂ ω - M a₁ ω) * (M b₂ ω - M a₂ ω) +
          (M b₁ ω - M a₂ ω) * (M b₂ ω - M a₂ ω) := by
      funext ω; ring
    have i1 : Integrable (fun ω => (M a₂ ω - M a₁ ω) * (M b₂ ω - M a₂ ω)) Q :=
      (h.mart_incr_memLp a₁ a₂).integrable_mul (h.mart_incr_memLp a₂ b₂)
    have i2 : Integrable (fun ω => (M b₁ ω - M a₂ ω) * (M b₂ ω - M a₂ ω)) Q :=
      (h.mart_incr_memLp a₂ b₁).integrable_mul (h.mart_incr_memLp a₂ b₂)
    rw [hsplit, integral_add i1.integrableOn i2.integrableOn, e0, zero_add, h.setIntegral_incr_mul_incr_same hlt h₂ hD]

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
