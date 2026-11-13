module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneSTwoUniformGap

/-!
# Direct ordinary-denominator transfer for theta-one `s₂`

The ordinary stability denominator is transferred under the uniform entry perturbation of the MDE
solutions, and the resulting lower bound is used directly in the stability quotient of
`sTwoSq_one_eq`, giving a deterministic bound on `s₂` with no radial feedback hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand.CEH

/-- Dimension-free perturbation of an ordinary (non-adjoint) normalized
product. -/
theorem norm_average_mul_sub_le_of_uniform_close
    {N : ℕ} (hN : 0 < N) (q₀ q₁ q₂ : Fin N → ℂ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ) :
    ‖average (fun i => q₁ i * q₂ i) -
      average (fun i => q₀ i * q₀ i)‖ ≤ 2 * B * δ + δ ^ 2 := by
  have hpoint (i : Fin N) :
      ‖q₁ i * q₂ i - q₀ i * q₀ i‖ ≤ 2 * B * δ + δ ^ 2 := by
    have hid : q₁ i * q₂ i - q₀ i * q₀ i =
        (q₁ i - q₀ i) * (q₂ i - q₀ i) +
        (q₁ i - q₀ i) * q₀ i + q₀ i * (q₂ i - q₀ i) := by ring
    rw [hid]
    calc
      ‖(q₁ i - q₀ i) * (q₂ i - q₀ i) +
          (q₁ i - q₀ i) * q₀ i + q₀ i * (q₂ i - q₀ i)‖ ≤
        ‖(q₁ i - q₀ i) * (q₂ i - q₀ i) +
          (q₁ i - q₀ i) * q₀ i‖ + ‖q₀ i * (q₂ i - q₀ i)‖ :=
            norm_add_le _ _
      _ ≤ ‖(q₁ i - q₀ i) * (q₂ i - q₀ i)‖ +
          ‖(q₁ i - q₀ i) * q₀ i‖ + ‖q₀ i * (q₂ i - q₀ i)‖ := by
        have hn := norm_add_le ((q₁ i - q₀ i) * (q₂ i - q₀ i))
          ((q₁ i - q₀ i) * q₀ i)
        linarith
      _ = ‖q₁ i - q₀ i‖ * ‖q₂ i - q₀ i‖ +
          ‖q₁ i - q₀ i‖ * ‖q₀ i‖ + ‖q₀ i‖ * ‖q₂ i - q₀ i‖ := by
            simp only [norm_mul]
      _ ≤ δ * δ + δ * B + B * δ := by
        gcongr
        · exact hq₁ i
        · exact hq₂ i
        · exact hq₁ i
        · exact hq₀ i
        · exact hq₀ i
        · exact hq₂ i
      _ = 2 * B * δ + δ ^ 2 := by ring
  have havg_sub : average (fun i => q₁ i * q₂ i) -
      average (fun i => q₀ i * q₀ i) =
      average (fun i => q₁ i * q₂ i - q₀ i * q₀ i) := by
    unfold average
    rw [← sub_div, Finset.sum_sub_distrib]
  rw [havg_sub]
  calc
    ‖average (fun i => q₁ i * q₂ i - q₀ i * q₀ i)‖ ≤
      averageReal (fun i => ‖q₁ i * q₂ i - q₀ i * q₀ i‖) :=
        norm_average_le hN _
    _ ≤ averageReal (fun _ : Fin N => 2 * B * δ + δ ^ 2) := by
      unfold averageReal
      gcongr with i
      exact hpoint i
    _ = 2 * B * δ + δ ^ 2 := by
      unfold averageReal
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- Direct transfer of the ordinary stability margin. -/
theorem ordinaryDenominator_lower_of_uniform_close
    {N : ℕ} (hN : 0 < N) {s c B δ : ℝ} (hs : 0 ≤ s)
    (q₀ q₁ q₂ : Fin N → ℂ) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ)
    (hboundary : c ≤ ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖) :
    c - s * (2 * B * δ + δ ^ 2) ≤
      ‖1 - (s : ℂ) * average (fun i => q₁ i * q₂ i)‖ := by
  have havg := norm_average_mul_sub_le_of_uniform_close
    hN q₀ q₁ q₂ hB hδ hq₀ hq₁ hq₂
  have hdiff :
      ‖(1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)) -
        (1 - (s : ℂ) * average (fun i => q₁ i * q₂ i))‖ ≤
          s * (2 * B * δ + δ ^ 2) := by
    rw [show (1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)) -
        (1 - (s : ℂ) * average (fun i => q₁ i * q₂ i)) =
        (s : ℂ) * (average (fun i => q₁ i * q₂ i) -
          average (fun i => q₀ i * q₀ i)) by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left havg hs
  have htri :
      ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖ ≤
        ‖(1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)) -
          (1 - (s : ℂ) * average (fun i => q₁ i * q₂ i))‖ +
        ‖1 - (s : ℂ) * average (fun i => q₁ i * q₂ i)‖ := by
    calc
      ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖ =
          ‖((1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)) -
            (1 - (s : ℂ) * average (fun i => q₁ i * q₂ i))) +
            (1 - (s : ℂ) * average (fun i => q₁ i * q₂ i))‖ := by
              congr 1
              ring
      _ ≤ _ := norm_add_le _ _
  linarith

/-- In particular, spending at most half the boundary margin leaves a uniform
half-margin at the two-energy canonical points. -/
theorem ordinaryDenominator_half_margin
    {N : ℕ} (hN : 0 < N) {s c B δ : ℝ} (hs : 0 ≤ s) (_hc : 0 ≤ c)
    (q₀ q₁ q₂ : Fin N → ℂ) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ B)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ)
    (hboundary : c ≤ ‖1 - (s : ℂ) * average (fun i => q₀ i * q₀ i)‖)
    (hbudget : s * (2 * B * δ + δ ^ 2) ≤ c / 2) :
    c / 2 ≤ ‖1 - (s : ℂ) * average (fun i => q₁ i * q₂ i)‖ := by
  have h := ordinaryDenominator_lower_of_uniform_close hN hs q₀ q₁ q₂
    hB hδ hq₀ hq₁ hq₂ hboundary
  linarith

/-- The exact canonical mixed-entry rate eventually spends at most half of
the boundary ordinary-stability margin under the given exponents. -/
theorem eventually_canonicalMixedEntryRate_denominator_budget
    {ξ β s c K : ℝ} (_hs : 0 < s) (hc : 0 < c)
    (hξβ : ξ < β) (hβ : β ≤ 1 / 2) :
    ∀ᶠ N : ℕ in Filter.atTop,
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2 := by
  have hξ : ξ < 1 := lt_of_lt_of_le hξβ (hβ.trans (by norm_num))
  have hβ1 : β < 1 := lt_of_le_of_lt hβ (by norm_num)
  have hd := tendsto_canonicalMixedEntryRate
    (s := s) (c := c) (K := K) hξ hβ1
  have hlin : Filter.Tendsto (fun N : ℕ =>
      (2 * (s * c)⁻¹) * canonicalMixedEntryRate N ξ β s c K)
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hd :
      Filter.Tendsto (fun N : ℕ =>
        (2 * (s * c)⁻¹) * canonicalMixedEntryRate N ξ β s c K)
        Filter.atTop (nhds (2 * (s * c)⁻¹ * 0)))
  have hsq : Filter.Tendsto (fun N : ℕ =>
      canonicalMixedEntryRate N ξ β s c K ^ 2)
      Filter.atTop (nhds 0) := by simpa using hd.pow 2
  have htotal : Filter.Tendsto (fun N : ℕ =>
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2))
      Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using tendsto_const_nhds.mul (hlin.add hsq)
  exact htotal.eventually
    (Iic_mem_nhds (by linarith : (0 : ℝ) < c / 2))

/-- Direct quotient bound from the transferred ordinary denominator, with no
radial feedback hypothesis. -/
theorem ordinaryStabilityQuotient_le_of_denominatorLower
    {N : ℕ} (hN : 0 < N) (lambda : ℂ)
    (M₁ M₂ Γ₁ Γ₂ A : Matrix (Fin N) (Fin N) ℂ)
    {d : ℝ} (hd : 0 < d)
    (hden : d ≤ ‖stabilityDenominator lambda (NTrace (M₁ * M₂))‖) :
    ‖NTrace (M₁ * A * Γ₂) * NTrace (Γ₁ * Aᴴ * M₂) /
        stabilityDenominator lambda (NTrace (M₁ * M₂))‖ ≤
      (‖M₁‖ * ‖A‖ * ‖Γ₂‖) * (‖Γ₁‖ * ‖A‖ * ‖M₂‖) / d := by
  rw [norm_div, norm_mul]
  apply div_le_div₀ (by positivity) _ hd hden
  calc
    ‖NTrace (M₁ * A * Γ₂)‖ * ‖NTrace (Γ₁ * Aᴴ * M₂)‖ ≤
        (‖M₁‖ * ‖A‖ * ‖Γ₂‖) * (‖Γ₁‖ * ‖Aᴴ‖ * ‖M₂‖) := by
      gcongr
      · exact norm_NTrace_three_mul_le hN M₁ A Γ₂
      · exact norm_NTrace_three_mul_le hN Γ₁ Aᴴ M₂
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose]

/-- Final deterministic `s₂` bound using the directly transferred denominator. -/
theorem sTwo_one_le_sqrt_of_denominatorLower
    {N : ℕ} (hN : 0 < N) (lambda : ℂ)
    (M₁ M₂ A : Matrix (Fin N) (Fin N) ℂ)
    {d : ℝ} (hd : 0 < d)
    (hden : d ≤ ‖stabilityDenominator lambda (NTrace (M₁ * M₂))‖) :
    sTwo 1 lambda M₁ M₂ A ≤ Real.sqrt
      (‖gammaMatrix M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖ * ‖A‖ +
        ‖lambda‖ ^ 2 *
          ((‖M₁‖ * ‖A‖ * ‖gammaMatrix M₂‖) *
            (‖gammaMatrix M₁‖ * ‖A‖ * ‖M₂‖) / d)) := by
  unfold sTwo
  apply Real.sqrt_le_sqrt
  rw [sTwoSq_one_eq]
  apply add_le_add
  · exact re_NTrace_gamma_word_le hN _ _ _
  · exact mul_le_mul_of_nonneg_left
      (ordinaryStabilityQuotient_le_of_denominatorLower hN lambda M₁ M₂
        (gammaMatrix M₁) (gammaMatrix M₂) A hd hden)
      (sq_nonneg ‖lambda‖)

end CEHNative.BlockBand.External.CEH
