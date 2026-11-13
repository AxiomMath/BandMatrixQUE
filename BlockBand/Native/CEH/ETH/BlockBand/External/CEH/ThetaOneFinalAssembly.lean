module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneSTwoPublishedAdapter

/-!
# Final theta-one assembly: canonical density and norm extraction

This file packages the last dimension-free consequences of the canonical entry
modulus needed by the published `s₂` adapter: preservation of the trace
imaginary part and a fixed operator-norm envelope.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix Filter
open scoped Matrix.Norms.L2Operator ComplexConjugate
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH

/-- A uniform entry perturbation controls its normalized average with the same
constant. -/
theorem norm_average_sub_le_of_uniform_close {N : ℕ} (hN : 0 < N)
    (q q₀ : Fin N → ℂ) {δ : ℝ} (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) :
    ‖average q - average q₀‖ ≤ δ := by
  have havg : average q - average q₀ = average (fun i => q i - q₀ i) := by
    unfold average
    rw [← sub_div, Finset.sum_sub_distrib]
  rw [havg]
  apply (norm_average_le hN _).trans
  unfold averageReal
  have hsum : (∑ i : Fin N, ‖q i - q₀ i‖) ≤
      ∑ _i : Fin N, δ := by
    gcongr with i
    exact hq i
  calc
    (∑ i : Fin N, ‖q i - q₀ i‖) / (N : ℝ) ≤
        (∑ _i : Fin N, δ) / (N : ℝ) := by gcongr
    _ = δ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr hN.ne']

/-- The canonical plus branch retains at least `c-δ` of a boundary trace
imaginary-part margin `c`. -/
theorem average_im_lower_of_uniform_close {N : ℕ} (hN : 0 < N)
    (q q₀ : Fin N → ℂ) {c δ : ℝ}
    (hboundary : c ≤ (average q₀).im)
    (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) :
    c - δ ≤ (average q).im := by
  have hn := norm_average_sub_le_of_uniform_close hN q q₀ hq
  have him : |(average q - average q₀).im| ≤ δ :=
    (Complex.abs_im_le_norm _).trans hn
  rw [Complex.sub_im] at him
  have hlower := neg_le_of_abs_le him
  linarith

/-- Consequently a half-margin is retained whenever the canonical entry rate
is at most half the boundary density margin. -/
theorem average_im_half_margin_of_uniform_close {N : ℕ} (hN : 0 < N)
    (q q₀ : Fin N → ℂ) {c δ : ℝ} (_hc : 0 ≤ c)
    (hboundary : c ≤ (average q₀).im)
    (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) (hδ : δ ≤ c / 2) :
    c / 2 ≤ (average q).im := by
  have h := average_im_lower_of_uniform_close hN q q₀ hboundary hq
  linarith

/-- Under the published exponents, the exact canonical entry rate eventually
simultaneously fits the density half-margin, a fixed unit norm envelope, and
the ordinary-denominator half-margin. -/
theorem eventually_canonical_final_budgets
    {ξ β s c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hξβ : ξ < β) (hβ : β ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 ∧
      canonicalMixedEntryRate N ξ β s c K ≤ 1 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2 := by
  have hξ : ξ < 1 := lt_of_lt_of_le hξβ (hβ.trans (by norm_num))
  have hβ1 : β < 1 := lt_of_le_of_lt hβ (by norm_num)
  have hrate := tendsto_canonicalMixedEntryRate
    (s := s) (c := c) (K := K) hξ hβ1
  have hc2 : 0 < c / 2 := by positivity
  have hhalf : ∀ᶠ N : ℕ in atTop,
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 :=
    hrate.eventually (Iic_mem_nhds hc2)
  have hone : ∀ᶠ N : ℕ in atTop,
      canonicalMixedEntryRate N ξ β s c K ≤ 1 :=
    hrate.eventually (Iic_mem_nhds zero_lt_one)
  filter_upwards [hhalf, hone,
    eventually_canonicalMixedEntryRate_denominator_budget hs hc hξβ hβ]
      with N hh ho hd
  exact ⟨hh, ho, hd⟩

/-- The fixed dimension-free operator envelope which results after the final
budget: boundary entries bounded by `(sc)⁻¹` and canonical perturbation at most
one give spectral-lift norm at most `(sc)⁻¹+1`. -/
theorem canonical_spectralLift_norm_le_fixed {N : ℕ}
    (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (q₀ q : Fin N → ℂ) {s c δ : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ (s * c)⁻¹)
    (hq : ∀ i, ‖q i - q₀ i‖ ≤ δ) (hδ : δ ≤ 1) :
    ‖spectralLift hF q‖ ≤ (s * c)⁻¹ + 1 := by
  have hbase : 0 ≤ (s * c)⁻¹ := by positivity
  have hδ0 : 0 ≤ δ := (norm_nonneg (q ⟨0, hN⟩ - q₀ ⟨0, hN⟩)).trans
    (hq ⟨0, hN⟩)
  apply (norm_spectralLift_le_of_uniform_close hF q₀ q hbase
    hδ0 hq₀ hq).trans
  gcongr

end CEHNative.BlockBand.External.CEH
