module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneCompactSTwoAPI

/-!
# Regular-window theta-one closure helpers

These lemmas discharge the final scalar conversions used when the common
regular-boundary witness is opened: the strict mixed real-part estimate gives
the norm lower bound required by regularization, and the published eventual
budgets select fixed positive constants for the compact `s₂` API.
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

/-- The theta-one mixed-pairing inequality supplies the dimension-free
norm lower bound needed to control the source regularization. -/
theorem mixedPairing_norm_gt_inv_two_mul
    {N : ℕ} {s : ℝ} (hs : 0 < s)
    (M₁ M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hpair : 1 / 2 < (s * NTrace (M₁ * M₂minus)).re) :
    (2 * s)⁻¹ < ‖NTrace (M₁ * M₂minus)‖ := by
  have hp := hpair
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hp
  have hre : (2 * s)⁻¹ < (NTrace (M₁ * M₂minus)).re := by
    apply (inv_lt_iff_one_lt_mul₀ (mul_pos (by norm_num) hs)).2
    nlinarith
  exact hre.trans_le (Complex.re_le_norm _)

/-- Non-strict form directly consumable by `thetaOneCompactClosure`. -/
theorem mixedPairing_norm_ge_inv_two_mul
    {N : ℕ} {s : ℝ} (hs : 0 < s)
    (M₁ M₂minus : Matrix (Fin N) (Fin N) ℂ)
    (hpair : 1 / 2 < (s * NTrace (M₁ * M₂minus)).re) :
    (2 * s)⁻¹ ≤ ‖NTrace (M₁ * M₂minus)‖ :=
  (mixedPairing_norm_gt_inv_two_mul hs M₁ M₂minus hpair).le

/-- All fixed constants used by the compact endpoint are positive in the
published regime. -/
theorem thetaOne_regularWindow_constants_pos
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    0 ≤ (s * c)⁻¹ + 1 ∧ 0 < c / 2 ∧
      0 < (2 * s)⁻¹ ∧ 0 < c / 2 := by
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

/-- Eventual fixed constants for the regular-window witness: the canonical
entry modulus is simultaneously small enough for density, norm, and ordinary
stability, with no dimension-dependent constant remaining. -/
theorem eventually_thetaOne_regularWindow_fixed_constants
    {ξ β s c K : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hξβ : ξ < β) (hβ : β ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 ∧
      (s * c)⁻¹ + canonicalMixedEntryRate N ξ β s c K ≤
        (s * c)⁻¹ + 1 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2 := by
  filter_upwards [eventually_canonical_final_budgets hs hc hξβ hβ]
    with N hN
  refine ⟨hN.1, ?_, hN.2.2⟩
  gcongr
  exact hN.2.1

end CEHNative.BlockBand.External.CEH
