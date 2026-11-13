module

public import BlockBand.Adapters.ErdosRiabov.CyclicModel.CharacterAngle
public import Mathlib

/-!
# ER stability consequences

The unique sign-dependent Herglotz transform, the spectral domain and the Θ/Ξ
matrices are defined in the core ER API.  This module contains only analytic
consequences for the core Θ scalar multiplier; it defines no copy of those objects.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERHerglotz

open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- The core Θ scalar multiplier lies in the open unit disk at nonreal
spectral arguments. -/
theorem norm_thetaMultiplier_lt_one {z₁ z₂ : ℂ}
    (h₁ : ‖erSemicircleStieltjes z₁‖ < 1)
    (h₂ : ‖erSemicircleStieltjes z₂‖ < 1) :
    ‖erSemicircleStieltjes z₁ *
      starRingEnd ℂ (erSemicircleStieltjes z₂)‖ < 1 := by
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (erSemicircleStieltjes z₁),
    norm_nonneg (erSemicircleStieltjes z₂)]

/-- The core Θ multiplier inherits an explicit radial margin from the
smaller of the two spectral heights. -/
theorem thetaMultiplier_height_margin {z₁ z₂ : ℂ}
    (h₁ : z₁.im ≠ 0) (h₂ : z₂.im ≠ 0) :
    min (1 / 2 : ℝ) (min |z₁.im| |z₂.im| / 4) ≤
      1 - ‖(erSemicircleStieltjes z₁ * starRingEnd ℂ (erSemicircleStieltjes z₂))‖ := by
  have hm₁ :=
    min_abs_im_div_four_le_one_sub_norm_erSemicircleStieltjes h₁
  have hn₁ := norm_erSemicircleStieltjes_lt_one h₁
  have hn₂ := norm_erSemicircleStieltjes_lt_one h₂
  have hsmall :
      min (1 / 2 : ℝ) (min |z₁.im| |z₂.im| / 4) ≤
        min (1 / 2 : ℝ) (|z₁.im| / 4) := by
    exact min_le_min le_rfl (div_le_div_of_nonneg_right
      (min_le_left _ _) (by norm_num))
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (erSemicircleStieltjes z₁),
    norm_nonneg (erSemicircleStieltjes z₂)]

end BlockBand.Adapters.ErdosRiabov.CyclicModel.GaussianRing.ERHerglotz
