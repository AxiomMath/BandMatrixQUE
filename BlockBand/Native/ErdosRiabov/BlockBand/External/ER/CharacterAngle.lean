module
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.GreenConvolution

/-!
# Block averages of block-constant and block-mean-zero vectors

Averaging a block-constant site vector over a block returns its block value, and the
within-block remainder `blockMeanZeroPart` averages to zero.
-/


set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERCharacterAngle

open scoped BigOperators
open ERProfile ERProfileAnalytic ERDiscreteFourier ERFourierInverse ERFourierAlgebra
  ERGreenConvolution

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Averaging a block-constant site vector returns its block value. -/
@[simp] theorem blockAverage_blockConstant (p : Params) (g : ZMod p.n → ℂ)
    (k : ZMod p.n) :
    blockAverage p (fun x => g x.1) k = g k := by
  have hW : (p.W : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt p.W_pos
  simp [blockAverage]
  field_simp

/-- Averaging the canonical within-block remainder gives zero. -/
@[simp] theorem blockAverage_blockMeanZero (p : Params)
    (f : Site p.n p.W → ℂ) (k : ZMod p.n) :
    blockAverage p (blockMeanZeroPart p f) k = 0 := by
  unfold blockAverage
  rw [sum_blockMeanZeroPart p f k]
  simp

end ERNative.BlockBand.GaussianRing.ERCharacterAngle
