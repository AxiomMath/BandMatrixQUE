module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.JumpNormalization

/-!
# Cyclic exponential summation and Green row bounds

This module sums the parity-free cyclic-distance estimates proved for the
nearest-neighbour Green kernel.  It keeps the block-constant correction and
the within-block mean-zero identity separate throughout.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERCyclicSummation

open scoped BigOperators
open ERDiscreteFourier ERFourierInverse ERFourierAlgebra ERCharacterAngle
  ERNearestNeighbor ERCyclicDecay ERJumpNormalization ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Canonical representatives as an explicit equivalence. -/
def zmodValEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, x.val_lt⟩
  invFun i := (i.val : ZMod n)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := by
    ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- First cyclic-distance moment of a single exponential. -/
theorem distance_mul_exp_neg_le_half_rate {γ : ℝ} (hγ : 0 < γ)
    (d : ℕ) :
    (d : ℝ) * Real.exp (-γ * d) ≤
      (2 / γ) * Real.exp (-(γ / 2) * d) := by
  let u : ℝ := γ * d / 2
  have hu : 0 ≤ u := by positivity
  have hue : u ≤ Real.exp u :=
    le_trans (by linarith : u ≤ u + 1) (Real.add_one_le_exp u)
  have hfac : 0 ≤ (2 / γ) * Real.exp (-γ * d) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hue hfac
  calc
    (d : ℝ) * Real.exp (-γ * d) =
        u * ((2 / γ) * Real.exp (-γ * d)) := by
      dsimp only [u]
      field_simp
    _ ≤ Real.exp u * ((2 / γ) * Real.exp (-γ * d)) := hmul
    _ = (2 / γ) * Real.exp (-(γ / 2) * d) := by
      rw [show Real.exp u * ((2 / γ) * Real.exp (-γ * d)) =
          (2 / γ) * (Real.exp u * Real.exp (-γ * d)) by ring,
        ← Real.exp_add]
      dsimp only [u]
      congr 1
      ring_nf

end ERNative.BlockBand.GaussianRing.ERCyclicSummation
