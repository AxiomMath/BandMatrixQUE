module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.HerglotzCompatibility

/-!
# Physical nearest-neighbour resolvent identities

This module starts the spatial part of the corrected Erdős–Riabov analysis.  It
derives the exact inhomogeneous three-term recurrence satisfied by the Fourier
Green kernel and identifies the full-site tensor Green kernel.  These are
physical-operator identities, not Fourier-coordinate certificates.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace ERNative.BlockBand.GaussianRing.ERNearestNeighbor

open scoped BigOperators
open ERProfile ERDiscreteFourier ERFourierInverse ERFourierAlgebra
  ERGreenConvolution ERCharacterAngle ERHerglotz

local instance (p : Params) : NeZero p.n := p.nNeZero

/-- Kronecker delta on the cyclic block ring. -/
def cyclicDelta {n : ℕ} (y x : ZMod n) : ℂ := if x = y then 1 else 0

@[simp] theorem cyclicDelta_self {n : ℕ} (x : ZMod n) :
    cyclicDelta x x = 1 := by
  simp [cyclicDelta]

@[simp] theorem cyclicDelta_apply {n : ℕ} (x y : ZMod n) :
    cyclicDelta y x = if x = y then 1 else 0 := rfl

/-- Block average of a physical-site point mass. -/
theorem blockAverage_pointMass (p : Params) (y : Site p.n p.W)
    (k : ZMod p.n) :
    blockAverage p (fun u => if u = y then 1 else 0) k =
      (if k = y.1 then 1 / (p.W : ℂ) else 0) := by
  by_cases hk : k = y.1
  · subst k
    have hsum :
        ∑ i : Fin p.W, (if (y.1, i) = y then (1 : ℂ) else 0) = 1 := by
      calc
        ∑ i : Fin p.W, (if (y.1, i) = y then (1 : ℂ) else 0) =
            (if (y.1, y.2) = y then 1 else 0) := by
          apply Finset.sum_eq_single y.2
          · intro j _ hj
            simp only [ite_eq_right_iff]
            intro h
            exact False.elim (hj (congrArg Prod.snd h))
          · intro h
            exact False.elim (h (Finset.mem_univ y.2))
        _ = 1 := by simp
    unfold blockAverage
    rw [hsum]
    simp
  · have hsum :
        ∑ i : Fin p.W, (if (k, i) = y then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hk (congrArg Prod.fst h))
    unfold blockAverage
    rw [hsum]
    simp [hk]

end ERNative.BlockBand.GaussianRing.ERNearestNeighbor
