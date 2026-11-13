module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhaseFixedUnitaryCompletion

/-!
# Unitarity of the phase-fixed Householder frame

This module proves the finite-dimensional identity
`PhaseFixedHouseholderUnitaryIdentity` (`phaseFixedHouseholderUnitaryIdentity`).  The proof computes the squared length
of `v + eᵢ`, identifies the associated rank-one outer product as twice an
idempotent, and expands the Householder square.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix

private theorem phaseFixedHouseholderShift_star_dotProduct
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ)) :
    star (phaseFixedHouseholderShift i v) ⬝ᵥ
        phaseFixedHouseholderShift i v =
      (((2 * (1 + (v i).re) : ℝ)) : ℂ) := by
  let e : EuclideanSpace ℂ ι := EuclideanSpace.single i 1
  have hw : WithLp.toLp 2 (phaseFixedHouseholderShift i v) = v + e := by
    ext j
    simp [phaseFixedHouseholderShift, phaseFixedCoordinateVector, e,
      Pi.single_apply]
  have hvv : inner ℂ v v = 1 := by
    rw [← inner_self_ofReal_re, inner_self_eq_norm_sq, hv]
    norm_num
  have hinner : inner ℂ (v + e) (v + e) =
      (((2 * (1 + (v i).re) : ℝ)) : ℂ) := by
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp only [hvv, e, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_right, map_one, one_mul]
    rw [hreal]
    simp
    ring
  rw [← dotProduct_comm]
  rw [← EuclideanSpace.inner_eq_star_dotProduct]
  rw [hw, hinner]

/-- The explicit positive-phase Householder matrix is unitary. -/
theorem phaseFixedHouseholderFrame_unitary
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) (hreal : v i = ((v i).re : ℂ))
    (hpos : 0 < (v i).re) :
    (phaseFixedHouseholderFrame i v)ᴴ *
      phaseFixedHouseholderFrame i v = 1 := by
  let w : ι → ℂ := phaseFixedHouseholderShift i v
  let d : ℝ := 1 + (v i).re
  let c : ℂ := ((d⁻¹ : ℝ) : ℂ)
  let P : Matrix ι ι ℂ := c • Matrix.vecMulVec w (star w)
  have hd : d ≠ 0 := by
    dsimp [d]
    linarith
  have hc : c * (((2 * d : ℝ)) : ℂ) = 2 := by
    dsimp [c]
    push_cast
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    field_simp [hdC]
  have hdot : star w ⬝ᵥ w = (((2 * d : ℝ)) : ℂ) := by
    simpa [w, d] using
      phaseFixedHouseholderShift_star_dotProduct i v hv hreal
  have hPstar : Pᴴ = P := by
    dsimp [P]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
    simp [c, w]
  have hPsq : P * P = (2 : ℂ) • P := by
    dsimp [P]
    rw [smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec, hdot]
    ext a b
    change c * c * (w a * (↑(2 * d) * star (w b))) =
      2 * (c * (w a * star (w b)))
    have hc' : c * c * (((2 * d : ℝ)) : ℂ) = 2 * c := by
      rw [mul_assoc, hc]
      ring
    calc
      c * c * (w a * (↑(2 * d) * star (w b))) =
          (c * c * ↑(2 * d)) * (w a * star (w b)) := by ring
      _ = 2 * c * (w a * star (w b)) := by rw [hc']
      _ = 2 * (c * (w a * star (w b))) := by ring
  have hframe : phaseFixedHouseholderFrame i v = -1 + P := by
    rfl
  rw [hframe, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_one, hPstar]
  calc
    (-1 + P) * (-1 + P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P - P + (2 : ℂ) • P := by rw [hPsq]
    _ = 1 := by
      rw [two_smul ℂ P]
      abel

/-- The formerly conditional algebraic interface is inhabited. -/
theorem phaseFixedHouseholderUnitaryIdentity :
    PhaseFixedHouseholderUnitaryIdentity where
  unitary := fun i v hv hreal hpos =>
    phaseFixedHouseholderFrame_unitary i v hv hreal hpos

/-- Every ordered least-entry eigenline chart has an unconditional unitary
Householder completion. -/
theorem orderedEigenlineHouseholderFrame_unitary_unconditional
    {d : ℕ} (r : HermitianEigenRank d)
    (p : OrderedEigenlineChartIndex d)
    (x : hermitianSimpleSpectrumCoordinates d) :
    (orderedEigenlineHouseholderFrame d r p x)ᴴ *
      orderedEigenlineHouseholderFrame d r p x = 1 :=
  orderedEigenlineHouseholderFrame_unitary
    phaseFixedHouseholderUnitaryIdentity r p x

end CoareaNative.BlockBand
