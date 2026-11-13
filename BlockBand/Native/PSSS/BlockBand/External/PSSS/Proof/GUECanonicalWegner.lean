module

public import Mathlib.MeasureTheory.Integral.Layercake
public import BlockBand.Native.PSSS.BlockBand.Analysis.CauchyResolventBound
public import BlockBand.Native.PSSS.BlockBand.LinearAlgebra.MeasurableMatrixInverse
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEBlockExpectedCountPoisson

/-!
# Endpoint-null and Fatou bridges for the canonical GUE Wegner estimate

This module develops the measure-theoretic passage from the positive-height
Ward bound to a closed-interval eigenvalue count.  Endpoint exclusions are
proved from the canonical GUE determinant-null theorem rather than assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- A nonzero determinant of the real-shifted pencil excludes an eigenvalue at
that energy, hence its singleton multiplicity count is zero. -/
theorem eigenCount_singleton_eq_zero_of_det_energyShift_ne_zero {N : ℕ}
    (H : HermitianMatrix (Fin N)) (e : ℝ)
    (hdet : (H.1 - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det ≠ 0) :
    eigenCount H {e} = 0 := by
  apply (eigenCount_singleton_eq_zero_iff H e).2
  intro i hi
  let j : Fin N :=
    Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin N))) i.rev
  have heig : H.property.eigenvalues j = e := by
    simpa [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, j] using hi
  let v : Fin N → ℂ := (H.property.eigenvectorBasis j).ofLp
  have hvne : v ≠ 0 := by
    dsimp [v]
    exact (WithLp.ofLp_eq_zero 2).ne.2
      (H.property.eigenvectorBasis.orthonormal.ne_zero j)
  have hzero :
      (H.1 - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v = 0 := by
    dsimp [v]
    rw [Matrix.sub_mulVec, H.property.mulVec_eigenvectorBasis,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [heig]
  have hu : IsUnit
      (H.1 - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hinv := Matrix.nonsing_inv_mul
    (H.1 - (e : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) hu
  have happ := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M *ᵥ v) hinv
  rw [← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero,
    Matrix.one_mulVec] at happ
  exact hvne happ.symm

/-- Explicit positive-height sequence used for the Fatou passage. -/
def canonicalWegnerEta (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem canonicalWegnerEta_pos (n : ℕ) : 0 < canonicalWegnerEta n := by
  unfold canonicalWegnerEta
  positivity

theorem tendsto_canonicalWegnerEta_zero :
    Tendsto canonicalWegnerEta atTop (𝓝 0) := by
  unfold canonicalWegnerEta
  apply tendsto_inv_atTop_zero.comp
  exact tendsto_atTop_add_const_right atTop 1
    tendsto_natCast_atTop_atTop

theorem tendsto_canonicalWegnerEta_nhdsGT_zero :
    Tendsto canonicalWegnerEta atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_canonicalWegnerEta_zero, ?_⟩
  filter_upwards with n
  exact canonicalWegnerEta_pos n

end PSSSNative.BlockBand.PSSS
