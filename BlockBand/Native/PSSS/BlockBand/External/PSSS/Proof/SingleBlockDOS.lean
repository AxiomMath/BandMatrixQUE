module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalOperatorTail
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUECanonicalWegner

/-!
# Single-block density of states from the inverse tail

This file contains the sharp APSSS/PSSS single-block density-of-states output.  The
normalization is `GUE_N(1/N)`, the interval is closed, and the constant is uniform in
the dimension and deterministic Hermitian deformation.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The sharp single-block density-of-states assertion. -/
def SingleBlockDOS (C : ℝ) : Prop :=
  ∀ (N : ℕ), 0 < N →
  ∀ (A : HermitianMatrix (Fin N)) (a b : ℝ), a ≤ b →
  ∫⁻ V, (eigenCount ⟨A.1 + V.1, A.2.add V.2⟩ (Set.Icc a b) : ℝ≥0∞)
    ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N))) ≤
    ENNReal.ofReal (C * N * (b - a))

/-- A normalized eigenvector realizes the reciprocal spectral gap under the
matrix inverse.  This is the deterministic implication used on every mesh cell. -/
theorem inv_gap_le_l2_opNorm {N : ℕ} (H : HermitianMatrix (Fin N))
    (j : Fin (Fintype.card (Fin N))) (x : ℝ)
    (hunit : IsUnit (H.1 - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))) :
    |orderedEigenvalue H j - x|⁻¹ ≤
      ‖(H.1 - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ := by
  let k : Fin N :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N))) j.rev
  let v : Fin N → ℂ := (H.2.eigenvectorBasis k).ofLp
  let M : Matrix (Fin N) (Fin N) ℂ :=
    H.1 - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ = 1 :=
    H.2.eigenvectorBasis.orthonormal.1 k
  have heig : H.2.eigenvalues k = orderedEigenvalue H j := by
    simp [orderedEigenvalue, Matrix.IsHermitian.eigenvalues, k]
  have hMv : M *ᵥ v = (orderedEigenvalue H j - x : ℂ) • v := by
    dsimp [M, v]
    rw [Matrix.sub_mulVec, H.2.mulVec_eigenvectorBasis,
      Matrix.smul_mulVec, Matrix.one_mulVec, heig]
    ext q
    simp
    ring
  have hd : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det]
    simpa [M] using hunit
  have hg : (orderedEigenvalue H j - x : ℂ) ≠ 0 := by
    intro hz
    have hz' : M *ᵥ v = 0 := by simpa [hz] using hMv
    have hleft := congrArg (fun w => M⁻¹ *ᵥ w) hz'
    have hmul : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hd
    have : v = 0 := by
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, Matrix.mulVec_zero] at hleft
      exact hleft
    have hv0 : (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) = 0 := by
      simp [this]
    simp [hv0] at hv
  have hMinv : M⁻¹ *ᵥ v = ((orderedEigenvalue H j - x : ℂ)⁻¹) • v := by
    apply Matrix.mulVec_injective_of_isUnit hunit
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hd,
      Matrix.one_mulVec, Matrix.mulVec_smul, hMv]
    simp [hg]
  have hop := (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M⁻¹).le_opNorm
    (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))
  have hout : ‖(WithLp.toLp 2 (M⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin N))‖ =
      |orderedEigenvalue H j - x|⁻¹ := by
    rw [hMinv, WithLp.toLp_smul, norm_smul, hv, mul_one]
    rw [norm_inv]
    congr 1
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [Matrix.l2_opNorm_toEuclideanCLM, hv, mul_one] at hop
  have happ :
      (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M⁻¹)
        (WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N)) =
      WithLp.toLp 2 (M⁻¹ *ᵥ v) := rfl
  rw [happ, hout] at hop
  simpa [M] using hop

/-- Membership in a half-open cell, away from its left endpoint, forces the
inverse-tail event at the reciprocal cell width. -/
theorem inv_width_le_l2_opNorm_of_orderedEigenvalue_mem_Ico {N : ℕ}
    (H : HermitianMatrix (Fin N)) (i : Fin (Fintype.card (Fin N))) {l w : ℝ}
    (_hw : 0 < w) (hi : orderedEigenvalue H i ∈ Set.Ico l (l + w))
    (hne : orderedEigenvalue H i ≠ l)
    (hunit : IsUnit (H.1 - (l : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))) :
    w⁻¹ ≤ ‖(H.1 - (l : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹‖ := by
  have hgap : 0 < |orderedEigenvalue H i - l| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hle : |orderedEigenvalue H i - l| ≤ w := by
    rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_ne hi.1 (Ne.symm hne)))]
    linarith [hi.2]
  exact (inv_anti₀ hgap hle).trans (inv_gap_le_l2_opNorm H i l hunit)

end PSSSNative.BlockBand.PSSS
