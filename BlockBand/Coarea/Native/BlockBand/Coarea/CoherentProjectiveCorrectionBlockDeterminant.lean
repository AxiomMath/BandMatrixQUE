module

public import BlockBand.Coarea.Native.BlockBand.Coarea.CoherentProjectiveCorrectionDeterminant
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Rank-one block determinant in the global projective correction

This module isolates and evaluates the real rank-one block produced by
differentiating normalized affine complex projective coordinates.  It is the
nontrivial diagonal block in the block-triangular form of the explicit global
correction differential.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

/-- The real radial covector on affine complex coordinates. -/
def projectiveRadialCovector {n : ℕ} (z : Fin n → ℂ) :
    Module.Dual ℝ (Fin n → ℂ) where
  toFun u := ∑ j, ((star (z j)) * u j).re
  map_add' u v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.add_apply, mul_add, Complex.add_re]
  map_smul' c u := by
    rw [RingHom.id_apply]
    change (∑ j, (star (z j) * (c • u j)).re) =
      c * ∑ j, (star (z j) * u j).re
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ]
    ring

@[simp] theorem projectiveRadialCovector_self {n : ℕ} (z : Fin n → ℂ) :
    projectiveRadialCovector z z = ∑ j, Complex.normSq (z j) := by
  change (∑ j, ((star (z j)) * z j).re) = _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.normSq_apply, Complex.mul_re]

/-- Squared affine radius, named locally for the determinant calculation. -/
def projectiveBlockRadiusSq {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  1 + ∑ j, Complex.normSq (z j)

/-- Rank-one angular correction to scalar radial normalization. -/
def projectiveRadialTransvection {n : ℕ} (z : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
  LinearMap.transvection
    (-((projectiveBlockRadiusSq z)⁻¹) • projectiveRadialCovector z) z

/-- The determinant defect of the radial rank-one update is exactly one
additional inverse affine-radius factor. -/
theorem det_projectiveRadialTransvection {n : ℕ} (z : Fin n → ℂ) :
    LinearMap.det (projectiveRadialTransvection z) =
      (projectiveBlockRadiusSq z)⁻¹ := by
  rw [projectiveRadialTransvection, LinearMap.transvection.det]
  simp only [LinearMap.smul_apply, projectiveRadialCovector_self,
    projectiveBlockRadiusSq, smul_eq_mul]
  have hsum : 0 ≤ ∑ j, Complex.normSq (z j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j)
  have hne : 1 + ∑ j, Complex.normSq (z j) ≠ 0 := by linarith
  field_simp
  ring

/-- The real normalized affine tangent block: uniform inverse-square-root
scaling followed by its radial rank-one correction. -/
def projectiveNormalizedTangentBlock {n : ℕ} (z : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) :=
  (Real.sqrt (projectiveBlockRadiusSq z))⁻¹ •
    projectiveRadialTransvection z

/-- Real dimension of `n` affine complex coordinates. -/
theorem finrank_real_fin_complex (n : ℕ) :
    Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
  rw [finrank_real_of_complex]
  simp

/-- Exact determinant of the normalized affine complex-projective tangent
block.  The `2n` scalar-normalization factors and the one rank-one radial
defect combine to the exponent `n+1`. -/
theorem det_projectiveNormalizedTangentBlock {n : ℕ} (z : Fin n → ℂ) :
    LinearMap.det (projectiveNormalizedTangentBlock z) =
      ((projectiveBlockRadiusSq z)⁻¹) ^ (n + 1) := by
  rw [projectiveNormalizedTangentBlock, LinearMap.det_smul,
    finrank_real_fin_complex, det_projectiveRadialTransvection]
  have hpos : 0 < projectiveBlockRadiusSq z := by
    unfold projectiveBlockRadiusSq
    have hsum : 0 ≤ ∑ j, Complex.normSq (z j) :=
      Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j)
    linarith
  have hsqrt : (Real.sqrt (projectiveBlockRadiusSq z))⁻¹ ^ 2 =
      (projectiveBlockRadiusSq z)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hpos.le]
  rw [pow_mul, hsqrt]
  ring

/-- Absolute determinant form, with the ambient eigenpair dimension `d = n+1`. -/
theorem abs_det_projectiveNormalizedTangentBlock {d : ℕ}
    (i : Fin d) (z : Fin (d - 1) → ℂ) :
    |LinearMap.det (projectiveNormalizedTangentBlock z)| =
      ((1 + ∑ j, Complex.normSq (z j))⁻¹) ^ d := by
  rw [det_projectiveNormalizedTangentBlock]
  unfold projectiveBlockRadiusSq
  have hsum : 0 ≤ ∑ j, Complex.normSq (z j) :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j)
  have hnonneg : 0 ≤ (1 + ∑ j, Complex.normSq (z j))⁻¹ :=
    inv_nonneg.mpr (by linarith)
  rw [abs_of_nonneg (pow_nonneg hnonneg _)]
  congr 1
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by
    intro hd
    subst hd
    exact Fin.elim0 i))

end CoareaNative.BlockBand
