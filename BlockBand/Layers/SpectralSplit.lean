module

public import Mathlib

/-!
# The low spectral projection of a Hermitian matrix

A deterministic component of the Gaussian absorption lemma: "Let `P` project onto the `k`
eigenvectors of `D` nearest zero, and let `δ ≤ 1` be the truncated absolute value of the next
eigenvalue".

For a Hermitian `D` and a threshold `τ > 0`, `lowProjection hD τ` is the orthogonal projection onto
the eigenvectors with `|λ_j| < τ`. Then `τ ‖v - P v‖ ≤ ‖D v‖` for every Euclidean vector `v`
(this is the hypothesis `hPD` of `BlockBand.Layers.layerResolvent_bound` with `δ = τ`), `P v` lies
in the span of those eigenvectors, and that span has dimension at most `#{j | |λ_j| < τ}`.
Taking `τ = δ` (the truncated `(k+1)`-st smallest `|λ|`), the span has dimension at most `k`.
Deterministic; no dimension or norm restriction.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The coordinate mask `c ↦ (1_{|λ_j| < τ} c_j)_j` in eigen-coordinates. -/
def lowMask {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) :
    EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanLin (Matrix.diagonal fun j => if |hD.eigenvalues j| < τ then (1 : ℂ) else 0)

/-- The low spectral projection as a linear map: `v ↦ Σ_{|λ_j|<τ} ⟨e_j, v⟩ e_j`. -/
def lowProjectionLin {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) :
    EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n :=
  hD.eigenvectorBasis.repr.symm.toLinearEquiv.toLinearMap ∘ₗ lowMask hD τ ∘ₗ
    hD.eigenvectorBasis.repr.toLinearEquiv.toLinearMap

/-- The low spectral projection `P_τ` as a matrix. -/
def lowProjection {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) : Matrix n n ℂ :=
  Matrix.toEuclideanLin.symm (lowProjectionLin hD τ)

theorem toEuclideanLin_lowProjection {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) :
    Matrix.toEuclideanLin (lowProjection hD τ) = lowProjectionLin hD τ := by
  simp [lowProjection]

/-- Eigen-coordinates of `D v`: `⟨e_j, D v⟩ = λ_j ⟨e_j, v⟩`. -/
theorem repr_toEuclideanLin {D : Matrix n n ℂ} (hD : D.IsHermitian) (v : EuclideanSpace ℂ n)
    (j : n) :
    hD.eigenvectorBasis.repr (Matrix.toEuclideanLin D v) j =
      (hD.eigenvalues j : ℂ) * hD.eigenvectorBasis.repr v j := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hsym : (Matrix.toEuclideanLin D).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hD
  rw [← hsym (hD.eigenvectorBasis j) v]
  have hev : Matrix.toEuclideanLin D (hD.eigenvectorBasis j) =
      (hD.eigenvalues j : ℂ) • hD.eigenvectorBasis j := by
    ext x
    have h := congrFun (hD.mulVec_eigenvectorBasis j) x
    rw [Matrix.toLpLin_apply]
    simp only [PiLp.smul_apply]
    rw [h, Pi.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hev, inner_smul_left]
  simp

/-- Eigen-coordinates of `v - P_τ v`. -/
theorem repr_sub_lowProjection {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ)
    (v : EuclideanSpace ℂ n) (j : n) :
    hD.eigenvectorBasis.repr (v - Matrix.toEuclideanLin (lowProjection hD τ) v) j =
      (if |hD.eigenvalues j| < τ then 0 else 1) * hD.eigenvectorBasis.repr v j := by
  rw [toEuclideanLin_lowProjection, map_sub]
  simp only [lowProjectionLin, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, lowMask, PiLp.sub_apply]
  rw [Matrix.toLpLin_apply]
  simp only [Matrix.mulVec_diagonal]
  split_ifs <;> ring

/-- **Spectral gap off the low projection** (the Gaussian absorption lemma, used as
`hPD` of `layerResolvent_bound`): for Hermitian `D`, `τ ‖v - P_τ v‖ ≤ ‖D v‖` for every Euclidean
vector `v`, when `0 ≤ τ`. -/
theorem lowProjection_gap {D : Matrix n n ℂ} (hD : D.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ)
    (v : EuclideanSpace ℂ n) :
    τ * ‖v - Matrix.toEuclideanLin (lowProjection hD τ) v‖ ≤ ‖Matrix.toEuclideanLin D v‖ := by
  have hn1 : ‖v - Matrix.toEuclideanLin (lowProjection hD τ) v‖ ^ 2 =
      ∑ j, ‖(if |hD.eigenvalues j| < τ then (0 : ℂ) else 1) * hD.eigenvectorBasis.repr v j‖ ^ 2 := by
    rw [← hD.eigenvectorBasis.repr.norm_map, EuclideanSpace.norm_sq_eq]
    simp_rw [repr_sub_lowProjection hD τ v]
  have hn2 : ‖Matrix.toEuclideanLin D v‖ ^ 2 =
      ∑ j, ‖(hD.eigenvalues j : ℂ) * hD.eigenvectorBasis.repr v j‖ ^ 2 := by
    rw [← hD.eigenvectorBasis.repr.norm_map, EuclideanSpace.norm_sq_eq]
    simp_rw [repr_toEuclideanLin hD v]
  have hsq : (τ * ‖v - Matrix.toEuclideanLin (lowProjection hD τ) v‖) ^ 2 ≤
      ‖Matrix.toEuclideanLin D v‖ ^ 2 := by
    rw [mul_pow, hn1, hn2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with h
    · simp only [norm_zero, zero_pow two_ne_zero, zero_mul, mul_zero]
      positivity
    · rw [norm_one, one_pow, one_mul]
      push Not at h
      have h2 : τ ^ 2 ≤ |hD.eigenvalues j| ^ 2 := pow_le_pow_left₀ hτ h 2
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h0 : 0 ≤ τ * ‖v - Matrix.toEuclideanLin (lowProjection hD τ) v‖ := by positivity
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).mp hsq

/-- The span of the low eigenvectors `{e_j : |λ_j| < τ}`. -/
def lowSubspace {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) :
    Submodule ℂ (EuclideanSpace ℂ n) :=
  Submodule.span ℂ (Set.range fun j : {j : n // |hD.eigenvalues j| < τ} => hD.eigenvectorBasis j)

/-- `P_τ v` lies in the low span. -/
theorem lowProjection_mem {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ)
    (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (lowProjection hD τ) v ∈ lowSubspace hD τ := by
  rw [toEuclideanLin_lowProjection]
  have hexp : lowProjectionLin hD τ v =
      ∑ j, hD.eigenvectorBasis.repr (lowProjectionLin hD τ v) j • hD.eigenvectorBasis j := (hD.eigenvectorBasis.sum_repr _).symm
  rw [hexp]
  apply Submodule.sum_mem
  intro j _
  have hcoord : hD.eigenvectorBasis.repr (lowProjectionLin hD τ v) j =
      (if |hD.eigenvalues j| < τ then 1 else 0) * hD.eigenvectorBasis.repr v j := by
    simp only [lowProjectionLin, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply, lowMask]
    rw [Matrix.toLpLin_apply]
    simp [Matrix.mulVec_diagonal]
  rw [hcoord]
  split_ifs with h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, h⟩, rfl⟩)
  · simp

/-- The low span has dimension at most `#{j | |λ_j| < τ}`. -/
theorem finrank_lowSubspace_le {D : Matrix n n ℂ} (hD : D.IsHermitian) (τ : ℝ) :
    Module.finrank ℂ (lowSubspace hD τ) ≤ Fintype.card {j : n // |hD.eigenvalues j| < τ} :=
  finrank_range_le_card _

end BlockBand.Layers
