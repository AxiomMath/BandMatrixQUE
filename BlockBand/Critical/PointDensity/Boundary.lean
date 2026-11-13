module

public import BlockBand.Palm.CoarseRelativeDyson
public import BlockBand.Palm.MomentFlow.EventNorm
public import BlockBand.Internal.Contracts.Inputs

/-!
# Point density: the boundary Dyson data of a regular deformation

Deterministic bounds on the boundary solution `m_{F,c}(x)` of the scalar Dyson equation for a
Hermitian `N × N` matrix `F` (`N ≥ 1`), `c > 0` and real `x`, and (for the location bound)
`‖F‖ ≤ N^A` with `Im m_{F,c}(x) ≥ v₀ > 0`. Here `‖F‖` is the Euclidean operator norm
(`Matrix.Norms.L2Operator`); `NormBound` is its vector form.

* `freshDyson_im_bounds`: `FreshClass F A c x r₀ s₀ v₀` gives
  `v₀ ≤ Im m_{F,c}(x) ≤ v₀⁻¹` (regularity at `s = c`, `y = x`, `η = 0`).
* `norm_freshDyson_le`: `|m_{F,s}(x)| ≤ (s Im m_{F,s}(x))⁻¹`.
* `abs_center_le`: `|x| ≤ N^A + 2 v₀⁻¹` (no a-priori bound on `x` is assumed).
* `opNorm_sub_center_le`: `‖F - x I‖ ≤ 2 N^A + 2 v₀⁻¹`.
* `isBoundaryMDE_freshM`: the resolvent `freshM F c x` solves the boundary matrix Dyson equation
  for `F - x I` at energy `0`, with normalized trace `m_{F,c}(x)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.PointDensity

open Matrix BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
  BlockBand.External
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {N : ℕ}

/-- Regularity of `F` at `(c, x)` read at `s = c`, `y = x`, `η = 0`:
`v₀ ≤ Im m_{F,c}(x) ≤ v₀⁻¹`. -/
theorem freshDyson_im_bounds {F : Matrix (Fin N) (Fin N) ℂ} {A c x r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c x r₀ s₀ v₀) :
    v₀ ≤ (freshDyson F c x).im ∧ (freshDyson F c x).im ≤ v₀⁻¹ := by
  obtain ⟨-, -, hr₀, hs₀, -, -⟩ := hK
  have h := hC.2.2 c ⟨by linarith, le_rfl⟩ x (by simp [hr₀.le]) 0 ⟨le_rfl, zero_le_one⟩
  exact h

/-- `|m_{F,s}(x)| ≤ (s Im m)⁻¹` for the positive boundary root. -/
theorem norm_freshDyson_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {x : ℝ} (hm : 0 < (freshDyson F s x).im) :
    ‖freshDyson F s x‖ ≤ (s * (freshDyson F s x).im)⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hz : (0 : ℝ) ≤ ((x : ℂ)).im := by simp
  have hres := freshDyson_residual_eq_zero hF hs hz hm
  have heq := (certificateDysonResidual_eq_zero_iff hF.eigenvalues s x _).mp hres
  have hpos : 0 < s * (freshDyson F s x).im := mul_pos hs hm
  conv_lhs => rw [heq]
  apply certificateAverage_norm_le_const
  intro i
  unfold certificateScalarResolvent
  rw [norm_inv]
  apply inv_anti₀ hpos
  have h := Complex.abs_im_le_norm (((hF.eigenvalues i : ℝ) : ℂ) -
    ((x : ℂ) + (s : ℂ) * freshDyson F s x))
  have him : (((hF.eigenvalues i : ℝ) : ℂ) - ((x : ℂ) + (s : ℂ) * freshDyson F s x)).im =
      -(s * (freshDyson F s x).im) := by simp
  rw [him, abs_neg, abs_of_pos hpos] at h
  exact h

/-- **Location of the centre.** `|x| ≤ N^A + 2 v₀⁻¹` when `‖F‖ ≤ N^A` and
`Im m_{F,c}(x) ≥ v₀ > 0`. -/
theorem abs_center_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {A c v₀ x : ℝ} (hB : NormBound F A) (hc : 0 < c) (hv0 : 0 < v₀)
    (hv : v₀ ≤ (freshDyson F c x).im) :
    |x| ≤ (N : ℝ) ^ A + 2 * v₀⁻¹ := by
  have hz : (0 : ℝ) ≤ ((x : ℂ)).im := by simp
  have hW := freshW_re_abs_le hF hN hB hc hz hv0 hv
  have hm : 0 < (freshDyson F c x).im := lt_of_lt_of_le hv0 hv
  have hre : (freshW F c x).re = x + c * (freshDyson F c x).re := by
    simp [freshW]
  rw [hre] at hW
  have hnorm := norm_freshDyson_le hF hN hc hm
  have h1 : |c * (freshDyson F c x).re| ≤ v₀⁻¹ := by
    rw [abs_mul, abs_of_pos hc]
    calc c * |(freshDyson F c x).re| ≤ c * ‖freshDyson F c x‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hc.le
      _ ≤ c * (c * (freshDyson F c x).im)⁻¹ := mul_le_mul_of_nonneg_left hnorm hc.le
      _ = ((freshDyson F c x).im)⁻¹ := by field_simp
      _ ≤ v₀⁻¹ := inv_anti₀ hv0 hv
  have h2 : |x| ≤ |x + c * (freshDyson F c x).re| + |c * (freshDyson F c x).re| := by
    have := abs_sub (x + c * (freshDyson F c x).re) (c * (freshDyson F c x).re)
    simpa using this
  linarith

/-- `‖F - x I‖ ≤ 2 N^A + 2 v₀⁻¹` (operator norm) under the hypotheses of `abs_center_le`. -/
theorem opNorm_sub_center_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {A c v₀ x : ℝ} (hB : NormBound F A) (hc : 0 < c) (hv0 : 0 < v₀)
    (hv : v₀ ≤ (freshDyson F c x).im) :
    ‖F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ 2 * (N : ℝ) ^ A + 2 * v₀⁻¹ := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hF' := BlockBand.Palm.MomentFlow.l2opNorm_le_of_normBound hB
  have hx := abs_center_le hF hN hB hc hv0 hv
  calc ‖F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)‖
      ≤ ‖F‖ + ‖(x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)‖ := norm_sub_le _ _
    _ = ‖F‖ + |x| := by rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * (N : ℝ) ^ A + 2 * v₀⁻¹ := by linarith

/-- If `Im m_{F,c}(x) > 0`, then `M = freshM F c x` satisfies the boundary matrix Dyson equation
`(F - x I - c tr(M)) M = 1` with `Im M` positive definite, and `tr M = m_{F,c}(x)`. -/
theorem isBoundaryMDE_freshM {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {c : ℝ}
    (hc : 0 < c) {x : ℝ} (hm : 0 < (freshDyson F c x).im) :
    BlockBand.Internal.Contracts.Inputs.IsBoundaryMDE c
        (F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) 0 (freshM F c x) ∧
      CEH.normalizedTrace (freshM F c x) = freshDyson F c x := by
  set m := freshDyson F c x with hmdef
  set w : ℂ := (x : ℂ) + (c : ℂ) * m with hwdef
  have hw : 0 < w.im := add_ofReal_mul_im_pos hc (by simp) hm
  have hw' : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hw.ne'
  have htr : CEH.normalizedTrace (freshM F c x) = m :=
    (freshDyson_spec_of_im_pos F c x hm).symm
  have hM : freshM F c x = (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := rfl
  refine ⟨⟨?_, ?_⟩, htr⟩
  · rw [htr]
    have hsh : F - (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) -
        (((0 : ℝ) : ℂ) + (c : ℂ) * m) • (1 : Matrix (Fin N) (Fin N) ℂ) =
        F - w • (1 : Matrix (Fin N) (Fin N) ℂ) := by
      rw [hwdef, Complex.ofReal_zero, zero_add, sub_sub, ← add_smul]
    rw [hsh, hM]
    exact hermitian_shift_mul_inv hF hw.ne'
  · set R := (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ with hR
    have hRH : Rᴴ = (F - (conj w) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
      hermitian_resolvent_conjTranspose hF w
    have himp : CEH.imaginaryPart (freshM F c x) = ((w.im : ℂ)) • (R * Rᴴ) := by
      unfold CEH.imaginaryPart
      rw [hM, hRH, hR, hermitian_resolvent_sub hF hw.ne' hw', smul_smul]
      congr 1
      rw [Complex.sub_conj]
      field_simp
      push_cast
      ring
    rw [himp]
    have hunit : IsUnit R := by
      rw [hR, Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det]
      exact hermitian_shift_det_isUnit hF hw.ne'
    have hpd : (R * Rᴴ).PosDef :=
      Matrix.PosDef.mul_conjTranspose_self R (Matrix.vecMul_injective_iff_isUnit.2 hunit)
    exact hpd.smul (by exact_mod_cast hw)

end BlockBand.Critical.PointDensity
