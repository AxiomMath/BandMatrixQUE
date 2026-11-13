module

public import BlockBand.SourceProcess.Closing.Defs
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Invertibility for almost every phase

For fixed matrices, `θ ↦ det(M₀ + e^{iθ}M₁)` is a polynomial in `e^{iθ}`. If `det M₀ ≠ 0` it is
nonzero, so it has finitely many roots and vanishes on a countable set of `θ`, a `phaseLaw`-null
set (`ae_isUnit_det_affine`). Consequences: `1 - zN` is invertible for a.e. phase
(`ae_isUnit_one_sub_smul`), and so is `R₀ + zL(1 - zN)⁻¹R_t` when `R₀` is
(`ae_isUnit_corner`, Schur complement of an affine block matrix).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.ClosedForm

open MeasureTheory Matrix Polynomial BlockBand.SourceProcess.Closing

theorem countable_phase_eq (r : ℂ) : {θ : ℝ | phase θ = r}.Countable := by
  by_cases hne : ∃ θ₀, phase θ₀ = r
  · obtain ⟨θ₀, h₀⟩ := hne
    refine (Set.countable_range fun n : ℤ => θ₀ + n * (2 * Real.pi)).mono ?_
    intro θ hθ
    have hexp : Complex.exp (θ * Complex.I) = Complex.exp (θ₀ * Complex.I) := by
      have := hθ.trans h₀.symm
      simpa only [phase] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat] at this
    simp only
    linarith
  · push Not at hne
    convert Set.countable_empty
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact hne θ

theorem phaseLaw_countable_null {S : Set ℝ} (hS : S.Countable) : phaseLaw S = 0 := by
  refine le_antisymm ?_ zero_le
  calc phaseLaw S = ENNReal.ofReal (2 * Real.pi)⁻¹ *
        (volume.restrict (Set.Ico 0 (2 * Real.pi))) S := by
        simp only [phaseLaw, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * volume S :=
        mul_le_mul_right (Measure.restrict_apply_le _ _) _
    _ = 0 := by rw [hS.measure_zero volume, mul_zero]

/-- **A nonzero polynomial is nonzero at almost every phase.** -/
theorem ae_phase_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ᵐ θ ∂phaseLaw, p.eval (phase θ) ≠ 0 := by
  rw [ae_iff]
  refine phaseLaw_countable_null ?_
  refine ((p.roots.toFinset.countable_toSet.biUnion fun r _ => countable_phase_eq r)).mono ?_
  intro θ hθ
  simp only [Set.mem_ofPred_eq, not_not] at hθ
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset]
  exact ⟨phase θ, (mem_roots hp).2 hθ, rfl⟩

variable {n m p : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p]

/-- **An affine determinant is nonzero at almost every phase.** -/
theorem ae_isUnit_det_affine (M₀ M₁ : Matrix n n ℂ) (h₀ : IsUnit M₀.det) :
    ∀ᵐ θ ∂phaseLaw, IsUnit (M₀ + phase θ • M₁).det := by
  set q : ℂ[X] := (M₀.map C + (X : ℂ[X]) • M₁.map C).det
  have hev : ∀ w : ℂ, q.eval w = (M₀ + w • M₁).det := by
    intro w
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
    ring
  have hq : q ≠ 0 := by
    intro h0
    have := hev 0
    rw [h0, eval_zero, zero_smul, add_zero] at this
    exact h₀.ne_zero this.symm
  filter_upwards [ae_phase_eval_ne_zero hq] with θ hθ
  rw [← hev]
  exact isUnit_iff_ne_zero.2 hθ

/-- `1 - (αz)M` is invertible at almost every phase `z`. -/
theorem ae_isUnit_one_sub_smul (α : ℂ) (M : Matrix n n ℂ) :
    ∀ᵐ θ ∂phaseLaw, IsUnit (1 - (phase θ * α) • M).det := by
  filter_upwards [ae_isUnit_det_affine 1 (-(α • M)) (by simp)] with θ hθ
  convert hθ using 2
  rw [smul_neg, smul_smul, sub_eq_add_neg]

/-- **The closed corner `R₀ + zL(1 - zN)⁻¹R_t` is invertible at almost every phase** when `R₀`
is. -/
theorem ae_isUnit_corner (R₀ : Matrix m m ℂ) (L : Matrix m p ℂ) (N : Matrix p p ℂ)
    (Rt : Matrix p m ℂ) (h₀ : IsUnit R₀.det) :
    ∀ᵐ θ ∂phaseLaw, IsUnit (R₀ + phase θ • (L * (1 - phase θ • N)⁻¹ * Rt)).det := by
  have hM₀ : IsUnit (fromBlocks (1 : Matrix p p ℂ) Rt 0 R₀).det := by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact h₀
  filter_upwards [ae_isUnit_det_affine _ (fromBlocks (-N) 0 (-L) 0) hM₀,
    (ae_isUnit_one_sub_smul 1 N)] with θ hθ hN
  rw [mul_one] at hN
  set z := phase θ
  have e : fromBlocks (1 : Matrix p p ℂ) Rt 0 R₀ + z • fromBlocks (-N) 0 (-L) 0 =
      fromBlocks (1 - z • N) Rt (-(z • L)) R₀ := by
    rw [fromBlocks_smul, fromBlocks_add]
    simp only [smul_neg, smul_zero, add_zero, zero_add, sub_eq_add_neg]
  rw [e] at hθ
  let : Invertible (1 - z • N) := (isUnit_iff_isUnit_det _ |>.mpr hN).invertible
  rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv] at hθ
  have h2 := isUnit_of_mul_isUnit_right hθ
  convert h2 using 2
  simp only [Matrix.neg_mul, Matrix.smul_mul, sub_neg_eq_add]

end BlockBand.SourceProcess.PhysApprox.ClosedForm
