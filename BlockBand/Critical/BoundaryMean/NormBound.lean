module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm of a Hermitian matrix from its quadratic form

If `|Re ⟨q, M q⟩| ≤ c ‖q‖²` for every vector `q` and `M` is Hermitian, then the `L²` operator
norm of `M` is at most `c`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- **Hermitian quadratic-form bound gives an operator-norm bound.** -/
theorem norm_le_of_abs_re_quad_le {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ q : ι → ℂ, |(star q ⬝ᵥ (M *ᵥ q)).re| ≤ c * ∑ x, ‖q x‖ ^ 2) : ‖M‖ ≤ c := by
  rw [l2_opNorm_def]
  set T := (toEuclideanLin (𝕜 := ℂ) (m := ι) (n := ι)).trans LinearMap.toContinuousLinearMap M
  have hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hM
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hT]
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · subst hx; simp [hc]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf, abs_div,
    abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 := h (WithLp.ofLp x)
  have hn : ‖x‖ ^ 2 = ∑ i, ‖WithLp.ofLp x i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  have hi : RCLike.re (inner ℂ (T x) x) = (star (WithLp.ofLp x) ⬝ᵥ (M *ᵥ WithLp.ofLp x)).re := by
    simp only [T, LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap']
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.toEuclideanLin, dotProduct, Pi.star_apply, mul_comm]
  rw [hi, hn]
  exact h1

end BlockBand.Critical.BoundaryMean
