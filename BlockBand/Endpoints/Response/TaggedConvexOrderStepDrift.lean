module

public import BlockBand.Endpoints.Response.TaggedConvexOrderCoreBackward
public import BlockBand.Endpoints.Response.ResponseVarianceTrace
public import Mathlib.Analysis.Convex.Deriv

/-!
# The drift deficit of Step 4: `P'` a projection and `0 ≤ (v*Pv)(v*P'v) ≤ X²` (item (c))

* `tcs_conj_projection`: `S*S = I`, `P` an orthogonal projection ⇒ `S*PS` an orthogonal projection.
* `tcs_nearProjection_hermitian`, `tcs_nearProjection_idem`: `P = diag(I_W, 0)`.
* `tcs_quad_proj_nonneg`, `tcs_quad_proj_le`: `0 ≤ v*Pv ≤ ‖v‖²` for an orthogonal projection.
* `tcs_drift_sign`: `0 ≤ (v*Pv)(v*P'v) ≤ X²`, `X = ‖v‖²`.
* `tcs_convex_deriv2_nonneg`: a polynomial convex on `[0,∞)` has `ψ'' ≥ 0` on `[0,∞)`.
* `tcs_deficit_pointwise`: `ψ''(X)((v*Pv)(v*P'v) - X²) ≤ 0` for convex `ψ` (the integrand of the
  drift deficit `d_l` of `TcsOneStepSplitAlong`).
* `tcs_deficit_coeff_sum`: `Σ_{m≤M} ψ_m m(m-1)x^{m-2} = ψ''(x)` for `deg ψ ≤ M` (the
  coefficientwise form of the deficit used in `TcsOneStepSplitAlong`).
* `tcs_deficit_integral_nonpos`: the integrated deficit is `≤ 0` when `P'` is a projection a.e.
* `tcs_deficit_sign_clause`: the sign clause of `TcsOneStepSplitAlong` for a deficit of the
  form `d(m) = c E[m(m-1)X^{m-2}(G - X²)]`, `c ≥ 0`, `0 ≤ X`, `G ≤ X²` a.e.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder

/-- **`S*PS` is an orthogonal projection** for `S*S = I` and `P` an orthogonal projection. -/
theorem tcs_conj_projection {ι : Type*} [Fintype ι] [DecidableEq ι] {S P : Matrix ι ι ℂ}
    (hS : Sᴴ * S = 1) (hPh : Pᴴ = P) (hPP : P * P = P) :
    (Sᴴ * P * S)ᴴ = Sᴴ * P * S ∧ (Sᴴ * P * S) * (Sᴴ * P * S) = Sᴴ * P * S := by
  have hS' : S * Sᴴ = 1 := mul_eq_one_comm.1 hS
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPh, Matrix.mul_assoc]
  · calc Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * (S * Sᴴ) * P * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * (P * P) * S := by rw [hS', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Sᴴ * P * S := by rw [hPP]

theorem tcs_nearProjection_hermitian (W : ℕ) : (nearProjection W)ᴴ = nearProjection W := by
  unfold nearProjection
  rw [diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : x.1 = 0 <;> simp [h]

theorem tcs_nearProjection_idem (W : ℕ) : nearProjection W * nearProjection W = nearProjection W := by
  unfold nearProjection
  rw [diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases h : x.1 = 0 <;> simp [h]

/-- **Item (c): `P' = 𝕊*P𝕊` is an orthogonal projection** at a path with Hermitian blocks and
invertible `𝓜` (both almost sure under `growthPathLaw`). -/
theorem tcs_pathProjection {b e : ℝ} {W n : ℕ} {ω : GrowthPath W}
    (hH : ∀ k, (ω.1 k).IsHermitian) (hM : IsUnit (fullPathMatrix b e W n ω).det) :
    ((scatteringMatrix b e W n ω)ᴴ * nearProjection W * scatteringMatrix b e W n ω)ᴴ =
        (scatteringMatrix b e W n ω)ᴴ * nearProjection W * scatteringMatrix b e W n ω ∧
      ((scatteringMatrix b e W n ω)ᴴ * nearProjection W * scatteringMatrix b e W n ω) *
          ((scatteringMatrix b e W n ω)ᴴ * nearProjection W * scatteringMatrix b e W n ω) =
        (scatteringMatrix b e W n ω)ᴴ * nearProjection W * scatteringMatrix b e W n ω := by
  have hS : (scatteringMatrix b e W n ω)ᴴ * scatteringMatrix b e W n ω = 1 := by
    rw [rvD_scattering_eq]; exact rvD_scattering_unitary hH hM
  exact tcs_conj_projection hS (tcs_nearProjection_hermitian W) (tcs_nearProjection_idem W)

/-- `v*Pv = ‖Pv‖²` for an orthogonal projection. -/
theorem tcs_quad_proj_eq {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (v : ι → ℂ) : star v ⬝ᵥ (P *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
  calc star v ⬝ᵥ (P *ᵥ v) = star v ⬝ᵥ ((Pᴴ * P) *ᵥ v) := by rw [hPh, hPP]
    _ = star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem tcs_quad_proj_nonneg {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hPh : Pᴴ = P)
    (hPP : P * P = P) (v : ι → ℂ) : 0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re := by
  rw [tcs_quad_proj_eq hPh hPP]
  exact (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg _)).1

theorem tcs_quad_proj_le {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (v : ι → ℂ) :
    (star v ⬝ᵥ (P *ᵥ v)).re ≤ (star v ⬝ᵥ v).re := by
  have hQh : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hPh]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hPP]
    abel
  have h := tcs_quad_proj_nonneg hQh hQQ v
  have e : star v ⬝ᵥ v = star v ⬝ᵥ (P *ᵥ v) + star v ⬝ᵥ ((1 - P) *ᵥ v) := by
    rw [← dotProduct_add, ← add_mulVec, add_sub_cancel, one_mulVec]
  rw [e, Complex.add_re]
  linarith

/-- **The drift sign**: for orthogonal projections `P, P'` and `X = ‖v‖²`,
`0 ≤ (v*Pv)(v*P'v) ≤ X²`. -/
theorem tcs_drift_sign {ι : Type*} [Fintype ι] [DecidableEq ι] {P P' : Matrix ι ι ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (hP'h : P'ᴴ = P') (hP'P' : P' * P' = P') (v : ι → ℂ) :
    0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re * (star v ⬝ᵥ (P' *ᵥ v)).re ∧
      (star v ⬝ᵥ (P *ᵥ v)).re * (star v ⬝ᵥ (P' *ᵥ v)).re ≤ (star v ⬝ᵥ v).re ^ 2 := by
  have a0 := tcs_quad_proj_nonneg hPh hPP v
  have b0 := tcs_quad_proj_nonneg hP'h hP'P' v
  have a1 := tcs_quad_proj_le hPh hPP v
  have b1 := tcs_quad_proj_le hP'h hP'P' v
  refine ⟨mul_nonneg a0 b0, ?_⟩
  rw [sq]
  exact mul_le_mul a1 b1 b0 (a0.trans a1)

/-- A polynomial convex on `[0,∞)` has nonnegative second derivative on `[0,∞)`. -/
theorem tcs_convex_deriv2_nonneg {ψ : ℝ[X]} (hψ : ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x))
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (derivative (derivative ψ)).eval x := by
  have hmono : MonotoneOn (deriv fun y => ψ.eval y) (Set.Ici 0) :=
    hψ.monotoneOn_deriv fun y _ => ψ.differentiableAt
  have e : (deriv fun y => ψ.eval y) = fun y => (derivative ψ).eval y := by
    funext y; exact Polynomial.deriv ψ
  rw [e] at hmono
  have hacc : AccPt x (Filter.principal (Set.Ici x)) := by
    have e : Set.Ici x \ {x} = Set.Ioi x := by
      ext y; simp [lt_iff_le_and_ne]
    rw [accPt_principal_iff_nhdsWithin, e]
    infer_instance
  exact ((derivative ψ).hasDerivAt x).hasDerivWithinAt.nonneg_of_monotoneOn hacc
    (hmono.mono (Set.Ici_subset_Ici.2 hx))

/-- **The deficit integrand is nonpositive** for convex `ψ`:
`ψ''(X)((v*Pv)(v*P'v) - X²) ≤ 0`, `X = ‖v‖²`. -/
theorem tcs_deficit_pointwise {ι : Type*} [Fintype ι] [DecidableEq ι] {P P' : Matrix ι ι ℂ}
    (hPh : Pᴴ = P) (hPP : P * P = P) (hP'h : P'ᴴ = P') (hP'P' : P' * P' = P') {ψ : ℝ[X]}
    (hψ : ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x)) (v : ι → ℂ) :
    (derivative (derivative ψ)).eval (star v ⬝ᵥ v).re *
      ((star v ⬝ᵥ (P *ᵥ v)).re * (star v ⬝ᵥ (P' *ᵥ v)).re - (star v ⬝ᵥ v).re ^ 2) ≤ 0 := by
  have hX : 0 ≤ (star v ⬝ᵥ v).re := (Complex.nonneg_iff.1 (dotProduct_star_self_nonneg v)).1
  exact mul_nonpos_of_nonneg_of_nonpos (tcs_convex_deriv2_nonneg hψ hX)
    (sub_nonpos.2 (tcs_drift_sign hPh hPP hP'h hP'P' v).2)

/-- **Coefficient form of `ψ''`**: `Σ_{m≤M} ψ_m m(m-1) x^{m-2} = ψ''(x)` for `deg ψ ≤ M`. -/
theorem tcs_deficit_coeff_sum {ψ : ℝ[X]} {M : ℕ} (hM : ψ.natDegree ≤ M) (x : ℝ) :
    ∑ m ∈ range (M + 1), ψ.coeff m * ((m : ℝ) * ((m : ℝ) - 1) * x ^ (m - 2)) =
      (derivative (derivative ψ)).eval x := by
  conv_rhs => rw [ψ.as_sum_range' (M + 1) (by omega)]
  simp only [derivative_sum, eval_finsetSum, derivative_monomial, eval_monomial]
  refine sum_congr rfl fun m _ => ?_
  rcases m with _ | m
  · simp
  · rw [show m + 1 - 1 - 1 = m + 1 - 2 by omega, Nat.add_sub_cancel]
    push_cast
    ring

/-- **The integrated deficit is nonpositive**: for a random vector `v` and a
random `P'` that is an orthogonal projection almost surely, and `ψ` convex on `[0,∞)`,
`E[ψ''(X)((v*Pv)(v*P'v) - X²)] ≤ 0`. No integrability is needed (the Bochner integral of an a.e.
nonpositive function is nonpositive). -/
theorem tcs_deficit_integral_nonpos {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    (P' : Ω → Matrix ι ι ℂ) (hP' : ∀ᵐ ω ∂μ, (P' ω)ᴴ = P' ω ∧ P' ω * P' ω = P' ω)
    (v : Ω → ι → ℂ) {ψ : ℝ[X]} (hψ : ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x)) :
    ∫ ω, (derivative (derivative ψ)).eval (star (v ω) ⬝ᵥ v ω).re *
      ((star (v ω) ⬝ᵥ (P *ᵥ v ω)).re * (star (v ω) ⬝ᵥ (P' ω *ᵥ v ω)).re -
        (star (v ω) ⬝ᵥ v ω).re ^ 2) ∂μ ≤ 0 := by
  refine integral_nonpos_of_ae ?_
  filter_upwards [hP'] with ω hω
  exact tcs_deficit_pointwise hPh hPP hω.1 hω.2 hψ (v ω)

/-- **The sign clause of `TcsOneStepSplitAlong` for a deficit of the paper's form**: if
`d(m) = c ∫ m(m-1)X^{m-2}(G - X²) dμ` with `c ≥ 0`, `X ≥ 0` and `G ≤ X²` a.e. (for
`G = (v*Pv)(v*P'v)`, `X = ‖v‖²` this is `tcs_drift_sign`) and each term integrable, then
`Σ_{m≤M} ψ_m d(m) = c E[ψ''(X)(G - X²)] ≤ 0` for every `ψ` convex on `[0,∞)` with `deg ψ ≤ M`. -/
theorem tcs_deficit_sign_clause {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X G : Ω → ℝ)
    (hXG : ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ G ω ≤ X ω ^ 2) {c : ℝ} (hc : 0 ≤ c) (M : ℕ)
    (hint : ∀ m ∈ range (M + 1),
      Integrable (fun ω => (m : ℝ) * ((m : ℝ) - 1) * X ω ^ (m - 2) * (G ω - X ω ^ 2)) μ)
    {ψ : ℝ[X]} (hψ : ConvexOn ℝ (Set.Ici 0) (fun x => ψ.eval x)) (hdeg : ψ.natDegree ≤ M) :
    ∑ m ∈ range (M + 1), ψ.coeff m *
      (c * ∫ ω, (m : ℝ) * ((m : ℝ) - 1) * X ω ^ (m - 2) * (G ω - X ω ^ 2) ∂μ) ≤ 0 := by
  have e : ∑ m ∈ range (M + 1), ψ.coeff m *
      (c * ∫ ω, (m : ℝ) * ((m : ℝ) - 1) * X ω ^ (m - 2) * (G ω - X ω ^ 2) ∂μ) =
      c * ∫ ω, (derivative (derivative ψ)).eval (X ω) * (G ω - X ω ^ 2) ∂μ := by
    have h1 : ∀ ω, (derivative (derivative ψ)).eval (X ω) * (G ω - X ω ^ 2) =
        ∑ m ∈ range (M + 1),
          ψ.coeff m * ((m : ℝ) * ((m : ℝ) - 1) * X ω ^ (m - 2) * (G ω - X ω ^ 2)) := by
      intro ω
      rw [← tcs_deficit_coeff_sum hdeg (X ω), sum_mul]
      exact sum_congr rfl fun m _ => by ring
    simp_rw [h1]
    rw [integral_finsetSum _ fun m hm => (hint m hm).const_mul _, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
    ring
  rw [e]
  refine mul_nonpos_of_nonneg_of_nonpos hc (integral_nonpos_of_ae ?_)
  filter_upwards [hXG] with ω hω
  exact mul_nonpos_of_nonneg_of_nonpos (tcs_convex_deriv2_nonneg hψ hω.1)
    (sub_nonpos.2 hω.2)

end BlockBand.Endpoints
