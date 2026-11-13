module

public import BlockBand.Critical.MatrixClosing.Boundary.Circle
public import BlockBand.Critical.MatrixClosing.MiddleShift.Forms
public import BlockBand.Critical.Collar.Kernel.BoundaryIdentity

/-!
# Matrix closing, boundary clause: rank-one damped twists (finite linear algebra)

Deterministic, on an arbitrary finite index type; `quadForm M u = Re u*Mu`. No hypothesis is used.

* `twist w u = I - (1-w)uu*`; `quad_inv_twist` (rank-one inverse identity),
  **`quadForm_poissonKernel_twist`**: `u*𝒫(T(I - (1-w)uu*))u = P(wζ)`, `ζ = 1 - (u*(1-T)⁻¹u)⁻¹`.
* `re_quad_inv_ge` (`Re q ≥ 1/2` for contractions), `re_quad_inv_eq` (`Re q = 1/2` for unitaries),
  `norm_one_sub_inv_le` (`|ζ| ≤ 1`), `cay_two_mul_im` (`c(2 Im q) = 1 - q⁻¹` when `Re q = 1/2`).
* `isUnit_det_one_sub_mul_twist`, `one_sub_mul_twist_mul_conjTranspose`,
  `posSemidef_one_sub_mul_twist`, `conductance_mul_twist` (`g = 1 - |w|² ≤ 1`),
  `posSemidef_one_sub_unitary_mul`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Boundary

open Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open scoped ComplexOrder ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one damped twist `I - (1 - w)uu*`. -/
def twist (w : ℂ) (u : ι → ℂ) : Matrix ι ι ℂ := 1 - (1 - w) • vecMulVec u (star u)

omit [DecidableEq ι] in
theorem star_dotProduct_conjTranspose_mulVec (A : Matrix ι ι ℂ) (u : ι → ℂ) :
    star u ⬝ᵥ (Aᴴ *ᵥ u) = conj (star u ⬝ᵥ (A *ᵥ u)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, Complex.star_def, map_sum,
    map_mul, Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `u*𝒫(M)u = 2 Re u*(1 - M)⁻¹u - 1` for a unit vector `u`. -/
theorem quadForm_poissonKernel (M : Matrix ι ι ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    quadForm (Critical.poissonKernel M) u = 2 * (star u ⬝ᵥ ((1 - M)⁻¹ *ᵥ u)).re - 1 := by
  unfold quadForm Critical.poissonKernel
  have h : (1 - Mᴴ)⁻¹ = ((1 - M)⁻¹)ᴴ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_one]
  rw [h, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add,
    star_dotProduct_conjTranspose_mulVec, one_mulVec, hu]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
  ring

/-- **The rank-one inverse identity**:
for a unit vector `u`, `q = u*(1 - T)⁻¹u ≠ 0`, and invertible `1 - T`, `1 - T(I - (1-w)uu*)`,
`u*(1 - T(I - (1-w)uu*))⁻¹u = (1 - wζ)⁻¹`, `ζ = 1 - q⁻¹`. -/
theorem quad_inv_twist (T : Matrix ι ι ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) (w : ℂ)
    (hT : IsUnit (1 - T).det) (hT' : IsUnit (1 - T * twist w u).det)
    (hq : star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u) ≠ 0) :
    star u ⬝ᵥ ((1 - T * twist w u)⁻¹ *ᵥ u) =
      (1 - w * (1 - (star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u))⁻¹))⁻¹ := by
  set q := star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u)
  set R := (1 - T)⁻¹
  set y := (1 - T * twist w u)⁻¹ *ᵥ u
  set a := star u ⬝ᵥ y
  have hy : (1 - T * twist w u) *ᵥ y = u := by
    simp only [y, mulVec_mulVec, mul_nonsing_inv _ hT', one_mulVec]
  have hsplit : (1 - T * twist w u) *ᵥ y = (1 - T) *ᵥ y + ((1 - w) * a) • (T *ᵥ u) := by
    have hP : vecMulVec u (star u) *ᵥ y = a • u := by rw [vecMulVec_mulVec, op_smul_eq_smul]
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, twist, sub_mulVec, one_mulVec, smul_mulVec, hP,
      mulVec_sub, mulVec_smul, mulVec_smul, smul_smul, sub_mulVec, one_mulVec]
    abel
  have hRT : R *ᵥ (T *ᵥ u) = R *ᵥ u - u := by
    have : T *ᵥ u = u - (1 - T) *ᵥ u := by rw [sub_mulVec, one_mulVec]; abel
    rw [this, mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hT, one_mulVec]
  have hR1 : R *ᵥ ((1 - T) *ᵥ y) = y := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hT, one_mulVec]
  have hy2 : y + ((1 - w) * a) • (R *ᵥ u - u) = R *ᵥ u := by
    have := congrArg (R *ᵥ ·) (hsplit.symm.trans hy)
    simp only [mulVec_add, mulVec_smul, hR1, hRT] at this
    exact this
  have ha : a + (1 - w) * a * (q - 1) = q := by
    have := congrArg (star u ⬝ᵥ ·) hy2
    simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, hu, smul_eq_mul] at this
    exact this
  have hden : w + (1 - w) * q ≠ 0 := by
    intro h
    apply hq
    have : a * (w + (1 - w) * q) = q := by linear_combination ha
    rw [h, mul_zero] at this
    exact this.symm
  have ha' : a = q / (w + (1 - w) * q) := by
    rw [eq_div_iff hden]; linear_combination ha
  change a = _
  rw [ha']
  field_simp
  ring

/-- **The scalar Poisson kernel of a damped twist**: `u*𝒫(T(I - (1-w)uu*))u = P(wζ)`,
`ζ = 1 - (u*(1-T)⁻¹u)⁻¹`. -/
theorem quadForm_poissonKernel_twist (T : Matrix ι ι ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1)
    (w : ℂ) (hT : IsUnit (1 - T).det) (hT' : IsUnit (1 - T * twist w u).det)
    (hq : star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u) ≠ 0) :
    quadForm (Critical.poissonKernel (T * twist w u)) u =
      pk w (1 - (star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u))⁻¹) := by
  rw [quadForm_poissonKernel _ hu, quad_inv_twist T hu w hT hT' hq, pk]

/-- For a contraction (`I - TT* ⪰ 0`) with `1 - T` invertible and unit `u`,
`Re u*(1 - T)⁻¹u ≥ 1/2`. -/
theorem re_quad_inv_ge (T : Matrix ι ι ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1)
    (hT : IsUnit (1 - T).det) (hc : (1 - T * Tᴴ).PosSemidef) :
    1 / 2 ≤ (star u ⬝ᵥ ((1 - T)⁻¹ *ᵥ u)).re := by
  have h := (Collar.Kernel.poissonKernel_posSemidef T hT hc).dotProduct_mulVec_nonneg u
  have h2 : 0 ≤ quadForm (Critical.poissonKernel T) u := by
    unfold quadForm; exact (RCLike.nonneg_iff.mp h).1
  rw [quadForm_poissonKernel T hu] at h2
  linarith

/-- For a unitary `V` (`VV* = 1`) with `1 - V` invertible, `Re u*(1 - V)⁻¹u = 1/2`. -/
theorem re_quad_inv_eq (V : Matrix ι ι ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1)
    (hV : IsUnit (1 - V).det) (hU : V * Vᴴ = 1) :
    (star u ⬝ᵥ ((1 - V)⁻¹ *ᵥ u)).re = 1 / 2 := by
  have h := Collar.Kernel.poissonKernel_eq_sandwich V hV
  rw [hU, sub_self, Matrix.mul_zero, Matrix.zero_mul] at h
  have h2 := quadForm_poissonKernel V hu
  rw [h] at h2
  simp [quadForm] at h2
  linarith

/-- `‖1 - q⁻¹‖ ≤ 1` when `Re q ≥ 1/2`. -/
theorem norm_one_sub_inv_le {q : ℂ} (hq : 1 / 2 ≤ q.re) : ‖1 - q⁻¹‖ ≤ 1 := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  have hn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  rw [show (1 : ℂ) - q⁻¹ = (q - 1) / q by field_simp, norm_div, div_le_one hn]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- **The Cayley phase of the boundary value**: if `Re q = 1/2`, then
`c(2 Im q) = 1 - q⁻¹` (`1/(1 - e^{iθ}) = 1/2 + (i/2)cot(θ/2)`). -/
theorem cay_two_mul_im {q : ℂ} (hq : q.re = 1 / 2) : cay (2 * q.im) = 1 - q⁻¹ := by
  set y := q.im
  have hqe : q = (1 / 2 : ℂ) + (y : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hq, y]
  have hq0 : (1 / 2 : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hd := ofReal_sub_I_ne_zero (2 * y)
  rw [hqe, cay, eq_comm, eq_div_iff hd]
  have h : ((2 * y : ℝ) : ℂ) - Complex.I = (-2 * Complex.I) * ((1 / 2 : ℂ) + y * Complex.I) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [sub_mul, one_mul, h, mul_comm _ (-2 * Complex.I * _), mul_assoc (-2 * Complex.I) _ _,
    mul_inv_cancel₀ hq0, mul_one]
  push_cast; ring_nf; rw [Complex.I_sq]; ring

/-!
## The damped twist of a unitary matrix
-/

omit [DecidableEq ι] in
theorem star_dotProduct_eq_conj (u x : ι → ℂ) : star x ⬝ᵥ u = conj (star u ⬝ᵥ x) := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [DecidableEq ι] in
theorem vecMulVec_mul_self {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    vecMulVec u (star u) * vecMulVec u (star u) = vecMulVec u (star u) := by
  rw [vecMulVec_mul_vecMulVec, hu, one_smul]

omit [Fintype ι] [DecidableEq ι] in
theorem conjTranspose_vecMulVec_self (u : ι → ℂ) :
    (vecMulVec u (star u))ᴴ = vecMulVec u (star u) := by
  rw [conjTranspose_vecMulVec, star_star]

omit [Fintype ι] in
theorem conjTranspose_twist (w : ℂ) (u : ι → ℂ) :
    (twist w u)ᴴ = 1 - conj (1 - w) • vecMulVec u (star u) := by
  rw [twist, conjTranspose_sub, conjTranspose_one, conjTranspose_smul,
    conjTranspose_vecMulVec_self]; rfl

/-- `(I - (1-w)P)(I - (1-w)P)* = I - (1 - |w|²)P`, `P = uu*`. -/
theorem twist_mul_conjTranspose (w : ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    twist w u * (twist w u)ᴴ = 1 - ((1 - Complex.normSq w : ℝ) : ℂ) • vecMulVec u (star u) := by
  rw [conjTranspose_twist, twist]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_self hu]
  have : ((1 - Complex.normSq w : ℝ) : ℂ) = (1 - w) + conj (1 - w) - conj (1 - w) * (1 - w) := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self]; simp only [map_sub, map_one]; ring
  rw [this]
  module

/-- The same for `(I - (1-w)P)*(I - (1-w)P)`. -/
theorem conjTranspose_twist_mul (w : ℂ) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    (twist w u)ᴴ * twist w u = 1 - ((1 - Complex.normSq w : ℝ) : ℂ) • vecMulVec u (star u) := by
  rw [conjTranspose_twist, twist]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_self hu]
  have : ((1 - Complex.normSq w : ℝ) : ℂ) = (1 - w) + conj (1 - w) - (1 - w) * conj (1 - w) := by
    push_cast; rw [Complex.normSq_eq_conj_mul_self]; simp only [map_sub, map_one]; ring
  rw [this]
  module

/-- **The damped twist of a unitary is invertible off the identity**: if `r*r = 1`, `1 - r` is
invertible, `u` is a unit vector and `‖w‖ < 1`, then `1 - r(I - (1-w)uu*)` is invertible. -/
theorem isUnit_det_one_sub_mul_twist {r : Matrix ι ι ℂ} (hr : rᴴ * r = 1)
    (h1 : IsUnit (1 - r).det) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) {w : ℂ} (hw : ‖w‖ < 1) :
    IsUnit (1 - r * twist w u).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x₁ x₂ hx
  rw [← sub_eq_zero]
  set x := x₁ - x₂
  have hv : (1 - r * twist w u) *ᵥ x = 0 := by simp only [x, mulVec_sub, hx, sub_self]
  clear_value x
  set a := star u ⬝ᵥ x
  set c := (1 - w) * a
  have hz : twist w u *ᵥ x = x - c • u := by
    rw [twist, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  have hrz : r *ᵥ (x - c • u) = x := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hz, sub_eq_zero] at hv
    exact hv.symm
  -- the norm of `x - c u` equals that of `x`
  have hnorm : star (x - c • u) ⬝ᵥ (x - c • u) = star x ⬝ᵥ x := by
    conv_rhs => rw [← hrz]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hr, one_mulVec]
  have hxu : star x ⬝ᵥ u = conj a := star_dotProduct_eq_conj u x
  rw [star_sub, star_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, hxu, hu] at hnorm
  simp only [smul_eq_mul, Complex.star_def] at hnorm
  have hw2 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hkey : (Complex.normSq a : ℂ) * (1 - (Complex.normSq w : ℂ)) = 0 := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [c, map_mul, map_sub, map_one] at hnorm
    linear_combination -hnorm
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 hkey with h | h
    · exact Complex.normSq_eq_zero.1 (by exact_mod_cast h)
    · exfalso
      have : (Complex.normSq w : ℂ) = 1 := by linear_combination -h
      have := congrArg Complex.re this
      simp at this
      linarith
  have hc0 : c = 0 := by simp [c, ha0]
  rw [hc0, zero_smul, sub_zero] at hrz
  have h1' : (1 - r) *ᵥ x = 0 := by rw [sub_mulVec, one_mulVec, hrz, sub_self]
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h1)
  exact hinj (h1'.trans (mulVec_zero _).symm)

/-- `1 - (r t)(r t)* = (1 - |w|²)(ru)(ru)*` for unitary `r` (`rr* = 1`), `t = I - (1-w)uu*`. -/
theorem one_sub_mul_twist_mul_conjTranspose {r : Matrix ι ι ℂ} (hr : r * rᴴ = 1) (w : ℂ)
    {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    1 - (r * twist w u) * (r * twist w u)ᴴ =
      ((1 - Complex.normSq w : ℝ) : ℂ) • vecMulVec (r *ᵥ u) (star (r *ᵥ u)) := by
  have e : (r * twist w u) * (r * twist w u)ᴴ = r * (twist w u * (twist w u)ᴴ) * rᴴ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e, twist_mul_conjTranspose w hu, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hr,
    Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, ← star_mulVec]
  abel

/-- `r(I - (1-w)uu*)` is a contraction for unitary `r` and `‖w‖ ≤ 1`. -/
theorem posSemidef_one_sub_mul_twist {r : Matrix ι ι ℂ} (hr : r * rᴴ = 1) {w : ℂ}
    (hw : ‖w‖ < 1) {u : ι → ℂ} (hu : star u ⬝ᵥ u = 1) :
    (1 - (r * twist w u) * (r * twist w u)ᴴ).PosSemidef := by
  rw [one_sub_mul_twist_mul_conjTranspose hr w hu]
  have hw2 : 0 ≤ 1 - Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast hw2)

/-- **Conductance of the damped twist**: `g(r(I - (1-w)uu*)) = 1 - |w|²` for `r*r = 1`. -/
theorem conductance_mul_twist {r : Matrix ι ι ℂ} (hr : rᴴ * r = 1) (w : ℂ) {u : ι → ℂ}
    (hu : star u ⬝ᵥ u = 1) : Critical.conductance (r * twist w u) = 1 - Complex.normSq w := by
  unfold Critical.conductance
  have e : (r * twist w u)ᴴ * (r * twist w u) = (twist w u)ᴴ * twist w u := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc rᴴ, hr, Matrix.one_mul]
  rw [e, conjTranspose_twist_mul w hu, sub_sub_cancel, trace_smul, trace_vecMulVec,
    dotProduct_comm, hu, smul_eq_mul, mul_one, Complex.ofReal_re]

/-- A unitary left factor preserves contractions. -/
theorem posSemidef_one_sub_unitary_mul {U V : Matrix ι ι ℂ} (hU : U * Uᴴ = 1)
    (hV : (1 - V * Vᴴ).PosSemidef) : (1 - (U * V) * (U * V)ᴴ).PosSemidef := by
  have e : 1 - (U * V) * (U * V)ᴴ = U * (1 - V * Vᴴ) * Uᴴ := by
    rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact hV.mul_mul_conjTranspose_same U

end BlockBand.Critical.MatrixClosing.Boundary
