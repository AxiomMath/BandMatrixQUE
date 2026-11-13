module

public import BlockBand.SourceProcess.Sampling.DetLin
public import Mathlib.Analysis.Matrix.Order

/-!
# A Lipschitz bound for `Re det(I + Σ_k c_k u_k u_k*)⁻¹` in the vectors `u_k`

For `Z ⪰ 0` and `c ≥ 0` the matrix determinant lemma gives
`F(Z + c uu*) = F(Z)(1 + c u*Ku)⁻¹`, `K = (I + Z)⁻¹`, `F = invDet`. With `K = B*B`,
`0 ≤ K ≤ I` and `|(1+a)⁻¹ - (1+b)⁻¹| ≤ |√a - √b|`:

`|F(Z + c uu*) - F(Z + c vv*)| ≤ √c ‖u - v‖₂` (`abs_invDet_rankOne_sub_le`),

and, replacing one rank-one term at a time,
`|F(Z + Σ_k c_k u_ku_k*) - F(Z + Σ_k c_k v_kv_k*)| ≤ Σ_k √c_k ‖u_k - v_k‖₂`
(`abs_invDet_sum_sub_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix BlockBand.SourceProcess.Sampling
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Euclidean norm `‖w‖₂ = (Σ_x |w_x|²)^{1/2}`. -/
def l2 (w : n → ℂ) : ℝ := Real.sqrt (∑ x, ‖w x‖ ^ 2)

omit [DecidableEq n] in
theorem l2_nonneg (w : n → ℂ) : 0 ≤ l2 w := Real.sqrt_nonneg _

omit [DecidableEq n] in
theorem l2_eq_norm (w : n → ℂ) : l2 w = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

omit [DecidableEq n] in
theorem abs_l2_sub_le (u v : n → ℂ) : |l2 u - l2 v| ≤ l2 (u - v) := by
  rw [l2_eq_norm, l2_eq_norm, l2_eq_norm, WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

omit [DecidableEq n] in
theorem dot_self_eq (w : n → ℂ) : star w ⬝ᵥ w = ((∑ x, ‖w x‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [DecidableEq n] in
theorem l2_sq (w : n → ℂ) : l2 w ^ 2 = (star w ⬝ᵥ w).re := by
  rw [l2, Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _), dot_self_eq, Complex.ofReal_re]

omit [DecidableEq n] in
theorem l2_le_of_sq_le {u v : n → ℂ} (h : (star u ⬝ᵥ u).re ≤ (star v ⬝ᵥ v).re) :
    l2 u ≤ l2 v := by
  rw [← l2_sq, ← l2_sq] at h
  exact (pow_le_pow_iff_left₀ (l2_nonneg u) (l2_nonneg v) two_ne_zero).1 h

theorem abs_inv_one_add_sq_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |(1 + x ^ 2)⁻¹ - (1 + y ^ 2)⁻¹| ≤ |x - y| := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  rw [inv_sub_inv h1.ne' h2.ne', abs_div, abs_of_pos (mul_pos h1 h2),
    div_le_iff₀ (mul_pos h1 h2)]
  have e : (1 + y ^ 2) - (1 + x ^ 2) = (y - x) * (y + x) := by ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg hy hx), abs_sub_comm]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), mul_nonneg (sq_nonneg x) (sq_nonneg y)]

/-- `|(1+a)⁻¹ - (1+b)⁻¹| ≤ |√a - √b|` for `a, b ≥ 0`. -/
theorem abs_inv_one_add_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(1 + a)⁻¹ - (1 + b)⁻¹| ≤ |Real.sqrt a - Real.sqrt b| := by
  have h := abs_inv_one_add_sq_sub_le (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  rwa [Real.sq_sqrt ha, Real.sq_sqrt hb] at h

/-- The matrix determinant lemma `det(A + wv*) = det A (1 + v A⁻¹ w)`. -/
theorem det_add_vecMulVec {A : Matrix n n ℂ} (hA : IsUnit A.det) (w v : n → ℂ) :
    (A + vecMulVec w v).det = A.det * (1 + v ⬝ᵥ (A⁻¹ *ᵥ w)) := by
  have e : A + vecMulVec w v = A * (1 + vecMulVec (A⁻¹ *ᵥ w) v) := by
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, mulVec_mulVec, mul_nonsing_inv _ hA,
      one_mulVec]
  rw [e, det_mul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

omit [Fintype n] in
theorem posDef_one_add {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) : (1 + Z).PosDef :=
  PosDef.one.add_posSemidef hZ

theorem isUnit_det_one_add {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) : IsUnit (1 + Z).det :=
  isUnit_iff_ne_zero.2 (posDef_one_add hZ).det_pos.ne'

/-- **Rank-one update**: `F(Z + c uu*) = F(Z)(1 + c Re u*(I+Z)⁻¹u)⁻¹`. -/
theorem invDet_add_rankOne {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) (c : ℝ) (u : n → ℂ) :
    invDet (Z + (c : ℂ) • vecMulVec u (star u)) =
      invDet Z * (1 + c * (star u ⬝ᵥ ((1 + Z)⁻¹ *ᵥ u)).re)⁻¹ := by
  have hP := posDef_one_add hZ
  have hd := Complex.lt_def.1 hP.det_pos
  have hq := Complex.nonneg_iff.1 (hP.inv.posSemidef.dotProduct_mulVec_nonneg u)
  have e : 1 + (Z + (c : ℂ) • vecMulVec u (star u)) =
      (1 + Z) + vecMulVec ((c : ℂ) • u) (star u) := by
    rw [← add_assoc, smul_vecMulVec]
  simp only [invDet]
  rw [e, det_add_vecMulVec (isUnit_det_one_add hZ), mulVec_smul, dotProduct_smul, smul_eq_mul]
  set d := (1 + Z).det
  set q := star u ⬝ᵥ ((1 + Z)⁻¹ *ᵥ u)
  have hdr : d = (d.re : ℂ) := Complex.ext rfl (by simp [← hd.2])
  have hqr : q = (q.re : ℂ) := Complex.ext rfl (by simp [← hq.2])
  rw [hdr, hqr]
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul,
    ← Complex.ofReal_inv, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re, mul_inv]

/-- `Re w*(I+Z)⁻¹w ≤ ‖w‖²` for `Z ⪰ 0`. -/
theorem re_dot_inv_le {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) (w : n → ℂ) :
    (star w ⬝ᵥ ((1 + Z)⁻¹ *ᵥ w)).re ≤ (star w ⬝ᵥ w).re := by
  have hU := isUnit_det_one_add hZ
  have hH : (1 + Z)ᴴ = 1 + Z := (posDef_one_add hZ).1
  have hZH : Zᴴ = Z := hZ.1
  set y := (1 + Z)⁻¹ *ᵥ w
  have hw : w = (1 + Z) *ᵥ y := by
    simp only [y]; rw [mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]
  have hs : star w = star y ᵥ* (1 + Z) := by rw [hw, star_mulVec, hH]
  have hZy : star (Z *ᵥ y) = star y ᵥ* Z := by rw [star_mulVec, hZH]
  have e1 : star w ⬝ᵥ y = star y ⬝ᵥ y + star y ⬝ᵥ (Z *ᵥ y) := by
    rw [hs, ← dotProduct_mulVec, add_mulVec, one_mulVec, dotProduct_add]
  have e3 : (1 + Z) *ᵥ ((1 + Z) *ᵥ y) = y + Z *ᵥ y + (Z *ᵥ y + Z *ᵥ (Z *ᵥ y)) := by
    simp only [add_mulVec, one_mulVec, mulVec_add]
  have e2 : star w ⬝ᵥ w =
      star y ⬝ᵥ y + 2 * (star y ⬝ᵥ (Z *ᵥ y)) + star (Z *ᵥ y) ⬝ᵥ (Z *ᵥ y) := by
    calc star w ⬝ᵥ w = (star y ᵥ* (1 + Z)) ⬝ᵥ ((1 + Z) *ᵥ y) := by rw [← hs, ← hw]
      _ = star y ⬝ᵥ ((1 + Z) *ᵥ ((1 + Z) *ᵥ y)) := (dotProduct_mulVec _ _ _).symm
      _ = _ := by
        rw [e3]
        simp only [dotProduct_add]
        rw [dotProduct_mulVec (star y) Z (Z *ᵥ y), ← hZy]
        ring
  rw [e1, e2]
  have h1 : 0 ≤ (star y ⬝ᵥ (Z *ᵥ y)).re := hZ.re_dotProduct_nonneg y
  have h2 : 0 ≤ (star (Z *ᵥ y) ⬝ᵥ (Z *ᵥ y)).re := by
    rw [dot_self_eq, Complex.ofReal_re]; exact Finset.sum_nonneg fun x _ => sq_nonneg _
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  linarith

omit [DecidableEq n] in
/-- `K = B*B` turns `Re u*Ku` into `‖Bu‖²`. -/
theorem re_dot_conj_mul (B : Matrix n n ℂ) (u : n → ℂ) :
    (star u ⬝ᵥ ((Bᴴ * B) *ᵥ u)).re = l2 (B *ᵥ u) ^ 2 := by
  rw [l2_sq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- **One replacement step**: `|F(Z + c uu*) - F(Z + c vv*)| ≤ √c ‖u - v‖₂` for `Z ⪰ 0`. -/
theorem abs_invDet_rankOne_sub_le {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (u v : n → ℂ) :
    |invDet (Z + (c : ℂ) • vecMulVec u (star u)) - invDet (Z + (c : ℂ) • vecMulVec v (star v))| ≤
      Real.sqrt c * l2 (u - v) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (posDef_one_add hZ).inv.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hB
  rw [invDet_add_rankOne hZ, invDet_add_rankOne hZ, ← mul_sub, abs_mul,
    abs_of_pos (invDet_mem hZ).1, hB, re_dot_conj_mul, re_dot_conj_mul]
  have hF := (invDet_mem hZ).2
  have ha : 0 ≤ c * l2 (B *ᵥ u) ^ 2 := by positivity
  have hb : 0 ≤ c * l2 (B *ᵥ v) ^ 2 := by positivity
  have hs : ∀ w : n → ℂ, Real.sqrt (c * l2 (B *ᵥ w) ^ 2) = Real.sqrt c * l2 (B *ᵥ w) := by
    intro w
    rw [Real.sqrt_mul hc, Real.sqrt_sq (l2_nonneg _)]
  have hBw : l2 (B *ᵥ (u - v)) ≤ l2 (u - v) := by
    apply l2_le_of_sq_le
    rw [← l2_sq, ← re_dot_conj_mul, ← hB]
    exact re_dot_inv_le hZ _
  calc invDet Z * |(1 + c * l2 (B *ᵥ u) ^ 2)⁻¹ - (1 + c * l2 (B *ᵥ v) ^ 2)⁻¹|
      ≤ 1 * |Real.sqrt (c * l2 (B *ᵥ u) ^ 2) - Real.sqrt (c * l2 (B *ᵥ v) ^ 2)| :=
        mul_le_mul hF (abs_inv_one_add_sub_le ha hb) (abs_nonneg _) zero_le_one
    _ = Real.sqrt c * |l2 (B *ᵥ u) - l2 (B *ᵥ v)| := by
        rw [one_mul, hs, hs, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg c)]
    _ ≤ Real.sqrt c * l2 (u - v) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg c)
        refine (abs_l2_sub_le _ _).trans ?_
        rw [← mulVec_sub]
        exact hBw

/-- The rank-one combination `Σ_{k∈s} c_k u_ku_k*`. -/
def rkSum {κ : Type*} (s : Finset κ) (c : κ → ℝ) (u : κ → n → ℂ) : Matrix n n ℂ :=
  ∑ k ∈ s, (c k : ℂ) • vecMulVec (u k) (star (u k))

omit [DecidableEq n] in
theorem rkSum_psd {κ : Type*} (s : Finset κ) {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (u : κ → n → ℂ) : (rkSum s c u).PosSemidef :=
  posSemidef_sum _ fun k _ =>
    (posSemidef_vecMulVec_self_star (u k)).smul (by exact_mod_cast hc k)

/-- **The hybrid bound**: replacing the vectors one at a time,
`|F(Z + Σ c_k u_ku_k*) - F(Z + Σ c_k v_kv_k*)| ≤ Σ_k √c_k ‖u_k - v_k‖₂`. -/
theorem abs_invDet_sum_sub_le {κ : Type*} [DecidableEq κ] (s : Finset κ) {c : κ → ℝ}
    (hc : ∀ k, 0 ≤ c k) (u v : κ → n → ℂ) :
    ∀ Z : Matrix n n ℂ, Z.PosSemidef →
      |invDet (Z + rkSum s c u) - invDet (Z + rkSum s c v)| ≤
        ∑ k ∈ s, Real.sqrt (c k) * l2 (u k - v k) := by
  induction s using Finset.induction_on with
  | empty => intro Z _; simp [rkSum]
  | insert k s hk ih =>
    intro Z hZ
    simp only [rkSum] at ih ⊢
    rw [Finset.sum_insert hk, Finset.sum_insert hk, Finset.sum_insert hk]
    set Pu := (c k : ℂ) • vecMulVec (u k) (star (u k))
    set Pv := (c k : ℂ) • vecMulVec (v k) (star (v k))
    set Su := ∑ x ∈ s, (c x : ℂ) • vecMulVec (u x) (star (u x))
    set Sv := ∑ x ∈ s, (c x : ℂ) • vecMulVec (v x) (star (v x))
    have hPu : Pu.PosSemidef := (posSemidef_vecMulVec_self_star (u k)).smul (by exact_mod_cast hc k)
    have hSv : Sv.PosSemidef := rkSum_psd s hc v
    have h1 := ih (Z + Pu) (hZ.add hPu)
    have h2 : |invDet (Z + Pu + Sv) - invDet (Z + Sv + Pv)| ≤
        Real.sqrt (c k) * l2 (u k - v k) := by
      have e2 : Z + Pu + Sv = Z + Sv + Pu := by abel
      rw [e2]; exact abs_invDet_rankOne_sub_le (hZ.add hSv) (hc k) (u k) (v k)
    have e1 : Z + (Pu + Su) = Z + Pu + Su := by abel
    have e3 : Z + (Pv + Sv) = Z + Sv + Pv := by abel
    rw [e1, e3]
    calc |invDet (Z + Pu + Su) - invDet (Z + Sv + Pv)|
        ≤ |invDet (Z + Pu + Su) - invDet (Z + Pu + Sv)| +
          |invDet (Z + Pu + Sv) - invDet (Z + Sv + Pv)| := abs_sub_le _ _ _
      _ ≤ (∑ x ∈ s, Real.sqrt (c x) * l2 (u x - v x)) +
          Real.sqrt (c k) * l2 (u k - v k) := add_le_add h1 h2
      _ = Real.sqrt (c k) * l2 (u k - v k) + ∑ x ∈ s, Real.sqrt (c x) * l2 (u x - v x) :=
          add_comm _ _

end BlockBand.SourceProcess.ClosingLeak
