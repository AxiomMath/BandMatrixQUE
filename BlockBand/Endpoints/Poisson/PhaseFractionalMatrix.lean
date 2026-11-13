module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic

/-!
# Deterministic matrix identities for the projected fractional inverse

* `quadNorm x = Re (x* x)`; `IsContraction X`: `‖X x‖ ≤ ‖x‖` for all `x`.
* `rankOneTwist v ω = I + (ω - 1) v v*`: for a unit vector `v` and `ω = e^{iθ}` this is
  `exp(iθ v v*)`, the rank-one twist; it is unitary when `|ω| = 1`.
* `two_re_quad_sub_eq` (the Cayley real part): with
  `q = v*(I-X)⁻¹v`, `y = (I-X)⁻¹v`: `2 Re q - ‖v‖² = ‖y‖² - ‖Xy‖²`.
* `quad_twist_eq` (the twist moves `q` on a circle): `q_ω = q / (1 - (ω-1)(q-1))`.
* `det_twist_eq` (the one-phase ratio): the matrix determinant lemma
  `det(I - X(I + (ω-1)vv*)) = det(I - X) (1 - (ω-1)(q-1))`.
* `two_re_quad_fromBlocks_le` (the full-kernel upper bound): for
  `X = [[a, c], [0, 0]]` a contraction, `2 Re q - 1 ≤ 2 Re v₁*𝒫(a)v₁ + 2‖v₂‖²`
  (`𝒫(a) = (I-a)⁻¹ + (I-a*)⁻¹ - I`); the Schur-complement step of the paper is replaced by the
  equivalent reflection `v ↦ (v₁, -v₂)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.PhaseFractional

open Matrix
open scoped ComplexOrder ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `‖x‖² = Re (x* x)`. -/
def quadNorm {κ : Type*} [Fintype κ] (x : κ → ℂ) : ℝ := (star x ⬝ᵥ x).re

/-- `X` is a contraction: `‖X x‖ ≤ ‖x‖` for every vector `x`. -/
def IsContraction {κ : Type*} [Fintype κ] (X : Matrix κ κ ℂ) : Prop :=
  ∀ x, quadNorm (X *ᵥ x) ≤ quadNorm x

/-- The rank-one twist `I + (ω - 1) v v*` (`= exp(iθ v v*)` for unit `v`, `ω = e^{iθ}`). -/
def rankOneTwist (v : ι → ℂ) (ω : ℂ) : Matrix ι ι ℂ :=
  1 + (ω - 1) • vecMulVec v (star v)

/-- The quadratic form `q = v*(I - X)⁻¹v`. -/
def resolventQuad (X : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  star v ⬝ᵥ ((1 - X)⁻¹ *ᵥ v)

theorem star_dotProduct_self_eq {κ : Type*} [Fintype κ] (x : κ → ℂ) :
    star x ⬝ᵥ x = (quadNorm x : ℂ) := by
  have h := dotProduct_star_self_nonneg x
  rw [quadNorm]
  exact (Complex.ext rfl (by
    have := (Complex.nonneg_iff.mp h).2
    simpa using this.symm))

theorem quadNorm_nonneg {κ : Type*} [Fintype κ] (x : κ → ℂ) : 0 ≤ quadNorm x :=
  (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg x)).1

theorem quadNorm_pos {κ : Type*} [Fintype κ] {x : κ → ℂ} (hx : x ≠ 0) : 0 < quadNorm x := by
  rcases (quadNorm_nonneg x).eq_or_lt with h | h
  · exfalso
    apply hx
    rw [← dotProduct_star_self_eq_zero, star_dotProduct_self_eq, ← h]
    simp
  · exact h

theorem star_mulVec_dotProduct_mulVec {κ : Type*} [Fintype κ] (A : Matrix κ κ ℂ)
    (x y : κ → ℂ) : star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem conj_dotProduct {κ : Type*} [Fintype κ] (x y : κ → ℂ) :
    conj (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  rw [show conj (star x ⬝ᵥ y) = star (star x ⬝ᵥ y) from rfl, star_dotProduct, star_star]

theorem vecMulVec_star_mulVec {κ : Type*} [Fintype κ] (v x : κ → ℂ) :
    vecMulVec v (star v) *ᵥ x = (star v ⬝ᵥ x) • v := by
  ext i
  simp [vecMulVec_mulVec, mul_comm]

theorem rankOneTwist_mulVec (v : ι → ℂ) (ω : ℂ) (x : ι → ℂ) :
    rankOneTwist v ω *ᵥ x = x + ((ω - 1) * (star v ⬝ᵥ x)) • v := by
  rw [rankOneTwist, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_star_mulVec, smul_smul]

/-!
## The Cayley real part
-/

/-- With `y = (I - X)⁻¹ v`: `q + q̄ - v*v = y*y - (Xy)*(Xy)`. -/
theorem quad_add_conj_eq (X : Matrix ι ι ℂ) (hX : IsUnit (1 - X).det) (v : ι → ℂ) :
    resolventQuad X v + conj (resolventQuad X v) - star v ⬝ᵥ v =
      star ((1 - X)⁻¹ *ᵥ v) ⬝ᵥ ((1 - X)⁻¹ *ᵥ v) -
        star (X *ᵥ ((1 - X)⁻¹ *ᵥ v)) ⬝ᵥ (X *ᵥ ((1 - X)⁻¹ *ᵥ v)) := by
  have hv : v = (1 - X)⁻¹ *ᵥ v - X *ᵥ ((1 - X)⁻¹ *ᵥ v) := by
    conv_lhs => rw [← one_mulVec v, ← mul_nonsing_inv _ hX, ← mulVec_mulVec]
    rw [sub_mulVec, one_mulVec]
  rw [resolventQuad, conj_dotProduct]
  generalize (1 - X)⁻¹ *ᵥ v = y at hv ⊢
  subst hv
  simp only [star_sub, sub_dotProduct, dotProduct_sub]
  ring

/-- Real form of `quad_add_conj_eq`: `2 Re q - ‖v‖² = ‖y‖² - ‖X y‖²`. -/
theorem two_re_quad_sub_eq (X : Matrix ι ι ℂ) (hX : IsUnit (1 - X).det) (v : ι → ℂ) :
    2 * (resolventQuad X v).re - quadNorm v =
      quadNorm ((1 - X)⁻¹ *ᵥ v) - quadNorm (X *ᵥ ((1 - X)⁻¹ *ᵥ v)) := by
  have h := congrArg Complex.re (quad_add_conj_eq X hX v)
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re] at h
  rw [quadNorm, quadNorm, quadNorm]
  linarith

theorem two_re_quad_sub_nonneg {X : Matrix ι ι ℂ} (hX : IsUnit (1 - X).det)
    (hc : IsContraction X) (v : ι → ℂ) : 0 ≤ 2 * (resolventQuad X v).re - quadNorm v := by
  rw [two_re_quad_sub_eq X hX v]
  linarith [hc ((1 - X)⁻¹ *ᵥ v)]

/-- `(I - X) (I - X)⁻¹ v = v`, i.e. `v = y - X y`. -/
theorem eq_sub_mulVec_inv {X : Matrix ι ι ℂ} (hX : IsUnit (1 - X).det) (v : ι → ℂ) :
    v = (1 - X)⁻¹ *ᵥ v - X *ᵥ ((1 - X)⁻¹ *ᵥ v) := by
  conv_lhs => rw [← one_mulVec v, ← mul_nonsing_inv _ hX, ← mulVec_mulVec]
  rw [sub_mulVec, one_mulVec]

/-- Strict contractions: `‖Xx‖ < ‖x‖` for `x ≠ 0`. -/
def IsStrictContraction {κ : Type*} [Fintype κ] (X : Matrix κ κ ℂ) : Prop :=
  ∀ x, x ≠ 0 → quadNorm (X *ᵥ x) < quadNorm x

theorem IsStrictContraction.isContraction {κ : Type*} [Fintype κ] {X : Matrix κ κ ℂ}
    (h : IsStrictContraction X) : IsContraction X := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · exact (h x hx).le

theorem IsStrictContraction.isUnit_det {κ : Type*} [Fintype κ] [DecidableEq κ]
    {X : Matrix κ κ ℂ} (h : IsStrictContraction X) : IsUnit (1 - X).det := by
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro a b hab
  by_contra hne
  have hx : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h0 : (1 - X) *ᵥ (a - b) = 0 := by
    rw [mulVec_sub]
    exact sub_eq_zero.mpr hab
  have h1 : X *ᵥ (a - b) = a - b := by
    rw [sub_mulVec, one_mulVec] at h0
    exact (sub_eq_zero.mp h0).symm
  have := h (a - b) hx
  rw [h1] at this
  exact lt_irrefl _ this

theorem quadNorm_smul {κ : Type*} [Fintype κ] (c : ℂ) (x : κ → ℂ) :
    quadNorm (c • x) = Complex.normSq c * quadNorm x := by
  have h : star (c • x) ⬝ᵥ (c • x) = (Complex.normSq c : ℂ) * (star x ⬝ᵥ x) := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul,
      Complex.normSq_eq_conj_mul_self]
    rfl
  rw [quadNorm, h, star_dotProduct_self_eq, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem IsContraction.smul_strict {κ : Type*} [Fintype κ] {Y : Matrix κ κ ℂ}
    (hY : IsContraction Y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    IsStrictContraction ((t : ℂ) • Y) := by
  intro x hx
  rw [smul_mulVec, quadNorm_smul, Complex.normSq_ofReal]
  have h1 := hY x
  have h2 := quadNorm_pos hx
  have h3 : t * t < 1 := by nlinarith
  have h4 := quadNorm_nonneg (Y *ᵥ x)
  nlinarith

theorem IsContraction.mul {κ : Type*} [Fintype κ] {U V : Matrix κ κ ℂ} (hU : IsContraction U)
    (hV : IsContraction V) : IsContraction (U * V) := by
  intro x
  rw [← mulVec_mulVec]
  exact (hU _).trans (hV x)

theorem quadNorm_mulVec_of_unitary {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : Matrix κ κ ℂ} (hV : Vᴴ * V = 1) (x : κ → ℂ) : quadNorm (V *ᵥ x) = quadNorm x := by
  rw [quadNorm, star_mulVec_dotProduct_mulVec, hV, one_mulVec, quadNorm]

theorem isContraction_of_unitary {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : Matrix κ κ ℂ} (hV : Vᴴ * V = 1) : IsContraction V := fun x =>
  (quadNorm_mulVec_of_unitary hV x).le

omit [Fintype ι] in
theorem conjTranspose_rankOneTwist (v : ι → ℂ) (ω : ℂ) :
    (rankOneTwist v ω)ᴴ = rankOneTwist v (conj ω) := by
  rw [rankOneTwist, rankOneTwist, conjTranspose_add, conjTranspose_one, conjTranspose_smul,
    conjTranspose_vecMulVec, star_star]
  congr 1
  simp

omit [DecidableEq ι] in
theorem vecMulVec_star_mul_self {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1) :
    vecMulVec v (star v) * vecMulVec v (star v) = vecMulVec v (star v) := by
  rw [vecMulVec_mul_vecMulVec, hv, one_smul]

theorem rankOneTwist_mul (v : ι → ℂ) (hv : star v ⬝ᵥ v = 1) (ω ω' : ℂ) :
    rankOneTwist v ω * rankOneTwist v ω' = rankOneTwist v (ω * ω') := by
  rw [rankOneTwist, rankOneTwist, rankOneTwist, add_mul, mul_add, mul_add, one_mul, mul_one,
    one_mul, smul_mul_smul_comm, vecMulVec_star_mul_self hv]
  rw [show (ω * ω' - 1) = (ω - 1) + (ω' - 1) + (ω - 1) * (ω' - 1) by ring, add_smul, add_smul]
  abel

omit [Fintype ι] in
theorem rankOneTwist_one (v : ι → ℂ) : rankOneTwist v 1 = 1 := by
  simp [rankOneTwist]

theorem rankOneTwist_unitary {v : ι → ℂ} (hv : star v ⬝ᵥ v = 1) {ω : ℂ} (hω : ‖ω‖ = 1) :
    (rankOneTwist v ω)ᴴ * rankOneTwist v ω = 1 := by
  rw [conjTranspose_rankOneTwist, rankOneTwist_mul v hv]
  have : conj ω * ω = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hω]
    simp
  rw [this, rankOneTwist_one]

/-!
## The rank-one twist moves `q` on a circle
-/

/-- **Sherman–Morrison for the twist**: for `‖v‖ = 1`, `I - X` and
`I - X(I + (ω-1)vv*)` invertible, `D = 1 - (ω-1)(q-1) ≠ 0`:
`v*(I - X(I + (ω-1)vv*))⁻¹ v = q / D`. -/
theorem quad_twist_eq {X : Matrix ι ι ℂ} (hX : IsUnit (1 - X).det) {v : ι → ℂ}
    (hv : star v ⬝ᵥ v = 1) {ω : ℂ} (hX' : IsUnit (1 - X * rankOneTwist v ω).det)
    (hD : 1 - (ω - 1) * (resolventQuad X v - 1) ≠ 0) :
    resolventQuad (X * rankOneTwist v ω) v =
      resolventQuad X v / (1 - (ω - 1) * (resolventQuad X v - 1)) := by
  set q := resolventQuad X v with hq
  set D := 1 - (ω - 1) * (q - 1) with hDdef
  set y := (1 - X)⁻¹ *ᵥ v with hy
  set c : ℂ := (ω - 1) * q / D with hc
  set x := y + c • (y - v) with hx
  have hvy := eq_sub_mulVec_inv hX v
  rw [← hy] at hvy
  have hqy : star v ⬝ᵥ y = q := rfl
  have hvx : star v ⬝ᵥ x = q + c * (q - 1) := by
    rw [hx, dotProduct_add, dotProduct_smul, dotProduct_sub, hqy, hv, smul_eq_mul]
  have hcs : (ω - 1) * (q + c * (q - 1)) = c := by
    rw [hc]
    field_simp
    ring
  have key : (1 - X * rankOneTwist v ω) *ᵥ x = v := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, rankOneTwist_mulVec, hvx, hcs]
    rw [hx, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, mulVec_sub]
    set a := X *ᵥ y
    set w := X *ᵥ v
    rw [hvy]
    module
  have hinv : (1 - X * rankOneTwist v ω)⁻¹ *ᵥ v = x := by
    calc (1 - X * rankOneTwist v ω)⁻¹ *ᵥ v
        = (1 - X * rankOneTwist v ω)⁻¹ *ᵥ ((1 - X * rankOneTwist v ω) *ᵥ x) := by rw [key]
      _ = x := by rw [mulVec_mulVec, nonsing_inv_mul _ hX', one_mulVec]
  rw [resolventQuad, hinv, hvx, hc]
  field_simp
  ring

/-!
## The matrix determinant lemma (the one-phase ratio)
-/

theorem det_one_add_vecMulVec (a b : ι → ℂ) : (1 + vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

/-- **The one-phase ratio**: for `‖v‖ = 1` and `I - X` invertible,
`det(I - X(I + (ω-1)vv*)) = det(I - X) (1 - (ω-1)(q-1))`. -/
theorem det_twist_eq {X : Matrix ι ι ℂ} (hX : IsUnit (1 - X).det) {v : ι → ℂ}
    (hv : star v ⬝ᵥ v = 1) (ω : ℂ) :
    (1 - X * rankOneTwist v ω).det =
      (1 - X).det * (1 - (ω - 1) * (resolventQuad X v - 1)) := by
  set a : ι → ℂ := -(ω - 1) • ((1 - X)⁻¹ *ᵥ (X *ᵥ v)) with ha
  have hfac : 1 - X * rankOneTwist v ω = (1 - X) * (1 + vecMulVec a (star v)) := by
    rw [mul_add, mul_one, mul_vecMulVec, ha, mulVec_smul, mulVec_mulVec, mul_nonsing_inv _ hX,
      one_mulVec, rankOneTwist, mul_add, mul_one, mul_smul_comm, mul_vecMulVec]
    rw [show vecMulVec (-(ω - 1) • (X *ᵥ v)) (star v) = -(ω - 1) • vecMulVec (X *ᵥ v) (star v) by
      ext i j; simp [vecMulVec, mul_assoc]]
    rw [neg_smul]
    abel
  have hdot : star v ⬝ᵥ a = -(ω - 1) * (resolventQuad X v - 1) := by
    have h1 : (1 - X)⁻¹ *ᵥ (X *ᵥ v) = (1 - X)⁻¹ *ᵥ v - v := by
      have : X *ᵥ v = v - (1 - X) *ᵥ v := by rw [sub_mulVec, one_mulVec]; abel
      rw [this, mulVec_sub, mulVec_mulVec, nonsing_inv_mul _ hX, one_mulVec]
    rw [ha, dotProduct_smul, h1, dotProduct_sub, hv, smul_eq_mul, resolventQuad]
  rw [hfac, det_mul, det_one_add_vecMulVec, hdot]
  ring

/-!
## Block structure: determinant compression and the full-kernel upper bound
-/

section Blocks

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The matrix kernel `𝒫(a) = (I - a)⁻¹ + (I - a*)⁻¹ - I` (the same matrix as `Critical.poissonKernel`). -/
def portKernel (a : Matrix α α ℂ) : Matrix α α ℂ := (1 - a)⁻¹ + (1 - aᴴ)⁻¹ - 1

omit [Fintype α] [Fintype β] in
theorem one_sub_fromBlocks (a : Matrix α α ℂ) (c : Matrix α β ℂ) :
    (1 : Matrix (α ⊕ β) (α ⊕ β) ℂ) - fromBlocks a c 0 0 = fromBlocks (1 - a) (-c) 0 1 := by
  ext (i | i) (j | j) <;> simp [one_apply]

theorem inv_one_sub_fromBlocks {a : Matrix α α ℂ} (ha : IsUnit (1 - a).det) (c : Matrix α β ℂ) :
    ((1 : Matrix (α ⊕ β) (α ⊕ β) ℂ) - fromBlocks a c 0 0)⁻¹ =
      fromBlocks (1 - a)⁻¹ ((1 - a)⁻¹ * c) 0 1 := by
  apply inv_eq_right_inv
  rw [one_sub_fromBlocks, fromBlocks_multiply, mul_nonsing_inv _ ha, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ha]
  simp [fromBlocks_one]

theorem isUnit_det_one_sub_fromBlocks {a : Matrix α α ℂ} (ha : IsUnit (1 - a).det)
    (c : Matrix α β ℂ) :
    IsUnit ((1 : Matrix (α ⊕ β) (α ⊕ β) ℂ) - fromBlocks a c 0 0).det := by
  apply isUnit_det_of_right_inverse (B := fromBlocks (1 - a)⁻¹ ((1 - a)⁻¹ * c) 0 1)
  rw [← inv_one_sub_fromBlocks ha c]
  exact mul_nonsing_inv _ (by
    rw [one_sub_fromBlocks, det_fromBlocks_zero₂₁, det_one, mul_one]; exact ha)

omit [DecidableEq α] [DecidableEq β] in
theorem star_dotProduct_sum {x y : α ⊕ β → ℂ} :
    star x ⬝ᵥ y = star (x ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl) + star (x ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq α] [DecidableEq β] in
theorem quadNorm_sum (x : α ⊕ β → ℂ) :
    quadNorm x = quadNorm (x ∘ Sum.inl) + quadNorm (x ∘ Sum.inr) := by
  rw [quadNorm, star_dotProduct_sum, Complex.add_re]
  rfl

theorem resolventQuad_fromBlocks {a : Matrix α α ℂ} (ha : IsUnit (1 - a).det)
    (c : Matrix α β ℂ) (v : α ⊕ β → ℂ) :
    resolventQuad (fromBlocks a c 0 0) v =
      star (v ∘ Sum.inl) ⬝ᵥ ((1 - a)⁻¹ *ᵥ (v ∘ Sum.inl)) +
        star (v ∘ Sum.inl) ⬝ᵥ (((1 - a)⁻¹ * c) *ᵥ (v ∘ Sum.inr)) +
          star (v ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr) := by
  rw [resolventQuad, inv_one_sub_fromBlocks ha, fromBlocks_mulVec, star_dotProduct_sum]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, one_mulVec, zero_add]
  rw [dotProduct_add]

theorem quad_portKernel (a : Matrix α α ℂ) (u : α → ℂ) :
    star u ⬝ᵥ (portKernel a *ᵥ u) =
      star u ⬝ᵥ ((1 - a)⁻¹ *ᵥ u) + conj (star u ⬝ᵥ ((1 - a)⁻¹ *ᵥ u)) - star u ⬝ᵥ u := by
  rw [portKernel, sub_mulVec, add_mulVec, one_mulVec, dotProduct_sub, dotProduct_add,
    conj_dotProduct, star_mulVec, ← dotProduct_mulVec, conjTranspose_nonsing_inv,
    conjTranspose_sub, conjTranspose_one]

/-- **Full-kernel upper bound**, quadratic-form version: for the contraction
`X = [[a, c], [0, 0]]` with `I - a` invertible, `2 Re q - ‖v‖² ≤ 2 Re v₁*𝒫(a)v₁ + 2‖v₂‖²`. -/
theorem two_re_quad_fromBlocks_le {a : Matrix α α ℂ} (ha : IsUnit (1 - a).det)
    {c : Matrix α β ℂ} (hc : IsContraction (fromBlocks a c 0 0)) (v : α ⊕ β → ℂ) :
    2 * (resolventQuad (fromBlocks a c 0 0) v).re - quadNorm v ≤
      2 * (star (v ∘ Sum.inl) ⬝ᵥ (portKernel a *ᵥ (v ∘ Sum.inl))).re +
        2 * quadNorm (v ∘ Sum.inr) := by
  set J : α ⊕ β → ℂ := Sum.elim (v ∘ Sum.inl) (-(v ∘ Sum.inr)) with hJ
  have hX := isUnit_det_one_sub_fromBlocks ha c
  have hnn := two_re_quad_sub_nonneg hX hc J
  have hJl : J ∘ Sum.inl = v ∘ Sum.inl := by rw [hJ, Sum.elim_comp_inl]
  have hJr : J ∘ Sum.inr = -(v ∘ Sum.inr) := by rw [hJ, Sum.elim_comp_inr]
  rw [resolventQuad_fromBlocks ha, hJl, hJr] at hnn
  rw [resolventQuad_fromBlocks ha, quad_portKernel]
  rw [quadNorm_sum J, hJl, hJr] at hnn
  rw [quadNorm_sum v]
  have hneg : quadNorm (-(v ∘ Sum.inr)) = quadNorm (v ∘ Sum.inr) := by
    rw [show -(v ∘ Sum.inr) = (-1 : ℂ) • (v ∘ Sum.inr) by simp, quadNorm_smul]
    simp
  rw [hneg] at hnn
  simp only [mulVec_neg, dotProduct_neg, star_neg, neg_dotProduct, neg_neg] at hnn
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.conj_re] at hnn ⊢
  rw [star_dotProduct_self_eq (v ∘ Sum.inl)]
  rw [star_dotProduct_self_eq (v ∘ Sum.inr)] at hnn ⊢
  simp only [Complex.ofReal_re] at hnn ⊢
  linarith

omit [DecidableEq α] [DecidableEq β] in
theorem isContraction_fromBlocks_zero {U : Matrix α α ℂ} (hU : IsContraction U) :
    IsContraction (fromBlocks U 0 0 (0 : Matrix β β ℂ)) := by
  intro x
  rw [fromBlocks_mulVec, quadNorm_sum, quadNorm_sum x]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero]
  have h0 : quadNorm (0 : β → ℂ) = 0 := by simp [quadNorm]
  rw [h0]
  linarith [hU (x ∘ Sum.inl), quadNorm_nonneg (x ∘ Sum.inr)]

omit [DecidableEq α] [DecidableEq β] in
theorem toBlocks₁₁_mulVec (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) (x : α → ℂ) :
    V.toBlocks₁₁ *ᵥ x = (V *ᵥ Sum.elim x 0) ∘ Sum.inl := by
  ext i
  simp [mulVec, dotProduct, toBlocks₁₁, Fintype.sum_sum_type]

omit [DecidableEq α] [DecidableEq β] in
theorem isContraction_toBlocks₁₁ {V : Matrix (α ⊕ β) (α ⊕ β) ℂ} (hV : IsContraction V) :
    IsContraction V.toBlocks₁₁ := by
  intro x
  rw [toBlocks₁₁_mulVec]
  have h1 := quadNorm_sum (V *ᵥ Sum.elim x 0)
  have h2 := hV (Sum.elim x 0)
  have h3 := quadNorm_sum (Sum.elim x (0 : β → ℂ))
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h3
  have h0 : quadNorm (0 : β → ℂ) = 0 := by simp [quadNorm]
  linarith [quadNorm_nonneg ((V *ᵥ Sum.elim x 0) ∘ Sum.inr)]

end Blocks

end BlockBand.Endpoints.PhaseFractional
