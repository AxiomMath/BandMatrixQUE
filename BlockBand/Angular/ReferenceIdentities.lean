module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.Module

/-!
# The angular reference covariance and its identities

Setting: a Hermitian `K₀` on a finite index set of cardinality `N_aux`, `s ≠ 0` and
an upper-half-plane root `ζ = s m` of `m = N_aux⁻¹ Tr (K₀ - s m)⁻¹`. Put `a_* = 2 Re ζ`,
`c_* = |ζ|²` and `Γ = s (K₀² - a_* K₀ + c_* I)⁻¹ = s (K₀ - ζ̄)⁻¹ (K₀ - ζ)⁻¹`. Then
`Tr Γ = N_aux`, `Tr K₀Γ = N_aux a_*` and `K₀²Γ = s I + a_* K₀Γ - c_* Γ`. These are exact
identities; no bound on `s, ζ` is used. `angularGamma` agrees with the center formula of
`Layers.centerFormula` (`(s/N_aux) Tr J (K-ζ)⁻¹ᴴ (K-ζ)⁻¹`) (`Angular.Stein.AngularData.Γ_eq`: `Γ = s R(ζ)ᴴ R(ζ)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Reference

open Matrix
open scoped ComplexConjugate ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `K - z` is invertible for Hermitian `K` and non-real `z`. -/
theorem isUnit_det_sub_smul {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (K - z • (1 : Matrix ι ι ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hKx : K *ᵥ x = z • x := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hx
    exact hx
  have hq : star x ⬝ᵥ (K *ᵥ x) = z * (star x ⬝ᵥ x) := by
    rw [hKx, dotProduct_smul, smul_eq_mul]
  have hreal : (star x ⬝ᵥ (K *ᵥ x)).im = 0 := by
    have h := hK.star_dotProduct_mulVec_comm x x
    exact Complex.conj_eq_iff_im.1 h
  have hp : star x ⬝ᵥ x ≠ 0 := fun h => hx0 (dotProduct_star_self_eq_zero.1 h)
  have hpim : (star x ⬝ᵥ x).im = 0 := by
    have h := (isHermitian_one (n := ι) (α := ℂ)).star_dotProduct_mulVec_comm x x
    rw [one_mulVec] at h
    exact Complex.conj_eq_iff_im.1 h
  have hpre : (star x ⬝ᵥ x).re ≠ 0 := by
    intro h; exact hp (Complex.ext h hpim)
  have h2 := congrArg Complex.im hq
  rw [hreal, Complex.mul_im, hpim, mul_zero, zero_add] at h2
  rcases mul_eq_zero.1 h2.symm with h | h
  · exact hz h
  · exact hpre h

variable (K : Matrix ι ι ℂ) (s : ℝ) (ζ : ℂ)

/-- `(K₀ - z)⁻¹`. -/
def resolvent (z : ℂ) : Matrix ι ι ℂ := (K - z • (1 : Matrix ι ι ℂ))⁻¹

/-- The reference covariance `Γ = s (K₀ - ζ̄)⁻¹ (K₀ - ζ)⁻¹`. -/
def angularGamma : Matrix ι ι ℂ := (s : ℂ) • (resolvent K (conj ζ) * resolvent K ζ)

/-- `a_* = 2 Re ζ`. -/
def aStar : ℝ := 2 * ζ.re

/-- `c_* = |ζ|²`. -/
def cStar : ℝ := Complex.normSq ζ

/-- `ζ` solves the scalar equation `ζ = s N_aux⁻¹ Tr (K₀ - ζ)⁻¹` in the upper half-plane. -/
def IsAngularRoot : Prop :=
  0 < ζ.im ∧ ζ = (s : ℂ) * (Fintype.card ι : ℂ)⁻¹ * (resolvent K ζ).trace

variable {K s ζ}

theorem resolvent_mul (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (K - z • (1 : Matrix ι ι ℂ)) * resolvent K z = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_sub_smul hK hz)

theorem mul_resolvent (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    resolvent K z * (K - z • (1 : Matrix ι ι ℂ)) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_sub_smul hK hz)

/-- `K₀ R(z) = I + z R(z)`. -/
theorem K_mul_resolvent (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    K * resolvent K z = 1 + z • resolvent K z := by
  have h := resolvent_mul hK hz
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  rw [← h]; abel

/-- `R(z) K₀ = I + z R(z)`. -/
theorem resolvent_mul_K (hK : K.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    resolvent K z * K = 1 + z • resolvent K z := by
  have h := mul_resolvent hK hz
  rw [mul_sub, mul_smul_comm, mul_one] at h
  rw [← h]; abel

/-- `R(z̄) = R(z)ᴴ` for Hermitian `K₀`. -/
theorem resolvent_conj (hK : K.IsHermitian) (z : ℂ) :
    resolvent K (conj z) = (resolvent K z)ᴴ := by
  unfold resolvent
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, hK.eq, conjTranspose_smul,
    conjTranspose_one]
  rfl

/-- Resolvent identity `R(z) - R(w) = (z - w) R(z) R(w)`. -/
theorem resolvent_sub (hK : K.IsHermitian) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent K z - resolvent K w = (z - w) • (resolvent K z * resolvent K w) := by
  have e1 := mul_resolvent hK hz
  have e2 := resolvent_mul hK hw
  calc resolvent K z - resolvent K w
      = resolvent K z * ((K - w • 1) * resolvent K w) -
          (resolvent K z * (K - z • 1)) * resolvent K w := by rw [e1, e2, mul_one, one_mul]
    _ = (z - w) • (resolvent K z * resolvent K w) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_sub, ← Matrix.sub_mul]
          have : (K - w • (1 : Matrix ι ι ℂ)) - (K - z • 1) = (z - w) • 1 := by
            rw [sub_smul]; abel
          rw [this, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]

/-- The two resolvents commute. -/
theorem resolvent_commute (hK : K.IsHermitian) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    resolvent K z * resolvent K w = resolvent K w * resolvent K z := by
  by_cases hzw : z = w
  · subst hzw; rfl
  have h1 := resolvent_sub hK hz hw
  have h2 := resolvent_sub hK hw hz
  have hne : (z - w) ≠ 0 := sub_ne_zero.2 hzw
  have : (z - w) • (resolvent K z * resolvent K w) = (z - w) • (resolvent K w * resolvent K z) := by
    rw [← h1, show (z - w) = -(w - z) by ring, neg_smul, ← h2]; abel
  exact smul_right_injective _ hne this

theorem im_conj_ne {z : ℂ} (hz : z.im ≠ 0) : (conj z).im ≠ 0 := by
  simpa using hz

theorem trace_resolvent_conj (hK : K.IsHermitian) (z : ℂ) :
    (resolvent K (conj z)).trace = conj (resolvent K z).trace := by
  rw [resolvent_conj hK, trace_conjTranspose]; rfl

/-- On an angular root `N_aux ≠ 0` and `Tr R(ζ) = N_aux ζ / s`. -/
theorem trace_resolvent_root (hs : s ≠ 0) (hζ : IsAngularRoot K s ζ) :
    (Fintype.card ι : ℂ) ≠ 0 ∧ (resolvent K ζ).trace = (Fintype.card ι : ℂ) * ζ / s := by
  obtain ⟨hy, hroot⟩ := hζ
  set t := (resolvent K ζ).trace with ht
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by
    intro h0
    rw [h0, _root_.inv_zero, mul_zero, zero_mul] at hroot
    rw [hroot] at hy; simp at hy
  refine ⟨hN, ?_⟩
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [eq_div_iff hs', hroot]
  field_simp

theorem conj_sub_ne {z : ℂ} (hz : z.im ≠ 0) : z - conj z ≠ 0 := by
  intro h
  apply hz
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `(ζ - ζ̄) Γ = s (R(ζ) - R(ζ̄))`. -/
theorem smul_angularGamma (hK : K.IsHermitian) (hz : ζ.im ≠ 0) :
    (ζ - conj ζ) • angularGamma K s ζ = (s : ℂ) • (resolvent K ζ - resolvent K (conj ζ)) := by
  rw [resolvent_sub hK hz (im_conj_ne hz), angularGamma,
    resolvent_commute hK (im_conj_ne hz) hz, smul_comm]

/-- `Tr Γ = N_aux` (first reference identity). -/
theorem trace_angularGamma (hK : K.IsHermitian) (hs : s ≠ 0) (hζ : IsAngularRoot K s ζ) :
    (angularGamma K s ζ).trace = Fintype.card ι := by
  have hz : ζ.im ≠ 0 := hζ.1.ne'
  obtain ⟨hN, htr⟩ := trace_resolvent_root hs hζ
  have h := congrArg Matrix.trace (smul_angularGamma (s := s) hK hz)
  rw [trace_smul, trace_smul, trace_sub, trace_resolvent_conj hK, htr, smul_eq_mul,
    smul_eq_mul] at h
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hc : conj ((Fintype.card ι : ℂ) * ζ / s) = (Fintype.card ι : ℂ) * conj ζ / s := by
    simp [map_div₀, Complex.conj_ofReal]
  rw [hc] at h
  have hne := conj_sub_ne hz
  have : (ζ - conj ζ) * (angularGamma K s ζ).trace = (ζ - conj ζ) * (Fintype.card ι : ℂ) := by
    rw [h]; field_simp
  exact mul_left_cancel₀ hne this

/-- `Tr K₀Γ = N_aux a_*` (second reference identity). -/
theorem trace_K_mul_angularGamma (hK : K.IsHermitian) (hs : s ≠ 0) (hζ : IsAngularRoot K s ζ) :
    (K * angularGamma K s ζ).trace = (Fintype.card ι : ℂ) * (aStar ζ : ℂ) := by
  have hz : ζ.im ≠ 0 := hζ.1.ne'
  obtain ⟨hN, htr⟩ := trace_resolvent_root hs hζ
  have hΓ := trace_angularGamma hK hs hζ
  have hKΓ : K * angularGamma K s ζ =
      (s : ℂ) • (resolvent K ζ + conj ζ • (resolvent K (conj ζ) * resolvent K ζ)) := by
    rw [angularGamma, Matrix.mul_smul, ← Matrix.mul_assoc, K_mul_resolvent hK (im_conj_ne hz),
      Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hΓ' : (resolvent K (conj ζ) * resolvent K ζ).trace = (Fintype.card ι : ℂ) / s := by
    have := hΓ
    rw [angularGamma, trace_smul, smul_eq_mul] at this
    field_simp
    rw [mul_comm]; exact this
  rw [hKΓ, trace_smul, trace_add, trace_smul, hΓ', htr, smul_eq_mul, smul_eq_mul, aStar]
  have : (ζ : ℂ) + conj ζ = ((2 * ζ.re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  field_simp
  rw [← this]

/-- `(K₀² - a_* K₀ + c_* I) Γ = s I`, hence `K₀²Γ = s I + a_* K₀Γ - c_* Γ`
(third reference identity). -/
theorem K_sq_mul_angularGamma (hK : K.IsHermitian) (hz : ζ.im ≠ 0) :
    K * K * angularGamma K s ζ =
      (s : ℂ) • 1 + (aStar ζ : ℂ) • (K * angularGamma K s ζ) -
        (cStar ζ : ℂ) • angularGamma K s ζ := by
  set P := resolvent K (conj ζ) * resolvent K ζ with hP
  have e1 := resolvent_mul hK hz
  have e2 := resolvent_mul hK (im_conj_ne hz)
  have hprod : (K - ζ • (1 : Matrix ι ι ℂ)) * (K - conj ζ • 1) * P = 1 := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc (K - conj ζ • 1), e2, Matrix.one_mul, e1]
  have ha : (aStar ζ : ℂ) = ζ + conj ζ := by
    rw [aStar, Complex.add_conj]
  have hc : (cStar ζ : ℂ) = ζ * conj ζ := by
    rw [cStar, Complex.mul_conj]
  have hexp : (K - ζ • (1 : Matrix ι ι ℂ)) * (K - conj ζ • 1) =
      K * K - (aStar ζ : ℂ) • K + (cStar ζ : ℂ) • 1 := by
    rw [ha, hc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rw [hexp, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul] at hprod
  have h2 : K * K * P = 1 + (aStar ζ : ℂ) • (K * P) - (cStar ζ : ℂ) • P := by
    rw [← hprod]; abel
  change K * K * ((s : ℂ) • P) = (s : ℂ) • 1 + (aStar ζ : ℂ) • (K * ((s : ℂ) • P)) -
    (cStar ζ : ℂ) • ((s : ℂ) • P)
  rw [Matrix.mul_smul, Matrix.mul_smul, h2]
  module

end BlockBand.Angular.Reference
