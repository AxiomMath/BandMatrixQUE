module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.NoncommRing
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Matrix identities for the weak-solution representation

For `σ ∈ ℝ^{d×m}` and a Moore–Penrose pseudoinverse `P = σ⁺ ∈ ℝ^{m×d}`
(`IsMoorePenrose σ P`: the four Penrose identities), with `E = Pσ` (orthogonal projection onto
`ran σᵀ`):

* `bracket_identity`: `P (σσᵀ) Pᵀ + (I - Pσ)(I - Pσ)ᵀ = I_m` — the bracket density of
  `W = ∫ σ⁺(Y) dN + ∫ (I - σ⁺σ)(Y) dB'` (with `d⟨N⟩ = σσᵀ dt`, `d⟨B'⟩ = I dt`, `⟨N, B'⟩ = 0`)
  is the identity, so `W` is a Brownian motion by Lévy;
* `sigma_mul_compl`: `σ (I - Pσ) = 0` — the `B'` part does not enter `σ dW`;
* `residual_bracket`: `(I - σP)(σσᵀ)(I - σP)ᵀ = 0` — the residual `N - ∫ σσ⁺ dN` has zero
  bracket, hence vanishes, which gives `N = ∫ σ dW`.
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open Matrix

variable {d m : ℕ}

/-- The four Penrose identities: `P` is the Moore–Penrose pseudoinverse of `σ`. -/
structure IsMoorePenrose (σ : Matrix (Fin d) (Fin m) ℝ) (P : Matrix (Fin m) (Fin d) ℝ) :
    Prop where
  left : σ * P * σ = σ
  right : P * σ * P = P
  symm_left : (σ * P)ᵀ = σ * P
  symm_right : (P * σ)ᵀ = P * σ

namespace IsMoorePenrose

variable {σ : Matrix (Fin d) (Fin m) ℝ} {P : Matrix (Fin m) (Fin d) ℝ}

theorem proj_idem (h : IsMoorePenrose σ P) : P * σ * (P * σ) = P * σ := by
  rw [← Matrix.mul_assoc, h.right]

theorem proj_idem' (h : IsMoorePenrose σ P) : σ * P * (σ * P) = σ * P := by
  rw [← Matrix.mul_assoc, h.left]

/-- **Bracket identity**: `P (σσᵀ) Pᵀ + (I - Pσ)(I - Pσ)ᵀ = I`. -/
theorem bracket_identity (h : IsMoorePenrose σ P) :
    P * (σ * σᵀ) * Pᵀ + (1 - P * σ) * (1 - P * σ)ᵀ = 1 := by
  have e1 : P * (σ * σᵀ) * Pᵀ = P * σ * (P * σ)ᵀ := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [e1, h.symm_right, transpose_sub, transpose_one, h.symm_right, h.proj_idem]
  set E := P * σ
  have e2 : (1 - E) * (1 - E) = 1 - E - E + E * E := by noncomm_ring
  rw [e2, h.proj_idem]
  abel

/-- `σ (I - Pσ) = 0`. -/
theorem sigma_mul_compl (h : IsMoorePenrose σ P) : σ * (1 - P * σ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.left, sub_self]

/-- `(I - σP) σ = 0`. -/
theorem compl_mul_sigma (h : IsMoorePenrose σ P) : (1 - σ * P) * σ = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, h.left, sub_self]

/-- **Residual bracket**: `(I - σP)(σσᵀ)(I - σP)ᵀ = 0`. -/
theorem residual_bracket (h : IsMoorePenrose σ P) :
    (1 - σ * P) * (σ * σᵀ) * (1 - σ * P)ᵀ = 0 := by
  rw [← Matrix.mul_assoc, h.compl_mul_sigma, Matrix.zero_mul, Matrix.zero_mul]

/-- `σ P (σσᵀ) = σσᵀ`: the bracket of `∫ σσ⁺ dN` is that of `N`. -/
theorem proj_mul_cov (h : IsMoorePenrose σ P) : σ * P * (σ * σᵀ) = σ * σᵀ := by
  rw [← Matrix.mul_assoc, h.left]

end IsMoorePenrose

end BlockBand.SourceProcess.Stochastic.Levy
