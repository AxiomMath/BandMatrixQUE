module

public import BlockBand.Palm.MomentFlow.BridgeLaw
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The removal identity for conditional moments

For the normalized monomials, `E[P_i X_j | m] = (ξ_j + 1) E[mono(X, ξ^{i,j}) | m]` for `j ≠ i` and
`E[P_i X_i | m] = ξ_i E[mono(X, ξ) | m]`, where `P_i` is the monomial of `ξ - δ_i`
(`condExp_remove_mul_ne`, `condExp_remove_mul_self`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory

variable {N : ℕ}

theorem condExp_remove_mul_ne {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) (ξ : Occ N) {i j : Fin N} (hij : i ≠ j) :
    μ[fun ω => momentMonomial (X ω) (remove ξ i) * X ω j | m] =ᵐ[μ]
      ((ξ j : ℝ) + 1) • μ[fun ω => momentMonomial (X ω) (move ξ i j) | m] := by
  have e : (fun ω => momentMonomial (X ω) (remove ξ i) * X ω j) =
      ((ξ j : ℝ) + 1) • fun ω => momentMonomial (X ω) (move ξ i j) := by
    funext ω; simp [momentMonomial_remove_mul_ne (X ω) ξ hij]
  rw [e]
  exact condExp_smul _ _ m

theorem condExp_remove_mul_self {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → Fin N → ℝ) {ξ : Occ N} {i : Fin N} (hi : 0 < ξ i) :
    μ[fun ω => momentMonomial (X ω) (remove ξ i) * X ω i | m] =ᵐ[μ]
      (ξ i : ℝ) • μ[fun ω => momentMonomial (X ω) ξ | m] := by
  have e : (fun ω => momentMonomial (X ω) (remove ξ i) * X ω i) =
      (ξ i : ℝ) • fun ω => momentMonomial (X ω) ξ := by
    funext ω; simp [momentMonomial_remove_mul_self (X ω) ξ hi]
  rw [e]
  exact condExp_smul _ _ m

end BlockBand.Palm.MomentFlow
