module

public import BlockBand.SourceProcess.FullSourceStops.PolyAlgebra

/-!
# The generator on powers: chain rule and the fourth-moment cancellation

* `wordGenerator_pow`: `𝒜(Φⁿ) = nΦⁿ⁻¹𝒜Φ + ½n(n-1)Φⁿ⁻²Γ(Φ)` (`Γ = wordCarre`): `wordGenerator`
  is a second-order operator whose second-order part is `½Γ`.
* `fourth_cancel`: at every point, `Σ_{r≤4} C(4,r)(-Φ)^{4-r}𝒜(Φ^r) = 0` — the generator of
  `(Φ - x)⁴` vanishes at `Φ = x`. Hence the conditional fourth moments of the increments are
  controlled by the summed errors of `Φ, …, Φ⁴` alone (used for the maximal jump in `tight`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements

variable {nT nI : ℕ}

theorem vars_pderiv_subset (Φ : TracePoly nT nI) (w : TraceWord nT nI) :
    (pderiv w Φ).vars ⊆ Φ.vars := by
  have h : Φ ∈ supported ℂ (↑Φ.vars : Set (TraceWord nT nI)) := mem_supported.mpr subset_rfl
  have h' := mem_supported.mp (FullSourceStops.pderiv_mem_supported h w)
  exact_mod_cast h'

/-- Sums over the variables of `Ψ` may be taken over any superset. -/
theorem sum_vars_pderiv_eq {Ψ : TracePoly nT nI} {s : Finset (TraceWord nT nI)}
    (hs : Ψ.vars ⊆ s) (X : TraceWord nT nI → TracePoly nT nI) :
    ∑ w ∈ Ψ.vars, pderiv w Ψ * X w = ∑ w ∈ s, pderiv w Ψ * X w :=
  Finset.sum_subset hs fun w _ hw => by rw [pderiv_eq_zero_of_notMem_vars hw, zero_mul]

theorem sum_vars_pderiv2_eq {Ψ : TracePoly nT nI} {s : Finset (TraceWord nT nI)}
    (hs : Ψ.vars ⊆ s) (Y : TraceWord nT nI → TraceWord nT nI → TracePoly nT nI) :
    ∑ w ∈ Ψ.vars, ∑ v ∈ Ψ.vars, pderiv v (pderiv w Ψ) * Y w v =
      ∑ w ∈ s, ∑ v ∈ s, pderiv v (pderiv w Ψ) * Y w v := by
  rw [Finset.sum_subset hs fun w _ hw => by
    simp [pderiv_eq_zero_of_notMem_vars hw]]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_subset hs fun v _ hv => ?_
  rw [pderiv_eq_zero_of_notMem_vars fun h => hv (vars_pderiv_subset Ψ w h), zero_mul]

theorem pderiv_pow' (Φ : TracePoly nT nI) (n : ℕ) (w : TraceWord nT nI) :
    pderiv w (Φ ^ n) = C (n : ℂ) * Φ ^ (n - 1) * pderiv w Φ := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, map_natCast, mul_assoc]

/-- **Chain rule for powers**: `𝒜(Φⁿ) = nΦⁿ⁻¹𝒜Φ + ½n(n-1)Φⁿ⁻²Γ(Φ)`. -/
theorem wordGenerator_pow (b E : ℝ) (q : Fin nI → ℝ → ℝ) (t : ℝ) (Φ : TracePoly nT nI)
    (n : ℕ) :
    wordGenerator b E q t (Φ ^ n) = C (n : ℂ) * Φ ^ (n - 1) * wordGenerator b E q t Φ +
      C (1 / 2 : ℂ) * (C (n : ℂ) * C ((n - 1 : ℕ) : ℂ)) * Φ ^ (n - 2) * wordCarre b E Φ := by
  have hs : (Φ ^ n).vars ⊆ Φ.vars := vars_pow Φ n
  unfold wordGenerator wordCarre
  rw [sum_vars_pderiv_eq hs, sum_vars_pderiv2_eq hs]
  have h2 : ∀ w v, pderiv v (pderiv w (Φ ^ n)) = C (n : ℂ) * (C ((n - 1 : ℕ) : ℂ) *
      Φ ^ (n - 2) * pderiv v Φ * pderiv w Φ + Φ ^ (n - 1) * pderiv v (pderiv w Φ)) := by
    intro w v
    rw [pderiv_pow', Derivation.leibniz, Derivation.leibniz, pderiv_pow', smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, pderiv_C, mul_zero, add_zero,
      show n - 1 - 1 = n - 2 by omega]
    ring
  have e1 : ∀ X : TraceWord nT nI → TracePoly nT nI, ∑ w ∈ Φ.vars, pderiv w (Φ ^ n) * X w =
      C (n : ℂ) * Φ ^ (n - 1) * ∑ w ∈ Φ.vars, pderiv w Φ * X w := fun X => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by rw [pderiv_pow']; ring
  have e2 : ∀ Y : TraceWord nT nI → TraceWord nT nI → TracePoly nT nI,
      ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars, pderiv v (pderiv w (Φ ^ n)) * Y w v =
        C (n : ℂ) * Φ ^ (n - 1) * ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars, pderiv v (pderiv w Φ) * Y w v +
          C (n : ℂ) * C ((n - 1 : ℕ) : ℂ) * Φ ^ (n - 2) *
            ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars, pderiv w Φ * pderiv v Φ * Y w v := fun Y => by
    simp only [h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2]
  ring

/-- **The fourth-moment cancellation**: `Σ_{r ≤ 4} C(4,r)(-Φ)^{4-r}𝒜(Φ^r)` evaluates to `0`. -/
theorem fourth_cancel (b E : ℝ) (q : Fin nI → ℝ → ℝ) (t : ℝ) (Φ : TracePoly nT nI)
    (z : TraceWord nT nI → ℂ) :
    ∑ r ∈ Finset.range 5, ((Nat.choose 4 r : ℕ) : ℂ) * (-eval z Φ) ^ (4 - r) *
      eval z (wordGenerator b E q t (Φ ^ r)) = 0 := by
  simp only [wordGenerator_pow, map_add, map_mul, map_pow, eval_C, Finset.sum_range_succ,
    Finset.range_zero, Finset.sum_empty]
  have h42 : Nat.choose 4 2 = 6 := by decide
  norm_num [h42]
  ring

end BlockBand.SourceProcess.FullSourceGenerator
