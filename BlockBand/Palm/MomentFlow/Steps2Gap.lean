module

public import BlockBand.Palm.RelativeLocalizationGapProb

/-!
# No collisions on `[a, ∞)`, base time included

This covers the endpoint `σ = a` of the moment flow (`ae_simple` covers `σ > a` only).
It uses `DysonBrownianMotion` through `RelativeLocalization.collision_null` (restart from `a/2`).

* **`ae_noCollision`** (`a > 0`): for `flowLaw N a`-a.e. `ω`, `ω.1` is Hermitian and
  `λ_i(σ) ≠ λ_j(σ)` for all `σ ≥ a` and all `i ≠ j`.
* `ae_shortGap_Icc`: the gap hypothesis of `exists_shortMomentFlow_one`
  (`continuousOn_shortGenerator`) holds a.s. on every `[s, u]` with `a ≤ s`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- **No collisions at any time `σ ≥ a`**, the base time included. -/
theorem ae_noCollision (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂flowLaw N a, ω.1.IsHermitian ∧ ∀ σ : ℝ, a ≤ σ → ∀ i j : Fin N, i ≠ j →
      flowEigenvalue F a ω σ i ≠ flowEigenvalue F a ω σ j := by
  have hnull : ∀ (T : ℕ) (p : {p : Fin N × Fin N // p.1 ≠ p.2}),
      ∀ᵐ ω ∂flowLaw N a, ω ∉ ⋂ n : ℕ, pairGapEvent F (T : ℝ≥0) p.1.1 p.1.2 (1 / ((n : ℝ) + 1)) :=
    fun T p => measure_eq_zero_iff_ae_notMem.1 (collision_null hDBM hF ha (T : ℝ≥0) p.2)
  have hall : ∀ᵐ ω ∂flowLaw N a, ∀ (T : ℕ) (p : {p : Fin N × Fin N // p.1 ≠ p.2}),
      ω ∉ ⋂ n : ℕ, pairGapEvent F (T : ℝ≥0) p.1.1 p.1.2 (1 / ((n : ℝ) + 1)) :=
    ae_all_iff.2 fun T => ae_all_iff.2 fun p => hnull T p
  filter_upwards [hall, ae_fst_isHermitian (N := N) a] with ω hω hH
  refine ⟨hH, fun σ hσ i j hij heq => ?_⟩
  obtain ⟨T, hT⟩ := exists_nat_ge (σ - a)
  apply hω T ⟨(i, j), hij⟩
  refine Set.mem_iInter.2 fun n => ⟨Real.toNNReal (σ - a), ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith)]; simpa using hT
  · rw [flowLam_eq_flowEigenvalue F a hH, Real.coe_toNNReal _ (by linarith),
      show a + (σ - a) = σ by ring]
    simp only [heq, sub_self, abs_zero]
    positivity

/-- The gap hypothesis of `exists_shortMomentFlow_one` holds a.s. on every `[s, u]`, `a ≤ s`. -/
theorem ae_shortGap_Icc (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂flowLaw N a, ∀ s u : ℝ, a ≤ s → ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l := by
  filter_upwards [ae_noCollision hDBM hF ha] with ω hω
  exact fun s u has x hx k l hkl => hω.2 x (has.trans hx.1) k l hkl

end BlockBand.Palm.MomentFlow
