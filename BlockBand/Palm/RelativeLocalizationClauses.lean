module

public import BlockBand.Palm.RelativeLocalizationBridge
public import BlockBand.Palm.RelativeLocalizationMarkov

/-!
# Relative localization: the clauses of the good spectral events along the flow

`goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ` is the conjunction of the six clauses of
`SpectralGoodEventContract` (and of `GoodEvent.spectralGoodEvent_s8`) at time `σ`, with
displacement constant `D₀` (`C√t`, resp. `C√τ`). Consequences when `ω.1` is Hermitian:
`flowEigenvalue_monotone'`, `disp_le` (Weyl: `|λ_k(σ) - λ_k(a)| ≤ D₀`), `clauses_not_fail`
(the vector is outside `failSet`), and the shifted forms through `flowLam`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory Set Matrix BlockBand.Internal.Contracts.CoareaPalm
open scoped NNReal

variable {N : ℕ}

/-- The six clauses of the good spectral event at time `σ`. -/
def goodClauses (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (E r₀ c₁ C₁ C b₀ : ℝ) (ℓ : ℕ) (h D₀ σ : ℝ) : Prop :=
  (∀ i j : Fin N, ℓ ≤ labelDist i j →
    c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) ∧
  (∀ i j : Fin N, labelDist i j < ℓ →
    min |flowEigenvalue F a ω σ i - E| |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
    |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| ≤ C₁ * ℓ / N) ∧
  (∀ x y : ℝ, x ≤ y →
    ((Finset.univ.filter fun i : Fin N =>
        flowEigenvalue F a ω σ i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h)) ∧
  (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
    c₁ * N * (y - x) ≤
      ((Finset.univ.filter fun i : Fin N =>
        flowEigenvalue F a ω σ i ∈ Set.Icc x y).card : ℝ)) ∧
  (∀ i : Fin N, longCoupling F a ω ℓ σ i ≤ C * N / ℓ ∧
    (|flowEigenvalue F a ω σ i - E| ≤ r₀ / 8 → b₀ * N / ℓ ≤ longCoupling F a ω ℓ σ i)) ∧
  (∀ x : Fin N → ℂ, l2Norm ((flowMatrix F a ω σ - flowMatrix F a ω a) *ᵥ x) ≤ D₀ * l2Norm x)

theorem flowMatrix_isHermitian {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian :=
  (hF.add hω).add (hermitianBrownian_isHermitian _ _)

theorem flowEigenvalue_monotone' {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) :
    Monotone (flowEigenvalue F a ω σ) :=
  freshEigenvalue_monotone (flowMatrix_isHermitian hF a hω σ)

theorem disp_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a : ℝ}
    {ω : FlowSample N} (hω : ω.1.IsHermitian) {E r₀ c₁ C₁ C b₀ : ℝ} {ℓ : ℕ} {h D₀ σ : ℝ}
    (hg : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ) (k : Fin N) :
    |flowEigenvalue F a ω σ k - flowEigenvalue F a ω a k| ≤ D₀ :=
  abs_freshEigenvalue_sub_le (flowMatrix_isHermitian hF a hω σ) (flowMatrix_isHermitian hF a hω a)
    hg.2.2.2.2.2 k

theorem clauses_not_fail {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} {ω : FlowSample N}
    {E r₀ c₁ C₁ C b₀ : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hN : 0 < N)
    {h D₀ σ : ℝ} (hg : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ) :
    flowEigenvalue F a ω σ ∉ failSet N ℓ E r₀ c₁ C₁ :=
  not_mem_failSet_of_clauses hℓ hc₁ hC₁ hN hg.1 hg.2.1

end BlockBand.Palm.RelativeLocalization
