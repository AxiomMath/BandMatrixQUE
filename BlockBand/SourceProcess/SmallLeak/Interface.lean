module

public import BlockBand.SourceProcess.SmallLeak.Defs

/-!
# The three steps of the small channel leakage bound

Notation: `n_s = ⌊Ws⌋`, `n_T = ⌊WT⌋`, `g_j = omittedFlux … j`, `ℓ_j = omittedLeak … j`.
The argument replaces the paper's transported carrier `D_t = N*|J_A(s)|N` by the omitted
flux `g_j` itself, which satisfies the one-step mean bound `E_j g_{j+1} ≤ (1 + ‖EΔ‖/η) g_j`
(`OmittedFluxGrowth`); the source leakage recursion is driven by `√g_j` and `g_j`
(`LeakRecursion`).

* `OmittedFluxStart`: `E g_{n_s} ≤ C h`. At `n_s`, `g = Σ_{t_i ≤ h²} t_i ≤ h Σ_i t_i^{1/2}`
  (the omitted part of `T_far`), and `E Tr T^{1/2} ≤ C` (the fractional transmission bound).
* `OmittedFluxGrowth`: `E g_j ≤ C E g_{n_s} + η` for `n_s ≤ j ≤ n_T`, all large `W`.
* `LeakRecursion`: if `E g_j ≤ x` on `[n_s, n_T]`, then
  `E ℓ_{n_T} ≤ C K (√x + x) + C/K + η` for every trace stop `K ≥ 1`, all large `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath

/-- **`E g_{n_s} ≤ C h`**: the omitted channels carry small flux at the closing time. -/
def OmittedFluxStart : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℝ, 0 < s →
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h < 1 → ∀ᶠ W : ℕ in atTop,
      ∫ ω, omittedFlux b E h s W ⌊(W : ℝ) * s⌋₊ ω ∂growthPathLaw W b ≤ C * h

/-- **The omitted flux stays comparable to its initial value in mean** along `[n_s, n_T]`. -/
def OmittedFluxGrowth : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → h < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ W : ℕ in atTop, ∀ j : ℕ,
      ⌊(W : ℝ) * s⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
        ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤
          C * ∫ ω, omittedFlux b E h s W ⌊(W : ℝ) * s⌋₊ ω ∂growthPathLaw W b + η

/-- **The summed leakage recursion** (the source leakage recursion, stopped at `Tr Q = K`). -/
def LeakRecursion : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ q : ℝ → ℝ, IsSourceTest s T q →
    ∃ C : ℝ, ∀ K : ℝ, 1 ≤ K → ∀ h : ℝ, 0 < h → h < 1 → ∀ η : ℝ, 0 < η → ∀ᶠ W : ℕ in atTop,
      ∀ x : ℝ, 0 ≤ x → (∀ j : ℕ, ⌊(W : ℝ) * s⌋₊ ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
        ∫ ω, omittedFlux b E h s W j ω ∂growthPathLaw W b ≤ x) →
      ∫ ω, omittedLeak b E h s q W ⌊(W : ℝ) * T⌋₊ ω ∂growthPathLaw W b ≤
        C * K * (Real.sqrt x + x) + C / K + η

end BlockBand.SourceProcess.SmallLeak
