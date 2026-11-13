module

public import BlockBand.Transmission.PathScalar.MeanStage2

/-!
# `PassiveMeanStep` from the one-port mean equations

`passiveMeanStep_of_equations : PassiveMeanEquations → PassiveMeanStep`. The deterministic part
(stable-branch selection and the sharp contraction `ρ < 1`) is `passiveMean_stability`.

**Input** `PassiveMeanEquations`: for one fresh one-port layer and a deterministic passive
`X`, the port mean `u = E W⁻¹Tr R₊` and some `v` with `Im v ≤ 0`, `|v| ≤ C_v`, satisfy
`|u(z - bv) - 1| ≤ C/W²` and `|v - W⁻¹Tr(ζ - X)⁻¹| ≤ C/W²` with `ζ = -E - cv - bu`. The intended
witness is `v = E W⁻¹Tr 𝒢₁₁`. The two equations are the IBP identities of
the layer contraction lemma for the one-port layer:
- `(z - b v) E𝒢₂₂ = 1 + b Cov(g, 𝒢₂₂)` (Ginibre IBP in `B̄`, `stein_layerBconj_lin`);
- `(ζ - X) E𝒢₁₁ = 1 + c Cov(g, 𝒢₁₁) + b Cov(u, 𝒢₁₁)` (GUE and Ginibre IBP,
  `stein_layerA_lin`, `stein_layerB_lin`).

Their covariances are `O(W⁻²)` in operator norm by `PassiveBoundsStatement.traceMatrix`.
The bounds needed besides are:
- `Im v ≤ 0`, since `Im 𝒢₁₁ ⪯ 0` at Hermitian `A`;
- `|v| ≤ E‖𝒢‖`, from the `moments` clause;
- `‖(ζ - X)⁻¹‖ ≤ 1/Im ζ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder

/-- **The one-port mean equations** (see the module docstring). -/
def PassiveMeanEquations : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (Cv C : ℝ) (W₀ : ℕ), 0 ≤ Cv ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
          ∃ v : ℂ, v.im ≤ 0 ∧ ‖v‖ ≤ Cv ∧
            ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) * (boundaryZ b E - (b : ℂ) * v) - 1‖ ≤
              C / (W : ℝ) ^ 2 ∧
            ‖v - stieltjes X (zetaOf b E v (∫ ω, freshPortTrace b E X ω ∂freshLaw W b))‖ ≤
              C / (W : ℝ) ^ 2

/-- **`PassiveMeanStep` from the mean equations.** -/
theorem passiveMeanStep_of_equations (h : PassiveMeanEquations) : PassiveMeanStep := by
  intro b hb0 hb κ hκ
  obtain ⟨Cv, C, W₀, hCv, hC, hEq⟩ := h b hb0 hb κ hκ
  obtain ⟨d₀, ρ, C', ε₀, hd₀, hρ0, hρ1, hC', hε₀, hst⟩ := passiveMean_stability hb0 hb hκ hCv
  refine ⟨d₀, ρ, C' * C, max W₀ (⌈C / ε₀⌉₊ + 1), hd₀, hρ0, hρ1, mul_nonneg hC' hC, ?_⟩
  intro W hW E hE X hY hX
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : ⌈C / ε₀⌉₊ + 1 ≤ W := le_trans (le_max_right _ _) hW
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast (by omega : 1 ≤ W)
  have hx0 : (0 : ℝ) < W := by linarith
  have hε : C / (W : ℝ) ^ 2 ≤ ε₀ := by
    have hc := Nat.le_ceil (C / ε₀)
    have hc' : ((⌈C / ε₀⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast (by omega : ⌈C / ε₀⌉₊ ≤ W)
    have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have h1 : C / ε₀ ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hε₀] at h1
    linarith
  obtain ⟨v, hv0, hvC, hs, hr⟩ := hEq W hW0 E hE X hY
  have := hst W E hE X hY v _ (C / (W : ℝ) ^ 2) hv0 hvC hs hr (by positivity) hε hX
  calc _ ≤ ρ * jetDistance0 b E X + C' * (C / (W : ℝ) ^ 2) := this
    _ = ρ * jetDistance0 b E X + C' * C / (W : ℝ) ^ 2 := by ring

end BlockBand.Transmission.PathScalar
