module

public import BlockBand.Internal.Contracts.LayersOnePort

/-!
# One-port passive mean: vocabulary and the named inputs

The objects and the two named inputs of `OnePortPassiveMeanContract`: the mean equations and the
bottom-source trace equations of the one-port layer, and the passive mean identity.

Setting (that of `OnePortPassiveMeanContract`): the fresh one-block one-port layer `layerLaw W b .oneBlockOnePort`
(`A ~ GUE_W(c/W)`, `c = 1 - 2b`, `B ~ Gin(b/W)`), `z = z_∂(E)`, `E ∈ bulkInterval κ`, a
deterministic passive `X` (`-Im X ⪰ 0`; no bound on `‖X‖` or on `‖Im X‖`), `𝒢 = onePortResolvent`,
`K = z - X`, `L = K𝒢₁₂`. All matrices live on `Fin W`; norms are `ℓ²` operator norms.

## Vocabulary (all defined from expectations under the fresh layer law only)

* `oppG11`, `oppG22`: the blocks `𝒢₁₁` (physical) and `𝒢₂₂` (port) of `𝒢`, on `Fin W`.
* `oppMeanTop = E 𝒢₁₁` (entrywise, `matrixExpect`); `oppG1 = W⁻¹ Tr E𝒢₁₁`, `oppG2 = W⁻¹ Tr E𝒢₂₂`
  (the layer means `ḡ₁, ḡ₂`).
* `oppT1 = E W⁻¹ Tr 𝒢₁₂𝒢₁₂*`, `oppT2 = E W⁻¹ Tr 𝒢₂₂𝒢₂₂*` (the bottom-source traces `t₁, t₂`;
  real and nonnegative by construction).
* `oppTopMatrix b E X g₁ g₂ = (-E - c g₁ - b g₂) - X` (`T̄ = z - X - Ω̄`, `Ω̄ = c(ḡ₁-a) + b(ḡ₂-a)`),
  `oppPortV b E g₁ = (z - b g₁)⁻¹` (`v̄`), `oppNTr M = W⁻¹ Re Tr MM*` (`A_M`),
  `oppS b t₁ t₂ = c t₁ + b t₂`.

## Named inputs

* `OppPassiveInverseMoments`: uniform moments of `‖𝒢‖` for passive `X` (shape of
  `OnePortOperatorMomentsContract.moments`, with `𝒢` in place of `L`); supplied by
  `opm_passive_inverse_moments`. Only `p = 1` is used.
* `OppPassiveMeanEquations` (see its docstring; proved as `oppPassiveMeanEquations_holds`): the passive one-port
  Schwinger–Dyson system with `O(W⁻²)` errors, uniformly in passive `X`, in terms of the layer
  means. These are exactly the paper's mean equations and its bottom-source trace
  equations and first form of the passive mean identity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.LayersOnePort
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 0. Blocks and means of the one-port layer
-/

/-- `𝒢₁₁`: the physical block of the one-port layer resolvent, on `Fin W`. -/
def oppG11 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y =>
    onePortResolvent b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))

/-- `𝒢₂₂`: the port block of the one-port layer resolvent, on `Fin W`. -/
def oppG22 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y =>
    onePortResolvent b E X ω (Sum.inr ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- `E 𝒢₁₁` (entrywise expectation under the fresh layer law). -/
def oppMeanTop (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  matrixExpect (layerLaw W b .oneBlockOnePort) (oppG11 b E X)

/-- `ḡ₁ = W⁻¹ Tr E𝒢₁₁`. -/
def oppG1 (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (oppMeanTop b E X).trace

/-- `ḡ₂ = W⁻¹ Tr E𝒢₂₂`. -/
def oppG2 (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (matrixExpect (layerLaw W b .oneBlockOnePort) (oppG22 b E X)).trace

/-- `t₁ = E W⁻¹ Tr 𝒢₁₂𝒢₁₂*` (the physical trace of the bottom source `𝒢 P_port 𝒢*`). -/
def oppT1 (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∫ ω, (W : ℝ)⁻¹ * (onePortG12 b E X ω * (onePortG12 b E X ω)ᴴ).trace.re
    ∂layerLaw W b .oneBlockOnePort

/-- `t₂ = E W⁻¹ Tr 𝒢₂₂𝒢₂₂*` (the port trace of the bottom source `𝒢 P_port 𝒢*`). -/
def oppT2 (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ∫ ω, (W : ℝ)⁻¹ * (oppG22 b E X ω * (oppG22 b E X ω)ᴴ).trace.re
    ∂layerLaw W b .oneBlockOnePort

/-!
## 1. Deterministic mean-field objects at given means
-/

/-- The top matrix at the means `g₁, g₂`: `T̄ = (-E - c g₁ - b g₂) - X`, `c = 1 - 2b`. With
`z = -E - (1-b)a` this is `z - X - Ω̄`, `Ω̄ = c(g₁ - a) + b(g₂ - a)`. -/
def oppTopMatrix (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (g₁ g₂ : ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (-(E : ℂ) - (1 - 2 * (b : ℂ)) * g₁ - (b : ℂ) * g₂) • (1 : Matrix (Fin W) (Fin W) ℂ) - X

/-- The port value at the mean `g₁`: `v̄ = (z - b g₁)⁻¹`, `z = z_∂(E)`. -/
def oppPortV (b E : ℝ) (g₁ : ℂ) : ℂ := (boundaryZ b E - (b : ℂ) * g₁)⁻¹

/-- `A_M = W⁻¹ Re Tr MM*`. -/
def oppNTr {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) : ℝ := (W : ℝ)⁻¹ * (M * Mᴴ).trace.re

/-- `s = c t₁ + b t₂`, `c = 1 - 2b` (the coefficient of `(KM)(KM)*` in the passive
mean identity). -/
def oppS (b t₁ t₂ : ℝ) : ℝ := (1 - 2 * b) * t₁ + b * t₂

/-!
## 2. The named inputs
-/

/-- **Passive inverse moments** (named input, supplied by `opm_passive_inverse_moments`). This is
the passive-bounds lemma ("all fixed operator moments of `𝒢` … are bounded uniformly in
`W ≥ W₀(p), X`"), via the Poisson extension. Shape of `OnePortOperatorMomentsContract.moments`
with `𝒢` in place of `L`.

* Law: `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`; `𝒢 = onePortResolvent b E X`.
* Quantifiers: `b ∈ (0,1/2)`, `κ > 0`, `p ≥ 1`; then `C_p, W₀`; then uniformly in `W ≥ W₀`, every
  passive `X` and `E ∈ bulkInterval κ`: `‖ ‖𝒢‖_op ‖_{L^p} ≤ C_p`.
* Use here: only `p = 1` (bounds on `‖E𝒢₁₁‖`, `|ḡ₂|` and integrability of `𝒢`). -/
def OppPassiveInverseMoments : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal p)
          (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal Cp

/-- **The passive one-port Schwinger–Dyson system** (named input, proved as
`oppPassiveMeanEquations_holds`). In the paper: the mean equations "`M = (z - X - Ω)⁻¹`,
`m = W⁻¹ Tr M`, `v = (z - bm)⁻¹`", "the advanced/retarded trace equations for a bottom source are
`t₁ = A_M(ct₁ + bt₂) + O(W⁻²)` and `t₂ = h(1 + bt₁) + O(W⁻²)`" and the first form of
the passive mean identity, `E(LL*|X) = (ct₁ + bt₂)(KM)(KM)* + O_op(W⁻²)`, all written at the
layer means.

* Law: `layerLaw W b .oneBlockOnePort` at `z = z_∂(E)`, deterministic passive `X` (no bound on
  `‖X‖` or `‖Im X‖`), `K = z - X`, `L = K𝒢₁₂`.
* Quantifiers: `b ∈ (0,1/2)`, `κ > 0`; then `C, W₀`; then uniformly in `W ≥ W₀`, every passive `X`
  and `E ∈ bulkInterval κ` (no scalar-domain restriction).
* Objects: `Ḡ = E𝒢₁₁`, `ḡ₁ = W⁻¹ Tr Ḡ`, `ḡ₂ = W⁻¹ Tr E𝒢₂₂`, `t₁ = E W⁻¹ Tr 𝒢₁₂𝒢₁₂*`,
  `t₂ = E W⁻¹ Tr 𝒢₂₂𝒢₂₂*`, `T̄ = (-E - cḡ₁ - bḡ₂) - X`, `M̄ = T̄⁻¹`, `v̄ = (z - bḡ₁)⁻¹`,
  `A = W⁻¹ Re Tr M̄M̄*`, `s = ct₁ + bt₂`.
* Conclusion (`ρ = C W⁻²`):
  1. `‖T̄ Ḡ - I‖ ≤ ρ` (top block of the first-order Schwinger–Dyson identity
     `(N₀ - S(E𝒢)) E𝒢 = I + E[S(𝒢 - E𝒢)𝒢]`; the error is `Cov(cg₁ + bg₂, 𝒢₁₁)`);
  2. `|ḡ₂ (z - bḡ₁) - 1| ≤ ρ` (normalized trace of its port block; error `b Cov(g₁, g₂)`);
  3. `|t₁ - s A| ≤ ρ` and 4. `|t₂ - (1 + bt₁)|v̄|²| ≤ ρ` (normalized traces of the blocks of the
     second-order identity `(N₀ - S(E𝒢)) EF = (P_port + S(EF)) E𝒢* + E[S(Δ𝒢)ΔF] + E[S(ΔF)Δ𝒢*]`,
     `F = 𝒢 P_port 𝒢*`, obtained from `N F = P_port 𝒢*` by Gaussian integration by parts);
  5. `‖E LL* - s (KM̄)(KM̄)*‖ ≤ ρ` (top block of the same identity multiplied by `K*` on the right
     and by `KM̄` on the left; with `E[(K𝒢₁₁)*] = (KM̄(I + T̄Ḡ - I))*`).
* Why it is true for every passive `X`: the only random words in the errors are
  `Cov(cg₁ + bg₂, 𝒢₁₂L*)`, `Cov(cτ₁ + bτ₂, (K𝒢₁₁)*)` and unweighted covariances of `𝒢`,
  i.e. words in `𝒢, 𝒢*, K𝒢, 𝒢*K*` only (never `𝒢₁₁K*`); their moments are uniform in passive `X`
  (`K𝒢₁₁ = I + [(z+E) - A + z⁻¹BB*]𝒢₁₁`, `L = -z⁻¹(K𝒢₁₁)B`, the passive-bounds lemma), and the
  trace–matrix contraction gives `W⁻²` ("normalized trace–matrix covariances of their fixed inverse
  words are `O(W⁻²)`"). The deterministic factor `KM̄ = I + Ω̄M̄` is bounded because
  `‖M̄‖ ≤ 2‖E𝒢₁₁‖` once item 1 holds. No smallness of `δ₀`, `δ₁`, `g/W` or of `‖Im X‖` enters. -/
def OppPassiveMeanEquations : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, IsPassiveInput X → ∀ E ∈ bulkInterval κ,
      ‖oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X) * oppMeanTop b E X - 1‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖oppG2 b E X * (boundaryZ b E - (b : ℂ) * oppG1 b E X) - 1‖ ≤ C / (W : ℝ) ^ 2 ∧
        |oppT1 b E X - oppS b (oppT1 b E X) (oppT2 b E X) *
            oppNTr (oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X))⁻¹| ≤ C / (W : ℝ) ^ 2 ∧
        |oppT2 b E X - (1 + b * oppT1 b E X) * ‖oppPortV b E (oppG1 b E X)‖ ^ 2| ≤
          C / (W : ℝ) ^ 2 ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort)
              (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ) -
            ((oppS b (oppT1 b E X) (oppT2 b E X) : ℝ) : ℂ) •
              (((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
                  (oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X))⁻¹) *
                ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
                  (oppTopMatrix b E X (oppG1 b E X) (oppG2 b E X))⁻¹)ᴴ)‖ ≤ C / (W : ℝ) ^ 2

end BlockBand.Layers
