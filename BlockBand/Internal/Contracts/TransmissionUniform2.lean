module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Energy-uniform source statements and the passive scalar contraction

Versions of the full-source covariance, contracting-word, stopping and tag-birth statements with
constants uniform over energies in a compact bulk set, as used in the tagged convex-order and
local mass flatness theorems, and the one-step predictable contraction of the scalar jet.

In each energy-uniform version the bulk margin `κI` comes first, then the constants
(`C, ρ, W₀, M`); the statement holds at every `E ∈ bulkInterval κI` (and every stationary jet at
`E` where one is used). The fixed-energy statements are the case `κI = min(E+2, 2−E)`; moving
energies `e_W → E` are covered by `κI = min(E+2, 2−E)/2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionUniform2
open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexConjugate ComplexOrder

/-!
## 1. The full-source covariance lemma uniformly on compact bulk sets
-/

/-- **The full-source covariance lemma, energy-uniform.** `b`, the bulk margin `κI`, then
`C, W₀`.
For `W ≥ W₀`, every energy `E ∈ bulkInterval κI`, every stationary jet `s` at `E`, every
deterministic Hermitian old two-port `𝕏` and every four vectors, the covariance bound of
`FullSourceCovarianceContract`
holds at `E`:
`|E[(v₁*𝓔⁰v₂)(v₃*𝓔⁰v₄)] - main| ≤ C[W⁻² + W⁻¹(δ₀ + δ₁ + g/W)] ∏‖v_i‖`.
-/
def FullSourceCovarianceEnergyUniformContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ,
      let X := nearSchur (boundaryZ b E) XX
      let P := nearProjection W
      let S := twoPortScattering b E XX
      let P' := Sᴴ * P * S
      let η2 : ℂ := ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ)
      ‖bilinearCovariance (freshLaw W b) (wardNoise b E XX) v₁ v₂ v₃ v₄ -
          ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
              (crossedTensor v₁ v₂ v₃ v₄ P P' + crossedTensor v₁ v₂ v₃ v₄ P' P) -
            sigmaMinus b E s / η2 * crossedTensor v₁ v₂ v₃ v₄ (P * S) (P * S) -
            conj (sigmaMinus b E s) / η2 * crossedTensor v₁ v₂ v₃ v₄ (Sᴴ * P) (Sᴴ * P))‖ ≤
        C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
          conductanceOf (passiveTransmission b E X) / W)) * fourNorm v₁ v₂ v₃ v₄

/-!
## 2. Contracting trace words uniformly on compact bulk sets
-/

/-- **The contracting-words lemma, energy-uniform.**
* `recursion`: `b`, the bulk margin `κI`, the source family `(nT, nI, q)`, the degree `d` and
 `ε, T, K, p`, then `C, ρ < 1, W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κI` and every
 stationary jet `s` at `E`, the one-step recursion and decay of every admitted product
 with a contracting separator hold at `E`, with these `C, ρ`.
* `summed`: `b, κI`, the source family, an ordinary trace polynomial `Φ` and `ε, T, K`, then
 `C, W₀`. For `W ≥ W₀` and every `E ∈ bulkInterval κI`, the summed increment errors at `E`
 are at most `C(W^{-1/2} + W⁻¹)`.
-/
structure ContractingWordsEnergyUniformContract : Prop where
  recursion : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) → ∀ j₀ : ℕ, ε * W ≤ j₀ → (∀ a, k a < j₀) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      let μ := growthPathLaw W b
      let lam : ℂ := thetaStar b E s ^ unconjCount Zs * conj (thetaStar b E s) ^ conjCount Zs
      let Z : ℕ → GrowthPath W → ℂ := fun j ω => productValue b E k q W j ω Zs
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      (∀ j : ℕ, j₀ ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W → ∃ ξ : GrowthPath W → ℂ,
        Integrable ((A j).indicator ξ) μ ∧
        μ[(A j).indicator ξ | growthSigma W j] =ᵐ[μ] 0 ∧
        eLpNorm ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / W) ∧
        eLpNorm ((A j).indicator ξ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / Real.sqrt W)) ∧
      ∀ j : ℕ, j₀ ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm ((A j).indicator (Z j)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * (ρ ^ (j - j₀) + 1 / Real.sqrt W))
  summed : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      let μ := growthPathLaw W b
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      let F : ℕ → GrowthPath W → ℂ := fun j ω => polyValue b E k q W j ω Φ
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ) ∧ ∀ a, j ≠ k a
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W)) ∧
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W))

/-!
## 3. The full-source stopping lemma uniformly on compact bulk sets
-/

/-- **The full-source stopping lemma, energy-uniform.** `b`, the bulk margin `κI`, the
source family and `0 < ε < T` come first.
* `tail`: then `C`. For every `K > 0`, the `limsup` in `W` of the supremum over tag birth
  indices **and over energies `E ∈ bulkInterval κI`** of
  `P{sup_{εW ≤ j ≤ TW} traceLoad > K}` is at most `C/K`.
* `supMoments`: for `p > 0`, then `C, W₀`. The supremum moments hold at every
  `E ∈ bulkInterval κI`.
* `compensatorUI`: for `Φ` and `η > 0`, then `M, W₀`. The uniform integrability bound holds at every
  `E ∈ bulkInterval κI`. -/
structure FullSourceStopsEnergyUniformContract : Prop where
  tail : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ C : ℝ, ∀ K : ℝ, 0 < K →
      limsup (fun W : ℕ => ⨆ (E : ℝ) (_ : E ∈ bulkInterval κI) (k : Fin nT → ℕ),
          growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧ (j : ℝ) ≤ T * W ∧
            K < traceLoad b E k q W j ω}) atTop ≤ ENNReal.ofReal (C / K)
  supMoments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T p : ℝ, 0 < ε → ε < T →
    0 < p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ (k : Fin nT → ℕ) (a : Fin nT ⊕ Fin nI),
      ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W), ‖sourceTrace b E k q W j ω a‖ₑ) ^ p
        ∂growthPathLaw W b ≤ ENNReal.ofReal C
  compensatorUI : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T η : ℝ, 0 < ε → ε < T → 0 < η →
    ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ k : Fin nT → ℕ,
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ)
      let drift : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)‖ₑ
      let qv : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordCarre b E Φ)‖ₑ
      ∫⁻ ω, {ω | ENNReal.ofReal M < drift ω}.indicator drift ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η ∧
        ∫⁻ ω, {ω | ENNReal.ofReal M < qv ω}.indicator qv ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η

/-!
## 4. Tag-birth values uniformly on compact bulk sets
-/

/-- **Tag-birth values, energy-uniform.** `b`, the bulk margin
`κI` and `0 < ε < T` come first.
* `trace`: for `p ≥ 1` and `θ > 0`, then `W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κI` and every
  birth index `εW ≤ k`, `k + 1 ≤ TW`: `‖W⁻¹Tr Y_{k+1;k} - d_*‖_p ≤ θ`. The `o(1)` rate is uniform in
  the energy.
* `square`: then `C, W₀`, and `E Tr(Y_{k+1;k}/W)² ≤ C/W` at every such `E` and `k`. -/
structure TagBirthValueEnergyUniformContract : Prop where
  trace : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε T p : ℝ, 0 < ε → ε < T →
    1 ≤ p → ∀ θ : ℝ, 0 < θ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : ℕ, ε * W ≤ k → ((k + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ))
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal θ
  square : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : ℕ, ε * W ≤ k → ((k + 1 : ℕ) : ℝ) ≤ T * W →
        ∫⁻ ω, ‖(((W : ℂ)⁻¹ • tagResponse b E W (k + 1) k ω) ^ 2).trace‖ₑ ∂growthPathLaw W b ≤
          ENNReal.ofReal (C / W)

/-!
## 5. The one-step predictable contraction of the scalar jet
-/

/-- `W⁻¹Tr(z − X₊)⁻¹` for one fresh one-port layer, `X₊ = freshSchur E X ω`;
`δ₀(X₊) = |freshTrace − a|`.
-/
def freshTrace (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  (W : ℂ)⁻¹ * (passiveResolvent b E (freshSchur E X ω)).trace

/-- The centered fresh part `ξ₊ = freshTrace - E freshTrace`. -/
def scalarFluct (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  freshTrace b E X ω - ∫ ω', freshTrace b E X ω' ∂freshLaw W b

/-- The one-step predictable contraction of the scalar jet.
* `contraction`: `b, κ`, then the domain radius `d₀ > 0`, the contraction `0 ≤ ρ < 1`, `C ≥ 0`
  and `W₀`. For `W ≥ W₀`, every `E ∈ bulkInterval κ` and every passive `X` with `δ₀(X) ≤ d₀`:
  `ξ₊` is integrable with mean `0`, and at every fresh sample
  `δ₀(X₊) ≤ ρ δ₀(X) + C/W² + |ξ₊|`.
* `fluct`: for every `r ≥ 1`, there are `C_r, W₀` such that `‖ξ₊‖_{L^r(freshLaw)} ≤ C_r/W` for every
  `W ≥ W₀`, every `E ∈ bulkInterval κ` and every passive `X`.

Here `X` is a deterministic passive input (`−Im X ⪰ 0`) and the fresh layer has law
`freshLaw W b`. -/
structure PassiveScalarContractionContract : Prop where
  contraction : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (d₀ ρ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ ρ ∧ ρ < 1 ∧ 0 ≤ C ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → jetDistance0 b E X ≤ d₀ →
          Integrable (scalarFluct b E X) (freshLaw W b) ∧
          ∫ ω, scalarFluct b E X ω ∂freshLaw W b = 0 ∧
          ∀ ω, jetDistance0 b E (freshSchur E X ω) ≤
            ρ * jetDistance0 b E X + C / (W : ℝ) ^ 2 + ‖scalarFluct b E X ω‖
  fluct : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ r : ℝ, 1 ≤ r →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (scalarFluct b E X) (ENNReal.ofReal r) (freshLaw W b) ≤ ENNReal.ofReal (C / W)

end BlockBand.Internal.Contracts.TransmissionUniform2
