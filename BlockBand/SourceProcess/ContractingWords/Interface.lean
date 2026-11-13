module

public import BlockBand.Internal.Contracts.TransmissionUniform2

/-!
# Contracting words: the one-step bounds and the summed step

This file defines the mean factor of a product of trace words and the hypotheses on one step of
the growth process used for the contracting-words lemma. Write `Z_j` for an admitted product,
`A_j = {j < σ_K}`, `F_j = growthSigma W j`, `E_j = E(·|F_j)`.

* **One step.** The Doob split of the step `j → j+1` is
  `ξ_{j+1} = Z_{j+1} - E_jZ_{j+1}` and `e_j = E_jZ_{j+1} - λZ_j`; `E_j[1_{A_j}ξ_{j+1}] = 0`
  because `A_j ∈ F_j` and `Z_{j+1}` is integrable. The two bounds are
  `WordStepMean` (`‖1_{A_j}(E_jZ_{j+1} - λZ_j)‖_p ≤ C/W`) and `WordStepFluct`
  (`‖1_{A_j}(Z_{j+1} - E_jZ_{j+1})‖_p ≤ C/√W`). They come from the transport
  `A ↦ N*AN` of the letters, the separator transport `B ↦ NBN*` with its conditional mean
  (`θ_*B`, `θ̄_*B`, `I + E𝓔`, `P - (D₀g/2W)P + …`) and the singular-value cut of the products of
  centered factors.
* **Decay** (`recursion_of`): Minkowski along the decreasing survival events, from the one-step
  bounds, the uniform bound `|λ| ≤ |θ_*| ≤ ρ₀ < 1` on `bulkInterval κI` and the initial bound
  `‖Z_{j₀}‖_p ≤ C` (every nonempty word is at most `L_j^{|w|}`,
  `L_j = 1 + 2g_j + Σ_a Tr Q_{a,j}`, together with the load moments).
* **Summation** (`summed_of`): from the per-step bound `SummedStep`
  (each conditional increment error is at most `C W⁻¹(ρ^{j - r_j} + W^{-1/2})`, with `r_j` the last
  restart: `⌈εW⌉` or a tag birth `k_a + 1 ≤ j`) by summing the geometric terms per restart.
  `SummedStep` is the finite-`W` form of the generator identity of the full-source generator
  theorem.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal ComplexConjugate

/-- The mean factor `λ = θ_*^r θ̄_*^{r̄}` of a product. -/
def meanFactor (b E : ℝ) (s : ℂ) {nT nI : ℕ} (Zs : List (TraceWord nT nI)) : ℂ :=
  thetaStar b E s ^ unconjCount Zs * conj (thetaStar b E s) ^ conjCount Zs

/-- **The conditional mean of one step.**
`b`, the bulk margin `κI`, the sources, `d, ε, T, K, p`, then `C, W₀`. For `W ≥ W₀`, every
`E ∈ bulkInterval κI`, every stationary jet `s`, tag births `k_a ≥ εW`, every admitted product of
degree `≤ d` with a contracting letter and every step `εW ≤ j`, `k_a < j` (no tag is born at the
step `j → j+1`), `j + 1 ≤ TW`: `‖1_{A_j}(E_jZ_{j+1} - λZ_j)‖_p ≤ C/W`. -/
def WordStepMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, k a < j) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            (growthPathLaw W b)[fun ω' => productValue b E k q W (j + 1) ω' Zs |
              growthSigma W j] ω - meanFactor b E s Zs * productValue b E k q W j ω Zs)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)

/-- **The centered part of one step.** Same data (no jet is
needed), then `C, W₀`: `‖1_{A_j}(Z_{j+1} - E_jZ_{j+1})‖_p ≤ C/√W`. -/
def WordStepFluct : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, k a < j) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm ((alive b E k q K ε W j).indicator fun ω =>
            productValue b E k q W (j + 1) ω Zs -
              (growthPathLaw W b)[fun ω' => productValue b E k q W (j + 1) ω' Zs |
                growthSigma W j] ω)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / Real.sqrt W)

/-- The restart index of the geometric term at step `j`: the last tag birth `k_a + 1 ≤ j`, or
`⌈εW⌉` before the first birth. -/
def restartIndex (ε : ℝ) (W : ℕ) {nT : ℕ} (k : Fin nT → ℕ) (j : ℕ) : ℕ :=
  max ⌈ε * W⌉₊ ((Finset.univ.filter fun a => k a < j).sup fun a => k a + 1)

/-- **The per-step increment errors.** `b`, the bulk
margin `κI`, the sources, an ordinary trace polynomial `Φ`, `ε, T, K`, then `C, ρ < 1, W₀`. For
`W ≥ W₀`, every `E ∈ bulkInterval κI`, tag births `k_a ≥ εW` and every step `εW ≤ j`, `j ≠ k_a`,
`j + 1 ≤ TW`, the expected absolute errors of the first and second conditional increment formulas
are at most `C W⁻¹(ρ^{j - r_j} + W^{-1/2})`, `r_j = restartIndex ε W k j`. The geometric term comes
from pairing the Ward mean with old words (a contracting word, by the word mixing rate started
at the last restart); the rest from the full-source covariance lemma and the one-step expansion. -/
def SummedStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      ∀ j : ℕ, ε * W ≤ j → (∀ a, j ≠ k a) → ((j + 1 : ℕ) : ℝ) ≤ T * W →
      let μ := growthPathLaw W b
      let A := alive b E k q K ε W j
      let F : ℕ → GrowthPath W → ℂ := fun i ω => polyValue b E k q W i ω Φ
      let err : ℝ := C / W * (ρ ^ (j - restartIndex ε W k j) + 1 / Real.sqrt W)
      ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ ≤ ENNReal.ofReal err ∧
      ∫⁻ ω, ‖A.indicator (fun ω =>
          μ[A.indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ ≤ ENNReal.ofReal err

end BlockBand.SourceProcess.ContractingWords
