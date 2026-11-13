module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.TransmissionFlow

/-!
# Relative localization, stochastic form: rotation rates and target statements

Definitions and statements only (no proofs). Along a sample `ω` of `flowLaw N a` the rotation
rates and the damping are deterministic functions of the eigenvalue path:

* `shortRate F a ω ℓ σ k l = c_kl(σ) 1{0 < |k-l| < ℓ}` (`c_kl = flowRate`), the short
  rotations, kept everywhere (all short rotations, no bulk cut);
* `refDamping F a b₀ ω ℓ σ k = β̂_k(σ) = max(β_k(σ), b₀N/ℓ)`.

* `ReferenceFiniteSpeedStochasticStatement` (reference finite speed):
  `∫_a^c E_aux Σ_{j∉J} |(𝓜_{s,c})_{kj}|² ds ≤ N^{-D}` outside path probability `N^{-D}`, for
  every family of reference flows `𝓜_{s,·}`, `s ∈ [a,c]`;
* `ShortRowStochasticStatement`, `ShortColumnStochasticStatement`:
  `E_aux Σ_{|j-k|>R} |M_{s,u}(k,j)|²` and `E_aux Σ_{|j-k|>R} |M_{s,u}(j,k)|²` exceed
  `exp(-c'N^ε)` with probability at most `N^{-D}` when the moving centre is in the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization.StochasticBridge

open MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow)
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal

variable {N : ℕ}

/-- Short rotation rates `c_kl(σ) 1{0 < |k-l| < ℓ}` along the eigenvalue path of `ω`. -/
def shortRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ)
    (k l : Fin N) : ℝ :=
  if k ≠ l ∧ labelDist k l < ℓ then flowRate F a ω σ k l else 0

/-- Reference damping `β̂_k(σ) = max(β_k(σ), b₀N/ℓ)` along the eigenvalue path of `ω`. -/
def refDamping (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ)
    (k : Fin N) : ℝ :=
  max (longCoupling F a ω ℓ σ k) (b₀ * N / ℓ)

/-- **Reference finite speed, stochastic form.** Same quantifiers,
scales and window `J` as `RelativeLocalizationContract.reference_finite_speed`; the integrand is
`E_aux Σ_{j∉J} |(𝓜_{s,c})_{kj}|²` for a family `Mf s` of reference rotation flows started at
every `s ∈ [a,c]` (short rates, damping `β̂`). -/
def ReferenceFiniteSpeedStochasticStatement : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ b₀ : ℝ, 0 < b₀ → ∀ Cw D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let w : ℕ := ⌈(N : ℝ) * Real.sqrt t * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
      ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
          ∃ Mf : ℝ → ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
            (∀ x ∈ Set.Icc a c,
              IsRotationFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c x (Mf x)) ∧
            ENNReal.ofReal ((N : ℝ) ^ (-D)) <
              ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∫ y, ∑ j : Fin N,
                (if Int.natAbs ((j : ℤ) -
                    ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                  then 0 else 1) * ‖Mf s (c - s).toNNReal y k j‖ ^ 2
                ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- **Short flow, row form, stochastic.** Same quantifiers and scales as
`RelativeLocalizationContract.short_row`; the tail is `E_aux Σ_{|j-k|>R} |M_{s,u}(k,j)|²` of the
short rotation flow (no damping) started at `s`. -/
def ShortRowStochasticStatement : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
              IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) <
                ∫ y, ∑ j : Fin N, ‖M (u - s).toNNReal y k j‖ ^ 2 *
                    (if R < (labelDist k j : ℝ) then 1 else 0)
                  ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- **Short flow, column form, stochastic.** Same quantifiers and scales as
`RelativeLocalizationContract.short_column`; the tail is `E_aux Σ_{|j-k|>R} |M_{s,u}(j,k)|²`. -/
def ShortColumnStochasticStatement : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
              IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) <
                ∫ y, ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) *
                    ‖M (u - s).toNNReal y j k‖ ^ 2
                  ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The relative localization lemma in stochastic form: the three fields. -/
def RelativeLocalizationStochasticStatement : Prop :=
  ReferenceFiniteSpeedStochasticStatement ∧ ShortRowStochasticStatement ∧
    ShortColumnStochasticStatement

end BlockBand.Palm.RelativeLocalization.StochasticBridge
