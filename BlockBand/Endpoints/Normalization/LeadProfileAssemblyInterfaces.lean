module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyWindow
public import BlockBand.Internal.Contracts.ClocksLeadProfile

/-!
# The physical lead-profile theorem: the two analytic statements of the assembly

This file defines the objects and states the two analytic statements used in the assembly of the
physical lead-profile theorem.

## Objects
* `leadAngularAverage p U Φ ω e = Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[Ψ(p(v,e))] / Z₀(e)`: the concrete normalized
  one-block (block `0`) angular average of `Ψ(q) = n⁻¹ Σ_s Φ(ℛ_{s/n} ν(q))` (the function `A` of
  `physicalOneMark_window_comparison`).
* `gaussianLeadSide p Φ e`: the expectation under `path ⊗ layer ⊗ g` (`growthPathLaw W b`,
  `layerLaw W b .common`, `g ~ CN(0, I_W)` on the common port) of `n⁻¹ Σ_{J<n} Φ(ℛ_J ν)` where `ν`
  is the profile of the Gaussian field `ULg` on the `n - 1` lead positions, block `0` removed and
  renormalized. It is written with `Clocks.leadProfile` at the probe `h = Lg = commonPortProbe`
  (`L = commonPortL` at the old self-energy `X = leadSchur e W (n-3)`), since `leadPositionMass`
  at `h = Lg` is `‖P_x ULg‖²`. The factor `√c` of the field (`LeadFieldIdentificationContract`)
  cancels on normalization.
* `leadLeadSide p Φ e = E_{path, h} n⁻¹ Σ_{J<n} Φ(leadProfile … e … J)`, `h ~ CN(0, I_{2W})`: the
  integrand of `Clocks.leadOneMark` (`leadOneMark_eq`, by `rfl`).

## Statements
* `LeadGaussianStep` (Gaussian ratios on the block regular event, covariance change, field
  identification, removal of block `0`). Window-integrated form, along every critical sequence
  (the removal of block `0` is controlled only after the spectral weighting, via
  `VanishingBlockAtom`, so no pointwise-in-`e` statement is claimed):
  `∫ A(e(u), ω) w(u) du dPω - ∫ w(u) gaussianLeadSide(e(u)) du → 0`, for every window `w`
  (`IsWindow`), `Φ ∈ C_b(𝒫(𝕋))`, every sequence of realizations, one-block splitting laws of block
  `0` and measurable block frames.
* `LeadCommonPortStep` (the common-port ratios theorem conditionally on the path, matched traces).
  Uniform in the energy: `b`, the bulk range `bulkInterval κ`, `0 < τ₀ ≤ T` and `Φ` fixed first;
  for every `ε > 0` there is `W₀`; for `W ≥ W₀`, `τ₀ W ≤ n ≤ T W` and every `e ∈ bulkInterval κ`,
  `|gaussianLeadSide p Φ e - leadLeadSide p Φ e| ≤ ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped BoundedContinuousFunction

/-- The concrete normalized one-block angular average `A(e, ω)` (block `0`). -/
def leadAngularAverage (p : Parameters)
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (Φ : MassProfile →ᵇ ℝ) (ω : BlockState p 0) (e : ℝ) : ℝ :=
  (∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p 0 U ω e ℓ (leadReconObservable p Φ 0 ω e)) /
    (blockNormalizer p 0 U ω e).toReal

/-- The law of `path ⊗ layer ⊗ g`. -/
def leadGaussianLaw (p : Parameters) :
    Measure ((GrowthPath p.W × LayerSample p.W .common) × (Fin 1 × Fin p.W → ℂ)) :=
  ((growthPathLaw p.W p.b).prod (layerLaw p.W p.b .common)).prod
    (circularVectorLaw (Fin 1 × Fin p.W))

/-- The Gaussian side: `E n⁻¹ Σ_J Φ(ℛ_J ν(ULg))`, block `0` removed and renormalized. -/
def gaussianLeadSide (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) : ℝ :=
  ∫ y, (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n,
      Φ (leadProfile p.b e p.n p.W y.1.1
        (commonPortProbe p.b e (leadSchur e p.W (p.n - 3) y.1.1) (y.1.2, y.2)) J)
    ∂leadGaussianLaw p

/-- The matched-lead side `E_{path,h} n⁻¹ Σ_J Φ(leadProfile … e … J)`. -/
def leadLeadSide (p : Parameters) (Φ : MassProfile →ᵇ ℝ) (e : ℝ) : ℝ :=
  ∫ x, (p.n : ℝ)⁻¹ * ∑ J ∈ Finset.range p.n, Φ (leadProfile p.b e p.n p.W x.1 x.2 J)
    ∂((growthPathLaw p.W p.b).prod (circularVectorLaw (Fin 2 × Fin p.W)))

theorem leadOneMark_eq (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (Φ : MassProfile →ᵇ ℝ) :
    leadOneMark p E w Φ = ∫ u, w u * leadLeadSide p Φ (microEnergy p E u) := rfl

/-- **Steps 2–4 of the physical lead-profile theorem**: window-integrated, along every critical
sequence (proved as `leadGaussianStep_of` from further hypotheses).
-/
def LeadGaussianStep : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, IsWindow w → ∀ Φ : MassProfile →ᵇ ℝ,
    ∀ (τ : ℝ), 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
      (Pω : ∀ j, Measure (BlockState (s.parameters b hb hb' j) 0)),
      (∀ j, IsBlockSplitting (s.parameters b hb hb' j) 0 (R j).model (Pω j)) →
    ∀ (U : ∀ j, (BlockSite (s.parameters b hb hb' j) 0 → ℂ) →
        Matrix (BlockSite (s.parameters b hb hb' j) 0)
          (BlockFrameIndex (s.parameters b hb hb' j)) ℂ),
      (∀ j, IsBlockFrame (s.parameters b hb hb' j) 0 (U j)) →
      Tendsto (fun j =>
          (∫ x, leadAngularAverage (s.parameters b hb hb' j) (U j) Φ x.2
              (microEnergy (s.parameters b hb hb' j) E x.1) ∂priorWindowMeasure (Pω j) w) -
            ∫ u, w u * gaussianLeadSide (s.parameters b hb hb' j) Φ
              (microEnergy (s.parameters b hb hb' j) E u))
        atTop (𝓝 0)

/-- **Step 5 of the physical lead-profile theorem**: uniform in the energy on the bulk range.
-/
def LeadCommonPortStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ τ₀ T : ℝ, 0 < κ → 0 < τ₀ → ∀ Φ : MassProfile →ᵇ ℝ,
    ∀ ε : ℝ, 0 < ε → ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W →
      τ₀ * p.W ≤ (p.n : ℝ) → (p.n : ℝ) ≤ T * p.W → ∀ e ∈ bulkInterval κ,
        |gaussianLeadSide p Φ e - leadLeadSide p Φ e| ≤ ε

end BlockBand.Endpoints.Normalization
