module

public import BlockBand.SourceProcess.FullSourceStops.PolyEval
public import BlockBand.SourceProcess.ContractingWords.Alive

/-!
# Trace polynomials at length `i` are past observables

The value of a trace polynomial at length `i ≤ j` depends only on the path up to `i`, and is
`growthSigma W j`-measurable (`measurable_polyValue_past`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.FullSourceStops

variable {W nT nI : ℕ}

theorem polyValue_congr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (i : ℕ)
    {ω ω' : GrowthPath W} (h : pathAt W i ω = pathAt W i ω') (Ψ : TracePoly nT nI) :
    polyValue b E k q W i ω Ψ = polyValue b E k q W i ω' Ψ := by
  have hL : ∀ ℓ : TraceLetter nT nI, letterMatrix b E k q W i ω ℓ =
      letterMatrix b E k q W i ω' ℓ := by
    intro ℓ
    cases ℓ <;> simp only [letterMatrix, pathCurrent, scatteringMatrix, boundaryResolvent,
      fullInverse, fullPathMatrix, tagResponse, boundaryToInterior, intervalSource, h]
  have hS : ∀ s : Separator, separatorMatrix b E W i ω s = separatorMatrix b E W i ω' s := by
    intro s
    cases s <;> simp only [separatorMatrix, scatteringMatrix, boundaryResolvent, fullInverse,
      fullPathMatrix, h]
  have hw : wordValue b E k q W i ω = wordValue b E k q W i ω' := by
    funext w; simp only [wordValue, hL, hS]
  simp only [polyValue, hw]

/-- **Adaptedness**: `polyValue` at length `i ≤ j` is `growthSigma W j`-measurable. -/
theorem measurable_polyValue_past (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    {i j : ℕ} (h : i ≤ j) (Ψ : TracePoly nT nI) :
    Measurable[growthSigma W j] fun ω : GrowthPath W => polyValue b E k q W i ω Ψ := by
  have e : (fun ω : GrowthPath W => polyValue b E k q W i ω Ψ) =
      (fun ω => polyValue b E k q W i ω Ψ) ∘ extPast W j ∘ pastCoords W j := by
    funext ω
    exact (polyValue_congr b E k q i (ContractingWords.pathAt_extPast_le h ω) Ψ).symm
  rw [e]
  exact ((measurable_polyValue b E k q i Ψ).comp (measurable_extPast j)).comp
    (comap_measurable (pastCoords W j))

end BlockBand.SourceProcess.FullSourceGenerator
