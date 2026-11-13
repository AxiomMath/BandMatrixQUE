module

public import BlockBand.SourceProcess.LengthCont.Doob
public import BlockBand.SourceProcess.LengthCont.Filtration

/-!
# The hypothesis `LayerIncrementBounds`: one-layer drift and fluctuation of the source data

Each real coordinate of each entry of the source data `(𝒦, M_pr, B_pr, J_pr)` at length `n` is a
process `n ↦ sourceCoord … n`, adapted to the length filtration `probedSigma` (blocks `< n`,
bonds `≤ n`, all tags). The hypothesis states: near the final length `TW` (window `|n - TW| ≤ δW`),
for `W ≥ W₀`, the one-layer increment is in `L²`, its predictable part
`E[X_{n+1} - X_n | 𝓕_n]` has `L¹` norm `≤ C/W`, and its martingale difference has second
moment `≤ C/W`. These are the integrated forms of the one-layer bounds of the exact complex source update
(mean `C(δ₀ + W⁻²) Tr M_pr`, centered `L^p` size `C_p Tr M_pr / √W`, with
`‖δ₀‖_p ≤ C_p/W` and fixed source moments). It is proved from the input hypotheses as
`OneLayer.layerIncrementBounds_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.LengthCont

open MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw

/-- The real (`s = true`) or imaginary (`s = false`) part of the entry `(i, k)` of component
`r` of the source data at length `n`, as a process in `n`. -/
def sourceCoord (b E : ℝ) {np : ℕ} (W : ℕ) (τ m : Fin np → ℝ) (r : Fin 4) (i k : Fin np)
    (s : Bool) (n : ℕ) (x : ProbedPath W np) : ℝ :=
  if s then (complexSourceData b E W n τ m x r i k).re
  else (complexSourceData b E W n τ m x r i k).im

theorem measurable_sourceCoord_sigma (b E : ℝ) {np : ℕ} (W : ℕ) (τ m : Fin np → ℝ)
    (r : Fin 4) (i k : Fin np) (s : Bool) (n : ℕ) :
    Measurable[probedSigma W np n] (sourceCoord b E W τ m r i k s n) := by
  have h := measurable_complexSourceData_sigma b E W n τ m
  have he : Measurable[probedSigma W np n]
      fun x => complexSourceData b E W n τ m x r i k :=
    Measurable.comp (g := fun y : SourceData np => y r i k)
      (measurable_pi_apply r).eval_matrix h
  unfold sourceCoord
  cases s
  · exact Complex.measurable_im.comp he
  · exact Complex.measurable_re.comp he

theorem stronglyMeasurable_sourceCoord_sigma (b E : ℝ) {np : ℕ} (W : ℕ) (τ m : Fin np → ℝ)
    (r : Fin 4) (i k : Fin np) (s : Bool) (n : ℕ) :
    StronglyMeasurable[probedSigma W np n] (sourceCoord b E W τ m r i k s n) :=
  (measurable_sourceCoord_sigma b E W τ m r i k s n).stronglyMeasurable

/-- **Layer increment bounds**.
On the domain of `ComplexSourceLawContract.limit`, there is a window `δ > 0` and
constants `C, W₀` such that for `W ≥ W₀`, every length `n` with `(T - δ)W ≤ n ≤ (T + δ)W` and
every real coordinate of every entry of the source data: the one-layer increment
`X_{n+1} - X_n` is in `L²(probedPathLaw)`, its predictable part `E[X_{n+1} - X_n | 𝓕_n]`
(`𝓕_n = probedSigma W np n`) has `L¹` norm at most `C/W`, and its martingale difference has
second moment at most `C/W`. -/
def LayerIncrementBounds : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
    ∃ δ : ℝ, 0 < δ ∧ ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ n : ℕ,
      (T - δ) * W ≤ n → (n : ℝ) ≤ (T + δ) * W →
      ∀ (r : Fin 4) (i k : Fin np) (s : Bool),
        MemLp (incr (sourceCoord b E W τ m r i k s) n) 2 (probedPathLaw W np b) ∧
        ∫ x, |(probedPathLaw W np b)[incr (sourceCoord b E W τ m r i k s) n |
            probedSigma W np n] x| ∂probedPathLaw W np b ≤ C / W ∧
        ∫ x, mart (probedPathLaw W np b) (probedSigma W np) (sourceCoord b E W τ m r i k s) n x ^ 2
            ∂probedPathLaw W np b ≤ C / W

end BlockBand.SourceProcess.LengthCont
