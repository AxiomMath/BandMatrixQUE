module

public import BlockBand.SourceProcess.PhysApprox.B3Pins

/-!
# The Lindeberg clause and the maximal `𝒦` moment

* `ComplexClosedLindeberg` (with its Gram and `𝒦` halves) and the maximal stopped `𝒦` moment
  `ComplexKStoppedMomentMax`, which implies the per-length `ComplexKStoppedMoment`.
* `TargetCapCond'`: the limit passage with the Lindeberg clause added and the stopped `𝒦` moment
  in its maximal form. It follows from `TargetCapCond` (`targetCapCond'_of`), so it is no
  stronger.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum
open scoped NNReal ENNReal

/-!
## The Lindeberg clause
-/

/-- Summed fourth moments of the increments of coordinate `c`, on the alive set, away from births. -/
def b3LindebergErr (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np) : ℝ≥0∞ :=
  ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
    ∫⁻ y, (b3Alive b E s h τ m R W j Vs).indicator
      (fun y => ‖b3dX b E s h τ m W j Vs c y‖ₑ ^ 4) y ∂closedLaw b W np

/-- **`ComplexClosedLindeberg`**: for every admissible time-`s` frame, trace level `R` and
coordinate `c`, the summed fourth moments of the closed increments on the alive set, away from the
births, tend to `0`. -/
def ComplexClosedLindeberg : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (c : CIdx K np),
      Tendsto (fun W => b3LindebergErr b E s T h τ m R W (Vs W) c) atTop (𝓝 0)

/-- **Gram half of `ComplexClosedLindeberg`**: the coordinates `c = Sum.inl e`. -/
def ComplexGramLindeberg : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ (R : ℝ) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
      Tendsto (fun W => b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inl e : CIdx K np)) atTop
        (𝓝 0)

/-- **`𝒦` half of `ComplexClosedLindeberg`**: the coordinates `c = Sum.inr ij`. -/
def ComplexKLindeberg : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (R : ℝ) (ij : Fin np × Fin np),
      Tendsto (fun W => b3LindebergErr b E s T h τ m R W (Vs W) (Sum.inr ij : CIdx K np)) atTop
        (𝓝 0)

/-- **The two halves give `ComplexClosedLindeberg`.** -/
theorem complexClosedLindeberg_of_parts (hG : ComplexGramLindeberg) (hK : ComplexKLindeberg) :
    ComplexClosedLindeberg := by
  intro b E np τ m T s h K Vs hD R c
  rcases c with e | ij
  · exact hG b E np τ m T s h K Vs hD R e
  · exact hK b E np τ m T s h K Vs hD R ij

/-!
## The maximal stopped `𝒦` moment
-/

/-- **`ComplexKStoppedMomentMax`: the stop for `𝒦`, maximal form** (Minkowski for the summed
means and Burkholder for the centered increments): uniformly in `W`, the fourth moment of the
supremum over the alive lengths `j` of the closed `𝒦` one step later. It bounds the stopped `𝒦`
at the exit of the Gram trace stop, which the per-`j` form `ComplexKStoppedMoment` does not.
-/
def ComplexKStoppedMomentMax : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop, ∀ ij : Fin np × Fin np,
      ∫⁻ y, ⨆ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
          (b3Alive b E s h τ m R W j (Vs W)).indicator
            (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y
        ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **The maximal form implies the per-length form `ComplexKStoppedMoment`.** -/
theorem complexKStoppedMoment_of_max (hM : ComplexKStoppedMomentMax) : ComplexKStoppedMoment := by
  intro b E np τ m T s h K Vs hD R
  obtain ⟨C, hC⟩ := hM b E np τ m T s h K Vs hD R
  refine ⟨C, hC.mono fun W hW j hj1 hj2 ij => le_trans (lintegral_mono fun y => ?_) (hW ij)⟩
  exact le_iSup₂ (f := fun j (_ : j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊) =>
    (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) j
    (Finset.mem_Ico.2 ⟨hj1, hj2⟩)

/-!
## The revised limit passage
-/

/-- **The limit passage, revised**: `TargetCapCond` with the Lindeberg clause
`ComplexClosedLindeberg` added and the stopped `𝒦` moment in its maximal form
`ComplexKStoppedMomentMax`.
-/
def TargetCapCond' : Prop :=
  TransmissionLawContract → ExistsTimeSFrame → ComplexClosedSummed → ComplexClosedTight →
    ComplexKStoppedMomentMax → ComplexClosedCurrent → ComplexClosedLindeberg →
    ComplexCapCondLimit

/-- `TargetCapCond'` has more hypotheses than `TargetCapCond`, so it is implied by it. -/
theorem targetCapCond'_of (h : TargetCapCond) : TargetCapCond' :=
  fun hTL hEx hS hT hK hC _ => h hTL hEx hS hT (complexKStoppedMoment_of_max hK) hC

end BlockBand.SourceProcess.PhysApprox.B3
