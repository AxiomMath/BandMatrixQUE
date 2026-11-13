module

public import BlockBand.QUE.Fourier.PhysicalFiniteTest
public import BlockBand.Statements

/-!
# Statements for prescribed-rank QUE

Definitions only: law-preserving extensions of the physical law carrying a real `L²` center,
and the statements of the physical center bound and of the physical angular bound for the
nonzero Fourier modes, at every bulk rank and adjacent pair of blocks.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.QUE

open MeasureTheory BlockBand.Model.Construction BlockBand.QUE.Fourier
open scoped ENNReal NNReal

/-- An enlarged probability space carrying exactly the physical law, as in the
simultaneous splitting of the paper. It carries no estimate. -/
structure PairExtension (p : Parameters) (model : p.GaussianRingModel) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  Hm : Ω → p.SiteMatrix
  measurable_Hm : Measurable Hm
  map_eq : P.map Hm = (model.law : Measure p.SiteMatrix)

attribute [instance] PairExtension.mΩ

/-- The trivial extension `(SiteMatrix, law, id)`. -/
def PairExtension.ofLaw (p : Parameters) (model : p.GaussianRingModel) :
    PairExtension p model where
  Ω := p.SiteMatrix
  P := (model.law : Measure p.SiteMatrix)
  Hm := id
  measurable_Hm := measurable_id
  map_eq := Measure.map_id

/-- The exact pair law, lifted to an extension. -/
def extendedPairMeasure (p : Parameters) (α : Fin p.N) (i : ZMod p.n) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (Hm : Ω → p.SiteMatrix) : Measure Ω :=
  P.withDensity (fun ω => (physicalPairWeight p α i (Hm ω) : ℝ≥0∞))

/-- The physical angular bound at `φ = conj A_m` for every nonzero mode `m`, against a
given center, with constant `A / W`. -/
def AngularModeComparison (p : Parameters) (α : Fin p.N) (i : ZMod p.n) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (Hm : Ω → p.SiteMatrix) (center : Ω → ℝ)
    (A : ℝ) : Prop :=
  ∀ m : ZMod p.n, m ≠ 0 →
    ‖∫ ω, ((physicalPairContrast p α i (Hm ω) - center ω : ℝ) : ℂ) *
        starRingEnd ℂ (physicalMode p α m (Hm ω)) ∂extendedPairMeasure p α i P Hm‖ ≤
      A / (p.W : ℝ)

/-- One law-preserving extension and one measurable real L² center for a
deterministic parameter set, model, rank and adjacent pair `S = {i, i+1}`. -/
structure PairCenterWitness (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (i : ZMod p.n) where
  X : PairExtension p model
  center : X.Ω → ℝ
  aesm : AEStronglyMeasurable center (extendedPairMeasure p α i X.P X.Hm)
  sq_integrable : Integrable (fun ω => center ω ^ 2) (extendedPairMeasure p α i X.P X.Hm)

/-- A center witness for every parameter set, model, rank and pair, shared by the
center and angular contracts. -/
abbrev PairCenterFamily : Type 1 :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n),
    PairCenterWitness p model α i

/-- The physical center bound: under the exact pair law, at every bulk rank and every adjacent
pair, `E♯ j² ≤ B/(√n W^(3/2))`, with `B` and the width threshold chosen from `(b, θ, T)` before
`n, W`, the model, rank and pair. -/
def PhysicalCenterContract (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) : Prop :=
  ∃ B W₀ : ℝ, 0 ≤ B ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) → W₀ < (W : ℝ) →
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α → ∀ i : ZMod p.n,
        (∫ ω, (w p model α i).center ω ^ 2 ∂extendedPairMeasure p α i
            (w p model α i).X.P (w p model α i).X.Hm) ≤
          B / (Real.sqrt (p.n : ℝ) * ((p.W : ℝ) * Real.sqrt (p.W : ℝ)))

/-- The physical angular bound at `φ = conj A_m` (`M = 1`, `L_φ = 2`) for all `m ≠ 0`, at every
bulk rank and adjacent pair, with the same center family, `A` chosen from `(b, θ, T)` first. -/
def PhysicalAngularModeContract (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (w : PairCenterFamily) : Prop :=
  ∃ A W₀ : ℝ, 0 ≤ A ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W), (n : ℝ) ≤ T * (W : ℝ) → W₀ < (W : ℝ) →
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p θ α → ∀ i : ZMod p.n,
        AngularModeComparison p α i (w p model α i).X.P (w p model α i).X.Hm
          (w p model α i).center A

end BlockBand.Internal.Contracts.QUE
