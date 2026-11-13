module

public import BlockBand.Transmission.LawDuality.Assembly
public import BlockBand.Transmission.LawDuality.Entrance
public import BlockBand.Transmission.DualBoundary.LawAssembly

/-!
# The transmission law from the refined limit hypotheses

`SubLimitRatioMP` is split into a martingale clause, a mass clause and the entrance, which is
proved from the finite-`W` entrance bound.

* `SubLimitRatioMartingale`: every subsequential limit is a ratio martingale
  (the `F_{x,y}` finite-`W` expansion with summable errors, the generator and the forced
  extension).
* `SubLimitMassBound`: every subsequential limit has `HasLocalMassBound`.
  **`subLimitMassBound_zero`**: its `κ ≡ 0` case from `hTG` (`hasLocalMassBound_zero`).
* **`subLimitRatioMP_of`**: `SubLimitRatioMartingale ∧ SubLimitMassBound ∧
  LawFinite.TransmissionEntranceBulk → SubLimitRatioMP` (entrance: `hasRatioEntrance_of`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal BoundedContinuousFunction

/-- **The martingale clause**: every subsequential limit solves the ratio
martingale problem with `D₀ = transportD0 b E`, `h = 4πρ(E)κ`. -/
def SubLimitRatioMartingale : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E κ φ P μ →
      IsRatioMartingale (transportD0 b E) E κ P μ

/-- **The mass clause**: every subsequential limit has a local mass bound (proved for `κ ≡ 0`
by `subLimitMassBound_zero`, and proved in general from `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient` as `subLimitMassBound_holds`). -/
def SubLimitMassBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E κ φ P μ →
      HasLocalMassBound P μ

/-- **The homogeneous mass clause from the transmission generator theorem.** -/
theorem subLimitMassBound_zero (hTG : TransmissionGeneratorContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E (fun _ => 0) φ P μ →
      HasLocalMassBound P μ :=
  fun _ hb hb2 _ hE1 hE2 _ hφ _ _ _ _ h => hasLocalMassBound_zero hTG hb hb2 hE1 hE2 hφ h

/-- `SubLimitRatioMP` from the martingale clause, the mass clause and the finite-`W` entrance
bound (`hasRatioEntrance_of`). -/
theorem subLimitRatioMP_of (hMart : SubLimitRatioMartingale) (hMass : SubLimitMassBound)
    (hEnt : TransmissionEntranceBulk) : SubLimitRatioMP :=
  fun b hb hb2 E hE1 hE2 κ hκ φ hφ Ω m P μ h =>
    ⟨hMart b hb hb2 E hE1 hE2 κ hκ φ hφ Ω m P μ h,
      hasRatioEntrance_of hEnt hb hb2 hE1 hE2 hκ hφ h,
      hMass b hb hb2 E hE1 hE2 κ hκ φ hφ Ω m P μ h⟩

/-- The `law` field of the transmission law theorem from `TransmissionSubLimitExists`,
`TransmissionTraceModulus`, `SubLimitRatioMartingale`, `SubLimitMassBound`, `TransmissionEntranceBulk`,
`RatioDualityPrinciple`, `SubLimitFddUnique`. -/
theorem law_of_refined (hEx : TransmissionSubLimitExists) (hMod : TransmissionTraceModulus)
    (hMart : SubLimitRatioMartingale) (hMass : SubLimitMassBound)
    (hEnt : TransmissionEntranceBulk) (hPr : RatioDualityPrinciple)
    (hUniq : SubLimitFddUnique) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) :=
  law_of hEx hMod (subLimitRatioMP_of hMart hMass hEnt) hPr hUniq

/-- The `p = 1` interior part of a `law` field. -/
theorem interiorDualLawOne_of_law
    (hlaw : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval),
          IsTransmissionLimit b E κ P μ ∧
          ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
            HasDualDeletionProcess (transportD0 b E) x y ∧
            DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)) :
    DualBoundary.InteriorDualLawOne := by
  intro b hb hb2 E hE1 hE2 κ hκ
  obtain ⟨Ω, m, P, μ, hlim, hl⟩ := hlaw b hb hb2 E hE1 hE2 κ hκ
  exact ⟨Ω, m, P, μ, hlim, fun t ht x y hxy => hl t ht 1 ![x] ![y] hxy⟩

/-- `DualBoundaryStartContract` from the same seven hypotheses (through
`interiorDualLawOne_of_law`). -/
theorem dualBoundaryStart_of_refined (hEx : TransmissionSubLimitExists)
    (hMod : TransmissionTraceModulus) (hMart : SubLimitRatioMartingale)
    (hMass : SubLimitMassBound) (hEnt : TransmissionEntranceBulk) (hPr : RatioDualityPrinciple)
    (hUniq : SubLimitFddUnique) :
    BlockBand.Internal.Contracts.TransmissionUniform.DualBoundaryStartContract :=
  DualBoundary.dualBoundaryStart_of
    (interiorDualLawOne_of_law (law_of_refined hEx hMod hMart hMass hEnt hPr hUniq))

end BlockBand.Transmission.LawDuality
