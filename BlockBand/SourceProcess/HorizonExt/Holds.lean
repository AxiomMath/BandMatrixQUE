module

public import BlockBand.SourceProcess.HorizonExt.Solution
public import BlockBand.SourceProcess.HorizonExt.Frame
public import BlockBand.SourceProcess.BornStopped.Main

/-!
# `GramHorizonExtension` holds

Given a horizon solution `G` on `(Ω, 𝓖, Q)`, take the driver space `Ω × (κ → C(ℝ≥0, ℝ))` with
old state `S = Ω`, law `Q ⊗ Wiener^κ` and `κ = SourceNoise (c ⊕ c)`, and the initial frame
`ξ = sqrtFrame (G_r ∘ fst)` with `P0 = diag(1, 0)`. It is `F₀`-measurable (`fst⁻¹ m ≤ F₀`) and
constrained a.s. (`twoProjection_sqrtFrame`, `G_r` feasible a.s.). Well-posedness of the finite
source equation (`SourceSDE.finiteSourceWellPosed_holds`) gives a global solution
`X`, and the ambient bridge makes `Y = gramPair P0 X` an `IsGramMartingaleSolution` for the
augmented driver filtration, with `Y₀ = G_r ∘ fst` a.s. (`gramPair_sqrtFrame`). The glued process
(`isGramMartingaleSolution_glue`) has the laws of `G₀` and `G_r` (`map_glueProc_of_le`).
Consequently `GramHorizonLaw` and `BornStoppedLaw` hold.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.BornStopped
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open scoped NNReal

theorem comap_fst_le_driverAugmented {Ω κ : Type} [m : MeasurableSpace Ω] [Fintype κ]
    (Q : Measure Ω) [IsProbabilityMeasure Q] :
    m.comap Prod.fst ≤ driverAugmented (κ := κ) Q 0 := by
  have h1 : m.comap Prod.fst ≤ commonWienerFiltration Ω κ 0 := by
    show m.comap Prod.fst ≤ MeasurableSpace.comap
      (fun x : Ω × (κ → CanonicalWienerPath) => (x.1, commonWienerPast 0 x.2)) inferInstance
    exact (measurable_fst.comp (comap_measurable
      (fun x : Ω × (κ → CanonicalWienerPath) => (x.1, commonWienerPast 0 x.2)))).comap_le
  exact h1.trans (le_augmentedFiltration (commonWienerFiltration Ω κ) (driverLaw (κ := κ) Q) 0)

/-- **`GramHorizonExtension` holds.** -/
theorem gramHorizonExtension_holds : GramHorizonExtension := by
  intro c _ _ D0 D hD0 hD r Ω m 𝓖 Q G hQ hG
  have hq := (measurePreserving_fst (μ := Q)
    (ν := commonWienerLaw (SourceNoise (c ⊕ c)))).quasiMeasurePreserving
  have hcomap := comap_fst_le_driverAugmented (κ := SourceNoise (c ⊕ c)) Q
  have hGr := SourceProcessLaw.measurable_of_stronglyMeasurable_gram (𝓖.le r) (hG.adapted r)
  set ξ : DriverSample Ω (SourceNoise (c ⊕ c)) → Matrix (c ⊕ c) c ℂ :=
    fun x => sqrtFrame (G r x.1) with hξ
  have hξm : StronglyMeasurable[driverAugmented (κ := SourceNoise (c ⊕ c)) Q 0] ξ := by
    have : BorelSpace (Matrix (c ⊕ c) c ℂ) := inferInstanceAs (BorelSpace ((c ⊕ c) → c → ℂ))
    have : SecondCountableTopology (Matrix (c ⊕ c) c ℂ) :=
      inferInstanceAs (SecondCountableTopology ((c ⊕ c) → c → ℂ))
    have : TopologicalSpace.PseudoMetrizableSpace (Matrix (c ⊕ c) c ℂ) :=
      inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace ((c ⊕ c) → c → ℂ))
    exact (((measurable_sqrtFrame.comp hGr).comp (comap_measurable Prod.fst)).mono hcomap
      le_rfl).stronglyMeasurable
  have hfr : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, GramFeasible D (G r x.1) := by
    filter_upwards [hq.ae hG.feasible] with x hx
    exact hx r le_rfl
  have hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, TwoProjection P0 D (ξ x) := by
    filter_upwards [hfr] with x hx
    exact twoProjection_sqrtFrame hD hx
  obtain ⟨X, hX⟩ := (SourceSDE.finiteSourceWellPosed_holds Q D0 (Fintype.card c) P0 D hD0
    isNearProjection_P0 hD ξ hξm hξc).1
  have hY := GramUniqueness.ambient_isGramMartingaleSolution Q hD0 isNearProjection_P0 hD hξm
    hξc hX
  have h0 : ∀ᵐ x ∂driverLaw (κ := SourceNoise (c ⊕ c)) Q, gramPair P0 (X 0 x) = G r x.1 := by
    filter_upwards [hX.2, hfr] with x h1 h2
    rw [h1, hξ, gramPair_sqrtFrame h2]
  refine ⟨DriverSample Ω (SourceNoise (c ⊕ c)), inferInstance,
    glueFil 𝓖 (driverAugmented (κ := SourceNoise (c ⊕ c)) Q) hcomap r,
    driverLaw (κ := SourceNoise (c ⊕ c)) Q, glueProc r G fun t x => gramPair P0 (X t x),
    inferInstance, isGramMartingaleSolution_glue hcomap hG hY h0,
    map_glueProc_of_le hG.adapted (zero_le : (0 : ℝ≥0) ≤ r), map_glueProc_of_le hG.adapted le_rfl⟩

/-- `GramHorizonLaw` holds (`gramHorizonLaw_of_extension`). -/
theorem gramHorizonLaw_holds : GramHorizonLaw :=
  gramHorizonLaw_of_extension gramHorizonExtension_holds

/-- `BornStoppedLaw` holds (`bornStoppedLaw_of_extension`). -/
theorem bornStoppedLaw_holds : BornUnique.BornStoppedLaw :=
  bornStoppedLaw_of_extension gramHorizonExtension_holds

end BlockBand.SourceProcess.HorizonExt
