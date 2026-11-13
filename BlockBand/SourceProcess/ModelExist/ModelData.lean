module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.SourceProcess.SourceProcessLaw.Entrance

/-!
# The data of the finite source model on the driver space

The initial randomness is `S = (ℕ → ℝ) × (Fin p × Fin M → ℝ)` with law
`μ = ρ ⊗ Π_{a,k} birthTimeLaw(q_a)`; the sample space is the driver space over `S`.
* `isProbabilityMeasure_birthTimeLaw`: the location law of a source test is a probability;
* `birthTimeLaw_Iic`: if the test has positive mass, a location `≤ s` has probability `0`;
* `measurable_fst_driver`, `map_fst_driverLaw`: the initial data are `𝓖₀`-measurable with law `μ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open scoped ENNReal NNReal

theorem integrableOn_sourceTest {s T : ℝ} {q : ℝ → ℝ} (hq : IsSourceTest s T q) :
    IntegrableOn q (Icc s T) := hq.2.2.integrableOn_compact isCompact_Icc

theorem sourceMass_nonneg {s T : ℝ} {q : ℝ → ℝ} (hq : IsSourceTest s T q) :
    0 ≤ sourceMass s T q :=
  setIntegral_nonneg measurableSet_Icc fun x _ => hq.1 x

theorem isProbabilityMeasure_birthTimeLaw {s T : ℝ} {q : ℝ → ℝ} (hq : IsSourceTest s T q) :
    IsProbabilityMeasure (birthTimeLaw s T q) := by
  unfold birthTimeLaw
  split_ifs with hm
  · refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have hint : IntegrableOn (fun x => q x / sourceMass s T q) (Icc s T) :=
      (integrableOn_sourceTest hq).div_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => div_nonneg (hq.1 x) hm.le), integral_div]
    rw [show ∫ x in Icc s T, q x = sourceMass s T q from rfl, div_self hm.ne', ENNReal.ofReal_one]
  · exact Measure.dirac.isProbabilityMeasure

theorem birthTimeLaw_Iic {s T : ℝ} {q : ℝ → ℝ} (hm : 0 < sourceMass s T q) :
    birthTimeLaw s T q (Iic s) = 0 := by
  unfold birthTimeLaw
  rw [ite_eq_left hm]
  refine withDensity_absolutelyContinuous _ _ ?_
  rw [Measure.restrict_apply measurableSet_Iic]
  refine measure_mono_null (fun x hx => ?_) (Real.volume_singleton (a := s))
  exact le_antisymm hx.1 hx.2.1

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

theorem measurable_fst_driver (μ : Measure S) [IsProbabilityMeasure μ] :
    Measurable[driverAugmented (κ := κ) μ 0] (fun x : DriverSample S κ => x.1) := by
  refine Measurable.mono ?_ (le_augmentedFiltration _ _ 0) le_rfl
  show Measurable[MeasurableSpace.comap (fun x : S × (κ → CanonicalWienerPath) =>
    (x.1, commonWienerPast 0 x.2)) inferInstance] _
  exact (comap_measurable (fun x : S × (κ → CanonicalWienerPath) =>
    (x.1, commonWienerPast 0 x.2))).fst

theorem map_fst_driverLaw (μ : Measure S) [IsProbabilityMeasure μ] :
    (driverLaw (κ := κ) μ).map (fun x : DriverSample S κ => x.1) = μ := by
  rw [driverLaw, Measure.map_fst_prod, measure_univ, one_smul]

end BlockBand.SourceProcess.ModelExist
