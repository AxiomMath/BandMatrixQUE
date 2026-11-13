module

public import BlockBand.SourceProcess.ModelExist.ModelData

/-!
# Laws of the entrance and of the sampled locations on the driver space

On the driver space, the transmission sequence and the sampled birth locations have the prescribed
laws, are independent, and the sequence is almost surely a transmission sequence.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.SourceProcessLaw
open scoped ENNReal NNReal

variable {π κ : Type*} [Fintype π] [Fintype κ] {ρ : Measure (ℕ → ℝ)} [IsProbabilityMeasure ρ]
  {ν : Measure (π → ℝ)} [IsProbabilityMeasure ν]

omit [Fintype π] [Fintype κ] in
theorem measurable_tseq' :
    Measurable (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.1) :=
  measurable_fst.comp measurable_fst

omit [Fintype π] [Fintype κ] in
theorem measurable_τ' :
    Measurable (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.2) :=
  measurable_snd.comp measurable_fst

theorem map_tseq :
    (driverLaw (κ := κ) (ρ.prod ν)).map (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.1) =
      ρ := by
  have h : (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.1) =
      Prod.fst ∘ fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1 := rfl
  rw [h, ← Measure.map_map measurable_fst measurable_fst, map_fst_driverLaw,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem map_τ :
    (driverLaw (κ := κ) (ρ.prod ν)).map (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.2) =
      ν := by
  have h : (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.2) =
      Prod.snd ∘ fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1 := rfl
  rw [h, ← Measure.map_map measurable_snd measurable_fst, map_fst_driverLaw,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem indep_tseq_τ :
    IndepFun (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.1)
      (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => x.1.2) (driverLaw (κ := κ) (ρ.prod ν)) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_tseq'.aemeasurable
    measurable_τ'.aemeasurable, map_tseq, map_τ]
  exact map_fst_driverLaw _

theorem map_seqTrace :
    (driverLaw (κ := κ) (ρ.prod ν)).map
        (fun x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ => seqTraceMeasure x.1.1) =
      ρ.map seqTraceMeasure := by
  conv_rhs => rw [← map_tseq (ρ := ρ) (κ := κ) (ν := ν)]
  rw [Measure.map_map measurable_seqTraceMeasure measurable_tseq']
  rfl

theorem ae_seq (hρ : ∀ᵐ t ∂ρ, IsTransmissionSequence t) :
    ∀ᵐ x ∂driverLaw (κ := κ) (ρ.prod ν),
      IsTransmissionSequence (x : DriverSample ((ℕ → ℝ) × (π → ℝ)) κ).1.1 := by
  refine ae_of_ae_map measurable_tseq'.aemeasurable ?_
  rw [map_tseq]
  exact hρ

end BlockBand.SourceProcess.ModelExist
