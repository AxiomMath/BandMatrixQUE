module

public import BlockBand.SourceProcess.ComplexSourceLaw.Interface
public import BlockBand.SourceProcess.FullSourceStops.WordValue
public import BlockBand.Transmission.Bridge.Marginal

/-!
# Measurability of the complex source data; the probed-path law is a probability measure

The probe columns, the complex source matrix `𝒦`, the probe frame and the complex source data are
measurable functions of the probed path, and the circular Gaussian law and the probed-path law
are probability measures.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops

theorem measurable_probeColumns (W n : ℕ) {np : ℕ} (τ m : Fin np → ℝ) :
    Measurable fun g : Fin np → Fin W → ℂ => probeColumns W n τ m g := by
  refine Measurable.of_eval_matrix _ fun x j => ?_
  simp only [probeColumns]
  split_ifs
  · exact measurable_const.mul ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · exact measurable_const

theorem measurable_complexSourceK (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) :
    Measurable (complexSourceK b E W n τ m) := by
  have hJ : Measurable fun x : ProbedPath W np => probeColumns W n τ m x.2 :=
    (measurable_probeColumns W n τ m).comp measurable_snd
  have hG : Measurable fun x : ProbedPath W np => (fullInverse b E W n x.1).toBlocks₁₁ :=
    Measurable.of_eval_matrix _ fun _ _ =>
      ((measurable_fullInverse b E n).comp measurable_fst).eval_matrix
  exact measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hJ) hG) hJ

theorem measurable_probeFrame (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) :
    Measurable (probeFrame b E W n τ m) := by
  have hJ : Measurable fun x : ProbedPath W np => probeColumns W n τ m x.2 :=
    (measurable_probeColumns W n τ m).comp measurable_snd
  have hU : Measurable fun x : ProbedPath W np => boundaryToInterior b E W n x.1 :=
    Measurable.of_eval_matrix _ fun _ _ =>
      ((measurable_fullInverse b E n).comp measurable_fst).eval_matrix
  exact measurable_matrix_mul' (measurable_matrix_conjTranspose' hU) hJ

theorem measurable_complexSourceData (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) :
    Measurable (complexSourceData b E W n τ m) := by
  have hV := measurable_probeFrame b E W n τ m
  have hVs := measurable_matrix_conjTranspose' hV
  have hC : Measurable fun x : ProbedPath W np => pathCurrent b E W n x.1 :=
    (measurable_pathCurrent b E n).comp measurable_fst
  refine Measurable.of_eval fun r => ?_
  fin_cases r
  · exact measurable_complexSourceK b E W n τ m
  · exact measurable_matrix_mul' hVs hV
  · exact measurable_matrix_mul' (measurable_matrix_mul' hVs measurable_const) hV
  · exact measurable_matrix_mul' (measurable_matrix_mul' hVs hC) hV

theorem measurable_circularMap (ι : Type*) [Fintype ι] :
    Measurable fun (r : ι × Fin 2 → ℝ) =>
      fun a : ι => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I :=
  Measurable.of_eval fun _ => (Complex.measurable_ofReal.comp (measurable_pi_apply _)).add
    ((Complex.measurable_ofReal.comp (measurable_pi_apply _)).mul measurable_const)

instance isProbabilityMeasure_circularVectorLaw (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw ι) := by
  unfold BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw
  infer_instance

instance isProbabilityMeasure_probedPathLaw (W np : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedPathLaw W np b) := by
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W)) := by infer_instance
  have : IsProbabilityMeasure (growthPathLaw W b) := isProbabilityMeasure_growthPathLaw W b
  unfold probedPathLaw; infer_instance

end BlockBand.SourceProcess.ComplexSourceLaw
