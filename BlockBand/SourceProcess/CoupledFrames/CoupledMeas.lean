module

public import BlockBand.SourceProcess.CoupledFrames.CoupledSetup

/-!
# Measurability of the shared births

* `isStronglyProgressive_jGram`: the joint Gram process is progressive.
* `measurable_jvec`: `jvec m` is `𝓕_{θ_m}`-measurable (`measurable_probeV`).
* `stronglyMeasurable_pv1`, `stronglyMeasurable_pv2`: `pv_j i` is `𝓕_{θ_i}`-measurable.
* `stronglyMeasurable_wv`: `wv k` is `𝓕_{τ_k}`-measurable (stopped value of `Y₁`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.Stochastic.SourceSDE

theorem continuous_fromCols' {ι c₁ c₂ : Type*} :
    Continuous fun p : Matrix ι c₁ ℂ × Matrix ι c₂ ℂ => fromCols p.1 p.2 := by
  refine continuous_pi fun i => continuous_pi fun z => ?_
  rcases z with y | y
  · exact continuous_fst.matrix_elem i y
  · exact continuous_snd.matrix_elem i y

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {K R : ℕ} {π : Type*} {n : ℕ} (eπ : π ≃ Fin n)
  {S : Type*} [MeasurableSpace S] {μ : Measure S}
  {Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
  {σ' : π → DriverSample S (SourceNoise (Amb K R)) → ℝ} (v : π → ℝ)

theorem isStronglyProgressive_jGram
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂) :
    IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) (jGram Y₁ Y₂) :=
  fun T => (continuous_gramPair _).comp_stronglyMeasurable
    (continuous_fromCols'.comp_stronglyMeasurable ((h₁ T).prodMk (h₂ T)))

theorem measurable_jvec
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂)
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i)) (m : Fin n) :
    Measurable[(isStoppingTime_of_meas0 (hσ (eπ.symm m)).real_toNNReal).measurableSpace]
      (jvec eπ Y₁ Y₂ σ' v m) :=
  measurable_probeV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mvf eπ v)
    (fun m => (hσ (eπ.symm m)).real_toNNReal) (measurable_jointSel _)
    (isStronglyProgressive_jGram h₁ h₂) m

theorem stronglyMeasurable_jvec_pi
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂)
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i)) (i : π) :
    StronglyMeasurable[(isStoppingTime_of_meas0 (hσ i).real_toNNReal).measurableSpace]
      (jvec eπ Y₁ Y₂ σ' v (eπ i)) := by
  have h := measurable_jvec eπ v h₁ h₂ hσ (eπ i)
  have e : (fun x => (((σ' (eπ.symm (eπ i)) x).toNNReal : ℝ≥0) : WithTop ℝ≥0)) =
      fun x => (((σ' i x).toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
    funext x; simp only [Equiv.symm_apply_apply]
  rw [measurableSpace_congr e _ (isStoppingTime_of_meas0 (hσ i).real_toNNReal)] at h
  exact h.stronglyMeasurable

theorem stronglyMeasurable_pv1
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂)
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i)) (i : π) :
    StronglyMeasurable[(isStoppingTime_of_meas0 (hσ i).real_toNNReal).measurableSpace]
      (pv1 eπ Y₁ Y₂ σ' v i) :=
  (continuous_pi fun y => continuous_apply (Sum.inl y)).comp_stronglyMeasurable
    (stronglyMeasurable_jvec_pi eπ v h₁ h₂ hσ i)

theorem stronglyMeasurable_pv2
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂)
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i)) (i : π) :
    StronglyMeasurable[(isStoppingTime_of_meas0 (hσ i).real_toNNReal).measurableSpace]
      (pv2 eπ Y₁ Y₂ σ' v i) :=
  (continuous_pi fun y => continuous_apply (Sum.inr y)).comp_stronglyMeasurable
    (stronglyMeasurable_jvec_pi eπ v h₁ h₂ hσ i)

theorem stronglyMeasurable_wv
    (h₁ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₁)
    (h₂ : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ) Y₂)
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i)) (k : Fin n) :
    StronglyMeasurable[(isStoppingTime_of_meas0 (hσ (eπ.symm k)).real_toNNReal).measurableSpace]
      (wv eπ Y₁ Y₂ σ' v k) := by
  have : SecondCountableTopology (Matrix (Amb K R) (ExtCol K R) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Amb K R → ExtCol K R → ℂ))
  have hY := (measurable_stoppedValue h₁
    (isStoppingTime_of_meas0 (hσ (eπ.symm k)).real_toNNReal)).stronglyMeasurable
  have hj := (continuous_pi fun y => continuous_apply (Sum.inl y)).comp_stronglyMeasurable
    (measurable_jvec eπ v h₁ h₂ hσ k).stronglyMeasurable
  exact (continuous_fst.matrix_mulVec continuous_snd).comp_stronglyMeasurable (hY.prodMk hj)

end BlockBand.SourceProcess.CoupledFrames
