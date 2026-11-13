module

public import BlockBand.SourceProcess.CoupledFrames.FramePerp
public import BlockBand.SourceProcess.CoupledFrames.GramCongr

/-!
# Each born frame has the law of the finite source model

`frame_model`: for the extended solution `Y` started at `[initialFrame | 1]` (cutoff `h`), probe
vectors with `ProbeSpec` a.s. and shared vectors `w_k = Y(τ_k) a_k` a.s., the Gram process
`gramPair P (bornFrame)` is the finite source model at cutoff `h` (`IsFiniteSourceModel`): it is
a.s. equal to the born Gram process `bornG 𝒢 θ λ` (`bornFrame_eq`, `gramPair_mul`), which is a
born Gram solution (`isBornGramSolution_bornG`, `bornRepresents_probe`) started at `initialGram`
(`bornG_zero_probe`); entrance and birth laws as in `Final`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Stochastic.GramUniqueness

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {p M : ℕ} {S₀ : Type} [MeasurableSpace S₀] {κ : Type} [Fintype κ] (s : ℝ)

/-- The model times `σ_i = τ_i − s` of the sampled locations. -/
def σs : Fin p × Fin M → DriverSample ((ℕ → ℝ) × (Fin p × Fin M → ℝ)) κ → ℝ :=
  fun i x => x.1.2 i - s

theorem measurable_σs (μ : Measure ((ℕ → ℝ) × (Fin p × Fin M → ℝ))) [IsProbabilityMeasure μ]
    (i : Fin p × Fin M) :
    Measurable[driverAugmented (κ := κ) μ 0] (σs (κ := κ) s i) :=
  ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_fst_driver μ))).sub_const s

/-- The born Gram process is progressive when its frame is. -/
theorem stronglyMeasurable_gram_of_prog {K R : ℕ} {π : Type} [Fintype π] [DecidableEq π]
    {μ : Measure S₀} {X : ℝ≥0 → DriverSample S₀ κ → Matrix (Amb K R) (SrcCol K π) ℂ}
    (hX : IsStronglyProgressive (driverAugmented (κ := κ) μ) X) (t : ℝ≥0) :
    StronglyMeasurable[driverAugmented (κ := κ) μ t] (fun x => gramPair (ambP K R) (X t x)) :=
  (continuous_gramPair _).comp_stronglyMeasurable (hX.stronglyAdapted t)

/-- The born frame is progressive. -/
theorem isStronglyProgressive_bornFrame {K R n : ℕ} {π : Type*} [Fintype π] [DecidableEq π]
    (eπ : π ≃ Fin n) {μ : Measure S₀} [IsProbabilityMeasure μ] {D0 : ℝ} {Naux : ℕ}
    {ξY : DriverSample S₀ (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    {Y : ℝ≥0 → DriverSample S₀ (SourceNoise (Amb K R)) → Matrix (Amb K R) (ExtCol K R) ℂ}
    (hY : IsSDESolution μ (sourceDrift D0 Naux (ambP K R))
      (sourceDiffusion D0 (ambP K R) (extSig K R)) ξY Y)
    {σ' : π → DriverSample S₀ (SourceNoise (Amb K R)) → ℝ}
    (hσ : ∀ i, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (σ' i))
    {pv : π → DriverSample S₀ (SourceNoise (Amb K R)) → ExtCol K R → ℂ}
    (hpv : ∀ i, StronglyMeasurable[(isStoppingTime_of_meas0 (hσ i).real_toNNReal).measurableSpace]
      (pv i))
    {w : Fin n → DriverSample S₀ (SourceNoise (Amb K R)) → Amb K R → ℂ}
    (hw : ∀ k, StronglyMeasurable[(isStoppingTime_of_meas0
      (hσ (eπ.symm k)).real_toNNReal).measurableSpace] (w k)) :
    IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ)
      (bornFrame eπ Y σ' pv w) := by
  have hθ0 : ∀ k, Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (bτ eπ σ' k) :=
    fun k => (hσ _).real_toNNReal
  have hτ := fun k => isStoppingTime_of_meas0 (hθ0 k)
  exact (isNativeItoProcess_frameN hY.1 (lcur K R π) hτ (bcol eπ) (a := ba eπ pv)
    (fun k => hpv (eπ.symm k))).progressive.add
    (isStronglyProgressive_frameBirthJump hθ0 hτ (bcol (K := K) eπ) hw)

end BlockBand.SourceProcess.CoupledFrames
