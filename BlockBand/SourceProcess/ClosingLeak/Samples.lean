module

public import BlockBand.SourceProcess.ClosingLeak.Phase

/-!
# The sample average of one leaked mass

Given the path, the sampled injection `ξ_{il} = κ_i u_{il}u_{il}*` (`rankOne`) has mean
`M⁻¹ Q(q_i)` against every linear functional (`isMatSample_rankOne`). For a fixed `K ⪰ 0`
this gives `∫⁻ Re Tr(K ξ_{il}) = Re Tr(K M⁻¹ Q(q_i))` under the joint law of the tag locations
and the Gaussians (`lintegral_sample_leak`), after transporting the product of the two `pi`
laws to the `pi` of the pair laws and projecting on the coordinate `il`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingLeak

open Matrix MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Sampling
open scoped ComplexOrder

variable {W n : ℕ}

/-- **The sample average of one leaked mass** against a fixed `K ⪰ 0`. -/
theorem lintegral_sample_leak (U : Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ) {p M : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (hW : 0 < W) (hM : 0 < M)
    {K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hK : K.PosSemidef) (il : Fin p × Fin M) :
    ∫⁻ z, ENNReal.ofReal ((K * rankOne U (gridMass W n (q il.1) / (M * W))
        (z.1 il, z.2 il)).trace.re)
        ∂((Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
          (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) =
      ENNReal.ofReal ((K * sampleMean U (q il.1) M).trace.re) := by
  have hP : ∀ x : Fin p × Fin M, IsProbabilityMeasure (tagSampleLaw W n (q x.1)) :=
    fun x => isProbabilityMeasure_tagSampleLaw W n (hq x.1)
  have hP2 : ∀ x : Fin p × Fin M, IsProbabilityMeasure (sampleLaw W n (q x.1)) := fun x => by
    infer_instance
  set κ := gridMass W n (q il.1) / (M * W)
  set G : ℕ × (Fin W → ℂ) → ENNReal := fun y => ENNReal.ofReal ((K * rankOne U κ y).trace.re)
  have hG : Measurable G :=
    ENNReal.measurable_ofReal.comp (measurable_trace_re_mul K (measurable_rankOne U κ))
  have hmp := measurePreserving_arrowProdEquivProdArrow ℕ (Fin W → ℂ) (Fin p × Fin M)
    (fun x => tagSampleLaw W n (q x.1)) (fun _ => circularVectorLaw (Fin W))
  have h1 : ∫⁻ z, G (z.1 il, z.2 il)
      ∂((Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
        (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W))) =
      ∫⁻ w, G (w il) ∂Measure.pi (fun x : Fin p × Fin M => sampleLaw W n (q x.1)) := by
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    rfl
  have h2 : ∫⁻ w, G (w il) ∂Measure.pi (fun x : Fin p × Fin M => sampleLaw W n (q x.1)) =
      ∫⁻ y, G y ∂sampleLaw W n (q il.1) :=
    (measurePreserving_eval (fun x : Fin p × Fin M => sampleLaw W n (q x.1)) il).lintegral_comp hG
  have hS := isMatSample_rankOne U (hq il.1) hW hM
  have h3 : ∫⁻ y, G y ∂sampleLaw W n (q il.1) =
      ENNReal.ofReal ((K * sampleMean U (q il.1) M).trace.re) := by
    rw [← hS.lin_eq K]
    exact (ofReal_integral_eq_lintegral_ofReal (hS.lin_int K)
      (ae_of_all _ fun y => re_trace_mul_nonneg hK (hS.psd y))).symm
  exact h1.trans (h2.trans h3)

/-- `M⁻¹ Q(q) = sampleMean`: the conditional mean of one injection. -/
theorem sampleMean_eq (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (M : ℕ) (ω : GrowthPath W) :
    sampleMean (boundaryToInterior b E W n ω) q M =
      (((M : ℝ)⁻¹ : ℝ) : ℂ) • intervalSource b E W n q ω := rfl

end BlockBand.SourceProcess.ClosingLeak
