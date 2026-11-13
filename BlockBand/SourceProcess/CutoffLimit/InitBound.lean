module

public import BlockBand.SourceProcess.CutoffLimit.Bounds
public import BlockBand.SourceProcess.CutoffLimit.InitFrame
public import BlockBand.SourceProcess.SourceProcessLaw.Entrance

/-!
# Initial moments of a cutoff coupling through the entrance law

With the entrance `ent` of the
coupled models (law of `seqTraceMeasure ∘ tseq`):

* `initTrace_le`: `E R₀ ≤ 8 E_ent ∫ψ_{1/2} dν` (uniform in `K`, `h₁`, `h₂`);
* `initDist_le` (`0 ≤ h₁ ≤ h₂`): `E X₀ ≤ 4 E_ent ∫ψ_{1/2} 1_{y ≤ h₂²} dν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

variable {b E s T : ℝ} {p : ℕ} {q : Fin p → ℝ → ℝ} {h₁ h₂ : ℝ} {K M : ℕ}
  {ent : Measure (Measure unitInterval)} {ι S : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {Naux : ℕ} {P : Matrix ι ι ℂ}
  {Emb : Matrix ι (Fin K × Fin 2) ℂ}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι)))}
  {tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ}
  {σb : DriverSample S (SourceNoise ι) → Fin p × Fin M → ℝ} {nb : ℕ}
  {τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → SrcCol K (Fin p × Fin M)}
  {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
  {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin p × Fin M)) ℂ}

/-- `E_Q F(seqTraceMeasure ∘ tseq) = E_ent F`. -/
theorem IsCutoffCoupling.lintegral_entrance
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    (F : unitInterval → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, ∫⁻ y, F y ∂seqTraceMeasure (tseq x) ∂driverLaw (κ := SourceNoise ι) μ =
      ∫⁻ ν, ∫⁻ y, F y ∂ν ∂ent := by
  have hm : Measurable fun x => seqTraceMeasure (tseq x) :=
    measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl)
  rw [← hC.model₁.entrance_law, lintegral_map (Measure.measurable_lintegral hF) hm]

theorem IsCutoffCoupling.initTrace_le
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂) :
    initTrace μ Emb tseq p M h₁ h₂ ≤ 8 * ∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent := by
  have hmeas : Measurable fun x => ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) :=
    (Measure.measurable_lintegral (measurable_psiP _)).comp
      (measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl))
  rw [← hC.lintegral_entrance _ (measurable_psiP _), ← lintegral_const_mul _ hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hC.model₁.entrance_sequence] with x hx
  have ht : ∀ i, 0 ≤ tseq x i ∧ tseq x i ≤ 1 := hx.2.1
  simp only [cutFrame, hsSq_isometry_mul hC.isometry]
  rw [ENNReal.ofReal_add (hsSq_nonneg _) (hsSq_nonneg _)]
  have e1 := hsSq_initialFrame_le (K := K) (π := Fin p × Fin M) ht h₁
  have e2 := hsSq_initialFrame_le (K := K) (π := Fin p × Fin M) ht h₂
  calc _ ≤ 4 * ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) +
        4 * ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) := add_le_add e1 e2
    _ = _ := by ring

theorem IsCutoffCoupling.initDist_le
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    (h0 : 0 ≤ h₁) (h12 : h₁ ≤ h₂) :
    initDist μ Emb tseq p M h₁ h₂ ≤ 4 * ∫⁻ ν, ∫⁻ y, tailPsi h₂ y ∂ν ∂ent := by
  have hmeas : Measurable fun x => ∫⁻ y, tailPsi h₂ y ∂seqTraceMeasure (tseq x) :=
    (Measure.measurable_lintegral (measurable_tailPsi _)).comp
      (measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl))
  rw [← hC.lintegral_entrance _ (measurable_tailPsi _), ← lintegral_const_mul _ hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hC.model₁.entrance_sequence] with x hx
  simp only [cutFrame, ← Matrix.mul_sub, hsSq_isometry_mul hC.isometry]
  exact hsSq_initialFrame_sub_le hx.2.1 h0 h12

end BlockBand.SourceProcess.CutoffLimit
