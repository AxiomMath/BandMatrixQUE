module

public import BlockBand.SourceProcess.ComplexCutoff.Pin
public import BlockBand.SourceProcess.CutoffLimit.Uniform

/-!
# Frame bounds for a complex cutoff coupling

The bounds of `IsCutoffCoupling`, for `IsComplexCutoffCoupling` (same proofs; the frame fields
are those of `IsCutoffCoupling`):

* `initTrace_le`: `E R₀ ≤ 8 E_ent ∫ψ_{1/2}`; `initDist_le`: `E X₀ ≤ 4 E_ent ∫ψ_{1/2}1_{y≤h₂²}`;
* `meas_trace_le`: `P(‖X₁(t)‖² + ‖X₂(t)‖² ≥ L) ≤ (E R₀ + 2B)/L`;
* `meas_dist_le`: the coupled distance, from `RankFreeCoupling` (`rankFreeCoupling_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.CutoffLimit
open BlockBand.SourceProcess.SourcePins BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h₁ h₂ : ℝ} {K : ℕ}
  {ent : Measure (Measure unitInterval)} {ι S : Type} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {Naux : ℕ} {P : Matrix ι ι ℂ}
  {Emb : Matrix ι (Fin K × Fin 2) ℂ}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DriverSample S (SourceNoise ι)))}
  {tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ} {nb : ℕ}
  {tb : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0} {col : Fin nb → SrcCol K (Fin np)}
  {w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ} {β : Fin nb → ℝ}
  {X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι (SrcCol K (Fin np)) ℂ}
  {Y₁ Y₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ}

/-- `E R₀ = E(‖ξ₁‖² + ‖ξ₂‖²)`. -/
def initTrace' (μ : Measure S) [IsProbabilityMeasure μ] (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) (np : ℕ) (h₁ h₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hsSq (cutFrame (Fin np) Emb tseq h₁ x) +
    hsSq (cutFrame (Fin np) Emb tseq h₂ x)) ∂driverLaw (κ := SourceNoise ι) μ

/-- `E X₀ = E ‖ξ₁ − ξ₂‖²`. -/
def initDist' (μ : Measure S) [IsProbabilityMeasure μ] (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) (np : ℕ) (h₁ h₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hsSq (cutFrame (Fin np) Emb tseq h₁ x -
    cutFrame (Fin np) Emb tseq h₂ x)) ∂driverLaw (κ := SourceNoise ι) μ

variable (hC : IsComplexCutoffCoupling b E s τ m h₁ h₂ K ent μ Naux P Emb 𝓖 tseq tb col w β
  X₁ X₂ Y₁ Y₂)
include hC

/-- `E_Q F(seqTraceMeasure ∘ tseq) = E_ent F`. -/
theorem IsComplexCutoffCoupling.lintegral_entrance (F : unitInterval → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ x, ∫⁻ y, F y ∂seqTraceMeasure (tseq x) ∂driverLaw (κ := SourceNoise ι) μ =
      ∫⁻ ν, ∫⁻ y, F y ∂ν ∂ent := by
  have hm : Measurable fun x => seqTraceMeasure (tseq x) :=
    measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl)
  rw [← hC.model₁.entrance_law, lintegral_map (Measure.measurable_lintegral hF) hm]

theorem IsComplexCutoffCoupling.initTrace_le :
    initTrace' μ Emb tseq np h₁ h₂ ≤ 8 * ∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent := by
  have hmeas : Measurable fun x => ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) :=
    (Measure.measurable_lintegral (measurable_psiP _)).comp
      (measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl))
  rw [← hC.lintegral_entrance _ (measurable_psiP _), ← lintegral_const_mul _ hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hC.model₁.entrance_sequence] with x hx
  have ht : ∀ i, 0 ≤ tseq x i ∧ tseq x i ≤ 1 := hx.2.1
  simp only [cutFrame, hsSq_isometry_mul hC.isometry]
  rw [ENNReal.ofReal_add (hsSq_nonneg _) (hsSq_nonneg _)]
  have e1 := hsSq_initialFrame_le (K := K) (π := Fin np) ht h₁
  have e2 := hsSq_initialFrame_le (K := K) (π := Fin np) ht h₂
  calc _ ≤ 4 * ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) +
        4 * ∫⁻ y, psiP (1 / 2) y ∂seqTraceMeasure (tseq x) := add_le_add e1 e2
    _ = _ := by ring

theorem IsComplexCutoffCoupling.initDist_le (h0 : 0 ≤ h₁) (h12 : h₁ ≤ h₂) :
    initDist' μ Emb tseq np h₁ h₂ ≤ 4 * ∫⁻ ν, ∫⁻ y, tailPsi h₂ y ∂ν ∂ent := by
  have hmeas : Measurable fun x => ∫⁻ y, tailPsi h₂ y ∂seqTraceMeasure (tseq x) :=
    (Measure.measurable_lintegral (measurable_tailPsi _)).comp
      (measurable_seqTraceMeasure.comp (hC.model₁.entrance_measurable.mono (𝓖.le 0) le_rfl))
  rw [← hC.lintegral_entrance _ (measurable_tailPsi _), ← lintegral_const_mul _ hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [hC.model₁.entrance_sequence] with x hx
  simp only [cutFrame, ← Matrix.mul_sub, hsSq_isometry_mul hC.isometry]
  exact hsSq_initialFrame_sub_le hx.2.1 h0 h12

/-- `E R₀ + 2B ≤ 8Γ + 2 Σ_j d_* m_j`. -/
theorem IsComplexCutoffCoupling.initTrace_add_le :
    initTrace' μ Emb tseq np h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k) ≤
      8 * (∫⁻ ν, ∫⁻ y, psiP (1 / 2) y ∂ν ∂ent) + ENNReal.ofReal (2 * ∑ j, dStar b * m j) := by
  rw [hC.birth_total]
  exact add_le_add hC.initTrace_le le_rfl

/-- **The trace tail.** -/
theorem IsComplexCutoffCoupling.meas_trace_le (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2)
    (t : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    driverLaw (κ := SourceNoise ι) μ {x | L ≤ hsSq (X₁ t x) + hsSq (X₂ t x)} ≤
      (initTrace' μ Emb tseq np h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L := by
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hD := isSignature_srcSignature K (Fin np)
  have hξ₁c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i,
      cutFrame (Fin np) Emb tseq h₁ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hC.col_zero k).mono fun x hx i => (hx i).1
  have hξ₂c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i,
      cutFrame (Fin np) Emb tseq h₂ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hC.col_zero k).mono fun x hx i => (hx i).2
  have hwβ : ∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∑ i, ‖w k x i‖ ^ 2 = β k :=
    fun k => (hC.birth_near k).mono fun x hx => hx.2
  have hB := lintegral_stopped_trace_le hD0 hC.nearProj hD hC.frame₁_meas hC.frame₂_meas
    hC.frame₁_two hC.frame₂_two hC.stopping hC.birth_meas hC.col_inj hC.col_sig hξ₁c hξ₂c hwβ
    hC.sol₁ hC.sol₂ (isStoppingTime_top _) t
  simp only [stoppedProcess_eq_stopTime, stopTime_top] at hB
  have hRloc := (locMart_traceProc hD0 hC.nearProj hD hC.frame₁_meas hC.frame₁_two hC.stopping
    hC.birth_meas hC.col_sig hξ₁c hwβ hC.sol₁).add
    (locMart_traceProc hD0 hC.nearProj hD hC.frame₂_meas hC.frame₂_two hC.stopping
      hC.birth_meas hC.col_sig hξ₂c hwβ hC.sol₂)
  have hm : AEMeasurable (fun x => traceProc X₁ tb col w β t x + traceProc X₂ tb col w β t x)
      (driverLaw (κ := SourceNoise ι) μ) :=
    ((hRloc.prog.stronglyAdapted t).mono
      ((driverAugmented (κ := SourceNoise ι) μ).le t)).measurable.aemeasurable
  have hd₁ := norm_sq_le_traceProc hD0 hC.nearProj hD hC.frame₁_meas hC.frame₁_two hC.stopping
    hC.birth_meas hC.col_inj hC.col_sig hξ₁c hwβ hC.sol₁
  have hd₂ := norm_sq_le_traceProc hD0 hC.nearProj hD hC.frame₂_meas hC.frame₂_two hC.stopping
    hC.birth_meas hC.col_inj hC.col_sig hξ₂c hwβ hC.sol₂
  have hincl : {x | L ≤ hsSq (X₁ t x) + hsSq (X₂ t x)} ≤ᵐ[driverLaw (κ := SourceNoise ι) μ]
      {x | L ≤ traceProc X₁ tb col w β t x + traceProc X₂ tb col w β t x} := by
    filter_upwards [hd₁, hd₂] with x h1 h2 hx
    simp only [hsSq_eq] at hx ⊢
    linarith [h1 t, h2 t]
  exact (measure_mono_ae hincl).trans ((meas_le_lintegral_div hm hL).trans
    (ENNReal.div_le_div_right hB _))

/-- **The coupled distance**, from `RankFreeCoupling` (proved as `rankFreeCoupling_holds`). -/
theorem IsComplexCutoffCoupling.meas_dist_le (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2)
    (t : ℝ≥0) {lev u : ℝ} (hlev : 0 < lev) (hu : 0 < u) :
    driverLaw (κ := SourceNoise ι) μ {x | u < hsSq (X₁ t x - X₂ t x)} ≤
      (initTrace' μ Emb tseq np h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal lev +
        ENNReal.ofReal (Real.exp (transportD0 b E * lev ^ 2 * t / 2)) *
          initDist' μ Emb tseq np h₁ h₂ / ENNReal.ofReal u := by
  have h := rankFreeCoupling_holds ι (SrcCol K (Fin np)) S μ (transportD0 b E) Naux P
    (srcSignature K (Fin np)) (transportD0_pos' hb0 hE1 hE2) hC.nearProj
    (isSignature_srcSignature K _) _ _ hC.frame₁_meas hC.frame₂_meas hC.frame₁_two hC.frame₂_two
    nb tb col w β hC.stopping hC.birth_meas hC.col_inj hC.col_sig hC.col_zero hC.birth_near X₁ X₂
    hC.sol₁ hC.sol₂ hC.perp lev u t hlev hu t.2
  refine (measure_mono fun x (hx : u < hsSq (X₁ t x - X₂ t x)) =>
    (⟨t, le_rfl, hx⟩ : ∃ t' : ℝ≥0, (t' : ℝ) ≤ t ∧ u < hsSq (X₁ t' x - X₂ t' x))).trans h

end BlockBand.SourceProcess.ComplexCutoff
