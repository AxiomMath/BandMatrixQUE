module

public import BlockBand.SourceProcess.CutoffLimit.Pin
public import BlockBand.SourceProcess.RankFree.Main
public import BlockBand.SourceProcess.BornUnique.Reduce

/-!
# Probability bounds for a cutoff coupling

For an `IsCutoffCoupling` at any time `t`:

* `meas_trace_le`: `P(‖X₁(t)‖² + ‖X₂(t)‖² ≥ L) ≤ (E R₀ + 2B_birth)/L`
  (`lintegral_stopped_trace_le` with `σ = ∞` and `norm_sq_le_traceProc`, then Markov);
* `meas_dist_le`: `P(‖X₁(t) − X₂(t)‖² > u) ≤ (E R₀ + 2B_birth)/lev + e^{D₀ lev² t/2} E X₀/u`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

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

/-- `E R₀ = E(‖ξ₁‖² + ‖ξ₂‖²)`. -/
def initTrace (μ : Measure S) [IsProbabilityMeasure μ] (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) (p M : ℕ) (h₁ h₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hsSq (cutFrame (Fin p × Fin M) Emb tseq h₁ x) +
    hsSq (cutFrame (Fin p × Fin M) Emb tseq h₂ x)) ∂driverLaw (κ := SourceNoise ι) μ

/-- `E X₀ = E ‖ξ₁ − ξ₂‖²`. -/
def initDist (μ : Measure S) [IsProbabilityMeasure μ] (Emb : Matrix ι (Fin K × Fin 2) ℂ)
    (tseq : DriverSample S (SourceNoise ι) → ℕ → ℝ) (p M : ℕ) (h₁ h₂ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hsSq (cutFrame (Fin p × Fin M) Emb tseq h₁ x -
    cutFrame (Fin p × Fin M) Emb tseq h₂ x)) ∂driverLaw (κ := SourceNoise ι) μ

theorem isStoppingTime_top {Ω : Type*} {m : MeasurableSpace Ω} (f : Filtration ℝ≥0 m) :
    IsStoppingTime f fun _ : Ω => (⊤ : WithTop ℝ≥0) := fun i => by
  simp only [top_le_iff, WithTop.coe_ne_top, Set.ofPred_false, MeasurableSet.empty]

/-- **The trace tail.** -/
theorem IsCutoffCoupling.meas_trace_le
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) (t : ℝ≥0) {L : ℝ} (hL : 0 < L) :
    driverLaw (κ := SourceNoise ι) μ {x | L ≤ hsSq (X₁ t x) + hsSq (X₂ t x)} ≤
      (initTrace μ Emb tseq p M h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal L := by
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hD := isSignature_srcSignature K (Fin p × Fin M)
  have hξ₁c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i,
      cutFrame (Fin p × Fin M) Emb tseq h₁ x i (col k) = 0 :=
    ae_all_iff.2 fun k => (hC.col_zero k).mono fun x hx i => (hx i).1
  have hξ₂c : ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ k i,
      cutFrame (Fin p × Fin M) Emb tseq h₂ x i (col k) = 0 :=
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
  have hm : AEMeasurable (fun x => traceProc X₁ τ col w β t x + traceProc X₂ τ col w β t x)
      (driverLaw (κ := SourceNoise ι) μ) :=
    ((hRloc.prog.stronglyAdapted t).mono
      ((driverAugmented (κ := SourceNoise ι) μ).le t)).measurable.aemeasurable
  have hd₁ := norm_sq_le_traceProc hD0 hC.nearProj hD hC.frame₁_meas hC.frame₁_two hC.stopping
    hC.birth_meas hC.col_inj hC.col_sig hξ₁c hwβ hC.sol₁
  have hd₂ := norm_sq_le_traceProc hD0 hC.nearProj hD hC.frame₂_meas hC.frame₂_two hC.stopping
    hC.birth_meas hC.col_inj hC.col_sig hξ₂c hwβ hC.sol₂
  have hincl : {x | L ≤ hsSq (X₁ t x) + hsSq (X₂ t x)} ≤ᵐ[driverLaw (κ := SourceNoise ι) μ]
      {x | L ≤ traceProc X₁ τ col w β t x + traceProc X₂ τ col w β t x} := by
    filter_upwards [hd₁, hd₂] with x h1 h2 hx
    simp only [hsSq_eq] at hx ⊢
    linarith [h1 t, h2 t]
  exact (measure_mono_ae hincl).trans ((meas_le_lintegral_div hm hL).trans
    (ENNReal.div_le_div_right hB _))

/-- **The coupled distance**, from `RankFreeCoupling` (proved as `rankFreeCoupling_holds`). -/
theorem IsCutoffCoupling.meas_dist_le
    (hC : IsCutoffCoupling b E s T q h₁ h₂ K M ent μ Naux P Emb 𝓖 tseq σb τ col w β X₁ X₂)
    (hb0 : 0 < b) (hE1 : -2 < E) (hE2 : E < 2) (t : ℝ≥0) {lev u : ℝ} (hlev : 0 < lev)
    (hu : 0 < u) :
    driverLaw (κ := SourceNoise ι) μ {x | u < hsSq (X₁ t x - X₂ t x)} ≤
      (initTrace μ Emb tseq p M h₁ h₂ + ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal lev +
        ENNReal.ofReal (Real.exp (transportD0 b E * lev ^ 2 * t / 2)) *
          initDist μ Emb tseq p M h₁ h₂ / ENNReal.ofReal u := by
  have h := rankFreeCoupling_holds ι (SrcCol K (Fin p × Fin M)) S μ (transportD0 b E) Naux P
    (srcSignature K (Fin p × Fin M)) (transportD0_pos' hb0 hE1 hE2) hC.nearProj
    (isSignature_srcSignature K _) _ _ hC.frame₁_meas hC.frame₂_meas hC.frame₁_two hC.frame₂_two
    nb τ col w β hC.stopping hC.birth_meas hC.col_inj hC.col_sig hC.col_zero hC.birth_near X₁ X₂
    hC.sol₁ hC.sol₂ hC.perp lev u t hlev hu t.2
  refine (measure_mono fun x (hx : u < hsSq (X₁ t x - X₂ t x)) =>
    (⟨t, le_rfl, hx⟩ : ∃ t' : ℝ≥0, (t' : ℝ) ≤ t ∧ u < hsSq (X₁ t' x - X₂ t' x))).trans h

end BlockBand.SourceProcess.CutoffLimit
