module

public import BlockBand.SourceProcess.CutoffLimit.Uniform
public import BlockBand.SourceProcess.SourceProcessLaw.Extraction

/-!
# `CutoffRemoval` from the coupled cutoff models

The target is `SourceProcessLaw.CutoffRemoval`.

* The uniform bound (in the proof of `cutoffRemoval_of`, through
  `IsCutoffCoupling.abs_sub_le_four`): for every `ε > 0` there is `h₀ > 0` with `|Φ(K,h₁) − Φ(K,h₂)| ≤ 4ε` for all
  `0 < h₁ ≤ h₂ < h₀` and **all caps `K`**. Proof: the coupling of `CoupledCutoffFrames`;
  `abs_sub_le` with the trace tail `(E R₀ + 2B)/L` and the rank-free bound
  `(E R₀ + 2B)/lev + e^{D₀lev²(T−s)/2} E X₀/u`; `E R₀ ≤ 8 E∫ψ_{1/2}` is finite by the
  `fractional` field of `TransmissionLawContract` (`lintegral_entrance_psi_lt_top`), `E X₀ ≤ 4 E∫ψ_{1/2}1_{y ≤ h₂²} → 0`
  (`tendsto_tail`). Choose `L`, then `δ` (`probeVal_uc`), `u`, `lev`, then `h₀`.
* `exists_tendsto_of_uniform`: such a family has a limit along `𝓝[>] 0` (Cauchy).
* `cutoffRemoval_of hTL hCF : CutoffRemoval`; `cutoffRemoval_holds hMT hGA hLp hP hCF`. The
  hypothesis `CoupledCutoffFrames` is proved as `CoupledFrames.coupledCutoffFrames_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourcePins
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal

/-- A Cauchy family along `𝓝[>] 0` converges. -/
theorem exists_tendsto_of_uniform (Λ : ℝ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ x y : ℝ, 0 < x → x ≤ y → y < h₀ →
      |Λ x - Λ y| ≤ ε) :
    ∃ L : ℝ, Tendsto Λ (𝓝[>] 0) (𝓝 L) := by
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  obtain ⟨h₀, hh₀, hΛ⟩ := h (ε / 2) (half_pos hε)
  refine ⟨Λ '' Set.Ioo 0 h₀, image_mem_map (Ioo_mem_nhdsGT hh₀), ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · exact (hΛ x y hx.1 hxy hy.2).trans_lt (half_lt_self hε)
  · rw [abs_sub_comm]
    exact (hΛ y x hy.1 hxy hx.2).trans_lt (half_lt_self hε)

/-- `A / L ≤ ε` for some `L > 0` when `A < ∞`. -/
theorem exists_div_le {A : ℝ≥0∞} (hA : A ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ A / ENNReal.ofReal L ≤ ENNReal.ofReal ε := by
  refine ⟨A.toReal / ε + 1, by positivity, ?_⟩
  rw [ENNReal.div_le_iff (by simp; positivity) ENNReal.ofReal_ne_top]
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal (ε * (A.toReal / ε + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_add, mul_div_cancel₀ _ hε.ne', mul_one]
        linarith
    _ = _ := ENNReal.ofReal_mul hε.le

/-- `c · (4η) / u = ε` for `η = εu/(4c)`. -/
theorem ofReal_mul_div_eq {c u ε : ℝ} (hc : 0 < c) (hu : 0 < u) (hε : 0 < ε) :
    ENNReal.ofReal c * (4 * ENNReal.ofReal (ε * u / (4 * c))) / ENNReal.ofReal u =
      ENNReal.ofReal ε := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_div_of_pos hu]
  congr 1
  field_simp

/-- **`CutoffRemoval`** from
`TransmissionLawContract` and `CoupledCutoffFrames` (proved as `CoupledFrames.coupledCutoffFrames_holds`). -/
theorem cutoffRemoval_of (hTL : TransmissionLawContract) (hCF : CoupledCutoffFrames) :
    CutoffRemoval := by
  intro b hb0 hb E hE1 hE2 Ω m P μ hlim s T hs hsT p q hq J a ha M hM Φ Λ hΦ hΛ
  obtain ⟨ρ, hρ, hρs, hρe⟩ :=
    entrance_sequence (entranceAtomic_of hTL) seqExtraction_holds hb0 hb hE1 hE2 hlim hs
  have hΓ := lintegral_entrance_psi_lt_top hTL hb0 hb hE1 hE2 hlim hs
  have htl := tendsto_tail hΓ
  have hA : momentBound (entranceLaw P μ s) b s T q M ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hΓ.ne, ENNReal.ofReal_ne_top⟩
  refine exists_tendsto_of_uniform Λ fun ε₄ hε₄ => ?_
  have hε : 0 < ε₄ / 4 := by positivity
  obtain ⟨L, hL, hAL⟩ := exists_div_le hA hε
  obtain ⟨δ, hδ0, hδ⟩ := probeVal_uc (π := Fin p × Fin M)
    (a := fun j (i : Fin p × Fin M) => a j i.1) (fun j i => ha j i.1) L (ε₄ / 4) hε
  have hr : 0 < δ / (2 * (Real.sqrt L + 1)) := by positivity
  have hu : 0 < (δ / (2 * (Real.sqrt L + 1))) ^ 2 := by positivity
  have huL : 2 * (Real.sqrt ((δ / (2 * (Real.sqrt L + 1))) ^ 2) * Real.sqrt L) < δ := by
    rw [Real.sqrt_sq hr.le]
    have h1 : δ / (2 * (Real.sqrt L + 1)) * (2 * (Real.sqrt L + 1)) = δ :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨lev, hlev, hAlev⟩ := exists_div_le hA hε
  have hc : 0 < Real.exp (transportD0 b E * lev ^ 2 * ((T - s).toNNReal : ℝ) / 2) :=
    Real.exp_pos _
  have hη : (0 : ℝ≥0∞) < ENNReal.ofReal (ε₄ / 4 * (δ / (2 * (Real.sqrt L + 1))) ^ 2 /
      (4 * Real.exp (transportD0 b E * lev ^ 2 * ((T - s).toNNReal : ℝ) / 2))) :=
    ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := (htl.eventually (gt_mem_nhds hη)).exists
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun x y hx hxy hy => ?_⟩
  have hy0 : 0 < y := hx.trans_le hxy
  have hlim' : Tendsto (fun K => Φ K x - Φ K y) atTop (𝓝 (Λ x - Λ y)) :=
    (hΛ x hx).sub (hΛ y hy0)
  refine le_of_tendsto hlim'.abs (Eventually.of_forall fun K => ?_)
  obtain ⟨ι, S, _, _, _, μ', _, Naux, P', Emb, 𝓖, tseq, σb, nb, τ, col, w, β, X₁, X₂, hC⟩ :=
    hCF b hb0 hb E hE1 hE2 s T hs hsT p q hq ρ hρ hρs x y K M hx hxy hM
  rw [hρe] at hC
  have htail : ENNReal.ofReal (Real.exp (transportD0 b E * lev ^ 2 * ((T - s).toNNReal : ℝ) / 2)) *
      (4 * tailMass (entranceLaw P μ s) y) /
        ENNReal.ofReal ((δ / (2 * (Real.sqrt L + 1))) ^ 2) ≤ ENNReal.ofReal (ε₄ / 4) := by
    rw [← ofReal_mul_div_eq hc hu hε]
    gcongr
    exact (lintegral_mono fun ν => lintegral_mono (tailPsi_mono hy0.le hy.le)).trans hn.le
  have h4 := hC.abs_sub_le_four hb0 hE1 hE2 hx.le hxy ha hε hL hu hlev hδ huL hAL hAlev htail
    (hΦ K x hx) (hΦ K y hy0)
  linarith

/-- **`CutoffRemoval` from `MatchedTracesContract` and the Gaussian inputs**, and
`CoupledCutoffFrames` (proved as `CoupledFrames.coupledCutoffFrames_holds`). -/
theorem cutoffRemoval_holds (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hCF : CoupledCutoffFrames) :
    CutoffRemoval :=
  cutoffRemoval_of (Transmission.LawForced.transmissionLawContract_holds hMT hGA hLp hP) hCF

/-- `CoupledCutoffFrames` is at least `ModelExists` (take `h₁ = h₂ = h` and the first model):
it is the frame-level construction of `ModelExists`, run for two cutoffs on one driver space. -/
theorem modelExists_of_coupled (hCF : CoupledCutoffFrames) : ModelExists := by
  intro b hb0 hb E hE1 hE2 s T hs hsT p q hq ρ hρ hρs h K M hh hM
  obtain ⟨ι, S, _, _, _, μ, _, Naux, P, Emb, 𝓖, tseq, σb, nb, τ, col, w, β, X₁, X₂, hC⟩ :=
    hCF b hb0 hb E hE1 hE2 s T hs hsT p q hq ρ hρ hρs h h K M hh le_rfl hM
  exact ⟨DriverSample S (SourceNoise ι), inferInstance, 𝓖, driverLaw (κ := SourceNoise ι) μ, tseq,
    σb, fun t x => gramPair P (X₁ t x), hC.model₁⟩

end BlockBand.SourceProcess.CutoffLimit
