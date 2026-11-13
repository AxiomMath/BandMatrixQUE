module

public import BlockBand.SourceProcess.SmallLeak.LeakPast
public import BlockBand.Transmission.PassiveCovariance.Step3

/-!
# One stopped step of the leakage

The source leakage recursion on the trace stop.

On `S_j = traceStopEv K j` (`γ_i ≤ K`): `E[1_{S_{j+1}}ℓ_{j+1}] ≤ E[1_{S_j}ℓ_j] + E b_j` with the past
bound `b_j = (m/η)K√g + ((m²+σ²)/(2η²))Kg + c_jBg/(4η²)` (`leak_stopped_step`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.ClosingLeak
open scoped Matrix ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The one-step leakage bound as a function of the past. -/
def leakBnd (b E h s : ℝ) (q : ℝ → ℝ) (K Cm Cf B : ℝ) (W j : ℕ) (p : PastSample W j) : ℝ :=
  Cm * (jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)) + (W : ℝ)⁻¹) /
      etaZ b E * K * Real.sqrt (fluxPast b E h s W j p) +
    ((Cm * (jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)) + (W : ℝ)⁻¹)) ^ 2 +
      (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p)))) ^ 2) /
      (2 * etaZ b E ^ 2) * K * fluxPast b E h s W j p +
    birthWeight q W j * B * fluxPast b E h s W j p / (4 * etaZ b E ^ 2)

theorem measurable_leakBnd (b E h s : ℝ) (q : ℝ → ℝ) (K Cm Cf B : ℝ) (j : ℕ) :
    Measurable (leakBnd b E h s q K Cm Cf B W j) := by
  have hδ := (measurable_jetDistance0 b E).comp (measurable_nearSchur_comp (boundaryZ b E)
    (measurable_pastXX (W := W) E j))
  have hg := measurable_fluxPast (W := W) b E h s j
  unfold leakBnd
  fun_prop

theorem trace_proj_sandwich {ι : Type*} [Fintype ι] {F Q : Matrix ι ι ℂ} (hF2 : F * F = F) :
    (F * Q * F).trace = (F * Q).trace := by
  rw [Matrix.trace_mul_cycle, hF2]

/-- **One stopped step of the leakage.** -/
theorem leak_stopped_step {b E h s : ℝ} (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) {j : ℕ} (hj1 : 1 ≤ j)
    (hsj : ⌊(W : ℝ) * s⌋₊ ≤ j) {K : ℝ} {Cm Cf B : ℝ} (hCf : 0 ≤ Cf)
    (hΔb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      (∀ x y, Integrable (fun f => freshDelta b E X f x y) (freshLaw W b)) ∧
        ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤
          Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) ∧
        ∀ u v : Fin W → ℂ, eLpNorm (fun f => bilinear u (freshDelta b E X f -
            matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal 2)
            (freshLaw W b) ≤
          ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v))
    (hN : ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      Integrable (fun f => ‖freshTransport b E XX f‖ ^ 2) (freshLaw W b))
    (hBb : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      Integrable (fun f => (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2) (freshLaw W b) ∧
        ∫ f, (1 + ‖freshDelta b E X f‖ / etaZ b E) ^ 2 ∂freshLaw W b ≤ B) :
    ∫⁻ ω, (traceStopEv b E s q K W (j + 1)).indicator
        (fun ω => ENNReal.ofReal (omittedLeak b E h s q W (j + 1) ω)) ω ∂growthPathLaw W b ≤
      ∫⁻ ω, (traceStopEv b E s q K W j).indicator
        (fun ω => ENNReal.ofReal (omittedLeak b E h s q W j ω)) ω ∂growthPathLaw W b +
      ∫⁻ ω, ENNReal.ofReal (leakBnd b E h s q K Cm Cf B W j (pastCoords W j ω))
        ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  set Ψ : PastSample W j → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (leakPast b E h s q W j p + leakBnd b E h s q K Cm Cf B W j p)
  have hmΨ : Measurable Ψ :=
    ((measurable_leakPast b E h s q j).add (measurable_leakBnd b E h s q K Cm Cf B j)).ennreal_ofReal
  have hmΦ : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
      ENNReal.ofReal (leakNext b E h s q W j x) := by
    have hXX : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
        pastXX E W j x.1 := (measurable_pastXX E j).comp measurable_fst
    have hNm := measurable_freshTransport_comp b E hXX measurable_snd
    have hDm : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
        freshD b E (pastXX E W j x.1) x.2 :=
      measurable_freshD_comp b E hXX measurable_snd
    have hA : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
        omittedPast b E h s W j x.1 := (measurable_omittedPast b E h s j).comp measurable_fst
    have hF := ClosingAux.measurable_farEmbed hA
    have hQ : Measurable fun x : PastSample W j × LayerSample W .oneBlockOnePort =>
        srcPast b E q W j x.1 := (measurable_srcPast b E q j).comp measurable_fst
    exact (measurable_trace_re (measurable_matrix_mul' hF (ClosingAux.measurable_matrix_add
      (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hNm) hQ)
        hNm) (measurable_matrix_smul _ (measurable_matrix_mul' (measurable_matrix_conjTranspose' hDm)
          hDm))))).ennreal_ofReal
  have h1 : ∫⁻ ω, (traceStopEv b E s q K W (j + 1)).indicator
      (fun ω => ENNReal.ofReal (omittedLeak b E h s q W (j + 1) ω)) ω ∂μ ≤
      ∫⁻ ω, (traceStopEv b E s q K W j).indicator
        (fun ω => ENNReal.ofReal (omittedLeak b E h s q W (j + 1) ω)) ω ∂μ :=
    lintegral_mono fun ω => Set.indicator_le_indicator_of_subset
      (traceStopEv_succ_subset b E s q K j) (fun _ => zero_le) ω
  refine h1.trans ?_
  rw [traceStopEv_eq b E s q K j]
  have hZ : ∀ᵐ ω ∂μ, pastCoords W j ω ∈ traceStopPast b E s q K W j →
      ENNReal.ofReal (omittedLeak b E h s q W (j + 1) ω) ≤
        ENNReal.ofReal (leakNext b E h s q W j (pastCoords W j ω, freshSample W j ω)) := by
    filter_upwards [ae_omittedLeak_succ (h := h) q hb0 hb hE1 hE2 hW hj1 hsj] with ω hω _
    rw [hω]
  have hstep : ∀ᵐ p ∂pastLaw W j b, p ∈ traceStopPast b E s q K W j →
      ∫⁻ f, ENNReal.ofReal (leakNext b E h s q W j (p, f)) ∂freshLaw W b ≤ Ψ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with p hp hG
    have hXX := pastXX_isHermitian E hp
    set X := nearSchur (boundaryZ b E) (pastXX E W j p) with hXdef
    have hXp : (passiveY X).PosSemidef := by
      have := passiveY_pastX (κ := fun _ => 0) (by linarith : b < 1) hE1 hE2 (fun _ => le_rfl) hp
      rwa [pastX_zero_eq] at this
    obtain ⟨hΔi, hm, hfl⟩ := hΔb X hXp
    obtain ⟨hBi, hB⟩ := hBb X hXp
    have hQpsd : (srcPast b E q W j p).PosSemidef := intervalSource_psd b E j hq _
    obtain ⟨R, hR⟩ := exists_conjTranspose_mul_self hQpsd
    have hγ : hsNorm R ^ 2 ≤ K := by
      have h := hG j le_rfl hsj
      rw [show restrictPast le_rfl p = p from rfl, hR, trace_conjTranspose_mul_self,
        Complex.ofReal_re] at h
      exact h
    have hc : 0 ≤ birthWeight q W j := div_nonneg (hq _) (sq_nonneg _)
    have hmΔ : Measurable (freshDelta b E X) :=
      measurable_freshDelta_comp b E (X := fun _ => X) measurable_const measurable_id
    have hstep' := leak_layer_step hb0 hb hE1 hE2 hXp (omittedPast_conjTranspose b E h s j p)
      (omittedPast_mul_self b E h s j p) R hc hΔi hmΔ
      (mul_nonneg hCf (add_nonneg (by positivity) (norm_nonneg _))) hm hfl (hN _ hXX) hBi hB
    rw [← hR] at hstep'
    refine hstep'.trans (ENNReal.ofReal_le_ofReal ?_)
    have hg0 : 0 ≤ fluxAt b E (pastXX E W j p) (omittedPast b E h s W j p) :=
      fluxAt_nonneg b E _ (omittedPast_conjTranspose b E h s j p)
    have hF2 : farEmbed (omittedPast b E h s W j p) * farEmbed (omittedPast b E h s W j p) =
        farEmbed (omittedPast b E h s W j p) := by rw [farEmbed_mul, omittedPast_mul_self]
    have hℓ : (farEmbed (omittedPast b E h s W j p) * srcPast b E q W j p *
        farEmbed (omittedPast b E h s W j p)).trace.re = leakPast b E h s q W j p := by
      rw [leakPast, trace_proj_sandwich hF2]
    rw [hℓ]
    simp only [leakBnd, fluxPast]
    have hm0 : 0 ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) := (norm_nonneg _).trans hm
    have e1 := mul_le_mul_of_nonneg_left hγ (show 0 ≤ Cm * (jetDistance0 b E X + (W : ℝ)⁻¹) /
      etaZ b E * Real.sqrt (fluxAt b E (pastXX E W j p) (omittedPast b E h s W j p)) by positivity)
    have e2 := mul_le_mul_of_nonneg_left hγ (show 0 ≤ ((Cm * (jetDistance0 b E X + (W : ℝ)⁻¹)) ^ 2 +
      (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X)) ^ 2) / (2 * etaZ b E ^ 2) *
        fluxAt b E (pastXX E W j p) (omittedPast b E h s W j p) by positivity)
    simp only [hXdef, jetDistance0] at e1 e2 ⊢
    linarith
  have hstepI := lintegral_indicator_step (μ := μ) (μP := pastLaw W j b) (ν := freshLaw W b)
    (measurable_pastCoords W j) (measurable_freshSample W j)
    (growthPathLaw_map_past_fresh W j b) (measurableSet_traceStopPast b E s q K j) hmΦ hmΨ hZ
    hstep
  refine hstepI.trans ?_
  rw [← lintegral_add_left ((Measurable.ennreal_ofReal (measurable_omittedLeak b E h s q j)).indicator
    ((measurableSet_traceStopPast b E s q K j).preimage (measurable_pastCoords W j)))]
  refine lintegral_mono fun ω => ?_
  by_cases hm : ω ∈ pastCoords W j ⁻¹' traceStopPast b E s q K W j
  · simp only [Set.indicator_of_mem hm, Ψ]
    rw [omittedLeak_eq_past q hsj ω]
    exact ENNReal.ofReal_add_le
  · simp only [Set.indicator_of_notMem hm, zero_add]; exact zero_le

end BlockBand.SourceProcess.SmallLeak
