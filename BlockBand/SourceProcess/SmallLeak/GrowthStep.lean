module

public import BlockBand.SourceProcess.SmallLeak.GrowthPast
public import BlockBand.SourceProcess.FullSource.TagPath
public import BlockBand.SourceProcess.FullSource.PathSetup
public import BlockBand.SourceProcess.FullSource.TagStep

/-!
# One stopped step of the weighted omitted flux

This is the analogue of `stopped_current_step_on` for the omitted flux.

`fluxWeight j = (1 + Kδ_j) g_j`. On the δ-stop `G_j = stopEv k d j` (`k + 1 ≤ j`, `n_s ≤ j`):
`E[1_{G_{j+1}} Z_{j+1}] ≤ (1 + α/W) E[1_{G_j} Z_j]` (`flux_stopped_step`).
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
open scoped Matrix ComplexOrder ENNReal

variable {W : ℕ}

/-- `Z_j = (1 + Kδ_j) g_j`. -/
def fluxWeight (b E h s K : ℝ) (W j : ℕ) (ω : GrowthPath W) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * pathDelta b E W j ω) * omittedFlux b E h s W j ω)

/-- `Z_j` as a function of the past. -/
def fluxPsi (b E h s K : ℝ) (W j : ℕ) (p : PastSample W j) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j p))) *
    fluxPast b E h s W j p)

/-- The fresh integrand of the step. -/
def fluxPhi (b E h s K ρ Cm : ℝ) (W j : ℕ) (q : PastSample W j × LayerSample W .oneBlockOnePort) :
    ℝ≥0∞ :=
  ENNReal.ofReal ((1 + K * (ρ * jetDistance0 b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) +
      Cm / (W : ℝ) ^ 2 + freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2)) *
    max (fluxNext b E (pastXX E W j q.1) (omittedPast b E h s W j q.1) q.2) 0)

theorem measurable_fluxNext_comp (b E : ℝ) {α : Type*} [MeasurableSpace α]
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {A : α → Matrix (Fin W) (Fin W) ℂ}
    {f : α → LayerSample W .oneBlockOnePort} (hXX : Measurable XX) (hA : Measurable A)
    (hf : Measurable f) : Measurable fun a => fluxNext b E (XX a) (A a) (f a) := by
  have hS := (CompleteSourceGap.measurable_twoPortScattering (W := W) b E).comp hXX
  have hM : Measurable fun a => scatOut b E (XX a) :=
    measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hS)
      measurable_const) hS
  have hN := measurable_freshTransport_comp b E hXX hf
  have hF := ClosingAux.measurable_farEmbed hA
  exact measurable_trace_re (measurable_matrix_mul' (measurable_matrix_mul' hF
    (ClosingAux.measurable_matrix_add (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_conjTranspose' hN) (measurable_matrix_sub hM measurable_const)) hN)
      measurable_const)) hF)

theorem measurable_fluxPhi (b E h s K ρ Cm : ℝ) (j : ℕ) :
    Measurable (fluxPhi b E h s K ρ Cm W j) := by
  have hXX : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      pastXX E W j q.1 := (measurable_pastXX E j).comp measurable_fst
  have hX := measurable_nearSchur_comp (boundaryZ b E) hXX
  have hδ := (measurable_jetDistance0 b E).comp hX
  have hF : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    measurable_freshPortTrace_comp b E hX measurable_snd
  have hI : Measurable fun p : PastSample W j =>
      ∫ f, freshPortTrace b E (nearSchur (boundaryZ b E) (pastXX E W j p)) f ∂freshLaw W b :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := freshLaw W b)).measurable
  have hξ : Measurable fun q : PastSample W j × LayerSample W .oneBlockOnePort =>
      freshXi b E (nearSchur (boundaryZ b E) (pastXX E W j q.1)) q.2 :=
    (hF.sub (hI.comp measurable_fst)).norm
  have hg := measurable_fluxNext_comp b E hXX
    ((measurable_omittedPast b E h s j).comp measurable_fst) measurable_snd
  unfold fluxPhi
  exact ((measurable_const.add (measurable_const.mul (((measurable_const.mul hδ).add
    measurable_const).add hξ))).mul (hg.max measurable_const)).ennreal_ofReal

theorem measurable_fluxWeight (b E h s K : ℝ) (j : ℕ) :
    Measurable (fluxWeight b E h s K W j) := by
  have hδ : Measurable (pathDelta b E W j) := by
    have e : pathDelta b E W j = fun ω => jetDistance0 b E (nearSchur (boundaryZ b E)
        (pastXX E W j (pastCoords W j ω))) := funext (pathDelta_eq_past b E j)
    rw [e]
    exact (measurable_jetDistance0 b E).comp (measurable_nearSchur_comp (boundaryZ b E)
      ((measurable_pastXX E j).comp (measurable_pastCoords W j)))
  exact ((measurable_const.add (measurable_const.mul hδ)).mul
    (measurable_omittedFlux b E h s j)).ennreal_ofReal

/-- Joint almost-sure statements pass to almost every past and almost every fresh layer. -/
theorem ae_ae_of_ae_pair {Ω P F : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    [MeasurableSpace F] {μ : Measure Ω} {μP : Measure P} {ν : Measure F} [SFinite μP] [SFinite ν]
    {π : Ω → P} {φ : Ω → F} (hπ : Measurable π) (hφ : Measurable φ)
    (hmap : μ.map (fun ω => (π ω, φ ω)) = μP.prod ν) {S : Set (P × F)} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂μ, (π ω, φ ω) ∈ S) : ∀ᵐ p ∂μP, ∀ᵐ f ∂ν, (p, f) ∈ S := by
  have : ∀ᵐ q ∂(μP.prod ν), q ∈ S := by
    rw [← hmap]; exact (ae_map_iff (hπ.prodMk hφ).aemeasurable hS).mpr h
  exact Measure.ae_ae_of_ae_prod this

/-- `E(1 + ‖Δ‖/(2η))⁴ ≤ (1 + C/(2η))⁴` from `‖Δ‖ ∈ L⁴`. -/
theorem delta_four {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {Δ : Ω → ℝ} {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (h : MomBd ν Δ ((4 : ℕ) : ℝ) C) :
    Integrable (fun ω => (1 + Δ ω / (2 * η)) ^ 4) ν ∧
      ∫ ω, (1 + Δ ω / (2 * η)) ^ 4 ∂ν ≤ (1 + C / (2 * η)) ^ 4 := by
  have h1 : MomBd ν (fun _ => (1 : ℝ)) ((4 : ℕ) : ℝ) 1 := by
    simpa using MomBd.const (μ := ν) (1 : ℝ) ((4 : ℕ) : ℝ) (by norm_num)
  have h2 : MomBd ν (fun ω => (2 * η)⁻¹ * Δ ω) ((4 : ℕ) : ℝ) ((2 * η)⁻¹ * C) :=
    h.const_mul (by positivity)
  have h3 := h1.add (by norm_num) h2 (by norm_num) (by positivity)
  obtain ⟨hi, hb⟩ := integral_abs_pow_le (ν := ν) (n := 4) (by norm_num) (by positivity) h3
  have e : ∀ ω, |1 + (2 * η)⁻¹ * Δ ω| ^ 4 = (1 + Δ ω / (2 * η)) ^ 4 := fun ω => by
    rw [abs_of_nonneg (by have := hΔ0 ω; positivity), div_eq_inv_mul]
  simp only [e] at hi hb
  refine ⟨hi, hb.trans (le_of_eq ?_)⟩
  rw [div_eq_inv_mul]

end BlockBand.SourceProcess.SmallLeak
