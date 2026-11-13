module

public import BlockBand.SourceProcess.FullSource.RightLetter

/-!
# `FullSourceEstimates.moments`: `‖N‖, ‖D₊‖ ∈ L^p` uniformly

`fullSourceMoments_field_holds`: for every Hermitian old two-port, `‖N‖` and `‖D₊‖` have `L^p`
norms bounded uniformly in `W ≥ W₀` and `E` in the bulk.

* `X = nearSchur z 𝕏` is passive (`nearSchur_passive`), so `moments_holds` applies at
  `w = z` and bounds `‖𝒢‖`, `‖L‖` in every `L^q`;
* pointwise on `{A Hermitian, B invertible}` (`transport_pointwise`), with
  `Q = 5 + ‖A‖ + η₀⁻¹‖B‖²`, `P = 1 + Q‖𝒢‖`, `η₀ = (1-b)κ/4 ≤ η`:
  `‖N‖ ≤ ‖L‖ + η₀⁻¹PQ + 1` (`‖Δ‖ ≤ PQ`, `‖ℝ₁₂‖ ≤ η⁻¹`) and `‖D₊‖ ≤ ‖𝒢‖ + η₀⁻¹P`
  (`‖𝒢₁₁K‖ ≤ P`);
* Gaussian moments of `‖A‖`, `‖B‖` (`blockA_mom`, `bondB_mom`) and Hölder (`MomBd`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- `Q = 5 + ‖A‖ + η₀⁻¹‖B‖²`. -/
def qPoly (η₀ : ℝ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)

theorem boundaryZ_mem_paramDisk {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) :
    boundaryZ b E ∈ paramDisk b E :=
  Metric.mem_closedBall_self (by have := etaZ_pos b E hb h1 h2; linarith)

/-- **Pointwise transport bounds** on `{A Hermitian, B invertible}`. -/
theorem transport_pointwise {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ‖freshTransport b E XX ω‖ ≤
        ‖lAt E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω‖ +
          ((1 - b) * κ / 4)⁻¹ * ((1 + qPoly ((1 - b) * κ / 4) ω *
            ‖layerAt E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω‖) *
            qPoly ((1 - b) * κ / 4) ω) + 1 ∧
      ‖freshD b E XX ω‖ ≤ ‖layerAt E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω‖ +
          ((1 - b) * κ / 4)⁻¹ * (1 + qPoly ((1 - b) * κ / 4) ω *
            ‖layerAt E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω‖) := by
  set η₀ := (1 - b) * κ / 4
  set z := boundaryZ b E
  set X := nearSchur z XX
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  have hEE := hE
  obtain ⟨hE1', hE2'⟩ := hEE
  have hE1 : -2 < E := by linarith
  have hE2 : E < 2 := by linarith
  obtain ⟨hw1, hw2, -, -⟩ :=
    disk_bounds hb0 hb hκ hE (boundaryZ_mem_paramDisk (by linarith) hE1 hE2)
  have hw : 0 < z.im := lt_of_lt_of_le hη₀ hw1
  have hY : (passiveY X).PosSemidef := nearSchur_passive hw hXX
  obtain ⟨hk, hd⟩ := right_letters_le E hw hY hA hB
  have hEabs : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hwb, hinv⟩ := weightBound_le (X := X) (ω := ω) hη₀ hw1 hw2 hEabs
  have hwb' : weightBound E z X ω ≤ 1 + qPoly η₀ ω * ‖layerAt E z X ω‖ := hwb
  have hv : letterVBound E z ω ≤ qPoly η₀ ω := by
    rw [letterVBound, qPoly, sq]
    have := mul_le_mul_of_nonneg_right hinv (mul_self_nonneg ‖ω.2 0 0‖)
    linarith
  have hR : ‖twoPortResolvent b E XX‖ ≤ η₀⁻¹ :=
    (norm_twoPortResolvent_le b E hXX hw).trans (inv_anti₀ hη₀ hw1)
  have hP0 : 0 ≤ 1 + qPoly η₀ ω * ‖layerAt E z X ω‖ :=
    (norm_nonneg _).trans (hk.trans hwb')
  constructor
  · refine (norm_freshTransport_le b E XX ω).trans ?_
    rw [freshL_eq_lAt, freshDelta_eq]
    have hΔ : ‖(z • 1 - X) * g11 E z X ω * (z • 1 - X) - (z • 1 - X)‖ ≤
        (1 + qPoly η₀ ω * ‖layerAt E z X ω‖) * qPoly η₀ ω :=
      hd.trans (mul_le_mul hwb' hv (letterVBound_nonneg E z ω) hP0)
    have := mul_le_mul hΔ hR (norm_nonneg _)
      (mul_nonneg hP0 ((letterVBound_nonneg E z ω).trans hv))
    nlinarith
  · refine (norm_freshD_le b E XX ω).trans ?_
    rw [freshBlock_tf_eq, freshBlock_tt_eq]
    have h1 := norm_g12_le E z X ω
    have h2 := mul_le_mul (hk.trans hwb') hR (norm_nonneg _) hP0
    nlinarith

/-- **The `moments` field of `FullSourceEstimates`** from `GaussianAbsorptionContract`: uniform
`L^p` bounds on `‖freshTransport‖` and `‖freshD‖` under `freshLaw W b`, for Hermitian inputs `XX`. -/
theorem fullSourceMoments_field_holds (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        eLpNorm (fun ω => ‖freshTransport b E XX ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal C ∧
          eLpNorm (fun ω => ‖freshD b E XX ω‖)
            (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal C := by
  intro b hb0 hb κ hκ p hp
  set η₀ := (1 - b) * κ / 4
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  have hp0 : 0 < p := by linarith
  obtain ⟨CM, W₀, hM⟩ := moments_holds hGA b hb0 hb κ hκ (4 * p) (by linarith)
  obtain ⟨CA, hCA0, hCA⟩ := blockA_mom hb (p := 4 * p) (by linarith)
  obtain ⟨CB, hCB0, hCB⟩ := bondB_mom hb0 (p := 8 * p) (by linarith)
  set CG := max CM 0
  have hCG : 0 ≤ CG := le_max_right _ _
  set CQ := 5 + CA + η₀⁻¹ * (CB * CB)
  set CP := 1 + CQ * CG
  have hCQ : 0 ≤ CQ := by positivity
  have hCP : 0 ≤ CP := by positivity
  set CN := CG + η₀⁻¹ * (CP * CQ) + 1
  set CD := CG + η₀⁻¹ * CP
  refine ⟨max CN CD, max W₀ 1, fun W hW E hE XX hXX => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hE' := hE
  obtain ⟨hE1', hE2'⟩ := hE'
  have hE1 : -2 < E := by linarith
  have hE2 : E < 2 := by linarith
  set z := boundaryZ b E
  set X := nearSchur z XX
  have hzD : z ∈ paramDisk b E := boundaryZ_mem_paramDisk (by linarith) hE1 hE2
  have hY : (passiveY X).PosSemidef :=
    nearSchur_passive (lt_of_lt_of_le hη₀ (disk_bounds hb0 hb hκ hE hzD).1) hXX
  obtain ⟨-, hG, -, hL⟩ := hM W (le_of_max_le_left hW) E hE z hzD X hY
  set μ := freshLaw W b
  have hGm : MomBd μ (fun ω => ‖layerAt E z X ω‖) (4 * p) CG :=
    ⟨(continuous_norm.measurable.comp (measurable_layerAt E z X)).aestronglyMeasurable,
      hG.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hLm4 : MomBd μ (fun ω => ‖lAt E z X ω‖) (4 * p) CG :=
    ⟨(continuous_norm.measurable.comp (measurable_lAt E z X)).aestronglyMeasurable,
      hL.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hLm : MomBd μ (fun ω => ‖lAt E z X ω‖) p CG := hLm4.exponent_mono (by linarith)
  have hAm := hCA W hW1
  have hBm := hCB W hW1
  have hP : MomBd μ (fun ω => 1 + (5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)) *
      ‖layerAt E z X ω‖) (2 * p) CP :=
    weight_mom (q := 2 * p) (by linarith) (inv_nonneg.mpr hη₀.le)
      (hAm.exponent_mono (by linarith)) (hBm.exponent_mono (by linarith))
      (hGm.exponent_mono (by linarith)) hCA0 hCB0 hCG
  have hQ : MomBd μ (fun ω => 5 + ‖ω.1 0‖ + η₀⁻¹ * (‖ω.2 0 0‖ * ‖ω.2 0 0‖)) (2 * p) CQ := by
    have hB' : MomBd μ (fun ω => ‖ω.2 0 0‖) (2 * (2 * p)) CB :=
      hBm.exponent_mono (by linarith)
    have hBB := (MomBd.mul (by positivity) hB' hB' hCB0).const_mul (inv_nonneg.mpr hη₀.le)
    have h5 : MomBd μ (fun _ => (5 : ℝ)) (2 * p) 5 := by
      simpa using MomBd.const (μ := μ) (5 : ℝ) (2 * p) (by positivity)
    exact (h5.add (by linarith) (hAm.exponent_mono (by linarith)) (by norm_num) hCA0).add
      (by linarith) hBB (by positivity) (by positivity)
  have hPQ := (hP.mul hp0 hQ hCP).const_mul (inv_nonneg.mpr hη₀.le)
  have h1 : MomBd μ (fun _ => (1 : ℝ)) p 1 := by simpa using MomBd.const (μ := μ) (1 : ℝ) p hp0
  have hNb := (hLm.add hp hPQ hCG (by positivity)).add hp h1 (by positivity) zero_le_one
  have hDb := (hGm.exponent_mono (by linarith : p ≤ 4 * p)).add hp
    (hP.exponent_mono (by linarith : p ≤ 2 * p) |>.const_mul (inv_nonneg.mpr hη₀.le)) hCG
    (by positivity)
  have hNm : MomBd μ (fun ω => ‖freshTransport b E XX ω‖) p CN := by
    refine MomBd.mono hNb ((BlockBand.SourceProcess.FullSource.measurable_freshTransport_comp
      b E (XX := fun _ => XX) measurable_const measurable_id).norm.aestronglyMeasurable) ?_
    filter_upwards [ae_good W hb0 hW1] with ω hω
    rw [norm_norm]
    exact (transport_pointwise hb0 hb hκ hE hXX hω.1 hω.2).1
  have hDm : MomBd μ (fun ω => ‖freshD b E XX ω‖) p CD := by
    refine MomBd.mono hDb ((measurable_freshD_comp b E (XX := fun _ => XX) measurable_const
      measurable_id).norm.aestronglyMeasurable) ?_
    filter_upwards [ae_good W hb0 hW1] with ω hω
    rw [norm_norm]
    exact (transport_pointwise hb0 hb hκ hE hXX hω.1 hω.2).2
  exact ⟨hNm.2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
    hDm.2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩

end BlockBand.SourceProcess.FullSource
