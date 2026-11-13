module

public import BlockBand.SourceProcess.FullSource.MomentsHolds
public import BlockBand.SourceProcess.FullSource.WardNoise
public import BlockBand.SourceProcess.FullSource.LayerStep
public import BlockBand.Transmission.PassiveCovariance.LayerBlocks

/-!
# Moments and integrability of `Δ = K𝒢₁₁K - K` at a passive input

* `delta_pointwise`: `‖Δ‖ ≤ PQ` on `{A Hermitian, B invertible}`
  (`Q = 5 + ‖A‖ + η₀⁻¹‖B‖²`, `P = 1 + Q‖𝒢‖`; `Δ = K𝒢₁₁V`);
* `delta_moments`: `‖‖Δ‖‖_{L^p} ≤ C_p`, uniformly in `W ≥ W₀`, `E ∈ bulkInterval κ` and passive `X`;
* `delta_integrable`: the entries of `Δ` are integrable and `‖EΔ‖ ≤ C`.
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

/-- `‖Δ‖ ≤ PQ` pointwise on `{A Hermitian, B invertible}`, for every passive `X`. -/
theorem delta_pointwise {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ‖freshDelta b E X ω‖ ≤ (1 + qPoly ((1 - b) * κ / 4) ω *
      ‖layerAt E (boundaryZ b E) X ω‖) * qPoly ((1 - b) * κ / 4) ω := by
  set η₀ := (1 - b) * κ / 4
  set z := boundaryZ b E
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  have hEE := hE
  obtain ⟨hE1', hE2'⟩ := hEE
  obtain ⟨hw1, hw2, -, -⟩ := disk_bounds hb0 hb hκ hE
    (boundaryZ_mem_paramDisk (by linarith) (by linarith) (by linarith))
  have hw : 0 < z.im := lt_of_lt_of_le hη₀ hw1
  obtain ⟨hk, hd⟩ := right_letters_le E hw hY hA hB
  have hEabs : |E| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hwb, hinv⟩ := weightBound_le (X := X) (ω := ω) hη₀ hw1 hw2 hEabs
  have hwb' : weightBound E z X ω ≤ 1 + qPoly η₀ ω * ‖layerAt E z X ω‖ := hwb
  have hv : letterVBound E z ω ≤ qPoly η₀ ω := by
    rw [letterVBound, qPoly, sq]
    have := mul_le_mul_of_nonneg_right hinv (mul_self_nonneg ‖ω.2 0 0‖)
    linarith
  have hP0 : 0 ≤ 1 + qPoly η₀ ω * ‖layerAt E z X ω‖ := (norm_nonneg _).trans (hk.trans hwb')
  rw [freshDelta_eq]
  exact hd.trans (mul_le_mul hwb' hv (letterVBound_nonneg E z ω) hP0)

/-- **`‖Δ‖ ∈ L^p`** uniformly over passive inputs. -/
theorem delta_moments (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        MomBd (freshLaw W b) (fun ω => ‖freshDelta b E X ω‖) p C := by
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
  refine ⟨CP * CQ, max W₀ 1, by positivity, fun W hW E hE X hY => ?_⟩
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hE' := hE
  obtain ⟨hE1', hE2'⟩ := hE'
  set z := boundaryZ b E
  have hzD : z ∈ paramDisk b E := boundaryZ_mem_paramDisk (by linarith) (by linarith) (by linarith)
  obtain ⟨-, hG, -, -⟩ := hM W (le_of_max_le_left hW) E hE z hzD X hY
  set μ := freshLaw W b
  have hGm : MomBd μ (fun ω => ‖layerAt E z X ω‖) (4 * p) CG :=
    ⟨(continuous_norm.measurable.comp (measurable_layerAt E z X)).aestronglyMeasurable,
      hG.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
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
  refine MomBd.mono (hP.mul hp0 hQ hCP) ((measurable_freshDelta_comp b E (X := fun _ => X)
    measurable_const measurable_id).norm.aestronglyMeasurable) ?_
  filter_upwards [ae_good W hb0 hW1] with ω hω
  rw [norm_norm]
  exact delta_pointwise hb0 hb hκ hE hY hω.1 hω.2

/-- Integrable entries and `‖EΔ‖ ≤ C`, uniformly over passive inputs. -/
theorem delta_integrable (hGA : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∀ x y, Integrable (fun ω => freshDelta b E X ω x y) (freshLaw W b)) ∧
          ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ ≤ C := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC, h⟩ := delta_moments hGA b hb0 hb κ hκ 1 le_rfl
  refine ⟨C, W₀, hC, fun W hW E hE X hY => ?_⟩
  have hm : Measurable fun ω => freshDelta b E X ω :=
    measurable_freshDelta_comp b E (X := fun _ => X) measurable_const measurable_id
  obtain ⟨hi, hle⟩ := integral_abs_pow_le (ν := freshLaw W b) (n := 1) le_rfl hC
    (by simpa using h W hW E hE X hY)
  simp only [pow_one, abs_norm] at hi hle
  have hent : ∀ x y, Integrable (fun ω => freshDelta b E X ω x y) (freshLaw W b) :=
    fun x y => hi.mono' hm.eval_matrix.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => norm_entry_le_op _ x y)
  exact ⟨hent, (norm_matrixExpect_le _ hent hi).trans hle⟩

end BlockBand.SourceProcess.FullSource
