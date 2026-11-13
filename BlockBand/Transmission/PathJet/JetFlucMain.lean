module

public import BlockBand.Transmission.PathJet.JetFluc
public import BlockBand.Transmission.PathScalar.MeanStepLimit

/-!
# `PassiveJetFluctuationStep`: the `C_p/W` fluctuation of the fresh jet

For a deterministic passive `X` and one fresh one-port layer, the fresh jet
`freshJet b E X = ∂_w W⁻¹Tr(w - X₊)⁻¹ |_{w = z_∂}` (so that
`jetDistance1 b E s X₊ = ‖freshJet - s‖`, `jetDistance1_freshSchur`) satisfies

`‖freshJet - E freshJet‖_{L^p(freshLaw)} ≤ C_p/W`,

uniformly in passive `X` and `E ∈ bulkInterval κ`
(`passiveJetFluctuationStep_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)`).

Proof: `freshJet = -W⁻¹Tr R₊² = -τ₂(𝒢)` a.s. (`freshJet_ae_eq`:
`deriv_normTrace_resolvent` and `ae_g22_eq_Rplus`). For `regX X ε` the Gaussian `L^p`
gradient inequality and `grad_tau2_reg` give `C₀√p · 2√8/W · ‖‖𝒢‖³‖_p`; the moments at `4p`
bound `‖‖𝒢‖³‖_p ≤ C_m³`; `ε ↓ 0` with the Fatou lemma `eLpNorm_centered_le_of_tendsto`.
This is the proof of `passiveFluctuationStep_holds` with the cubic word `GP₂GP₂G` in place of
`GP₂G`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- The fresh jet `∂_w W⁻¹Tr(w - X₊)⁻¹` at `w = z_∂(E)`, `X₊ = freshSchur E X ω` held fixed. -/
def freshJet (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℂ :=
  deriv (fun w : ℂ => (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E X ω)⁻¹).trace)
    (boundaryZ b E)

theorem jetDistance1_freshSchur (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    jetDistance1 b E s (freshSchur E X ω) = ‖freshJet b E X ω - s‖ := rfl

theorem trace_g22_sq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (g22 E w X ω * g22 E w X ω).trace = (pTwo W * layerAt E w X ω * pTwo W * layerAt E w X ω).trace := by
  rw [g22_eq_iota, pTwo]
  set G := layerAt E w X ω
  set ι := iota2 W
  rw [show ι * G * ιᴴ * (ι * G * ιᴴ) = ι * (G * ιᴴ * ι * G * ιᴴ) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm ι]
  rw [show ιᴴ * ι * G * (ιᴴ * ι) * G = ιᴴ * ι * (G * ιᴴ * ι * G) by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm (ιᴴ * ι)]
  simp only [Matrix.mul_assoc]

/-- `freshJet = -τ₂(𝒢)` almost surely. -/
theorem freshJet_ae_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (h1 : -2 < E)
    (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, freshJet b E X ω = -tau2Layer E (boundaryZ b E) X ω := by
  have hzim : 0 < (boundaryZ b E).im := Bridge.boundaryZ_im_pos (by linarith) h1 h2
  filter_upwards [ae_g22_eq_Rplus hb0 hb hW E hzim hY, PathScalar.ae_layer_herm b] with ω hω hA
  rw [freshJet, deriv_normTrace_resolvent hb0 hb h1 h2 (PathScalar.passiveY_freshSchur E hY ω hA),
    tau2Layer, tau2Map, ← trace_g22_sq, hω]
  rfl

/-- **Passive jet fluctuation step**: `‖freshJet - E freshJet‖_p ≤ C/W` for every passive `X`,
uniformly on `bulkInterval κ`. -/
def PassiveJetFluctuationStep : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => ‖freshJet b E X ω - ∫ ω', freshJet b E X ω' ∂freshLaw W b‖)
          (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (C / W)

theorem tendsto_tau2Layer_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    Tendsto (fun n : ℕ => tau2Layer E w (regX X (epsN n)) ω) atTop (𝓝 (tau2Layer E w X ω)) :=
  (continuous_tau2Map.tendsto _).comp (tendsto_layerAt_reg E w X ω hu)

theorem passiveJetFluctuationStep_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : PassiveJetFluctuationStep := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨Cm', W₀m, hm⟩ := moments_holds hGA b hb0 hb κ hκ (2 * (2 * p)) (by linarith)
  set Cm := max Cm' 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  refine ⟨2 * (C₀ * Real.sqrt p) * (2 * Real.sqrt 8) * (Cm * (Cm * Cm)), max W₀m 1, by positivity, ?_⟩
  intro W hW E hE X hY
  have hWm : W₀m ≤ W := le_of_max_le_left hW
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hz := boundaryZ_mem_paramDisk (b := b) (by linarith) hE1 hE2
  have hzim : 0 < (boundaryZ b E).im := Bridge.boundaryZ_im_pos (by linarith) hE1 hE2
  set z := boundaryZ b E
  have hpass : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      MemLp (tau2Layer E z X') (ENNReal.ofReal p) (freshLaw W b) ∧
      eLpNorm (tau2Layer E z X') (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (2 * (Cm * Cm)) ∧
      eLpNorm (fun ω => ‖layerAt E z X' ω‖ ^ 3) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (Cm * (Cm * Cm)) := by
    intro X' hY'
    have hg4 := (letter_momBd (hm W hWm E hE z hz X' hY').2).1
    have hg2 := hg4.exponent_mono (show 2 * p ≤ 2 * (2 * p) by linarith)
    have hsq := MomBd.mul (by linarith : (0 : ℝ) < 2 * p) hg4 hg4 hCm
    have hsqp := hsq.exponent_mono (show p ≤ 2 * p by linarith)
    have hcube := MomBd.mul hp0 hg2 hsq hCm
    have hτm := (measurable_tau2Layer (W := W) E z X').aestronglyMeasurable (μ := freshLaw W b)
    have hτ : eLpNorm (tau2Layer E z X') (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (2 * (Cm * Cm)) := by
      refine (eLpNorm_mono_ae_real hτm (ae_of_all _ fun ω => ?_)).trans
        (hsqp.const_mul zero_le_two).2
      have := norm_tau2Map_le (layerAt E z X' ω)
      simpa [tau2Layer, sq] using this
    refine ⟨lt_of_le_of_lt hτ ENNReal.ofReal_lt_top, hτ, ?_⟩
    have := hcube.2
    have e : (fun ω => ‖layerAt E z X' ω‖ ^ 3) =
        fun ω => ‖layerAt E z X' ω‖ * (‖layerAt E z X' ω‖ * ‖layerAt E z X' ω‖) := by
      funext ω; ring
    rw [e]; exact this
  obtain ⟨hMem, -, -⟩ := hpass X hY
  set B := ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal (2 * Real.sqrt 8 / W) *
    ENNReal.ofReal (Cm * (Cm * Cm)))
  have hfix : ∀ n, eLpNorm (fun ω => tau2Layer E z (regX X (epsN n)) ω -
      ∫ ω', tau2Layer E z (regX X (epsN n)) ω' ∂freshLaw W b) (ENNReal.ofReal p)
        (freshLaw W b) ≤ B := by
    intro n
    obtain ⟨hMn, -, hwn⟩ := hpass _ (regX_posSemidef hY (epsN_pos n).le)
    exact (tau2_centered_reg hLp' hb0 hb hW1 E hzim hY (epsN_pos n) hp hMn).trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hwn))
  have hmean : ∀ n, ‖∫ ω', tau2Layer E z (regX X (epsN n)) ω' ∂freshLaw W b‖ ≤ 2 * (Cm * Cm) := by
    intro n
    obtain ⟨hMn, hn, -⟩ := hpass _ (regX_posSemidef hY (epsN_pos n).le)
    have h1 := (enorm_integral_le_eLpNorm hp1 hMn.aestronglyMeasurable).trans hn
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hlim : ∀ᵐ ω ∂freshLaw W b, Tendsto (fun n => tau2Layer E z (regX X (epsN n)) ω)
      atTop (𝓝 (tau2Layer E z X ω)) := by
    filter_upwards [ae_good W hb0 hW1] with ω hω
    exact tendsto_tau2Layer_reg E z X ω ((isUnit_iff_isUnit_det _).mpr
      (layer_schur E hzim hY hω.1 hω.2).1)
  have hF := eLpNorm_centered_le_of_tendsto hp1
    (fun n => (measurable_tau2Layer E z _).aestronglyMeasurable)
    (measurable_tau2Layer E z X).aestronglyMeasurable
    (hMem.integrable hp1) hlim hmean hfix
  have hae := freshJet_ae_eq hb0 hb hW1 hE1 hE2 hY
  have hcongr : (fun ω => freshJet b E X ω - ∫ ω', freshJet b E X ω' ∂freshLaw W b) =ᵐ[freshLaw W b]
      fun ω => -(tau2Layer E z X ω - ∫ ω', tau2Layer E z X ω' ∂freshLaw W b) := by
    have hi := integral_congr_ae hae
    filter_upwards [hae] with ω hω
    rw [hi, hω, integral_neg]; ring
  rw [eLpNorm_norm (f := fun ω => freshJet b E X ω - ∫ ω', freshJet b E X ω' ∂freshLaw W b),
    eLpNorm_congr_ae hcongr,
    show (fun ω => -(tau2Layer E z X ω - ∫ ω', tau2Layer E z X ω' ∂freshLaw W b)) =
      -(fun ω => tau2Layer E z X ω - ∫ ω', tau2Layer E z X ω' ∂freshLaw W b) from rfl,
    eLpNorm_neg]
  refine hF.trans (le_of_eq ?_)
  simp only [B]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  · congr 1
    ring
  all_goals exact (((measurable_tau2Layer E z X).aestronglyMeasurable.sub
    aestronglyMeasurable_const).neg).congr hcongr.symm

end BlockBand.Transmission.PathJet
