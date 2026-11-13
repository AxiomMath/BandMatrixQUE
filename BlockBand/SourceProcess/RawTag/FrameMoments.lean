module

public import BlockBand.SourceProcess.RawTag.FrameAlgebra
public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# Moments of the boundary frames `𝒰*ξ`

`momBd_frame`: under `FullSourceMomentsEnergyUniformContract`, the boundary frames of unit tags
have bounded `L^r` moments (`r ≥ 2`), uniformly in `β < l ≤ TW`, in `W` and in the bulk energy.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ENNReal

theorem measurable_tagTrace (b E : ℝ) (W l β : ℕ) :
    Measurable fun ω : GrowthPath W => (W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace := by
  have hU : Measurable (boundaryToInterior b E W l) :=
    Measurable.of_eval_matrix _ fun _ _ =>
      (BlockBand.SourceProcess.FullSourceStops.measurable_fullInverse b E l).eval_matrix
  have hY : Measurable (tagResponse b E W l β) :=
    BlockBand.Transmission.Bridge.measurable_matrix_mul'
      (BlockBand.Transmission.Bridge.measurable_matrix_mul'
        (BlockBand.Transmission.Bridge.measurable_matrix_conjTranspose' hU) measurable_const) hU
  simp only [Matrix.trace, Matrix.diag]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hY.eval_matrix)

/-- **Frame moments** (uniform in `β < l ≤ TW` and bulk `E`). -/
theorem momBd_frame (hFS : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (T : ℝ) {r : ℝ} (hr : 2 ≤ r) :
    ∃ (A : ℝ) (W₀ : ℕ), 0 ≤ A ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ l β : ℕ, β < l →
      (l : ℝ) ≤ T * W → ∀ (Γ : Type) [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
      (g : Γ → Fin W → ℂ), Measurable g → ν.map g = circularVectorLaw (Fin W) →
        MomBd ((growthPathLaw W b).prod ν) (fun w => vecNorm (frame b E W l β w.1 (g w.2))) r
          A := by
  have hr0 : 0 < r := by linarith
  have hr2 : 1 ≤ r / 2 := by linarith
  obtain ⟨C, W₀, h⟩ := hFS.tag b hb0 hb κ 0 T (r / 2) hκ hr2
  set M := 2 * gaussMoment r
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (gaussMoment_nonneg r)
  set C' := max C 0
  refine ⟨(M * C' ^ (r / 2)) ^ (1 / r), W₀, by positivity, fun W hW E hE l β hβ hl Γ _ ν _ g hg
    hlaw => ?_⟩
  have hfm : Measurable fun w : GrowthPath W × Γ => vecNorm (frame b E W l β w.1 (g w.2)) := by
    have := measurable_frame (W := W) b E l β measurable_fst (hg.comp measurable_snd)
    unfold vecNorm; fun_prop
  refine MomBd.of_lintegral hfm.aestronglyMeasurable hr0 (by positivity) ?_
  -- the tag clause as a moment bound
  have htag := h W hW E hE E (by simp [IsNearEnergy]) l hl β hβ
  have hmom : MomBd (growthPathLaw W b) (fun ω => ‖(W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace‖)
      (r / 2) C' :=
    ⟨(measurable_tagTrace b E W l β).norm.aestronglyMeasurable,
      by
        rw [eLpNorm_norm]
        · exact htag.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        · exact (measurable_tagTrace b E W l β).aestronglyMeasurable⟩
  have hout := lintegral_rpow_le_of_momBd hmom (by linarith) (le_max_right _ _)
  -- the Gaussian integral at fixed path
  have hin : ∀ ω : GrowthPath W, ∫⁻ γ, ‖vecNorm (frame b E W l β ω (g γ))‖ₑ ^ r ∂ν ≤
      ENNReal.ofReal M * ENNReal.ofReal
        (|‖(W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace‖| ^ (r / 2)) := by
    intro ω
    have hFm : Measurable fun g' : Fin W → ℂ => ‖vecNorm (frame b E W l β ω g')‖ₑ ^ r := by
      have := measurable_frame (W := W) b E l β (measurable_const (a := ω)) measurable_id
      unfold vecNorm; fun_prop
    rw [← lintegral_map hFm hg, hlaw]
    have e : ∀ g' : Fin W → ℂ, ‖vecNorm (frame b E W l β ω g')‖ₑ ^ r =
        ENNReal.ofReal (((W : ℝ)⁻¹) ^ (r / 2)) *
          ENNReal.ofReal ((∑ c, ‖(tagRows b E W l β ω *ᵥ g') c‖ ^ 2) ^ (r / 2)) := by
      intro g'
      rw [Real.enorm_eq_ofReal (vecNorm_nonneg _), ENNReal.ofReal_rpow_of_nonneg
        (vecNorm_nonneg _) hr0.le, norm_frame_rpow, ENNReal.ofReal_mul (by positivity)]
    simp_rw [e]
    rw [lintegral_const_mul _ (by fun_prop)]
    have hK := lintegral_normSq_rpow_le (tagRows b E W l β ω) hr2
    rw [show 2 * (r / 2) = r by ring] at hK
    refine (mul_le_mul_right hK _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hM]
    congr 1
    have hS0 : 0 ≤ ∑ c, ∑ a, ‖tagRows b E W l β ω c a‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have hn : ‖(W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace‖ =
        (W : ℝ)⁻¹ * ∑ c, ∑ a, ‖tagRows b E W l β ω c a‖ ^ 2 := by
      rw [trace_tagResponse_eq, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hS0]
    rw [hn, abs_of_nonneg (by positivity), Real.mul_rpow (by positivity) hS0]
    ring
  calc ∫⁻ w, ‖vecNorm (frame b E W l β w.1 (g w.2))‖ₑ ^ r ∂((growthPathLaw W b).prod ν)
      = ∫⁻ ω, ∫⁻ γ, ‖vecNorm (frame b E W l β ω (g γ))‖ₑ ^ r ∂ν ∂growthPathLaw W b :=
        lintegral_prod _ (hfm.enorm.pow_const r).aemeasurable
    _ ≤ ∫⁻ ω, ENNReal.ofReal M * ENNReal.ofReal
          (|‖(W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace‖| ^ (r / 2)) ∂growthPathLaw W b :=
        lintegral_mono hin
    _ = ENNReal.ofReal M * ∫⁻ ω, ENNReal.ofReal
          (|‖(W : ℂ)⁻¹ * (tagResponse b E W l β ω).trace‖| ^ (r / 2)) ∂growthPathLaw W b :=
        lintegral_const_mul _ (by
          have := (measurable_tagTrace b E W l β).norm
          fun_prop)
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal (C' ^ (r / 2)) := mul_le_mul_right hout _
    _ = ENNReal.ofReal (M * C' ^ (r / 2)) := (ENNReal.ofReal_mul hM).symm

end BlockBand.SourceProcess.RawTag
