module

public import BlockBand.Transmission.SourceMixingBulk.OneStepMean
public import BlockBand.Transmission.SourceMixing.MixingLayer
public import BlockBand.Transmission.LengthUniform.BulkMassLayer

/-!
# One fresh layer of the source-mixing recursions, uniformly on the bulk

The one-layer excess bounds `mx_layer` with constants uniform in `E ∈ bulkInterval κ` and in the
stationary jet `s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The one-layer excess bounds for `G_tr` and `G_hs`, at a fixed `p ≥ 2`.
The version of `mx_layer` with constants uniform on `bulkInterval κ` and on `s`. -/
theorem mx_layer_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) {ρ : ℝ} {p : ℝ} (hp : 2 ≤ p) :
    ∃ (C C' : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ‖thetaStar b E s‖ ≤ ρ →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (fun ω => mx_excess (mx_trG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
            (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X) ∧
        eLpNorm (fun ω => mx_excess (mx_hsG b E) ρ C b E s (X, ω)) (ENNReal.ofReal p)
            (freshLaw W b) ≤ ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X) := by
  obtain ⟨C₁, W₁, -, hC₁⟩ := oneStepMean_bulk hA hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂⟩ := oneStepFluctuation_bulk hA hb0 hb hκ p (by linarith)
  refine ⟨max C₁ 0, max C₂ 0, max (max W₁ W₂) 1, le_max_right _ _, le_max_right _ _,
    fun W hW E hEκ s hs hρ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 ≤ alphaCoef b E := by
    rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW1⟩ := hW
  set μ := freshLaw W b
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set f := passiveF b E X
  set F := freshTransportedF b E X
  set EF := matrixExpect μ F
  set θ' := thetaStar b E s / (1 + alphaCoef b E * q / W)
  set Δ := EF - θ' • f
  have hQ : Q.PosSemidef := hX.conjTranspose_mul_mul_same _
  have hq0 : 0 ≤ q := passiveMass_nonneg b E hX
  have hqtr : Q.trace.re = q := rfl
  have hθ : ‖θ'‖ ≤ ρ := by
    have := mx_norm_theta' (W := W) hρ hα hq0; simpa [θ'] using this
  have hΔ' : ‖Δ‖ * q ≤ max C₁ 0 * mx_err b E s X := by
    have h := hC₁ W hW₁ E hEκ s hs X hX
    rw [mx_jet1_eq (by linarith) h1 h2 s hX] at h
    unfold mx_err
    have he : 0 ≤ jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2 := by
      have := norm_nonneg ((W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E)
      have : 0 ≤ mx_jet1 b E s X := norm_nonneg _
      have : 0 ≤ q / W := by positivity
      unfold jetDistance0; positivity
    calc ‖Δ‖ * q ≤ (C₁ * (jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2)) * q :=
          mul_le_mul_of_nonneg_right h hq0
      _ ≤ (max C₁ 0 * (jetDistance0 b E X + mx_jet1 b E s X + q / W + (W : ℝ)⁻¹ ^ 2)) * q := by
          gcongr; exact le_max_left _ _
      _ = _ := by ring
  -- the fluctuation bound for `Z = F - EF`
  have hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (F ω - EF) v) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (max C₂ 0 / Real.sqrt W * vecNorm u * vecNorm v) := fun u v =>
    ((hC₂ W hW₂ E hEκ X hX u v).2).trans (ENNReal.ofReal_le_ofReal (by
      have := vecNorm_nonneg u; have := vecNorm_nonneg v
      gcongr; exact le_max_left _ _))
  have hB0 : 0 ≤ max C₂ 0 / Real.sqrt W := by positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]; exact ENNReal.ofReal_le_ofReal hp
  have hdec : ∀ ω, F ω = θ' • f + Δ + (F ω - EF) := fun ω => by simp only [Δ]; abel
  constructor
  · have hae := ae_traceQF_freshSchur hb0 hb hW1 h1 h2 hX
    have hbd : ∀ᵐ ω ∂μ, ‖mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω)‖ ≤
        ‖(Q * (F ω - EF)).trace‖ := by
      filter_upwards [hae] with ω hω
      have hG : mx_trG b E (freshSchur E X ω) = ‖(Q * F ω).trace‖ := by
        rw [mx_trG, hω]
      have hsplit : (Q * F ω).trace = θ' * (Q * f).trace + (Q * Δ).trace + (Q * (F ω - EF)).trace := by
        nth_rewrite 1 [hdec ω]
        rw [Matrix.mul_add, Matrix.mul_add, trace_add, trace_add, Matrix.mul_smul,
          trace_smul, smul_eq_mul]
      have h1' : ‖(Q * F ω).trace‖ ≤ ρ * mx_trG b E X + max C₁ 0 * mx_err b E s X +
          ‖(Q * (F ω - EF)).trace‖ := by
        have a1 : ‖θ' * (Q * f).trace‖ ≤ ρ * mx_trG b E X := by
          rw [norm_mul, mx_trG]; exact mul_le_mul_of_nonneg_right hθ (norm_nonneg _)
        have a2 : ‖(Q * Δ).trace‖ ≤ max C₁ 0 * mx_err b E s X :=
          (mx_trace_le hQ Δ).trans (by rw [hqtr]; exact hΔ')
        rw [hsplit]
        calc ‖θ' * (Q * f).trace + (Q * Δ).trace + (Q * (F ω - EF)).trace‖
            ≤ ‖θ' * (Q * f).trace‖ + ‖(Q * Δ).trace‖ + ‖(Q * (F ω - EF)).trace‖ :=
              (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
          _ ≤ _ := by linarith
      have hex : mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω) ≤ ‖(Q * (F ω - EF)).trace‖ := by
        unfold mx_excess
        exact max_le (norm_nonneg _) (by rw [hG]; linarith)
      have h0 : 0 ≤ mx_excess (mx_trG b E) ρ (max C₁ 0) b E s (X, ω) := le_max_left _ _
      exact (Real.norm_of_nonneg h0).trans_le hex
    refine (eLpNorm_mono_ae ((measurable_mx_excess (measurable_mx_trG b E) ρ (max C₁ 0) b E s).comp
      measurable_prodMk_left).aestronglyMeasurable hbd).trans ?_
    have := eLpNorm_trace_mul_le μ hQ (Z := fun ω => F ω - EF) hp1 hB0 hB
    rw [hqtr] at this; exact this
  · have hae := ae_hsSandwich_freshSchur hb0 hb hW1 h1 h2 hX
    have hbd : ∀ᵐ ω ∂μ, ‖mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω)‖ ≤
        ‖hsSandwich Q (F ω - EF)‖ := by
      filter_upwards [hae] with ω hω
      have hG : mx_hsG b E (freshSchur E X ω) = hsSandwich Q (F ω) := by rw [mx_hsG, hω]
      have h1' : hsSandwich Q (F ω) ≤ ρ * mx_hsG b E X + max C₁ 0 * mx_err b E s X +
          hsSandwich Q (F ω - EF) := by
        rw [show hsSandwich Q (F ω) = hsSandwich Q (θ' • f + Δ + (F ω - EF)) from
          congrArg _ (hdec ω)]
        have a1 : hsSandwich Q (θ' • f) ≤ ρ * mx_hsG b E X := by
          rw [hsSandwich_smul hQ, mx_hsG]
          exact mul_le_mul_of_nonneg_right hθ (Real.sqrt_nonneg _)
        have a2 : hsSandwich Q Δ ≤ max C₁ 0 * mx_err b E s X :=
          (hsSandwich_le_norm hQ Δ).trans (by rw [hqtr]; exact hΔ')
        have a3 := hsSandwich_add_le hQ (θ' • f + Δ) (F ω - EF)
        have a4 := hsSandwich_add_le hQ (θ' • f) Δ
        linarith
      have hex : mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω) ≤ hsSandwich Q (F ω - EF) := by
        unfold mx_excess
        exact max_le (Real.sqrt_nonneg _) (by rw [hG]; linarith)
      have h0 : 0 ≤ mx_excess (mx_hsG b E) ρ (max C₁ 0) b E s (X, ω) := le_max_left _ _
      exact (Real.norm_of_nonneg h0).trans_le (hex.trans (le_abs_self _))
    refine (eLpNorm_mono_ae ((measurable_mx_excess (measurable_mx_hsG b E) ρ (max C₁ 0) b E s).comp
      measurable_prodMk_left).aestronglyMeasurable hbd).trans ?_
    have hZ : Measurable fun ω => F ω - EF :=
      (measurable_freshTransportedF_fixed b E X).sub measurable_const
    have := eLpNorm_hsSandwich_le μ hQ hZ hp2 hB0 hB
    rw [hqtr] at this; exact this

end BlockBand.Transmission.SourceMixingBulk
