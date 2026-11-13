module

public import BlockBand.SourceProcess.ContractingWords.InjLong

/-!
# Moments of the fresh layer used by the injection

Measure `freshLaw W b` (one fresh layer),
deterministic Hermitian `𝕏`, bulk-uniform (`C, W₀` from `b, κ, n`).

* `fresh_G_moment`: `E(1 + ‖N‖ + ‖D‖)^n ≤ C` (from `fullSourceMoments_field_holds`);
* `integrable_trace_DD`: `y ↦ Tr(D*D M)` is integrable for every fixed `M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open scoped ENNReal Matrix.Norms.L2Operator

variable {W nT nI : ℕ}

/-- `G = 1 + ‖N‖ + ‖D‖` at one fresh layer. -/
abbrev freshG (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (y : LayerSample W .oneBlockOnePort) : ℝ :=
  1 + ‖freshTransport b E XX y‖ + ‖freshD b E XX y‖

theorem measurable_freshG (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (freshG b E XX) :=
  (measurable_const.add (BlockBand.SourceProcess.FullSource.measurable_freshTransport_comp b E
    measurable_const measurable_id).norm).add
    (BlockBand.SourceProcess.FullSource.measurable_freshD_comp b E measurable_const
      measurable_id).norm

/-- **The moments of `G = 1 + ‖N‖ + ‖D‖`**, bulk-uniform. -/
theorem fresh_G_moment (hGA : GaussianAbsorptionContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        Integrable (fun y => freshG b E XX y ^ n) (freshLaw W b) ∧
          ∫ y, freshG b E XX y ^ n ∂freshLaw W b ≤ C := by
  obtain ⟨C, W₀, hC⟩ := BlockBand.SourceProcess.FullSource.fullSourceMoments_field_holds hGA b
    hb0 hb κ hκ n (by exact_mod_cast hn)
  refine ⟨(1 + 2 * max C 0) ^ n, W₀, by positivity, fun W hW E hE XX hXX => ?_⟩
  obtain ⟨hN, hD⟩ := hC W hW E hE XX hXX
  have hNm := (BlockBand.SourceProcess.FullSource.measurable_freshTransport_comp (W := W) b E
    (measurable_const (a := XX)) measurable_id).norm
  have hDm := (BlockBand.SourceProcess.FullSource.measurable_freshD_comp (W := W) b E
    (measurable_const (a := XX)) measurable_id).norm
  have hN' : eLpNorm (fun y => ‖freshTransport b E XX y‖) (ENNReal.ofReal ((1 : ℕ) * (n : ℝ)))
      (freshLaw W b) ≤ ENNReal.ofReal (max C 0) := by
    rw [Nat.cast_one, one_mul]; exact hN.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hD' : eLpNorm (fun y => ‖freshD b E XX y‖) (ENNReal.ofReal ((1 : ℕ) * (n : ℝ)))
      (freshLaw W b) ≤ ENNReal.ofReal (max C 0) := by
    rw [Nat.cast_one, one_mul]; exact hD.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hG := ContractingWords.eLpNorm_G_pow_le hNm.aestronglyMeasurable hDm.aestronglyMeasurable
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) le_rfl (by exact_mod_cast hn)
    (le_max_right C 0) hN' hD'
  simp only [pow_one] at hG
  have hMB : BlockBand.Transmission.PassiveLayer.MomBd (freshLaw W b) (freshG b E XX) n
      (1 + 2 * max C 0) := ⟨(measurable_freshG b E XX).aestronglyMeasurable, hG⟩
  obtain ⟨hI, hle⟩ := BlockBand.SourceProcess.FullSource.integral_abs_pow_le hn (by positivity) hMB
  have e : (fun y => |freshG b E XX y| ^ n) = fun y => freshG b E XX y ^ n := funext fun y => by
    rw [abs_of_nonneg (by positivity)]
  rw [e] at hI hle
  exact ⟨hI, hle⟩

theorem norm_trace_DD_le (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ‖(Dᴴ * D * M).trace‖ ≤ 2 * W * ‖M‖ * ‖D‖ ^ 2 := by
  refine (norm_trace_le_card _).trans ?_
  have h1 := norm_mul_le (Dᴴ * D) M
  have h2 : ‖Dᴴ * D‖ ≤ ‖D‖ ^ 2 := by
    calc ‖Dᴴ * D‖ ≤ ‖Dᴴ‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖D‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose, sq]
  calc 2 * (W : ℝ) * ‖Dᴴ * D * M‖ ≤ 2 * W * (‖D‖ ^ 2 * ‖M‖) := by
        gcongr; exact h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    _ = 2 * W * ‖M‖ * ‖D‖ ^ 2 := by ring

theorem integrable_trace_DD {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hG : Integrable (fun y => freshG b E XX y ^ 2) (freshLaw W b))
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Integrable (fun y => ((freshD b E XX y)ᴴ * freshD b E XX y * M).trace) (freshLaw W b) := by
  have hDm := BlockBand.SourceProcess.FullSource.measurable_freshD_comp (W := W) b E
    (measurable_const (a := XX)) measurable_id
  have hc : Continuous fun D : Matrix (Fin W) (Fin 2 × Fin W) ℂ => (Dᴴ * D * M).trace :=
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_mul
      continuous_const).matrix_trace
  refine (hG.const_mul (2 * W * ‖M‖)).mono' (hc.measurable.comp hDm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_trace_DD_le _ M).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have := norm_nonneg (freshTransport b E XX y)
  have := norm_nonneg (freshD b E XX y)
  simp only [freshG]
  nlinarith

end BlockBand.SourceProcess.ContractingWords
