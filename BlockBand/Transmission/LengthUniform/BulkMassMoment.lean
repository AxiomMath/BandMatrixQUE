module

public import BlockBand.Transmission.SourceMixing.Conductance
public import BlockBand.Transmission.LengthUniform.BulkMassLayer

/-!
# Bulk-uniform, length-uniform mass moments

The moments of the passive mass `q_r` along the growth path are bounded by a constant free of the
total length `T`, uniformly in `E ∈ bulkInterval κ` (`massMomentBound_bulk`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- `qc ≤ (4η_L)⁻¹ W` on the bulk interval. -/
theorem qc_le_bulk {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (X : Matrix (Fin W) (Fin W) ℂ) :
    qc b E X ≤ (4 * etaLow b κ)⁻¹ * W := by
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  have hηle : etaLow b κ ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  have := qc_le (b := b) (by linarith) h1 h2 X
  rw [div_eq_inv_mul] at this
  exact this.trans (mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by linarith))
    (Nat.cast_nonneg W))

/-- **The `T`-free mass moment bound, uniform on `bulkInterval κ`.** -/
theorem massMomentBound_bulk (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => passiveMass b E (pathX b E W r ω)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (K * (1 + W / r)) := by
  set n := ⌈p⌉₊
  have hpn : p ≤ n := Nat.le_ceil p
  have hn : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := hp.trans hpn
    exact_mod_cast this
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨c, D₁, D₂, W₁, hc, hD₁, hD₂, hstep⟩ := massLayer_step_bulk hA hb0 hb hκ n hn
  obtain ⟨Cδ, hCδ, hδT⟩ := LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp b hb0 hb κ
    (((n + 1 : ℕ) : ℝ)) hκ (by norm_cast; omega)
  set ηL := etaLow b κ
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set D := D₁ + D₂ * Cδ ^ (n + 1)
  have hD : 0 ≤ D := by positivity
  obtain ⟨K', hK', hlog⟩ := logistic_bound n hn hc hD (by positivity : 0 ≤ ((4 * ηL)⁻¹) ^ n)
  refine ⟨K' ^ (n : ℝ)⁻¹, by positivity, fun T => ?_⟩
  obtain ⟨Wδ, hδW⟩ := hδT T
  refine ⟨max (max W₁ Wδ) 1, fun W hW E hE r hr1 hrT => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWδ⟩, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set P := growthPathLaw W b
  set x : ℕ → ℝ := fun r => ∫ ω, qc b E (pathX b E W r ω) ^ n ∂P
  have hx0 : ∀ r, 0 ≤ x r := fun r => integral_nonneg fun ω => pow_nonneg (qc_nonneg b E _) n
  have hx1 : x 1 ≤ ((4 * ηL)⁻¹) ^ n * (1 + W) ^ n := by
    have hbd : ∀ ω, qc b E (pathX b E W 1 ω) ^ n ≤ ((4 * ηL)⁻¹ * (1 + W)) ^ n := fun ω => by
      refine pow_le_pow_left₀ (qc_nonneg b E _) ((qc_le_bulk hb0 hb hκ hE _).trans ?_) n
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc x 1 ≤ ∫ _ω, ((4 * ηL)⁻¹ * (1 + W)) ^ n ∂P :=
          integral_mono (mm_integrable_qc (by linarith) h1 h2 n 1) (integrable_const _) hbd
      _ = ((4 * ηL)⁻¹) ^ n * (1 + W) ^ n := by
          rw [integral_const, probReal_univ, one_smul, mul_pow]
  have hrec : ∀ j, 1 ≤ j → j < ⌊T * W⌋₊ → ∀ l : ℝ, 0 ≤ l →
      x (j + 1) ≤ x j * (1 - c * l / W) + (c * l ^ (n + 1) + D) / W := by
    intro j hj hjN l hl
    have hTW : (1 : ℝ) ≤ T * W := Nat.floor_pos.mp (by omega)
    have hjT : (j : ℝ) ≤ T * W :=
      (Nat.cast_le.mpr hjN.le).trans (Nat.floor_le (by linarith))
    have hδj := hδW W hWδ E hE j hj hjT
    have hδint := mp_integral_pow_le (ae_of_all _ fun ω => (norm_nonneg _ :
      0 ≤ jetDistance0 b E (pathX b E W j ω))) (n + 1) (by omega) (by positivity) hδj
    exact mm_path_step hb0 hb h1 h2 hD₂ hW1 (fun X hX => hstep W hW₁ E hE X hX l hl) hj hδint
  have hxr := hlog (W : ℝ) hW1' x ⌊T * W⌋₊ hx0 hx1 hrec r hr1 (Nat.le_floor hrT)
  have hpn' : ENNReal.ofReal p ≤ (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hpn
  have hcongr : eLpNorm (fun ω => passiveMass b E (pathX b E W r ω)) (n : ℝ≥0∞) P =
      eLpNorm (fun ω => qc b E (pathX b E W r ω)) (n : ℝ≥0∞) P := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [mm_ae_passive (W := W) (by linarith) h1 h2 r] with ω hω
    exact (qc_eq hω).symm
  have hv : 0 ≤ 1 + (W : ℝ) / r := by positivity
  refine (eLpNorm_le_eLpNorm_of_exponent_le hpn').trans ?_
  rw [hcongr]
  refine (mp_eLpNorm_le ((measurable_qc b E).comp
    (PathJet.measurable_pathX b E r)).aestronglyMeasurable (fun ω => qc_nonneg b E _)
    (fun ω => qc_le (by linarith) h1 h2 _) n hn hxr).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Real.mul_rpow hK' (by positivity), Real.pow_rpow_inv_natCast hv (by omega)]

end BlockBand.Transmission.LengthUniform
