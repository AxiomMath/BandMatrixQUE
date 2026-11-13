module

public import BlockBand.Transmission.Generator.BrLayer
public import BlockBand.Transmission.Generator.BrCond

/-!
# The bracket error: almost-sure bound along the path

**`bracketError_le hGA hLp hP`**: `b, κ, k, l` first; then `K ≥ 0, W₀`; for `W ≥ W₀`, path energy
`E' ∈ bulkInterval κ`, stationary jet `s` at `E'`, base energy `E` and `r ≥ 1`, a.s.
`|bracketError b E E' W (k+1) (l+1) r| ≤ (K/√W³ + |D₀(E) - D₀(E')|(k+1)(l+1)/W)·Y_r⁶`,
`Y_r = brY b E' s X_r`. From `bracketError_ae`, `bracket_layer_bulk` and
`transmissionBracket_sub_le` (`g ≤ Y ≤ Y⁶`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

theorem brY_one_le {b E : ℝ} (s : ℂ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hg : 0 ≤ (passiveTransmission b E X).trace.re) :
    1 ≤ brY b E s X ∧ (passiveTransmission b E X).trace.re ≤ brY b E s X ^ 6 := by
  have ha : 0 ≤ (W : ℝ) * jetDistance0 b E X := mul_nonneg (Nat.cast_nonneg W) (norm_nonneg _)
  have ht : 0 ≤ Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X)) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hd : 0 ≤ (W : ℝ) * jetDistance1 b E s X := mul_nonneg (Nat.cast_nonneg W) (norm_nonneg _)
  obtain ⟨h1, h2, -⟩ := brY_ge hg ha ht hd
  refine ⟨h1, h2.trans ?_⟩
  have := pow_le_pow_right₀ h1 (show 1 ≤ 6 by norm_num)
  rwa [pow_one] at this

/-- **The bracket error, a.s. bound along the path.** -/
theorem bracketError_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (k l : ℕ) :
    ∃ (K : ℝ) (W₀ : ℕ), 0 ≤ K ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E' s → ∀ E : ℝ, ∀ r : ℕ, 1 ≤ r →
      ∀ᵐ ω ∂growthPathLaw W b, |bracketError b E E' W (k + 1) (l + 1) r ω| ≤
        (K / Real.sqrt W ^ 3 + |transportD0 b E - transportD0 b E'| *
          (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) / W) *
          brY b E' s (pathX b E' W r ω) ^ 6 := by
  obtain ⟨K, WL, hK, hL⟩ := bracket_layer_bulk hGA hLp hP hb0 hb hκ k l
  refine ⟨K, max WL 1, hK, fun W hW E' hE' s hs E r hr => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hWL, hW1⟩ := hW
  have h1 : -2 < E' := by have := hE'.1; linarith
  have h2 : E' < 2 := by have := hE'.2; linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  filter_upwards [bracketError_ae (E := E) hb0 hb h1 h2 hW1 (k := k + 1) (l := l + 1)
      (by omega) (by omega) hr, mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r]
    with ω e hX
  rw [e]
  set X := pathX b E' W r ω
  have hA := hL W hWL E' hE' s hs X hX
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  have hT1 := one_sub_passiveTransmission_posSemidef b E' X
  have hg : 0 ≤ (passiveTransmission b E' X).trace.re := (mm_trace_posSemidef hT).1
  obtain ⟨hY1, hgY⟩ := brY_one_le s hg
  have hPm : ∀ m, 1 ≤ m → 0 ≤ ((passiveTransmission b E' X) ^ m).trace.re ∧
      ((passiveTransmission b E' X) ^ m).trace.re ≤ (passiveTransmission b E' X).trace.re :=
    fun m hm => trace_pow_mem hT hT1 m hm
  have hD := transmissionBracket_sub_le (k := k + 1) (l := l + 1) (by omega) hPm
    (transportD0 b E') (transportD0 b E)
  have hB : |(transmissionBracket (transportD0 b E') (k + 1) (l + 1)
        (fun m => ((passiveTransmission b E' X) ^ m).trace.re) -
      transmissionBracket (transportD0 b E) (k + 1) (l + 1)
        (fun m => ((passiveTransmission b E' X) ^ m).trace.re)) / W| ≤
      |transportD0 b E - transportD0 b E'| * (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) / W *
        brY b E' s X ^ 6 := by
    rw [abs_div, abs_of_pos hWpos]
    rw [abs_sub_comm (transportD0 b E')] at hD
    have hc : 0 ≤ |transportD0 b E - transportD0 b E'| * (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) :=
      by positivity
    calc _ ≤ |transportD0 b E - transportD0 b E'| *
          (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) * (passiveTransmission b E' X).trace.re) / W :=
          div_le_div_of_nonneg_right hD hWpos.le
      _ = |transportD0 b E - transportD0 b E'| * (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) / W *
          (passiveTransmission b E' X).trace.re := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgY (by positivity)
  refine (abs_add_le _ _).trans ?_
  have e2 : (K / Real.sqrt W ^ 3 + |transportD0 b E - transportD0 b E'| *
      (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) / W) * brY b E' s X ^ 6 =
      K * (brY b E' s X ^ 6 / Real.sqrt W ^ 3) + |transportD0 b E - transportD0 b E'| *
        (((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ)) / W * brY b E' s X ^ 6 := by ring
  rw [e2]
  exact add_le_add hA hB

end BlockBand.Transmission.Generator
