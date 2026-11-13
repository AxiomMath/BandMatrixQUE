module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.Transmission.PassiveCovariance.StationaryJet

/-!
# The noncancellation gap `|σ₋| < σ₊` (`TransmissionLawContract.jetGap`)

For `0 < b < 1/2` and `-2 < E < 2`, a stationary jet exists and every stationary jet `s`
satisfies `|σ₋(s)| < σ₊` (`norm_sigmaMinus_lt_sigmaPlus`); the proof bounds
`|σ₋(s)| = K/|1 + k₋s|` by `K/(1 - K d_*)`, `K = |k₋|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.PassiveCovariance

/-- `|σ₋(s)| < σ₊` at every stationary jet. -/
theorem norm_sigmaMinus_lt_sigmaPlus {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) : ‖sigmaMinus b E s‖ < sigmaPlus b := by
  set K := ‖kMinus b E‖
  have hK := norm_kMinus_lt b E hb0 hb h1 h2
  have hm := jet_margin_gt hb0 hb h1 h2
  have hlow := jet_denom_lower (b := b) (E := E) s hs.2
  have h1b : 0 < 1 - b := by linarith
  have hmpos : 0 < 1 - K * dStar b := lt_trans hb0 hm
  have hD : 0 < ‖1 + kMinus b E * s‖ := lt_of_lt_of_le hmpos hlow
  rw [sigmaMinus, norm_div, sigmaPlus, kPlus]
  -- `K/|1+k₋s| ≤ K/m < k/b`
  have hstep : K / ‖1 + kMinus b E * s‖ ≤ K / (1 - K * dStar b) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hmpos hlow
  refine lt_of_le_of_lt hstep ?_
  rw [div_lt_div_iff₀ hmpos hb0]
  have hd : (1 - 2 * b + b ^ 2) * dStar b = 1 - b := by
    rw [dStar]; field_simp; ring
  nlinarith

/-- **`TransmissionLawContract.jetGap`**, with exactly the field type. -/
theorem jetGap : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧
      ∀ s : ℂ, IsStationaryJet b E s → ‖sigmaMinus b E s‖ < sigmaPlus b :=
  fun _ hb0 hb _ h1 h2 =>
    ⟨stationaryJet_exists hb0 hb h1 h2, fun _ hs => norm_sigmaMinus_lt_sigmaPlus hb0 hb h1 h2 hs⟩

end BlockBand.Transmission.LawClauses
