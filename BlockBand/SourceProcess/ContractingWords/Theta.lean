module

public import BlockBand.Transmission.SourceMixing.MatchedScalars

/-!
# A uniform contraction factor `sup_{bulkInterval κ} |θ_*| < 1`

`norm_thetaStar_le` (SourceMixing) gives `|θ_*| ≤ 1` at each bulk energy. For the energy-uniform
contract one `ρ < 1` must serve every `E ∈ bulkInterval κ`: since
`|k₋|² = (1-b)⁴ - 4cb²(Im a)²` and `4(Im a)² = 4 - E² ≥ κ²` on `bulkInterval κ`,
`|k₋| ≤ K₀ := ((1-b)⁴ - cb²κ²)^{1/2} < (1-b)²`, so `|1 + k₋s| ≥ 1 - K₀d_* > b` and
`|θ_*| ≤ b/(1 - K₀d_*) =: ρ₀ < 1` (`thetaStar_bulk_bound`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.SourceMixing

theorem mem_bulk_bounds {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    -2 < E ∧ E < 2 ∧ κ ^ 2 ≤ 4 - E ^ 2 := by
  obtain ⟨h1, h2⟩ := hE
  refine ⟨by linarith, by linarith, ?_⟩
  have e : 4 - E ^ 2 = (2 - E) * (2 + E) := by ring
  rw [e, sq]
  exact mul_le_mul (by linarith) (by linarith) hκ.le (by linarith)

/-- The uniform bound `K₀` for `|k₋|` on `bulkInterval κ`. -/
def kBound (b κ : ℝ) : ℝ := Real.sqrt ((1 - b) ^ 4 - (1 - 2 * b) * b ^ 2 * κ ^ 2)

/-- The uniform contraction factor `ρ₀ = b/(1 - K₀d_*)`. -/
def thetaBound (b κ : ℝ) : ℝ := b / (1 - kBound b κ * dStar b)

theorem norm_kMinus_le_kBound {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : ‖kMinus b E‖ ≤ kBound b κ := by
  obtain ⟨h1, h2, h4⟩ := mem_bulk_bounds hκ hE
  have hsq := normSq_kMinus b E h1 h2
  rw [Complex.normSq_eq_norm_sq] at hsq
  have him : (matchedA E).im ^ 2 = (4 - E ^ 2) / 4 := by
    rw [matchedA_im, div_pow, neg_sq, sqrt_four_sub_sq E h1 h2]; norm_num
  have hc : 0 ≤ (1 - 2 * b) * b ^ 2 := by
    have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have hle : ‖kMinus b E‖ ^ 2 ≤ (1 - b) ^ 4 - (1 - 2 * b) * b ^ 2 * κ ^ 2 := by
    rw [hsq, him]
    have : (1 - 2 * b) * b ^ 2 * κ ^ 2 ≤ (1 - 2 * b) * b ^ 2 * (4 - E ^ 2) :=
      mul_le_mul_of_nonneg_left h4 hc
    nlinarith
  rw [kBound]
  calc ‖kMinus b E‖ = Real.sqrt (‖kMinus b E‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hle

theorem kBound_lt {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    kBound b κ < (1 - b) ^ 2 := by
  rw [kBound, Real.sqrt_lt' (by nlinarith)]
  have : 0 < (1 - 2 * b) * b ^ 2 * κ ^ 2 := by
    have : 0 < 1 - 2 * b := by linarith
    positivity
  nlinarith

theorem thetaBound_margin {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    b < 1 - kBound b κ * dStar b := by
  have hk := kBound_lt hb0 hb hκ
  have h1b : 0 < 1 - b := by linarith
  rw [dStar]
  have : kBound b κ * (1 / (1 - b)) < 1 - b := by
    rw [mul_one_div, div_lt_iff₀ h1b]; nlinarith
  linarith

/-- **`|θ_*| ≤ ρ₀ < 1` uniformly on `bulkInterval κ`.** -/
theorem thetaStar_bulk_bound {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    0 ≤ thetaBound b κ ∧ thetaBound b κ < 1 ∧ ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ‖thetaStar b E s‖ ≤ thetaBound b κ := by
  have hm := thetaBound_margin hb0 hb hκ
  have hmpos : 0 < 1 - kBound b κ * dStar b := lt_trans hb0 hm
  refine ⟨div_nonneg hb0.le hmpos.le, (div_lt_one hmpos).mpr hm, fun E hE s hs => ?_⟩
  obtain ⟨h1, h2, -⟩ := mem_bulk_bounds hκ hE
  obtain ⟨-, hprod, hden⟩ := norm_thetaStar_le hb0 hb h1 h2 hs
  have hd0 : 0 ≤ dStar b := by rw [dStar]; have : 0 < 1 - b := by linarith
                               positivity
  have hlow : 1 - kBound b κ * dStar b ≤ ‖1 + kMinus b E * s‖ :=
    le_trans (by nlinarith [norm_kMinus_le_kBound hb0 hb hκ hE])
      (jet_denom_lower (b := b) (E := E) s hs.2)
  have hn : ‖thetaStar b E s‖ * ‖1 + kMinus b E * s‖ = b := by
    rw [← norm_mul, hprod, norm_mul, norm_pow, norm_matchedA E h1 h2, Complex.norm_real,
      Real.norm_of_nonneg hb0.le, one_pow, mul_one]
  have hpos : 0 < ‖1 + kMinus b E * s‖ := lt_trans hb0 hden
  rw [thetaBound, le_div_iff₀ hmpos]
  calc ‖thetaStar b E s‖ * (1 - kBound b κ * dStar b)
      ≤ ‖thetaStar b E s‖ * ‖1 + kMinus b E * s‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = b := hn

end BlockBand.SourceProcess.ContractingWords
