module

public import BlockBand.Transmission.LawForced.AbsMoments
public import BlockBand.Transmission.LawForced.RatioL1

/-!
# The absorbed ratio drift error in `L¹` at one length

**`ratioDriftError_abs_L1 hMT hGA hLp hP hJ hMix`** (`hJ`, `hMix`:
`AbsorbedJetMoments`, `AbsorbedSourceMixingBulk`): for an admissible profile `κ`, a chamber
point `z` and `0 < ε < T`, `∃ C W₀`, for `W ≥ W₀`, `E ∈ bulkInterval κ_I`, `1 ≤ r`,
`εW ≤ r ≤ TW`:
`E|ratioDriftError b E κ W z r| ≤ C·W^{-3/2} + R·|h(r/W)/W − 4ηd_*ε_rW|`,
`ε_r = κ((r+1)/W)/W²`. The last term is the time shift `h(r/W)` vs `h((r+1)/W)`
(`4ηd_*κ = h`, `absorptionRate_eq_injection`); it is summed in `AbsSum`.
Proof: `ratioDriftError_abs_ae`, `abs_layer_bulk`, `ratioP_absorb_le`, `prod27_le`,
`abs_moments`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PathScalar BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.Generator BlockBand.Transmission.Bridge
open BlockBand.Transmission.LawDuality BlockBand.Transmission.LawFinite
open scoped ENNReal ComplexOrder

variable {p W : ℕ}

theorem pow27_le_atoms {c P x y z w : ℝ} (hc : 0 ≤ c) (hP0 : 0 ≤ P) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hw : 0 ≤ w) (hle : P ≤ c * (x ^ 2 * y * z * w)) :
    P ^ 27 ≤ c ^ 27 * ((x ^ 2) ^ 108 + y ^ 108 + z ^ 108 + w ^ 108) := by
  have h27 := pow_le_pow_left₀ hP0 hle 27
  rw [mul_pow] at h27
  exact h27.trans (mul_le_mul_of_nonneg_left (prod27_le (pow_nonneg hx 2) hy hz hw)
    (pow_nonneg hc 27))

theorem ratioP_pow_le_atoms {b E : ℝ} {κ : ℝ → ℝ} {s : ℂ} {r : ℕ} {ω : GrowthPath W} {c P : ℝ}
    (hc : 0 ≤ c) (hP0 : 0 ≤ P) (hX : (passiveY (pathNearSchur b E κ W r ω)).PosSemidef)
    (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    (hle : P ≤ c * (((passiveTransmission b E (pathNearSchur b E κ W r ω)).trace.re + 1) ^ 2 *
      (W * jetDistance0 b E (pathNearSchur b E κ W r ω) + 1) *
      Absorbed.mixM3 b E (pathNearSchur b E κ W r ω) *
      (W * jetDistance1 b E s (pathNearSchur b E κ W r ω) + 1))) :
    P ^ 27 ≤ c ^ 27 * absAtoms b E κ s W r ω := by
  have hg := (mm_trace_posSemidef (passiveTransmission_posSemidef hb h1 h2 hX)).1
  have j0 : 0 ≤ jetDistance0 b E (pathNearSchur b E κ W r ω) := norm_nonneg _
  have j1 : 0 ≤ jetDistance1 b E s (pathNearSchur b E κ W r ω) := norm_nonneg _
  have hs : 0 ≤ hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
      (passiveF b E (pathNearSchur b E κ W r ω)) := Real.sqrt_nonneg _
  have hm : 0 ≤ Absorbed.mixM3 b E (pathNearSchur b E κ W r ω) := by
    unfold Absorbed.mixM3; positivity
  unfold absAtoms
  exact pow27_le_atoms hc hP0 (by positivity) (by positivity) hm (by positivity) hle

/-- **`L¹` bound of the absorbed ratio drift error at one length.** -/
theorem ratioDriftError_abs_L1 (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) (hJ : Absorbed.AbsorbedJetMoments)
    (hMix : Absorbed.AbsorbedSourceMixingBulk) {b κI ε T : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκI : 0 < κI) (hε : 0 < ε) (hεT : ε < T) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ)
    {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ r : ℕ, 1 ≤ r →
      ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫ ω, |ratioDriftError b E κ W z r ω| ∂growthPathLaw W b ≤
          C * (Real.sqrt W)⁻¹ ^ 3 + (∑ i, (z.1 i + z.2 i)) *
            |absorptionRate E κ ((r : ℝ) / W) / W -
              4 * etaZ b E * dStar b * layerAbsorption W κ (r + 1) 0 * W| := by
  obtain ⟨K, hKb⟩ := hκ.2.2
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  obtain ⟨C₁, W₁, hC₁, hlay⟩ := abs_layer_bulk hGA hLp hP hb0 hb hκI hz hK0
  obtain ⟨M, W₂, hM⟩ := abs_moments hMT hGA hLp hJ hMix hb0 hb hκI hε hεT hκ
  have hL0 : 0 ≤ (etaLow b κI)⁻¹ := inv_nonneg.2 (etaLow_pos (by linarith) hκI).le
  have hcP : 0 ≤ Absorbed.cP (etaLow b κI)⁻¹ (max K 0) := by
    unfold Absorbed.cP; have := Absorbed.cMix_nonneg hL0 hK0; positivity
  refine ⟨C₁ * Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 * max M 0,
    max (max W₁ W₂) (max 1 ⌈max K 0 * (etaLow b κI)⁻¹⌉₊), by positivity,
    fun W hW E hE r hr1 hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hW₂⟩, hW1, hWK⟩ := hW
  have hWK' : max K 0 * (etaLow b κI)⁻¹ ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWK)
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  obtain ⟨s, hs⟩ := PassiveCovariance.stationaryJet_exists hb0 hb h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  set μ := growthPathLaw W b
  set εr := layerAbsorption W κ (r + 1) 0
  have hε0 : 0 ≤ εr := div_nonneg (hκ.2.1 _) (sq_nonneg _)
  have hεK : εr ≤ max K 0 / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right ((hKb _).trans (le_max_left _ _)) (sq_nonneg _)
  set D := (∑ i, (z.1 i + z.2 i)) * |absorptionRate E κ ((r : ℝ) / W) / W -
    4 * etaZ b E * dStar b * εr * W|
  set v := (Real.sqrt W)⁻¹
  have hv0 : 0 ≤ v := inv_nonneg.2 (Real.sqrt_nonneg _)
  obtain ⟨iA, mA⟩ := hM W hW₂ E hE s hs r hεr hrT
  set c27 := C₁ * Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 * v ^ 3
  have hc27 : 0 ≤ c27 := by positivity
  have hpt : ∀ᵐ ω ∂μ, |ratioDriftError b E κ W z r ω| ≤ c27 * absAtoms b E κ s W r ω + D := by
    filter_upwards [ratioDriftError_abs_ae hz hb0 hb h1 h2 hW1 hκ hr1,
      ae_passiveSample W hκ.2.1 hb1 h1 h2] with ω he hPs
    have hX := pathNearSchur_passive hPs r
    rw [he]
    refine (hlay W hW₁ E hE s hs _ hX εr hε0 hεK κ ((r : ℝ) / W)).trans ?_
    have hY' := passiveY_absorbedInput hX hε0
    have hg'0 := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY')).1
    have hP1 := (ratioP_facts (b := b) (E := E) s (absorbedInput (pathNearSchur b E κ W r ω) εr)
      hg'0).1
    have hle := Absorbed.ratioP_absorb_le hb0 hb hκI hK0 hE hW1 hWK' hX hε0 hεK s
    have hpow := ratioP_pow_le_atoms hcP (by linarith) hX hb1 h1 h2 hle
    have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₁ (pow_nonneg hv0 3))
    have e : c27 * absAtoms b E κ s W r ω = C₁ * (v ^ 3 *
        (Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 * absAtoms b E κ s W r ω)) := by
      simp only [c27]; ring
    have e2 : C₁ * (ratioP b E s (absorbedInput (pathNearSchur b E κ W r ω) εr) ^ 27 * v ^ 3) =
        C₁ * v ^ 3 * ratioP b E s (absorbedInput (pathNearSchur b E κ W r ω) εr) ^ 27 := by ring
    have e3 : C₁ * v ^ 3 * (Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 *
        absAtoms b E κ s W r ω) = C₁ * (v ^ 3 *
        (Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 * absAtoms b E κ s W r ω)) := by ring
    linarith
  have hEi : Integrable (fun ω => |ratioDriftError b E κ W z r ω|) μ :=
    (integrable_condExp.sub (integrable_ratioDriftAt hκ hb1 h1 h2 hz r)).abs
  have iB : Integrable (fun ω => c27 * absAtoms b E κ s W r ω + D) μ :=
    (iA.const_mul c27).add (integrable_const D)
  refine (integral_mono_ae hEi iB hpt).trans ?_
  rw [integral_add (iA.const_mul c27) (integrable_const D), integral_const_mul, integral_const,
    probReal_univ, one_smul]
  have := mul_le_mul_of_nonneg_left (mA.trans (le_max_left M 0)) hc27
  have e : C₁ * Absorbed.cP (etaLow b κI)⁻¹ (max K 0) ^ 27 * max M 0 * v ^ 3 =
      c27 * max M 0 := by simp only [c27]; ring
  linarith

end BlockBand.Transmission.LawForced
