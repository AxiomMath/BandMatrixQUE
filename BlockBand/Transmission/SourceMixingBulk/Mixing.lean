module

public import BlockBand.Transmission.SourceMixingBulk.MixingG
public import BlockBand.Transmission.SourceMixing.Mixing
public import BlockBand.Transmission.LengthUniform.BulkMassMoment
public import BlockBand.Transmission.Generator.DriftOneTools

/-!
# Passive source mixing, uniformly on the bulk

Proves `Generator.PassiveSourceMixingBulk`: the source-mixing bound
`‖Tr(Q_r f_r)‖_p + ‖‖Q_r^{1/2} f_r Q_r^{1/2}‖_HS‖_p ≤ C W^{-1/2}` for `εW ≤ r ≤ TW`, with `C`
uniform in `E ∈ bulkInterval κ`. The proof follows `SourceMixing.mixing_of_mass`:
* `thetaStar_le_bulk`: `‖θ_*‖ ≤ ρ_κ := b/(b + kGap b κ) < 1` for every `E ∈ bulkInterval κ` and
  every stationary jet `s` at `E` (`|θ_*| = b/|1 + k₋s|`, `|1 + k₋s| ≥ 1 - |k₋|d_* ≥ b + kGap`,
  `PathScalar.bulk_kMinus`). This replaces the fixed-`E` ratio `max |θ_*| ½`.
* `Λ = η_L⁻¹ + 1/((1-b)κ)` majorizes `η⁻¹ + |c₀|`, so `G ≤ Λq` uniformly.
* `mx_G_final_bulk` (proved in the sibling module) for `G = |Tr(Qf)|` and `G = ‖Q^{1/2}fQ^{1/2}‖_HS`, with the excess bounds
  `mx_layer_bulk`, the mass moments `LengthUniform.massMomentBound_bulk` and the jet moments
  `LengthUniform.passiveJetMomentsUniform_of (deltaZeroLengthUniform_holds …)`.
* The stationary jet at `E` is `PassiveCovariance.stationaryJet_exists`; constants do not depend
  on it (every bound above is uniform in `s` with `‖s‖ ≤ d_*`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

/-- Uniform contraction ratio: `‖θ_*‖ ≤ b/(b + kGap b κ)` on the bulk, at every stationary
jet. -/
theorem thetaStar_le_bulk {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {s : ℂ} (hs : IsStationaryJet b E s) :
    ‖thetaStar b E s‖ ≤ b / (b + kGap b κ) := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hg := kGap_pos hb0 hb hκ
  have hk := bulk_kMinus hb0 hb hκ hE
  have hl := jet_denom_lower (b := b) (E := E) s hs.2
  have hden : b + kGap b κ ≤ ‖1 + kMinus b E * s‖ := by linarith only [hk, hl]
  rw [thetaStar, norm_div, norm_mul, norm_pow, norm_matchedA E h1 h2, Complex.norm_real,
    Real.norm_of_nonneg hb0.le, one_pow, mul_one]
  exact div_le_div_of_nonneg_left hb0.le (by linarith only [hb0, hg]) hden

theorem rhoBulk_lt_one {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) :
    b / (b + kGap b κ) < 1 := by
  have hg := kGap_pos hb0 hb hκ
  rw [div_lt_one (by linarith only [hb0, hg])]; linarith only [hg]

/-- **`Generator.PassiveSourceMixingBulk`**, from the input hypotheses `MatchedTracesContract`,
`GaussianAbsorptionContract` and `GaussianLpGradient`.
-/
theorem passiveSourceMixingBulk_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    Generator.PassiveSourceMixingBulk := by
  intro b hb0 hb κ ε T p hκ hε _ hp
  set ρ := max (b / (b + kGap b κ)) (1 / 2)
  have hρ1 : ρ < 1 := max_lt (rhoBulk_lt_one hb0 hb hκ) (by norm_num)
  have hθρ : ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s → ‖thetaStar b E s‖ ≤ ρ :=
    fun E hE s hs => (thetaStar_le_bulk hb0 hb hκ hE hs).trans (le_max_left _ _)
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  set p' := max p 2
  have hp' : 1 ≤ p' := hp.trans (le_max_left _ _)
  obtain ⟨C, C', W₁, hC, hC', hL⟩ := mx_layer_bulk hA hb0 hb hκ (ρ := ρ)
    (le_max_right p 2)
  have hJet := LengthUniform.passiveJetMomentsUniform_of
    (LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp) hGA hLp
  have hMass := fun q (hq : 1 ≤ q) => LengthUniform.massMomentBound_bulk hMT hGA hLp hb0 hb hκ q hq
  have hl := etaLow_pos (b := b) (by linarith) hκ
  have h1b : 0 < 1 - b := by linarith
  set Λ := (etaLow b κ)⁻¹ + 1 / ((1 - b) * κ)
  have hΛ : 0 ≤ Λ := by positivity
  have hfq : ∀ E ∈ bulkInterval κ, ∀ (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ),
      (passiveY X).PosSemidef →
      ‖passiveF b E X‖ * (passiveQ b E X).trace.re ≤ Λ * passiveMass b E X := fun E hE W X hX => by
    obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
    have hF : ‖passiveF b E X‖ ≤ Λ := (SourceMixing.norm_passiveF_le hb0 hb h1 h2 hX).trans
      (add_le_add (inv_etaZ_le_bulk hb hκ hE) (PassiveLayer.norm_cZero_le hb hκ hE))
    exact mul_le_mul_of_nonneg_right hF (passiveMass_nonneg b E hX)
  obtain ⟨Ct, Wt, hCt, ht⟩ := mx_G_final_bulk hb0 hb hκ (fun E W => mx_trG (W := W) b E)
    (fun E _ => measurable_mx_trG b E) (fun E _ X => mx_G_nonneg_tr b E X) hΛ
    (fun E hE W X hX => (mx_trace_le (hX.conjTranspose_mul_mul_same _) _).trans (hfq E hE W X hX))
    (le_max_right _ _) hρ1 hp' hC hC'
    (fun W hW E hE s hs hθ X hX => (hL W hW E hE s hs hθ X hX).1) hMass hJet (T := T) hε
  obtain ⟨Ch, Wh, hCh, hh⟩ := mx_G_final_bulk hb0 hb hκ (fun E W => mx_hsG (W := W) b E)
    (fun E _ => measurable_mx_hsG b E) (fun E _ X => mx_G_nonneg_hs b E X) hΛ
    (fun E hE W X hX => (hsSandwich_le_norm (hX.conjTranspose_mul_mul_same _) _).trans
      (hfq E hE W X hX))
    (le_max_right _ _) hρ1 hp' hC hC'
    (fun W hW E hE s hs hθ X hX => (hL W hW E hE s hs hθ X hX).2) hMass hJet (T := T) hε
  refine ⟨Ct + Ch, max Wt Wh, fun W hW E hE r hr1 hr2 => ?_⟩
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  obtain ⟨s, hs⟩ := stationaryJet_exists hb0 hb h1 h2
  have hmono : ENNReal.ofReal p ≤ ENNReal.ofReal p' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have a1 := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans
    (ht W (le_trans (le_max_left _ _) hW) E hE s hs (hθρ E hE s hs) r hr1 hr2)
  have a2 := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans
    (hh W (le_trans (le_max_right _ _) hW) E hE s hs (hθρ E hE s hs) r hr1 hr2)
  simp only [mx_trG] at a1
  rw [eLpNorm_norm (fun ω => (passiveQ b E (pathX b E W r ω) *
    passiveF b E (pathX b E W r ω)).trace)
    ((measurable_traceQF b E).comp (PathJet.measurable_pathX b E r)).aestronglyMeasurable] at a1
  rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add a1 a2

/-- `passiveSourceMixingBulk_holds` has the type `Generator.PassiveSourceMixingBulk`. -/
example (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : Generator.PassiveSourceMixingBulk :=
  passiveSourceMixingBulk_holds hMT hGA hLp

end BlockBand.Transmission.SourceMixingBulk
