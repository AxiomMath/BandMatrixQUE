module

public import BlockBand.Transmission.SourceMixing.MixingG

/-!
# Source mixing from the mass moments

The `mixing` field of `PassiveSourceMixingContract`: for `0 < ε < T`, `p ≥ 1` and `εW ≤ r ≤ TW`,
`‖Tr(Q_r f_r)‖_p + ‖‖Q_r^{1/2} f_r Q_r^{1/2}‖_HS‖_p ≤ C W^{-1/2}`, deduced from the mass moment
bound `MassMomentBound`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

theorem mx_norm_thetaStar_lt {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {s : ℂ} (hs : IsStationaryJet b E s) : ‖thetaStar b E s‖ < 1 := by
  obtain ⟨-, -, hden⟩ := norm_thetaStar_le hb0 hb h1 h2 hs
  rw [thetaStar, norm_div, norm_mul, norm_pow, norm_matchedA E h1 h2, Complex.norm_real,
    Real.norm_of_nonneg hb0.le, one_pow, mul_one]
  exact (div_lt_one (by linarith)).mpr hden

/-- The `mixing` field of `PassiveSourceMixingContract`, from the mass moment bound. -/
theorem mixing_of_mass (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient)
    (hMass : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → MassMomentBound b E) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ ε T p : ℝ, 0 < ε → ε < T → 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => (passiveQ b E (pathX b E W r ω) *
            passiveF b E (pathX b E W r ω)).trace) (ENNReal.ofReal p) (growthPathLaw W b) +
          eLpNorm (fun ω => hsSandwich (passiveQ b E (pathX b E W r ω))
            (passiveF b E (pathX b E W r ω))) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W) := by
  intro b hb0 hb E h1 h2 ε T p hε _ hp
  obtain ⟨s, hs⟩ := stationaryJet_exists hb0 hb h1 h2
  have hθ1 := mx_norm_thetaStar_lt hb0 hb h1 h2 hs
  set ρ := max ‖thetaStar b E s‖ (1 / 2)
  have hρ1 : ρ < 1 := max_lt hθ1 (by norm_num)
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  set p' := max p 2
  have hp' : 1 ≤ p' := hp.trans (le_max_left _ _)
  obtain ⟨C, C', W₁, hC, hC', hL⟩ := mx_layer hA hb0 hb h1 h2 hs (le_max_left _ _ : _ ≤ ρ)
    (le_max_right p 2)
  have hJet := LengthUniform.passiveJetMomentsUniform_of
    (LengthUniform.deltaZeroLengthUniform_holds hMT hGA hLp) hGA hLp
  set Λ := (etaZ b E)⁻¹ + ‖cZero b E‖
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hΛ : 0 ≤ Λ := by positivity
  have hfq : ∀ (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ), (passiveY X).PosSemidef →
      ‖passiveF b E X‖ * (passiveQ b E X).trace.re ≤ Λ * passiveMass b E X := fun W X hX =>
    mul_le_mul_of_nonneg_right (norm_passiveF_le hb0 hb h1 h2 hX) (passiveMass_nonneg b E hX)
  obtain ⟨Ct, Wt, hCt, ht⟩ := mx_G_final hb0 hb h1 h2 s (fun W => mx_trG (W := W) b E)
    (fun _ => measurable_mx_trG b E) (fun _ X => mx_G_nonneg_tr b E X) hΛ
    (fun W X hX => (mx_trace_le (hX.conjTranspose_mul_mul_same _) _).trans (hfq W X hX))
    (le_max_right _ _) hρ1 hp' hC hC' (fun W hW X hX => (hL W hW X hX).1)
    (hMass b hb0 hb E h1 h2) hJet hs (T := T) hε
  obtain ⟨Ch, Wh, hCh, hh⟩ := mx_G_final hb0 hb h1 h2 s (fun W => mx_hsG (W := W) b E)
    (fun _ => measurable_mx_hsG b E) (fun _ X => mx_G_nonneg_hs b E X) hΛ
    (fun W X hX => (hsSandwich_le_norm (hX.conjTranspose_mul_mul_same _) _).trans (hfq W X hX))
    (le_max_right _ _) hρ1 hp' hC hC' (fun W hW X hX => (hL W hW X hX).2)
    (hMass b hb0 hb E h1 h2) hJet hs (T := T) hε
  refine ⟨Ct + Ch, max Wt Wh, fun W hW r hr1 hr2 => ?_⟩
  have hmono : ENNReal.ofReal p ≤ ENNReal.ofReal p' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have a1 := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans
    (ht W (le_trans (le_max_left _ _) hW) r hr1 hr2)
  have a2 := (eLpNorm_le_eLpNorm_of_exponent_le hmono).trans
    (hh W (le_trans (le_max_right _ _) hW) r hr1 hr2)
  simp only [mx_trG] at a1
  rw [eLpNorm_norm (fun ω => (passiveQ b E (pathX b E W r ω) *
    passiveF b E (pathX b E W r ω)).trace)
    ((measurable_traceQF b E).comp (PathJet.measurable_pathX b E r)).aestronglyMeasurable] at a1
  rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add a1 a2

example (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient)
    (hMass : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → MassMomentBound b E)
    (h : PassiveSourceMixingContract) : PassiveSourceMixingContract :=
  { h with mixing := mixing_of_mass hMT hGA hLp hMass }

end BlockBand.Transmission.SourceMixing
