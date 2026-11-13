module

public import BlockBand.Transmission.SourceMixing.WordRegX

/-!
# The one-step mean of the transported source

Hypothesis `PassiveBoundsStatement`. Law `freshLaw W b`, deterministic passive `X` (`Y ⪰ 0`),
operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; at every stationary jet `s` the constants depend
on `b, E, s` only, uniformly in `W ≥ W₀` and `X`.

The `oneStepMean` field of `PassiveSourceMixingContract`: for every passive `X`,
`‖E F₊ - θ_*(1 + αq/W)⁻¹ f‖ ≤ C(δ₀ + δ₁ + q/W + W⁻²)`.

* `oneStepMean_holds`: the field as stated in the structure (the `example` below checks this).

Proof: `oneStepMean_strict` for `regX X n` and the limit `n → ∞` (`tendsto_transportedF_regX`,
`Continuity.tendsto_*_regX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- The `oneStepMean` field of `PassiveSourceMixingContract`. -/
theorem oneStepMean_holds (hA : PassiveBoundsStatement) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
      (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
        ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
          (passiveY X).PosSemidef →
          ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
              (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
            C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
              (W : ℝ)⁻¹ ^ 2) := by
  intro b hb0 hb E h1 h2
  refine ⟨stationaryJet_exists hb0 hb h1 h2, fun s hs => ?_⟩
  obtain ⟨C, W₀, -, hC⟩ := oneStepMean_strict hA hb0 hb h1 h2 s hs
  obtain ⟨W₁, hT⟩ := tendsto_transportedF_regX hA hb0 hb h1 h2
  refine ⟨C, max W₀ W₁, fun W hW X hX => ?_⟩
  set Xn := PassiveCovariance.regX X
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 ≤ alphaCoef b E := by
    rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  -- the denominators
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have hden : Tendsto (fun n => (1 + (alphaCoef b E : ℂ) * (passiveMass b E (Xn n) : ℂ) /
      (W : ℂ))) atTop (𝓝 (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) / (W : ℂ))) :=
    tendsto_const_nhds.add (((Complex.continuous_ofReal.tendsto _).comp tq).const_mul _ |>.div_const _)
  have hne : (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) / (W : ℂ)) ≠ 0 := by
    have hq := passiveMass_nonneg b E hX
    have e : (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) / (W : ℂ)) =
        ((1 + alphaCoef b E * passiveMass b E X / W : ℝ) : ℂ) := by push_cast; ring
    rw [e]; exact_mod_cast (show (0 : ℝ) < 1 + alphaCoef b E * passiveMass b E X / W by positivity).ne'
  have hθd := (tendsto_const_nhds (x := thetaStar b E s)).div hden hne
  have hf : Tendsto (fun n => passiveF b E (Xn n)) atTop (𝓝 (passiveF b E X)) :=
    (tendsto_res_regX hb0 hb h1 h2 hX).sub tendsto_const_nhds
  have hL := ((hT W (le_trans (le_max_right _ _) hW) X hX).sub (hθd.smul hf)).norm
  have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + jetDistance1 b E s (Xn n) +
      passiveMass b E (Xn n) / W + (W : ℝ)⁻¹ ^ 2)) atTop
      (𝓝 (C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
        (W : ℝ)⁻¹ ^ 2))) :=
    ((((tendsto_jet0_regX hb0 hb h1 h2 hX).add (tendsto_jet1_regX hb0 hb h1 h2 hX s)).add
      (tq.div_const _)).add_const _).const_mul _
  refine le_of_tendsto_of_tendsto' hL hR fun n => ?_
  exact hC W (le_trans (le_max_left _ _) hW) (Xn n) (passiveY_regX_posDef hX n)

example (hA : PassiveBoundsStatement) (h : PassiveSourceMixingContract) :
    PassiveSourceMixingContract :=
  { h with oneStepMean := oneStepMean_holds hA }

end BlockBand.Transmission.SourceMixing
