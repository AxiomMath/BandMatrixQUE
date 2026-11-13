module

public import BlockBand.Transmission.SourceMixingBulk.WordRegX
public import BlockBand.Transmission.SourceMixing.OneStepMean

/-!
# The one-step mean, uniformly on the bulk

The one-step mean estimate `oneStepMean_holds` with constants uniform in `E ∈ bulkInterval κ` and
in the stationary jet `s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

/-- The one-step mean estimate, uniformly on the bulk.
The version of `oneStepMean_holds` for its `∀ s` clause, with constants uniform on
`bulkInterval κ` and on `s`. -/
theorem oneStepMean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
          (passiveY X).PosSemidef →
          ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
              (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
            C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
              (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨C, W₀, hC0, hC⟩ := oneStepMean_strict_bulk hA hb0 hb hκ
  obtain ⟨W₁, hT⟩ := tendsto_transportedF_regX_bulk hA hb0 hb hκ
  refine ⟨C, max W₀ W₁, hC0, fun W hW E hEκ s hs X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
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
  have hL := ((hT W (le_trans (le_max_right _ _) hW) E hEκ X hX).sub (hθd.smul hf)).norm
  have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + jetDistance1 b E s (Xn n) +
      passiveMass b E (Xn n) / W + (W : ℝ)⁻¹ ^ 2)) atTop
      (𝓝 (C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
        (W : ℝ)⁻¹ ^ 2))) :=
    ((((tendsto_jet0_regX hb0 hb h1 h2 hX).add (tendsto_jet1_regX hb0 hb h1 h2 hX s)).add
      (tq.div_const _)).add_const _).const_mul _
  refine le_of_tendsto_of_tendsto' hL hR fun n => ?_
  exact hC W (le_trans (le_max_left _ _) hW) E hEκ s hs (Xn n) (passiveY_regX_posDef hX n)

end BlockBand.Transmission.SourceMixingBulk
