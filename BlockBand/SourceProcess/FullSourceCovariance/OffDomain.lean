module

public import BlockBand.SourceProcess.FullSourceCovariance.Assembly
public import BlockBand.SourceProcess.FullSourceCovariance.DeltaFlucAll
public import BlockBand.Transmission.LawClauses.JetGap

/-!
# Off-domain reduction of the two `Δ`-covariance statements

The covariance expansion works on a fixed small jet domain `δ₀ + δ₁ + g/W ≤ d`. Off it, the
error `W⁻¹(δ₀ + δ₁ + g/W) ≥ d/W` dominates the crude bound
`|Cov| + |main| ≤ (C₁ + σ₊)/W ∏‖v‖`, with `C₁` from Cauchy–Schwarz and the `L²` fluctuation of
`Δ` at every passive `X` (`deltaFluctuation_all`), and `|σ₋| < σ₊` (`norm_sigmaMinus_lt_sigmaPlus`).

* `DeltaCovarianceSameOnDomain`, `DeltaCovarianceOppositeOnDomain`: `DeltaCovarianceSame` and
  `DeltaCovarianceOpposite` with the extra hypothesis `δ₀ + δ₁ + g/W ≤ d` (`∃ d > 0` after `b, κI`).
* `deltaCovarianceSame_of_onDomain hGA hLp`, `deltaCovarianceOpposite_of_onDomain hGA hLp`.
* `fullSourceCovarianceEnergyUniform_of_onDomain hGA hLp hS hO`: the energy-uniform covariance
  statement.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The jet distance `δ₀ + δ₁ + g/W` of `X`. -/
def jetDist {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  jetDistance0 b E X + jetDistance1 b E s X + conductanceOf (passiveTransmission b E X) / W

/-- `DeltaCovarianceSame` on a jet domain `δ₀ + δ₁ + g/W ≤ d`. -/
def DeltaCovarianceSameOnDomain : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            sigmaMinus b E s / W * crossedTensor x y x' y' 1 1‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- `DeltaCovarianceOpposite` on a jet domain `δ₀ + δ₁ + g/W ≤ d`. -/
def DeltaCovarianceOppositeOnDomain : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → jetDist b E s X ≤ d →
      ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y' -
            ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear x 1 x' * bilinear y' 1 y)‖ ≤
          C * covErr b E s X * fourNorm x y x' y'

/-- Cauchy–Schwarz `‖∫ fg‖ₑ ≤ ‖f‖₂‖g‖₂`. -/
theorem enorm_integral_mul_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℂ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ‖∫ ω, f ω * g ω ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  simp only [enorm_mul]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.enorm hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hg.aestronglyMeasurable]
  simpa using h

/-- **Crude bounds**: `|Cov|, |CrossCov| ≤ C₁W⁻¹‖x‖‖y‖‖x'‖‖y'‖` for every passive `X`. -/
theorem crude_delta_cov (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (C₁ : ℝ) (W₀ : ℕ), 0 ≤ C₁ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ x y x' y' : Fin W → ℂ,
        ‖bilinearCovariance (freshLaw W b) (freshDelta b E X) x y x' y'‖ ≤
            C₁ / W * fourNorm x y x' y' ∧
          ‖bilinearCrossCovariance (freshLaw W b) (freshDelta b E X) x y x' y'‖ ≤
            C₁ / W * fourNorm x y x' y' := by
  intro b hb0 hb κ hκ
  obtain ⟨C, W₀, hC⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ 2 one_le_two
  refine ⟨|C| ^ 2, max W₀ 1, sq_nonneg _, fun W hW E hE X hY x y x' y' => ?_⟩
  have hW0 : W₀ ≤ W := le_of_max_le_left hW
  have hW1 : (0 : ℝ) < W := by exact_mod_cast le_of_max_le_right hW
  set μ := freshLaw W b
  set D₀ := matrixExpect μ (freshDelta b E X)
  set β := fun (u v : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) =>
    bilinear u (freshDelta b E X ω - D₀) v
  have hm : ∀ u v, Measurable (β u v) := fun u v => by
    have hc : Continuous fun M : Matrix (Fin W) (Fin W) ℂ => bilinear u (M - D₀) v := by
      unfold bilinear; fun_prop
    exact hc.measurable.comp (measurable_freshDelta_comp b E (X := fun _ => X) measurable_const
      measurable_id)
  have hle : ∀ u v, eLpNorm (β u v) 2 μ ≤
      ENNReal.ofReal (|C| / Real.sqrt W * vecNorm u * vecNorm v) := fun u v => by
    have h := hC W hW0 E hE X hY u v
    rw [ENNReal.ofReal_ofNat] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    gcongr; exact le_abs_self C
  have hsq : ∀ u v u' v' : Fin W → ℂ,
      ENNReal.ofReal (|C| / Real.sqrt W * vecNorm u * vecNorm v) *
        ENNReal.ofReal (|C| / Real.sqrt W * vecNorm u' * vecNorm v') =
      ENNReal.ofReal (|C| ^ 2 / W * fourNorm u v u' v') := by
    intro u v u' v'
    have := vecNorm_nonneg u; have := vecNorm_nonneg v
    have := vecNorm_nonneg u'; have := vecNorm_nonneg v'
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [fourNorm, show |C| ^ 2 / (W : ℝ) = (|C| / Real.sqrt W) ^ 2 by
      rw [div_pow, Real.sq_sqrt hW1.le]]
    ring
  have hB : 0 ≤ |C| ^ 2 / W * fourNorm x y x' y' :=
    mul_nonneg (by positivity) (fourNorm_nonneg _ _ _ _)
  have fin : ∀ (I : ℂ), ‖I‖ₑ ≤ ENNReal.ofReal (|C| ^ 2 / W * fourNorm x y x' y') →
      ‖I‖ ≤ |C| ^ 2 / W * fourNorm x y x' y' := fun I h => by
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp h
  constructor
  · refine fin _ ?_
    have := enorm_integral_mul_le μ (β x y) (β x' y') (hm x y).aemeasurable
      (hm x' y').aemeasurable
    refine this.trans ((mul_le_mul' (hle x y) (hle x' y')).trans (le_of_eq (hsq _ _ _ _)))
  · refine fin _ ?_
    have hs : eLpNorm (fun ω => star (β x' y' ω)) 2 μ = eLpNorm (β x' y') 2 μ :=
      eLpNorm_star (f := β x' y')
    have := enorm_integral_mul_le μ (β x y) (fun ω => star (β x' y' ω)) (hm x y).aemeasurable
      (continuous_star.measurable.comp (hm x' y')).aemeasurable
    rw [hs] at this
    refine this.trans ((mul_le_mul' (hle x y) (hle x' y')).trans (le_of_eq (hsq _ _ _ _)))

end BlockBand.SourceProcess.FullSourceCovariance
