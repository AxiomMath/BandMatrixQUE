module

public import BlockBand.Transmission.LengthUniform.DeltaZero
public import BlockBand.Transmission.PathJet.JetMomentsMain
public import BlockBand.Transmission.PathJet.JetMeanLimit
public import BlockBand.Transmission.PathJet.JetFlucMain

/-!
# Length-uniform jet moments: the recursion

`passiveJetMomentsUniform_of`: from length-uniform `δ₀` moments and the one-step jet mean and
fluctuation steps, the jet moments `PassiveJetMoments` hold with the constant chosen before the
total length `T`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PathJet
open scoped ENNReal ComplexOrder

/-- **`PassiveJetMoments` with `C` chosen before the total length `T`.** -/
def PassiveJetMomentsUniform : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ p : ℝ, 0 < κ → 1 ≤ p →
    ∃ C₁ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, 1 ≤ r → C₁ * Real.log W ≤ r →
        (r : ℝ) ≤ T * W →
          eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
              (growthPathLaw W b) +
            eLpNorm (fun ω => pathJet1 b E s W r ω) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W)

/-- The length-uniform `PassiveJetMoments` from length-uniform `δ₀` moments,
`GaussianAbsorptionContract` and `GaussianLpGradient` (via the jet mean and fluctuation steps). -/
theorem passiveJetMomentsUniform_of (hδ : DeltaZeroLengthUniform)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) : PassiveJetMomentsUniform := by
  intro b hb0 hb κ p hκ hp
  obtain ⟨d₀, ρ₁, C₂, Cm, W₀m, hd₀, hρ₁0, hρ₁1, hC₂, hCm, hmean⟩ :=
    passiveJetMeanStep_holds (PassiveLayer.passiveBounds_holds hGA hLp) b hb0 hb κ hκ
  obtain ⟨Cf, W₀f, hCf, hfl⟩ := passiveJetFluctuationStep_holds hGA hLp b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀0, hδT⟩ := hδ b hb0 hb κ p hκ hp
  have hρh : (1 : ℝ) / 2 ≤ max ρ₁ (1 / 2) := le_max_right _ _
  have hρ1 : max ρ₁ (1 / 2) < 1 := max_lt hρ₁1 (by norm_num)
  have hρ0 : 0 ≤ max ρ₁ (1 / 2) := by linarith
  have hM : 0 ≤ jetM b κ := by
    unfold jetM; have := etaLow_pos (by linarith : b < 1) hκ; positivity
  have hC₃ : 0 ≤ C₂ + jetM b κ / d₀ := by positivity
  have h1ρ : 0 < 1 - max ρ₁ (1 / 2) := by linarith
  refine ⟨1 / Real.log (1 / max ρ₁ (1 / 2)), C₀ + 2 * jetM b κ +
    ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - max ρ₁ (1 / 2)), fun T => ?_⟩
  obtain ⟨W₀p, hPIS⟩ := hδT T
  refine ⟨max (max W₀m W₀f) (max W₀p 1), ?_⟩
  intro W hW E hE s hs r hr1 hrlog hrT
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWf⟩, hWp, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hx : (0 : ℝ) < W := by exact_mod_cast (by omega : 0 < W)
  have hx1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hp0 : 0 < p := by linarith
  -- `δ₀`, now with a length-uniform constant
  have hδ0 : ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => jetDistance0 b E (pathX b E W j ω)) (ENNReal.ofReal p) (growthPathLaw W b) ≤
        ENNReal.ofReal (C₀ / W) := fun j hj hjT => hPIS W hWp E hE j hj hjT
  -- the recursion for `δ₁` (as in `passiveJetMoments_holds`)
  have hΦ : Measurable fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort =>
      jetFun b E q.1 q.2 := measurable_jetFun_comp b E measurable_fst measurable_snd
  have hae := ae_jet_step hb0 hb hκ hE hs hd₀ hρ₁0 hC₂ hCm hW1 (hmean W hWm E hE s hs)
  have hstep : ∀ j, 1 ≤ j → j < r → ∀ᵐ ω ∂growthPathLaw W b,
      pathJetV b E s W (j + 1) ω ≤ max ρ₁ (1 / 2) * pathJetV b E s W j ω +
        ((C₂ + jetM b κ / d₀) * jetDistance0 b E (pathX b E W j ω) + Cm / (W : ℝ) ^ 2 +
          stepFluctOf (jetFun b E) b E (fun _ => 0) j ω) := by
    intro j hj _
    filter_upwards [hae] with ω hω
    have h := hω j hj
    have := mul_le_mul_of_nonneg_right (le_max_left ρ₁ (1 / 2))
      (norm_nonneg (-crossTr (pathX b E W j ω) (boundaryZ b E) (boundaryZ b E) - s))
    change _ ≤ ρ₁ * ‖_‖ + _ at h
    change _ ≤ max ρ₁ (1 / 2) * ‖_‖ + _
    linarith
  have hy1 : eLpNorm (pathJetV b E s W 1) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (jetM b κ) := by
    refine (eLpNorm_le_of_ae_bound (C := jetM b κ)
      (measurable_pathJetV b E s 1).aestronglyMeasurable
      ((ae_pathJetV_le hb0 hb hκ hE hs 1).mono fun ω hω => by
        rwa [Real.norm_of_nonneg (by unfold pathJetV; exact norm_nonneg _)])).trans (le_of_eq ?_)
    simp
  have hBc : 0 ≤ ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / W := by positivity
  have he : ∀ j, 1 ≤ j → j < r →
      eLpNorm (fun ω => (C₂ + jetM b κ / d₀) * jetDistance0 b E (pathX b E W j ω) +
        Cm / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E (fun _ => 0) j ω) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤
      ENNReal.ofReal (((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / W) := by
    intro j hj hjr
    have hjT : (j : ℝ) ≤ T * W := le_trans (by exact_mod_cast hjr.le) hrT
    have hξ := eLpNorm_stepFluctOf_le hΦ (by linarith : b < 1) h1 h2 hp0
      (κ := fun _ => 0) (fun _ => le_rfl) j (C := Cf / W)
      (jetFun_fluct hb0 hb hκ hfl hWf hE)
    refine (eLpNorm_err_le hp hC₃ (by positivity) (hδ0 j hj hjT) hξ (by positivity)
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : Cm / (W : ℝ) ^ 2 ≤ Cm / W :=
      div_le_div_of_nonneg_left hCm hx (by nlinarith)
    rw [add_div, add_div, mul_div_assoc]
    linarith
  have hrec := eLpNorm_linrec (growthPathLaw W b) (y := pathJetV b E s W)
    (e := fun j ω => (C₂ + jetM b κ / d₀) * jetDistance0 b E (pathX b E W j ω) +
      Cm / (W : ℝ) ^ 2 + stepFluctOf (jetFun b E) b E (fun _ => 0) j ω)
    hp1 hρ0 hρ1 hM hBc (fun j ω => norm_nonneg _)
    (fun j => (measurable_pathJetV b E s j).aestronglyMeasurable) hstep hy1 he r hr1 le_rfl
  have hJ : eLpNorm (fun ω => pathJet1 b E s W r ω) (ENNReal.ofReal p) (growthPathLaw W b) =
      eLpNorm (pathJetV b E s W r) (ENNReal.ofReal p) (growthPathLaw W b) :=
    eLpNorm_congr_ae (pathJet1_ae_eq (by linarith) h1 h2 s r)
  have hpow := pow_le_two_div hρh hρ1 hW1 hr1 hrlog
  rw [hJ]
  refine (add_le_add (hδ0 r hr1 hrT) hrec).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : max ρ₁ (1 / 2) ^ (r - 1) * jetM b κ ≤ 2 / W * jetM b κ :=
    mul_le_mul_of_nonneg_right hpow hM
  have e1 : 2 / (W : ℝ) * jetM b κ = 2 * jetM b κ / W := by ring
  have e2 : ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / W / (1 - max ρ₁ (1 / 2)) =
      ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - max ρ₁ (1 / 2)) / W := by ring
  have e3 : (C₀ + 2 * jetM b κ + ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) /
      (1 - max ρ₁ (1 / 2))) / W = C₀ / W + 2 * jetM b κ / W +
      ((C₂ + jetM b κ / d₀) * C₀ + Cm + Cf) / (1 - max ρ₁ (1 / 2)) / W := by ring
  rw [e3]
  linarith

end BlockBand.Transmission.LengthUniform
