module

public import BlockBand.Transmission.LawForced.AbsBulk
public import BlockBand.Transmission.LawForced.AbsCond
public import BlockBand.Transmission.Absorbed.ShiftRatioP
public import BlockBand.Transmission.Absorbed.JetMoments
public import BlockBand.Transmission.Absorbed.MixSource
public import BlockBand.Transmission.Absorbed.Conductance
public import BlockBand.Transmission.Generator.PowL2

/-!
# Moments of the absorbed atoms

**`abs_moments hMT hGA hLp hJ hMix`**: `∃ M W₀`, for `W ≥ W₀`, `E ∈ bulkInterval κ_I`, every
stationary jet `s` and `εW ≤ r ≤ TW`: `absAtoms` is integrable with `E absAtoms ≤ M`.
Inputs: `absorbedConductance_bulk` (`p = 216`), and the hypotheses
`Absorbed.AbsorbedJetMoments` (`δ₀, δ₁`, `p = 108`) and `Absorbed.AbsorbedSourceMixingBulk`
(`p = 108`).
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
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- The four atoms of `ratioP_absorb_le` at `X_r`, to the power `108`. -/
def absAtoms (b E : ℝ) (κ : ℝ → ℝ) (s : ℂ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  (((passiveTransmission b E (pathNearSchur b E κ W r ω)).trace.re + 1) ^ 2) ^ 108 +
    ((W : ℝ) * jetDistance0 b E (pathNearSchur b E κ W r ω) + 1) ^ 108 +
    Absorbed.mixM3 b E (pathNearSchur b E κ W r ω) ^ 108 +
    ((W : ℝ) * jetDistance1 b E s (pathNearSchur b E κ W r ω) + 1) ^ 108

/-- **Moments of the absorbed atoms**, from `absorbedConductance_bulk`, `AbsorbedJetMoments` and
`AbsorbedSourceMixingBulk`. -/
theorem abs_moments (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hJ : Absorbed.AbsorbedJetMoments)
    (hMix : Absorbed.AbsorbedSourceMixingBulk) {b κI ε T : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκI : 0 < κI) (hε : 0 < ε) (hεT : ε < T) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) :
    ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        Integrable (absAtoms b E κ s W r) (growthPathLaw W b) ∧
          ∫ ω, absAtoms b E κ s W r ω ∂growthPathLaw W b ≤ M := by
  obtain ⟨K, hKb⟩ := hκ.2.2
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  obtain ⟨Cg, hCg⟩ := Absorbed.absorbedConductance_bulk hMT hGA hLp b hb0 hb κI ε
    ((216 : ℕ) : ℝ) (max K 0) hκI hε (by norm_num) hK0
  obtain ⟨Wg, hg⟩ := hCg T
  obtain ⟨Cj, hCjT⟩ := hJ b hb0 hb κI ε ((108 : ℕ) : ℝ) hκI hε (by norm_num) κ hκ
  obtain ⟨Wj, hj⟩ := hCjT T
  obtain ⟨Cm, Wm, hm⟩ := hMix b hb0 hb κI ε T ((108 : ℕ) : ℝ) hκI hε hεT (by norm_num) κ hκ
  set Cg' := max Cg 0
  set Cj' := max Cj 0
  set Cm' := max Cm 0
  refine ⟨2 ^ 216 * (Cg' + 1) + 2 ^ 108 * (Cj' ^ 108 + 1) + 2 ^ 108 * (Cm' ^ 108 + 1) +
    2 ^ 108 * (Cj' ^ 108 + 1), max (max Wg Wj) (max Wm 1), fun W hW E hE s hs r hεr hrT => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWg, hWj⟩, hWm, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < W := by linarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hWpos
  set μ := growthPathLaw W b
  have hκb : ∀ x, 0 ≤ κ x ∧ κ x ≤ max K 0 := fun x => ⟨hκ.2.1 x, (hKb x).trans (le_max_left _ _)⟩
  have hXm := Absorbed.measurable_pathNearSchur' (W := W) b E κ r
  have hP : ∀ᵐ ω ∂μ, (passiveY (pathNearSchur b E κ W r ω)).PosSemidef := by
    filter_upwards [ae_passiveSample W hκ.2.1 hb1 h1 h2] with ω hω
    exact pathNearSchur_passive hω r
  -- conductance
  have hgm := Absorbed.measurable_absorbedConductance (W := W) b E κ r
  have hgB : ∀ᵐ ω ∂μ, 0 ≤ Absorbed.absorbedConductance b E κ W r ω ∧
      Absorbed.absorbedConductance b E κ W r ω ≤ W := by
    filter_upwards [hP] with ω hω
    have := trace_pow_le_card (b := b) hb1 h1 h2 hω (k := 1) le_rfl
    simp only [pow_one] at this
    exact this
  have hgi := integral_pow_le_of_lintegral (μ := μ) hgm (hgB.mono fun _ h => h.1) 216
    (le_max_right Cg 0) ((hg W hWg E hE κ hκb r hεr hrT).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have mG : ∫ ω, (Absorbed.absorbedConductance b E κ W r ω + 1) ^ 216 ∂μ ≤
      2 ^ 216 * (Cg' + 1) :=
    (moment_shift hgm (hgB.mono fun _ h => h.1) (hgB.mono fun _ h => h.2) 216).trans
      (by gcongr)
  have iG : Integrable (fun ω => (Absorbed.absorbedConductance b E κ W r ω + 1) ^ 216) μ :=
    integrable_of_bdd ((hgm.add_const 1).pow_const 216) (B := ((W : ℝ) + 1) ^ 216) (by
      filter_upwards [hgB] with ω h
      rw [abs_of_nonneg (pow_nonneg (by linarith [h.1]) 216)]
      exact pow_le_pow_left₀ (by linarith [h.1]) (by linarith [h.2]) 216)
  -- jets
  have hjet := hj W hWj E hE s hs r hεr hrT
  have hδ0m : AEStronglyMeasurable (fun ω => jetDistance0 b E (pathNearSchur b E κ W r ω)) μ :=
    ((measurable_jetDistance0 b E).comp hXm).aestronglyMeasurable
  have hδ1e : (fun ω => ‖-crossTr (pathNearSchur b E κ W r ω) (boundaryZ b E) (boundaryZ b E) -
      s‖) =ᵐ[μ] fun ω => jetDistance1 b E s (pathNearSchur b E κ W r ω) := by
    filter_upwards [hP] with ω hω
    exact (PathJet.jetDistance1_eq_crossTr hb1 h1 h2 s hω).symm
  have hδ1m : AEStronglyMeasurable (fun ω => jetDistance1 b E s (pathNearSchur b E κ W r ω)) μ :=
    ((((PathJet.measurable_crossTr_mat _).comp hXm).neg.sub measurable_const).norm
      ).aestronglyMeasurable.congr hδ1e
  have hCjW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (Cj' / W) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le)
  obtain ⟨iA, mA⟩ := shifted_moment hδ0m (ae_of_all _ fun _ => norm_nonneg _) 108 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_self_add.trans hjet).trans hCjW)
  obtain ⟨iD, mD⟩ := shifted_moment hδ1m (ae_of_all _ fun _ => norm_nonneg _) 108 (by norm_num)
    (le_max_right Cj 0) hWpos ((le_add_self.trans hjet).trans hCjW)
  -- mixing
  have hτm : AEStronglyMeasurable (fun ω =>
      ‖(passiveQ b E (pathNearSchur b E κ W r ω) * passiveF b E (pathNearSchur b E κ W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
          (passiveF b E (pathNearSchur b E κ W r ω))) μ :=
    ((((measurable_traceQF b E).comp hXm).norm).add
      ((measurable_hsQF b E).comp hXm)).aestronglyMeasurable
  have hτL : eLpNorm (fun ω =>
      ‖(passiveQ b E (pathNearSchur b E κ W r ω) * passiveF b E (pathNearSchur b E κ W r ω)).trace‖ +
        hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
          (passiveF b E (pathNearSchur b E κ W r ω)))
        (ENNReal.ofReal ((108 : ℕ) : ℝ)) μ ≤ ENNReal.ofReal (Cm' / Real.sqrt W) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_norm (fun ω => (passiveQ b E (pathNearSchur b E κ W r ω) *
      passiveF b E (pathNearSchur b E κ W r ω)).trace)
      (((measurable_traceQF b E).comp hXm).aestronglyMeasurable)]
    exact (hm W hWm E hE r hεr hrT).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  obtain ⟨iT, mT⟩ := shifted_moment hτm
    (ae_of_all _ fun _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) 108 (by norm_num)
    (le_max_right Cm 0) hs0 hτL
  -- assemble
  have eG : ∀ ω, (((passiveTransmission b E (pathNearSchur b E κ W r ω)).trace.re + 1) ^ 2) ^ 108
      = (Absorbed.absorbedConductance b E κ W r ω + 1) ^ 216 := fun ω => by
    rw [← pow_mul]; rfl
  have eA : absAtoms b E κ s W r = fun ω =>
      (Absorbed.absorbedConductance b E κ W r ω + 1) ^ 216 +
        ((W : ℝ) * jetDistance0 b E (pathNearSchur b E κ W r ω) + 1) ^ 108 +
        (Real.sqrt W * (‖(passiveQ b E (pathNearSchur b E κ W r ω) *
          passiveF b E (pathNearSchur b E κ W r ω)).trace‖ +
          hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
            (passiveF b E (pathNearSchur b E κ W r ω))) + 1) ^ 108 +
        ((W : ℝ) * jetDistance1 b E s (pathNearSchur b E κ W r ω) + 1) ^ 108 := by
    funext ω; rw [absAtoms, eG]; rfl
  rw [eA]
  set fG := fun ω => (Absorbed.absorbedConductance b E κ W r ω + 1) ^ 216
  set fA := fun ω => ((W : ℝ) * jetDistance0 b E (pathNearSchur b E κ W r ω) + 1) ^ 108
  set fT := fun ω => (Real.sqrt W * (‖(passiveQ b E (pathNearSchur b E κ W r ω) *
          passiveF b E (pathNearSchur b E κ W r ω)).trace‖ +
          hsSandwich (passiveQ b E (pathNearSchur b E κ W r ω))
            (passiveF b E (pathNearSchur b E κ W r ω))) + 1) ^ 108
  set fD := fun ω => ((W : ℝ) * jetDistance1 b E s (pathNearSchur b E κ W r ω) + 1) ^ 108
  have j1 : Integrable (fun ω => fG ω + fA ω) μ := iG.add iA
  have j2 : Integrable (fun ω => fG ω + fA ω + fT ω) μ := j1.add iT
  have j3 : Integrable (fun ω => fG ω + fA ω + fT ω + fD ω) μ := j2.add iD
  refine ⟨j3, ?_⟩
  rw [integral_add j2 iD, integral_add j1 iT, integral_add iG iA]
  linarith

end BlockBand.Transmission.LawForced
