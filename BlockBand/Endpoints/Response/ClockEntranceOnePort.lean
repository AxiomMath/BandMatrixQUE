module

public import BlockBand.Endpoints.Response.ClockEntranceJensen
public import BlockBand.Endpoints.Response.ClockEntranceLayerWeight
public import BlockBand.Internal.Contracts.LayersOnePort

/-!
# The one-port inputs (a), (b) from the one-port contracts

This file derives the one-port inputs `OnePortPassiveMean` and `OnePortOperatorMoments` of the
one-layer clock step from `OnePortPassiveMeanContract` and `OnePortOperatorMomentsContract`.

* `opg_passiveY_eq`, `opg_onePortL_eq`, `opg_freshU_eq`, `opg_onePortDistance_eq`: the
  identification facts `onePortDissipation X = passiveY X`, `onePortL = freshL`,
  `freshU = onePortL onePortL*`, `onePortDistance = jetDistance0` (the last three by `rfl`).
* `opg_lintegral_pow_le_of_eLpNorm_le`: `‖ ‖L‖ ‖_{L^{2r}} ≤ C` gives `∫⁻ ‖L‖^{2r} ≤ C^{2r}`
  (`r ≥ 1`).
* `onePortPassiveMean_of_contract`: `OnePortPassiveMean` from `OnePortPassiveMeanContract`.
* `onePortOperatorMoments_of_contract`: `OnePortOperatorMoments` from `OnePortOperatorMomentsContract`
  (the case `r = 0` is the total mass `1`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.LayersOnePort BlockBand.Internal.Contracts.Endpoints
  BlockBand.Internal.Contracts.Inputs

/-!
## Identification facts
-/

/-- `onePortDissipation X = (i/2)(X - X*) = -Im X = passiveY X`. -/
theorem opg_passiveY_eq {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    onePortDissipation X = passiveY X := by
  rw [onePortDissipation, passiveY, BlockBand.Transmission.matrixImaginaryPart, ← neg_smul,
    neg_div, neg_neg]

/-- Passivity in the two vocabularies. -/
theorem opg_isPassiveInput_iff {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    IsPassiveInput X ↔ (passiveY X).PosSemidef := by
  rw [IsPassiveInput, opg_passiveY_eq]

/-- `onePortL = freshL` (by `rfl`). -/
theorem opg_onePortL_eq {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : onePortL b E X ω = freshL b E X ω :=
  rfl

/-- `freshU = onePortL onePortL*` (by `rfl`). -/
theorem opg_freshU_eq {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshU b E X ω = onePortL b E X ω * (onePortL b E X ω)ᴴ :=
  rfl

/-- `onePortDistance = jetDistance0` (by `rfl`). -/
theorem opg_onePortDistance_eq {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    onePortDistance b E X = jetDistance0 b E X :=
  rfl

/-!
## Positivity of the mean
-/

/-- `0 ⪯ E U`: the entrywise mean of a PSD-valued random matrix with integrable entries is PSD
(for any measure). It is Hermitian by conjugating the integrals, and `x*(EU)x = ∫ x*Ux`, whose
integrand is real and `≥ 0`. -/
theorem opg_matrixExpect_posSemidef {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (μ : Measure Ω) {U : Ω → Matrix n n ℂ} (hU : ∀ ω, (U ω).PosSemidef)
    (hInt : ∀ x y, Integrable (fun ω => U ω x y) μ) : (matrixExpect μ U).PosSemidef := by
  have hH : (matrixExpect μ U).IsHermitian := by
    ext a c
    simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
    rw [Complex.star_def, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have := congrFun (congrFun (hU ω).isHermitian a) c
    simp only [conjTranspose_apply] at this
    simpa [Complex.star_def] using this
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun v => ?_
  set f : Ω → ℂ := fun ω => star v ⬝ᵥ (U ω *ᵥ v) with hf
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => (hU ω).dotProduct_mulVec_nonneg v
  have e1 : star v ⬝ᵥ (matrixExpect μ U *ᵥ v) = ∫ ω, f ω ∂μ := by
    simp only [hf, dotProduct, mulVec, matrixExpect, Matrix.of_apply, Pi.star_apply]
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_finsetSum _ fun j _ => (hInt i j).mul_const _]
      congr 1
      exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm
    · exact (integrable_finsetSum _ fun j _ => (hInt i j).mul_const _).const_mul _
  have e2 : ∫ ω, f ω ∂μ = ((∫ ω, (f ω).re ∂μ : ℝ) : ℂ) := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans integral_ofReal
    have h := Complex.le_def.mp (hf0 ω)
    exact Complex.ext (by simp) (by simpa using h.2.symm)
  rw [e1, e2]
  exact_mod_cast integral_nonneg fun ω => (Complex.le_def.mp (hf0 ω)).1

/-!
## `eLpNorm` to `lintegral`
-/

/-- `‖g‖_{L^{2r}(μ)} ≤ C` for `g ≥ 0`, `r ≥ 1`, gives `∫⁻ g^{2r} ≤ (max C 0)^{2r}`. -/
theorem opg_lintegral_pow_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) (hg0 : ∀ x, 0 ≤ g x) {r : ℕ} (hr : 1 ≤ r)
    {C : ℝ} (h : eLpNorm g (ENNReal.ofReal (2 * r)) μ ≤ ENNReal.ofReal C) :
    ∫⁻ x, ENNReal.ofReal (g x ^ (2 * r)) ∂μ ≤ ENNReal.ofReal (max C 0 ^ (2 * r)) := by
  have hq : (0 : ℝ) < 2 * r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hp0 : ENNReal.ofReal (2 * r) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq
  have hpt : (ENNReal.ofReal (2 * r)).toReal = 2 * r := ENNReal.toReal_ofReal hq.le
  have e1 : ∀ x, ENNReal.ofReal (g x ^ (2 * r)) = ‖g x‖ₑ ^ ((2 * r : ℕ) : ℝ) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hg0 x), ENNReal.rpow_natCast,
      ENNReal.ofReal_pow (hg0 x)]
  simp_rw [e1]
  have hcast : ((2 * r : ℕ) : ℝ) = 2 * r := by push_cast; ring
  rw [hcast]
  calc ∫⁻ x, ‖g x‖ₑ ^ ((2 : ℝ) * r) ∂μ = eLpNorm' g (2 * r) μ ^ ((2 : ℝ) * r) :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hq
    _ = eLpNorm g (ENNReal.ofReal (2 * r)) μ ^ ((2 : ℝ) * r) := by
        rw [eLpNorm_eq_eLpNorm' hp0 ENNReal.ofReal_ne_top hg, hpt]
    _ ≤ ENNReal.ofReal C ^ ((2 : ℝ) * r) := ENNReal.rpow_le_rpow h hq.le
    _ = ENNReal.ofReal (max C 0) ^ ((2 : ℝ) * r) := by
        rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
    _ = ENNReal.ofReal (max C 0 ^ (2 * r)) := by
        rw [← hcast, ENNReal.rpow_natCast, ENNReal.ofReal_pow (le_max_right _ _)]

/-!
## The bulk parameter
-/

/-- `κ = min (E + 2) (2 - E) / 2 > 0` puts `E` in `bulkInterval κ`. -/
theorem opg_bulk {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (E + 2) (2 - E) / 2 ∧ E ∈ bulkInterval (min (E + 2) (2 - E) / 2) := by
  have h1 : min (E + 2) (2 - E) ≤ E + 2 := min_le_left _ _
  have h2 : min (E + 2) (2 - E) ≤ 2 - E := min_le_right _ _
  have h3 : 0 < min (E + 2) (2 - E) := lt_min (by linarith) (by linarith)
  refine ⟨by linarith, ?_, ?_⟩ <;> linarith

/-!
## The one-port inputs (a), (b)
-/

/-- **One-port input (a).** `OnePortPassiveMean` from `OnePortPassiveMeanContract`: the upper
bound is the contract at `κ = min(E+2, 2-E)/2` (passive inputs from the jet domain through
`opg_passiveY_eq`), any jet radius (`d = 1`), `W₀' = max W₀ 1`; the lower bound `0 ⪯ E LL*` is
`opg_matrixExpect_posSemidef` with the contract's integrability. -/
theorem onePortPassiveMean_of_contract (h : OnePortPassiveMeanContract) : OnePortPassiveMean := by
  intro b hb0 hb1 E hE1 hE2 s _
  obtain ⟨hκ, hEκ⟩ := opg_bulk hE1 hE2
  obtain ⟨C, W₀, hC0, hC⟩ := h b hb0 hb1 _ hκ
  refine ⟨C, 1, max W₀ 1, hC0, one_pos, fun W hW X hX => ?_⟩
  have hW0 : 0 < W := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hW)
  have hpass : IsPassiveInput X := (opg_isPassiveInput_iff X).mpr hX.1
  obtain ⟨hint, hub⟩ := hC W hW0 (le_trans (le_max_left _ _) hW) X hpass E hEκ
  exact ⟨opg_matrixExpect_posSemidef _ (fun ν => posSemidef_self_mul_conjTranspose _) hint, hub⟩

/-- **One-port input (b).** `OnePortOperatorMoments` from `OnePortOperatorMomentsContract`: for
`r ≥ 1` the contract at `p = 2r`, `κ = min(E+2, 2-E)/2`, with `∫⁻ ‖L‖^{2r} ≤ (max C 0)^{2r}`
(`opg_lintegral_pow_le_of_eLpNorm_le`); for `r = 0` the integral is the total mass `1` of the
probability law `freshLaw W b`. Any jet radius (`d = 1`). -/
theorem onePortOperatorMoments_of_contract (h : OnePortOperatorMomentsContract) :
    OnePortOperatorMoments := by
  intro b hb0 hb1 E hE1 hE2 s _
  obtain ⟨hκ, hEκ⟩ := opg_bulk hE1 hE2
  refine ⟨1, one_pos, fun r => ?_⟩
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨1, 0, fun W _ X _ => ?_⟩
    have := cel_isProbabilityMeasure_freshLaw W b
    simp
  · have hp : (1 : ℝ) ≤ 2 * r := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    obtain ⟨Cp, W₀, hCp⟩ := h.moments b hb0 hb1 _ hκ (2 * r) hp
    refine ⟨max Cp 0 ^ (2 * r), max W₀ 1, fun W hW X hX => ?_⟩
    have hW0 : 0 < W := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hW)
    have hpass : IsPassiveInput X := (opg_isPassiveInput_iff X).mpr hX.1
    have hb := hCp W hW0 (le_trans (le_max_left _ _) hW) X hpass E hEκ
    have hm : AEStronglyMeasurable (fun ν => ‖freshL b E X ν‖) (freshLaw W b) :=
      (continuous_norm.measurable.comp (h.measurable W b E X)).aestronglyMeasurable
    exact opg_lintegral_pow_le_of_eLpNorm_le hm (fun ν => norm_nonneg _) hr hb

/-- **`ClockFractionalEntranceContract` from the one-port contracts.** As
`clockFractionalEntrance_of_onePortProps`, with the one-port inputs (a), (b) supplied by
`OnePortPassiveMeanContract` and `OnePortOperatorMomentsContract`. The other one-port hypotheses
are `OnePortJetContraction` and `FractionalTraceJensenGap`. -/
theorem clockFractionalEntrance_of_onePort (hECM : EdgeClockMomentsContract)
    (hTLU : BlockBand.Internal.Contracts.TransmissionUniform.TransmissionLengthUniformContract)
    (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hJet : OnePortJetContraction) (hTay : FractionalTraceJensenGap) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_of_onePortProps hECM hTLU hCount hTL hPC hPSM hTay
    (onePortPassiveMean_of_contract hPM) (onePortOperatorMoments_of_contract hOM) hJet

end BlockBand.Endpoints
