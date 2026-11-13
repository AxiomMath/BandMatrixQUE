module

public import BlockBand.SourceProcess.CompleteSourceGap.OnePort
public import BlockBand.SourceProcess.FullSource.DeltaMoments

/-!
# The gap identities almost surely, and integrability of the one-port letters

* `ae_transportedSep_projS`: a.s. `N P𝕊₊ N* = ι Γ ι*𝕊`, `Γ = gapLetter b E X`;
* `ae_transportedSep_projSProj`: a.s. `N P𝕊₊P N* = -c · ι (Lf₊L*) ι*` (`freshTransportedF`);
* `integrable_entries_of_momBd`: integrable entries from an `L¹` bound on the operator norm
  (applied to the one-port letters for `W ≥ W₀`, with the moment bounds of `moments_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `A - E - C` is a.s. invertible for the fresh GUE block `A` (`b < 1/2`, `W ≥ 1`). -/
theorem ae_isUnit_block_sub {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (C : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ ω ∂freshLaw W b, IsUnit (ω.1 0 - (E : ℂ) • 1 - C) := by
  have h := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW) (-((E : ℂ) • 1) - C)
  rw [← freshLaw_map_block W b] at h
  filter_upwards [ae_of_ae_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable h]
    with ω hω
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  convert hω using 2
  simp only [Function.comp_apply]
  abel

theorem cZero_mul (b E : ℝ) (hη : 0 < etaZ b E) :
    ((2 * Complex.I) * (etaZ b E : ℂ)) * cZero b E = 1 := by
  rw [cZero]
  exact mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hη.ne'))

/-- **a.s. gap identity for `P𝕊`.** -/
theorem ae_transportedSep_projS {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) :
    ∀ᵐ ω ∂freshLaw W b, transportedSep b E XX .projS ω =
      (nearSel W)ᴴ * gapLetter b E (nearSchur (boundaryZ b E) XX) ω *
        (nearSel W * twoPortScattering b E XX) := by
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  filter_upwards [ae_good W hb0 hW, ae_isUnit_block_sub hb hW E (portBlock XX 0 0)] with ω hω hS
  exact transportedSep_projS b E hXX hη hω.1 hω.2 hS

/-- **a.s. projected letter**: `N P𝕊₊P N* = -c · ι (Lf₊L*) ι*`. -/
theorem ae_transportedSep_projSProj {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) :
    ∀ᵐ ω ∂freshLaw W b, transportedSep b E XX .projSProj ω =
      (-((2 * Complex.I) * (etaZ b E : ℂ))) • ((nearSel W)ᴴ *
        freshTransportedF b E (nearSchur (boundaryZ b E) XX) ω * nearSel W) := by
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  have hY : (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef := nearSchur_passive hη hXX
  filter_upwards [ae_good W hb0 hW, ae_isUnit_block_sub hb hW E (portBlock XX 0 0),
    ae_g22_eq_Rplus hb0 hb hW E (w := boundaryZ b E) hη hY] with ω hω hS hR
  rw [transportedSep_projSProj b E hXX hη hω.1 hω.2 hS, hR]
  have hc := cZero_mul b E hη
  have e : (1 : Matrix (Fin W) (Fin W) ℂ) - ((2 * Complex.I) * (etaZ b E : ℂ)) •
      (boundaryZ b E • 1 - freshSchur E (nearSchur (boundaryZ b E) XX) ω)⁻¹ =
      (-((2 * Complex.I) * (etaZ b E : ℂ))) •
        passiveF b E (freshSchur E (nearSchur (boundaryZ b E) XX) ω) := by
    rw [passiveF, passiveResolvent, smul_sub, smul_smul, neg_mul, hc, neg_smul, neg_smul,
      sub_neg_eq_add, one_smul]
    abel
  rw [e, freshTransportedF]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem norm_g21_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖g21 E w X ω‖ ≤ ‖layerAt E w X ω‖ := by
  have : g21 E w X ω = (layerAt E w X ω).submatrix (fun x => Sum.inr ((0 : Fin 1), x))
      (fun y => Sum.inl ((0 : Fin 1), y)) := by ext; rfl
  rw [this]
  exact norm_submatrix_le _ (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)

theorem norm_g22_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖g22 E w X ω‖ ≤ ‖layerAt E w X ω‖ := by
  have : g22 E w X ω = (layerAt E w X ω).submatrix (fun x => Sum.inr ((0 : Fin 1), x))
      (fun y => Sum.inr ((0 : Fin 1), y)) := by ext; rfl
  rw [this]
  exact norm_submatrix_le _ (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)

/-- Integrable entries from an `L¹` bound on the operator norm. -/
theorem integrable_entries_of_momBd {μ : Measure (LayerSample W .oneBlockOnePort)}
    [IsProbabilityMeasure μ] {U : LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ}
    (hm : Measurable U) {C : ℝ} (hC : 0 ≤ C) (h : MomBd μ (fun ω => ‖U ω‖) 1 C) (x y : Fin W) :
    Integrable (fun ω => U ω x y) μ := by
  obtain ⟨hi, -⟩ := integral_abs_pow_le (ν := μ) (n := 1) le_rfl hC (by simpa using h)
  simp only [pow_one, abs_norm] at hi
  exact hi.mono' hm.eval_matrix.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => norm_entry_le_op _ x y)

end BlockBand.SourceProcess.CompleteSourceGap
