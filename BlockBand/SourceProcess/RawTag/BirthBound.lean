module

public import BlockBand.SourceProcess.RawTag.Birth

/-!
# The birth bound

`birth_bound`: under `RawBirth`, `GaussianAbsorptionContract` and
`FullSourceMomentsEnergyUniformContract`, the raw forms at the birth length `max β₁ β₂ + 1` have
bounded `4m`-th moments, uniformly in `W`, in the birth indices `≤ TW` and in the bulk energy `E`
(the three cases: an old tag against the new one, coincident birth indices, the new tag against
an old one).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Birth bound.** -/
theorem birth_bound (hBirth : RawBirth) (hGA : GaussianAbsorptionContract)
    (hFS : FullSourceMomentsEnergyUniformContract) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) (T : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ (Bb : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ (Γ : Type) [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
      (g₁ g₂ : Γ → Fin W → ℂ), Measurable g₁ → Measurable g₂ →
      ν.map g₁ = circularVectorLaw (Fin W) → ν.map g₂ = circularVectorLaw (Fin W) →
      ∀ β₁ β₂ : ℕ, ((max β₁ β₂ : ℕ) : ℝ) ≤ T * W →
        ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W (max β₁ β₂ + 1) β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^
          (2 * m)) ∂((growthPathLaw W b).prod ν) ≤ ENNReal.ofReal Bb := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨A, Wf, hA, hfr⟩ := momBd_frame hFS hb0 hb hκ T (r := 16 * m) (by linarith)
  obtain ⟨CΔ, WΔ, hCΔ, hΔ⟩ := momBd_stepDelta hGA hb0 hb hκ (r := 16 * m) (by linarith)
  obtain ⟨CG, WG, hCG, hG⟩ := momBd_firstInverse hGA hb0 hb hκ (r := 16 * m) (by linarith)
  set Ag := (2 * gaussMoment (16 * m)) ^ (1 / (16 * (m : ℝ)))
  have hAg : 0 ≤ Ag := Real.rpow_nonneg (mul_nonneg (by norm_num) (gaussMoment_nonneg _)) _
  set η₀ := (1 - b) * κ / 4
  have hη₀ : 0 < η₀ := by have : 0 < 1 - b := by linarith
                          positivity
  set e := η₀⁻¹
  have he : 0 ≤ e := inv_nonneg.mpr hη₀.le
  set B₁ := Ag * CG * Ag
  set B₂ := Ag * (|e| + e ^ 2 * CΔ) * Ag
  set B₃ := A * (|1| + e * CΔ) * Ag
  set B₄ := Ag * (|1| + e * CΔ) * A
  refine ⟨B₁ ^ (4 * m) + B₂ ^ (4 * m) + B₃ ^ (4 * m) + B₄ ^ (4 * m),
    max (max Wf WΔ) (max WG 1), fun W hW E hE Γ _ ν _ g₁ g₂ hg₁ hg₂ hl₁ hl₂ β₁ β₂ hβ => ?_⟩
  have hWf : Wf ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hW)
  have hWΔ : WΔ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hW)
  have hWG : WG ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hE' := hE
  obtain ⟨hE1, hE2⟩ := hE'
  have hκ2 : κ ≤ 2 := by linarith
  set μΩ := (growthPathLaw W b).prod ν
  have hU := momBd_unitVec (r := 16 * m) (by linarith) W hW1
  have hU₁ : MomBd μΩ (fun w => vecNorm (unitVec W (g₁ w.2))) (16 * m) Ag :=
    momBd_tag hg₁ hl₁ hU
  have hU₂ : MomBd μΩ (fun w => vecNorm (unitVec W (g₂ w.2))) (16 * m) Ag :=
    momBd_tag hg₂ hl₂ hU
  have hpas : ∀ l : ℕ, ∀ᵐ w ∂μΩ, ‖stepR b E W l w.1‖ ≤ e := by
    intro l
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae
      (ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith : b < 1)
        (by linarith : -2 < E) (by linarith : E < 2))] with w hw
    refine (norm_passiveResolvent_le hb0 hb (by linarith) (by linarith)
      (pathNearSchur_passive hw l)).trans ?_
    exact inv_anti₀ hη₀ (etaZ_ge hb0 hb hκ hE)
  have hbirth := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae
    (hBirth b E hb0 hb (by linarith) (by linarith) W hW1)
  have hD₁ : ∀ l : ℕ, MomBd μΩ (fun w => 1 + e * ‖stepDelta b E W l w.1‖) (16 * m)
      (|1| + e * CΔ) := fun l =>
    (MomBd.const (μ := μΩ) (1 : ℝ) (16 * m) (by linarith)).add (by linarith)
      ((MomBd.comp_fst (ν := ν) (hΔ W hWΔ E hE l)).const_mul he) (abs_nonneg _) (by positivity)
  have hD₂ : ∀ l : ℕ, MomBd μΩ (fun w => e + e ^ 2 * ‖stepDelta b E W l w.1‖) (16 * m)
      (|e| + e ^ 2 * CΔ) := fun l =>
    (MomBd.const (μ := μΩ) e (16 * m) (by linarith)).add (by linarith)
      ((MomBd.comp_fst (ν := ν) (hΔ W hWΔ E hE l)).const_mul (sq_nonneg e)) (abs_nonneg _)
      (by positivity)
  have hB0 : ∀ x : ℝ, 0 ≤ x → x ^ (4 * m) ≤ B₁ ^ (4 * m) + B₂ ^ (4 * m) + B₃ ^ (4 * m) +
      B₄ ^ (4 * m) → ENNReal.ofReal (x ^ (4 * m)) ≤
        ENNReal.ofReal (B₁ ^ (4 * m) + B₂ ^ (4 * m) + B₃ ^ (4 * m) + B₄ ^ (4 * m)) :=
    fun x _ h => ENNReal.ofReal_le_ofReal h
  have p1 : 0 ≤ B₁ ^ (4 * m) := by positivity
  have p2 : 0 ≤ B₂ ^ (4 * m) := by positivity
  have p3 : 0 ≤ B₃ ^ (4 * m) := by positivity
  have p4 : 0 ≤ B₄ ^ (4 * m) := by positivity
  rcases lt_trichotomy β₁ β₂ with h12 | h12 | h12
  · -- an old tag against the new one
    have hmax : max β₁ β₂ = β₂ := max_eq_right h12.le
    rw [hmax] at hβ ⊢
    have hl1 : 1 ≤ β₂ := by omega
    have hfr₁ := momBd_nearL_of_frame hg₁ (hfr W hWf E hE β₂ β₁ h12 hβ Γ ν g₁ hg₁ hl₁)
    refine (lintegral_of_three hm hA (by positivity) hAg (fun w => by
      have := vecNorm_nonneg (nearL b E W β₂ β₁ w.1 (g₁ w.2))
      have := vecNorm_nonneg (unitVec W (g₂ w.2)); positivity) ?_ hfr₁ (hD₁ β₂) hU₂).trans
      (hB0 _ (by positivity) (by linarith))
    filter_upwards [hbirth, hpas β₂] with w hw hR
    rw [(hw β₂ hl1).1 β₁ h12]
    refine (norm_bilinear_le _ _ _).trans ?_
    have := norm_one_add_mul_le (M := stepDelta b E W β₂ w.1) hR
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
      (vecNorm_nonneg _)) (vecNorm_nonneg _)
  · -- coincident birth indices
    subst h12
    rw [max_self] at hβ ⊢
    rcases Nat.eq_zero_or_pos β₁ with h0 | h0
    · subst h0
      refine (lintegral_of_three hm hAg hCG hAg (fun w => by
        have := vecNorm_nonneg (unitVec W (g₁ w.2))
        have := vecNorm_nonneg (unitVec W (g₂ w.2)); positivity) (Filter.Eventually.of_forall
          fun w => ?_) hU₁ (MomBd.comp_fst (ν := ν) (hG W hWG E hE)) hU₂).trans
        (hB0 _ (by positivity) (by linarith))
      refine (norm_bilinear_le (unitTag W 1 0 (g₁ w.2)) _ (unitTag W 1 0 (g₂ w.2))).trans ?_
      rw [vecNorm_unitTag_one, vecNorm_unitTag_one]
      have hsub : ‖(fullInverse b E W (0 + 1) w.1).toBlocks₁₁‖ ≤ ‖fullInverse b E W 1 w.1‖ :=
        norm_submatrix_le _ (f := Sum.inl) (g := Sum.inl) Sum.inl_injective Sum.inl_injective
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsub (vecNorm_nonneg _))
        (vecNorm_nonneg _)
    · refine (lintegral_of_three hm hAg (by positivity) hAg (fun w => by
        have := vecNorm_nonneg (unitVec W (g₁ w.2))
        have := vecNorm_nonneg (unitVec W (g₂ w.2)); positivity) ?_ hU₁ (hD₂ β₁) hU₂).trans
        (hB0 _ (by positivity) (by linarith))
      filter_upwards [hbirth, hpas β₁] with w hw hR
      rw [(hw β₁ h0).2.2]
      refine (norm_bilinear_le _ _ _).trans ?_
      have := norm_res_le (M := stepDelta b E W β₁ w.1) he hR
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
        (vecNorm_nonneg _)) (vecNorm_nonneg _)
  · -- the new tag against an old one
    have hmax : max β₁ β₂ = β₁ := max_eq_left h12.le
    rw [hmax] at hβ ⊢
    have hl1 : 1 ≤ β₁ := by omega
    have hfr₂ := momBd_nearR_of_frame hg₂ (hfr W hWf E hE β₁ β₂ h12 hβ Γ ν g₂ hg₂ hl₂)
    refine (lintegral_of_three hm hAg (by positivity) hA (fun w => by
      have := vecNorm_nonneg (unitVec W (g₁ w.2))
      have := vecNorm_nonneg (nearR b E W β₁ β₂ w.1 (g₂ w.2)); positivity) ?_ hU₁ (hD₁ β₁)
      hfr₂).trans (hB0 _ (by positivity) (by linarith))
    filter_upwards [hbirth, hpas β₁] with w hw hR
    rw [(hw β₁ hl1).2.1 β₂ h12]
    refine (norm_bilinear_le _ _ _).trans ?_
    have := norm_one_add_mul_le' (M := stepDelta b E W β₁ w.1) hR
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
      (vecNorm_nonneg _)) (vecNorm_nonneg _)

end BlockBand.SourceProcess.RawTag
