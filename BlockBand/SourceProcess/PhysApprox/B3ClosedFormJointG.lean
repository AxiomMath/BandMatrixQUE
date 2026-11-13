module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormJointCov
public import BlockBand.SourceProcess.PhysApprox.B3CovRepQuadBound

/-!
# `CovLayerHypKG` without the uniform cubic bound

`FreshDeltaQuadCovG` (proved from the Gaussian inputs, `freshDeltaQuadCovG_holds`) is the
cubic fresh bound with the factor `1 + g`, `g = Tr T(X)`. On the closed chain at the alive set
`g(X_cl) ≤ R²/2` (`cond_le_of_current`), which is all `covLayerAt_mixed_step` asks.

* `fresh_dK_dB_le_G`: the `(𝒦, B)` joint one-layer lemma for inputs with `g ≤ G₀`, from the Gaussian
  inputs and `FreshDeltaQuadCovG`;
* **`covLayerHypKG_of_nearG`**: `CovLayerHypKG b3CovErr b3CovZ` from the Gaussian inputs and the
  near-rows chain hypothesis `B3ClosedChainNearPin` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.FullSource (wardF nearSchur_passive)
open BlockBand.SourceProcess.FullSourceCovariance (covErr)
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open BlockBand.Transmission.Bridge
open scoped ENNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The `(𝒦, B)` joint one-layer covariance for inputs of conductance `≤ G₀`**, from the Gaussian
inputs and `FreshDeltaQuadCovG`. -/
theorem fresh_dK_dB_le_G (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hQ : FreshDeltaQuadCovG) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {G₀ : ℝ} (hG₀ : 0 ≤ G₀) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) ≤ G₀ →
      ∀ (u v : Fin W → ℂ) (c c' : Fin 2 × Fin W → ℂ) (Cf : ℝ), vecNorm u ≤ Cf →
        vecNorm v ≤ Cf → vecNorm (nearSel W *ᵥ c) ≤ Cf → vecNorm (nearSel W *ᵥ c') ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c)) ≤ Cf →
        vecNorm (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c')) ≤ Cf →
        ‖∫ F, bilinear u (freshDelta b E (nearSchur (boundaryZ b E) XX) F) v *
              bilinear c (freshTransport b E XX F * nearProjection W *
                (freshTransport b E XX F)ᴴ - nearProjection W) c' ∂freshLaw W b -
            (sigmaMinus b E s / W * crossedTensor u v (nearSel W *ᵥ c)
                (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c')) 1 1 +
              ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 (nearSel W *ᵥ c') *
                bilinear (passiveF b E (nearSchur (boundaryZ b E) XX) *ᵥ (nearSel W *ᵥ c)) 1 v))‖
          ≤ C * Cf ^ 4 * ((W : ℝ)⁻¹ / Real.sqrt W + covErr b E s (nearSchur (boundaryZ b E) XX) +
            (jetDistance0 b E (nearSchur (boundaryZ b E) XX) + (W : ℝ)⁻¹) ^ 2) := by
  obtain ⟨CS, WS, hCS, hS⟩ := fresh_delta_same_le hGA hLp hb0 hb hκ
  obtain ⟨CO, WO, hCO, hO⟩ := fresh_delta_opp_le hGA hLp hP hb0 hb hκ
  obtain ⟨CQ, WQ, hCQ, hQ'⟩ := hQ b hb0 hb κ hκ
  obtain ⟨C₂, W₂, -, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  refine ⟨CS + CO + CQ * (1 + G₀), max (max WS WO) (max W₂ WQ), by positivity, ?_⟩
  intro W hW E hE s hs XX hXX hg u v c c' Cf hu hv ha ha' hw hw'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWS, hWO⟩, hW2, hWQ⟩ := hW
  have hη := eta_pos_of_bulk hb hκ hE
  set X := nearSchur (boundaryZ b E) XX
  have hX : (passiveY X).PosSemidef := nearSchur_passive hη hXX
  obtain ⟨-, -, hL2⟩ := hM W hW2 E hE X hX
  set a := nearSel W *ᵥ c
  set a' := nearSel W *ᵥ c'
  set w := passiveF b E X *ᵥ a
  set w' := passiveF b E X *ᵥ a'
  obtain ⟨hQi, hQb⟩ := hQ' W hWQ E hE s hs X hX u v a a' Cf hu hv ha ha'
  have e : ∫ F, bilinear u (freshDelta b E X F) v * bilinear c (freshTransport b E XX F *
        nearProjection W * (freshTransport b E XX F)ᴴ - nearProjection W) c' ∂freshLaw W b =
      (∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w'
          ∂freshLaw W b +
        ∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b) +
        ∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshQuad b E X F) a'
          ∂freshLaw W b := by
    have hi1 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        bilinear a (freshDelta b E X F) w') (freshLaw W b) := (hL2 u v).integrable_mul (hL2 a w')
    have hi2 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        star (bilinear a' (freshDelta b E X F) w)) (freshLaw W b) :=
      (hL2 u v).integrable_mul (hL2 a' w).star
    have hi12 : Integrable (fun F => bilinear u (freshDelta b E X F) v *
        bilinear a (freshDelta b E X F) w' + bilinear u (freshDelta b E X F) v *
        star (bilinear a' (freshDelta b E X F) w)) (freshLaw W b) := hi1.add hi2
    rw [← integral_add hi1 hi2, ← integral_add hi12 hQi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
    simp only [freshTransport_P_sub, bilinear_nearSel_sandwich, bilinear_freshU_sub, X, a, a', w,
      w']
    ring
  rw [e]
  have h1 := hS W hWS E hE s hs X hX u v a w' Cf hu hv ha hw'
  have h2 := hO W hWO E hE s hs X hX u v a' w Cf hu hv ha' hw
  have hC4 : 0 ≤ Cf ^ 4 := by
    have := Transmission.PassiveCovariance.vecNorm_nonneg u
    have : 0 ≤ Cf := le_trans this hu
    positivity
  set P := (W : ℝ)⁻¹ / Real.sqrt W + covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2
  have hce : 0 ≤ covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 :=
    add_nonneg (B3.covErr_nonneg hb hκ hE s hX) (sq_nonneg _)
  have hw3 : 0 ≤ (W : ℝ)⁻¹ / Real.sqrt W := by positivity
  have hP0 : 0 ≤ P := by simp only [P]; linarith
  have hPle : covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2 ≤ P := by
    simp only [P]; linarith
  have k1 : CS * Cf ^ 4 * (covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2) ≤
      CS * Cf ^ 4 * P := mul_le_mul_of_nonneg_left hPle (by positivity)
  have k2 : CO * Cf ^ 4 * (covErr b E s X + (jetDistance0 b E X + (W : ℝ)⁻¹) ^ 2) ≤
      CO * Cf ^ 4 * P := mul_le_mul_of_nonneg_left hPle (by positivity)
  have k3 : CQ * Cf ^ 4 * (1 + conductanceOf (passiveTransmission b E X)) * P ≤
      CQ * (1 + G₀) * Cf ^ 4 * P := by
    have : CQ * Cf ^ 4 * (1 + conductanceOf (passiveTransmission b E X)) ≤
        CQ * (1 + G₀) * Cf ^ 4 := by
      have := mul_le_mul_of_nonneg_left (by linarith : 1 + conductanceOf
        (passiveTransmission b E X) ≤ 1 + G₀) (mul_nonneg hCQ hC4)
      linarith
    exact mul_le_mul_of_nonneg_right this hP0
  calc _ = ‖((∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshDelta b E X F) w'
          ∂freshLaw W b - sigmaMinus b E s / W * crossedTensor u v a w' 1 1) +
        (∫ F, bilinear u (freshDelta b E X F) v * star (bilinear a' (freshDelta b E X F) w)
          ∂freshLaw W b - ((sigmaPlus b : ℝ) : ℂ) / W * (bilinear u 1 a' * bilinear w 1 v))) +
        ∫ F, bilinear u (freshDelta b E X F) v * bilinear a (freshQuad b E X F) a'
          ∂freshLaw W b‖ := by
        congr 1; ring
    _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        have h12 := (norm_add_le _ _).trans (add_le_add h1 h2)
        have e3 : (CS + CO + CQ * (1 + G₀)) * Cf ^ 4 * P =
            CS * Cf ^ 4 * P + CO * Cf ^ 4 * P + CQ * (1 + G₀) * Cf ^ 4 * P := by ring
        rw [e3]
        linarith

/-- **`CovLayerHypKG b3CovErr b3CovZ` from the Gaussian inputs and `B3ClosedChainNearPin`**
(`freshDeltaQuadCovG_holds` replaces the uniform cubic bound). -/
theorem covLayerHypKG_of_nearG (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hN : B3ClosedChainNearPin) : CovLayerHypKG b3CovErr b3CovZ := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨hκ, hE⟩ := cov_bulk hE1 hE2
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  have hjet := b3Jet_spec hb0 hb hE1 hE2
  obtain ⟨C0, W0, hC0, hJ0⟩ := ClosedForm.fresh_dK_dM_le hGA hLp hP hb0 hb hκ
  obtain ⟨C1, W1, hC1, hJ1⟩ := fresh_dK_dB_le_G hGA hLp hP (freshDeltaQuadCovG_holds hGA hLp)
    hb0 hb hκ (G₀ := max R 0 ^ 2 / 2) (by positivity)
  obtain ⟨C₂, W₂, hC₂0, hM⟩ := fresh_delta_memLp hGA hb0 hb hκ
  obtain ⟨C₄, W₄, hC₄, h4⟩ := ClosedSummedProof.fresh_pow_bound hGA hb0 hb hκ
  obtain ⟨Cch, -, hevC⟩ := hN b E np τ m T s h K Vs hFD R
  set CJ := max C0 C1
  have hCJ : 0 ≤ CJ := le_max_of_le_left hC0
  refine ⟨2 * (CJ * ((1 + ‖cZero b E‖) * Real.sqrt R) ^ 4) +
    ‖sigmaMinus b E (b3Jet b E)‖ * ‖cZero b E‖ * Real.sqrt R ^ 2, 2, by positivity, le_rfl, ?_⟩
  filter_upwards [hevC, hFD.2.2.2.2.2, eventually_ge_atTop 1, eventually_ge_atTop W0,
    eventually_ge_atTop W1, eventually_ge_atTop W₂, eventually_ge_atTop W₄,
    B3Cur.eventually_one_le_closeLen hFD.2.1] with W hW hVW hW1 hW0' hW1' hW2 hW4 hs1 j hj ij g
  obtain ⟨XX, hch, hnear⟩ := hW j hj
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  have hjs : 1 ≤ j := hs1.trans hj'.1.1
  have hη : 0 < etaZ b E := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  have hpos : ∀ X' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X'.IsHermitian →
      0 ≤ covErr b E (b3Jet b E) (nearSchur (boundaryZ b E) X') +
        (jetDistance0 b E (nearSchur (boundaryZ b E) X') + (W : ℝ)⁻¹) ^ 2 := fun X' hX' =>
    add_nonneg (covErr_nonneg hb hκ hE _ (nearSchur_passive hη hX')) (sq_nonneg _)
  have hΔ : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∫⁻ f, ENNReal.ofReal (‖freshDelta b E X f‖ ^ 2) ∂freshLaw W b ≤
        ENNReal.ofReal (C₂ ^ 2) := fun X hX =>
    lintegral_sq_le_of_eLpNorm _ (fun _ => norm_nonneg _) hC₂0
      (by rw [ENNReal.ofReal_ofNat]; exact (hM W hW2 E hE X hX).2.1)
  have hA := covLayerAt_mixed_step hb0 hb hE1 hE2 hκ hE s h hh τ m R hW1 hjs hj hVW.1 hch hnear
    hCJ hC₄
    (fun X' hX' u v c c' Cf h1 h2 h3 h4' h5 h6 =>
      (hJ0 W hW0' E hE (b3Jet b E) hjet X' hX' u v c c' Cf h1 h2 h3 h4' h5 h6).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by have := (Transmission.PassiveCovariance.vecNorm_nonneg u).trans h1; positivity))
          (hpos X' hX')))
    (fun X' hX' hg u v c c' Cf h1 h2 h3 h4' h5 h6 =>
      (hJ1 W hW1' E hE (b3Jet b E) hjet X' hX' hg u v c c' Cf h1 h2 h3 h4' h5 h6).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (by have := (Transmission.PassiveCovariance.vecNorm_nonneg u).trans h1; positivity))
          (by linarith [hpos X' hX', (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹ / Real.sqrt W)])))
    hΔ (fun X' hX' => h4 W hW4 E hE X' hX') ij g
  refine ⟨hA, ?_⟩
  unfold CovLayerAt at hA ⊢
  have hf : (fun y => b3dX b E s h τ m W j (Vs W) (Sum.inl g) y *
      b3dX b E s h τ m W j (Vs W) (Sum.inr ij) y) =
      fun y => b3dX b E s h τ m W j (Vs W) (Sum.inr ij) y *
        b3dX b E s h τ m W j (Vs W) (Sum.inl g) y := funext fun y => mul_comm _ _
  rw [hf]
  exact hA

/-- **`CovLayerHypK b3CovErr b3CovZ`** (all pairs with a `𝒦` coordinate), combined with
`covLayerHypK_of_mixed`. -/
theorem covLayerHypK_of_nearG (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hN : B3ClosedChainNearPin) : CovLayerHypK b3CovErr b3CovZ :=
  covLayerHypK_of_mixed hGA hLp (covLayerHypKG_of_nearG hGA hLp hP hN)

end BlockBand.SourceProcess.PhysApprox.B3

