module

public import BlockBand.SourceProcess.FullSourceCovariance.SameMeanCov
public import BlockBand.SourceProcess.FullSourceCovariance.PhiOppHolds
public import BlockBand.Transmission.PassiveCovariance.LeadAlgebra

/-!
# `PhiSameMean` holds: `W·EΦ(x,y') = σ₋·x*y' + O(δ₀ + δ₁ + g/W + W⁻¹)`

Law `freshLaw W b`, strictly passive `X`, `E ∈ bulkInterval κ`, near the jet; constants uniform in
`W ≥ W₀`, `E`, `X`, `x, y'`.

* `PhiSameMean`: the equal-sign analogue of `PhiOppMean`;
* `integral_sig1_mul`: `E[σ₁(f₀,f₁)T] = σ₁(Ef₀,Ef₁)ET + σ₁(Cov(f₀,T), Cov(f₁,T))`;
* **`phiSameMean_holds hGA hLp : PhiSameMean`**. Starting from `phiSame_mean_eq`
  (`W·EΦ = ET₁ + E[Ω₀T₂] + E[F·t]`):
  - `T₁ = c·F` (`tOne_eq`), `EF = x*y' + x*EΔ(Ry')` (`rightForms_bulk`, `deltaMean_strict`);
  - `τ = σ₁(⟨𝒢⟩₀,⟨𝒢⟩₁)`, so `E[Ω₀T₂] = Ω̄·ET₂ + O(W⁻²)` (`traceCov_form_bulk`, `omegaBar_close`);
  - `t = σ₁(⟨𝒢S̃𝒢⟩₀,⟨𝒢S̃𝒢⟩₁)`, so `E[Ft] = EF·Et + O(W⁻²)` and
    `Et = c(x₀ - 1) + b·x₁` (`sTilde_eq`, `tauP`, `xP`);
  - `W·EΦ - σ₋x*y' = (EF - x*y')·Σ_p s_p x_p + x*y'·Σ_p s_p(x_p - A_p) + Ω̄ET₂ + O(W⁻²)`, with
    `x_p ≈ A_p` (`xP_matched_bulk`) and `Σ_p s_pA_p = σ₋` (`sum_leadA`).
  The hypotheses enter only through `passiveBounds_holds hGA hLp`; no Poincaré inequality is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **The mean of `Φ`** (equal-sign ladder, determinant `1 + k₋s`). -/
def PhiSameMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∃ d : ℝ, 0 < d ∧
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef → jetDist b E s X ≤ d →
      ∀ x y' : Fin W → ℂ,
        ‖(W : ℂ) * (∫ ω, phiSame b E X x y' ω ∂freshLaw W b) -
            sigmaMinus b E s * bilinear x 1 y'‖ ≤
          C * (jetDist b E s X + (W : ℝ)⁻¹) * (vecNorm x * vecNorm y')

theorem wordVal_KG1 (Kh G : LayerMat W) : wordVal Kh G ![1] ![1, 1] = Kh * G := by
  rw [wordVal_succ, wordVal_zero]; simp [wLetter]

theorem wordVal_KGSG (Kh G S : LayerMat W) :
    wordVal Kh G ![1, 0] ![1, S, 1] = Kh * G * S * G := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [wLetter, Matrix.mul_assoc]

theorem wordVal_GSG (Kh G S : LayerMat W) : wordVal Kh G ![0, 0] ![1, S, 1] = G * S * G := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]; simp [wLetter, Matrix.mul_assoc]

theorem blkTr_add_smul (c d : ℂ) (A B : LayerMat W) (r : Fin 2) :
    SourceMixing.blkTr (c • A + d • B) r =
      c * SourceMixing.blkTr A r + d * SourceMixing.blkTr B r := by
  rw [SourceMixing.blkTr_def, SourceMixing.blkTr_def, SourceMixing.blkTr_def, blkAt_add,
    SourceMixing.blkAt_smul, SourceMixing.blkAt_smul, trace_add, trace_smul, trace_smul,
    smul_eq_mul, smul_eq_mul]
  ring

theorem norm_D3_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (j : Fin 3) :
    ‖(![1, sTilde W b, 1] : Fin 3 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_sTilde_le hb0 hb
  · exact norm_one_matrix_le

theorem norm_D2_le (j : Fin 2) : ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j <;> exact norm_one_matrix_le

section Generic
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_sig1 (b : ℝ) {f₀ f₁ : Ω → ℂ} (h₀ : Integrable f₀ μ) (h₁ : Integrable f₁ μ) :
    ∫ ω, sig1 b (f₀ ω) (f₁ ω) ∂μ = sig1 b (∫ ω, f₀ ω ∂μ) (∫ ω, f₁ ω ∂μ) := by
  simp only [sig1]
  rw [integral_add (h₀.const_mul _) (h₁.const_mul _), integral_const_mul, integral_const_mul]

/-- `E[σ₁(f₀,f₁)T] = σ₁(Ef₀,Ef₁)ET + σ₁(Cov(f₀,T), Cov(f₁,T))`. -/
theorem integral_sig1_mul (b : ℝ) {f₀ f₁ T : Ω → ℂ}
    (h₀ : Integrable (fun ω => f₀ ω * T ω) μ) (h₁ : Integrable (fun ω => f₁ ω * T ω) μ) :
    ∫ ω, sig1 b (f₀ ω) (f₁ ω) * T ω ∂μ =
      sig1 b (∫ ω, f₀ ω ∂μ) (∫ ω, f₁ ω ∂μ) * ∫ ω, T ω ∂μ +
        sig1 b ((∫ ω, f₀ ω * T ω ∂μ) - (∫ ω, f₀ ω ∂μ) * ∫ ω, T ω ∂μ)
          ((∫ ω, f₁ ω * T ω ∂μ) - (∫ ω, f₁ ω ∂μ) * ∫ ω, T ω ∂μ) := by
  have e : (fun ω => sig1 b (f₀ ω) (f₁ ω) * T ω) =
      fun ω => sig1 b (f₀ ω * T ω) (f₁ ω * T ω) := funext fun ω => by simp only [sig1]; ring
  rw [e, integral_sig1 b h₀ h₁]
  simp only [sig1]; ring

end Generic

/-- **`PhiSameMean`**, from `GaussianAbsorptionContract` and `GaussianLpGradient`. -/
theorem phiSameMean_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    PhiSameMean := by
  intro b hb0 hb κ hκ
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨W₁, hId⟩ := phiSame_mean_eq hA hb0 hb hκ
  obtain ⟨Cc, Wc, hCc, hcov⟩ := traceCov_form_bulk hA hb0 hb hκ
  obtain ⟨d₁, CΩ, WΩ, hd₁, hCΩ, hΩ⟩ := omegaBar_close hA hb0 hb hκ
  obtain ⟨d₂, CΔ, WΔ, hd₂, hCΔ, hΔ⟩ := FullSource.deltaMean_strict hA hb0 hb hκ
  obtain ⟨Cr, Wr, -, hrf⟩ := rightForms_bulk hGA hLp hb0 hb hκ 2 one_le_two
  obtain ⟨d₃, Cx, Wx, hd₃, hCx, hxm⟩ := CovarianceBulk.xP_matched_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hw⟩ := LengthUniform.wordMean_bound_bulk hA hb0 hb hκ 2 1
  have hηL := PathScalar.etaLow_pos (b := b) (by linarith) hκ
  set m := max 1 (PathScalar.etaLow b κ)⁻¹
  set ηi := (PathScalar.etaLow b κ)⁻¹
  set K := 2 * Cx * CΔ * ηi + 2 * Cx * m + CΩ * Cw + 4 * Cc
  refine ⟨min d₁ (min d₂ d₃), lt_min hd₁ (lt_min hd₂ hd₃), K,
    max (max (max W₁ Wc) (max WΩ WΔ)) (max (max Wr Wx) (max Ww 1)),
    fun W hW E hE s hs X hY hd x y' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₁, hWc⟩, hWΩ, hWΔ⟩, ⟨hWr, hWx⟩, hWw, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW0 : W ≠ 0 := by omega
  have hWr0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW0
  have hWge : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set w := (W : ℝ)⁻¹
  have hw0 : 0 ≤ w := inv_nonneg.mpr hWr0.le
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hWge
  have hw2 : w ^ 2 ≤ w := by nlinarith
  -- the jet distance
  have hg := conductance_nonneg b E hη.le hY.posSemidef
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hJ : jetDistance0 b E X ≤ jetDist b E s X := by
    unfold jetDist; have := div_nonneg hg hWr0.le
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    linarith
  set J := jetDist b E s X
  have hd0₁ : jetDistance0 b E X ≤ d₁ := hJ.trans (hd.trans (min_le_left _ _))
  have hd0₂ : jetDistance0 b E X ≤ d₂ :=
    hJ.trans (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd0₃ : jetDistance0 b E X ≤ d₃ :=
    hJ.trans (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  have nx := vecNorm_nonneg x
  have ny := vecNorm_nonneg y'
  set n := vecNorm x * vecNorm y'
  have hn : 0 ≤ n := mul_nonneg nx ny
  obtain ⟨-, -, -, hmean⟩ := hId W hW₁ E hE X hY x y'
  -- (1) `T₁ = c·F`
  have e1 : ∫ ω, tOne b E X x y' ω ∂freshLaw W b = c * ∫ ω, fForm b E X x y' ω ∂freshLaw W b := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ω => tOne_eq hb hW0 E X x y' ω)
  -- (2) the self-energy term
  have hτc := fun r => hcov W hWc E hE X hY.posSemidef 1 (by norm_num) ![0] ![1, 1] norm_D2_le
    2 le_rfl ![1, 0] ![1, sTilde W b, 1] (norm_D3_le hb0 hb) r x y'
    (fun ω => SourceMixing.blkTr (gRes b E X ω) r) (tTwoS b E X x y')
    (fun ω => by rw [wordVal_Gs1']) (fun ω => by rw [wordVal_KGSG]; rfl)
  obtain ⟨cτ, hcτ⟩ : ∃ cτ : Fin 2 → ℂ, ∀ r, cτ r =
      (∫ ω, SourceMixing.blkTr (gRes b E X ω) r * tTwoS b E X x y' ω ∂freshLaw W b) -
        (∫ ω, SourceMixing.blkTr (gRes b E X ω) r ∂freshLaw W b) * ∫ ω, tTwoS b E X x y' ω ∂freshLaw W b :=
    ⟨_, fun _ => rfl⟩
  have hT2 : Integrable (tTwoS b E X x y') (freshLaw W b) := (hτc 0).2.1
  have e2 : ∫ ω, omega0 b E X ω * tTwoS b E X x y' ω ∂freshLaw W b =
      ((boundaryZ b E + E) + ∫ ω, selfTau b (gRes b E X ω) ∂freshLaw W b) * ∫ ω, tTwoS b E X x y' ω ∂freshLaw W b +
        sig1 b (cτ 0) (cτ 1) := by
    have eτ : ∀ ω, omega0 b E X ω * tTwoS b E X x y' ω = (boundaryZ b E + E) *
        tTwoS b E X x y' ω + sig1 b (SourceMixing.blkTr (gRes b E X ω) 0)
          (SourceMixing.blkTr (gRes b E X ω) 1) * tTwoS b E X x y' ω := fun ω => by
      rw [omega0, selfTau_eq_sig1 hb0 hb]; ring
    have hp : Integrable (fun ω => sig1 b (SourceMixing.blkTr (gRes b E X ω) 0)
        (SourceMixing.blkTr (gRes b E X ω) 1) * tTwoS b E X x y' ω) (freshLaw W b) := by
      have e : (fun ω => sig1 b (SourceMixing.blkTr (gRes b E X ω) 0)
          (SourceMixing.blkTr (gRes b E X ω) 1) * tTwoS b E X x y' ω) = fun ω =>
          c * (SourceMixing.blkTr (gRes b E X ω) 0 * tTwoS b E X x y' ω) +
            (b : ℂ) * (SourceMixing.blkTr (gRes b E X ω) 1 * tTwoS b E X x y' ω) :=
        funext fun ω => by simp only [sig1, c]; ring
      rw [e]; exact ((hτc 0).2.2.1.const_mul _).add ((hτc 1).2.2.1.const_mul _)
    have es : ∫ ω, selfTau b (gRes b E X ω) ∂freshLaw W b = sig1 b (∫ ω, SourceMixing.blkTr (gRes b E X ω) 0 ∂freshLaw W b)
        (∫ ω, SourceMixing.blkTr (gRes b E X ω) 1 ∂freshLaw W b) := by
      simp only [selfTau_eq_sig1 hb0 hb]; exact integral_sig1 b (hτc 0).1 (hτc 1).1
    rw [integral_congr_ae (Eventually.of_forall eτ), integral_add (hT2.const_mul _) hp,
      integral_const_mul, integral_sig1_mul b (hτc 0).2.2.1 (hτc 1).2.2.1, es, hcτ, hcτ]
    ring
  -- (3) the ladder term
  have htc := fun r => hcov W hWc E hE X hY.posSemidef 2 le_rfl ![0, 0] ![1, sTilde W b, 1]
    (norm_D3_le hb0 hb) 1 (by norm_num) ![1] ![1, 1] norm_D2_le r x y'
    (fun ω => SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) r) (fForm b E X x y')
    (fun ω => by rw [wordVal_GSG]) (fun ω => by rw [wordVal_KG1]; rfl)
  obtain ⟨ct, hct⟩ : ∃ ct : Fin 2 → ℂ, ∀ r, ct r =
      (∫ ω, SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) r *
          fForm b E X x y' ω ∂freshLaw W b) -
        (∫ ω, SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) r ∂freshLaw W b) *
          ∫ ω, fForm b E X x y' ω ∂freshLaw W b := ⟨_, fun _ => rfl⟩
  have hpp := fun p r => (hcov W hWc E hE X hY.posSemidef 2 le_rfl ![0, 0] (dP3 p)
    (norm_dP3_le p) 1 (by norm_num) ![1] ![1, 1] norm_D2_le r x y'
    (fun ω => SourceMixing.blkTr (gRes b E X ω * (bProj p * gRes b E X ω)) r) (fForm b E X x y')
    (fun ω => by rw [wordVal_GPpG]) (fun ω => by rw [wordVal_KG1]; rfl)).1
  have hm : ∀ r, ∫ ω, SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) r ∂freshLaw W b =
      c * tauP b E X 0 r + (b : ℂ) * tauP b E X 1 r := fun r => by
    have e : ∀ ω, SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) r =
        c * SourceMixing.blkTr (gRes b E X ω * (bProj 0 * gRes b E X ω)) r +
          (b : ℂ) * SourceMixing.blkTr (gRes b E X ω * (bProj 1 * gRes b E X ω)) r := fun ω => by
      rw [← blkTr_add_smul, sTilde_eq hb0 hb hW0]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      rfl
    rw [integral_congr_ae (Eventually.of_forall e), integral_add ((hpp 0 r).const_mul _)
      ((hpp 1 r).const_mul _), integral_const_mul, integral_const_mul]
    rfl
  have e3 : ∫ ω, fForm b E X x y' ω * tSame b (sTilde W b) (gRes b E X ω) ∂freshLaw W b =
      (c * (xP b E X 0 - 1) + (b : ℂ) * xP b E X 1) * ∫ ω, fForm b E X x y' ω ∂freshLaw W b +
        sig1 b (ct 0) (ct 1) := by
    have e : ∀ ω, fForm b E X x y' ω * tSame b (sTilde W b) (gRes b E X ω) =
        sig1 b (SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) 0)
          (SourceMixing.blkTr (gRes b E X ω * sTilde W b * gRes b E X ω) 1) *
          fForm b E X x y' ω := fun ω => by rw [tSame_eq_sig1 hb0 hb, mul_comm]
    rw [integral_congr_ae (Eventually.of_forall e),
      integral_sig1_mul b (htc 0).2.2.1 (htc 1).2.2.1, hct, hct, hm, hm]
    have i00 : ind 0 0 = 1 := by simp [ind]
    have i01 : ind 0 1 = 0 := by simp [ind]
    simp only [xP, i00, i01, sig1, c]
    ring
  -- (4) the scalars
  obtain ⟨-, -, hFm, -⟩ := hrf W hWr E hE X hY.posSemidef x y'
  have hR : vecNorm (passiveResolvent b E X *ᵥ y') ≤ ηi * vecNorm y' :=
    (vecNorm_mulVec_le' _ _).trans (mul_le_mul_of_nonneg_right ((norm_passiveResolvent_le hb0 hb
      h1 h2 hY.posSemidef).trans (CovarianceBulk.inv_etaZ_le_bulk hb hκ hE)) ny)
  have hD := hΔ W hWΔ E hE X hY hd0₂
  have hFB : ‖(∫ ω, fForm b E X x y' ω ∂freshLaw W b) - bilinear x 1 y'‖ ≤
      CΔ * ηi * (jetDistance0 b E X + w ^ 2) * n := by
    rw [hFm, add_sub_cancel_left]
    refine (norm_bilinear_le _ _ _).trans ?_
    have := vecNorm_nonneg (passiveResolvent b E X *ᵥ y')
    calc vecNorm x * ‖matrixExpect (freshLaw W b) (freshDelta b E X)‖ *
          vecNorm (passiveResolvent b E X *ᵥ y') ≤
        vecNorm x * (CΔ * (jetDistance0 b E X + w ^ 2)) * (ηi * vecNorm y') := by gcongr
      _ = _ := by simp only [n]; ring
  have hB : ‖bilinear x 1 y'‖ ≤ n := by
    refine (norm_bilinear_le _ _ _).trans ?_
    calc vecNorm x * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * vecNorm y' ≤ vecNorm x * 1 * vecNorm y' := by
          gcongr; exact norm_one_matrix_le
      _ = n := by ring
  have hΩb := hΩ W hWΩ E hE X hY hd0₁
  obtain ⟨hent, -, -, hEn, -⟩ := hw W hWw E hE X hY.posSemidef 2 le_rfl ![1, 0]
    ![1, sTilde W b, 1] (norm_D3_le hb0 hb)
  have hT2m : ‖∫ ω, tTwoS b E X x y' ω ∂freshLaw W b‖ ≤ Cw * n := by
    have e : ∫ ω, tTwoS b E X x y' ω ∂freshLaw W b = bilinear x (blkAt (matrixExpect (freshLaw W b)
        (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![1, 0] ![1, sTilde W b, 1])) 0 0) y' := by
      rw [← integral_form _ hent]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        beta_reduce
        rw [wordVal_KGSG]; rfl)
    rw [e]
    refine (norm_bilinear_le _ _ _).trans ?_
    calc _ ≤ vecNorm x * Cw * vecNorm y' := by gcongr; exact (norm_blkAt_le _ _ _).trans hEn
      _ = Cw * n := by simp only [n]; ring
  have hcτb : ∀ r, ‖cτ r‖ ≤ Cc * w ^ 2 * n := fun r => by
    rw [hcτ]; refine (hτc r).2.2.2.trans (le_of_eq ?_); rw [div_eq_mul_inv, inv_pow]
  have hctb : ∀ r, ‖ct r‖ ≤ Cc * w ^ 2 * n := fun r => by
    rw [hct]; refine (htc r).2.2.2.trans (le_of_eq ?_); rw [div_eq_mul_inv, inv_pow]
  have hx := fun p => hxm W hWx E hE s hs X hY hd0₃ p
  set e := SourceMixing.epsOf b E s X
  have hem := epsOf_le_jetDist hb0 hb hκ hE s hY.posSemidef hW1
  -- (5) the leading value
  have hu : 1 + kMinus b E * s ≠ 0 := by
    intro h0; have := jet_denom_pos hb0 hb h1 h2 s hs.2; rw [h0, norm_zero] at this; linarith
  have hσ : sigmaMinus b E s = c * leadA b E s 0 + (b : ℂ) * leadA b E s 1 := by
    have s0 : sRow b 0 = c := rfl
    have s1 : sRow b 1 = (b : ℂ) := rfl
    rw [← sum_leadA hu, Fin.sum_univ_two, s0, s1]
  have hsplit : (W : ℂ) * (∫ ω, phiSame b E X x y' ω ∂freshLaw W b) -
      sigmaMinus b E s * bilinear x 1 y' =
      ((∫ ω, fForm b E X x y' ω ∂freshLaw W b) - bilinear x 1 y') *
          (c * xP b E X 0 + (b : ℂ) * xP b E X 1) +
        bilinear x 1 y' * (c * (xP b E X 0 - leadA b E s 0) + (b : ℂ) * (xP b E X 1 -
          leadA b E s 1)) +
        ((boundaryZ b E + E) + ∫ ω, selfTau b (gRes b E X ω) ∂freshLaw W b) *
          (∫ ω, tTwoS b E X x y' ω ∂freshLaw W b) +
        sig1 b (cτ 0) (cτ 1) + sig1 b (ct 0) (ct 1) := by
    rw [hmean, e1, e2, e3, hσ]; ring
  rw [hsplit]
  have hcn : ‖c‖ ≤ 1 := by
    simp only [c]; rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
  have hXs : ‖c * xP b E X 0 + (b : ℂ) * xP b E X 1‖ ≤ 2 * Cx := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t0 := mul_le_mul hcn (hx 0).1 (norm_nonneg _) zero_le_one
    have t1 := mul_le_mul hbn (hx 1).1 (norm_nonneg _) zero_le_one
    linarith only [t0, t1]
  have hXL : ‖c * (xP b E X 0 - leadA b E s 0) + (b : ℂ) * (xP b E X 1 - leadA b E s 1)‖ ≤
      2 * (Cx * e) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t0 := mul_le_mul hcn (hx 0).2 (norm_nonneg _) zero_le_one
    have t1 := mul_le_mul hbn (hx 1).2 (norm_nonneg _) zero_le_one
    linarith only [t0, t1]
  have hs1 := norm_sig1_le hb0 hb (hcτb 0) (hcτb 1)
  have hs2 := norm_sig1_le hb0 hb (hctb 0) (hctb 1)
  have hJw : jetDistance0 b E X + w ^ 2 ≤ J + w := by linarith
  have hw2J : w ^ 2 ≤ J + w := by linarith [hδ0.trans hJ]
  have hCx2 : 0 ≤ 2 * Cx := by positivity
  calc _ ≤ ‖((∫ ω, fForm b E X x y' ω ∂freshLaw W b) - bilinear x 1 y') *
          (c * xP b E X 0 + (b : ℂ) * xP b E X 1)‖ +
        ‖bilinear x 1 y' * (c * (xP b E X 0 - leadA b E s 0) + (b : ℂ) * (xP b E X 1 -
          leadA b E s 1))‖ +
        ‖((boundaryZ b E + E) + ∫ ω, selfTau b (gRes b E X ω) ∂freshLaw W b) *
          (∫ ω, tTwoS b E X x y' ω ∂freshLaw W b)‖ +
        ‖sig1 b (cτ 0) (cτ 1)‖ + ‖sig1 b (ct 0) (ct 1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ CΔ * ηi * (jetDistance0 b E X + w ^ 2) * n * (2 * Cx) + n * (2 * (Cx * e)) +
        CΩ * (jetDistance0 b E X + w ^ 2) * (Cw * n) + Cc * w ^ 2 * n + Cc * w ^ 2 * n := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
    _ ≤ CΔ * ηi * (J + w) * n * (2 * Cx) + n * (2 * (Cx * (m * (J + w)))) +
        CΩ * (J + w) * (Cw * n) + Cc * (J + w) * n + Cc * (J + w) * n := by gcongr
    _ = (2 * Cx * CΔ * ηi + 2 * Cx * m + CΩ * Cw + 2 * Cc) * (J + w) * n := by ring
    _ ≤ K * (J + w) * n := by
        have hJw0 : 0 ≤ J + w := by linarith [hδ0.trans hJ]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hJw0) hn
        simp only [K]; linarith

end BlockBand.SourceProcess.FullSourceCovariance
