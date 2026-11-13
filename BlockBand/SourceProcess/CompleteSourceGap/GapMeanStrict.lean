module

public import BlockBand.SourceProcess.CompleteSourceGap.GapMeanParts

/-!
# `‖EΓ - θ_*I‖ ≤ C(δ₀ + δ₁ + q/W + W⁻²)` for strictly passive `X`

Hypothesis: `PassiveBoundsStatement`. Law `freshLaw W b`; fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`,
stationary jet `s`; operator norm; the constants depend on `b, E, s`, uniformly in `W ≥ W₀` and
strictly passive `X` (on and off the scalar domain).

`gap_decomp` and `theta_eq` give
`EΓ - θ_*I = ΩE[L𝒢₂₁] + (θ - θ_*)E[K𝒢₁₁] + θ_*(E[K𝒢₁₁] - I) + cR₁ + cR₂ + bR₃ + bR₄`, and:
* `Ω = c(v - a) + b(u - a)` (`z + E = -(1-b)a`), `|v - a|, |u - a| ≤ C(δ₀ + W⁻²)` on `δ₀ ≤ d₁`
  (`meanScalars_close`);
* `|θ - θ_*| ≤ C·e` on `δ₀ ≤ d₀` (`matchedScalars`);
* `‖E[K𝒢₁₁] - I‖ ≤ ‖(K̂E𝒢)₀₀ - KM‖ + ‖KM - I‖ ≤ C·e` (`mixedBlock`, `matchedBasic`);
* `‖R_i‖ ≤ C/W²` (`gap_covs`), `‖E[L𝒢₂₁]‖, ‖E[K𝒢₁₁]‖, |v|, |u| ≤ C` (passive moments).
Off the domain each factor is bounded, hence `≤ (C/d)·δ₀` (`le_of_domain`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer (passiveLetter PassiveBoundsStatement layerAt kG11 lAt
  paramDisk MomBd letter_momBd)
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- A quantity bounded by `A` everywhere and by `A'e` on `δ ≤ d` is `≤ (A' + A/d)e` (`δ ≤ e`). -/
theorem le_of_domain {q A A' δ d e : ℝ} (hq : q ≤ A) (hq' : δ ≤ d → q ≤ A' * e) (hδ : δ ≤ e)
    (hd : 0 < d) (hA : 0 ≤ A) (hA' : 0 ≤ A') (he : 0 ≤ e) : q ≤ (A' + A / d) * e := by
  have hAd : 0 ≤ A / d := div_nonneg hA hd.le
  by_cases h : δ ≤ d
  · have := hq' h; nlinarith
  · replace h := not_le.mp h
    have h1 : A ≤ A / d * δ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]; nlinarith
    nlinarith

/-- `∫|f| ≤ C` and integrability from an `L¹` bound. -/
theorem integral_le_of_momBd1 {μ : Measure (LayerSample W .oneBlockOnePort)}
    [IsProbabilityMeasure μ] {f : LayerSample W .oneBlockOnePort → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : MomBd μ f 1 C) : Integrable (fun ω => |f ω|) μ ∧ ∫ ω, |f ω| ∂μ ≤ C := by
  have h1 : MomBd μ f ((1 : ℕ) : ℝ) C := by simpa using hf
  have := FullSource.integral_abs_pow_le (ν := μ) (n := 1) le_rfl hC h1
  simpa using this

/-- `∫|f| ≤ C` and integrability from an `L²` bound. -/
theorem integral_le_of_momBd {μ : Measure (LayerSample W .oneBlockOnePort)} [IsProbabilityMeasure μ]
    {f : LayerSample W .oneBlockOnePort → ℝ} {C : ℝ} (hC : 0 ≤ C) (hf : MomBd μ f 2 C) :
    Integrable (fun ω => |f ω|) μ ∧ ∫ ω, |f ω| ∂μ ≤ C :=
  integral_le_of_momBd1 hC (hf.exponent_mono (by norm_num))

/-- **The strict gap-letter mean**, on and off the scalar domain. -/
theorem gapMean_strict (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (gapLetter b E X) - thetaStar b E s • 1‖ ≤
          C * SourceMixing.epsOf b E s X := by
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hsc⟩ := FullSource.meanScalars_close hA hb0 hb hκ
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Cb, Wb, hd₂, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨Cx, Wx, hCx, hmx⟩ := SourceMixing.mixedBlock hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTb⟩ := SourceMixing.scalarTheta_blocks hA hb0 hb h1 h2
  obtain ⟨Cc, Wc, hCc, hcov⟩ := gap_covs hA hb0 hb h1 h2
  obtain ⟨C4, W4, m4⟩ := layer_moments_u hA hb0 hb hκ (2 * (2 : ℕ)) (by norm_num)
  obtain ⟨C6, W6, m6⟩ := layer_moments_u hA hb0 hb hκ (2 * (3 : ℕ)) (by norm_num)
  obtain ⟨Cq, Wq, hmq⟩ := hA.moments b hb0 hb _ hκ 2 (by norm_num)
  obtain ⟨hθ1, -, -⟩ := SourceMixing.norm_thetaStar_le hb0 hb h1 h2 hs
  set C2 := max Cq 0
  have hC2 : 0 ≤ C2 := le_max_right _ _
  set d := min (min d₀ d₁) d₂
  have hd : 0 < d := lt_min (lt_min hd₀ hd₁) hd₂
  set ρΩ := Cs + (‖boundaryZ b E + E‖ + C2) / d
  set ρθ := Cm + (Ct + 1) / d
  set ρK := (Cx + Cb) + (C2 + 1) / d
  refine ⟨ρΩ * (C2 * C2) + ρθ * C2 + ρK + 2 * Cc,
    max (max (max Ws Wm) (max Wb Wx)) (max (max Wt Wc) (max (max W4 W6) (max Wq 1))),
    by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWs, hWm⟩, hWb, hWx⟩, ⟨hWt, hWc⟩, ⟨hW4, hW6⟩, hWq, hW1⟩ := hW
  have hW0 : 0 < W := by omega
  set μ := freshLaw W b
  set z := boundaryZ b E
  set e := SourceMixing.epsOf b E s X
  obtain ⟨hδ0, -, -, hδw, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
  have hw2 : ((W : ℝ)⁻¹) ^ 2 ≤ e := by linarith
  have he : 0 ≤ e := le_trans (by positivity) hw2
  have hδe : jetDistance0 b E X ≤ e := by linarith [show (0 : ℝ) ≤ ((W : ℝ)⁻¹) ^ 2 by positivity]
  have hCW : Cc / (W : ℝ) ^ 2 ≤ Cc * e := by
    rw [div_eq_mul_inv, ← inv_pow]; exact mul_le_mul_of_nonneg_left hw2 hCc
  obtain ⟨hi0, hi4, hiKF, -, -, hiP, hiQ, hR1, hR2, hR3, hR4⟩ := hcov W hWc X hX.posSemidef
  -- moments
  obtain ⟨hdet, hg, hk, hl⟩ := hmq W hWq E hE z (PassiveLayer.boundaryZ_mem_paramDisk (by linarith)
    h1 h2) X hX.posSemidef
  obtain ⟨hgM, hkM, hlM⟩ := letter_momBd (b := b) ⟨hg, hk, hl⟩
  obtain ⟨hgi, hgI⟩ := integral_le_of_momBd hC2 hgM
  obtain ⟨hki, hkI⟩ := integral_le_of_momBd hC2 hkM
  have hlg := PassiveLayer.MomBd.mul (p := 1) one_pos (by simpa using hlM) (by simpa using hgM) hC2
  obtain ⟨hlgi, hlgI⟩ := integral_le_of_momBd1 (mul_nonneg hC2 hC2) hlg
  simp only [abs_norm] at hgi hgI hki hkI
  -- the bounded factors
  set EK := matrixExpect μ (fun ω => passiveLetter E z X ω 4)
  set EKF := matrixExpect μ (kfGap b E X)
  have hEK : ‖EK‖ ≤ C2 :=
    (norm_matrixExpect_le _ hi4 hki).trans hkI
  have hKFle : ∀ ω, ‖kfGap b E X ω‖ ≤ |‖lAt E z X ω‖ * ‖layerAt E z X ω‖| := fun ω => by
    rw [abs_of_nonneg (by positivity)]
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left (norm_g21_le E z X ω)
      (norm_nonneg _))
  have hKFi : Integrable (fun ω => ‖kfGap b E X ω‖) μ :=
    hlgi.mono' ((PassiveLayer.measurable_passiveLetter E z X 5).mul
      (PassiveLayer.measurable_passiveLetter E z X 2)).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [norm_norm]; exact hKFle ω)
  have hEKF : ‖EKF‖ ≤ C2 * C2 :=
    (norm_matrixExpect_le _ hiKF hKFi).trans ((integral_mono hKFi hlgi hKFle).trans hlgI)
  have htr : ∀ k : Fin 4, ‖∫ ω, (W : ℂ)⁻¹ * (passiveLetter E z X ω k.castSucc.castSucc).trace ∂μ‖ ≤ C2 :=
    fun k => (norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun ω =>
      (PathScalar.norm_normTrace_le _).trans (norm_letter_le b E X ω k))).trans hgI
  -- the decomposition
  have hdec := gap_decomp hb0 hb h1 h2 hX (m4 W hW4 _ hE X hX.posSemidef)
    (m6 W hW6 _ hE X hX.posSemidef) hW0
  simp only [] at hdec
  rw [theta_eq] at hdec
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  set v := ∫ ω, physTr b E X ω ∂μ
  set u := ∫ ω, portTr b E X ω ∂μ
  set Ω := z + E + c * v + (b : ℂ) * u
  set θ := SourceMixing.thetaOf b E X
  set R1 := covR μ (tau0 b E X) (fun ω => passiveLetter E z X ω 4)
  set R2 := covR μ (physTr b E X) (kfGap b E X)
  set R3 := covR μ (tau1 b E X) (fun ω => passiveLetter E z X ω 4)
  set R4 := covR μ (portTr b E X) (kfGap b E X)
  have hsplit : matrixExpect μ (gapLetter b E X) - thetaStar b E s • 1 =
      Ω • EKF + (θ - thetaStar b E s) • EK + thetaStar b E s • (EK - 1) +
        (c • R1 + c • R2 + (b : ℂ) • R3 + (b : ℂ) • R4) := by
    rw [hdec]; simp only [sub_smul, smul_sub]; abel
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hnc : ‖c‖ = 1 - 2 * b := by simp only [c, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hnb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  -- `Ω`
  have hΩ : ‖Ω‖ ≤ ρΩ * e := by
    refine le_of_domain (A := ‖z + E‖ + C2) ?_ (fun hδ => ?_) hδe hd (by positivity) hCs he
    · have hv := htr 0
      have hu := htr 3
      calc ‖Ω‖ ≤ ‖z + E‖ + ‖c‖ * ‖v‖ + ‖(b : ℂ)‖ * ‖u‖ := by
            refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
              (add_le_add le_rfl (norm_mul _ _).le)) (norm_mul _ _).le)
        _ ≤ ‖z + E‖ + (1 - 2 * b) * C2 + b * C2 := by
            rw [hnc, hnb]; gcongr <;> assumption
        _ ≤ ‖z + E‖ + C2 := by linarith [mul_nonneg hb0.le hC2]
    · have hδ' : jetDistance0 b E X ≤ d₁ := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
      obtain ⟨hv, hu⟩ := hsc W hWs E hE X hX hδ'
      rw [← FullSource.integral_portTr_eq hb hW1 X] at hu
      have e1 : Ω = c * (v - matchedA E) + (b : ℂ) * (u - matchedA E) := by
        simp only [Ω, z]; rw [FullSource.boundaryZ_add_E h1 h2]; simp only [c]; push_cast; ring
      rw [e1]
      calc ‖c * (v - matchedA E) + (b : ℂ) * (u - matchedA E)‖
          ≤ (1 - 2 * b) * (Cs * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2)) +
              b * (Cs * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2)) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
            · rw [hnc]; exact mul_le_mul_of_nonneg_left hv hc0
            · rw [hnb]; exact mul_le_mul_of_nonneg_left hu hb0.le
        _ ≤ Cs * e := by
            have : Cs * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) ≤ Cs * e :=
              mul_le_mul_of_nonneg_left hδw hCs
            have h0 : 0 ≤ Cs * (jetDistance0 b E X + ((W : ℝ)⁻¹) ^ 2) :=
              mul_nonneg hCs (by positivity)
            linarith [mul_nonneg hb0.le h0]
  -- `θ`
  have hθ : ‖θ - thetaStar b E s‖ ≤ ρθ * e := by
    refine le_of_domain (A := Ct + 1) ?_ (fun hδ => ?_) hδe hd (by positivity) hCm he
    · exact (norm_sub_le _ _).trans (add_le_add (hTb W hWt X hX).2.1 hθ1)
    · exact (hms W hWm X hX (hδ.trans ((min_le_left _ _).trans (min_le_left _ _)))).2.2.2.1
  -- `E[K𝒢₁₁] - I`
  have hK1 : ‖EK - 1‖ ≤ ρK * e := by
    refine le_of_domain (A := C2 + 1) ?_ (fun hδ => ?_) hδe hd (by positivity) (by positivity) he
    · exact (norm_sub_le _ _).trans (add_le_add hEK norm_one_matrix_le)
    · have hb' := (hmb W hWb X hX (hδ.trans (min_le_right _ _))).2.2.2.1
      have hx := (hmx W hWx X hX).2
      rw [← expect_letter4 b E X hi0] at hx
      have hx' : ‖EK - SourceMixing.kmOf b E X‖ ≤ Cx * e := by
        refine hx.trans ?_
        rw [div_eq_mul_inv, ← inv_pow]; exact mul_le_mul_of_nonneg_left hw2 hCx
      calc ‖EK - 1‖ ≤ ‖EK - SourceMixing.kmOf b E X‖ + ‖SourceMixing.kmOf b E X - 1‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ Cx * e + Cb * e := add_le_add hx' hb'
        _ = (Cx + Cb) * e := by ring
  -- assembly
  rw [hsplit]
  have hR : ‖c • R1 + c • R2 + (b : ℂ) • R3 + (b : ℂ) • R4‖ ≤ 2 * Cc * e := by
    have t1 : ‖c • R1‖ ≤ (1 - 2 * b) * (Cc * e) := by
      rw [norm_smul, hnc]; exact mul_le_mul_of_nonneg_left (hR1.trans hCW) hc0
    have t2 : ‖c • R2‖ ≤ (1 - 2 * b) * (Cc * e) := by
      rw [norm_smul, hnc]; exact mul_le_mul_of_nonneg_left (hR2.trans hCW) hc0
    have t3 : ‖(b : ℂ) • R3‖ ≤ b * (Cc * e) := by
      rw [norm_smul, hnb]; exact mul_le_mul_of_nonneg_left (hR3.trans hCW) hb0.le
    have t4 : ‖(b : ℂ) • R4‖ ≤ b * (Cc * e) := by
      rw [norm_smul, hnb]; exact mul_le_mul_of_nonneg_left (hR4.trans hCW) hb0.le
    have n1 := norm_add_le (c • R1 + c • R2 + (b : ℂ) • R3) ((b : ℂ) • R4)
    have n2 := norm_add_le (c • R1 + c • R2) ((b : ℂ) • R3)
    have n3 := norm_add_le (c • R1) (c • R2)
    have hCe : 0 ≤ Cc * e := mul_nonneg hCc he
    have hb2 : 0 ≤ b * (Cc * e) := mul_nonneg hb0.le hCe
    linarith
  have hn1 : ‖Ω • EKF‖ ≤ ρΩ * e * (C2 * C2) := by
    rw [norm_smul]; exact mul_le_mul hΩ hEKF (norm_nonneg _) (by positivity)
  have hn2 : ‖(θ - thetaStar b E s) • EK‖ ≤ ρθ * e * C2 := by
    rw [norm_smul]; exact mul_le_mul hθ hEK (norm_nonneg _) (by positivity)
  have hn3 : ‖thetaStar b E s • (EK - 1)‖ ≤ ρK * e := by
    rw [norm_smul]
    calc ‖thetaStar b E s‖ * ‖EK - 1‖ ≤ 1 * (ρK * e) :=
          mul_le_mul hθ1 hK1 (norm_nonneg _) zero_le_one
      _ = ρK * e := one_mul _
  calc ‖Ω • EKF + (θ - thetaStar b E s) • EK + thetaStar b E s • (EK - 1) +
        (c • R1 + c • R2 + (b : ℂ) • R3 + (b : ℂ) • R4)‖
      ≤ ‖Ω • EKF‖ + ‖(θ - thetaStar b E s) • EK‖ + ‖thetaStar b E s • (EK - 1)‖ +
          ‖c • R1 + c • R2 + (b : ℂ) • R3 + (b : ℂ) • R4‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ ρΩ * e * (C2 * C2) + ρθ * e * C2 + ρK * e + 2 * Cc * e := by gcongr
    _ = _ := by ring

end BlockBand.SourceProcess.CompleteSourceGap
