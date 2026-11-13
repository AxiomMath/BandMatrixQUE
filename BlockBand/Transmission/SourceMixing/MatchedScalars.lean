module

public import BlockBand.Transmission.SourceMixing.MatchedAlg

/-!
# Matched values of `s₁, θ, ρ₁` on the jet domain

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`) with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, a stationary jet `s`;
constants depend on `b, E, s` only, uniformly in `W ≥ W₀` and `X`.

With `e = epsOf b E s X`, the scalars `s₁, θ, ρ₁` of the mean equations are `O(e)`-close to their
matched values `1, θ_*, c₀(1 - θ_*)`.

* `matchedScalars`: `|s₁ - 1|, |θ - θ_*|, |ρ₁ - c₀(1 - θ_*)| ≤ Ce`, `|θ|, |s₁| ≤ C`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_thetaStar_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {s : ℂ} (hs : IsStationaryJet b E s) :
    ‖thetaStar b E s‖ ≤ 1 ∧ thetaStar b E s * (1 + kMinus b E * s) = (b : ℂ) * matchedA E ^ 2 ∧
      b < ‖1 + kMinus b E * s‖ := by
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  have hne : 1 + kMinus b E * s ≠ 0 := fun h => by rw [h, norm_zero] at hden; linarith
  refine ⟨?_, div_mul_cancel₀ _ hne, hden⟩
  rw [thetaStar, norm_div, norm_mul, norm_pow, norm_matchedA E h1 h2, Complex.norm_real,
    Real.norm_of_nonneg hb0.le, one_pow, mul_one, div_le_one (by linarith)]
  exact hden.le

/-- Matched values of `s₁, θ, ρ₁`. -/
theorem matchedScalars (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖sOne b E X‖ ≤ C ∧ ‖thetaOf b E X‖ ≤ C ∧
        ‖sOne b E X - 1‖ ≤ C * epsOf b E s X ∧
        ‖thetaOf b E X - thetaStar b E s‖ ≤ C * epsOf b E s X ∧
        ‖rhoOf b E X - cZero b E * (1 - thetaStar b E s)‖ ≤ C * epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  obtain ⟨C₁, W₁, hC₁, hS1⟩ := scalarS1 hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTb⟩ := scalarTheta_blocks hA hb0 hb h1 h2
  obtain ⟨C₂, W₂, hC₂, hTh⟩ := scalarTheta hA hb0 hb h1 h2
  obtain ⟨Cr, Wr, hCr, hRb⟩ := scalarRho_blocks hA hb0 hb h1 h2
  obtain ⟨C₃, W₃, hC₃, hRh⟩ := scalarRho hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound hA hb0 hb h1 h2 2 1
  obtain ⟨hθ1, hθs, hden⟩ := norm_thetaStar_le hb0 hb h1 h2 hs
  set D := dStar b
  have hD : 0 ≤ D := by simp only [D, dStar]; have : 0 < 1 - b := by linarith
                        positivity
  have hsD : ‖s‖ ≤ D := hs.2
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + C₁ + C₂ + C₃ := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  obtain ⟨BA, hBAd⟩ : ∃ x : ℝ, x = Cb * Cb := ⟨_, rfl⟩
  have hBA : 0 ≤ BA := by rw [hBAd]; positivity
  obtain ⟨CB, hCBd⟩ : ∃ x : ℝ, x = Cb * (Cb * Cb) := ⟨_, rfl⟩
  have hCB : 0 ≤ CB := by rw [hCBd]; positivity
  obtain ⟨Kx, hKxd⟩ : ∃ x : ℝ, x = b ^ 2 * K * BA + K := ⟨_, rfl⟩
  have hKx : 0 ≤ Kx := by rw [hKxd]; positivity
  obtain ⟨Ks, hKsd⟩ : ∃ x : ℝ, x = (Cf * Kx + K + b * K) / b := ⟨_, rfl⟩
  have hKs : 0 ≤ Ks := by rw [hKsd]; positivity
  obtain ⟨Kθ, hKθd⟩ : ∃ x : ℝ, x = (Ct * ((1 + b ^ 2 * Cb ^ 2) * K + b ^ 2 * ((Cb + 1) * K) * D) +
      K + b * ((Cb + 1) * K)) / b := ⟨_, rfl⟩
  have hKθ : 0 ≤ Kθ := by rw [hKθd]; positivity
  obtain ⟨Kτ, hKτd⟩ : ∃ x : ℝ, x = K + Ct * K + Kθ * D := ⟨_, rfl⟩
  have hKτ : 0 ≤ Kτ := by rw [hKτd]; positivity
  obtain ⟨Kt1, hKt1d⟩ : ∃ x : ℝ, x = K + Ks * BA + K := ⟨_, rfl⟩
  have hKt1 : 0 ≤ Kt1 := by rw [hKt1d]; positivity
  obtain ⟨Kt, hKtd⟩ : ∃ x : ℝ, x = K + K * (1 + b * Cw) + b * Kt1 := ⟨_, rfl⟩
  have hKt : 0 ≤ Kt := by rw [hKtd]; positivity
  obtain ⟨KT, hKTd⟩ : ∃ x : ℝ, x = b ^ 2 * K * (Ct * Cf * CB) + Kθ * Cf * CB + Ks * CB + K +
      b * K * (1 + b * Ct) * Cw + b * b * Kτ * Cw + b * (1 + b * D) * Kt := ⟨_, rfl⟩
  have hKT : 0 ≤ KT := by rw [hKTd]; positivity
  obtain ⟨Kρ, hKρd⟩ : ∃ x : ℝ, x = (Cr * Kx + K + KT) / b := ⟨_, rfl⟩
  have hKρ : 0 ≤ Kρ := by rw [hKρd]; positivity
  refine ⟨d₀, Ks + Kθ + Kρ + Ct + Cf, max (max (max Wb Wf) (max W₁ Wt))
    (max (max W₂ Wr) (max W₃ Ww)), hd₀, by positivity, fun W hW X hX hd => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWb, hWf⟩, hW₁, hWt⟩, ⟨hW₂, hWr⟩, hW₃, hWw⟩ := hW
  obtain ⟨hM, hv, -, -, -, hva, hh, hAd, hm2, hBj⟩ := hmb W hWb X hX hd
  obtain ⟨-, hs₁, -⟩ := hF W hWf X hX
  obtain ⟨d1, d2, d3⟩ := hS1 W hW₁ X hX
  obtain ⟨hτ, hθ, -, -, -⟩ := hTb W hWt X hX
  obtain ⟨g1, -, g3⟩ := hTh W hW₂ X hX
  obtain ⟨-, hρ, -, -, -⟩ := hRb W hWr X hX
  obtain ⟨-, r2⟩ := hRh W hW₃ X hX
  obtain ⟨e0, -, -, e01, -⟩ := epsOf_ge (b := b) (E := E) s hX.posSemidef
  set e := epsOf b E s X
  have he : 0 ≤ e := by have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hWe : ∀ C' : ℝ, 0 ≤ C' → C' / (W : ℝ) ^ 2 ≤ C' * e := fun C' hC' => by
    rw [← div_sq_eq]; exact mul_le_mul_of_nonneg_left (by linarith) hC'
  have hKe : ∀ C' : ℝ, 0 ≤ C' → C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' _ hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hCbK : Cb ≤ K := by rw [hKd]; linarith
  have hC₁K : C₁ ≤ K := by rw [hKd]; linarith
  have hC₂K : C₂ ≤ K := by rw [hKd]; linarith
  have hC₃K : C₃ ≤ K := by rw [hKd]; linarith
  -- bounds on the traces
  have ht : ∀ r, ‖tTwo b E X r‖ ≤ Cw := fun r => by
    have h := (hw W hWw X hX.posSemidef 2 le_rfl ![0, 2] ![1, pTwo, 1] norm_ins_le).2.2.2.2 r
    have e' : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, pTwo, 1]) r) =
        fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e'] at h; exact h
  have hAb : ‖aOf b E X‖ ≤ BA := hBAd ▸ (PassiveCovariance.norm_normTrace_le _).trans
    ((Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCb))
  have hBb : ‖bOf b E X‖ ≤ CB := hCBd ▸ (PassiveCovariance.norm_normTrace_le _).trans
    ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ((Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCb))
      (norm_nonneg _) hCb))
  -- inputs at level `K e`
  have hh' := hKe Cb hCb hCbK _ hh
  have hAd' := hKe Cb hCb hCbK _ hAd
  have hva' := hKe Cb hCb hCbK _ hva
  have hm2' := hKe Cb hCb hCbK _ hm2
  have hBj' := hKe Cb hCb hCbK _ hBj
  have d1' := hKe C₁ hC₁ hC₁K _ (d1.trans (hWe C₁ hC₁))
  have d2' := hKe C₁ hC₁ hC₁K _ (d2.trans (hWe C₁ hC₁))
  have d3' := hKe C₁ hC₁ hC₁K _ (d3.trans (hWe C₁ hC₁))
  have g1' := hKe C₂ hC₂ hC₂K _ (g1.trans (hWe C₂ hC₂))
  have g3' := hKe C₂ hC₂ hC₂K _ (g3.trans (hWe C₂ hC₂))
  have r2' := hKe C₃ hC₃ hC₃K _ (r2.trans (hWe C₃ hC₃))
  -- `s₁`
  unfold khOf at d3' r2'
  obtain ⟨hx, hs1⟩ := s1_close hb0 hb he hK hAb hs₁ hh' hAd' d3'
  rw [← hKxd] at hx hs1
  rw [← hKsd] at hs1
  -- `θ`
  unfold kvOf at g3'
  have hθθ := theta_close (E := E) hb0 hb he hK hv hθ hsD (norm_matchedA E h1 h2) hden hθs hm2'
    hva' g3'
  rw [← hKθd] at hθθ
  -- `τ₁ + θ_*s`
  have hτs : ‖tauTwo b E X 0 + thetaStar b E s * s‖ ≤ Kτ * e := by
    have e' : tauTwo b E X 0 + thetaStar b E s * s = (tauTwo b E X 0 - thetaOf b E X * m2Of b E X) +
        thetaOf b E X * (m2Of b E X + s) - (thetaOf b E X - thetaStar b E s) * s := by ring
    rw [e']
    refine (norm_sub_le _ _).trans ?_
    refine le_trans (add_le_add ((norm_add_le _ _).trans (add_le_add g1'
      ((norm_mul_le _ _).trans (mul_le_mul (hθ) hm2' (norm_nonneg _) hCt))))
      ((norm_mul_le _ _).trans (mul_le_mul hθθ hsD (norm_nonneg _) (by positivity)))) ?_
    exact le_of_eq (by rw [hKτd]; ring)
  -- `t₂ - d_*`
  have hb1 : 1 + (b : ℂ) * (D : ℂ) = D := one_add_b_dStar hb
  have ht1d : ‖tTwo b E X 0 - D‖ ≤ Kt1 * e := by
    have e' : tTwo b E X 0 - D = (tTwo b E X 0 - sOne b E X * aOf b E X) +
        (sOne b E X - 1) * aOf b E X + (aOf b E X - D) := by ring
    rw [e']
    refine (norm_add₃_le).trans (le_trans (add_le_add_three d1'
      ((norm_mul_le _ _).trans (mul_le_mul hs1 hAb (norm_nonneg _) (by positivity))) hAd') ?_)
    exact le_of_eq (by rw [hKt1d]; ring)
  have htd : ‖tTwo b E X 1 - D‖ ≤ Kt * e := by
    have e' : tTwo b E X 1 - D = (tTwo b E X 1 - hOf b E X * (1 + (b : ℂ) * tTwo b E X 0)) +
        (hOf b E X - 1) * (1 + (b : ℂ) * tTwo b E X 0) + (b : ℂ) * (tTwo b E X 0 - D) := by
      linear_combination hb1
    rw [e']
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h1t : ‖1 + (b : ℂ) * tTwo b E X 0‖ ≤ 1 + b * Cw := (norm_add_le _ _).trans (by
      rw [norm_one, norm_mul, nb]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ht 0) hb0.le))
    refine (norm_add₃_le).trans (le_trans (add_le_add_three d2'
      ((norm_mul_le _ _).trans (mul_le_mul hh' h1t (norm_nonneg _) (by positivity)))
      (show ‖(b : ℂ) * (tTwo b E X 0 - D)‖ ≤ b * (Kt1 * e) by
        rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left ht1d hb0.le)) ?_)
    exact le_of_eq (by rw [hKtd]; ring)
  -- `ρ₁`
  have hkh : ‖(((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * hOf b E X) - kStarC b‖ ≤ b ^ 2 * K * e := by
    rw [show (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * hOf b E X) - kStarC b =
      (b : ℂ) ^ 2 * (hOf b E X - 1) by unfold kStarC; ring, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hb0.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left hh' (by positivity)
  have hT := T_close hb0 hb hkh hθ hs₁ hBb hθ1 hBj' hva' (hτ 0) (ht 1) (norm_matchedA E h1 h2)
    hτs hsD htd hθθ hs1
  rw [← hKTd] at hT
  have hTs : kStarC b * (thetaStar b E s * 1 * jetB b E s) + (b : ℂ) * matchedA E *
      (1 + (b : ℂ) * (-(thetaStar b E s * s))) * (D : ℂ) =
      (b : ℂ) * (cZero b E * (1 - thetaStar b E s)) :=
    rhoStar_identity hb0 hb h1 h2 s (thetaStar b E s) hθs
  have hρρ := rho_close hb0 hb hTs hρ hx r2' hT
  rw [← hKρd] at hρρ
  have hle : ∀ x : ℝ, 0 ≤ x → x ≤ Ks + Kθ + Kρ + Ct + Cf → x * e ≤ (Ks + Kθ + Kρ + Ct + Cf) * e :=
    fun x _ h => mul_le_mul_of_nonneg_right h he
  refine ⟨hs₁.trans (by linarith), hθ.trans (by linarith), hs1.trans (hle _ hKs (by linarith)),
    hθθ.trans (hle _ hKθ (by linarith)), hρρ.trans (hle _ hKρ (by linarith))⟩

end BlockBand.Transmission.SourceMixing
