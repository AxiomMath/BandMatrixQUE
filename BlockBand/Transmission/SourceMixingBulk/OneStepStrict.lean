module

public import BlockBand.Transmission.SourceMixingBulk.TransportedMean
public import BlockBand.Transmission.SourceMixing.OneStepStrict

/-!
# The one-step mean for strictly passive inputs, uniformly on the bulk

The estimate `oneStepMean_strict` with constants uniform in `E ∈ bulkInterval κ` and in the
stationary jet `s`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `α ≤ (1-b)²/(bη_L)` on the bulk. -/
theorem alphaCoef_le_bulk {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) : alphaCoef b E ≤ (1 - b) ^ 2 / (b * etaLow b κ) := by
  have hl := etaLow_pos (b := b) (by linarith) hκ
  have hle : etaLow b κ ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  rw [alphaCoef]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hb0 hl)
    (mul_le_mul_of_nonneg_left hle hb0.le)

/-- The one-step mean for strictly passive inputs.
The version of `oneStepMean_strict` with constants uniform on `bulkInterval κ` and on `s`. -/
theorem oneStepMean_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
            (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨C₃, W₃, hC₃, hT⟩ := transportedF_mean_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cs, Ws, hd₀, hCs, hS⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₀', Cb, Wb, hd₀', hCb, hB⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨Ct, Wt, hCt, hTb⟩ := scalarTheta_blocks_bulk hA hb0 hb hκ
  obtain ⟨Cr, Wr, hCr, hRb⟩ := scalarRho_blocks_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  have hl := etaLow_pos (b := b) (by linarith) hκ
  have h1b : 0 < 1 - b := by linarith
  obtain ⟨ηi, hηid⟩ : ∃ x : ℝ, x = (etaLow b κ)⁻¹ := ⟨_, rfl⟩
  have hηi : 0 ≤ ηi := by rw [hηid]; positivity
  obtain ⟨cL, hcLd⟩ : ∃ x : ℝ, x = 1 / ((1 - b) * κ) := ⟨_, rfl⟩
  have hcL : 0 ≤ cL := by rw [hcLd]; positivity
  obtain ⟨αU, hαUd⟩ : ∃ x : ℝ, x = (1 - b) ^ 2 / (b * etaLow b κ) := ⟨_, rfl⟩
  have hαU : 0 ≤ αU := by rw [hαUd]; positivity
  obtain ⟨BfL, hBfLd⟩ : ∃ x : ℝ, x = ηi + cL := ⟨_, rfl⟩
  have hBfL : 0 ≤ BfL := by rw [hBfLd]; positivity
  obtain ⟨BgL, hBgLd⟩ : ∃ x : ℝ, x = Ct * Cf * (Cf * CD * Cf) + (Cr + cL * Cf) *
      (Cf * Cf) + C₃ + BfL := ⟨_, rfl⟩
  have hBgL : 0 ≤ BgL := by rw [hBgLd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  obtain ⟨KonL, hKonLd⟩ : ∃ x : ℝ, x = (Ct * K + K) * (Cf * CD * Cf) + (K * (CD * Cf) + K * Cf +
      ηi * K) + (K + cL * K) * (Cf * Cf) + cL * (K * Cf + K) := ⟨_, rfl⟩
  have hKonL : 0 ≤ KonL := by rw [hKonLd]; positivity
  obtain ⟨dd, hddd⟩ : ∃ x : ℝ, x = min d₀ d₀' := ⟨_, rfl⟩
  have hdd : 0 < dd := by rw [hddd]; exact lt_min hd₀ hd₀'
  refine ⟨C₃ + KonL + BgL / dd + αU * BfL, max (max (max W₃ Ws) (max Wb Wf))
    (max (max Wt Wr) WD), by positivity, fun W hW E hEκ s hs X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηle : (etaZ b E)⁻¹ ≤ ηi := hηid ▸ inv_etaZ_le_bulk hb hκ hEκ
  have hcle : ‖cZero b E‖ ≤ cL := hcLd ▸ norm_cZero_le hb hκ hEκ
  obtain ⟨hθ1, -, -⟩ := norm_thetaStar_le hb0 hb h1 h2 hs
  obtain ⟨α, hαd⟩ : ∃ x : ℝ, x = alphaCoef b E := ⟨_, rfl⟩
  have hα : 0 ≤ α := by
    rw [hαd, alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  have hαle : α ≤ αU := by rw [hαd, hαUd]; exact alphaCoef_le_bulk hb0 hb hκ hEκ
  obtain ⟨Bf, hBfd⟩ : ∃ x : ℝ, x = (etaZ b E)⁻¹ + ‖cZero b E‖ := ⟨_, rfl⟩
  have hBf : 0 ≤ Bf := by rw [hBfd]; positivity
  have hBfle : Bf ≤ BfL := by rw [hBfd, hBfLd]; linarith only [hηle, hcle]
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₃, hWs⟩, hWb, hWf⟩, ⟨hWt, hWr⟩, hWD⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hKM, hs₁, -⟩ := hF W hWf E hEκ X hX
  obtain ⟨-, hθ, -, -, -⟩ := hTb W hWt E hEκ X hX
  obtain ⟨-, hρ, -, -, -⟩ := hRb W hWr E hEκ X hX
  obtain ⟨-, -, hM, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨e0, e1, eq, e01, eall⟩ := epsOf_ge (b := b) (E := E) s hY
  change _ ≤ _ * epsOf b E s X
  have he : 0 ≤ epsOf b E s X := by
    have := sq_nonneg ((W : ℝ)⁻¹); linarith only [this, e0, e01]
  have hT' := hT W hW₃ E hEκ X hX
  have hf : ‖passiveF b E X‖ ≤ Bf := hBfd ▸ norm_passiveF_le hb0 hb h1 h2 hY
  have hW2 : C₃ / (W : ℝ) ^ 2 ≤ C₃ * epsOf b E s X := by
    rw [← div_sq_eq]; exact mul_le_mul_of_nonneg_left (by linarith only [e0, e01]) hC₃
  -- the `q/W` correction
  have hxc : (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) / (W : ℂ)) =
      1 + ((α * (passiveMass b E X / W) : ℝ) : ℂ) := by rw [hαd]; push_cast; ring
  have hx0 : 0 ≤ α * (passiveMass b E X / W) := mul_nonneg hα eq
  have hcorr : ‖thetaStar b E s • passiveF b E X - (thetaStar b E s /
      (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) / (W : ℂ))) • passiveF b E X‖ ≤
      α * Bf * epsOf b E s X := by
    rw [hxc, ← sub_smul]
    refine (norm_smul_le _ _).trans ?_
    rw [norm_sub_rev]
    have hq : α * (passiveMass b E X / W) ≤ α * epsOf b E s X :=
      mul_le_mul_of_nonneg_left (by linarith only [e0, e1, eall]) hα
    calc _ ≤ (‖thetaStar b E s‖ * (α * (passiveMass b E X / W))) * Bf :=
          mul_le_mul (norm_div_one_add_sub_le _ hx0) hf (norm_nonneg _) (by positivity)
      _ ≤ (1 * (α * epsOf b E s X)) * Bf := by gcongr
      _ = _ := by ring
  set G := matrixExpect (freshLaw W b) (freshTransportedF b E X)
  set F := (thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
    (rhoOf b E X - cZero b E * sOne b E X) • (kmOf b E X * (kmOf b E X)ᴴ)
  have hGF : ‖G - F‖ ≤ C₃ * epsOf b E s X := hT'.trans hW2
  have hfin : ‖G - thetaStar b E s • passiveF b E X‖ ≤ (C₃ + KonL + BgL / dd) * epsOf b E s X := by
    by_cases hdom : jetDistance0 b E X ≤ dd
    · obtain ⟨-, -, hR, hKM1, hMR, -, -, -, -, -⟩ :=
        hB W hWb E hEκ s X hX (hdom.trans (hddd ▸ min_le_right _ _))
      obtain ⟨-, -, hs1, hθθ, hρρ⟩ := hS W hWs E hEκ s hs X hX (hdom.trans (hddd ▸ min_le_left _ _))
      have lift : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * epsOf b E s X → x ≤ K * epsOf b E s X :=
        fun C' hC' x hx => hx.trans (mul_le_mul_of_nonneg_right hC' he)
      have hCbK : Cb ≤ K := by rw [hKd]; linarith only [hCs]
      have hCsK : Cs ≤ K := by rw [hKd]; linarith only [hCb]
      have hFf := assemble_on (kmOf b E X) (mOf b E X) (passiveResolvent b E X) (thetaOf b E X)
        (sOne b E X) (rhoOf b E X) (thetaStar b E s) (cZero b E) he hK hKM hM (hR.trans hηle) hθ
        hθ1 (lift _ hCbK _ hKM1) (lift _ hCbK _ hMR) (lift _ hCsK _ hs1) (lift _ hCsK _ hθθ)
        (lift _ hCsK _ hρρ)
      have hKon : ((Ct * K + K) * (Cf * CD * Cf) + (K * (CD * Cf) + K * Cf + ηi * K) +
          (K + ‖cZero b E‖ * K) * (Cf * Cf) + ‖cZero b E‖ * (K * Cf + K)) ≤ KonL := by
        rw [hKonLd]; gcongr
      have hFf' := hFf.trans (mul_le_mul_of_nonneg_right hKon he)
      have e' : G - thetaStar b E s • passiveF b E X = (G - F) + (F - thetaStar b E s •
          (passiveResolvent b E X - cZero b E • 1)) := by rw [passiveF]; abel
      rw [e']
      refine (norm_add_le _ _).trans ?_
      have h0 : 0 ≤ BgL / dd * epsOf b E s X := by positivity
      calc _ ≤ C₃ * epsOf b E s X + KonL * epsOf b E s X := add_le_add hGF hFf'
        _ ≤ _ := by linarith only [h0]
    · push Not at hdom
      have hFn := assemble_bound (kmOf b E X) (mOf b E X) (thetaOf b E X) (sOne b E X)
        (rhoOf b E X) (cZero b E) hKM hM hθ hs₁ hρ
      have hW1 : C₃ / (W : ℝ) ^ 2 ≤ C₃ := by
        rcases Nat.eq_zero_or_pos W with h0 | h0
        · simp [h0]; exact hC₃
        · exact div_le_self hC₃ (one_le_pow₀ (by exact_mod_cast h0))
      have hGn : ‖G‖ ≤ ‖F‖ + C₃ := by
        have := norm_le_insert' G F
        linarith only [this, hT', hW1]
      have h2' : ‖thetaStar b E s • passiveF b E X‖ ≤ Bf := (norm_smul_le _ _).trans
        (le_trans (mul_le_mul hθ1 hf (norm_nonneg _) zero_le_one) (le_of_eq (one_mul _)))
      have hFn' : Ct * Cf * (Cf * CD * Cf) + (Cr + ‖cZero b E‖ * Cf) * (Cf * Cf) ≤
          Ct * Cf * (Cf * CD * Cf) + (Cr + cL * Cf) * (Cf * Cf) := by gcongr
      have hGB : ‖G - thetaStar b E s • passiveF b E X‖ ≤ BgL := by
        refine (norm_sub_le _ _).trans ?_
        rw [hBgLd]; linarith only [hGn, h2', hFn, hFn', hBfle]
      calc ‖G - thetaStar b E s • passiveF b E X‖ ≤ BgL := hGB
        _ ≤ BgL / dd * jetDistance0 b E X := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hdd]; exact mul_le_mul_of_nonneg_left hdom.le hBgL
        _ ≤ BgL / dd * epsOf b E s X := mul_le_mul_of_nonneg_left
            (by linarith only [e01, sq_nonneg ((W : ℝ)⁻¹)]) (by positivity)
        _ ≤ (C₃ + KonL + BgL / dd) * epsOf b E s X := by
            have h0 : 0 ≤ (C₃ + KonL) * epsOf b E s X := by positivity
            linarith only [h0]
  have hsplit : G - (thetaStar b E s / (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) /
      (W : ℂ))) • passiveF b E X = (G - thetaStar b E s • passiveF b E X) +
      (thetaStar b E s • passiveF b E X - (thetaStar b E s / (1 + (alphaCoef b E : ℂ) *
        (passiveMass b E X : ℂ) / (W : ℂ))) • passiveF b E X) := by abel
  have hαB : α * Bf ≤ αU * BfL := mul_le_mul hαle hBfle hBf hαU
  rw [hsplit]
  calc _ ≤ (C₃ + KonL + BgL / dd) * epsOf b E s X + α * Bf * epsOf b E s X :=
        (norm_add_le _ _).trans (add_le_add hfin hcorr)
    _ ≤ (C₃ + KonL + BgL / dd) * epsOf b E s X + αU * BfL * epsOf b E s X := by gcongr
    _ = _ := by ring

end BlockBand.Transmission.SourceMixingBulk
