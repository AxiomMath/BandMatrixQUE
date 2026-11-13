module

public import BlockBand.Transmission.SourceMixing.Assemble

/-!
# The one-step mean for strictly passive inputs

Hypothesis `PassiveBoundsStatement`. Law `freshLaw W b`, deterministic strictly passive `X`, operator
norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, a stationary jet `s`; constants depend on `b, E, s` only,
uniformly in `W ≥ W₀` and `X`.

The one-step mean estimate when `Y` is positive definite.

* `oneStepMean_strict`:
  `‖E(Lf₊L*) - θ_*(1 + αq/W)⁻¹f‖ ≤ C(δ₀ + δ₁ + q/W + W⁻²)`.
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

theorem norm_passiveF_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ‖passiveF b E X‖ ≤ (etaZ b E)⁻¹ + ‖cZero b E‖ :=
  (norm_sub_le _ _).trans (add_le_add (norm_passiveResolvent_le hb0 hb h1 h2 hY)
    (norm_smul_one_le _))

/-- The one-step mean estimate for strictly passive inputs. -/
theorem oneStepMean_strict (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
            (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            (W : ℝ)⁻¹ ^ 2) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  obtain ⟨C₃, W₃, hC₃, hT⟩ := transportedF_mean hA hb0 hb h1 h2
  obtain ⟨d₀, Cs, Ws, hd₀, hCs, hS⟩ := matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₀', Cb, Wb, hd₀', hCb, hB⟩ := matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hTb⟩ := scalarTheta_blocks hA hb0 hb h1 h2
  obtain ⟨Cr, Wr, hCr, hRb⟩ := scalarRho_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨hθ1, -, -⟩ := norm_thetaStar_le hb0 hb h1 h2 hs
  have hηi : 0 ≤ (etaZ b E)⁻¹ := inv_nonneg.mpr hη.le
  obtain ⟨α, hαd⟩ : ∃ x : ℝ, x = alphaCoef b E := ⟨_, rfl⟩
  have hα : 0 ≤ α := by
    rw [hαd, alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  obtain ⟨Bf, hBfd⟩ : ∃ x : ℝ, x = (etaZ b E)⁻¹ + ‖cZero b E‖ := ⟨_, rfl⟩
  have hBf : 0 ≤ Bf := by rw [hBfd]; positivity
  obtain ⟨Bglob, hBgd⟩ : ∃ x : ℝ, x = Ct * Cf * (Cf * CD * Cf) + (Cr + ‖cZero b E‖ * Cf) *
      (Cf * Cf) + C₃ + Bf := ⟨_, rfl⟩
  have hBg : 0 ≤ Bglob := by rw [hBgd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  obtain ⟨Kon, hKond⟩ : ∃ x : ℝ, x = (Ct * K + K) * (Cf * CD * Cf) + (K * (CD * Cf) + K * Cf +
      (etaZ b E)⁻¹ * K) + (K + ‖cZero b E‖ * K) * (Cf * Cf) + ‖cZero b E‖ * (K * Cf + K) :=
    ⟨_, rfl⟩
  have hKon : 0 ≤ Kon := by rw [hKond]; positivity
  obtain ⟨dd, hddd⟩ : ∃ x : ℝ, x = min d₀ d₀' := ⟨_, rfl⟩
  have hdd : 0 < dd := by rw [hddd]; exact lt_min hd₀ hd₀'
  refine ⟨C₃ + Kon + Bglob / dd + α * Bf, max (max (max W₃ Ws) (max Wb Wf))
    (max (max Wt Wr) WD), by positivity, fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₃, hWs⟩, hWb, hWf⟩, ⟨hWt, hWr⟩, hWD⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hKM, hs₁, -⟩ := hF W hWf X hX
  obtain ⟨-, hθ, -, -, -⟩ := hTb W hWt X hX
  obtain ⟨-, hρ, -, -, -⟩ := hRb W hWr X hX
  obtain ⟨-, -, hM, -⟩ := hD W hWD X hX
  obtain ⟨e0, e1, eq, e01, eall⟩ := epsOf_ge (b := b) (E := E) s hY
  change _ ≤ _ * epsOf b E s X
  have he : 0 ≤ epsOf b E s X := by
    have := sq_nonneg ((W : ℝ)⁻¹); linarith only [this, e0, e01]
  have hT' := hT W hW₃ X hX
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
  have hfin : ‖G - thetaStar b E s • passiveF b E X‖ ≤ (C₃ + Kon + Bglob / dd) * epsOf b E s X := by
    by_cases hdom : jetDistance0 b E X ≤ dd
    · obtain ⟨-, -, hR, hKM1, hMR, -, -, -, -, -⟩ :=
        hB W hWb X hX (hdom.trans (hddd ▸ min_le_right _ _))
      obtain ⟨-, -, hs1, hθθ, hρρ⟩ := hS W hWs X hX (hdom.trans (hddd ▸ min_le_left _ _))
      have lift : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * epsOf b E s X → x ≤ K * epsOf b E s X :=
        fun C' hC' x hx => hx.trans (mul_le_mul_of_nonneg_right hC' he)
      have hCbK : Cb ≤ K := by rw [hKd]; linarith only [hCs]
      have hCsK : Cs ≤ K := by rw [hKd]; linarith only [hCb]
      have hFf := assemble_on (kmOf b E X) (mOf b E X) (passiveResolvent b E X) (thetaOf b E X)
        (sOne b E X) (rhoOf b E X) (thetaStar b E s) (cZero b E) he hK hKM hM hR hθ hθ1
        (lift _ hCbK _ hKM1) (lift _ hCbK _ hMR) (lift _ hCsK _ hs1) (lift _ hCsK _ hθθ)
        (lift _ hCsK _ hρρ)
      rw [← hKond] at hFf
      have e' : G - thetaStar b E s • passiveF b E X = (G - F) + (F - thetaStar b E s •
          (passiveResolvent b E X - cZero b E • 1)) := by rw [passiveF]; abel
      rw [e']
      refine (norm_add_le _ _).trans ?_
      have h0 : 0 ≤ Bglob / dd * epsOf b E s X := by positivity
      calc _ ≤ C₃ * epsOf b E s X + Kon * epsOf b E s X := add_le_add hGF hFf
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
      have hGB : ‖G - thetaStar b E s • passiveF b E X‖ ≤ Bglob := by
        refine (norm_sub_le _ _).trans ?_
        rw [hBgd]; linarith only [hGn, h2', hFn]
      calc ‖G - thetaStar b E s • passiveF b E X‖ ≤ Bglob := hGB
        _ ≤ Bglob / dd * jetDistance0 b E X := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hdd]; exact mul_le_mul_of_nonneg_left hdom.le hBg
        _ ≤ Bglob / dd * epsOf b E s X := mul_le_mul_of_nonneg_left
            (by linarith only [e01, sq_nonneg ((W : ℝ)⁻¹)]) (by positivity)
        _ ≤ (C₃ + Kon + Bglob / dd) * epsOf b E s X := by
            have h0 : 0 ≤ (C₃ + Kon) * epsOf b E s X := by positivity
            linarith only [h0]
  have hsplit : G - (thetaStar b E s / (1 + (alphaCoef b E : ℂ) * (passiveMass b E X : ℂ) /
      (W : ℂ))) • passiveF b E X = (G - thetaStar b E s • passiveF b E X) +
      (thetaStar b E s • passiveF b E X - (thetaStar b E s / (1 + (alphaCoef b E : ℂ) *
        (passiveMass b E X : ℂ) / (W : ℂ))) • passiveF b E X) := by abel
  rw [hsplit]
  calc _ ≤ (C₃ + Kon + Bglob / dd) * epsOf b E s X + α * Bf * epsOf b E s X :=
        (norm_add_le _ _).trans (add_le_add hfin hcorr)
    _ = _ := by ring

end BlockBand.Transmission.SourceMixing
