module

public import BlockBand.Transmission.PassiveCovariance.M4Lead

/-!
# The mean `m4_p ↦ B_pR*R + conj σv_p R* + σv_pR + σz_p` (index `(1, p)` of `alpFam`)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` with
`δ = δ₀ + δ₁ + q/W ≤ d`, stationary jet `s`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p` and the vectors. Operator norm.

* **`alpNear_one hA p`**: `MeanNear` for the single word `alpFam (1, p)` with leading value
  `leadM4 p`. Chain: `m4_block` (`Y = KM·Q + O(W⁻²)`, `Q = s₁X'₀₀ + S_pN₀₀ + σz_p·Kgᴴ`),
  `gsN_block` (`X'₀₀ = Mᴴ(rB_pN₀₀ + conj S_p·Kgᴴ) + O(W⁻²)`), `mixedBlock`
  (`N₀₀ = s₁M·KMᴴ + O(W⁻²)`, `Kg = KM + O(W⁻²)`), then `m4_lead` (`KM·Q₂ = leadM4 p + O(ε)`).
* **`alpNear_holds hA : MeanNear alpFam leadAlp`** (with `alpNear_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **`m4_p ↦ leadM4 p`**: the index `(1, p)` of `MeanNear alpFam leadAlp`. -/
theorem alpNear_one (hA : PassiveLayer.PassiveBoundsStatement) (p : Fin 2) :
    MeanNear (ι := Unit) (fun _ => alpFam (1, p)) (fun _ => leadAlp (1, p)) := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨Cw, Ww, hCw, hwb⟩ := m4_block hA hb0 hb h1 h2
  obtain ⟨Cg, Wg, hCg, hgs⟩ := gsN_block hA hb0 hb h1 h2
  obtain ⟨Cm, Wm, hCm, hmix⟩ := SourceMixing.mixedBlock hA hb0 hb h1 h2
  obtain ⟨d₁, CL, WL, hd₁, hCL, hlead⟩ := m4_lead hA hb0 hb h1 h2 s hs
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := SourceMixing.freshU_mean hA hb0 hb h1 h2
  obtain ⟨Cv, Wv, hCv, hVs⟩ := vP_system hA hb0 hb h1 h2
  obtain ⟨Cz, Wz, hCz, hZs⟩ := zP_system hA hb0 hb h1 h2
  obtain ⟨Ct, Wt, hCt, hQb⟩ := tP_blocks hA hb0 hb h1 h2
  obtain ⟨Cw', Ww', hCw', hwm⟩ := SourceMixing.wordMean_bound hA hb0 hb h1 h2 4 1
  set Cr := 1 + Ct
  set c3 := Cf * (CD * (Cr * Cm + Cv * Cm)) + Cv * Cm + Cz * Cm
  set C := Cw + Cf * (Cf * Cg) + Cf * c3 + CL
  refine ⟨d₁, C, max (max (max Ww Wg) (max Wm WL)) (max (max WD Wf) (max (max Wv Wz) (max Wt
    (max Ww' 1)))), hd₁, by positivity, fun W hW X hX hδ _ u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWg⟩, hWm, hWL⟩, ⟨hWD, hWf⟩, ⟨hWv, hWz⟩, hWt, hWw', hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  obtain ⟨-, -, hM, -, -, -, -, -, -, -, -⟩ := hD W hWD X hX
  obtain ⟨hKMn, hs, -⟩ := hF W hWf X hX
  obtain ⟨hS, -⟩ := hVs W hWv X hX p
  obtain ⟨hσ, -⟩ := hZs W hWz X hX p
  obtain ⟨ht, -, -, -⟩ := hQb W hWt X hX 0
  obtain ⟨ht1, -, -, -⟩ := hQb W hWt X hX 1
  obtain ⟨hN, hKg⟩ := hmix W hWm X hX
  have hT := hwb W hWw X hX p
  have hX' := hgs W hWg X hX p
  have hL := hlead W hWL X hX (h0.trans hδ) p
  set μ := layerLaw W b .oneBlockOnePort
  set e := SourceMixing.epsOf b E s X
  have he0 : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hent : ∀ α β, Integrable (fun ω => (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
      (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) : LayerMat W) α β) μ :=
    integrable_entries_of_eq (fun ω => by rw [wordVal_GM4])
      (hwm W hWw' X hX.posSemidef 4 le_rfl ![0, 2, 0, 3] (dZ5 p) (norm_dZ5_le p)).1
  have hint : ∀ i j, Integrable (fun ω => alpFam (1, p) b E W X ω i j) μ := fun i j => by
    simp only [alpFam_one, Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hent k j).const_mul _
  show ‖(∫ ω, star (physVec u) ⬝ᵥ (alpFam (1, p) b E W X ω *ᵥ physVec v) ∂μ) -
    bilinear u (leadM4 b E s X p) v‖ ≤ _
  rw [integral_form _ hint]
  have ef : alpFam (1, p) b E W X = fun ω => kHat b E X * (gRes b E X ω * (portProj *
      ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ)))))) :=
    funext (alpFam_one p b E X)
  rw [ef, ← SourceMixing.mul_matrixExpect' _ _ hent]
  refine norm_bilinear_sub_le u v _ _ ?_
  set Y := blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω * (portProj *
    ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))))) 0 0
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set X0 := blkAt (matrixExpect μ (fun ω => (gRes b E X ω)ᴴ * (bProj p *
    (gRes b E X ω * (portProj * (kHat b E X * gRes b E X ω)ᴴ))))) 0 0
  set N0 := blkAt (matrixExpect μ (fun ω => gRes b E X ω *
    (portProj * (kHat b E X * gRes b E X ω)ᴴ))) 0 0
  set Kg := blkAt (kHat b E X * matrixExpect μ (gRes b E X)) 0 0
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  have hN' : ‖N0 - s₁ • (M * KMᴴ)‖ ≤ Cm / (W : ℝ) ^ 2 := hN
  have hKgh : ‖Kgᴴ - KMᴴ‖ ≤ Cm / (W : ℝ) ^ 2 := by
    rw [SourceMixing.norm_conjTranspose_sub]; exact hKg
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hcS : ‖conj S‖ ≤ Cv := by rw [Complex.norm_conj]; exact hS
  have hMh : ‖Mᴴ‖ ≤ CD := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  have hW2 : ∀ c : ℝ, 0 ≤ c → c / (W : ℝ) ^ 2 ≤ c * e := fun c hc =>
    div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hc
  set Q := s₁ • X0 + S • N0 + σ • Kgᴴ
  set Q1 := s₁ • (Mᴴ * (r • N0 + conj S • Kgᴴ)) + S • N0 + σ • Kgᴴ
  set Q2 := s₁ • (Mᴴ * (r • (s₁ • (M * KMᴴ)) + conj S • KMᴴ)) + S • (s₁ • (M * KMᴴ)) + σ • KMᴴ
  have eq : Y - leadM4 b E s X p = (Y - KM * Q) + KM * (Q - Q1) + KM * (Q1 - Q2) +
      (KM * Q2 - leadM4 b E s X p) := by
    simp only [Matrix.mul_sub]; abel
  have eQ : Q - Q1 = s₁ • (X0 - Mᴴ * (r • N0 + conj S • Kgᴴ)) := by
    simp only [Q, Q1, smul_sub]; abel
  have eQ1 : Q1 - Q2 = s₁ • (Mᴴ * (r • (N0 - s₁ • (M * KMᴴ)) + conj S • (Kgᴴ - KMᴴ))) +
      S • (N0 - s₁ • (M * KMᴴ)) + σ • (Kgᴴ - KMᴴ) := by
    simp only [Q1, Q2, Matrix.mul_sub, Matrix.mul_add, smul_sub, smul_add]; abel
  rw [eq]
  have t1 : ‖Y - KM * Q‖ ≤ Cw * e := hT.trans (hW2 Cw hCw)
  have t2 : ‖KM * (Q - Q1)‖ ≤ Cf * (Cf * Cg) * e := by
    rw [eQ]
    refine (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKMn ((norm_smul_le _ _).trans
      (mul_le_mul hs (hX'.trans (hW2 Cg hCg)) (norm_nonneg _) hCf)) (by positivity) hCf).trans
      (le_of_eq (by ring)))
  have hQ1 : ‖Q1 - Q2‖ ≤ c3 * e := by
    rw [eQ1]
    have a1 : ‖r • (N0 - s₁ • (M * KMᴴ)) + conj S • (Kgᴴ - KMᴴ)‖ ≤
        Cr * (Cm / (W : ℝ) ^ 2) + Cv * (Cm / (W : ℝ) ^ 2) :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_smul_le _ _).trans (mul_le_mul hr hN' (norm_nonneg _) (by positivity)))
        ((norm_smul_le _ _).trans (mul_le_mul hcS hKgh (norm_nonneg _) hCv)))
    have a2 : ‖s₁ • (Mᴴ * (r • (N0 - s₁ • (M * KMᴴ)) + conj S • (Kgᴴ - KMᴴ)))‖ ≤
        Cf * (CD * (Cr * (Cm / (W : ℝ) ^ 2) + Cv * (Cm / (W : ℝ) ^ 2))) :=
      (norm_smul_le _ _).trans (mul_le_mul hs ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hMh a1 (norm_nonneg _) hCD)) (by positivity) hCf)
    have a3 : ‖S • (N0 - s₁ • (M * KMᴴ))‖ ≤ Cv * (Cm / (W : ℝ) ^ 2) :=
      (norm_smul_le _ _).trans (mul_le_mul hS hN' (norm_nonneg _) hCv)
    have a4 : ‖σ • (Kgᴴ - KMᴴ)‖ ≤ Cz * (Cm / (W : ℝ) ^ 2) :=
      (norm_smul_le _ _).trans (mul_le_mul hσ hKgh (norm_nonneg _) hCz)
    refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add a2 a3))
      a4).trans ?_)
    rw [show Cf * (CD * (Cr * (Cm / (W : ℝ) ^ 2) + Cv * (Cm / (W : ℝ) ^ 2))) +
      Cv * (Cm / (W : ℝ) ^ 2) + Cz * (Cm / (W : ℝ) ^ 2) = c3 / (W : ℝ) ^ 2 by simp only [c3]; ring]
    exact hW2 c3 (by positivity)
  have t3 : ‖KM * (Q1 - Q2)‖ ≤ Cf * c3 * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKMn hQ1 (norm_nonneg _) hCf).trans
      (le_of_eq (by ring)))
  have hsum : ‖(Y - KM * Q) + KM * (Q - Q1) + KM * (Q1 - Q2) + (KM * Q2 - leadM4 b E s X p)‖ ≤
      C * e := by
    refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) hL).trans (le_of_eq ?_))
    simp only [C]; ring
  exact hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- **`MeanNear alpFam leadAlp`** (`m2_p ↦ A_pR + σw_p`, `m4_p ↦ leadM4 p`). -/
theorem alpNear_holds (hA : PassiveLayer.PassiveBoundsStatement) : MeanNear alpFam leadAlp :=
  meanNear_of_forall fun i => by
    obtain ⟨k, p⟩ := i
    fin_cases k
    · exact alpNear_zero hA p
    · exact alpNear_one hA p

end BlockBand.Transmission.PassiveCovariance
