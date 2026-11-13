module

public import BlockBand.Transmission.PassiveCovariance.M5Near
public import BlockBand.Transmission.PassiveCovariance.VMatched

/-!
# The mean `m6_p = E[K̂𝒢Π𝒢ᴴP_p𝒢]₁₁ ↦ B_pR*R + σv_pR` (index `(1, p)` of `alpFamI`)

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` with
`δ = δ₀ + δ₁ + q/W ≤ d`, stationary jet `s`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on
`b, E, s` only, uniformly in `W ≥ W₀`, `X`, `p` and the vectors. Operator norm.

* `alpFamI_one`: `alpFamI (1, p) = K̂𝒢Π𝒢ᴴP_p𝒢` pointwise.
* `m6_block`: `‖(K̂E[𝒢Π𝒢ᴴP_p𝒢])₀₀ - KM(s₁X₀₀ + S_p(E𝒢)₀₀)‖ ≤ C/W²` (`weightedBlock` at
  `![2,0] (dV p)`; `X = E[𝒢ᴴP_p𝒢]`, `S_p = σ₁(v^p)`; the `(Ew)₀₀` term vanishes since `w = Π⋯`).
* **`alpINear_one hA p`**: `MeanNear` for the single word `alpFamI (1, p)` with leading value
  `leadM6 p = B_pR*R + σv_pR`, from `X₀₀ ≈ rB_pMᴴ(E𝒢)₀₀` (`gsMean_block`), `(E𝒢)₀₀ ≈ M`, `KM ≈ 1`,
  `M ≈ R`, `s₁ ≈ 1`, `rB_p ≈ B_p` (`tP_matched`, `rB_star_eq`), `S_p ≈ σv_p` (`svP_matched`).
* **`alpINear_holds hA : MeanNear alpFamI leadAlpI`** (with `alpINear_zero`).
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

theorem alpFamI_one (p : Fin 2) (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    alpFamI (1, p) b E W X ω = kHat b E X * (gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ *
      (bProj p * gRes b E X ω)))) := by
  simp [alpFamI, wordAlpha, wLeft, wLetter, gSide, wordVal_zero, Matrix.mul_assoc]

/-- The block form of `m6_p`. -/
theorem m6_block (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖blkAt (kHat b E X * matrixExpect (layerLaw W b .oneBlockOnePort) (fun ω => gRes b E X ω *
            (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 0 0 -
          SourceMixing.kmOf b E X * (SourceMixing.sOne b E X • blkAt (gsMean b E X p) 0 0 +
            svP b E X p • blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hw⟩ := weightedBlock hA hb0 hb h1 h2 2 1
  refine ⟨C, W₁, hC, fun W hW X hX p => ?_⟩
  have hT := hw W hW X hX 2 le_rfl ![2, 0] (dV p) (norm_dV_le p)
  rw [Fin.sum_univ_two] at hT
  set μ := layerLaw W b .oneBlockOnePort
  have e1 : (fun ω => gRes b E X ω * wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordVal_V]
  have e2 : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![2, 0] (dV p)) =
      fun ω => portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)) :=
    funext fun ω => by rw [wordVal_V]
  have e3 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω)ᴴ) :=
    funext fun ω => by rw [wordAlpha_V0]
  have e4 : (fun ω => gRes b E X ω * wordAlpha (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω * (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))) :=
    funext fun ω => by rw [wordAlpha_V1]
  have e5 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 0) =
      fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω) :=
    funext fun ω => by rw [wordGamma_V0]
  have e6 : (fun ω => wordGamma (kHat b E X) (gRes b E X ω) 2 ![2, 0] (dV p) 1) =
      fun ω => gRes b E X ω := funext fun ω => by rw [wordGamma_V1]
  obtain ⟨p0, -⟩ := blkAt_expect_portProj (μ := μ)
    (fun ω => (gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))
  rw [e1, e2, e3, e4, e5, e6, p0, zero_add] at hT
  exact hT

/-- **`m6_p ↦ B_pR*R + σv_pR`**: the index `(1, p)` of `MeanNear alpFamI leadAlpI`. -/
theorem alpINear_one (hA : PassiveLayer.PassiveBoundsStatement) (p : Fin 2) :
    MeanNear (ι := Unit) (fun _ => alpFamI (1, p)) (fun _ => leadAlpI (1, p)) := by
  intro b hb0 hb E h1 h2 s hs
  obtain ⟨Cw, Ww, hCw, hwb⟩ := m6_block hA hb0 hb h1 h2
  obtain ⟨d₁, Cb, Wb, hd₁, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₂, Cs, Ws, hd₂, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₃, Ct, Wt, hd₃, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨d₄, Cv, Wv, hd₄, hCv, hsv⟩ := svP_matched hA hb0 hb h1 h2 s hs
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsMean_block hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := SourceMixing.norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨CV, WV, hCV, hVb⟩ := vP_blocks hA hb0 hb h1 h2
  set ηi := (etaZ b E)⁻¹
  have hη : 0 ≤ ηi := (inv_pos.mpr (etaZ_pos b E (by linarith) h1 h2)).le
  set Cr := 1 + Ct
  set c2 := Cs * Cg + Cs * (Cr * (Cb * CD)) + Cv * CD
  set c3 := Cs * (Cr * (Cb * Cb)) + Cv * Cb
  set C := Cw + CK * c2 + Cb * c3 + (Cs * (Cr * (Cb * Cb)) + Cr * (Cb * Cb) + Cr * (Cb * ηi) +
    Ct * (ηi * ηi) + Cv * Cb + Cv * ηi)
  refine ⟨min (min d₁ d₂) (min d₃ d₄), C,
    max (max (max Ww Wb) (max Ws Wt)) (max (max Wv Wg) (max (max WD WK) (max WV 1))),
    lt_min (lt_min hd₁ hd₂) (lt_min hd₃ hd₄), by positivity, fun W hW X hX hδ _ u v => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWw, hWb⟩, hWs, hWt⟩, ⟨hWv, hWg⟩, ⟨hWD, hWK⟩, hWV, hW1⟩ := hW
  obtain ⟨h0, he⟩ := jetDelta_bounds (b := b) (E := E) s hX.posSemidef hW1
  have hd := h0.trans hδ
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd1, hd2⟩, hd3, hd4⟩ := hd
  obtain ⟨hM, -, hR, hKM1, hMR, -⟩ := hmb W hWb X hX hd1
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs X hX hd2
  have ht := htm W hWt X hX hd3
  obtain ⟨hS, hSl⟩ := hsv W hWv X hX hd4 p
  obtain ⟨-, hX00⟩ := hGs W hWg X hX p
  obtain ⟨-, -, -, -, -, -, hE0, -, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, -, hKD, -⟩ := hK W hWK X hX
  obtain ⟨-, hentV, -, -⟩ := hVb W hWV X hX p
  have hT := hwb W hWw X hX p
  set μ := layerLaw W b .oneBlockOnePort
  set e := SourceMixing.epsOf b E s X
  have he0 : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hint : ∀ i j, Integrable (fun ω => alpFamI (1, p) b E W X ω i j) μ := fun i j => by
    simp only [alpFamI_one, Matrix.mul_apply]
    exact integrable_finsetSum _ fun k _ => (hentV k j).const_mul _
  show ‖(∫ ω, star (physVec u) ⬝ᵥ (alpFamI (1, p) b E W X ω *ᵥ physVec v) ∂μ) -
    bilinear u (leadM6 b E s X p) v‖ ≤ _
  rw [integral_form _ hint]
  have ef : alpFamI (1, p) b E W X = fun ω => kHat b E X * (gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω)))) := funext (alpFamI_one p b E X)
  rw [ef, ← SourceMixing.mul_matrixExpect' _ _ hentV]
  refine norm_bilinear_sub_le u v _ _ ?_
  set Y := blkAt (kHat b E X * matrixExpect μ (fun ω => gRes b E X ω *
    (portProj * ((gRes b E X ω)ᴴ * (bProj p * gRes b E X ω))))) 0 0
  set KM := SourceMixing.kmOf b E X
  set M := SourceMixing.mOf b E X
  set R := passiveResolvent b E X
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set X0 := blkAt (gsMean b E X p) 0 0
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set r := rB b E X p
  have hKMn : ‖KM‖ ≤ CK := (norm_blkAt_le _ 0 0).trans hKD
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht 0 p).1 (ht 1 p).1))
  have hrl : ‖r - leadB b p‖ ≤ Ct * e := by
    rw [← rB_star_eq hb0 hb p]
    have e' : r - (ind 0 p + sig1 b (tStar b 0 p) (tStar b 1 p)) =
        sig1 b (tP b E X 0 p - tStar b 0 p) (tP b E X 1 p - tStar b 1 p) := by
      simp only [r, rB, sig1]; ring
    rw [e']; exact norm_sig1_le hb0 hb (ht 0 p).2 (ht 1 p).2
  have hMh : ‖Mᴴ‖ ≤ Cb := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  have hW2 : ∀ c : ℝ, 0 ≤ c → c / (W : ℝ) ^ 2 ≤ c * e := fun c hc =>
    div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hc
  set Q := s₁ • X0 + S • G0
  set Q1 := s₁ • (r • (Mᴴ * M)) + S • M
  -- the decomposition
  have eq : Y - leadM6 b E s X p = (Y - KM * Q) + KM * (Q - Q1) + (KM - 1) * Q1 +
      ((s₁ - 1) • (r • (Mᴴ * M)) + r • (Mᴴ * (M - R)) + r • ((M - R)ᴴ * R) +
        (r - leadB b p) • (Rᴴ * R) + S • (M - R) + (S - leadSv b E s p) • R) := by
    simp only [leadM6, Q, Q1, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, conjTranspose_sub,
      smul_sub, sub_smul, one_smul]
    abel
  have eQ : Q - Q1 = s₁ • (X0 - r • (Mᴴ * G0)) + s₁ • (r • (Mᴴ * (G0 - M))) + S • (G0 - M) := by
    simp only [Q, Q1, Matrix.mul_sub, smul_sub]; abel
  rw [eq]
  have t1 : ‖Y - KM * Q‖ ≤ Cw * e := hT.trans (hW2 Cw hCw)
  have hQ : ‖Q - Q1‖ ≤ c2 * e := by
    rw [eQ]
    have a1 : ‖s₁ • (X0 - r • (Mᴴ * G0))‖ ≤ Cs * (Cg / (W : ℝ) ^ 2) :=
      (norm_smul_le _ _).trans (mul_le_mul hs1n hX00 (norm_nonneg _) hCs)
    have a2 : ‖s₁ • (r • (Mᴴ * (G0 - M)))‖ ≤ Cs * (Cr * (Cb * (CD / (W : ℝ) ^ 2))) :=
      (norm_smul_le _ _).trans (mul_le_mul hs1n ((norm_smul_le _ _).trans (mul_le_mul hr
        ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMh hE0 (norm_nonneg _) hCb))
        (by positivity) (by positivity))) (by positivity) hCs)
    have a3 : ‖S • (G0 - M)‖ ≤ Cv * (CD / (W : ℝ) ^ 2) :=
      (norm_smul_le _ _).trans (mul_le_mul hS hE0 (norm_nonneg _) hCv)
    refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add a1 a2))
      a3).trans ?_)
    rw [show Cs * (Cg / (W : ℝ) ^ 2) + Cs * (Cr * (Cb * (CD / (W : ℝ) ^ 2))) +
      Cv * (CD / (W : ℝ) ^ 2) = c2 / (W : ℝ) ^ 2 by simp only [c2]; ring]
    exact hW2 c2 (by positivity)
  have t2 : ‖KM * (Q - Q1)‖ ≤ CK * c2 * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKMn hQ (norm_nonneg _) hCK).trans
      (le_of_eq (by ring)))
  have hQ1 : ‖Q1‖ ≤ c3 :=
    (norm_add_le _ _).trans (add_le_add ((norm_smul_le _ _).trans (mul_le_mul hs1n
      ((norm_smul_le _ _).trans (mul_le_mul hr ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hMh hM (norm_nonneg _) hCb)) (by positivity) (by positivity)))
      (by positivity) hCs)) ((norm_smul_le _ _).trans (mul_le_mul hS hM (norm_nonneg _) hCv)))
  have t3 : ‖(KM - 1) * Q1‖ ≤ Cb * c3 * e :=
    (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul hKM1 hQ1 (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have hMM : ‖Mᴴ * M‖ ≤ Cb * Cb := (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMh hM
    (norm_nonneg _) hCb)
  have u1 : ‖(s₁ - 1) • (r • (Mᴴ * M))‖ ≤ Cs * (Cr * (Cb * Cb)) * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hs1 ((norm_smul_le _ _).trans (mul_le_mul hr hMM
      (norm_nonneg _) (by positivity))) (by positivity) (by positivity)).trans (le_of_eq (by ring)))
  have u2 : ‖r • (Mᴴ * (M - R))‖ ≤ Cr * (Cb * Cb) * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hr ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hMh hMR (norm_nonneg _) hCb)) (by positivity) (by positivity)).trans
      (le_of_eq (by ring)))
  have hMRh : ‖(M - R)ᴴ‖ ≤ Cb * e := by rw [Matrix.l2_opNorm_conjTranspose]; exact hMR
  have u3 : ‖r • ((M - R)ᴴ * R)‖ ≤ Cr * (Cb * ηi) * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hr ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hMRh hR (norm_nonneg _) (by positivity))) (by positivity) (by positivity)).trans
      (le_of_eq (by ring)))
  have hRh : ‖Rᴴ‖ ≤ ηi := by rw [Matrix.l2_opNorm_conjTranspose]; exact hR
  have u4 : ‖(r - leadB b p) • (Rᴴ * R)‖ ≤ Ct * (ηi * ηi) * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hrl ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hRh hR (norm_nonneg _) hη)) (by positivity) (by positivity)).trans
      (le_of_eq (by ring)))
  have u5 : ‖S • (M - R)‖ ≤ Cv * Cb * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hS hMR (norm_nonneg _) hCv).trans (le_of_eq (by ring)))
  have u6 : ‖(S - leadSv b E s p) • R‖ ≤ Cv * ηi * e :=
    (norm_smul_le _ _).trans ((mul_le_mul hSl hR (norm_nonneg _) (by positivity)).trans
      (le_of_eq (by ring)))
  have hu : ‖(s₁ - 1) • (r • (Mᴴ * M)) + r • (Mᴴ * (M - R)) + r • ((M - R)ᴴ * R) +
      (r - leadB b p) • (Rᴴ * R) + S • (M - R) + (S - leadSv b E s p) • R‖ ≤
      (Cs * (Cr * (Cb * Cb)) + Cr * (Cb * Cb) + Cr * (Cb * ηi) + Ct * (ηi * ηi) + Cv * Cb +
        Cv * ηi) * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add u1 u2)) u3)) u4)) u5)) u6).trans (le_of_eq (by ring))
  have hsum : ‖(Y - KM * Q) + KM * (Q - Q1) + (KM - 1) * Q1 +
      ((s₁ - 1) • (r • (Mᴴ * M)) + r • (Mᴴ * (M - R)) + r • ((M - R)ᴴ * R) +
        (r - leadB b p) • (Rᴴ * R) + S • (M - R) + (S - leadSv b E s p) • R)‖ ≤ C * e := by
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add t1 t2)) t3)) hu).trans (le_of_eq ?_)
    simp only [C]; ring
  exact hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- **`MeanNear alpFamI leadAlpI`** (`m5_p ↦ A_pR`, `m6_p ↦ B_pR*R + σv_pR`). -/
theorem alpINear_holds (hA : PassiveLayer.PassiveBoundsStatement) : MeanNear alpFamI leadAlpI :=
  meanNear_of_forall fun i => by
    obtain ⟨k, p⟩ := i
    fin_cases k
    · exact alpINear_zero hA p
    · exact alpINear_one hA p

end BlockBand.Transmission.PassiveCovariance
