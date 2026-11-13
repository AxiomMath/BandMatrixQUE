module

public import BlockBand.Transmission.Generator.MeanDomain

/-!
# On-domain bounds of the one-layer mean `Ū = E[LL*]`

* `wm_onDomain_op` (a): `‖Ū - c·I‖ ≤ K_a1W⁻² + K_a2e + 10L_i/b·q/W`.
* `wm_onDomain_wt` (b): for every `G ⪰ 0`,
  `|Tr(GŪ) - c·Tr G| ≤ K₀W⁻²g + 4C_m eτ_G + K₂e²g + K₃eqg/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **(a) on the domain.** -/
theorem wm_onDomain_op {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e : ℝ} (hLi : (etaZ b E)⁻¹ ≤ Li) (hCme : Cm * e ≤ 1 / 2)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e) (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e)
    (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hU : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤
      C2 / (W : ℝ) ^ 2) :
    ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ ≤
      (Cf + (3 * C2 + Cf * (2 * CD)) * (2 * Li / b)) * (W : ℝ)⁻¹ ^ 2 +
        (Cf * (5 / 2 * Cm) + Cm * Li) * e + 10 * Li / b * (passiveMass b E X / W) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  obtain ⟨hsρ, hD0, hDinv, hKMn, hu0, hu94⟩ :=
    wm_prep hb0 hb h1 h2 hW1 hX hLi hCme hzζ hKM1 hh1 hz2 hsn hG hB0 hB1 hzM hS
  refine wm_op_alg hU hsn hKM1 hKMn hsρ hD0 hDinv ?_
  have hr : wmRho b E X = (etaZ b E - (boundaryZ b E - zetaX b E X).im) / etaZ b E /
      (1 + ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) /
        (b * Complex.normSq (vOf b E X) * etaZ b E) * wmU b E X / W) := by
    have : 0 < Complex.normSq (vOf b E X) := by
      have := neg_abs_le (Complex.normSq (vOf b E X) - 1); linarith
    rw [wmRho, wmD]
    field_simp
  set h := Complex.normSq (vOf b E X)
  set ωi := (boundaryZ b E - zetaX b E X).im
  set q := passiveMass b E X
  set u := wmU b E X
  have hhlo : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith
  have hhhi : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hωi : |ωi| ≤ Cm * e := (Complex.abs_im_le_norm _).trans hzζ
  have hκ'le : ((1 - 2 * b) + b ^ 2 * h) / (b * h * etaZ b E) ≤ 4 * Li / b :=
    rf_kappa_le hη hLi hb0 hb hhlo hhhi
  have hcdef : meanC b E X = 1 / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W) := by
    rw [meanC, one_div]; rfl
  have hρc : |wmRho b E X - meanC b E X| ≤ |ωi / etaZ b E| +
      ((1 - 2 * b) + b ^ 2 * h) / (b * h * etaZ b E) * u / W +
      (1 - b) ^ 2 / (b * etaZ b E) * q / W := by
    rw [hr, hcdef]
    exact wm_ratio_c hη (by have : 0 ≤ 1 - 2 * b := by linarith
                            have : 0 < h := by linarith
                            positivity)
      (by have := passiveMass_nonneg b E hX.posSemidef; positivity)
  have a1 : |ωi / etaZ b E| ≤ Cm * Li * e := by
    rw [abs_div, abs_of_pos hη, div_eq_mul_inv]
    calc |ωi| * (etaZ b E)⁻¹ ≤ Cm * e * Li :=
          mul_le_mul hωi hLi (by positivity) ((abs_nonneg _).trans hωi)
      _ = _ := by ring
  have a2 : ((1 - 2 * b) + b ^ 2 * h) / (b * h * etaZ b E) * u / W ≤ 9 * Li / b * (q / W) := by
    rw [mul_div_assoc]
    calc ((1 - 2 * b) + b ^ 2 * h) / (b * h * etaZ b E) * (u / W) ≤
          4 * Li / b * (9 / 4 * q / W) :=
          mul_le_mul hκ'le (div_le_div_of_nonneg_right hu94 hWpos.le) (div_nonneg hu0 hWpos.le)
            (by positivity)
      _ = _ := by ring
  have a3 : (1 - b) ^ 2 / (b * etaZ b E) * q / W ≤ Li / b * (q / W) := by
    have hq := passiveMass_nonneg b E hX.posSemidef
    have : (1 - b) ^ 2 / (b * etaZ b E) ≤ Li / b := by
      rw [div_le_div_iff₀ (by positivity) hb0]
      have hLiη : 1 ≤ Li * etaZ b E := by
        have := mul_le_mul_of_nonneg_right hLi hη.le
        rwa [inv_mul_cancel₀ hη.ne'] at this
      have : (1 - b) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right this (by positivity)
  have e10 : 10 * Li / b * (q / W) = 9 * Li / b * (q / W) + Li / b * (q / W) := by ring
  linarith

/-- **(b) on the domain**, every weight `G ⪰ 0`. -/
theorem wm_onDomain_wt {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e : ℝ} (hCm : 0 ≤ Cm) (hCD : 0 ≤ CD) (he0 : 0 ≤ e)
    (hLi : (etaZ b E)⁻¹ ≤ Li) (hCme : Cm * e ≤ 1 / 2) (hCmeLi : Cm * e * Li ≤ 1)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e) (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e)
    (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hU : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hM : ‖mOf b E X‖ ≤ CD)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤
      C2 / (W : ℝ) ^ 2)
    (G : Matrix (Fin W) (Fin W) ℂ) (hGp : G.PosSemidef) :
    ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
        ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤
      (Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)) * ((W : ℝ)⁻¹ ^ 2 * G.trace.re) +
      (4 * Cm * (e * ‖(G * passiveF b E X).trace‖) +
      (Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))) * (e ^ 2 * G.trace.re) +
      (4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b) *
        (e * passiveMass b E X * G.trace.re / W)) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hYs := hX.posSemidef
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  obtain ⟨hsρ, hD0, hDinv, hKMn, hu0, -⟩ :=
    wm_prep hb0 hb h1 h2 hW1 hX hLi hCme hzζ hKM1 hh1 hz2 hsn hG hB0 hB1 hzM hS
  refine wm_wt_alg hGp hU hKMn hsρ hD0 hDinv ?_
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set R := passiveResolvent b E X
  set M := mOf b E X
  set KM := kmOf b E X
  set ω := boundaryZ b E - zetaX b E X with hωdef
  have hq : 0 ≤ q := passiveMass_nonneg b E hYs
  obtain ⟨-, hRz⟩ := nearPencil_inverse hb0 hb h1 h2 hYs
  have hKMeq : KM = (boundaryZ b E • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
  have hRKM : R * KM = M := by rw [hKMeq, ← Matrix.mul_assoc, hRz, Matrix.one_mul]
  have hKMω : KM = 1 + ω • M := by
    rw [hKMeq, show boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X =
        ω • 1 + (zetaX b E X • 1 - X) by rw [hωdef, sub_smul]; abel, Matrix.add_mul, hzM,
      Matrix.smul_mul, Matrix.one_mul]
    abel
  have hexp := rf_u_expand hη hYs (show Q = Rᴴ * passiveY X * R from rfl) hRKM hKMω
  change |wmU b E X - q - 2 * (ω * (Q * passiveF b E X).trace).re - q * ω.im / etaZ b E| ≤ _
    at hexp
  have hGexp := wm_u_expand hη hGp hRKM hKMω
  change |(KMᴴ * G * KM).trace.re - G.trace.re - 2 * (ω * (G * passiveF b E X).trace).re -
    G.trace.re * ω.im / etaZ b E| ≤ _ at hGexp
  have hω : ‖ω‖ ≤ Cm * e := hzζ
  have hR : ‖R‖ ≤ Li := (norm_passiveResolvent_le hb0 hb h1 h2 hYs).trans hLi
  set KR := Cm * (2 * Li * CD + CD ^ 2)
  have hKR : 0 ≤ KR := by positivity
  have hρg : ∀ g : ℝ, 0 ≤ g → ‖ω‖ ^ 2 * g * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) ≤
      Cm * e * (KR * (e * g)) := by
    intro g hg
    have a1 : ‖ω‖ ^ 2 ≤ (Cm * e) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
    have a2 : 2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2 ≤ 2 * Li * CD + CD ^ 2 := by
      have := mul_le_mul hR hM (norm_nonneg _) hLi0
      have := pow_le_pow_left₀ (norm_nonneg _) hM 2
      nlinarith
    calc ‖ω‖ ^ 2 * g * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) ≤ (Cm * e) ^ 2 * g * (2 * Li * CD + CD ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right a1 hg) a2 (by positivity) (by positivity)
      _ = _ := by simp only [KR]; ring
  have htg : ∀ x : ℂ, |2 * (ω * x).re| ≤ 2 * Cm * e * ‖x‖ := by
    intro x
    rw [abs_mul, abs_two]
    have := (Complex.abs_re_le_norm (ω * x)).trans (le_of_eq (norm_mul _ _))
    have h3 : ‖ω‖ * ‖x‖ ≤ Cm * e * ‖x‖ := mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    linarith
  have hτ : ‖(Q * passiveF b E X).trace‖ ≤ 3 / 2 * Li * q := by
    have hf := norm_passiveF_le hb0 hb h1 h2 hYs
    have h3 : ‖(Q * passiveF b E X).trace‖ ≤ ‖passiveF b E X‖ * q := by
      rw [trace_mul_comm]
      exact norm_trace_mul_posSemidef_le (hYs.conjTranspose_mul_mul_same _) _
    have h4 : 3 / (2 * etaZ b E) ≤ 3 / 2 * Li := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_left hLi (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right (hf.trans h4) hq)
  have hωi : |ω.im| ≤ Cm * e := (Complex.abs_im_le_norm _).trans hω
  have hg0 : 0 ≤ G.trace.re := (mm_trace_posSemidef hGp).1
  have hsc := wm_scalar hη hLi hb0 hb hCm he0 hCmeLi hCme hh1 hq hu0 hWpos hωi hexp
    (hρg q hq) hKR (htg _) hτ hg0 hGexp (hρg _ hg0) (htg _)
  have e1 : wmRho b E X * (KMᴴ * G * KM).trace.re - meanC b E X * G.trace.re =
      b * Complex.normSq (vOf b E X) * (etaZ b E - ω.im) * (KMᴴ * G * KM).trace.re /
        (b * Complex.normSq (vOf b E X) * etaZ b E + ((1 - 2 * b) +
          b ^ 2 * Complex.normSq (vOf b E X)) * (wmU b E X / W)) -
      G.trace.re / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W) := by
    rw [wmRho, wmD, meanC]
    simp only [alphaCoef, div_eq_mul_inv]
    ring
  rw [e1]
  exact hsc

end BlockBand.Transmission.Generator
