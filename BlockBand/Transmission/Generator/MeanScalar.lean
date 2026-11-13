module

public import BlockBand.Transmission.Generator.RefinedSre

/-!
# Complex `s₁`, the `G`-weighted `u`-expansion and the weighted scalar step

* `rf_s_cplx`: the complex form of `rf_sre`: `‖s₁D - bhι‖ ≤ (I_zC₂ + 2C_fC_D)/W²`
  (so `Im s₁ = O(W⁻²)` as well as `Re s₁`).
* `wm_u_expand`: for any `G ⪰ 0`, `u_G = Tr(KMᴴGKM)` has
  `|u_G - Tr G - 2Re(ωTr(G(R - c₀))) - Tr G·Im ω/η| ≤ |ω|²Tr G(2‖R‖‖M‖ + ‖M‖²)`.
* `wm_scalar`: `rf_scalar` with the numerator weighted by `G` and the denominator still
  carrying `u = u_Q`.
* `wm_ratio_c`: `|(η - ω_i)/η/(1+x) - 1/(1+y)| ≤ |ω_i/η| + x + y` (`x, y ≥ 0`).
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
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Complex form of `rf_re_s_two`. -/
theorem rf_s_two_c {s : ℂ} {L D E₁ ι c ε₂ Cs : ℝ} (hsL : ‖s * L - c‖ ≤ ε₂)
    (hιL : ι * L = D + E₁) (hs : ‖s‖ ≤ Cs) :
    ‖s * D - c * ι‖ ≤ |ι| * ε₂ + Cs * |E₁| := by
  have e : s * D - c * ι = ι * (s * L - c) - s * E₁ := by
    have : (D : ℂ) = ι * L - E₁ := by exact_mod_cast (by linarith : D = ι * L - E₁)
    rw [this]; ring
  rw [e]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hsL (abs_nonneg _)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

/-- **Complex `s₁`** (copy of `rf_sre` with the complex conclusion). -/
theorem rf_s_cplx (hW1 : 1 ≤ W) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {X : Matrix (Fin W) (Fin W) ℂ} {C2 Cf CD Iz : ℝ}
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C2 / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hh : |Complex.normSq (vOf b E X) - 1| ≤ 1 / 2)
    (hιb : |(zetaX b E X).im| ≤ Iz) :
    ‖sOne b E X * (((b * Complex.normSq (vOf b E X) * etaZ b E +
        ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) *
        (((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re / W)) : ℝ) : ℂ) -
      ((b * Complex.normSq (vOf b E X) : ℝ) : ℂ) * (((zetaX b E X).im : ℝ) : ℂ)‖ ≤
      (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 := by
  set M := mOf b E X
  set v := vOf b E X
  set h := Complex.normSq v
  set u := (Mᴴ * passiveY X * M).trace.re
  have hhhi : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hAP := mm_trace_posSemidef (Matrix.posSemidef_self_mul_conjTranspose M)
  set A := (aOf b E X).re
  have hAeq : aOf b E X = (A : ℂ) := by
    refine Complex.ext (by simp [A]) ?_
    simp only [aOf, Complex.ofReal_im]
    rw [hAP.2]; simp [Complex.mul_im]
  have hheq : hOf b E X = (h : ℂ) := by simp only [hOf, h, Complex.mul_conj]; rfl
  have hward := mm_ward X M (zetaX b E X) hzM
  have hy : ((W : ℂ)⁻¹ * (Mᴴ * passiveY X * M).trace).re = u / W := by
    rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      div_eq_inv_mul]
  rw [hy] at hward
  obtain ⟨hm1, hm2⟩ := meanTr_eq_blk b E X hG
  have hd1 : ‖meanTr b E X 0 - (W : ℂ)⁻¹ * M.trace‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [hm1]; exact (norm_normTrace_sub_le _ _).trans hB0
  have hd2 : ‖meanTr b E X 3 - v‖ ≤ CD / (W : ℝ) ^ 2 := by
    have e1 := normTrace_smul_one hW1 v
    rw [hm2]
    calc _ = ‖(W : ℂ)⁻¹ * (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1).trace -
          (W : ℂ)⁻¹ * (v • (1 : Matrix (Fin W) (Fin W) ℂ)).trace‖ := by rw [e1]
      _ ≤ _ := (norm_normTrace_sub_le _ _).trans hB1
  have hι : (zetaX b E X).im = (1 - 2 * b) * (-(meanTr b E X 0).im) +
      b * (-(meanTr b E X 3).im) := im_zetaOf b E _ _
  have hvim : v.im = -h * (etaZ b E - b * (meanTr b E X 0).im) := by
    have := mm_inv_im (boundaryZ b E - (b : ℂ) * meanTr b E X 0)
    rw [show (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹ = v from rfl] at this
    rw [this, Complex.mul_conj, Complex.ofReal_re, Complex.sub_im, Complex.im_ofReal_mul]; rfl
  have hE₁ := mm_im_algebra hb0 hb (Complex.normSq_nonneg _) hhhi hward hι hvim hd1 hd2
  set ι := (zetaX b E X).im
  set k := (1 - 2 * b) + b ^ 2 * h
  set L := 1 - k * A
  set D := b * h * etaZ b E + k * (u / W)
  have hsL : ‖sOne b E X * (L : ℂ) - ((b * h : ℝ) : ℂ)‖ ≤ C2 / (W : ℝ) ^ 2 := by
    rw [hAeq, hheq] at hS
    convert hS using 2; simp only [L, k, khOf, hheq]; push_cast; ring
  have hres := rf_s_two_c hsL (show ι * L = D + (ι * L - D) by ring) hsn
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans hsn
  have hε : |ι| * (C2 / (W : ℝ) ^ 2) + Cf * |ι * L - D| ≤ (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 := by
    have hC2 : 0 ≤ C2 / (W : ℝ) ^ 2 := (norm_nonneg _).trans hsL
    have a1 : |ι| * (C2 / (W : ℝ) ^ 2) ≤ Iz * (C2 / (W : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hιb hC2
    have a2 : Cf * |ι * L - D| ≤ Cf * (2 * (CD / (W : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hE₁ hCf
    have e : (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 =
        Iz * (C2 / (W : ℝ) ^ 2) + Cf * (2 * (CD / (W : ℝ) ^ 2)) := by ring
    rw [e]; linarith
  exact hres.trans hε

/-- **`G`-weighted second-order expansion** of `u_G = Tr(KMᴴGKM)`, `M = R·KM`, `KM = 1 + ωM`. -/
theorem wm_u_expand {G R M KM : Matrix (Fin W) (Fin W) ℂ} {ω : ℂ} {η : ℝ} (hη : 0 < η)
    (hGp : G.PosSemidef) (hRKM : R * KM = M) (hKM : KM = 1 + ω • M) :
    |(KMᴴ * G * KM).trace.re - G.trace.re -
        2 * (ω * (G * (R - (2 * Complex.I * (η : ℂ))⁻¹ • 1)).trace).re -
        G.trace.re * ω.im / η| ≤
      ‖ω‖ ^ 2 * G.trace.re * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) := by
  set c₀ : ℂ := (2 * Complex.I * (η : ℂ))⁻¹
  set q := G.trace.re
  have hq0 : 0 ≤ q := (mm_trace_posSemidef hGp).1
  have hTrQ : G.trace = (q : ℂ) := (mm_trace_posSemidef hGp).2
  set τ := (G * M).trace
  set σ := (G * (M * Mᴴ)).trace
  set ρ := (G * (R * M)).trace
  have hstar : (G * Mᴴ).trace = star τ := by
    rw [← trace_conjTranspose, conjTranspose_mul, hGp.1.eq, trace_mul_comm]
  have hexp : (KMᴴ * G * KM).trace = (q : ℂ) + ω * τ + star (ω * τ) + (ω * star ω) * σ := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm, hKM]
    simp only [conjTranspose_add, conjTranspose_one, conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_smul, smul_eq_mul]
    rw [hTrQ, hstar, star_mul', ← Matrix.mul_assoc G M Mᴴ]
    simp only [σ]
    rw [Matrix.mul_assoc]
    ring
  have hM : M = R + ω • (R * M) := by
    conv_lhs => rw [← hRKM, hKM]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hτ : τ = (G * (R - c₀ • 1)).trace + c₀ * q + ω * ρ := by
    simp only [τ]
    conv_lhs => rw [hM]
    rw [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, Matrix.mul_sub, trace_sub,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, hTrQ, smul_eq_mul, smul_eq_mul]
    ring
  have hu : (KMᴴ * G * KM).trace.re = q + 2 * (ω * τ).re + ((ω * star ω) * σ).re := by
    rw [hexp]; simp only [Complex.add_re, Complex.ofReal_re, Complex.star_def, Complex.conj_re]
    ring
  have hτre : (ω * τ).re = (ω * (G * (R - c₀ • 1)).trace).re + q * ω.im / (2 * η) +
      (ω * ω * ρ).re := by
    rw [hτ, mul_add, mul_add, Complex.add_re, Complex.add_re, ← mul_assoc ω ω ρ]
    have : (ω * (c₀ * q)).re = (ω * c₀).re * q := by
      rw [← mul_assoc]; simp [Complex.mul_re]
    rw [this, rf_re_mul_cZero hη]; ring
  have hρ : ‖ρ‖ ≤ ‖R‖ * ‖M‖ * q := by
    simp only [ρ]; rw [trace_mul_comm]
    exact (norm_trace_mul_posSemidef_le hGp _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) hq0)
  have hσ : ‖σ‖ ≤ ‖M‖ ^ 2 * q := by
    simp only [σ]; rw [trace_mul_comm]
    refine (norm_trace_mul_posSemidef_le hGp _).trans (mul_le_mul_of_nonneg_right ?_ hq0)
    refine (Matrix.l2_opNorm_mul _ _).trans (le_of_eq ?_)
    rw [Matrix.l2_opNorm_conjTranspose, sq]
  have e : (KMᴴ * G * KM).trace.re - q - 2 * (ω * (G * (R - c₀ • 1)).trace).re - q * ω.im / η =
      2 * (ω * ω * ρ).re + ((ω * star ω) * σ).re := by
    rw [hu, hτre]; field_simp; ring
  rw [e]
  have n1 : |2 * (ω * ω * ρ).re| ≤ 2 * (‖ω‖ ^ 2 * (‖R‖ * ‖M‖ * q)) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans ?_) (by norm_num)
    rw [norm_mul, norm_mul, ← sq]
    exact mul_le_mul_of_nonneg_left hρ (by positivity)
  have n2 : |((ω * star ω) * σ).re| ≤ ‖ω‖ ^ 2 * (‖M‖ ^ 2 * q) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, Complex.star_def, Complex.norm_conj, ← sq]
    exact mul_le_mul_of_nonneg_left hσ (by positivity)
  calc |2 * (ω * ω * ρ).re + ((ω * star ω) * σ).re|
      ≤ |2 * (ω * ω * ρ).re| + |((ω * star ω) * σ).re| := abs_add_le _ _
    _ ≤ 2 * (‖ω‖ ^ 2 * (‖R‖ * ‖M‖ * q)) + ‖ω‖ ^ 2 * (‖M‖ ^ 2 * q) := add_le_add n1 n2
    _ = _ := by ring

/-- **Weighted scalar step**: `rf_scalar` with numerator `u_G` (weight `g = Tr G`) and the
denominator `bhη + k_h u/W` still at `u = u_Q`. -/
theorem wm_scalar {η b h u q W ωi t ρ Li Cm e τ KR uG g tG ρG τG : ℝ} (hη : 0 < η)
    (hLi : η⁻¹ ≤ Li) (hb0 : 0 < b) (hb : b < 1 / 2) (hCm : 0 ≤ Cm) (he : 0 ≤ e)
    (hCme : Cm * e * Li ≤ 1) (hCme2 : Cm * e ≤ 1 / 2)
    (hh : |h - 1| ≤ Cm * e) (hq : 0 ≤ q) (hu : 0 ≤ u) (hW : 0 < W)
    (hωi : |ωi| ≤ Cm * e) (huexp : |u - q - t - q * ωi / η| ≤ ρ) (hρ : ρ ≤ Cm * e * (KR * (e * q)))
    (hKR : 0 ≤ KR) (ht : |t| ≤ 2 * Cm * e * τ) (hτ : τ ≤ 3 / 2 * Li * q)
    (hg : 0 ≤ g) (hGexp : |uG - g - tG - g * ωi / η| ≤ ρG)
    (hρG : ρG ≤ Cm * e * (KR * (e * g))) (htG : |tG| ≤ 2 * Cm * e * τG) :
    |b * h * (η - ωi) * uG / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) -
        g / (1 + (1 - b) ^ 2 / (b * η) * q / W)| ≤
      4 * Cm * (e * τG) + (Cm ^ 2 * Li ^ 2 + 2 * Cm * KR) * (e ^ 2 * g) +
        (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q * g / W) := by
  have hLi0 : 0 < Li := lt_of_lt_of_le (inv_pos.mpr hη) hLi
  have hh1 : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith
  have hh2 : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hh0 : 0 < h := by linarith
  have hc : 0 ≤ 1 - 2 * b := by linarith
  have hbhη : 0 < b * h * η := by positivity
  obtain ⟨κ', hκdef⟩ : ∃ x, x = ((1 - 2 * b) + b ^ 2 * h) / (b * h * η) := ⟨_, rfl⟩
  obtain ⟨α, hαdef⟩ : ∃ x, x = (1 - b) ^ 2 / (b * η) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ' := by rw [hκdef]; positivity
  have hα0 : 0 ≤ α := by rw [hαdef]; positivity
  have hκle : κ' ≤ 4 * Li / b := by rw [hκdef]; exact rf_kappa_le hη hLi hb0 hb hh1 hh2
  have hκα : |κ' - α| ≤ 2 * Li / b * |h - 1| := by
    rw [hκdef, hαdef]; exact rf_kappa_sub hη hLi hb0 hb hh1
  have hratio : b * h * (η - ωi) * uG / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) =
      ((η - ωi) * uG / η) / (1 + κ' * u / W) := by
    rw [hκdef]; field_simp
  rw [hratio, ← hαdef]
  have hA : 1 ≤ 1 + κ' * u / W := by have : 0 ≤ κ' * u / W := by positivity
                                     linarith
  have hB : 1 ≤ 1 + α * q / W := by have : 0 ≤ α * q / W := by positivity
                                    linarith
  refine (rf_ratio hg hA hB).trans ?_
  have hωη : |ωi / η| ≤ Cm * e * Li := by
    rw [abs_div, abs_of_pos hη, div_eq_mul_inv]
    exact mul_le_mul hωi hLi (inv_pos.mpr hη).le (by positivity)
  -- numerator
  obtain ⟨rG, hrG⟩ : ∃ x, x = uG - g - tG - g * ωi / η := ⟨_, rfl⟩
  have huG' : uG = g + tG + g * ωi / η + rG := by rw [hrG]; ring
  have hN := rf_numer hη hωη hCme hg huG'
  have hrGρ : |rG| ≤ ρG := by rw [hrG]; exact hGexp
  have hN' : |(η - ωi) * uG / η - g| ≤ 4 * Cm * (e * τG) + (Cm ^ 2 * Li ^ 2 + 2 * Cm * KR) *
      (e ^ 2 * g) := by
    refine hN.trans ?_
    have h1 : g * (Cm * e * Li) ^ 2 = Cm ^ 2 * Li ^ 2 * (e ^ 2 * g) := by ring
    have h2 : 2 * ρG ≤ 2 * Cm * KR * (e ^ 2 * g) := by
      have : Cm * e * (KR * (e * g)) = Cm * KR * (e ^ 2 * g) := by ring
      linarith
    have h3 : 2 * |tG| ≤ 4 * Cm * (e * τG) := by linarith
    linarith
  -- denominator
  obtain ⟨r', hr'⟩ : ∃ x, x = u - q - t - q * ωi / η := ⟨_, rfl⟩
  have hu' : u = q + t + q * ωi / η + r' := by rw [hr']; ring
  have hr'ρ : |r'| ≤ ρ := by rw [hr']; exact huexp
  have ht' : |t| ≤ 3 * Cm * Li * (e * q) := by
    refine ht.trans ?_
    have : 2 * Cm * e * τ ≤ 2 * Cm * e * (3 / 2 * Li * q) :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    linarith
  have hρ' : ρ ≤ KR / 2 * (e * q) := by
    refine hρ.trans ?_
    calc Cm * e * (KR * (e * q)) ≤ 1 / 2 * (KR * (e * q)) :=
          mul_le_mul_of_nonneg_right hCme2 (by positivity)
      _ = _ := by ring
  have huq : |u - q| ≤ (4 * Cm * Li + KR) * (e * q) := by
    have e1 : u - q = t + q * (ωi / η) + r' := by rw [hu']; ring
    have h2 : |q * (ωi / η)| ≤ Cm * Li * (e * q) := by
      rw [abs_mul, abs_of_nonneg hq]
      calc q * |ωi / η| ≤ q * (Cm * e * Li) := mul_le_mul_of_nonneg_left hωη hq
        _ = _ := by ring
    rw [e1]
    have h3 : |t + q * (ωi / η) + r'| ≤ |t| + |q * (ωi / η)| + |r'| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have h4 : 0 ≤ KR / 2 * (e * q) := by positivity
    have h5 : (4 * Cm * Li + KR) * (e * q) = 3 * Cm * Li * (e * q) + Cm * Li * (e * q) +
        KR / 2 * (e * q) + KR / 2 * (e * q) := by ring
    linarith
  have hAB : g * |1 + κ' * u / W - (1 + α * q / W)| ≤
      (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q * g / W) := by
    have e1 : 1 + κ' * u / W - (1 + α * q / W) = (κ' * (u - q) + (κ' - α) * q) / W := by
      field_simp; ring
    rw [e1, abs_div, abs_of_pos hW]
    have a1 : κ' * |u - q| ≤ 4 * Li / b * ((4 * Cm * Li + KR) * (e * q)) :=
      mul_le_mul hκle huq (abs_nonneg _) (by positivity)
    have a2 : |κ' - α| * q ≤ 2 * Li / b * (Cm * e) * q :=
      mul_le_mul_of_nonneg_right (hκα.trans (mul_le_mul_of_nonneg_left hh (by positivity))) hq
    have h1 : |κ' * (u - q) + (κ' - α) * q| ≤
        (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hq]
      have h6 : 2 * Li / b * (Cm * e) * q = 2 * Cm * Li / b * (e * q) := by ring
      have h7 : (4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) =
          4 * Li / b * ((4 * Cm * Li + KR) * (e * q)) + 2 * Cm * Li / b * (e * q) := by ring
      linarith
    calc g * (|κ' * (u - q) + (κ' - α) * q| / W)
        ≤ g * ((4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b) * (e * q) / W) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hW.le) hg
      _ = _ := by ring
  linarith

/-- `|(η - ω_i)/η/(1+x) - 1/(1+y)| ≤ |ω_i/η| + x + y` for `x, y ≥ 0`. -/
theorem wm_ratio_c {η ωi x y : ℝ} (hη : 0 < η) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |(η - ωi) / η / (1 + x) - 1 / (1 + y)| ≤ |ωi / η| + x + y := by
  have e : (η - ωi) / η / (1 + x) - 1 / (1 + y) = -(ωi / η) / (1 + x) + (y - x) / ((1 + x) * (1 + y)) := by
    field_simp; ring
  rw [e]
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  have h2 : (1 : ℝ) ≤ (1 + x) * (1 + y) := by nlinarith
  have a1 : |-(ωi / η) / (1 + x)| ≤ |ωi / η| := by
    rw [abs_div, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 1 + x)]
    exact div_le_self (abs_nonneg (ωi / η)) h1
  have a2 : |(y - x) / ((1 + x) * (1 + y))| ≤ x + y := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + x) * (1 + y))]
    refine (div_le_self (abs_nonneg (y - x)) h2).trans ?_
    rw [abs_le]; constructor <;> linarith
  have := abs_add_le (-(ωi / η) / (1 + x)) ((y - x) / ((1 + x) * (1 + y)))
  linarith

end BlockBand.Transmission.Generator
