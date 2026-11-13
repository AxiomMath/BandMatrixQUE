module

public import BlockBand.Transmission.PassiveCovariance.VSysTrace

/-!
# Matched values of `S_p = σ₁(v^p)`: `S_p ↦ σv_p = leadSv p`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive `X` with
`δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`, stationary jet `s`; constants depend on `b, E, s`
only, uniformly in `W ≥ W₀`, `X`, `p`.

* `norm_prod4_sub_le` (algebra): products of four approximate factors.
* `tStar_one_eq`: `t¹_p ↦ [p=1] + b·leadR1 p`; `one_add_tStar`: `1 + bt¹₀ ↦ d_*`.
* **`svP_matched`**: `|S_p| ≤ C`, `|S_p - leadSv p| ≤ C·epsOf`. From `vP_system`,
  `matchedScalars` (`s₁ ≈ 1`), `matchedBasic` (`v ≈ a`, `⟨M²⟩ ≈ -s`, `⟨M²Mᴴ⟩ ≈ B_*`) and
  `tP_matched` (`rB ≈ B_p`, `t¹ ≈ tStar 1`); division by `1 + k₋s` as in `xP_close`.
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

theorem norm_prod4_sub_le {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℂ} {Λ ε : ℝ} (hΛ : 0 ≤ Λ)
    (hx₂ : ‖x₂‖ ≤ Λ) (hx₃ : ‖x₃‖ ≤ Λ) (hx₄ : ‖x₄‖ ≤ Λ)
    (hy₁ : ‖y₁‖ ≤ Λ) (hy₂ : ‖y₂‖ ≤ Λ) (hy₃ : ‖y₃‖ ≤ Λ)
    (h₁ : ‖x₁ - y₁‖ ≤ ε) (h₂ : ‖x₂ - y₂‖ ≤ ε) (h₃ : ‖x₃ - y₃‖ ≤ ε) (h₄ : ‖x₄ - y₄‖ ≤ ε) :
    ‖x₁ * x₂ * x₃ * x₄ - y₁ * y₂ * y₃ * y₄‖ ≤ 4 * Λ ^ 3 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans h₁
  have e : x₁ * x₂ * x₃ * x₄ - y₁ * y₂ * y₃ * y₄ = (x₁ - y₁) * x₂ * x₃ * x₄ +
      y₁ * (x₂ - y₂) * x₃ * x₄ + y₁ * y₂ * (x₃ - y₃) * x₄ + y₁ * y₂ * y₃ * (x₄ - y₄) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl).trans ?_
  simp only [norm_mul]
  have n1 := norm_nonneg (x₁ - y₁); have n2 := norm_nonneg (x₂ - y₂)
  have n3 := norm_nonneg (x₃ - y₃); have n4 := norm_nonneg (x₄ - y₄)
  have a1 := norm_nonneg x₂; have a2 := norm_nonneg x₃; have a3 := norm_nonneg x₄
  have b1 := norm_nonneg y₁; have b2 := norm_nonneg y₂; have b3 := norm_nonneg y₃
  have t1 : ‖x₁ - y₁‖ * ‖x₂‖ * ‖x₃‖ * ‖x₄‖ ≤ ε * Λ * Λ * Λ := by gcongr
  have t2 : ‖y₁‖ * ‖x₂ - y₂‖ * ‖x₃‖ * ‖x₄‖ ≤ Λ * ε * Λ * Λ := by gcongr
  have t3 : ‖y₁‖ * ‖y₂‖ * ‖x₃ - y₃‖ * ‖x₄‖ ≤ Λ * Λ * ε * Λ := by gcongr
  have t4 : ‖y₁‖ * ‖y₂‖ * ‖y₃‖ * ‖x₄ - y₄‖ ≤ Λ * Λ * Λ * ε := by gcongr
  nlinarith

theorem tStar_one_eq {b : ℝ} (hb0 : 0 < b) (p : Fin 2) :
    tStar b 1 p = leadInd p + (b : ℂ) * leadR1 b p := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  fin_cases p <;> (simp [tStar, yStar, ind, leadInd, leadR1]; try field_simp; try simp)

theorem one_add_tStar {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    1 + (b : ℂ) * tStar b 1 0 = dStar b := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  rw [← SourceMixing.one_add_b_dStar hb]
  simp [tStar, yStar, ind]; field_simp; simp

/-- **Matched values of `S_p`.** -/
theorem svP_matched (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ) (hs : IsStationaryJet b E s) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖svP b E X p‖ ≤ C ∧ ‖svP b E X p - leadSv b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := SourceMixing.matchedBasic hA hb0 hb h1 h2 s
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := SourceMixing.matchedScalars hA hb0 hb h1 h2 s hs
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched hA hb0 hb h1 h2 s
  obtain ⟨Cv, Wv, hCv, hsys⟩ := vP_system hA hb0 hb h1 h2
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set ts := ‖tStar b 1 0‖ + ‖tStar b 1 1‖
  set Λ := 1 + b ^ 2 * Cb ^ 2 + 1 + Cs + (1 + Ct) + (1 / b + 1) + Cb * (Cb * Cb) +
    ‖jetB b E s‖ + Cb + (1 + b * Ct) + Ct + dStar b + ts + 1
  have hts : 0 ≤ ts := by positivity
  have hΛ : 0 ≤ Λ := by positivity
  set K := Cb + Cs + Ct + Cv + b ^ 2 * ((Cb + 1) * Cb)
  have hK5 : 0 ≤ b ^ 2 * ((Cb + 1) * Cb) := by positivity
  have hK : 0 ≤ K := by positivity
  set KR := 4 * Λ ^ 3 * K + 4 * Λ ^ 3 * K
  set Kx := (Cv * ((1 + b ^ 2 * Cb ^ 2) * K + b ^ 2 * ((Cb + 1) * K) * dStar b) + K +
    b * ((Cb + 1) * K)) / b
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨min d₀ (min d₁ d₂), Cv + (Kx + KR / b), max (max Wb Ws) (max Wt Wv),
    lt_min hd₀ (lt_min hd₁ hd₂), by positivity, fun W hW X hX hd p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨hd0, hd1, hd2⟩ := hd
  obtain ⟨hM, hv, -, -, -, hva, -, -, hm2, hBj⟩ := hmb W hWb X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs X hX hd1
  have ht := htm W hWt X hX hd2
  obtain ⟨hS, h3⟩ := hsys W hWv X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  -- the right side and its leading value
  set Ra := SourceMixing.kvOf b E X * SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X +
    (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p
  set Rs := kMinus b E * 1 * leadB b p * jetB b E s +
    (b : ℂ) * matchedA E * (1 + (b : ℂ) * tStar b 1 0) * tStar b 1 p
  have hRs : leadSv b E s p = Rs / (1 + kMinus b E * s) := by
    simp only [Rs, leadSv, leadDen, one_add_tStar hb0 hb, tStar_one_eq hb0 p]; ring
  -- `S ≈ Ra / D₋`
  have h3' : ‖svP b E X p * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * SourceMixing.vOf b E X ^ 2) *
      SourceMixing.m2Of b E X) - (Ra + (b : ℂ) * SourceMixing.vOf b E X ^ 2 * 0)‖ ≤ K * e := by
    rw [mul_zero, add_zero]
    exact hKe Cv (by simp only [K]; linarith) _
      (h3.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCv))
  have hc := xP_close (E := E) hb0 hb he hK hv hS hs.2 ha hden (by simp)
    (hKe Cb (by simp only [K]; linarith) _ hm2)
    (hKe Cb (by simp only [K]; linarith) _ hva) h3'
  rw [mul_zero, add_zero] at hc
  -- `Ra ≈ Rs`
  have hkv : ‖SourceMixing.kvOf b E X - kMinus b E‖ ≤ K * e := by
    have e' : SourceMixing.kvOf b E X - kMinus b E =
        (b : ℂ) ^ 2 * ((SourceMixing.vOf b E X + matchedA E) * (SourceMixing.vOf b E X - matchedA E)) := by
      unfold SourceMixing.kvOf kMinus; ring
    rw [e', norm_mul, norm_pow, nb, norm_mul]
    have hva2 : ‖SourceMixing.vOf b E X + matchedA E‖ ≤ Cb + 1 :=
      (norm_add_le _ _).trans (by rw [ha]; linarith)
    refine (mul_le_mul_of_nonneg_left (mul_le_mul hva2
      hva (norm_nonneg _) (by positivity)) (by positivity)).trans ?_
    calc b ^ 2 * ((Cb + 1) * (Cb * e)) = b ^ 2 * ((Cb + 1) * Cb) * e := by ring
      _ ≤ K * e := mul_le_mul_of_nonneg_right (by simp only [K]; linarith) he
  have hrB : ‖rB b E X p - leadB b p‖ ≤ K * e := by
    rw [← rB_star_eq hb0 hb p]
    have e' : rB b E X p - (ind 0 p + sig1 b (tStar b 0 p) (tStar b 1 p)) =
        sig1 b (tP b E X 0 p - tStar b 0 p) (tP b E X 1 p - tStar b 1 p) := by
      simp only [rB, sig1]; ring
    rw [e']
    exact (norm_sig1_le hb0 hb (ht 0 p).2 (ht 1 p).2).trans
      (mul_le_mul_of_nonneg_right (by simp only [K]; linarith) he)
  have hB' : ‖SourceMixing.bOf b E X‖ ≤ Cb * (Cb * Cb) := (PassiveCovariance.norm_normTrace_le _).trans
    ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hM ((Matrix.l2_opNorm_mul _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hM hM (norm_nonneg _) hCb))
      (norm_nonneg _) hCb))
  have hkvn : ‖SourceMixing.kvOf b E X‖ ≤ 1 + b ^ 2 * Cb ^ 2 := by
    unfold SourceMixing.kvOf
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    · rw [norm_mul, norm_pow, norm_pow, nb]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (by positivity)
  have hkm : ‖kMinus b E‖ ≤ 1 + b ^ 2 * Cb ^ 2 + 1 := by
    unfold kMinus
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_mul, norm_pow, norm_pow, nb, ha]
    nlinarith [sq_nonneg Cb]
  have hlB : ‖leadB b p‖ ≤ 1 / b + 1 := by
    fin_cases p <;> (simp [leadB, abs_of_pos hb0]; try positivity)
  have hlt : ‖tStar b 1 p‖ ≤ ts := by
    fin_cases p
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have h1t : ‖1 + (b : ℂ) * SourceMixing.tTwo b E X 0‖ ≤ 1 + b * Ct := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul, nb, tTwo_eq]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (ht 1 0).1 hb0.le)
  have hrBn : ‖rB b E X p‖ ≤ 1 + Ct := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht 0 p).1 (ht 1 p).1))
  have hd1 : ‖1 + (b : ℂ) * tStar b 1 0‖ ≤ dStar b := by
    rw [one_add_tStar hb0 hb, Complex.norm_real, Real.norm_of_nonneg hD]
  have nn := norm_nonneg (jetB b E s)
  have hb1 : b ≤ 1 := by linarith
  have hbi : 0 ≤ 1 / b := by positivity
  have : 0 ≤ b ^ 2 * Cb ^ 2 := by positivity
  have : 0 ≤ Cb * (Cb * Cb) := by positivity
  have : 0 ≤ b * Ct := by positivity
  have l1 : 1 + b ^ 2 * Cb ^ 2 ≤ Λ := by simp only [Λ]; linarith
  have l2 : Cs ≤ Λ := by simp only [Λ]; linarith
  have l3 : 1 + Ct ≤ Λ := by simp only [Λ]; linarith
  have l4 : 1 / b + 1 ≤ Λ := by simp only [Λ]; linarith
  have l5 : Cb * (Cb * Cb) ≤ Λ := by simp only [Λ]; linarith
  have l6 : Cb ≤ Λ := by simp only [Λ]; linarith
  have l7 : 1 + b * Ct ≤ Λ := by simp only [Λ]; linarith
  have l8 : Ct ≤ Λ := by simp only [Λ]; linarith
  have l9 : dStar b ≤ Λ := by simp only [Λ]; linarith
  have l11 : (1 : ℝ) ≤ Λ := by simp only [Λ]; linarith
  have l12 : 1 + b ^ 2 * Cb ^ 2 + 1 ≤ Λ := by simp only [Λ]; linarith
  have hKs : Cs * e ≤ K * e := mul_le_mul_of_nonneg_right (by simp only [K]; linarith) he
  have hKb : Cb * e ≤ K * e := mul_le_mul_of_nonneg_right (by simp only [K]; linarith) he
  have hKt : Ct * e ≤ K * e := mul_le_mul_of_nonneg_right (by simp only [K]; linarith) he
  have hKRdef : KR = 4 * Λ ^ 3 * K + 4 * Λ ^ 3 * K := rfl
  have hKR0 : 0 ≤ KR := by positivity
  change _ ≤ Kx * e at hc
  clear_value KR Kx Λ K
  have tA := norm_prod4_sub_le (x₁ := SourceMixing.kvOf b E X) (x₂ := SourceMixing.sOne b E X)
    (x₃ := rB b E X p) (x₄ := SourceMixing.bOf b E X) (y₁ := kMinus b E) (y₂ := 1)
    (y₃ := leadB b p) (y₄ := jetB b E s) hΛ (hs1n.trans l2) (hrBn.trans l3) (hB'.trans l5)
    (hkm.trans l12) (by rw [norm_one]; exact l11) (hlB.trans l4) hkv (hs1.trans hKs) hrB
    (hBj.trans hKb)
  have hvt : ‖(1 + (b : ℂ) * SourceMixing.tTwo b E X 0) - (1 + (b : ℂ) * tStar b 1 0)‖ ≤ K * e := by
    rw [add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb, tTwo_eq]
    calc b * ‖tP b E X 1 0 - tStar b 1 0‖ ≤ 1 * (Ct * e) :=
          mul_le_mul hb1 (ht 1 0).2 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKt
  have tB := norm_prod4_sub_le (x₁ := (b : ℂ)) (x₂ := SourceMixing.vOf b E X)
    (x₃ := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0) (x₄ := tP b E X 1 p) (y₁ := (b : ℂ))
    (y₂ := matchedA E) (y₃ := 1 + (b : ℂ) * tStar b 1 0) (y₄ := tStar b 1 p) hΛ
    (hv.trans l6) (h1t.trans l7) ((ht 1 p).1.trans l8) (by rw [nb]; linarith)
    (by rw [ha]; exact l11) (hd1.trans l9) (by rw [sub_self, norm_zero]; positivity)
    (hva.trans hKb) hvt ((ht 1 p).2.trans hKt)
  have hRR : ‖Ra - Rs‖ ≤ KR * e := by
    have e' : Ra - Rs = (SourceMixing.kvOf b E X * SourceMixing.sOne b E X * rB b E X p *
        SourceMixing.bOf b E X - kMinus b E * 1 * leadB b p * jetB b E s) +
        ((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p -
          (b : ℂ) * matchedA E * (1 + (b : ℂ) * tStar b 1 0) * tStar b 1 p) := by
      exact add_sub_add_comm _ _ _ _
    rw [e']
    refine (norm_add_le _ _).trans ((add_le_add tA tB).trans (le_of_eq ?_))
    rw [hKRdef]; ring
  have hD0 : (0 : ℝ) < ‖1 + kMinus b E * s‖ := lt_trans hb0 hden
  have hq : ‖Ra / (1 + kMinus b E * s) - Rs / (1 + kMinus b E * s)‖ ≤ KR / b * e := by
    rw [← sub_div, norm_div]
    calc ‖Ra - Rs‖ / ‖1 + kMinus b E * s‖ ≤ (KR * e) / b :=
          div_le_div₀ (mul_nonneg hKR0 he) hRR hb0 hden.le
      _ = KR / b * e := by ring
  have hKK : 0 ≤ Kx + KR / b := add_nonneg hKx (div_nonneg hKR0 hb0.le)
  refine ⟨hS.trans (le_add_of_nonneg_right hKK), ?_⟩
  rw [hRs]
  calc ‖svP b E X p - Rs / (1 + kMinus b E * s)‖ ≤
      ‖svP b E X p - Ra / (1 + kMinus b E * s)‖ + ‖Ra / (1 + kMinus b E * s) - Rs / (1 + kMinus b E * s)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Kx * e + KR / b * e := add_le_add hc hq
    _ = (Kx + KR / b) * e := by ring
    _ ≤ (Cv + (Kx + KR / b)) * e := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCv) he

end BlockBand.Transmission.PassiveCovariance
