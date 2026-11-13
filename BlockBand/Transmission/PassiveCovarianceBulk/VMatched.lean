module

public import BlockBand.Transmission.PassiveCovarianceBulk.Systems
public import BlockBand.Transmission.PassiveCovarianceBulk.JetBounds
public import BlockBand.Transmission.PassiveCovarianceBulk.Matched1
public import BlockBand.Transmission.PassiveCovariance.VMatched
public import BlockBand.Transmission.PassiveCovariance.VMatchedTr

/-!
# Bulk-uniform matched values of `σv_p`, `v^p_0`, `v^p_1`

The matched values of `S_p = σ₁(v^p)`, `v^p₀` and `v^p₁` at a stationary jet, with constants and
`W₀` uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds bulk_eta_le_one bulk_norm_z)
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Matched values of `S_p`.**
Bulk-uniform copy of `svP_matched` (constants uniform on `bulkInterval κ`). -/
theorem svP_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖svP b E X p‖ ≤ C ∧ ‖svP b E X p - leadSv b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨Cv, Wv, hCv, hsys⟩ := vP_system_bulk hA hb0 hb hκ
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set ts := ‖tStar b 1 0‖ + ‖tStar b 1 1‖
  set Λ := 1 + b ^ 2 * Cb ^ 2 + 1 + Cs + (1 + Ct) + (1 / b + 1) + Cb * (Cb * Cb) +
    Cb + (1 + b * Ct) + Ct + dStar b + ts + 1
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
    lt_min hd₀ (lt_min hd₁ hd₂), by positivity, fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨hd0, hd1, hd2⟩ := hd
  obtain ⟨hM, hv, -, -, -, hva, -, -, hm2, hBj⟩ := hmb W hWb E hEκ s X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs E hEκ s hs X hX hd1
  have ht := htm W hWt E hEκ s X hX hd2
  obtain ⟨hS, h3⟩ := hsys W hWv E hEκ X hX p
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
  have hKR0 : 0 ≤ KR := by
    rw [hKRdef]
    have h3 : 0 ≤ 4 * Λ ^ 3 * K := mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hΛ 3)) hK
    exact add_nonneg h3 h3
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
    (by rw [ha]; exact l11) (hd1.trans l9) (by rw [sub_self, norm_zero]; exact mul_nonneg hK he)
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

/-- **`v^p₀ ↦ leadV1 p`.**
Bulk-uniform copy of `vP0_matched` (constants uniform on `bulkInterval κ`). -/
theorem vP0_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖vP b E X p 0 - leadV1 b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched_bulk hA hb0 hb hκ
  obtain ⟨Ctr, Wtr, hCtr, htr⟩ := vP_traces_bulk hA hb0 hb hκ
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = ‖leadB b 0‖ + ‖leadB b 1‖ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; positivity
  have h0S : 0 ≤ nS := by rw [hnSd]; exact jetL_nonneg' b κ
  have h0j := jetL_nonneg' b κ
  have hb3 : 0 ≤ Cb * (Cb * Cb) := by positivity
  have hb2 : 0 ≤ Cb * Cb := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Ct + Cb * (Cb * Cb) + nB + jetL b κ + Cb * Cb + nS +
    dStar b := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Ctr := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ d₃), Ctr + 8 * Λ ^ 3 * K, max (max Wb Ws) (max (max Wt Wv) Wtr),
    lt_min (lt_min hd₀ hd₁) (lt_min hd₂ hd₃), by positivity, fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  have hJB := (lead_le_jetL hb0 hb hκ hEκ hs p).1
  have hLp := lead_le_jetL hb0 hb hκ hEκ hs p
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, ⟨hWt, hWv⟩, hWtr⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3⟩ := hd
  obtain ⟨hM, -, -, -, -, -, -, -, hm2, hBj⟩ := hmb W hWb E hEκ s X hX hd0
  obtain ⟨-, -, hs1, -, -⟩ := hms W hWs E hEκ s hs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt E hEκ s X hX hd2)
  obtain ⟨-, hSl⟩ := hsv W hWv E hEκ s hs X hX hd3 p
  obtain ⟨d0, -⟩ := htr W hWtr E hEκ X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have kb : Cb ≤ K := by rw [hKd]; linarith
  have ks : Cs ≤ K := by rw [hKd]; linarith
  have kt : Ct ≤ K := by rw [hKd]; linarith
  have kv : Cv ≤ K := by rw [hKd]; linarith
  have hlB : ‖leadB b p‖ ≤ nB := by rw [hnBd]; exact norm_le_sum_two _ p
  have hlS : ‖leadSv b E s p‖ ≤ nS := by rw [hnSd]; exact hLp.2.2.2.2.2.2.1
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l2 : 1 + Ct ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l3 : Cb * (Cb * Cb) ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l4 : nB ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l5 : ‖jetB b E s‖ ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD, hJB]
  have l6 : Cb * Cb ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l7 : nS ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have l8 : dStar b ≤ Λ := by linarith only [hΛd, hCt, hb3, h0B, h0j, hb2, h0S, hD]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.sOne b E X) (x₂ := rB b E X p)
    (x₃ := SourceMixing.bOf b E X) (x₄ := 1) (y₁ := 1) (y₂ := leadB b p) (y₃ := jetB b E s) (y₄ := 1)
    (x₅ := svP b E X p) (x₆ := SourceMixing.m2Of b E X) (x₇ := 1) (x₈ := 1) (y₅ := leadSv b E s p)
    (y₆ := -s) (y₇ := 1) (y₈ := 1) hΛ (hrn.trans l2) ((norm_bOf_le hM).trans l3) h1n h1n
    (hlB.trans l4) l5 ((norm_m2Of_le hM).trans l6) h1n h1n (hlS.trans l7)
    (by rw [norm_neg]; exact hs.2.trans l8) h1n (hKe Cs ks _ hs1) (hKe Ct kt _ hrl)
    (hKe Cb kb _ hBj) hz (hKe Cv kv _ hSl) (by rw [sub_neg_eq_add]; exact hKe Cb kb _ hm2) hz hz
  have eq : vP b E X p 0 - leadV1 b E s p =
      (vP b E X p 0 - (SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X +
        svP b E X p * SourceMixing.m2Of b E X)) +
      ((SourceMixing.sOne b E X * rB b E X p * SourceMixing.bOf b E X * 1 +
        svP b E X p * SourceMixing.m2Of b E X * 1 * 1) -
        (1 * leadB b p * jetB b E s * 1 + leadSv b E s p * -s * 1 * 1)) := by
    simp only [leadV1]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add (d0.trans (div_sq_le_epsOf (b := b) (E := E) s
    hX.posSemidef hCtr)) hP).trans (le_of_eq ?_))
  ring

/-- **`v^p₁ ↦ v1Star p`.**
Bulk-uniform copy of `vP1_matched` (constants uniform on `bulkInterval κ`). -/
theorem vP1_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖vP b E X p 1 - v1Star b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₃, C0, W0, hd₃, hC0, hv0⟩ := vP0_matched_bulk hA hb0 hb hκ
  obtain ⟨Ctr, Wtr, hCtr, htr⟩ := vP_traces_bulk hA hb0 hb hκ
  obtain ⟨Cvb, Wvb, hCvb, hVb⟩ := vP_blocks_bulk hA hb0 hb hκ
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nT, hnTd⟩ : ∃ x : ℝ, x = ‖tStar b 1 0‖ + ‖tStar b 1 1‖ := ⟨_, rfl⟩
  obtain ⟨nV, hnVd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0T : 0 ≤ nT := by rw [hnTd]; positivity
  have h0V : 0 ≤ nV := by rw [hnVd]; exact jetL_nonneg' b κ
  have h0bt : 0 ≤ b * Ct := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + (1 + b * Ct) + Ct + dStar b + nT + Cb + Cvb + nV := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Ct + C0 + Ctr := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min d₀ (min d₂ d₃), Ctr + 8 * Λ ^ 3 * K, max (max Wb Wt) (max W0 (max Wtr Wvb)),
    lt_min hd₀ (lt_min hd₂ hd₃), by positivity, fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  have hJB := (lead_le_jetL hb0 hb hκ hEκ hs p).1
  have hLp := lead_le_jetL hb0 hb hκ hEκ hs p
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWt⟩, hW0, hWtr, hWvb⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨hd0, hd2, hd3⟩ := hd
  obtain ⟨-, hv, -, -, -, hva, -⟩ := hmb W hWb E hEκ s X hX hd0
  have ht := htm W hWt E hEκ s X hX hd2
  have h0 := hv0 W hW0 E hEκ s hs X hX hd3 p
  obtain ⟨-, d1⟩ := htr W hWtr E hEκ X hX p
  obtain ⟨hvb, -⟩ := hVb W hWvb E hEκ X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have kb : Cb ≤ K := by rw [hKd]; linarith
  have kt : Ct ≤ K := by rw [hKd]; linarith
  have k0 : C0 ≤ K := by rw [hKd]; linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  have hb1 : b ≤ 1 := by linarith
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l2 : 1 + b * Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l3 : Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l4 : dStar b ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l5 : nT ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l7 : Cvb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have l8 : nV ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, h0T, hCb, hCvb, h0V]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hbn : ‖(b : ℂ)‖ ≤ Λ := by rw [nb]; linarith
  have han : ‖matchedA E‖ ≤ Λ := by rw [ha]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hzb : ‖(b : ℂ) - b‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hc : ‖1 + (b : ℂ) * SourceMixing.tTwo b E X 0‖ ≤ 1 + b * Ct :=
    (norm_add_le _ _).trans (add_le_add (le_of_eq norm_one) (by
      rw [norm_mul, nb, tTwo_eq]; exact mul_le_mul_of_nonneg_left (ht 1 0).1 hb0.le))
  have hcd : ‖(1 + (b : ℂ) * SourceMixing.tTwo b E X 0) - (dStar b : ℂ)‖ ≤ K * e := by
    rw [← one_add_tStar hb0 hb, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb, tTwo_eq]
    calc b * ‖tP b E X 1 0 - tStar b 1 0‖ ≤ 1 * (Ct * e) :=
          mul_le_mul hb1 (ht 1 0).2 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Ct kt _ le_rfl
  have hdn : ‖(dStar b : ℂ)‖ ≤ Λ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hD]; exact l4
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.vOf b E X)
    (x₂ := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0) (x₃ := tP b E X 1 p) (x₄ := 1)
    (y₁ := matchedA E) (y₂ := (dStar b : ℂ)) (y₃ := tStar b 1 p) (y₄ := 1) (x₅ := (b : ℂ))
    (x₆ := SourceMixing.vOf b E X) (x₇ := vP b E X p 0) (x₈ := SourceMixing.vOf b E X)
    (y₅ := (b : ℂ)) (y₆ := matchedA E) (y₇ := leadV1 b E s p) (y₈ := matchedA E) hΛ
    (hc.trans l2) ((ht 1 p).1.trans l3) h1n han hdn
    ((by rw [hnTd]; exact norm_le_sum_two _ p : ‖tStar b 1 p‖ ≤ nT).trans l5)
    (hv.trans l6) ((hvb 0).trans l7) (hv.trans l6) hbn han
    ((by rw [hnVd]; exact hLp.2.2.2.2.2.2.2.2.1 : ‖leadV1 b E s p‖ ≤ nV).trans l8)
    (hKe Cb kb _ hva) hcd (hKe Ct kt _ (ht 1 p).2) hz hzb (hKe Cb kb _ hva) (hKe C0 k0 _ h0)
    (hKe Cb kb _ hva)
  have eq : vP b E X p 1 - v1Star b E s p =
      (vP b E X p 1 - SourceMixing.vOf b E X * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        tP b E X 1 p + (b : ℂ) * vP b E X p 0 * SourceMixing.vOf b E X)) +
      ((SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) * tP b E X 1 p * 1 +
        (b : ℂ) * SourceMixing.vOf b E X * vP b E X p 0 * SourceMixing.vOf b E X) -
        (matchedA E * (dStar b : ℂ) * tStar b 1 p * 1 +
          (b : ℂ) * matchedA E * leadV1 b E s p * matchedA E)) := by
    simp only [v1Star]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add (d1.trans (div_sq_le_epsOf (b := b) (E := E) s
    hX.posSemidef hCtr)) hP).trans (le_of_eq ?_))
  ring

end BlockBand.Transmission.CovarianceBulk
