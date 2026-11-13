module

public import BlockBand.Transmission.PassiveCovarianceBulk.ZSystem
public import BlockBand.Transmission.PassiveCovarianceBulk.VMatched
public import BlockBand.Transmission.PassiveCovariance.ZMatched2

/-!
# Bulk-uniform matched value of `σz_p`

The matched value of `σz_p` at a stationary jet, with constants and `W₀` uniform in
`E ∈ bulkInterval κ`.
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

/-- `I_z ≈ I_*` (and `|I_z| ≤ C`).
Bulk-uniform copy of `zI_close` (constants uniform on `bulkInterval κ`). -/
theorem zI_close_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
            conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
            svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X‖ ≤ C ∧
        ‖(SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
            conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
            svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) - zIStar b E s p‖ ≤
          C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cs, Ws, hd₁, hCs, hms⟩ := matchedScalars_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₃, Cv, Wv, hd₃, hCv, hsv⟩ := svP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₄, Cq, Wq, hd₄, hCq, hcq⟩ := cq_matched_bulk hA hb0 hb hκ
  obtain ⟨nB, hnBd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  obtain ⟨nS, hnSd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0B : 0 ≤ nB := by rw [hnBd]; exact jetL_nonneg' b κ
  have h0S : 0 ≤ nS := by rw [hnSd]; exact jetL_nonneg' b κ
  have h0j := jetL_nonneg' b κ
  have h0c := jetL_nonneg' b κ
  have hb3 : 0 ≤ Cb * (Cb * Cb) := by positivity
  have hb4 : 0 ≤ Cb * (Cb * (Cb * Cb)) := by positivity
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + Cs + Ct + Cv + Cb * (Cb * Cb) + Cb * (Cb * (Cb * Cb)) + nB +
    nS + jetL b κ + jetL b κ := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Cs + Ct + Cv + Cq := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₁) (min d₂ (min d₃ d₄)),
    Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
      Cv * Cs * (Cb * (Cb * Cb)) + 12 * Λ ^ 3 * K,
    max (max Wb Ws) (max Wt (max Wv Wq)), lt_min (lt_min hd₀ hd₁) (lt_min hd₂ (lt_min hd₃ hd₄)),
    by positivity, fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hLp := lead_le_jetL hb0 hb hκ hEκ hs p
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWs⟩, hWt, hWv, hWq⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd1⟩, hd2, hd3, hd4⟩ := hd
  obtain ⟨hM, -, -, -, -, -, -, -, -, hBj⟩ := hmb W hWb E hEκ s X hX hd0
  obtain ⟨hs1n, -, hs1, -, -⟩ := hms W hWs E hEκ s hs X hX hd1
  obtain ⟨hrn, hrl⟩ := rB_close hb0 hb p (htm W hWt E hEκ s X hX hd2)
  obtain ⟨hSn, hSl⟩ := hsv W hWv E hEκ s hs X hX hd3 p
  have hCql := hcq W hWq E hEκ s X hX hd4
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
  have kq : Cq ≤ K := by rw [hKd]; linarith
  have hB := norm_bOf_le hM
  have hcqn := norm_cqOf_le (b := b) (E := E) (X := X) hM
  have hlB : ‖leadB b p‖ ≤ nB := by rw [hnBd]; exact hLp.2.2.2.1
  have hlS : ‖leadSv b E s p‖ ≤ nS := by rw [hnSd]; exact hLp.2.2.2.2.2.2.1
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l2 : Cs ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l3 : 1 + Ct ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l4 : Cv ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l5 : Cb * (Cb * Cb) ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l6 : Cb * (Cb * (Cb * Cb)) ≤ Λ := by
    linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l7 : nB ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l8 : nS ≤ Λ := by linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c]
  have l9 : ‖jetB b E s‖ ≤ Λ := by
    linarith only [hΛd, hCs, hCt, hCv, hb3, hb4, h0B, h0S, h0j, h0c, hLp.1]
  have h1n : ‖(1 : ℂ)‖ ≤ Λ := by rw [norm_one]; exact l1
  have hz : ‖(1 : ℂ) - 1‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hS1 := hKe Cs ks _ hs1
  have hP := norm_prod4_pair_sub_le (x₁ := SourceMixing.sOne b E X) (x₂ := SourceMixing.sOne b E X)
    (x₃ := rB b E X p) (x₄ := cqOf b E X) (y₁ := 1) (y₂ := 1) (y₃ := leadB b p) (y₄ := jetC b E s)
    (x₅ := SourceMixing.sOne b E X) (x₆ := conj (svP b E X p)) (x₇ := conj (SourceMixing.bOf b E X))
    (x₈ := 1) (y₅ := 1) (y₆ := conj (leadSv b E s p)) (y₇ := conj (jetB b E s)) (y₈ := 1) hΛ
    (hs1n.trans l2) (hrn.trans l3) (hcqn.trans l6) h1n h1n (hlB.trans l7)
    (by rw [Complex.norm_conj]; exact hSn.trans l4) (by rw [Complex.norm_conj]; exact hB.trans l5) h1n
    h1n (by rw [Complex.norm_conj]; exact hlS.trans l8) (by rw [Complex.norm_conj]; exact l9)
    hS1 hS1 (hKe Ct kt _ hrl) (hKe Cq kq _ hCql) hS1
    (by rw [norm_conj_sub]; exact hKe Cv kv _ hSl) (by rw [norm_conj_sub]; exact hKe Cb kb _ hBj) hz
  have hQ := norm_prod4_sub_le (x₁ := svP b E X p) (x₂ := SourceMixing.sOne b E X)
    (x₃ := SourceMixing.bOf b E X) (x₄ := 1) (y₁ := leadSv b E s p) (y₂ := 1) (y₃ := jetB b E s)
    (y₄ := 1) hΛ (hs1n.trans l2) (hB.trans l5) h1n (hlS.trans l8) h1n l9 (hKe Cv kv _ hSl) hS1
    (hKe Cb kb _ hBj) hz
  have hb' : ‖conj (svP b E X p) * conj (SourceMixing.bOf b E X)‖ ≤ Cv * (Cb * (Cb * Cb)) := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_conj]; exact mul_le_mul hSn hB (norm_nonneg _) hCv
  have h12 : 0 ≤ 12 * Λ ^ 3 * K := by positivity
  have hI : ‖SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X‖ ≤
      Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
        Cv * Cs * (Cb * (Cb * Cb)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      refine mul_le_mul hs1n ((norm_add_le _ _).trans (add_le_add ?_ hb')) (by positivity) hCs
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hs1n hrn (norm_nonneg _) hCs) hcqn (norm_nonneg _) (by positivity)
    · rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hSn hs1n (norm_nonneg _) hCv) hB (norm_nonneg _) (by positivity)
  refine ⟨hI.trans (le_add_of_nonneg_right h12), ?_⟩
  have eq : (SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) - zIStar b E s p =
      ((SourceMixing.sOne b E X * SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
        SourceMixing.sOne b E X * conj (svP b E X p) * conj (SourceMixing.bOf b E X) * 1) -
        (1 * 1 * leadB b p * jetC b E s + 1 * conj (leadSv b E s p) * conj (jetB b E s) * 1)) +
      (svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X * 1 -
        leadSv b E s p * 1 * jetB b E s * 1) := by
    simp only [zIStar]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add hP hQ).trans ?_)
  have : 0 ≤ Cs * (Cs * (1 + Ct) * (Cb * (Cb * (Cb * Cb))) + Cv * (Cb * (Cb * Cb))) +
      Cv * Cs * (Cb * (Cb * Cb)) := by positivity
  rw [show 8 * Λ ^ 3 * (K * e) + 4 * Λ ^ 3 * (K * e) = 12 * Λ ^ 3 * K * e by ring]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left this) he

/-- `σz_p ≈ R/b`.
Bulk-uniform copy of `zP_div` (constants uniform on `bulkInterval κ`). -/
theorem zP_div_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧
        ‖szP b E X p - (SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
            (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
              conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1) / b‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, hCw, hsys⟩ := zP_system_bulk hA hb0 hb hκ
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  set K := Cb + Cw
  have hK : 0 ≤ K := by positivity
  set Kx := (Cw * ((1 + b ^ 2 * (Cb * Cb)) * K + b ^ 2 * K * dStar b) + K + b * K) / b
  have hKx : 0 ≤ Kx := by positivity
  refine ⟨d₀, Cw + Kx, max Wb Ww, hd₀, by positivity, fun W hW E hEκ s X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨-, hv, -, -, -, -, hh1, hAd, -, -⟩ := hmb W (le_trans (le_max_left _ _) hW) E hEκ s X hX hd
  obtain ⟨hS, h3⟩ := hsys W (le_trans (le_max_right _ _) hW) E hEκ X hX p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have hKe : ∀ C' : ℝ, C' ≤ K → ∀ x : ℝ, x ≤ C' * e → x ≤ K * e := fun C' hC' x hx =>
    hx.trans (mul_le_mul_of_nonneg_right hC' he)
  have hhB : ‖SourceMixing.hOf b E X‖ ≤ Cb * Cb := by
    unfold SourceMixing.hOf; rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hv hv (norm_nonneg _) hCb
  set Ra := SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
    (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
    (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
      conj (vP b E X p 1) +
    (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1
  have h3' : ‖szP b E X p * (1 - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * SourceMixing.hOf b E X) *
      SourceMixing.aOf b E X) - (Ra + (b : ℂ) * SourceMixing.hOf b E X * 0)‖ ≤ K * e := by
    rw [mul_zero, add_zero]
    exact hKe Cw (by simp only [K]; linarith) _
      (h3.trans (div_sq_le_epsOf (b := b) (E := E) s hX.posSemidef hCw))
  have hc := yq_close hb0 hb he hK hS hhB (by simp) (hKe Cb (by simp only [K]; linarith) _ hh1)
    (hKe Cb (by simp only [K]; linarith) _ hAd) h3'
  rw [mul_zero, add_zero] at hc
  exact ⟨hS.trans (le_add_of_nonneg_right hKx),
    hc.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCw) he)⟩

/-- The right side of the `z_p` system approaches `R_*`.
Bulk-uniform copy of `zP_rhs_close` (constants uniform on `bulkInterval κ`). -/
theorem zP_rhs_close_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖(SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
            (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
              conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            ((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1)) - zRStar b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, Cb, Wb, hd₀, hCb, hmb⟩ := matchedBasic_bulk hA hb0 hb hκ
  obtain ⟨d₂, Ct, Wt, hd₂, hCt, htm⟩ := tP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₃, C0, W0, hd₃, hC0, hv0⟩ := vP0_matched_bulk hA hb0 hb hκ
  obtain ⟨d₄, C1, W1, hd₄, hC1, hv1⟩ := vP1_matched_bulk hA hb0 hb hκ
  obtain ⟨d₅, CI, WI, hd₅, hCI, hIc⟩ := zI_close_bulk hA hb0 hb hκ
  obtain ⟨Cvb, Wvb, hCvb, hVb⟩ := vP_blocks_bulk hA hb0 hb hκ
  have hD : 0 ≤ dStar b := by simp only [dStar]; have : 0 < 1 - b := by linarith
                              positivity
  obtain ⟨nV, hnVd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0V : 0 ≤ nV := by rw [hnVd]; exact jetL_nonneg' b κ
  have h0bt : 0 ≤ b * Ct := by positivity
  obtain ⟨nW, hnWd⟩ : ∃ x : ℝ, x = jetL b κ := ⟨_, rfl⟩
  have h0W : 0 ≤ nW := by rw [hnWd]; exact jetL_nonneg' b κ
  obtain ⟨Λ, hΛd⟩ : ∃ x : ℝ, x = 1 + (1 + b * Ct) + Ct + dStar b + Cb + Cvb + nV + nW := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨K, hKd⟩ : ∃ x : ℝ, x = Cb + Ct + C0 + C1 := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKd]; positivity
  refine ⟨min (min d₀ d₂) (min d₃ (min d₄ d₅)), b ^ 2 * Cb * CI + 2 * CI + 8 * Λ ^ 3 * K,
    max (max Wb Wt) (max W0 (max W1 (max WI Wvb))),
    lt_min (lt_min hd₀ hd₂) (lt_min hd₃ (lt_min hd₄ hd₅)), by positivity,
      fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  have hLp := lead_le_jetL hb0 hb hκ hEκ hs p
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWb, hWt⟩, hW0, hW1, hWI, hWvb⟩ := hW
  simp only [le_min_iff] at hd
  obtain ⟨⟨hd0, hd2⟩, hd3, hd4, hd5⟩ := hd
  obtain ⟨-, hv, -, -, -, hva, hh1, -⟩ := hmb W hWb E hEκ s X hX hd0
  have ht := htm W hWt E hEκ s X hX hd2
  have h0 := hv0 W hW0 E hEκ s hs X hX hd3 p
  have h1' := hv1 W hW1 E hEκ s hs X hX hd4 p
  obtain ⟨hIn, hIl⟩ := hIc W hWI E hEκ s hs X hX hd5 p
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
  have k1 : C1 ≤ K := by rw [hKd]; linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have ha := norm_matchedA E h1 h2
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  -- the first term
  have hkh : ‖SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2)‖ ≤ b ^ 2 * Cb * e := by
    have e' : SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) =
        (b : ℂ) ^ 2 * (SourceMixing.hOf b E X - 1) := by unfold SourceMixing.khOf; ring
    rw [e', norm_mul, norm_pow, nb, mul_assoc]
    exact mul_le_mul_of_nonneg_left hh1 (by positivity)
  have hkP : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_pow, nb]
    linarith only [hb2, hb0]
  set I := SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
    conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
    svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X
  have tI : ‖SourceMixing.khOf b E X * I - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p‖ ≤
      (b ^ 2 * Cb * CI + 2 * CI) * e := by
    have eq : SourceMixing.khOf b E X * I - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p =
        (SourceMixing.khOf b E X - (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2)) * I +
          (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * (I - zIStar b E s p) := by ring
    rw [eq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have t1 := mul_le_mul hkh hIn (norm_nonneg _) (by positivity)
    have t2 := mul_le_mul hkP hIl (norm_nonneg _) zero_le_two
    calc _ ≤ b ^ 2 * Cb * e * CI + 2 * (CI * e) := add_le_add t1 t2
      _ = _ := by ring
  -- the second term
  have l1 : (1 : ℝ) ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l2 : 1 + b * Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l3 : Ct ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l4 : dStar b ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l6 : Cb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l7 : Cvb ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l8 : nV ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have l9 : nW ≤ Λ := by linarith only [hΛd, h0bt, hCt, hD, hCb, hCvb, h0V, h0W]
  have hbn : ‖(b : ℂ)‖ ≤ Λ := by rw [nb]; linarith
  have han : ‖matchedA E‖ ≤ Λ := by rw [ha]; exact l1
  have hdn : ‖(dStar b : ℂ)‖ ≤ Λ := by rw [Complex.norm_real, Real.norm_of_nonneg hD]; exact l4
  have hzb : ‖(b : ℂ) - b‖ ≤ K * e := by rw [sub_self, norm_zero]; positivity
  have hc : ‖1 + (b : ℂ) * SourceMixing.tTwo b E X 0‖ ≤ 1 + b * Ct :=
    (norm_add_le _ _).trans (add_le_add (le_of_eq norm_one) (by
      rw [norm_mul, nb, tTwo_eq]; exact mul_le_mul_of_nonneg_left (ht 1 0).1 hb0.le))
  have hcd : ‖(1 + (b : ℂ) * SourceMixing.tTwo b E X 0) - (dStar b : ℂ)‖ ≤ K * e := by
    rw [← one_add_tStar hb0 hb, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, nb, tTwo_eq]
    calc b * ‖tP b E X 1 0 - tStar b 1 0‖ ≤ 1 * (Ct * e) :=
          mul_le_mul hb1 (ht 1 0).2 (norm_nonneg _) zero_le_one
      _ ≤ K * e := by rw [one_mul]; exact hKe Ct kt _ le_rfl
  have hbv : ‖(b : ℂ) * SourceMixing.vOf b E X‖ ≤ Λ := by
    rw [norm_mul, nb]; exact (mul_le_of_le_one_left (norm_nonneg _) hb1).trans (hv.trans l6)
  have hba : ‖(b : ℂ) * matchedA E‖ ≤ Λ := by rw [norm_mul, nb, ha, mul_one]; linarith
  have hbva : ‖(b : ℂ) * SourceMixing.vOf b E X - (b : ℂ) * matchedA E‖ ≤ K * e := by
    rw [← mul_sub, norm_mul, nb]
    exact (mul_le_of_le_one_left (norm_nonneg _) hb1).trans (hKe Cb kb _ hva)
  have ht2 : ‖SourceMixing.tTwo b E X 1‖ ≤ Λ := by rw [tTwo_eq]; exact (ht 1 1).1.trans l3
  have ht2d : ‖SourceMixing.tTwo b E X 1 - (dStar b : ℂ)‖ ≤ K * e := by
    rw [tTwo_eq, ← tStar_one_one hb0 hb]; exact hKe Ct kt _ (ht 1 1).2
  have hP := norm_prod4_pair_sub_le (x₁ := (b : ℂ)) (x₂ := SourceMixing.vOf b E X)
    (x₃ := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0) (x₄ := conj (vP b E X p 1))
    (y₁ := (b : ℂ)) (y₂ := matchedA E) (y₃ := (dStar b : ℂ)) (y₄ := conj (v1Star b E s p))
    (x₅ := (b : ℂ)) (x₆ := (b : ℂ) * SourceMixing.vOf b E X) (x₇ := vP b E X p 0)
    (x₈ := SourceMixing.tTwo b E X 1) (y₅ := (b : ℂ)) (y₆ := (b : ℂ) * matchedA E)
    (y₇ := leadV1 b E s p) (y₈ := (dStar b : ℂ)) hΛ (hv.trans l6) (hc.trans l2)
    (by rw [Complex.norm_conj]; exact (hvb 1).trans l7) hbn han hdn hbv ((hvb 0).trans l7) ht2
    hbn hba ((by rw [hnVd]; exact hLp.2.2.2.2.2.2.2.2.1 : ‖leadV1 b E s p‖ ≤ nV).trans l8)
    hzb (hKe Cb kb _ hva) hcd (by rw [norm_conj_sub]; exact hKe C1 k1 _ h1') hzb hbva
    (hKe C0 k0 _ h0) ht2d
  have eq : (SourceMixing.khOf b E X * I +
      ((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        conj (vP b E X p 1) +
      (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1)) -
      zRStar b E s p = (SourceMixing.khOf b E X * I -
        (((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2) * zIStar b E s p) +
      (((b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
        conj (vP b E X p 1) +
      (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1) -
        ((b : ℂ) * matchedA E * (dStar b : ℂ) * conj (v1Star b E s p) +
          (b : ℂ) * ((b : ℂ) * matchedA E) * leadV1 b E s p * (dStar b : ℂ))) := by
    simp only [zRStar]; ring
  rw [eq]
  refine (norm_add_le _ _).trans ((add_le_add tI hP).trans (le_of_eq ?_))
  ring

/-- **Matched values of `σz_p`.**
Bulk-uniform copy of `zP_matched` (constants uniform on `bulkInterval κ`). -/
theorem zP_matched_bulk (hA : PassiveLayer.PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧ ‖szP b E X p - leadSz b E s p‖ ≤ C * SourceMixing.epsOf b E s X := by
  obtain ⟨d₀, C₀, W₀, hd₀, hC₀, hdiv⟩ := zP_div_bulk hA hb0 hb hκ
  obtain ⟨d₁, C₁, W₁, hd₁, hC₁, hrhs⟩ := zP_rhs_close_bulk hA hb0 hb hκ
  refine ⟨min d₀ d₁, C₀ + C₁ / b, max W₀ W₁, lt_min hd₀ hd₁, by positivity,
    fun W hW E hEκ s hs X hX hd p => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  obtain ⟨hS, hq⟩ := hdiv W (le_trans (le_max_left _ _) hW) E hEκ s X hX (hd.trans (min_le_left _ _)) p
  have hr := hrhs W (le_trans (le_max_right _ _) hW) E hEκ s hs X hX (hd.trans (min_le_right _ _)) p
  set e := SourceMixing.epsOf b E s X
  have he : 0 ≤ e := by
    obtain ⟨e0, -, -, e01, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hX.posSemidef
    have := sq_nonneg ((W : ℝ)⁻¹); linarith
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  refine ⟨hS.trans (le_add_of_nonneg_right (by positivity)), ?_⟩
  rw [leadSz_eq hb0 h1 h2]
  set Ra := SourceMixing.khOf b E X * (SourceMixing.sOne b E X *
    (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
      conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
      svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
    (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
      conj (vP b E X p 1) +
    (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 * SourceMixing.tTwo b E X 1
  rw [← add_assoc] at hr
  have hq2 : ‖Ra / b - zRStar b E s p / b‖ ≤ C₁ / b * e := by
    rw [← sub_div, norm_div, nb]
    calc ‖Ra - zRStar b E s p‖ / b ≤ (C₁ * e) / b := div_le_div_of_nonneg_right hr hb0.le
      _ = C₁ / b * e := by ring
  calc ‖szP b E X p - zRStar b E s p / b‖ ≤ ‖szP b E X p - Ra / b‖ + ‖Ra / b - zRStar b E s p / b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C₀ * e + C₁ / b * e := add_le_add hq hq2
    _ = (C₀ + C₁ / b) * e := by ring

end BlockBand.Transmission.CovarianceBulk
