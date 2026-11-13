module

public import BlockBand.Transmission.PassiveCovarianceBulk.Scalars
public import BlockBand.Transmission.PassiveCovariance.MeansTransfer

/-!
# Uniform bounds of the leading jet values on `bulkInterval κ`

The leading values of the means of the passive covariance are bounded by `N^24`,
`N = 2 + d_* + 1/b + 1/η_L`, uniformly on `bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.CovarianceBulk

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PathScalar (etaLow etaLow_pos etaLow_le bulk_bounds)
open scoped ComplexConjugate

/-- The base `N = 2 + d_* + 1/b + 1/η_L`. -/
def jetN (b κ : ℝ) : ℝ := 2 + dStar b + 1 / b + (etaLow b κ)⁻¹

/-- The uniform bound `N^24` of the leading jet values. -/
def jetL (b κ : ℝ) : ℝ := jetN b κ ^ 24

/-- Uniform majorant of `leadConst b E s`. -/
def leadConstL (b κ : ℝ) : ℝ := (12 * jetL b κ + 1) * (1 + (etaLow b κ)⁻¹) ^ 2

theorem jetL_nonneg' (b κ : ℝ) : 0 ≤ jetL b κ := by unfold jetL; positivity

theorem leadConstL_nonneg (b κ : ℝ) : 0 ≤ leadConstL b κ := by
  unfold leadConstL
  exact mul_nonneg (by linarith [jetL_nonneg' b κ]) (sq_nonneg _)

section Pw

variable {N : ℝ} (hN : 2 ≤ N)
include hN

theorem pw_mono {x : ℂ} {i j : ℕ} (h : ‖x‖ ≤ N ^ i) (hij : i ≤ j) : ‖x‖ ≤ N ^ j :=
  h.trans (pow_le_pow_right₀ (by linarith) hij)

theorem pw_mul {x y : ℂ} {i j : ℕ} (hx : ‖x‖ ≤ N ^ i) (hy : ‖y‖ ≤ N ^ j) :
    ‖x * y‖ ≤ N ^ (i + j) := by
  rw [norm_mul, pow_add]
  exact mul_le_mul hx hy (norm_nonneg _) (by positivity)

theorem pw_add {x y : ℂ} {i j : ℕ} (hx : ‖x‖ ≤ N ^ i) (hy : ‖y‖ ≤ N ^ j) :
    ‖x + y‖ ≤ N ^ (max i j + 1) := by
  have hx' := pw_mono hN hx (le_max_left i j)
  have hy' := pw_mono hN hy (le_max_right i j)
  have hp : 0 ≤ N ^ max i j := by positivity
  refine (norm_add_le _ _).trans ?_
  rw [pow_succ]; nlinarith

theorem pw_sub {x y : ℂ} {i j : ℕ} (hx : ‖x‖ ≤ N ^ i) (hy : ‖y‖ ≤ N ^ j) :
    ‖x - y‖ ≤ N ^ (max i j + 1) := by
  rw [sub_eq_add_neg]; exact pw_add hN hx (by rwa [norm_neg])

omit hN in
theorem pw_conj {x : ℂ} {i : ℕ} (hx : ‖x‖ ≤ N ^ i) : ‖conj x‖ ≤ N ^ i := by
  rwa [Complex.norm_conj]

theorem pw_div {x y : ℂ} {i j : ℕ} (hx : ‖x‖ ≤ N ^ i) (hy : ‖y⁻¹‖ ≤ N ^ j) :
    ‖x / y‖ ≤ N ^ (i + j) := by
  rw [div_eq_mul_inv]; exact pw_mul hN hx hy

end Pw

section Bulk

variable {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
  {s : ℂ} (hs : IsStationaryJet b E s)
include hb0 hb hκ hE hs

/-- The basic bounds, all `≤ N`. -/
theorem jet_basic :
    2 ≤ jetN b κ ∧ ‖s‖ ≤ jetN b κ ^ 1 ∧ ‖matchedA E‖ ≤ jetN b κ ^ 0 ∧
    ‖kMinus b E‖ ≤ jetN b κ ^ 0 ∧ ‖(leadDen b E s)⁻¹‖ ≤ jetN b κ ^ 1 ∧
    ‖(b : ℂ)‖ ≤ jetN b κ ^ 0 ∧ ‖((dStar b : ℝ) : ℂ)‖ ≤ jetN b κ ^ 1 ∧
    ‖cZero b E‖ ≤ jetN b κ ^ 1 ∧ ‖((sigmaPlus b : ℝ) : ℂ)‖ ≤ jetN b κ ^ 1 ∧
    ‖(etaZ b E : ℂ)⁻¹‖ ≤ jetN b κ ^ 1 := by
  obtain ⟨h1, h2⟩ := bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηL := etaLow_pos (b := b) (by linarith) hκ
  have hηle := etaLow_le (b := b) (by linarith) hκ hE
  have h1b : 0 < 1 - b := by linarith
  have hd1 : 1 ≤ dStar b := by rw [dStar, le_div_iff₀ h1b]; linarith
  have hib : 0 < 1 / b := by positivity
  have hiη : 0 < (etaLow b κ)⁻¹ := inv_pos.mpr hηL
  have hN2 : 2 ≤ jetN b κ := by unfold jetN; linarith
  have hbN : 1 / b ≤ jetN b κ := by unfold jetN; linarith
  have hdN : dStar b ≤ jetN b κ := by unfold jetN; linarith
  have hηN : (etaZ b E)⁻¹ ≤ jetN b κ := by
    have := inv_anti₀ hηL hηle
    unfold jetN; linarith
  simp only [pow_one, pow_zero]
  have hk := (norm_kMinus_lt b E hb0 hb h1 h2).le
  have hden := jet_denom_pos hb0 hb h1 h2 s hs.2
  refine ⟨hN2, hs.2.trans hdN, (norm_matchedA E h1 h2).le, hk.trans (by nlinarith), ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [norm_inv]
    exact (inv_anti₀ hb0 hden.le).trans (by rw [one_div] at hbN; exact hbN)
  · rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
  · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hdN
  · rw [cZero, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hη.le]
    simp only [Complex.norm_ofNat, mul_one]
    rw [mul_inv]
    have : (2 : ℝ)⁻¹ ≤ 1 := by norm_num
    nlinarith [inv_pos.mpr hη]
  · rw [Complex.norm_real, sigmaPlus, kPlus]
    rw [Real.norm_of_nonneg (div_nonneg (by nlinarith) hb0.le)]
    calc ((1 - 2 * b) + b ^ 2) / b ≤ 1 / b := by
          apply div_le_div_of_nonneg_right _ hb0.le; nlinarith
      _ ≤ _ := hbN
  · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hη.le]; exact hηN

theorem norm_jetB_pw : ‖jetB b E s‖ ≤ jetN b κ ^ 3 := by
  obtain ⟨hN, hs', -, -, -, -, hd, hc, -, -⟩ := jet_basic hb0 hb hκ hE hs
  exact pw_mono hN (pw_mul hN hc (pw_add hN hd hs')) (by norm_num)

theorem norm_jetC_pw : ‖jetC b E s‖ ≤ jetN b κ ^ 5 := by
  obtain ⟨hN, hs', -, -, -, -, hd, -, -, hη⟩ := jet_basic hb0 hb hκ hE hs
  have h2 : ‖(2 : ℂ)‖ ≤ jetN b κ ^ 1 := by simp only [Complex.norm_ofNat, pow_one]; exact hN
  have hi : ‖(4 * (etaZ b E : ℂ) ^ 2)⁻¹‖ ≤ jetN b κ ^ 2 := by
    have e : (4 * (etaZ b E : ℂ) ^ 2)⁻¹ = (4 : ℂ)⁻¹ * ((etaZ b E : ℂ)⁻¹ * (etaZ b E : ℂ)⁻¹) := by
      rw [mul_inv, pow_two, mul_inv]
    rw [e]
    have h4 : ‖(4 : ℂ)⁻¹‖ ≤ jetN b κ ^ 0 := by
      rw [norm_inv]; simp only [Complex.norm_ofNat, pow_zero]; norm_num
    exact pw_mono hN (pw_mul hN h4 (pw_mul hN hη hη)) (by norm_num)
  unfold jetC
  exact pw_mono hN (pw_div hN (pw_add hN (pw_add hN hs' (pw_conj hs')) (pw_mul hN h2 hd)) hi)
    (by norm_num)

theorem norm_leadA_pw (p : Fin 2) : ‖leadA b E s p‖ ≤ jetN b κ ^ 3 := by
  obtain ⟨hN, -, ha, -, hD, hbb, -, -, -, -⟩ := jet_basic hb0 hb hκ hE hs
  have h1 : ‖(1 : ℂ)‖ ≤ jetN b κ ^ 0 := by simp
  fin_cases p
  · show ‖1 / leadDen b E s‖ ≤ _
    exact pw_mono hN (pw_div hN h1 hD) (by norm_num)
  · show ‖(b : ℂ) * matchedA E ^ 2 / leadDen b E s‖ ≤ _
    rw [pow_two]
    exact pw_mono hN (pw_div hN (pw_mul hN hbb (pw_mul hN ha ha)) hD) (by norm_num)

theorem norm_leadB_pw (p : Fin 2) : ‖leadB b p‖ ≤ jetN b κ ^ 3 := by
  obtain ⟨hN, -⟩ := jet_basic hb0 hb hκ hE hs
  have hbN : 1 / b ≤ jetN b κ := by
    unfold jetN; have := etaLow_pos (b := b) (by linarith) hκ
    have : 0 ≤ dStar b := by rw [dStar]; exact div_nonneg zero_le_one (by linarith)
    have : 0 ≤ (etaLow b κ)⁻¹ := by positivity
    linarith
  refine pw_mono hN (i := 1) ?_ (by norm_num)
  fin_cases p
  · show ‖((1 / b : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), pow_one]; exact hbN
  · show ‖((1 : ℝ) : ℂ)‖ ≤ _
    simp only [Complex.ofReal_one, norm_one, pow_one]; linarith

omit hb0 hb hκ hE hs in
theorem norm_leadInd_pw (p : Fin 2) : ‖leadInd p‖ ≤ jetN b κ ^ 0 := by
  fin_cases p <;> simp [leadInd]

theorem norm_leadR1_pw (p : Fin 2) : ‖leadR1 b p‖ ≤ jetN b κ ^ 4 := by
  obtain ⟨hN, -, -, -, -, -, hd, -⟩ := jet_basic hb0 hb hκ hE hs
  have hB := norm_leadB_pw hb0 hb hκ hE hs 0
  have e0 : leadR1 b 0 = ((dStar b : ℝ) : ℂ) * leadB b 0 := by
    simp only [leadR1, leadB, Matrix.cons_val_zero]; push_cast; ring
  have e1 : leadR1 b 1 = ((dStar b : ℝ) : ℂ) * 1 := by
    simp only [leadR1, Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  have h1 : ‖(1 : ℂ)‖ ≤ jetN b κ ^ 0 := by simp
  fin_cases p
  · show ‖leadR1 b 0‖ ≤ _
    rw [e0]; exact pw_mono hN (pw_mul hN hd hB) (by norm_num)
  · show ‖leadR1 b 1‖ ≤ _
    rw [e1]; exact pw_mono hN (pw_mul hN hd h1) (by norm_num)

theorem norm_leadU1_pw (p : Fin 2) : ‖leadU1 b E s p‖ ≤ jetN b κ ^ 4 := by
  obtain ⟨hN, hs', ha, -, hD, hbb, -, -, -, -⟩ := jet_basic hb0 hb hκ hE hs
  have hs'' : ‖-s‖ ≤ jetN b κ ^ 1 := by rwa [norm_neg]
  fin_cases p
  · show ‖-s / leadDen b E s‖ ≤ _
    exact pw_mono hN (pw_div hN hs'' hD) (by norm_num)
  · show ‖-s * b * matchedA E ^ 2 / leadDen b E s‖ ≤ _
    rw [pow_two]
    exact pw_mono hN (pw_div hN (pw_mul hN (pw_mul hN hs'' hbb) (pw_mul hN ha ha)) hD)
      (by norm_num)

theorem norm_leadSv_pw (p : Fin 2) : ‖leadSv b E s p‖ ≤ jetN b κ ^ 16 := by
  obtain ⟨hN, -, ha, hk, hD, hbb, hd, -, -, -⟩ := jet_basic hb0 hb hκ hE hs
  have hB := norm_leadB_pw hb0 hb hκ hE hs p
  have hJ := norm_jetB_pw hb0 hb hκ hE hs
  have hI := norm_leadInd_pw (b := b) (κ := κ) p
  have hR := norm_leadR1_pw hb0 hb hκ hE hs p
  unfold leadSv
  exact pw_mono hN (pw_div hN (pw_add hN (pw_mul hN (pw_mul hN hk hB) hJ)
    (pw_mul hN (pw_mul hN (pw_mul hN hbb ha) hd) (pw_add hN hI (pw_mul hN hbb hR)))) hD)
    (by norm_num)

theorem norm_leadSw_pw (p : Fin 2) : ‖leadSw b E s p‖ ≤ jetN b κ ^ 8 := by
  obtain ⟨hN, -, ha, -, -, hbb, hd, -, hσ, -⟩ := jet_basic hb0 hb hκ hE hs
  have hA := norm_leadA_pw hb0 hb hκ hE hs p
  have hJ := norm_jetB_pw hb0 hb hκ hE hs
  have hI := norm_leadInd_pw (b := b) (κ := κ) p
  have hU := norm_leadU1_pw hb0 hb hκ hE hs p
  unfold leadSw
  exact pw_mono hN (pw_add hN (pw_mul hN (pw_mul hN hσ hA) hJ)
    (pw_mul hN (pw_mul hN ha hd) (pw_add hN hI (pw_mul hN hbb hU)))) (by norm_num)

theorem norm_leadV1_pw (p : Fin 2) : ‖leadV1 b E s p‖ ≤ jetN b κ ^ 18 := by
  obtain ⟨hN, hs', -⟩ := jet_basic hb0 hb hκ hE hs
  have hB := norm_leadB_pw hb0 hb hκ hE hs p
  have hJ := norm_jetB_pw hb0 hb hκ hE hs
  have hS := norm_leadSv_pw hb0 hb hκ hE hs p
  unfold leadV1
  exact pw_mono hN (pw_sub hN (pw_mul hN hB hJ) (pw_mul hN hs' hS)) (by norm_num)

theorem norm_leadSz_pw (p : Fin 2) : ‖leadSz b E s p‖ ≤ jetN b κ ^ 24 := by
  obtain ⟨hN, -, ha, -, -, hbb, hd, -, hσ, -⟩ := jet_basic hb0 hb hκ hE hs
  have hB := norm_leadB_pw hb0 hb hκ hE hs p
  have hJ := norm_jetB_pw hb0 hb hκ hE hs
  have hC := norm_jetC_pw hb0 hb hκ hE hs
  have hS := norm_leadSv_pw hb0 hb hκ hE hs p
  have hI := norm_leadInd_pw (b := b) (κ := κ) p
  have hR := norm_leadR1_pw hb0 hb hκ hE hs p
  have hV := norm_leadV1_pw hb0 hb hκ hE hs p
  have haV := pw_mul hN ha hV
  unfold leadSz
  rw [pow_two]
  exact pw_mono hN (pw_add hN (pw_add hN (pw_mul hN hσ (pw_add hN (pw_add hN (pw_mul hN hB hC)
    (pw_mul hN hS hJ)) (pw_mul hN (pw_conj hS) (pw_conj hJ))))
    (pw_mul hN (pw_mul hN hd hd) (pw_add hN hI (pw_mul hN hbb hR))))
    (pw_mul hN (pw_mul hN hbb hd) (pw_add hN haV (pw_conj haV)))) (by norm_num)

theorem jetL_nonneg : 0 ≤ jetL b κ := by
  obtain ⟨hN, -⟩ := jet_basic hb0 hb hκ hE hs
  unfold jetL; positivity

/-- **Uniform bounds of the leading jet values** on `bulkInterval κ`. -/
theorem lead_le_jetL (p : Fin 2) :
    ‖jetB b E s‖ ≤ jetL b κ ∧ ‖jetC b E s‖ ≤ jetL b κ ∧ ‖leadA b E s p‖ ≤ jetL b κ ∧
    ‖leadB b p‖ ≤ jetL b κ ∧ ‖leadR1 b p‖ ≤ jetL b κ ∧ ‖leadU1 b E s p‖ ≤ jetL b κ ∧
    ‖leadSv b E s p‖ ≤ jetL b κ ∧ ‖leadSw b E s p‖ ≤ jetL b κ ∧ ‖leadV1 b E s p‖ ≤ jetL b κ ∧
    ‖leadSz b E s p‖ ≤ jetL b κ := by
  obtain ⟨hN, -⟩ := jet_basic hb0 hb hκ hE hs
  have m : ∀ {x : ℂ} {i : ℕ}, ‖x‖ ≤ jetN b κ ^ i → i ≤ 24 → ‖x‖ ≤ jetL b κ :=
    fun h hi => pw_mono hN h hi
  exact ⟨m (norm_jetB_pw hb0 hb hκ hE hs) (by norm_num),
    m (norm_jetC_pw hb0 hb hκ hE hs) (by norm_num), m (norm_leadA_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadB_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadR1_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadU1_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadSv_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadSw_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadV1_pw hb0 hb hκ hE hs p) (by norm_num),
    m (norm_leadSz_pw hb0 hb hκ hE hs p) le_rfl⟩

theorem leadConst_le_bulk : leadConst b E s ≤ leadConstL b κ := by
  have h0 := lead_le_jetL hb0 hb hκ hE hs 0
  have h1 := lead_le_jetL hb0 hb hκ hE hs 1
  have hi := inv_etaZ_le_bulk hb hκ hE
  have hη := etaZ_pos_bulk hb hκ hE
  have hc : leadCoef b E s 0 + leadCoef b E s 1 + 1 ≤ 12 * jetL b κ + 1 := by
    unfold leadCoef; linarith [h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.1,
      h0.2.2.2.2.2.2.2.2.2, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1,
      h1.2.2.2.2.2.2.2.2.2]
  have hc0 : 0 ≤ leadCoef b E s 0 + leadCoef b E s 1 + 1 := by
    have := leadCoef_nonneg b E s 0; have := leadCoef_nonneg b E s 1; linarith
  have hq : (1 + (etaZ b E)⁻¹) ^ 2 ≤ (1 + (etaLow b κ)⁻¹) ^ 2 := by
    have : 0 ≤ (etaZ b E)⁻¹ := inv_nonneg.mpr hη.le
    gcongr
  unfold leadConst leadConstL
  exact mul_le_mul hc hq (by positivity) (by linarith)

end Bulk

end BlockBand.Transmission.CovarianceBulk
