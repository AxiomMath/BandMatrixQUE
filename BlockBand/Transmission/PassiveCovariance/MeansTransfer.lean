module

public import BlockBand.Transmission.PassiveCovariance.MeansNear
public import BlockBand.Transmission.SourceMixing.MatchedBasic

/-!
# `MeansMatchMain` from the single-mean approximations

* `leadConst`, `norm_leadGam_le`, `norm_leadAlp_le`, `norm_leadAlpI_le`: `‖L_i‖ ≤ Λ` uniformly in
  passive `X` (`‖R‖ ≤ η⁻¹`).
* `srcX1_eq`, `srcX2_eq`: the sources with only `p = 0` (the left vectors `x̌ = (K̂M̄)ᴴι₁v` are
  physical, `x̌ = ι₁(KMᴴv)`, `KM = kmOf`), and `s_{0p} = w_p/W`.
* **`meansMatchMain_of_near (hA) (hT) (hG) (hP) (hQ) : MeansMatchMain`**: from
  `PassiveBoundsStatement`, `TauNear` and the three `MeanNear` statements of `MeansNear`, with
  `lead_eq_main` for the exact sum and `matchedBasic` for `‖KM - 1‖ ≤ C·ε`.
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

/-!
## Bounds on the leading values
-/

/-- The coefficient size of the leading values. -/
def leadCoef (b E : ℝ) (s : ℂ) (p : Fin 2) : ℝ :=
  ‖leadA b E s p‖ + ‖leadB b p‖ + 2 * ‖leadSv b E s p‖ + ‖leadSw b E s p‖ + ‖leadSz b E s p‖

/-- `Λ = (Σ_p coef_p + 1)(1 + η⁻¹)²`. -/
def leadConst (b E : ℝ) (s : ℂ) : ℝ :=
  (leadCoef b E s 0 + leadCoef b E s 1 + 1) * (1 + (etaZ b E)⁻¹) ^ 2

theorem leadCoef_nonneg (b E : ℝ) (s : ℂ) (p : Fin 2) : 0 ≤ leadCoef b E s p := by
  unfold leadCoef; positivity

theorem coef_le_leadConst (b E : ℝ) (s : ℂ) (p : Fin 2) :
    leadCoef b E s p * (1 + (etaZ b E)⁻¹) ^ 2 ≤ leadConst b E s := by
  have h0 := leadCoef_nonneg b E s 0
  have h1 := leadCoef_nonneg b E s 1
  unfold leadConst
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  fin_cases p <;> simp <;> linarith

theorem norm_smul_le' {W : ℕ} (c : ℂ) (A : Matrix (Fin W) (Fin W) ℂ) {r : ℝ} (hA : ‖A‖ ≤ r) :
    ‖c • A‖ ≤ ‖c‖ * r := (norm_smul_le c A).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg _))

section Bounds

variable {b E : ℝ} {s : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
  (hR : ‖passiveResolvent b E X‖ ≤ (etaZ b E)⁻¹)
include hη hR

theorem lead_basic :
    ‖passiveResolvent b E X‖ ≤ (1 + (etaZ b E)⁻¹) ^ 2 ∧
      ‖(passiveResolvent b E X)ᴴ‖ ≤ (1 + (etaZ b E)⁻¹) ^ 2 ∧
      ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ (1 + (etaZ b E)⁻¹) ^ 2 ∧
      ‖(passiveResolvent b E X)ᴴ * passiveResolvent b E X‖ ≤ (1 + (etaZ b E)⁻¹) ^ 2 := by
  have hi : 0 ≤ (etaZ b E)⁻¹ := inv_nonneg.mpr hη.le
  have h1 : (etaZ b E)⁻¹ ≤ (1 + (etaZ b E)⁻¹) ^ 2 := by nlinarith
  have hRR : ‖(passiveResolvent b E X)ᴴ * passiveResolvent b E X‖ ≤ (1 + (etaZ b E)⁻¹) ^ 2 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg (passiveResolvent b E X)]
  refine ⟨hR.trans h1, by rw [Matrix.l2_opNorm_conjTranspose]; exact hR.trans h1,
    norm_one_matrix_le.trans (by nlinarith), hRR⟩

theorem norm_leadAlp_le (i : Fin 2 × Fin 2) : ‖leadAlp i b E s W X‖ ≤ leadConst b E s := by
  obtain ⟨hr, hrh, h1, hrr⟩ := lead_basic hη hR
  refine le_trans ?_ (coef_le_leadConst b E s i.2)
  have hc := leadCoef_nonneg b E s i.2
  set ρ := (1 + (etaZ b E)⁻¹) ^ 2
  obtain ⟨k, p⟩ := i
  fin_cases k
  · show ‖leadM2 b E s X p‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    have := norm_smul_le' (leadA b E s p) _ hr
    have := norm_smul_le' (leadSw b E s p) _ h1
    have : 0 ≤ ρ := by positivity
    unfold leadCoef
    nlinarith [norm_nonneg (leadB b p), norm_nonneg (leadSv b E s p), norm_nonneg (leadSz b E s p)]
  · show ‖leadM4 b E s X p‖ ≤ _
    have hn : ‖leadM4 b E s X p‖ ≤ ‖leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X)‖ +
        ‖conj (leadSv b E s p) • (passiveResolvent b E X)ᴴ‖ +
        ‖leadSv b E s p • passiveResolvent b E X‖ + ‖leadSz b E s p • (1 : Matrix (Fin W) (Fin W) ℂ)‖ := by
      unfold leadM4
      have := norm_add_le (leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) +
        conj (leadSv b E s p) • (passiveResolvent b E X)ᴴ + leadSv b E s p • passiveResolvent b E X)
        (leadSz b E s p • (1 : Matrix (Fin W) (Fin W) ℂ))
      have := norm_add_le (leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) +
        conj (leadSv b E s p) • (passiveResolvent b E X)ᴴ) (leadSv b E s p • passiveResolvent b E X)
      have := norm_add_le (leadB b p • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X))
        (conj (leadSv b E s p) • (passiveResolvent b E X)ᴴ)
      linarith
    refine hn.trans ?_
    have := norm_smul_le' (leadB b p) _ hrr
    have := norm_smul_le' (conj (leadSv b E s p)) _ hrh
    have := norm_smul_le' (leadSv b E s p) _ hr
    have := norm_smul_le' (leadSz b E s p) _ h1
    rw [Complex.norm_conj] at *
    have : 0 ≤ ρ := by positivity
    unfold leadCoef
    nlinarith [norm_nonneg (leadA b E s p), norm_nonneg (leadSw b E s p)]

theorem norm_leadAlpI_le (i : Fin 2 × Fin 2) : ‖leadAlpI i b E s W X‖ ≤ leadConst b E s := by
  obtain ⟨hr, -, -, hrr⟩ := lead_basic hη hR
  refine le_trans ?_ (coef_le_leadConst b E s i.2)
  have hc := leadCoef_nonneg b E s i.2
  set ρ := (1 + (etaZ b E)⁻¹) ^ 2
  obtain ⟨k, p⟩ := i
  have : 0 ≤ ρ := by positivity
  fin_cases k
  · show ‖leadA b E s p • passiveResolvent b E X‖ ≤ leadCoef b E s p * ρ
    have := norm_smul_le' (leadA b E s p) _ hr
    unfold leadCoef
    nlinarith [norm_nonneg (leadB b p), norm_nonneg (leadSv b E s p), norm_nonneg (leadSz b E s p),
      norm_nonneg (leadSw b E s p)]
  · show ‖leadM6 b E s X p‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    have := norm_smul_le' (leadB b p) _ hrr
    have := norm_smul_le' (leadSv b E s p) _ hr
    unfold leadCoef
    nlinarith [norm_nonneg (leadA b E s p), norm_nonneg (leadSw b E s p),
      norm_nonneg (leadSz b E s p), norm_nonneg (leadSv b E s p)]

theorem norm_leadGam_le (k : Fin 2) : ‖leadGam k b E s W X‖ ≤ leadConst b E s := by
  obtain ⟨hr, -, h1, -⟩ := lead_basic hη hR
  have h0 := leadCoef_nonneg b E s 0
  have h1' := leadCoef_nonneg b E s 1
  have hρ : (1 + (etaZ b E)⁻¹) ^ 2 ≤ leadConst b E s := by
    unfold leadConst
    have : 0 ≤ (1 + (etaZ b E)⁻¹) ^ 2 := by positivity
    nlinarith
  fin_cases k
  · exact hr.trans hρ
  · exact h1.trans hρ

end Bounds

/-!
## The sources with `p = 0` only
-/

/-- `∫ x*(P_pΓ)y = [p=0] ∫ x*Γy` for physical `x`. -/
theorem integral_form_bProj (p : Fin 2) {w : LayerSite W .oneBlockOnePort → ℂ} (hw : IsPhys w)
    (μ : Measure (LayerSample W .oneBlockOnePort)) (Γ : LayerSample W .oneBlockOnePort → LayerMat W)
    (y : LayerSite W .oneBlockOnePort → ℂ) :
    ∫ ω, star w ⬝ᵥ ((bProj p * Γ ω) *ᵥ y) ∂μ =
      (if p = 0 then 1 else 0) * ∫ ω, star w ⬝ᵥ (Γ ω *ᵥ y) ∂μ := by
  have e := fun ω => form_bProj_phys p hw (Γ ω) y
  simp only [e]
  exact integral_const_mul _ _

theorem srcX1_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ u₁ : Fin W → ℂ)
    (hu : (kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁ = physVec u₁) :
    srcX1 b E X v₁ v₂ v₃ v₄ = ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W *
      ((∫ ω, star (physVec u₁) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₄) ∂layerLaw W b .oneBlockOnePort) *
        ∫ ω, star (physVec v₃) ⬝ᵥ (alpFam (k, p) b E W X ω *ᵥ physVec v₂)
          ∂layerLaw W b .oneBlockOnePort) := by
  unfold srcX1
  rw [hu]
  simp only [integral_form_bProj _ (isPhys_physVec u₁), Fin.sum_univ_two, bVar_zero hb0 hb]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, one_mul, zero_mul, mul_zero, add_zero]
  rfl

theorem srcX2_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ u₁ u₂ : Fin W → ℂ)
    (hu₁ : (kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₁ = physVec u₁)
    (hu₂ : (kHat b E X * mbarSide b E X false)ᴴ *ᵥ physVec v₂ = physVec u₂) :
    srcX2 b E X v₁ v₂ v₃ v₄ = ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W *
      ((∫ ω, star (physVec u₂) ⬝ᵥ (gamFam k b E W X ω *ᵥ physVec v₃) ∂layerLaw W b .oneBlockOnePort) *
        ∫ ω, star (physVec v₄) ⬝ᵥ (alpFamI (k, p) b E W X ω *ᵥ physVec u₁)
          ∂layerLaw W b .oneBlockOnePort) := by
  unfold srcX2
  rw [hu₁, hu₂]
  simp only [integral_form_bProj _ (isPhys_physVec u₂), Fin.sum_univ_two, bVar_zero hb0 hb]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, one_mul, zero_mul, mul_zero, add_zero]
  rfl

theorem leadX1_eq' (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    leadX1 b E s X v₁ v₂ v₃ v₄ = ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W *
      (bilinear v₁ (leadGam k b E s W X) v₄ * bilinear v₃ (leadAlp (k, p) b E s W X) v₂) := by
  simp only [leadX1, Fin.sum_univ_two, leadGam, leadAlp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

theorem leadX2_eq' (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    leadX2 b E s X v₁ v₂ v₃ v₄ = ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W *
      (bilinear v₂ (leadGam k b E s W X) v₃ * bilinear v₄ (leadAlpI (k, p) b E s W X) v₁) := by
  simp only [leadX2, Fin.sum_univ_two, leadGam, leadAlpI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  ring

/-!
## Error bookkeeping
-/

theorem norm_wsum_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (f : Fin 2 → Fin 2 → ℂ) {e : ℝ}
    (h : ∀ k p, ‖f k p‖ ≤ e) :
    ‖∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * f k p‖ ≤ 4 * e / W := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have ht : ∀ k p, ‖sRow b p / W * f k p‖ ≤ e / W := fun k p => by
    rw [norm_mul, norm_div, Complex.norm_natCast]
    rcases hW.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right ((mul_le_mul (norm_sRow_le hb0 hb p) (h k p)
        (norm_nonneg _) zero_le_one).trans (one_mul _).le) hW
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun p _ => ht k p)).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring_nf; rfl

theorem norm_wsum_sub_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (x y : Fin 2 → Fin 2 → ℂ) {e : ℝ}
    (h : ∀ k p, ‖x k p - y k p‖ ≤ e) :
    ‖∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * x k p - ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * y k p‖ ≤
      4 * e / W := by
  have e' : ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * x k p -
      ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * y k p =
      ∑ k : Fin 2, ∑ p : Fin 2, sRow b p / W * (x k p - y k p) := by
    simp only [Fin.sum_univ_two]; ring
  rw [e']
  exact norm_wsum_le hb0 hb _ h

/-- Replacing the left vector `KMᴴv` by `v` costs `‖KM - 1‖‖L‖`. -/
theorem near_left {u v w : Fin W → ℂ} {L KM : Matrix (Fin W) (Fin W) ℂ} {m : ℂ}
    {C ε Λ C₀ K₁ : ℝ} (hu : u = KMᴴ *ᵥ v)
    (hm : ‖m - bilinear u L w‖ ≤ C * ε * (vecNorm u * vecNorm w)) (hv : vecNorm v ≤ 1)
    (hw : vecNorm w ≤ 1) (hK : ‖KM‖ ≤ K₁) (hK1 : ‖KM - 1‖ ≤ C₀ * ε) (hL : ‖L‖ ≤ Λ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    ‖m - bilinear v L w‖ ≤ (C * K₁ + C₀ * Λ) * ε := by
  have hu' : vecNorm u ≤ K₁ := by
    rw [hu]; refine (vecNorm_mulVec_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg KM, vecNorm_nonneg v]
  have e : m - bilinear v L w = (m - bilinear u L w) + bilinear v ((KM - 1) * L) w := by
    rw [hu, bilinear_conjT_left, Matrix.sub_mul, Matrix.one_mul, bilinear_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 := norm_bilinear_le v ((KM - 1) * L) w
  have h3 : ‖(KM - 1) * L‖ ≤ C₀ * ε * Λ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hK1 hL (norm_nonneg _) (by
      exact (norm_nonneg _).trans hK1))
  have hvw : vecNorm u * vecNorm w ≤ K₁ := by
    nlinarith [vecNorm_nonneg u, vecNorm_nonneg w]
  have := vecNorm_nonneg v; have := vecNorm_nonneg w
  calc _ ≤ C * ε * K₁ + C₀ * ε * Λ := by
        refine add_le_add (hm.trans (mul_le_mul_of_nonneg_left hvw (by positivity))) ?_
        refine h2.trans ?_
        have h3' : 0 ≤ C₀ * ε * Λ := (norm_nonneg _).trans h3
        calc vecNorm v * ‖(KM - 1) * L‖ * vecNorm w ≤ 1 * (C₀ * ε * Λ) * 1 := by gcongr
          _ = C₀ * ε * Λ := by ring
    _ = (C * K₁ + C₀ * Λ) * ε := by ring

/-- Replacing the right vector `KMᴴv` by `v`. -/
theorem near_right {u v w : Fin W → ℂ} {L KM : Matrix (Fin W) (Fin W) ℂ} {m : ℂ}
    {C ε Λ C₀ K₁ : ℝ} (hu : u = KMᴴ *ᵥ v)
    (hm : ‖m - bilinear w L u‖ ≤ C * ε * (vecNorm w * vecNorm u)) (hv : vecNorm v ≤ 1)
    (hw : vecNorm w ≤ 1) (hK : ‖KM‖ ≤ K₁) (hK1 : ‖KM - 1‖ ≤ C₀ * ε) (hL : ‖L‖ ≤ Λ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ) :
    ‖m - bilinear w L v‖ ≤ (C * K₁ + C₀ * Λ) * ε := by
  have hu' : vecNorm u ≤ K₁ := by
    rw [hu]; refine (vecNorm_mulVec_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg KM, vecNorm_nonneg v]
  have e : m - bilinear w L v = (m - bilinear w L u) + bilinear w (L * (KM - 1)ᴴ) v := by
    rw [hu, bilinear_mulVec_right, conjTranspose_sub, conjTranspose_one, Matrix.mul_sub,
      Matrix.mul_one, bilinear_sub]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have h2 := norm_bilinear_le w (L * (KM - 1)ᴴ) v
  have h3 : ‖L * (KM - 1)ᴴ‖ ≤ Λ * (C₀ * ε) := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    exact mul_le_mul hL hK1 (norm_nonneg _) hΛ
  have hvw : vecNorm w * vecNorm u ≤ K₁ := by
    nlinarith [vecNorm_nonneg u, vecNorm_nonneg w]
  have := vecNorm_nonneg v; have := vecNorm_nonneg w
  calc _ ≤ C * ε * K₁ + Λ * (C₀ * ε) := by
        refine add_le_add (hm.trans (mul_le_mul_of_nonneg_left hvw (by positivity))) ?_
        refine h2.trans ?_
        have h3' : 0 ≤ Λ * (C₀ * ε) := (norm_nonneg _).trans h3
        calc vecNorm w * ‖L * (KM - 1)ᴴ‖ * vecNorm v ≤ 1 * (Λ * (C₀ * ε)) * 1 := by gcongr
          _ = Λ * (C₀ * ε) := by ring
    _ = (C * K₁ + C₀ * Λ) * ε := by ring

end BlockBand.Transmission.PassiveCovariance
