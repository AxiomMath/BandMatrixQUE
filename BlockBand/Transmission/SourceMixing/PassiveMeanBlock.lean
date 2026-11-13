module

public import BlockBand.Transmission.SourceMixing.WordMean

/-!
# Block extraction of the two-resolvent mean: `E[LL*] = s₁(KM)(KM)* + O(W⁻²)`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`), operator norm, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E`
only, uniformly in `W ≥ W₀` and `X`.

The physical block of the two-resolvent weighted equation gives the mean of `LL*`.

* `kmOf = blkAt(K̂D⁻¹) 0 0` (`= (z - X)M`, `M = (ζ - X)⁻¹` the dressed physical block);
* `tTwo r = E⟨(𝒢P₂𝒢ᴴ)_{rr}⟩`, `sOne = (1-2b)t₁ + bt₂`;
* `freshU_mean`: `‖E[LL*] - s₁·KM(KM)ᴴ‖ ≤ C/W²` (the `(0,0)` block of `twoResolvent_weighted`),
  together with the bounds `‖KM‖, |s₁| ≤ C`.
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
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `KM = blkAt(K̂D⁻¹) 0 0`. -/
def kmOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  blkAt (kHat b E X * (dressed b E X)⁻¹) 0 0

/-- `t_r = E⟨(𝒢P₂𝒢ᴴ)_{rr}⟩`. -/
def tTwo (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (r : Fin 2) : ℂ :=
  ∫ ω, blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r ∂layerLaw W b .oneBlockOnePort

/-- `s₁ = (1-2b)t₁ + bt₂`. -/
def sOne (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  ((1 - 2 * b : ℝ) : ℂ) * tTwo b E X 0 + (b : ℂ) * tTwo b E X 1

theorem matrixExpect_conjTranspose {Ω n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : Ω → Matrix n n ℂ) : matrixExpect μ (fun ω => (F ω)ᴴ) = (matrixExpect μ F)ᴴ := by
  ext i j
  simp only [matrixExpect, conjTranspose_apply, Matrix.of_apply]
  exact integral_conj

theorem mul_matrixExpect' {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {μ : Measure Ω}
    (R : Matrix n n ℂ) (F : Ω → Matrix n n ℂ) (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    R * matrixExpect μ F = matrixExpect μ (fun ω => R * F ω) := by
  ext i j
  simp only [matrixExpect, Matrix.mul_apply, Matrix.of_apply]
  rw [integral_finsetSum _ fun k _ => (hF k j).const_mul _]
  simp only [integral_const_mul]

theorem blkAt_matrixExpect {μ : Measure (LayerSample W .oneBlockOnePort)}
    (F : LayerSample W .oneBlockOnePort → LayerMat W) (r s : Fin 2) :
    blkAt (matrixExpect μ F) r s = matrixExpect μ (fun ω => blkAt (F ω) r s) := rfl

theorem blkAt_selfEnergy (b : ℝ) (m₁ m₂ : ℂ) :
    blkAt (selfEnergy b m₁ m₂ : LayerMat W) 0 0 = (((1 - 2 * b : ℝ) : ℂ) * m₁ + (b : ℂ) * m₂) • 1 ∧
      blkAt (selfEnergy b m₁ m₂ : LayerMat W) 0 1 = 0 := by
  constructor <;> ext x y <;>
    simp [blkAt, siteOf, selfEnergy, Matrix.diagonal_apply, Matrix.one_apply]

theorem blkAt_portProj_mul_zero (M : LayerMat W) (s : Fin 2) : blkAt (pTwo * M) 0 s = 0 := by
  rw [blkAt_mul, Fin.sum_univ_two, blkAt_portProj, blkAt_portProj]
  simp

theorem blkAt_kHat_mul_zero (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (M : LayerMat W) :
    blkAt (kHat b E X * M) 0 0 = (boundaryZ b E • 1 - X) * blkAt M 0 0 ∧
      blkAt (kHat b E X * M) 0 1 = (boundaryZ b E • 1 - X) * blkAt M 0 1 := by
  obtain ⟨k00, k01, -, -⟩ := blkAt_kHat b E X
  constructor <;> rw [blkAt_mul, Fin.sum_univ_two, k00, k01, Matrix.zero_mul, add_zero]

/-- `blkAt(K̂𝒢P₂(K̂𝒢)ᴴ) 0 0 = LL*` pointwise. -/
theorem blkAt_freshU (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    blkAt (kHat b E X * (gRes b E X ω * (pTwo * (kHat b E X * gRes b E X ω)ᴴ))) 0 0 =
      freshU b E X ω := by
  set G := gRes b E X ω
  have hM : kHat b E X * (G * (pTwo * (kHat b E X * G)ᴴ)) =
      wLetter (kHat b E X) G 1 * (portProj * wLetter (kHat b E X) G 3) := by
    show _ = (kHat b E X * G) * (portProj * (kHat b E X * G)ᴴ)
    rw [Matrix.mul_assoc]
  have h01 : blkAt (wLetter (kHat b E X) G 1) 0 1 = lAt E (boundaryZ b E) X ω := by
    rw [blkAt_wLetter]; rfl
  have h10 : blkAt (wLetter (kHat b E X) G 3) 1 0 = (lAt E (boundaryZ b E) X ω)ᴴ := by
    rw [blkAt_wLetter]; rfl
  have c0 : ((0 : Fin 2) = 1) = False := by decide
  rw [hM, blkAt_mul, Fin.sum_univ_two, blkAt_mul, blkAt_mul, Fin.sum_univ_two, Fin.sum_univ_two,
    blkAt_portProj, blkAt_portProj, blkAt_portProj, blkAt_portProj]
  simp only [c0, and_false, false_and, and_self, ↓reduceIte, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero, h01, h10]
  rfl

theorem wordVal_GPGstar (Kh G : LayerMat W) :
    wordVal Kh G ![0, 2] ![1, pTwo, 1] = G * (pTwo * Gᴴ) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wLetter]

theorem wordVal_GPKGstar (Kh G : LayerMat W) :
    wordVal Kh G ![0, 3] ![1, pTwo, 1] = G * (pTwo * (Kh * G)ᴴ) := by
  rw [wordVal_succ, wordVal_succ, wordVal_zero]
  simp [wLetter]

theorem wordVal_G1 (Kh G : LayerMat W) : wordVal Kh G ![0] ![1, 1] = G := by
  rw [wordVal_succ, wordVal_zero]
  simp [wLetter]

theorem norm_ins_le (j : Fin 3) : ‖(![1, pTwo, 1] : Fin 3 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j
  · exact norm_one_matrix_le
  · exact norm_portProj_le
  · exact norm_one_matrix_le

theorem norm_ins1_le (j : Fin 2) : ‖(![1, 1] : Fin 2 → LayerMat W) j‖ ≤ 1 := by
  fin_cases j <;> exact norm_one_matrix_le

/-- Block extraction of the passive mean: `‖E[LL*] - s₁·KM(KM)ᴴ‖ ≤ C/W²`, with the
bounds `‖KM‖ ≤ C`, `|s₁| ≤ C`. -/
theorem freshU_mean (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖kmOf b E X‖ ≤ C ∧ ‖sOne b E X‖ ≤ C ∧
        ‖matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X) -
          sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hT⟩ := twoResolvent_weighted hA hb0 hb h1 h2
  obtain ⟨CK, WK, hCK, hK⟩ := norm_kHat_dressedInv hA hb0 hb h1 h2
  obtain ⟨Cw, Ww, hCw, hw⟩ := wordMean_bound hA hb0 hb h1 h2 2 1
  obtain ⟨CD, WD, -, hres⟩ := mean_residuals hA hb0 hb h1 h2
  set Cs := (1 - 2 * b) * Cw + b * Cw
  have hCs : 0 ≤ Cs := by have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  refine ⟨max (max CK Cs) (C₁ + Cs * CK * CK), max (max W₁ WK) (max Ww WD), by positivity,
    fun W hW X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₁, hWK⟩, hWw, hWD⟩ := hW
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set D := dressed b E X
  obtain ⟨-, -, hKD, hKE⟩ := hK W hWK X hX
  obtain ⟨-, -, -, -, -, -, e01, -⟩ := hres W hWD X hX
  have hKM : ‖kmOf b E X‖ ≤ CK := (norm_blkAt_le _ _ _).trans hKD
  -- `|t_r| ≤ Cw`, `|s₁| ≤ Cs`
  have ht : ∀ r, ‖tTwo b E X r‖ ≤ Cw := fun r => by
    have h := (hw W hWw X hX.posSemidef 2 le_rfl ![0, 2] ![1, pTwo, 1] norm_ins_le).2.2.2.2 r
    have e : (fun ω => blkTr (wordVal (kHat b E X) (gRes b E X ω) ![0, 2] ![1, pTwo, 1]) r) =
        fun ω => blkTr (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ)) r :=
      funext fun ω => by rw [wordVal_GPGstar]
    rw [e] at h
    exact h
  have hs : ‖sOne b E X‖ ≤ Cs := by
    unfold sOne
    have hb1 : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hb2 : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hb1, hb2]
    have : 0 ≤ 1 - 2 * b := by linarith
    exact add_le_add (mul_le_mul_of_nonneg_left (ht 0) this)
      (mul_le_mul_of_nonneg_left (ht 1) hb0.le)
  refine ⟨hKM.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hs.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
  -- integrability
  have hiN : ∀ α β, Integrable
      (fun ω => (gRes b E X ω * (pTwo * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 2 le_rfl ![0, 3] ![1, pTwo, 1] norm_ins_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] ![1, pTwo, 1] α β) =
        fun ω => (gRes b E X ω * (pTwo * (Kh * gRes b E X ω)ᴴ) : LayerMat W) α β :=
      funext fun ω => by rw [wordVal_GPKGstar]
    rw [e] at h
    exact h
  have hiG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) μ := fun α β => by
    have h := (hw W hWw X hX.posSemidef 1 (by norm_num) ![0] ![1, 1] norm_ins1_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0] ![1, 1] α β) =
        fun ω => gRes b E X ω α β := funext fun ω => by rw [wordVal_G1]
    rw [e] at h
    exact h
  have hT' := hT W hW₁ X hX
  set N := matrixExpect μ (fun ω => gRes b E X ω * (pTwo * (Kh * gRes b E X ω)ᴴ))
  set Ps := matrixExpect μ (fun ω => pTwo * (Kh * gRes b E X ω)ᴴ) with hPsdef
  set S := (selfEnergy b (tTwo b E X 0) (tTwo b E X 1) : LayerMat W) with hSdef
  set Gs := matrixExpect μ (fun ω => (Kh * gRes b E X ω)ᴴ) with hGsdef
  -- (a) the left block
  have ha : blkAt (Kh * N) 0 0 = matrixExpect μ (freshU b E X) := by
    rw [mul_matrixExpect' _ _ hiN, blkAt_matrixExpect]
    exact congrArg (matrixExpect μ) (funext fun ω => blkAt_freshU b E X ω)
  -- (b) the right block
  have hKD01 : blkAt (Kh * D⁻¹) 0 1 = 0 := by
    rw [(blkAt_kHat_mul_zero b E X D⁻¹).2, e01, Matrix.mul_zero]
  have hPs : blkAt Ps 0 0 = 0 := by
    have e : (fun ω => blkAt (pTwo * (Kh * gRes b E X ω)ᴴ) 0 0) =
        fun _ => (0 : Matrix (Fin W) (Fin W) ℂ) := funext fun ω => blkAt_portProj_mul_zero _ 0
    rw [hPsdef, blkAt_matrixExpect, e]
    ext x y; simp [matrixExpect]
  obtain ⟨hS00, hS01⟩ := blkAt_selfEnergy (W := W) b (tTwo b E X 0) (tTwo b E X 1)
  have hGs : blkAt Gs 0 0 = (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ := by
    rw [hGsdef, matrixExpect_conjTranspose, blkAt_conjTranspose, mul_matrixExpect' _ _ hiG]
  have hb : blkAt (Kh * D⁻¹ * (Ps + S * Gs)) 0 0 =
      kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ) := by
    have hSG : blkAt (S * Gs) 0 0 = sOne b E X • blkAt Gs 0 0 := by
      rw [blkAt_mul, Fin.sum_univ_two, hSdef, hS00, hS01, Matrix.zero_mul, add_zero,
        Matrix.smul_mul, Matrix.one_mul]
      rfl
    rw [blkAt_mul, Fin.sum_univ_two, hKD01, Matrix.zero_mul, add_zero, blkAt_add, hPs, zero_add,
      hSG, hGs]
    rfl
  -- assemble
  have hblk : ‖matrixExpect μ (freshU b E X) -
      kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ)‖ ≤
        C₁ / (W : ℝ) ^ 2 := by
    rw [← ha, ← hb, ← blkAt_sub]
    exact (norm_blkAt_le _ _ _).trans hT'
  have hdiff : ‖blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0 - kmOf b E X‖ ≤ CK / (W : ℝ) ^ 2 := by
    rw [kmOf, ← blkAt_sub]; exact (norm_blkAt_le _ _ _).trans hKE
  have e : matrixExpect μ (freshU b E X) - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ) =
      (matrixExpect μ (freshU b E X) -
        kmOf b E X * (sOne b E X • (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0)ᴴ)) +
      sOne b E X • (kmOf b E X * (blkAt (Kh * matrixExpect μ (gRes b E X)) 0 0 - kmOf b E X)ᴴ) := by
    rw [Matrix.mul_smul, conjTranspose_sub, Matrix.mul_sub, smul_sub]; abel
  rw [e]
  have hW2 : (0 : ℝ) ≤ (W : ℝ) ^ 2 := by positivity
  calc _ ≤ C₁ / (W : ℝ) ^ 2 + ‖sOne b E X‖ * (‖kmOf b E X‖ * (CK / (W : ℝ) ^ 2)) := by
        refine (norm_add_le _ _).trans (add_le_add hblk ?_)
        refine (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        refine (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [Matrix.l2_opNorm_conjTranspose]; exact hdiff
    _ ≤ C₁ / (W : ℝ) ^ 2 + Cs * (CK * (CK / (W : ℝ) ^ 2)) := by gcongr
    _ = (C₁ + Cs * CK * CK) / (W : ℝ) ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hW2

end BlockBand.Transmission.SourceMixing
