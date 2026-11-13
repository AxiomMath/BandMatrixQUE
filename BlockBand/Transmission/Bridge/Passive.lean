module

public import BlockBand.Transmission.Bridge.Recursion

/-!
# Passive coordinates along the near-end-grown path

For Hermitian GUE blocks (almost surely under `growthPathLaw`, see `ae_growth_isHermitian`),
nonnegative absorption `κ ≥ 0` and `Im z > 0`, along **every** sample and at **every** length
(no invertibility hypothesis; the totalized inverse is harmless here):

* `pathNearSchur_passive`: `-Im X_r ⪰ 0`;
* `isUnit_farPencil`: `z - 𝕏₁₁` is invertible (a hypothesis of `pathNearSchur_succ`);
* `pathTransmission_eq_one_sub` (no hypothesis, but see the caveat in its docstring):
  `T_r = I - S_rᴴS_r`, `S_r = I - 2iηR_r`;
* `pathTransmission_posSemidef`, `one_sub_pathTransmission_posSemidef`: `0 ⪯ T_r ⪯ I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-!
## Generic imaginary-part facts
-/

theorem matrixImaginaryPart_smul_hermitian {n : Type*} (c : ℂ) (M : Matrix n n ℂ)
    (hM : M.IsHermitian) : matrixImaginaryPart (c • M) = (c.im : ℂ) • M := by
  ext i j
  have hij : star (M j i) = M i j := by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hM i) j
  simp only [matrixImaginaryPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.conjTranspose_apply, smul_eq_mul, star_mul', hij]
  apply Complex.ext <;> simp <;> ring

/-- `-Im F⁻¹ ⪰ 0` whenever `Im F ⪰ 0` (also when `F` is singular: then `F⁻¹ = 0`). -/
theorem neg_im_inv_posSemidef {n : Type*} [Fintype n] [DecidableEq n] (F : Matrix n n ℂ)
    (hF : (matrixImaginaryPart F).PosSemidef) : (-matrixImaginaryPart F⁻¹).PosSemidef := by
  by_cases h : IsUnit F.det
  · exact neg_matrixImaginaryPart_nonsing_inv_posSemidef F h hF
  · rw [Matrix.nonsing_inv_apply_not_isUnit F h]
    simpa [matrixImaginaryPart] using Matrix.PosSemidef.zero

theorem neg_congruence {n k : Type*} [Fintype n] (C : Matrix n k ℂ) (M : Matrix n n ℂ) :
    -(Cᴴ * M * C) = Cᴴ * (-M) * C := by
  simp only [Matrix.mul_neg, Matrix.neg_mul]

/-!
## The path pencil
-/

theorem absorptionDiag_eq_I_smul {r : ℕ} (ε : Fin r → ℝ) :
    absorptionDiag W ε = Complex.I • Matrix.diagonal fun x : Fin r × Fin W => ((ε x.1 : ℝ) : ℂ) := by
  ext x y
  simp only [absorptionDiag, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem pathMatrix_pathAt_isHermitian (r : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) : (pathMatrix (pathAt W r ω)).IsHermitian := by
  ext x y
  have hAe : ∀ k (a c : Fin W), star (ω.1 k c a) = ω.1 k a c := fun k a c => by
    simpa [Matrix.conjTranspose_apply] using congrFun (congrFun (hA k) a) c
  simp only [Matrix.conjTranspose_apply, pathMatrix_pathAt_apply]
  by_cases h1 : x.1 = y.1
  · simp [h1, hAe]
  · have h1' : y.1 ≠ x.1 := Ne.symm h1
    by_cases h2 : x.1.val + 1 = y.1.val
    · have h3 : ¬ y.1.val + 1 = x.1.val := by omega
      simp [h1, h1', h2, h3]
    · by_cases h3 : y.1.val + 1 = x.1.val
      · simp [h1, h1', h2, h3]
      · simp [h1, h1', h2, h3]

theorem matrixImaginaryPart_pathPencil (E : ℝ) {r : ℕ} (ε : Fin r → ℝ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    matrixImaginaryPart (pathPencil E ε (pathAt W r ω)) =
      Matrix.diagonal fun x : Fin r × Fin W => ((ε x.1 : ℝ) : ℂ) := by
  rw [pathPencil, absorptionDiag_eq_I_smul]
  apply matrixImaginaryPart_add_I_smul
  · exact (pathMatrix_pathAt_isHermitian r ω hA).sub
      (by rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        Complex.star_def, Complex.conj_ofReal])
  · exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext; simp)

theorem diagonal_absorption_posSemidef {r : ℕ} (ε : Fin r → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    (Matrix.diagonal fun x : Fin r × Fin W => ((ε x.1 : ℝ) : ℂ)).PosSemidef :=
  Matrix.PosSemidef.diagonal fun x => Complex.zero_le_real.mpr (hε x.1)

theorem layerAbsorption_nonneg (κ : ℝ → ℝ) (hκ : ∀ s, 0 ≤ κ s) (r : ℕ) (i : Fin r) :
    0 ≤ layerAbsorption W κ r i :=
  div_nonneg (hκ _) (sq_nonneg _)

/-- Hypotheses shared by the passive statements: Hermitian blocks, `κ ≥ 0`, `Im z > 0`. -/
structure PassiveSample (b E : ℝ) (κ : ℝ → ℝ) (ω : GrowthPath W) : Prop where
  herm : ∀ k, (ω.1 k).IsHermitian
  absorb : ∀ s, 0 ≤ κ s
  height : 0 < (boundaryZ b E).im

theorem PassiveSample.im_pencil {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) :
    (matrixImaginaryPart (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))).PosSemidef := by
  rw [matrixImaginaryPart_pathPencil E _ ω h.herm]
  exact diagonal_absorption_posSemidef _ (layerAbsorption_nonneg κ h.absorb r)

/-- `z - 𝕏₁₁` is invertible: `Im(z - C_fᴴF⁻¹C_f) = Im z + C_fᴴ(-Im F⁻¹)C_f ≻ 0`. -/
theorem isUnit_farPencil {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) : IsUnit (farPencil b E κ W r ω) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  have hG := neg_im_inv_posSemidef _ (h.im_pencil r)
  have hp : farPencil b E κ W r ω = portPencil ((farCol W r ω)ᴴ *
      (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))⁻¹ * farCol W r ω) (boundaryZ b E) := rfl
  rw [hp, matrixImaginaryPart_portPencil_general,
    matrixImaginaryPart_congruence, sub_eq_add_neg, add_comm, neg_congruence]
  exact Matrix.PosDef.posSemidef_add (hG.conjTranspose_mul_mul_same _)
    (Matrix.PosDef.one.smul h.height)

/-- `Im F̃ ⪰ 0` for the lead-closed pencil `F̃ = F - z⁻¹C_fC_fᴴ`. -/
theorem PassiveSample.im_leadPencil {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) :
    (matrixImaginaryPart (leadPencil b E κ W r ω)).PosSemidef := by
  rw [leadPencil, matrixImaginaryPart_sub,
    matrixImaginaryPart_smul_hermitian _ _ (Matrix.isHermitian_mul_conjTranspose_self _),
    Complex.inv_im, sub_eq_add_neg, ← neg_smul]
  refine (h.im_pencil r).add ((Matrix.posSemidef_self_mul_conjTranspose _).smul ?_)
  rw [Complex.nonneg_iff]
  refine ⟨?_, by simp⟩
  simp only [Complex.neg_re, Complex.ofReal_re, neg_div, neg_neg]
  exact div_nonneg h.height.le (Complex.normSq_nonneg _)

/-- **Passivity along the path**: `Y_r = -Im X_r ⪰ 0` at every length, along every sample
with Hermitian blocks, `κ ≥ 0`, `Im z > 0`. -/
theorem pathNearSchur_passive {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) : (passiveY (pathNearSchur b E κ W r ω)).PosSemidef := by
  by_cases hF : IsUnit (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))
  · obtain ⟨hX, hU⟩ := pathNearSchur_eq_lead b E κ r ω (fun h0 => by
      have := h.height; rw [h0] at this; simp at this) hF (isUnit_farPencil h r)
    rw [passiveY, hX, matrixImaginaryPart_congruence, neg_congruence]
    exact (neg_im_inv_posSemidef _ (h.im_leadPencil r)).conjTranspose_mul_mul_same _
  · have h0 : (pathPencil E (layerAbsorption W κ r) (pathAt W r ω))⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rwa [← Matrix.isUnit_iff_isUnit_det])
    have hX : pathNearSchur b E κ W r ω = 0 := by
      simp only [pathNearSchur, nearSchur, portBlock_absorbedPathSchur, h0, Matrix.mul_zero,
        Matrix.zero_mul, add_zero]
    rw [hX]
    simpa [passiveY, matrixImaginaryPart] using Matrix.PosSemidef.zero

/-!
## Transmission along the path
-/

/-- The scattering matrix of the near port, `S = I - 2iηR`. -/
def passiveS {n : ℕ} (b E : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (2 * Complex.I * (etaZ b E : ℂ)) • passiveResolvent b E X

/-- `T = 4ηR*YR = I - S*S` for **every** matrix `X`. -/
theorem passiveTransmission_eq_one_sub {n : ℕ} (b E : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    passiveTransmission b E X = 1 - (passiveS b E X)ᴴ * passiveS b E X := by
  set K := boundaryZ b E • (1 : Matrix (Fin n) (Fin n) ℂ) - X
  by_cases hK : IsUnit K.det
  · have hbal := passive_scattering_physical K K⁻¹ (passiveY X) (etaZ b E)
      (Matrix.mul_nonsing_inv K hK) (by
        have hp : K = portPencil X (boundaryZ b E) := rfl
        rw [Matrix.star_eq_conjTranspose, matrix_difference_eq_twoI_imaginaryPart, hp,
          matrixImaginaryPart_portPencil_general, passiveY, etaZ]
        ext i j
        simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
          smul_eq_mul, Complex.real_smul]
        ring)
    simp only [Matrix.star_eq_conjTranspose] at hbal
    rw [passiveS, passiveTransmission, passiveQ, passiveResolvent, hbal]
    push_cast; rfl
  · have h0 : passiveResolvent b E X = 0 := Matrix.nonsing_inv_apply_not_isUnit _ hK
    simp [passiveS, passiveTransmission, passiveQ, h0]

/-- `T_r = I - S_rᴴS_r` along the path. -/
theorem pathTransmission_eq_one_sub (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) :
    pathTransmission b E κ W r ω =
      1 - (passiveS b E (pathNearSchur b E κ W r ω))ᴴ * passiveS b E (pathNearSchur b E κ W r ω) :=
  passiveTransmission_eq_one_sub b E _

/-- `T_r ⪯ I`. -/
theorem one_sub_pathTransmission_posSemidef (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) :
    (1 - pathTransmission b E κ W r ω).PosSemidef := by
  rw [pathTransmission_eq_one_sub, sub_sub_cancel]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **`0 ⪯ T_r`** along the path; together with `one_sub_pathTransmission_posSemidef`,
`0 ⪯ T_r ⪯ I`. -/
theorem pathTransmission_posSemidef {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) : (pathTransmission b E κ W r ω).PosSemidef := by
  have hc : (0 : ℂ) ≤ ((4 * etaZ b E : ℝ) : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨by simpa [etaZ] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h.height.le, by simp⟩
  exact ((pathNearSchur_passive h r).conjTranspose_mul_mul_same _).smul hc

/-- The conductance `g_r = Tr T_r ∈ [0, W]`. -/
theorem conductanceOf_pathTransmission_mem {b E : ℝ} {κ : ℝ → ℝ} {ω : GrowthPath W}
    (h : PassiveSample b E κ ω) (r : ℕ) :
    0 ≤ conductanceOf (pathTransmission b E κ W r ω) ∧
      conductanceOf (pathTransmission b E κ W r ω) ≤ W := by
  have h1 := (pathTransmission_posSemidef h r).trace_nonneg
  have h2 := (one_sub_pathTransmission_posSemidef b E κ W r ω).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin] at h2
  constructor
  · exact (Complex.nonneg_iff.mp h1).1
  · have := (Complex.nonneg_iff.mp h2).1
    simp only [Complex.sub_re, Complex.natCast_re] at this
    simp only [conductanceOf]; linarith

end BlockBand.Transmission.Bridge
