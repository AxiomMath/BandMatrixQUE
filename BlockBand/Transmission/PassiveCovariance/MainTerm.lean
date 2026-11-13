module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# The leading tensor of the passive covariance and the ladder summation

* `mainTensor`: the leading term
  `(D₀/2W)[I⊗(I-T) + (I-T)⊗I] + (σ₋/W) f⊗f + (σ̄₋/W) f*⊗f*` exactly as in
  `PassiveCovarianceContract`.
* `ladderTensor`: the six-term ladder sum,
  `σ₊(I⊗R*R + R*R⊗I) - r(R⊗I + I⊗R) - r̄(R*⊗I + I⊗R*) + σ₋R⊗R + σ̄₋R*⊗R* + r₁₂I⊗I`
  with the simplified replica scalars `r = c₀(σ₋-σ₊)`, `r₁₂ = (2σ₊-σ₋-σ̄₋)/(4η²)`.
* **`mainTensor_eq_ladderTensor`**: `W · mainTensor = ladderTensor`, for every `X`
  (it uses only `T = I - S*S`, `S = I - 2iηR`, `σ₊ = 2η²D₀`; no commutation of `R, R*`).
* `norm_mainTensor_le`: `|mainTensor| ≤ C_m W⁻¹ ∏‖v_j‖` uniformly in passive `X`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The leading tensor of the passive covariance, as in `PassiveCovarianceContract`. -/
def mainTensor (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  let T := passiveTransmission b E X
  let f := passiveF b E X
  let I : Matrix (Fin W) (Fin W) ℂ := 1
  (((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
      (crossedTensor v₁ v₂ v₃ v₄ I (I - T) + crossedTensor v₁ v₂ v₃ v₄ (I - T) I) +
    sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ f f +
    conj (sigmaMinus b E s) / W * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ

/-- The replica scalar `r = c₀(σ₋ - σ₊)`. -/
def ladderR (b E : ℝ) (s : ℂ) : ℂ := cZero b E * (sigmaMinus b E s - sigmaPlus b)

/-- The replica scalar `r₁₂ = (2σ₊ - σ₋ - σ̄₋)/(4η²)`. -/
def ladderR12 (b E : ℝ) (s : ℂ) : ℂ :=
  (2 * sigmaPlus b - sigmaMinus b E s - conj (sigmaMinus b E s)) / (4 * (etaZ b E : ℂ) ^ 2)

/-- The six-term sum of the four crossed products of the leading values. -/
def ladderTensor (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin W → ℂ) : ℂ :=
  let R := passiveResolvent b E X
  let I : Matrix (Fin W) (Fin W) ℂ := 1
  let t := crossedTensor v₁ v₂ v₃ v₄
  (sigmaPlus b : ℂ) * (t I (Rᴴ * R) + t (Rᴴ * R) I) - ladderR b E s * (t R I + t I R) -
      conj (ladderR b E s) * (t Rᴴ I + t I Rᴴ) + sigmaMinus b E s * t R R +
    conj (sigmaMinus b E s) * t Rᴴ Rᴴ + ladderR12 b E s * t I I

section Bilinear

variable {n : Type*} [Fintype n]

theorem bilinear_add (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A + B) v = bilinear u A v + bilinear u B v := by
  simp [bilinear, add_mulVec, dotProduct_add]

theorem bilinear_sub (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A - B) v = bilinear u A v - bilinear u B v := by
  simp [bilinear, sub_mulVec, dotProduct_sub]

theorem bilinear_smul (u : n → ℂ) (c : ℂ) (A : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (c • A) v = c * bilinear u A v := by
  simp [bilinear, smul_mulVec, dotProduct_smul]

end Bilinear

/-- `c₀ = -i/(2η)`. -/
theorem cZero_eq (b E : ℝ) :
    cZero b E = -Complex.I / (2 * (etaZ b E : ℂ)) := by
  rw [cZero, inv_eq_iff_eq_inv, inv_div, div_neg, eq_neg_iff_add_eq_zero]
  field_simp
  ring_nf
  rw [Complex.I_sq]; ring

/-- `I - T = S*S = I + 2iηR* - 2iηR + 4η²R*R`. -/
theorem one_sub_transmission_expand (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    1 - passiveTransmission b E X =
      1 + (2 * Complex.I * (etaZ b E : ℂ)) • (passiveResolvent b E X)ᴴ -
        (2 * Complex.I * (etaZ b E : ℂ)) • passiveResolvent b E X +
        (4 * (etaZ b E : ℂ) ^ 2) • ((passiveResolvent b E X)ᴴ * passiveResolvent b E X) := by
  rw [passiveTransmission_eq_one_sub, sub_sub_cancel, passiveS]
  set R := passiveResolvent b E X
  have hc : star (2 * Complex.I * (etaZ b E : ℂ)) = -(2 * Complex.I * (etaZ b E : ℂ)) := by
    simp
  have hcc : -(2 * Complex.I * (etaZ b E : ℂ)) * (2 * Complex.I * (etaZ b E : ℂ)) =
      4 * (etaZ b E : ℂ) ^ 2 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hc, ← hcc]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  module

/-- **The ladder summation**: the six-term ladder sum equals `W` times the leading tensor, for every
old input `X`. -/
theorem mainTensor_eq_ladderTensor {b E : ℝ} (h1 : -2 < E) (h2 : E < 2) (hb0 : 0 < b)
    (hb : b < 1) (hW : W ≠ 0) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    (W : ℂ) * mainTensor b E s X v₁ v₂ v₃ v₄ = ladderTensor b E s X v₁ v₂ v₃ v₄ := by
  have hη := (etaZ_pos b E hb h1 h2).ne'
  have hη' : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hc : conj (ladderR b E s) = -cZero b E * (conj (sigmaMinus b E s) - sigmaPlus b) := by
    rw [ladderR, map_mul, map_sub, conj_cZero, Complex.conj_ofReal]
  simp only [ladderTensor, hc]
  simp only [mainTensor, ladderR, ladderR12, one_sub_transmission_expand,
    passiveF, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, crossedTensor,
    bilinear_add, bilinear_sub, bilinear_smul]
  rw [Complex.star_def, conj_cZero, cZero_eq b E, sigmaPlus_eq b E hb0 h1 h2]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `q = Tr Q ≥ 0` for passive `X`. -/
theorem passiveMass_nonneg {W : ℕ} (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : 0 ≤ passiveMass b E X := by
  have hQ : (passiveQ b E X).PosSemidef := hY.conjTranspose_mul_mul_same _
  exact (Complex.nonneg_iff.mp hQ.trace_nonneg).1

/-- The constant of the crude bound on the leading tensor. -/
def mainConst (b E : ℝ) (s : ℂ) : ℝ :=
  9 * |transportD0 b E| + 2 * ‖sigmaMinus b E s‖ * (3 / (2 * etaZ b E)) ^ 2

/-- **Crude bound on the leading tensor**: `|mainTensor| ≤ C_m W⁻¹∏‖v_j‖` for every
passive `X`. -/
theorem norm_mainTensor_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (s : ℂ) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (v₁ v₂ v₃ v₄ : Fin W → ℂ) :
    ‖mainTensor b E s X v₁ v₂ v₃ v₄‖ ≤ mainConst b E s / W * fourNorm v₁ v₂ v₃ v₄ := by
  have hT := norm_one_sub_transmission_le hb0 hb h1 h2 hY
  have hf := norm_passiveF_le hb0 hb h1 h2 hY
  have hfH : ‖(passiveF b E X)ᴴ‖ ≤ 3 / (2 * etaZ b E) := by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have hI := norm_one_matrix_le (n := Fin W)
  have hF : 0 ≤ fourNorm v₁ v₂ v₃ v₄ := by
    have := vecNorm_nonneg v₁; have := vecNorm_nonneg v₂; have := vecNorm_nonneg v₃
    have := vecNorm_nonneg v₄; rw [fourNorm]; positivity
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  set F := fourNorm v₁ v₂ v₃ v₄
  set c := 3 / (2 * etaZ b E)
  have hc0 : 0 ≤ c := by have := etaZ_pos b E (by linarith) h1 h2; positivity
  have t1 := norm_crossedTensor_le v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X)
  have t2 := norm_crossedTensor_le v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1
  have t3 := norm_crossedTensor_le v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X)
  have t4 := norm_crossedTensor_le v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ
  have n1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ * ‖1 - passiveTransmission b E X‖ ≤ 9 := by
    nlinarith [norm_nonneg (1 : Matrix (Fin W) (Fin W) ℂ), norm_nonneg (1 - passiveTransmission b E X)]
  have n2 : ‖1 - passiveTransmission b E X‖ * ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 9 := by
    nlinarith [norm_nonneg (1 : Matrix (Fin W) (Fin W) ℂ), norm_nonneg (1 - passiveTransmission b E X)]
  have b1 : ‖crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X)‖ ≤ 9 * F :=
    t1.trans (mul_le_mul_of_nonneg_right n1 hF)
  have b2 : ‖crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1‖ ≤ 9 * F :=
    t2.trans (mul_le_mul_of_nonneg_right n2 hF)
  have n3 : ‖passiveF b E X‖ * ‖passiveF b E X‖ ≤ c ^ 2 := by
    rw [pow_two]; exact mul_le_mul hf hf (norm_nonneg _) hc0
  have n4 : ‖(passiveF b E X)ᴴ‖ * ‖(passiveF b E X)ᴴ‖ ≤ c ^ 2 := by
    rw [pow_two]; exact mul_le_mul hfH hfH (norm_nonneg _) hc0
  have b3 : ‖crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X)‖ ≤ c ^ 2 * F :=
    t3.trans (mul_le_mul_of_nonneg_right n3 hF)
  have b4 : ‖crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ‖ ≤ c ^ 2 * F :=
    t4.trans (mul_le_mul_of_nonneg_right n4 hF)
  rcases hW0.lt_or_eq with hWpos | hWz
  · have hD : ‖(((transportD0 b E / (2 * W) : ℝ)) : ℂ)‖ = |transportD0 b E| / (2 * W) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * W)]
    have hs1 : ‖sigmaMinus b E s / W‖ = ‖sigmaMinus b E s‖ / W := by
      rw [norm_div, Complex.norm_natCast]
    have hs2 : ‖conj (sigmaMinus b E s) / W‖ = ‖sigmaMinus b E s‖ / W := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_conj]
    simp only [mainTensor]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul, norm_mul, hD, hs1, hs2, mainConst]
    have e1 := mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add b1 b2))
      (by positivity : 0 ≤ |transportD0 b E| / (2 * W))
    have e2 := mul_le_mul_of_nonneg_left b3 (by positivity : 0 ≤ ‖sigmaMinus b E s‖ / W)
    have e3 := mul_le_mul_of_nonneg_left b4 (by positivity : 0 ≤ ‖sigmaMinus b E s‖ / W)
    have : |transportD0 b E| / (2 * W) * (9 * F + 9 * F) + ‖sigmaMinus b E s‖ / W * (c ^ 2 * F) +
        ‖sigmaMinus b E s‖ / W * (c ^ 2 * F) =
        (9 * |transportD0 b E| + 2 * ‖sigmaMinus b E s‖ * c ^ 2) / W * F := by
      field_simp; ring
    linarith
  · have hW' : W = 0 := by exact_mod_cast hWz.symm
    subst hW'
    have hv : ∀ v : Fin 0 → ℂ, vecNorm v = 0 := fun v => by simp [vecNorm]
    have hb : ∀ (u v : Fin 0 → ℂ) (M : Matrix (Fin 0) (Fin 0) ℂ), bilinear u M v = 0 :=
      fun u v M => by simp [bilinear]
    simp [mainTensor, crossedTensor, hb]

end BlockBand.Transmission.PassiveCovariance
