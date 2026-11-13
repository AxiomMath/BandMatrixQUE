module

public import BlockBand.Transmission.PassiveCovariance.MainTerm

/-!
# Exact passive partial fractions and the first scalar word

For a passive old input (`Y = -Im X ⪰ 0`), `R = (z - X)⁻¹`, `Q = R*YR`, `Q̃ = RYR*`,
`c₀ = (2iη)⁻¹`:

* `adj_mul_resolvent`: `R*R = c₀(R* - R) - Q/η` (exact);
* `resolvent_mul_adj`: `RR* = c₀(R* - R) - Q̃/η` (exact);
* `trace_tildeQ`: `Tr Q̃ = Tr Q = q`;
* `cZero_mul_conj_sub`: `c₀(ā - a) = d_*`;
* `normTrace_RRstar_sub_dStar_le`: `|⟨RR*⟩ - d_*| ≤ (δ₀ + q/W)/η` (`⟨·⟩ = W⁻¹Tr`).

No commutation of `R` and `R*` is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ} {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)

/-- `K - K* = 2iη + 2iY` for `K = z - X`. -/
theorem nearPencil_balance (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) -
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)ᴴ =
      (2 * Complex.I * (etaZ b E : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ) +
        (2 * Complex.I) • passiveY X := by
  rw [matrix_difference_eq_twoI_imaginaryPart, matrixImaginaryPart_nearPencil,
    ← Complex.coe_smul, smul_add, smul_smul, add_comm]

include hb0 hb h1 h2 hY

theorem nearPencil_inverse :
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * passiveResolvent b E X = 1 ∧
      passiveResolvent b E X * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 := by
  have h := passive_inverse_constructed _ _ (etaZ_pos b E (by linarith) h1 h2) hY
    (matrixImaginaryPart_nearPencil b E X)
  exact ⟨h.2.1, h.2.2⟩

/-- `R*R = c₀(R* - R) - Q/η`. -/
theorem adj_mul_resolvent :
    (passiveResolvent b E X)ᴴ * passiveResolvent b E X =
      cZero b E • ((passiveResolvent b E X)ᴴ - passiveResolvent b E X) -
        ((etaZ b E : ℂ)⁻¹) • passiveQ b E X := by
  have hη : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast (etaZ_pos b E (by linarith) h1 h2).ne'
  have hbal := passive_inverse_balance _ (passiveResolvent b E X) (passiveY X) _ _
    (nearPencil_inverse hb0 hb h1 h2 hY).1 (nearPencil_balance b E X)
  simp only [Matrix.star_eq_conjTranspose] at hbal
  rw [hbal, passiveQ, cZero, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (by simp [hη]),
    one_smul]
  have : (2 * Complex.I * (etaZ b E : ℂ))⁻¹ * (2 * Complex.I) = (etaZ b E : ℂ)⁻¹ := by
    field_simp
  rw [this]; abel

/-- `RR* = c₀(R* - R) - Q̃/η`, `Q̃ = RYR*`. -/
theorem resolvent_mul_adj :
    passiveResolvent b E X * (passiveResolvent b E X)ᴴ =
      cZero b E • ((passiveResolvent b E X)ᴴ - passiveResolvent b E X) -
        ((etaZ b E : ℂ)⁻¹) •
          (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ) := by
  have hη : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast (etaZ_pos b E (by linarith) h1 h2).ne'
  set R := passiveResolvent b E X
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hinv := nearPencil_inverse hb0 hb h1 h2 hY
  have hRK : R * K = 1 := hinv.2
  have hKR' : Kᴴ * Rᴴ = 1 := by rw [← conjTranspose_mul, hRK, conjTranspose_one]
  have hdiff : Rᴴ - R = R * (K - Kᴴ) * Rᴴ := by
    rw [mul_sub, sub_mul, hRK, one_mul, mul_assoc, hKR', mul_one]
  rw [nearPencil_balance b E X] at hdiff
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one] at hdiff
  rw [hdiff, cZero, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ (by simp [hη]), one_smul]
  have : (2 * Complex.I * (etaZ b E : ℂ))⁻¹ * (2 * Complex.I) = (etaZ b E : ℂ)⁻¹ := by
    field_simp
  rw [this]; abel

/-- `Tr Q̃ = Tr Q` (both have trace `q`; it follows from the two exact identities
and `Tr R*R = Tr RR*`, although `Q ≠ Q̃` for nonnormal `R`). -/
theorem trace_tildeQ :
    (passiveResolvent b E X * passiveY X * (passiveResolvent b E X)ᴴ).trace =
      (passiveQ b E X).trace := by
  have hη : (etaZ b E : ℂ)⁻¹ ≠ 0 := by
    simpa using (etaZ_pos b E (by linarith) h1 h2).ne'
  have hc := trace_mul_comm (passiveResolvent b E X)ᴴ (passiveResolvent b E X)
  rw [adj_mul_resolvent hb0 hb h1 h2 hY, resolvent_mul_adj hb0 hb h1 h2 hY] at hc
  simp only [trace_sub, trace_smul, smul_eq_mul, sub_right_inj] at hc
  exact (mul_left_cancel₀ hη hc).symm

omit hY in
/-- `c₀(ā - a) = d_*` (the value of `⟨RR*⟩` at the matched point). -/
theorem cZero_mul_conj_sub : cZero b E * (conj (matchedA E) - matchedA E) = (dStar b : ℂ) := by
  have hη := etaZ_eq b E h1 h2
  have hy := matchedA_im_neg E h1 h2
  have hsub : conj (matchedA E) - matchedA E = -2 * Complex.I * ((matchedA E).im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have h1b : (1 - b : ℂ) ≠ 0 := by
    have : (1 - b : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have hyc : ((matchedA E).im : ℂ) ≠ 0 := by exact_mod_cast hy.ne
  rw [hsub, cZero, hη, dStar]
  push_cast
  field_simp

/-- **The first scalar word**: `|⟨RR*⟩ - d_*| ≤ (δ₀ + q/W)/η`. -/
theorem normTrace_RRstar_sub_dStar_le (hW : W ≠ 0) :
    ‖(W : ℂ)⁻¹ * (passiveResolvent b E X * (passiveResolvent b E X)ᴴ).trace - dStar b‖ ≤
      (jetDistance0 b E X + passiveMass b E X / W) / etaZ b E := by
  have hηpos := etaZ_pos b E (by linarith) h1 h2
  have hη : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hηpos.ne'
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hq : (passiveQ b E X).trace = ((passiveMass b E X : ℝ) : ℂ) := by
    have hQ : (passiveQ b E X).PosSemidef := hY.conjTranspose_mul_mul_same _
    apply Complex.ext
    · rfl
    · simp [(Complex.nonneg_iff.mp hQ.trace_nonneg).2.symm]
  set m := (W : ℂ)⁻¹ * (passiveResolvent b E X).trace with hmdef
  have hm : conj m = (W : ℂ)⁻¹ * star (passiveResolvent b E X).trace := by
    rw [hmdef, map_mul, map_inv₀, Complex.conj_natCast]; rfl
  have key : (W : ℂ)⁻¹ * (passiveResolvent b E X * (passiveResolvent b E X)ᴴ).trace - dStar b =
      cZero b E * ((conj m - conj (matchedA E)) - (m - matchedA E)) -
        (etaZ b E : ℂ)⁻¹ * ((passiveMass b E X : ℂ) / W) := by
    rw [resolvent_mul_adj hb0 hb h1 h2 hY, trace_sub, trace_smul, trace_smul, trace_sub,
      trace_tildeQ hb0 hb h1 h2 hY, hq, ← cZero_mul_conj_sub hb0 hb h1 h2, hm, hmdef,
      trace_conjTranspose]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [key]
  refine (norm_sub_le _ _).trans ?_
  have hc := norm_cZero b E hηpos
  have hδ : ‖conj m - conj (matchedA E) - (m - matchedA E)‖ ≤ 2 * jetDistance0 b E X := by
    refine (norm_sub_le _ _).trans ?_
    rw [← map_sub, Complex.norm_conj]
    simp only [jetDistance0]
    linarith
  rw [norm_mul, norm_mul, hc, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos,
    norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (passiveMass_nonneg b E hY)]
  have hδ' := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ (2 * etaZ b E)⁻¹)
  have e1 : (2 * etaZ b E)⁻¹ * (2 * jetDistance0 b E X) = jetDistance0 b E X / etaZ b E := by
    field_simp
  have e2 : (etaZ b E)⁻¹ * (passiveMass b E X / W) = passiveMass b E X / W / etaZ b E := by
    ring
  rw [add_div]
  linarith

end BlockBand.Transmission.PassiveCovariance
