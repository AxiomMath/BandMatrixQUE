module

public import BlockBand.External.CEH.SourceStatement

/-!
# CEH: deterministic resolvent facts

Deterministic identities and bounds for the resolvent `R(w) = (H - w)⁻¹` of a Hermitian matrix.
Conventions are those of `BlockBand.External.CEH`: `normalizedTrace A = N⁻¹ tr A`,
`imaginaryPart A = (2i)⁻¹ (A - Aᴴ)`, `sourceVectorNorm` is the Euclidean norm and
`sourceMatrixElement A x y = x* A y`. The matrix norm is the `ℓ²` operator norm.

* Invertibility, adjoint `Rᴴ = R(w̄)`, the resolvent identity, the Ward identities
  `Im R = (Im w) R Rᴴ = (Im w) Rᴴ R`, `⟨R Rᴴ⟩ = ⟨Im R⟩ / Im w`, the bound
  `‖R‖ ≤ |Im w|⁻¹`, and positivity of `(Im w) Im R`.
* Cauchy–Schwarz bounds for quadratic forms and normalized traces of products of
  resolvents, and the exact quadratic-variation identities used for the Itô equations of
  `⟨G B⟩` and `G_xy`.

No probability, measure or asymptotic statement appears here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Phase1

open Matrix
open BlockBand.External.CEH
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
## Generic vector and trace facts
-/

/-- The resolvent `(H - w)⁻¹`, with total matrix inverse. -/
def resolvent (H : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (H - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- `sourceResolvent` is the resolvent of the deformed matrix. -/
theorem sourceResolvent_eq_resolvent (lambda : ℝ) (H0 W : SourceHermitian N) (z : ℂ) :
    sourceResolvent lambda H0 W z = resolvent (deformedMatrix lambda H0 W) z := rfl

theorem sourceVectorNorm_nonneg (v : Fin N → ℂ) : 0 ≤ sourceVectorNorm v :=
  Real.sqrt_nonneg _

theorem sourceVectorNorm_sq (v : Fin N → ℂ) : sourceVectorNorm v ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

/-- `sourceVectorNorm` is the Euclidean norm. -/
theorem norm_toLp_eq_sourceVectorNorm (v : Fin N → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ = sourceVectorNorm v := by
  rw [EuclideanSpace.norm_eq]
  rfl

theorem sourceVectorNorm_eq_zero_iff (v : Fin N → ℂ) : sourceVectorNorm v = 0 ↔ v = 0 := by
  rw [← norm_toLp_eq_sourceVectorNorm, norm_eq_zero]
  constructor
  · intro h
    simpa using congrArg WithLp.ofLp h
  · rintro rfl
    rfl

theorem star_dotProduct_self (v : Fin N → ℂ) :
    star v ⬝ᵥ v = ((sourceVectorNorm v ^ 2 : ℝ) : ℂ) := by
  rw [sourceVectorNorm_sq]
  simp [dotProduct, Complex.conj_mul']

/-- Cauchy–Schwarz for the sesquilinear dot product. -/
theorem norm_star_dotProduct_le (x y : Fin N → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ sourceVectorNorm x * sourceVectorNorm y := by
  calc ‖star x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
        unfold dotProduct
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- `x* A y = (Aᴴ x)* y`. -/
theorem sourceMatrixElement_eq_adjoint (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    sourceMatrixElement A x y = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  simp [sourceMatrixElement, star_mulVec, dotProduct_mulVec]

/-- `y* Aᴴ A y = ‖A y‖²`. -/
theorem sourceMatrixElement_conjTranspose_mul_self (A : Matrix (Fin N) (Fin N) ℂ)
    (y : Fin N → ℂ) :
    sourceMatrixElement (Aᴴ * A) y y = ((sourceVectorNorm (A *ᵥ y) ^ 2 : ℝ) : ℂ) := by
  rw [← star_dotProduct_self, sourceMatrixElement, ← mulVec_mulVec, dotProduct_mulVec,
    star_mulVec]

/-- `x* A Aᴴ x = ‖Aᴴ x‖²`. -/
theorem sourceMatrixElement_mul_conjTranspose_self (A : Matrix (Fin N) (Fin N) ℂ)
    (x : Fin N → ℂ) :
    sourceMatrixElement (A * Aᴴ) x x = ((sourceVectorNorm (Aᴴ *ᵥ x) ^ 2 : ℝ) : ℂ) := by
  simpa using sourceMatrixElement_conjTranspose_mul_self Aᴴ x

/-- Cauchy–Schwarz for a product: `|x* A B y| ≤ ‖Aᴴ x‖ ‖B y‖`. -/
theorem norm_sourceMatrixElement_mul_le (A B : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    ‖sourceMatrixElement (A * B) x y‖ ≤
      sourceVectorNorm (Aᴴ *ᵥ x) * sourceVectorNorm (B *ᵥ y) := by
  have : sourceMatrixElement (A * B) x y = star (Aᴴ *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
    rw [sourceMatrixElement, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  rw [this]
  exact norm_star_dotProduct_le _ _

/-- Normalized trace is additive. -/
theorem normalizedTrace_add (A B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (A + B) = normalizedTrace A + normalizedTrace B := by
  simp [normalizedTrace, trace_add, mul_add]

theorem normalizedTrace_sub (A B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (A - B) = normalizedTrace A - normalizedTrace B := by
  simp [normalizedTrace, trace_sub, mul_sub]

theorem normalizedTrace_smul (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (c • A) = c * normalizedTrace A := by
  simp [normalizedTrace, trace_smul]
  ring

theorem normalizedTrace_mul_comm (A B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (A * B) = normalizedTrace (B * A) := by
  rw [normalizedTrace, normalizedTrace, trace_mul_comm]

theorem normalizedTrace_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace Aᴴ = starRingEnd ℂ (normalizedTrace A) := by
  simp [normalizedTrace, trace_conjTranspose]

/-- `tr (A Aᴴ) = ∑ |A_ij|²`. -/
theorem trace_mul_conjTranspose_self_eq (A : Matrix (Fin N) (Fin N) ℂ) :
    (A * Aᴴ).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  simp [trace, mul_apply, Complex.mul_conj']

/-- `tr (Aᴴ A) = ∑ |A_ij|²`. -/
theorem trace_conjTranspose_mul_self_eq (A : Matrix (Fin N) (Fin N) ℂ) :
    (Aᴴ * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_mul_comm, trace_mul_conjTranspose_self_eq]

/-- The normalized trace of `A Aᴴ` is real and nonnegative. -/
theorem normalizedTrace_mul_conjTranspose_self (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (A * Aᴴ) = (((N : ℝ)⁻¹ * ∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [normalizedTrace, trace_mul_conjTranspose_self_eq]
  push_cast
  rfl

theorem normalizedTrace_mul_conjTranspose_self_re_nonneg (A : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (normalizedTrace (A * Aᴴ)).re := by
  rw [normalizedTrace_mul_conjTranspose_self, Complex.ofReal_re]
  positivity

theorem normalizedTrace_mul_conjTranspose_self_im (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace (A * Aᴴ)).im = 0 := by
  rw [normalizedTrace_mul_conjTranspose_self, Complex.ofReal_im]

/-- The normalized trace of the matrix imaginary part is the imaginary part of the normalized
trace. -/
theorem normalizedTrace_imaginaryPart (A : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (External.CEH.imaginaryPart A) = (((normalizedTrace A).im : ℝ) : ℂ) := by
  rw [External.CEH.imaginaryPart, normalizedTrace_smul, normalizedTrace_sub,
    normalizedTrace_conjTranspose, Complex.sub_conj]
  push_cast
  field_simp

/-!
## Resolvent basics
-/

section Resolvent

variable {H : Matrix (Fin N) (Fin N) ℂ}

/-- Lower bound `|Im w| ‖v‖ ≤ ‖(H - w) v‖` for Hermitian `H` (no condition on `w`). -/
theorem abs_im_mul_sourceVectorNorm_le (hH : H.IsHermitian) (w : ℂ) (v : Fin N → ℂ) :
    |w.im| * sourceVectorNorm v ≤
      sourceVectorNorm ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) := by
  set q := star v ⬝ᵥ ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) with hq
  have hq' : q = star v ⬝ᵥ (H *ᵥ v) - w * ((sourceVectorNorm v ^ 2 : ℝ) : ℂ) := by
    rw [hq, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
      star_dotProduct_self, smul_eq_mul]
  have him : q.im = -(w.im * sourceVectorNorm v ^ 2) := by
    have h0 := hH.im_star_dotProduct_mulVec_self v
    simp only [RCLike.im_to_complex] at h0
    rw [hq', Complex.sub_im, h0, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hle : |w.im| * sourceVectorNorm v ^ 2 ≤
      sourceVectorNorm v * sourceVectorNorm ((H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ v) := by
    calc |w.im| * sourceVectorNorm v ^ 2 = |q.im| := by
          rw [him, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (sourceVectorNorm v))]
      _ ≤ ‖q‖ := Complex.abs_im_le_norm q
      _ ≤ _ := norm_star_dotProduct_le _ _
  rcases (sourceVectorNorm_nonneg v).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact sourceVectorNorm_nonneg _
  · nlinarith

variable {w : ℂ}

theorem isUnit_det_sub_smul (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    IsUnit (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have h := abs_im_mul_sourceVectorNorm_le hH w v
  rw [hAv, show sourceVectorNorm (0 : Fin N → ℂ) = 0 by simp [sourceVectorNorm]] at h
  have h0 : sourceVectorNorm v = 0 := by
    have := sourceVectorNorm_nonneg v
    have hpos : 0 < |w.im| := abs_pos.mpr hw
    nlinarith
  exact hv ((sourceVectorNorm_eq_zero_iff v).mp h0)

theorem isUnit_sub_smul (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    IsUnit (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
  (isUnit_iff_isUnit_det _).mpr (isUnit_det_sub_smul hH hw)

theorem sub_smul_mul_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) * resolvent H w = 1 :=
  mul_nonsing_inv _ (isUnit_det_sub_smul hH hw)

theorem resolvent_mul_sub_smul (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    resolvent H w * (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 :=
  nonsing_inv_mul _ (isUnit_det_sub_smul hH hw)

theorem isUnit_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) : IsUnit (resolvent H w) :=
  (isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det _ (isUnit_det_sub_smul hH hw))

/-- `Rᴴ = R(w̄)`. -/
theorem resolvent_conjTranspose (hH : H.IsHermitian) (w : ℂ) :
    (resolvent H w)ᴴ = resolvent H (starRingEnd ℂ w) := by
  rw [resolvent, resolvent, conjTranspose_nonsing_inv, conjTranspose_sub, hH.eq,
    conjTranspose_smul, conjTranspose_one, Complex.star_def]

/-- Abstract second resolvent identity. -/
theorem nonsing_inv_sub_nonsing_inv {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUnit A.det)
    (hB : IsUnit B.det) : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  rw [mul_sub, sub_mul, nonsing_inv_mul _ hA, one_mul, mul_assoc, mul_nonsing_inv _ hB,
    mul_one]

/-- The resolvent identity `R(w) - R(w') = (w - w') R(w) R(w')`. -/
theorem resolvent_sub_resolvent (hH : H.IsHermitian) {w' : ℂ} (hw : w.im ≠ 0)
    (hw' : w'.im ≠ 0) :
    resolvent H w - resolvent H w' = (w - w') • (resolvent H w * resolvent H w') := by
  rw [resolvent, resolvent,
    nonsing_inv_sub_nonsing_inv (isUnit_det_sub_smul hH hw) (isUnit_det_sub_smul hH hw'),
    show H - w' • (1 : Matrix (Fin N) (Fin N) ℂ) - (H - w • 1) = (w - w') • 1 by
      rw [sub_smul]; abel,
    Matrix.mul_smul, mul_one, smul_mul]

/-- The resolvent identity in the other order, `R(w) - R(w') = (w - w') R(w') R(w)`. -/
theorem resolvent_sub_resolvent' (hH : H.IsHermitian) {w' : ℂ} (hw : w.im ≠ 0)
    (hw' : w'.im ≠ 0) :
    resolvent H w - resolvent H w' = (w - w') • (resolvent H w' * resolvent H w) := by
  have := resolvent_sub_resolvent hH hw' hw
  rw [← neg_sub, this, ← neg_smul, neg_sub]

theorem resolvent_commute (hH : H.IsHermitian) {w' : ℂ} (hw : w.im ≠ 0) (hw' : w'.im ≠ 0) :
    resolvent H w * resolvent H w' = resolvent H w' * resolvent H w := by
  by_cases h : w = w'
  · rw [h]
  · have h1 := resolvent_sub_resolvent hH hw hw'
    rw [resolvent_sub_resolvent' hH hw hw'] at h1
    exact (smul_right_injective _ (sub_ne_zero.mpr h) h1).symm

theorem resolvent_mul_conjTranspose_comm (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    resolvent H w * (resolvent H w)ᴴ = (resolvent H w)ᴴ * resolvent H w := by
  rw [resolvent_conjTranspose hH]
  exact resolvent_commute hH hw (by simpa using hw)

/-- Ward identity `Im R = (Im w) R Rᴴ`. -/
theorem imaginaryPart_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    External.CEH.imaginaryPart (resolvent H w) =
      (w.im : ℂ) • (resolvent H w * (resolvent H w)ᴴ) := by
  rw [External.CEH.imaginaryPart, resolvent_conjTranspose hH,
    resolvent_sub_resolvent hH hw (by simpa using hw), smul_smul, Complex.sub_conj]
  congr 1
  push_cast
  field_simp

/-- Ward identity `Im R = (Im w) Rᴴ R`. -/
theorem imaginaryPart_resolvent' (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    External.CEH.imaginaryPart (resolvent H w) =
      (w.im : ℂ) • ((resolvent H w)ᴴ * resolvent H w) := by
  rw [imaginaryPart_resolvent hH hw, resolvent_mul_conjTranspose_comm hH hw]

/-- `R Rᴴ = (Im w)⁻¹ Im R`. -/
theorem resolvent_mul_conjTranspose (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    resolvent H w * (resolvent H w)ᴴ = (w.im : ℂ)⁻¹ • External.CEH.imaginaryPart (resolvent H w) := by
  rw [imaginaryPart_resolvent hH hw, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hw),
    one_smul]

/-- `Rᴴ R = (Im w)⁻¹ Im R`. -/
theorem conjTranspose_mul_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    (resolvent H w)ᴴ * resolvent H w = (w.im : ℂ)⁻¹ • External.CEH.imaginaryPart (resolvent H w) := by
  rw [← resolvent_mul_conjTranspose_comm hH hw, resolvent_mul_conjTranspose hH hw]

/-- Averaged Ward identity `⟨R Rᴴ⟩ = ⟨Im R⟩ / Im w`. -/
theorem normalizedTrace_resolvent_mul_conjTranspose (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    normalizedTrace (resolvent H w * (resolvent H w)ᴴ) =
      normalizedTrace (External.CEH.imaginaryPart (resolvent H w)) / w.im := by
  rw [resolvent_mul_conjTranspose hH hw, normalizedTrace_smul, div_eq_inv_mul]

/-- The real form: `⟨R Rᴴ⟩ = Im⟨R⟩ / Im w`, a nonnegative real number. -/
theorem normalizedTrace_resolvent_mul_conjTranspose_eq_real (hH : H.IsHermitian)
    (hw : w.im ≠ 0) :
    normalizedTrace (resolvent H w * (resolvent H w)ᴴ) =
      (((normalizedTrace (resolvent H w)).im / w.im : ℝ) : ℂ) := by
  rw [normalizedTrace_resolvent_mul_conjTranspose hH hw, normalizedTrace_imaginaryPart]
  push_cast
  rfl

/-- `Im⟨R⟩ / Im w ≥ 0`: `Im⟨R⟩` has the sign of `Im w`. -/
theorem im_normalizedTrace_resolvent_div_nonneg (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    0 ≤ (normalizedTrace (resolvent H w)).im / w.im := by
  have := normalizedTrace_mul_conjTranspose_self_re_nonneg (resolvent H w)
  rwa [normalizedTrace_resolvent_mul_conjTranspose_eq_real hH hw, Complex.ofReal_re] at this

theorem im_mul_im_normalizedTrace_resolvent_nonneg (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    0 ≤ w.im * (normalizedTrace (resolvent H w)).im := by
  have h := im_normalizedTrace_resolvent_div_nonneg hH hw
  have : w.im * (normalizedTrace (resolvent H w)).im =
      w.im ^ 2 * ((normalizedTrace (resolvent H w)).im / w.im) := by
    field_simp
  rw [this]
  positivity

/-- `(Im w) Im R = (Im w)² R Rᴴ` is positive definite (for every `N`, vacuously at `N = 0`). -/
theorem posDef_im_smul_imaginaryPart_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    ((w.im : ℂ) • External.CEH.imaginaryPart (resolvent H w)).PosDef := by
  rw [imaginaryPart_resolvent hH hw, smul_smul]
  have hR : (resolvent H w * (resolvent H w)ᴴ).PosDef :=
    PosDef.mul_conjTranspose_self _
      (vecMul_injective_iff_isUnit.mpr (isUnit_resolvent hH hw))
  refine hR.smul ?_
  have : (0 : ℝ) < w.im * w.im := mul_self_pos.mpr hw
  exact_mod_cast this

theorem posSemidef_im_smul_imaginaryPart_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    ((w.im : ℂ) • External.CEH.imaginaryPart (resolvent H w)).PosSemidef :=
  (posDef_im_smul_imaginaryPart_resolvent hH hw).posSemidef

/-- Vector resolvent bound `‖R u‖ ≤ |Im w|⁻¹ ‖u‖`. -/
theorem sourceVectorNorm_resolvent_mulVec_le (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (u : Fin N → ℂ) :
    sourceVectorNorm (resolvent H w *ᵥ u) ≤ |w.im|⁻¹ * sourceVectorNorm u := by
  have h := abs_im_mul_sourceVectorNorm_le hH w (resolvent H w *ᵥ u)
  rw [mulVec_mulVec, sub_smul_mul_resolvent hH hw, one_mulVec] at h
  have hpos : 0 < |w.im| := abs_pos.mpr hw
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- The same bound for `Rᴴ`. -/
theorem sourceVectorNorm_resolvent_conjTranspose_mulVec_le (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (u : Fin N → ℂ) :
    sourceVectorNorm ((resolvent H w)ᴴ *ᵥ u) ≤ |w.im|⁻¹ * sourceVectorNorm u := by
  rw [resolvent_conjTranspose hH]
  simpa using sourceVectorNorm_resolvent_mulVec_le hH (w := starRingEnd ℂ w)
    (by simpa using hw) u

/-- Operator-norm resolvent bound `‖R‖ ≤ |Im w|⁻¹` (`ℓ²` operator norm). -/
theorem norm_resolvent_le (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    ‖resolvent H w‖ ≤ |w.im|⁻¹ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h := sourceVectorNorm_resolvent_mulVec_le hH hw (WithLp.ofLp x)
  rw [← norm_toLp_eq_sourceVectorNorm, ← norm_toLp_eq_sourceVectorNorm] at h
  exact h

end Resolvent

/-!
## Quadratic-form, trace and quadratic-variation bounds
-/

theorem sourceMatrixElement_smul (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    sourceMatrixElement (c • A) x y = c * sourceMatrixElement A x y := by
  simp [sourceMatrixElement, smul_mulVec, dotProduct_smul]

/-- `ℓ²` operator-norm bound on vectors: `‖B v‖ ≤ ‖B‖ ‖v‖`. -/
theorem sourceVectorNorm_mulVec_le (B : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    sourceVectorNorm (B *ᵥ v) ≤ ‖B‖ * sourceVectorNorm v := by
  have h := Matrix.l2_opNorm_mulVec B (WithLp.toLp 2 v)
  rw [← norm_toLp_eq_sourceVectorNorm, ← norm_toLp_eq_sourceVectorNorm]
  exact h

/-- Cauchy–Schwarz for a sandwiched product: `|x* A B C y| ≤ ‖B‖ ‖Aᴴ x‖ ‖C y‖`. -/
theorem norm_sourceMatrixElement_mul_mul_le (A B C : Matrix (Fin N) (Fin N) ℂ)
    (x y : Fin N → ℂ) :
    ‖sourceMatrixElement (A * B * C) x y‖ ≤
      ‖B‖ * sourceVectorNorm (Aᴴ *ᵥ x) * sourceVectorNorm (C *ᵥ y) := by
  rw [Matrix.mul_assoc]
  refine (norm_sourceMatrixElement_mul_le A (B * C) x y).trans ?_
  rw [← mulVec_mulVec]
  calc sourceVectorNorm (Aᴴ *ᵥ x) * sourceVectorNorm (B *ᵥ C *ᵥ y)
      ≤ sourceVectorNorm (Aᴴ *ᵥ x) * (‖B‖ * sourceVectorNorm (C *ᵥ y)) :=
        mul_le_mul_of_nonneg_left (sourceVectorNorm_mulVec_le _ _) (sourceVectorNorm_nonneg _)
    _ = _ := by ring

theorem re_normalizedTrace (A : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace A).re = (N : ℝ)⁻¹ * (A.trace).re := by
  rw [normalizedTrace, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

/-- Cauchy–Schwarz for normalized traces: `|⟨X Y⟩| ≤ √⟨X Xᴴ⟩ √⟨Yᴴ Y⟩`. -/
theorem norm_normalizedTrace_mul_le (X Y : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (X * Y)‖ ≤
      Real.sqrt (normalizedTrace (X * Xᴴ)).re * Real.sqrt (normalizedTrace (Yᴴ * Y)).re := by
  have hY : Yᴴ * Y = Yᴴ * Yᴴᴴ := by rw [conjTranspose_conjTranspose]
  rw [hY, normalizedTrace_mul_conjTranspose_self, normalizedTrace_mul_conjTranspose_self,
    Complex.ofReal_re, Complex.ofReal_re]
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have hS : ∀ Z : Matrix (Fin N) (Fin N) ℂ,
      ∑ i, ∑ j, ‖Z i j‖ ^ 2 = ∑ p : Fin N × Fin N, ‖Z p.1 p.2‖ ^ 2 := fun Z =>
    (Fintype.sum_prod_type' (fun i j => ‖Z i j‖ ^ 2)).symm
  have htr : ‖(X * Y).trace‖ ≤ Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) *
      Real.sqrt (∑ i, ∑ j, ‖Yᴴ i j‖ ^ 2) := by
    rw [hS X, hS Yᴴ]
    calc ‖(X * Y).trace‖ = ‖∑ p : Fin N × Fin N, X p.1 p.2 * Y p.2 p.1‖ := by
          rw [Fintype.sum_prod_type]
          simp [trace, mul_apply]
      _ ≤ ∑ p : Fin N × Fin N, ‖X p.1 p.2‖ * ‖Yᴴ p.1 p.2‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN, normalizedTrace, norm_mul, norm_inv,
    Complex.norm_natCast]
  have hsq : (N : ℝ)⁻¹ = Real.sqrt (N : ℝ)⁻¹ * Real.sqrt (N : ℝ)⁻¹ :=
    (Real.mul_self_sqrt hN).symm
  calc (N : ℝ)⁻¹ * ‖(X * Y).trace‖ ≤ (N : ℝ)⁻¹ * (Real.sqrt (∑ i, ∑ j, ‖X i j‖ ^ 2) *
      Real.sqrt (∑ i, ∑ j, ‖Yᴴ i j‖ ^ 2)) := mul_le_mul_of_nonneg_left htr hN
    _ = _ := by nth_rewrite 1 [hsq]; ring

/-- Column bound: if `‖A v‖ ≤ c ‖v‖` for all `v`, then `tr((A X)ᴴ (A X)) ≤ c² tr(Xᴴ X)`. -/
theorem re_trace_conjTranspose_mul_self_mul_le (A X : Matrix (Fin N) (Fin N) ℂ) {c : ℝ}
    (hA : ∀ v, sourceVectorNorm (A *ᵥ v) ≤ c * sourceVectorNorm v) :
    (((A * X)ᴴ * (A * X)).trace).re ≤ c ^ 2 * ((Xᴴ * X).trace).re := by
  rw [trace_conjTranspose_mul_self_eq, trace_conjTranspose_mul_self_eq, Complex.ofReal_re,
    Complex.ofReal_re, Finset.sum_comm, Finset.sum_comm (f := fun i j => ‖X i j‖ ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hcol : (fun i => (A * X) i j) = A *ᵥ (fun i => X i j) := by
    ext i
    simp [mul_apply, mulVec, dotProduct]
  have h1 := hA (fun i => X i j)
  rw [← hcol] at h1
  have h2 := pow_le_pow_left₀ (sourceVectorNorm_nonneg _) h1 2
  rw [mul_pow, sourceVectorNorm_sq, sourceVectorNorm_sq] at h2
  exact h2

section ResolventBounds

variable {H : Matrix (Fin N) (Fin N) ℂ} {w : ℂ}

/-- Vector Ward identity: `Re (y* Im R y) = Im w · ‖R y‖²`. -/
theorem re_sourceMatrixElement_imaginaryPart_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (y : Fin N → ℂ) :
    (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re =
      w.im * sourceVectorNorm (resolvent H w *ᵥ y) ^ 2 := by
  rw [imaginaryPart_resolvent' hH hw, sourceMatrixElement_smul,
    sourceMatrixElement_conjTranspose_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Vector Ward identity for the adjoint: `Re (x* Im R x) = Im w · ‖Rᴴ x‖²`. -/
theorem re_sourceMatrixElement_imaginaryPart_resolvent' (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (x : Fin N → ℂ) :
    (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re =
      w.im * sourceVectorNorm ((resolvent H w)ᴴ *ᵥ x) ^ 2 := by
  rw [imaginaryPart_resolvent hH hw, sourceMatrixElement_smul,
    sourceMatrixElement_mul_conjTranspose_self, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem sourceVectorNorm_resolvent_mulVec_sq (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (y : Fin N → ℂ) :
    sourceVectorNorm (resolvent H w *ᵥ y) ^ 2 =
      |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re| / |w.im| := by
  rw [re_sourceMatrixElement_imaginaryPart_resolvent hH hw, abs_mul,
    abs_of_nonneg (sq_nonneg (sourceVectorNorm (resolvent H w *ᵥ y)))]
  field_simp

theorem sourceVectorNorm_resolvent_conjTranspose_mulVec_sq (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (x : Fin N → ℂ) :
    sourceVectorNorm ((resolvent H w)ᴴ *ᵥ x) ^ 2 =
      |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re| / |w.im| := by
  rw [re_sourceMatrixElement_imaginaryPart_resolvent' hH hw, abs_mul,
    abs_of_nonneg (sq_nonneg (sourceVectorNorm ((resolvent H w)ᴴ *ᵥ x)))]
  field_simp

private theorem sqrt_div_mul_sqrt_div {a b c : ℝ} (hc : 0 < c) :
    Real.sqrt (a / c) * Real.sqrt (b / c) = c⁻¹ * Real.sqrt a * Real.sqrt b := by
  rw [Real.sqrt_div' a hc.le, Real.sqrt_div' b hc.le, mul_assoc]
  have hs0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  field_simp
  rw [Real.sq_sqrt hc.le]
  ring

/-- Isotropic Cauchy–Schwarz with Ward:
`|x* R² y| ≤ |Im w|⁻¹ √|x* Im R x| √|y* Im R y|`. -/
theorem norm_sourceMatrixElement_resolvent_mul_resolvent_le (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (x y : Fin N → ℂ) :
    ‖sourceMatrixElement (resolvent H w * resolvent H w) x y‖ ≤
      |w.im|⁻¹ *
        Real.sqrt |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re| *
        Real.sqrt |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re| := by
  refine (norm_sourceMatrixElement_mul_le _ _ x y).trans (le_of_eq ?_)
  rw [← Real.sqrt_sq (sourceVectorNorm_nonneg ((resolvent H w)ᴴ *ᵥ x)),
    ← Real.sqrt_sq (sourceVectorNorm_nonneg (resolvent H w *ᵥ y)),
    sourceVectorNorm_resolvent_conjTranspose_mulVec_sq hH hw,
    sourceVectorNorm_resolvent_mulVec_sq hH hw]
  exact sqrt_div_mul_sqrt_div (abs_pos.mpr hw)

/-- Sandwiched isotropic bound: `|x* R B R y| ≤ ‖B‖ |Im w|⁻¹ √|x* Im R x| √|y* Im R y|`. -/
theorem norm_sourceMatrixElement_resolvent_mul_mul_resolvent_le (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (B : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    ‖sourceMatrixElement (resolvent H w * B * resolvent H w) x y‖ ≤
      ‖B‖ * (|w.im|⁻¹ *
        Real.sqrt |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re| *
        Real.sqrt |(sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re|) := by
  refine (norm_sourceMatrixElement_mul_mul_le _ B _ x y).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.sqrt_sq (sourceVectorNorm_nonneg ((resolvent H w)ᴴ *ᵥ x)),
    ← Real.sqrt_sq (sourceVectorNorm_nonneg (resolvent H w *ᵥ y)),
    sourceVectorNorm_resolvent_conjTranspose_mulVec_sq hH hw,
    sourceVectorNorm_resolvent_mulVec_sq hH hw,
    sqrt_div_mul_sqrt_div (abs_pos.mpr hw)]

/-- `Re ⟨Im R⟩ / Im w = ⟨R Rᴴ⟩ ≥ 0`. -/
theorem re_normalizedTrace_imaginaryPart_resolvent_div_nonneg (hH : H.IsHermitian)
    (hw : w.im ≠ 0) :
    0 ≤ (normalizedTrace (External.CEH.imaginaryPart (resolvent H w))).re / w.im := by
  rw [normalizedTrace_imaginaryPart, Complex.ofReal_re]
  exact im_normalizedTrace_resolvent_div_nonneg hH hw

/-- `Re ⟨Im R · B Bᴴ⟩ / Im w = ⟨Rᴴ R B Bᴴ⟩ = ⟨(R B)ᴴ (R B)⟩`. -/
theorem normalizedTrace_conjTranspose_resolvent_mul_self (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace ((resolvent H w * B)ᴴ * (resolvent H w * B)) =
      (w.im : ℂ)⁻¹ * normalizedTrace (External.CEH.imaginaryPart (resolvent H w) * B * Bᴴ) := by
  rw [conjTranspose_mul, Matrix.mul_assoc, normalizedTrace_mul_comm,
    ← Matrix.mul_assoc (resolvent H w)ᴴ, conjTranspose_mul_resolvent hH hw, smul_mul,
    smul_mul, normalizedTrace_smul]

theorem re_normalizedTrace_imaginaryPart_resolvent_mul_div_nonneg (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (B : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ (normalizedTrace (External.CEH.imaginaryPart (resolvent H w) * B * Bᴴ)).re / w.im := by
  have h := normalizedTrace_mul_conjTranspose_self_re_nonneg (resolvent H w * B)ᴴ
  rw [conjTranspose_conjTranspose, normalizedTrace_conjTranspose_resolvent_mul_self hH hw,
    ← Complex.ofReal_inv, Complex.re_ofReal_mul] at h
  rw [div_eq_inv_mul]
  exact h

/-- Averaged Cauchy–Schwarz with Ward:
`|⟨R² B⟩| ≤ |Im w|⁻¹ √(Re⟨Im R⟩ · Re⟨Im R · B Bᴴ⟩)`. The product under the root is
nonnegative (both factors have the sign of `Im w`). -/
theorem norm_normalizedTrace_resolvent_sq_mul_le (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    ‖normalizedTrace (resolvent H w * resolvent H w * B)‖ ≤
      |w.im|⁻¹ * Real.sqrt ((normalizedTrace (External.CEH.imaginaryPart (resolvent H w))).re *
        (normalizedTrace (External.CEH.imaginaryPart (resolvent H w) * B * Bᴴ)).re) := by
  rw [Matrix.mul_assoc]
  refine (norm_normalizedTrace_mul_le _ _).trans (le_of_eq ?_)
  set a := (normalizedTrace (External.CEH.imaginaryPart (resolvent H w))).re
  set b := (normalizedTrace (External.CEH.imaginaryPart (resolvent H w) * B * Bᴴ)).re
  have ha : 0 ≤ a / w.im := re_normalizedTrace_imaginaryPart_resolvent_div_nonneg hH hw
  have hb : 0 ≤ b / w.im := re_normalizedTrace_imaginaryPart_resolvent_mul_div_nonneg hH hw B
  have h1 : (normalizedTrace (resolvent H w * (resolvent H w)ᴴ)).re = a / w.im := by
    rw [normalizedTrace_resolvent_mul_conjTranspose hH hw, Complex.div_ofReal_re]
  have h2 : (normalizedTrace ((resolvent H w * B)ᴴ * (resolvent H w * B))).re = b / w.im := by
    rw [normalizedTrace_conjTranspose_resolvent_mul_self hH hw, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, div_eq_inv_mul]
  rw [h1, h2, ← Real.sqrt_mul ha]
  have hab : a / w.im * (b / w.im) = (a * b) / |w.im| ^ 2 := by
    rw [sq_abs]
    ring
  rw [hab, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (abs_nonneg _), div_eq_inv_mul]

/-- `|⟨R²⟩| ≤ |Re⟨Im R⟩| / |Im w|`. -/
theorem norm_normalizedTrace_resolvent_sq_le (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    ‖normalizedTrace (resolvent H w * resolvent H w)‖ ≤
      |(normalizedTrace (External.CEH.imaginaryPart (resolvent H w))).re| / |w.im| := by
  have h := norm_normalizedTrace_resolvent_sq_mul_le hH hw 1
  simp only [Matrix.mul_one, conjTranspose_one] at h
  rw [Real.sqrt_mul_self_eq_abs] at h
  rw [div_eq_inv_mul]
  exact h

/-- Exact quadratic-variation identity for `d⟨G B⟩ = -λ ⟨G dB G B⟩`:
`⟨(R B R)(R B R)ᴴ⟩ = (Im w)⁻² ⟨Im R · B · Im R · Bᴴ⟩`. -/
theorem normalizedTrace_resolvent_mul_mul_resolvent_mul_conjTranspose (hH : H.IsHermitian)
    (hw : w.im ≠ 0) (B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace ((resolvent H w * B * resolvent H w) *
        (resolvent H w * B * resolvent H w)ᴴ) =
      ((w.im : ℂ)⁻¹) ^ 2 * normalizedTrace (External.CEH.imaginaryPart (resolvent H w) * B *
        External.CEH.imaginaryPart (resolvent H w) * Bᴴ) := by
  set R := resolvent H w
  have e1 : R * B * R * (R * B * R)ᴴ = (R * B * (R * Rᴴ) * Bᴴ) * Rᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have e2 : Rᴴ * (R * B * (R * Rᴴ) * Bᴴ) = (Rᴴ * R) * B * (R * Rᴴ) * Bᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e1, normalizedTrace_mul_comm, e2, conjTranspose_mul_resolvent hH hw,
    resolvent_mul_conjTranspose hH hw]
  simp only [smul_mul, Matrix.mul_smul, normalizedTrace_smul, smul_smul]
  ring

/-- `⟨R² (R²)ᴴ⟩ ≤ |Re⟨Im R⟩| / |Im w|³`. -/
theorem re_normalizedTrace_resolvent_sq_mul_conjTranspose_le (hH : H.IsHermitian)
    (hw : w.im ≠ 0) :
    (normalizedTrace ((resolvent H w * resolvent H w) *
        (resolvent H w * resolvent H w)ᴴ)).re ≤
      |(normalizedTrace (External.CEH.imaginaryPart (resolvent H w))).re| / |w.im| ^ 3 := by
  set R := resolvent H w
  set a := (normalizedTrace (External.CEH.imaginaryPart R)).re
  have hpos : 0 < |w.im| := abs_pos.mpr hw
  have hcol := re_trace_conjTranspose_mul_self_mul_le R R
    (sourceVectorNorm_resolvent_mulVec_le hH hw)
  have hRR : (N : ℝ)⁻¹ * ((Rᴴ * R).trace).re = |a| / |w.im| := by
    rw [← re_normalizedTrace, conjTranspose_mul_resolvent hH hw, normalizedTrace_smul,
      ← Complex.ofReal_inv, Complex.re_ofReal_mul, ← abs_div, inv_mul_eq_div]
    exact (abs_of_nonneg (re_normalizedTrace_imaginaryPart_resolvent_div_nonneg hH hw)).symm
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  rw [normalizedTrace_mul_comm, re_normalizedTrace]
  calc (N : ℝ)⁻¹ * (((R * R)ᴴ * (R * R)).trace).re
      ≤ (N : ℝ)⁻¹ * ((|w.im|⁻¹) ^ 2 * ((Rᴴ * R).trace).re) := mul_le_mul_of_nonneg_left hcol hN
    _ = (|w.im|⁻¹) ^ 2 * ((N : ℝ)⁻¹ * ((Rᴴ * R).trace).re) := by ring
    _ = _ := by rw [hRR]; field_simp

/-- Entrywise expansion of a sandwiched form: `x* A E C y = ∑_ab (x* A)_a E_ab (C y)_b`
(the coefficient of `dB_ab` in `x* R dB R y`). -/
theorem sourceMatrixElement_mul_mul_eq_sum (A E C : Matrix (Fin N) (Fin N) ℂ)
    (x y : Fin N → ℂ) :
    sourceMatrixElement (A * E * C) x y =
      ∑ a, ∑ b, (star x ᵥ* A) a * E a b * (C *ᵥ y) b := by
  rw [sourceMatrixElement, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec,
    dotProduct_mulVec]
  simp only [dotProduct, vecMul, Finset.sum_mul]
  exact Finset.sum_comm

/-- Isotropic quadratic-variation factor (left): `∑_a |(x* R)_a|² = Re(x* Im R x) / Im w`. -/
theorem sum_norm_sq_vecMul_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (x : Fin N → ℂ) :
    ∑ a, ‖(star x ᵥ* resolvent H w) a‖ ^ 2 =
      (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re / w.im := by
  have hv : star x ᵥ* resolvent H w = star ((resolvent H w)ᴴ *ᵥ x) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [hv, re_sourceMatrixElement_imaginaryPart_resolvent' hH hw]
  simp only [Pi.star_apply, norm_star]
  rw [← sourceVectorNorm_sq]
  field_simp

/-- Isotropic quadratic-variation factor (right): `∑_b |(R y)_b|² = Re(y* Im R y) / Im w`. -/
theorem sum_norm_sq_resolvent_mulVec (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (y : Fin N → ℂ) :
    ∑ b, ‖(resolvent H w *ᵥ y) b‖ ^ 2 =
      (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re / w.im := by
  rw [re_sourceMatrixElement_imaginaryPart_resolvent hH hw, ← sourceVectorNorm_sq]
  field_simp

/-- Exact isotropic quadratic-variation identity for `d(G)_xy = -λ (G dB G)_xy`:
`∑_ab |(x* R)_a|² |(R y)_b|² = Re(x* Im R x) Re(y* Im R y) / (Im w)²`. -/
theorem sum_sum_norm_sq_resolvent_entries (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (x y : Fin N → ℂ) :
    ∑ a, ∑ b, ‖(star x ᵥ* resolvent H w) a‖ ^ 2 * ‖(resolvent H w *ᵥ y) b‖ ^ 2 =
      (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) x x).re *
        (sourceMatrixElement (External.CEH.imaginaryPart (resolvent H w)) y y).re / w.im ^ 2 := by
  rw [← Finset.sum_mul_sum, sum_norm_sq_vecMul_resolvent hH hw,
    sum_norm_sq_resolvent_mulVec hH hw]
  ring

end ResolventBounds

end BlockBand.Native.CEH.Phase1
