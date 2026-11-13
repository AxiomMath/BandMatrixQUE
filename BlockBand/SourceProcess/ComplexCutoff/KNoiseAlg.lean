module

public import BlockBand.SourceProcess.ComplexCutoff.DataAlg

/-!
# Rank-free bracket bounds for the `𝒦` noise coefficient

With `C_L = kC D₀ η L = 80 η² D₀ (1 + L)⁴`, for frames with `‖V₁‖² + ‖V₂‖² ≤ L`:
`Σ_a ‖kNoise_a(V₁)‖² ≤ C_L` (`kNoise_size_le`) and
`Σ_a ‖kNoise_a(V₁) - kNoise_a(V₂)‖² ≤ C_L ‖V₁ - V₂‖²` (`kNoise_sub_le`). The constants do not
depend on the rank.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCutoff

open Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.CutoffLimit BlockBand.SourceProcess.ComplexUnique
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.Internal.Contracts.TransmissionLaws

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The constant `C_L = 80 η² D₀ (1 + L)⁴`. -/
def kC (D0 η L : ℝ) : ℝ := 80 * η ^ 2 * D0 * (1 + L) ^ 4

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

omit [DecidableEq c] in
theorem sum_norm_unit_sandwich (A : Matrix c ι ℂ) (B : Matrix ι c ℂ) :
    ∑ e : ι × ι, ‖A * Matrix.single e.1 e.2 (1 : ℂ) * B‖ ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  simp only [← hsSq_eq, hsSq, unit_entry, norm_mul, mul_pow]
  rw [Fintype.sum_prod_type]
  have h : ∀ x y : ι, ∑ i, ∑ j, ‖A i x‖ ^ 2 * ‖B y j‖ ^ 2 =
      (∑ i, ‖A i x‖ ^ 2) * ∑ j, ‖B y j‖ ^ 2 := fun x y => by
    rw [Finset.sum_mul_sum]
  simp only [h, ← Finset.sum_mul_sum]
  rw [Finset.sum_comm (f := fun x i => ‖A i x‖ ^ 2)]

omit [DecidableEq c] in
theorem sum_norm_unit_sandwich_sub_le (A₁ A₂ : Matrix c ι ℂ) (B₁ B₂ : Matrix ι c ℂ) :
    ∑ e : ι × ι, ‖A₁ * Matrix.single e.1 e.2 (1 : ℂ) * B₁ -
        A₂ * Matrix.single e.1 e.2 (1 : ℂ) * B₂‖ ^ 2 ≤
      2 * (‖A₁ - A₂‖ ^ 2 * ‖B₁‖ ^ 2) + 2 * (‖A₂‖ ^ 2 * ‖B₁ - B₂‖ ^ 2) := by
  rw [← sum_norm_unit_sandwich, ← sum_norm_unit_sandwich, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have h : A₁ * Matrix.single e.1 e.2 (1 : ℂ) * B₁ - A₂ * Matrix.single e.1 e.2 (1 : ℂ) * B₂ =
      (A₁ - A₂) * Matrix.single e.1 e.2 (1 : ℂ) * B₁ +
        A₂ * Matrix.single e.1 e.2 (1 : ℂ) * (B₁ - B₂) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h]
  have := norm_add_le ((A₁ - A₂) * Matrix.single e.1 e.2 (1 : ℂ) * B₁)
    (A₂ * Matrix.single e.1 e.2 (1 : ℂ) * (B₁ - B₂))
  nlinarith [norm_nonneg ((A₁ - A₂) * Matrix.single e.1 e.2 (1 : ℂ) * B₁ +
    A₂ * Matrix.single e.1 e.2 (1 : ℂ) * (B₁ - B₂)),
    norm_nonneg ((A₁ - A₂) * Matrix.single e.1 e.2 (1 : ℂ) * B₁),
    norm_nonneg (A₂ * Matrix.single e.1 e.2 (1 : ℂ) * (B₁ - B₂)),
    sq_nonneg (‖(A₁ - A₂) * Matrix.single e.1 e.2 (1 : ℂ) * B₁‖ -
      ‖A₂ * Matrix.single e.1 e.2 (1 : ℂ) * (B₁ - B₂)‖)]

omit [DecidableEq ι] in
/-- `‖V𝖣‖ ≤ ‖V‖` for a signature `𝖣` (`𝖣²` is an orthogonal projection). -/
theorem norm_mul_signature_le {D : Matrix c c ℂ} (hD : IsSignature D) (V : Matrix ι c ℂ) :
    ‖V * D‖ ≤ ‖V‖ := by
  obtain ⟨hDH, hD3⟩ := hD
  have hQH : (D * D)ᴴ = D * D := by rw [conjTranspose_mul, hDH]
  have hQQ : D * D * (D * D) = D * D := by
    rw [← Matrix.mul_assoc, hD3]
  have e : ‖D * Vᴴ‖ ^ 2 = ‖D * D * Vᴴ‖ ^ 2 := by
    rw [← hsSq_eq, ← hsSq_eq, hsSq_eq_re_trace, hsSq_eq_re_trace, conjTranspose_mul,
      conjTranspose_mul, hQH, hDH]
    congr 2
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc D D (D * (D * Vᴴ)), ← Matrix.mul_assoc (D * D) D (D * Vᴴ), hD3]
  have h := norm_proj_mul_le' hQH hQQ Vᴴ
  rw [frobenius_norm_conjTranspose] at h
  have h2 : ‖D * Vᴴ‖ ≤ ‖V‖ := by
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).2 h
    rw [← e] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  rw [← frobenius_norm_conjTranspose, conjTranspose_mul, hDH]
  exact h2

variable {P : Matrix ι ι ℂ} {Naux : ℕ} {D : Matrix c c ℂ}

omit [DecidableEq ι] [DecidableEq c] in
/-- `P'(V)ᴴ V = P V + V 𝖣 (VᴴV)`. -/
theorem gramProjection_conj_mul (hP : IsNearProjection P Naux) (hD : IsSignature D)
    (V : Matrix ι c ℂ) :
    (gramProjection P V D)ᴴ * V = P * V + V * D * (Vᴴ * V) := by
  rw [gramProjection, conjTranspose_add, hP.1, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hD.1, Matrix.add_mul]
  simp only [Matrix.mul_assoc]

theorem norm_pV_le (hP : IsNearProjection P Naux) (hD : IsSignature D) (V : Matrix ι c ℂ) :
    ‖(gramProjection P V D)ᴴ * V‖ ≤ ‖V‖ * (1 + ‖V‖ ^ 2) := by
  rw [gramProjection_conj_mul hP hD]
  have h1 := norm_proj_mul_le hP V
  have h2 := frobenius_norm_mul (V * D) (Vᴴ * V)
  have h3 := norm_mul_signature_le hD V
  have h4 := norm_gram_le V
  have := norm_add_le (P * V) (V * D * (Vᴴ * V))
  have h5 : ‖V * D‖ * ‖Vᴴ * V‖ ≤ ‖V‖ * ‖V‖ ^ 2 :=
    mul_le_mul h3 h4 (norm_nonneg _) (norm_nonneg _)
  nlinarith

theorem norm_pV_sub_le (hP : IsNearProjection P Naux) (hD : IsSignature D)
    (V₁ V₂ : Matrix ι c ℂ) :
    ‖(gramProjection P V₁ D)ᴴ * V₁ - (gramProjection P V₂ D)ᴴ * V₂‖ ≤
      ‖V₁ - V₂‖ * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ * (‖V₁‖ + ‖V₂‖)) := by
  rw [gramProjection_conj_mul hP hD, gramProjection_conj_mul hP hD]
  have e : P * V₁ + V₁ * D * (V₁ᴴ * V₁) - (P * V₂ + V₂ * D * (V₂ᴴ * V₂)) =
      P * (V₁ - V₂) + (V₁ - V₂) * D * (V₁ᴴ * V₁) + V₂ * D * (V₁ᴴ * V₁ - V₂ᴴ * V₂) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e]
  have a0 := norm_proj_mul_le hP (V₁ - V₂)
  have a1 : ‖(V₁ - V₂) * D * (V₁ᴴ * V₁)‖ ≤ ‖V₁ - V₂‖ * ‖V₁‖ ^ 2 :=
    (frobenius_norm_mul _ _).trans (mul_le_mul (norm_mul_signature_le hD _) (norm_gram_le V₁)
      (norm_nonneg _) (norm_nonneg _))
  have a2 : ‖V₂ * D * (V₁ᴴ * V₁ - V₂ᴴ * V₂)‖ ≤ ‖V₂‖ * (‖V₁ - V₂‖ * (‖V₁‖ + ‖V₂‖)) :=
    (frobenius_norm_mul _ _).trans (mul_le_mul (norm_mul_signature_le hD _)
      (norm_gram_sub_le V₁ V₂) (norm_nonneg _) (norm_nonneg _))
  have t1 := norm_add_le (P * (V₁ - V₂) + (V₁ - V₂) * D * (V₁ᴴ * V₁))
    (V₂ * D * (V₁ᴴ * V₁ - V₂ᴴ * V₂))
  have t2 := norm_add_le (P * (V₁ - V₂)) ((V₁ - V₂) * D * (V₁ᴴ * V₁))
  nlinarith

omit [DecidableEq c] in
theorem kNoise_eq (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) : kNoise D0 η P D a V =
      (((-2 * η : ℝ) : ℂ) * Complex.I * star (sourceWeight D0 a.2)) •
        ((P * V)ᴴ * Matrix.single a.1.1 a.1.2 (1 : ℂ) * ((gramProjection P V D)ᴴ * V)) := by
  rw [kNoise, conjTranspose_mul]

theorem norm_sq_kCoeff {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (r : Fin 2) :
    ‖((-2 * η : ℝ) : ℂ) * Complex.I * star (sourceWeight D0 r)‖ ^ 2 = η ^ 2 * D0 := by
  rw [norm_mul, norm_mul, norm_star, norm_sourceWeight, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, mul_one, mul_pow, div_pow, Real.sq_sqrt hD0, abs_mul, mul_pow, sq_abs]
  norm_num
  ring

omit [DecidableEq c] in
/-- `Σ_a ‖kNoise_a(V₁) - kNoise_a(V₂)‖² = 2η²D₀ Σ_e ‖A₁E_eB₁ - A₂E_eB₂‖²`. -/
theorem sum_norm_kNoise_sub {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (V₁ V₂ : Matrix ι c ℂ) :
    ∑ a, ‖kNoise D0 η P D a V₁ - kNoise D0 η P D a V₂‖ ^ 2 =
      2 * (η ^ 2 * D0) * ∑ e : ι × ι,
        ‖(P * V₁)ᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V₁ D)ᴴ * V₁) -
          (P * V₂)ᴴ * Matrix.single e.1 e.2 (1 : ℂ) * ((gramProjection P V₂ D)ᴴ * V₂)‖ ^ 2 := by
  simp only [kNoise_eq, ← smul_sub, norm_smul, mul_pow, norm_sq_kCoeff hD0]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Fin.sum_univ_two]
  ring

theorem real_q1 {r L : ℝ} (h : r ^ 2 ≤ L) : (r * (1 + r ^ 2)) ^ 2 ≤ (1 + L) ^ 3 := by
  have hL : 0 ≤ L := (sq_nonneg r).trans h
  have b : (1 + r ^ 2) ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc (r * (1 + r ^ 2)) ^ 2 = r ^ 2 * (1 + r ^ 2) ^ 2 := by ring
    _ ≤ L * (1 + L) ^ 2 := mul_le_mul h b (by positivity) hL
    _ ≤ (1 + L) * (1 + L) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (1 + L) ^ 3 := by ring

theorem real_q2 {r₁ r₂ L : ℝ} (h : r₁ ^ 2 + r₂ ^ 2 ≤ L) :
    1 + r₁ ^ 2 + r₂ * (r₁ + r₂) ≤ 2 * (1 + L) := by
  nlinarith [sq_nonneg (r₁ - r₂)]

theorem norm_sq_pV_le (hP : IsNearProjection P Naux) (hD : IsSignature D) {V : Matrix ι c ℂ}
    {L : ℝ} (hV : ‖V‖ ^ 2 ≤ L) : ‖(gramProjection P V D)ᴴ * V‖ ^ 2 ≤ (1 + L) ^ 3 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_pV_le hP hD V) 2).trans (real_q1 hV)

theorem norm_sq_pV_sub_le (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {V₁ V₂ : Matrix ι c ℂ} {L : ℝ} (h : ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2 ≤ L) :
    ‖(gramProjection P V₁ D)ᴴ * V₁ - (gramProjection P V₂ D)ᴴ * V₂‖ ^ 2 ≤
      4 * (1 + L) ^ 2 * ‖V₁ - V₂‖ ^ 2 := by
  have h1 := real_q2 h
  have h0 : 0 ≤ 1 + ‖V₁‖ ^ 2 + ‖V₂‖ * (‖V₁‖ + ‖V₂‖) := by positivity
  have he := norm_nonneg (V₁ - V₂)
  calc _ ≤ (‖V₁ - V₂‖ * (1 + ‖V₁‖ ^ 2 + ‖V₂‖ * (‖V₁‖ + ‖V₂‖))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_pV_sub_le hP hD V₁ V₂) 2
    _ ≤ (‖V₁ - V₂‖ * (2 * (1 + L))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h1 he) 2
    _ = 4 * (1 + L) ^ 2 * ‖V₁ - V₂‖ ^ 2 := by ring

omit [DecidableEq c] in
theorem kNoise_zero (D0 η : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι) :
    kNoise D0 η P D a (0 : Matrix ι c ℂ) = 0 := by
  rw [kNoise_eq]; simp

/-- **The rank-free `𝒦` bracket bound, size**. -/
theorem kNoise_size_le {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (hP : IsNearProjection P Naux)
    (hD : IsSignature D) {V : Matrix ι c ℂ} {L : ℝ} (hL : ‖V‖ ^ 2 ≤ L) :
    ∑ a, ‖kNoise D0 η P D a V‖ ^ 2 ≤ kC D0 η L := by
  have h := sum_norm_kNoise_sub (P := P) (D := D) hD0 η V 0
  simp only [kNoise_zero, sub_zero, Matrix.mul_zero, conjTranspose_zero, Matrix.zero_mul] at h
  rw [h, sum_norm_unit_sandwich]
  have hL0 : 0 ≤ L := (sq_nonneg _).trans hL
  have k1 : ‖(P * V)ᴴ‖ ^ 2 ≤ 1 + L := by
    rw [frobenius_norm_conjTranspose]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_proj_mul_le hP V) 2
    linarith
  have k2 : ‖(P * V)ᴴ‖ ^ 2 * ‖(gramProjection P V D)ᴴ * V‖ ^ 2 ≤ (1 + L) * (1 + L) ^ 3 :=
    mul_le_mul k1 (norm_sq_pV_le hP hD hL) (sq_nonneg _) (by positivity)
  have hA : 0 ≤ η ^ 2 * D0 * (1 + L) ^ 4 := by positivity
  calc _ ≤ 2 * (η ^ 2 * D0) * ((1 + L) * (1 + L) ^ 3) :=
        mul_le_mul_of_nonneg_left k2 (by positivity)
    _ = 2 * (η ^ 2 * D0 * (1 + L) ^ 4) := by ring
    _ ≤ kC D0 η L := by rw [kC]; linarith

/-- **The rank-free `𝒦` bracket bound, difference**: `≤ C_L ‖V₁ - V₂‖²` on `‖V₁‖² + ‖V₂‖² ≤ L`. -/
theorem kNoise_sub_le {D0 : ℝ} (hD0 : 0 ≤ D0) (η : ℝ) (hP : IsNearProjection P Naux)
    (hD : IsSignature D) {V₁ V₂ : Matrix ι c ℂ} {L : ℝ} (hL : ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2 ≤ L) :
    ∑ a, ‖kNoise D0 η P D a V₁ - kNoise D0 η P D a V₂‖ ^ 2 ≤ kC D0 η L * ‖V₁ - V₂‖ ^ 2 := by
  rw [sum_norm_kNoise_sub hD0]
  have hS := sum_norm_unit_sandwich_sub_le (P * V₁)ᴴ (P * V₂)ᴴ
    ((gramProjection P V₁ D)ᴴ * V₁) ((gramProjection P V₂ D)ᴴ * V₂)
  have hL0 : 0 ≤ L := by nlinarith [sq_nonneg ‖V₁‖, sq_nonneg ‖V₂‖]
  have hM : ‖(P * V₁)ᴴ - (P * V₂)ᴴ‖ ^ 2 ≤ ‖V₁ - V₂‖ ^ 2 := by
    rw [← conjTranspose_sub, ← Matrix.mul_sub, frobenius_norm_conjTranspose]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_proj_mul_le hP _) 2
  have hM₂ : ‖(P * V₂)ᴴ‖ ^ 2 ≤ 1 + L := by
    rw [frobenius_norm_conjTranspose]
    have := pow_le_pow_left₀ (norm_nonneg _) (norm_proj_mul_le hP V₂) 2
    nlinarith [sq_nonneg ‖V₁‖]
  have q1 := norm_sq_pV_le hP hD (show ‖V₁‖ ^ 2 ≤ L by nlinarith [sq_nonneg ‖V₂‖])
  have q2 := norm_sq_pV_sub_le hP hD hL
  set e2 := ‖V₁ - V₂‖ ^ 2
  have he2 : 0 ≤ e2 := sq_nonneg _
  set sL := 1 + L
  have hs1 : 1 ≤ sL := by simp only [sL]; linarith
  have k1 := mul_le_mul hM q1 (sq_nonneg _) he2
  have k2 := mul_le_mul hM₂ q2 (sq_nonneg _) (by positivity)
  have hs34 : sL ^ 3 ≤ sL ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hA : 0 ≤ η ^ 2 * D0 * e2 := by positivity
  have hsum : 2 * (‖(P * V₁)ᴴ - (P * V₂)ᴴ‖ ^ 2 * ‖(gramProjection P V₁ D)ᴴ * V₁‖ ^ 2) +
      2 * (‖(P * V₂)ᴴ‖ ^ 2 * ‖(gramProjection P V₁ D)ᴴ * V₁ - (gramProjection P V₂ D)ᴴ * V₂‖ ^ 2)
        ≤ 10 * (e2 * sL ^ 3) := by
    have : sL * (4 * sL ^ 2 * e2) = 4 * (e2 * sL ^ 3) := by ring
    linarith
  calc _ ≤ 2 * (η ^ 2 * D0) * (10 * (e2 * sL ^ 3)) :=
        mul_le_mul_of_nonneg_left (hS.trans hsum) (by positivity)
    _ = 20 * (η ^ 2 * D0 * e2) * sL ^ 3 := by ring
    _ ≤ 20 * (η ^ 2 * D0 * e2) * sL ^ 4 := mul_le_mul_of_nonneg_left hs34 (by positivity)
    _ ≤ 80 * (η ^ 2 * D0 * e2) * sL ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = kC D0 η L * e2 := by rw [kC]; ring

end BlockBand.SourceProcess.ComplexCutoff
