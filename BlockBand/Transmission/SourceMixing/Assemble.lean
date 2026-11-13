module

public import BlockBand.Transmission.SourceMixing.MatchedScalars

/-!
# Matrix assembly of the transported mean (deterministic part)

* `assemble_on`: `F = (θs₁)·KM·M·KMᴴ + (ρ₁ - c₀s₁)·KM·KMᴴ` is within `O(e)` of `θ_*(R - c₀)`
  once `KM, M, s₁, θ, ρ₁` are within `O(e)` of `1, R, 1, θ_*, c₀(1 - θ_*)`;
* `assemble_bound`: `‖F‖ ≤ |θ||s₁|‖KM‖²‖M‖ + (|ρ₁| + |c₀||s₁|)‖KM‖²`;
* `norm_div_one_add_sub_le`: `|θ/(1+x) - θ| ≤ |θ|x` for real `x ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open Matrix
open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `|θ/(1+x) - θ| ≤ |θ|x` for real `x ≥ 0`. -/
theorem norm_div_one_add_sub_le (θ : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖θ / (1 + (x : ℂ)) - θ‖ ≤ ‖θ‖ * x := by
  have h1 : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hne : ((1 + x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [h1, show θ / ((1 + x : ℝ) : ℂ) - θ = -(θ * (x : ℂ)) / ((1 + x : ℝ) : ℂ) by
    field_simp; push_cast; ring, norm_div, norm_neg, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hx, Real.norm_of_nonneg hpos.le]
  rw [div_le_iff₀ hpos]
  nlinarith [norm_nonneg θ, mul_nonneg (norm_nonneg θ) hx]

theorem norm_conjT_le {A : Matrix (Fin W) (Fin W) ℂ} {c : ℝ} (h : ‖A‖ ≤ c) : ‖Aᴴ‖ ≤ c := by
  rwa [Matrix.l2_opNorm_conjTranspose]

/-- A global bound on `‖F‖`. -/
theorem assemble_bound (KM M : Matrix (Fin W) (Fin W) ℂ) (θ s₁ ρ c₀ : ℂ) {CK CM Cθ Cs Cρ : ℝ}
    (hKM : ‖KM‖ ≤ CK) (hM : ‖M‖ ≤ CM) (hθ : ‖θ‖ ≤ Cθ) (hs : ‖s₁‖ ≤ Cs) (hρ : ‖ρ‖ ≤ Cρ) :
    ‖(θ * s₁) • (KM * M * KMᴴ) + (ρ - c₀ * s₁) • (KM * KMᴴ)‖ ≤
      Cθ * Cs * (CK * CM * CK) + (Cρ + ‖c₀‖ * Cs) * (CK * CK) := by
  have hCK : 0 ≤ CK := (norm_nonneg _).trans hKM
  have hCM : 0 ≤ CM := (norm_nonneg _).trans hM
  have hCθ : 0 ≤ Cθ := (norm_nonneg _).trans hθ
  have hCs : 0 ≤ Cs := (norm_nonneg _).trans hs
  have hCρ : 0 ≤ Cρ := (norm_nonneg _).trans hρ
  have hX₁ : ‖KM * M * KMᴴ‖ ≤ CK * CM * CK :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hKM hM (norm_nonneg _) hCK)) (norm_conjT_le hKM) (norm_nonneg _) (by positivity))
  have hX₂ : ‖KM * KMᴴ‖ ≤ CK * CK := (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hKM (norm_conjT_le hKM) (norm_nonneg _) hCK)
  refine (norm_add_le _ _).trans (add_le_add ((norm_smul_le _ _).trans (mul_le_mul
    ((norm_mul_le _ _).trans (mul_le_mul hθ hs (norm_nonneg _) hCθ)) hX₁ (norm_nonneg _)
    (by positivity))) ((norm_smul_le _ _).trans (mul_le_mul ((norm_sub_le _ _).trans
    (add_le_add hρ ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)))))
    hX₂ (norm_nonneg _) (by positivity))))

/-- If `KM, M, s₁, θ, ρ₁` are within `K e` of `1, R, 1, θ_*, c₀(1 - θ_*)`, then `F` is within an
explicit constant times `e` of `θ_*(R - c₀)`. -/
theorem assemble_on (KM M R : Matrix (Fin W) (Fin W) ℂ) (θ s₁ ρ θs c₀ : ℂ)
    {CK CM CR Cθ K e : ℝ} (he : 0 ≤ e) (hK : 0 ≤ K)
    (hKM : ‖KM‖ ≤ CK) (hM : ‖M‖ ≤ CM) (hR : ‖R‖ ≤ CR) (hθ : ‖θ‖ ≤ Cθ) (hθs : ‖θs‖ ≤ 1)
    (hKM1 : ‖KM - 1‖ ≤ K * e) (hMR : ‖M - R‖ ≤ K * e) (hs1 : ‖s₁ - 1‖ ≤ K * e)
    (hθθ : ‖θ - θs‖ ≤ K * e) (hρρ : ‖ρ - c₀ * (1 - θs)‖ ≤ K * e) :
    ‖((θ * s₁) • (KM * M * KMᴴ) + (ρ - c₀ * s₁) • (KM * KMᴴ)) - θs • (R - c₀ • 1)‖ ≤
      ((Cθ * K + K) * (CK * CM * CK) + (K * (CM * CK) + K * CK + CR * K) +
        (K + ‖c₀‖ * K) * (CK * CK) + ‖c₀‖ * (K * CK + K)) * e := by
  have hCK : 0 ≤ CK := (norm_nonneg _).trans hKM
  have hCM : 0 ≤ CM := (norm_nonneg _).trans hM
  have hCR : 0 ≤ CR := (norm_nonneg _).trans hR
  have hCθ : 0 ≤ Cθ := (norm_nonneg _).trans hθ
  have hKe : 0 ≤ K * e := (norm_nonneg _).trans hKM1
  have hKMs := norm_conjT_le hKM
  have hKMs1 : ‖KMᴴ - 1‖ ≤ K * e := by
    rw [← conjTranspose_one, ← conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]; exact hKM1
  have hX₁ : ‖KM * M * KMᴴ‖ ≤ CK * CM * CK :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hKM hM (norm_nonneg _) hCK)) hKMs (norm_nonneg _) (by positivity))
  have hX₂ : ‖KM * KMᴴ‖ ≤ CK * CK := (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_mul hKM hKMs (norm_nonneg _) hCK)
  have hd : ((θ * s₁) • (KM * M * KMᴴ) + (ρ - c₀ * s₁) • (KM * KMᴴ)) - θs • (R - c₀ • 1) =
      (θ * s₁ - θs) • (KM * M * KMᴴ) + θs • (KM * M * KMᴴ - R) +
        (ρ - c₀ * s₁ + c₀ * θs) • (KM * KMᴴ) + (c₀ * θs) • (1 - KM * KMᴴ) := by
    simp only [smul_sub, sub_smul, add_smul, smul_smul, mul_comm θs c₀]
    abel
  have a1 : ‖(θ * s₁ - θs) • (KM * M * KMᴴ)‖ ≤ (Cθ * K + K) * e * (CK * CM * CK) := by
    refine (norm_smul_le _ _).trans (mul_le_mul ?_ hX₁ (norm_nonneg _) (by positivity))
    rw [show θ * s₁ - θs = θ * (s₁ - 1) + (θ - θs) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hθ hs1 (norm_nonneg _) hCθ
    nlinarith
  have a2 : ‖θs • (KM * M * KMᴴ - R)‖ ≤ (K * (CM * CK) + K * CK + CR * K) * e := by
    refine (norm_smul_le _ _).trans ?_
    have e' : KM * M * KMᴴ - R = (KM - 1) * (M * KMᴴ) + (M - R) * KMᴴ + R * (KMᴴ - 1) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    have hMK : ‖M * KMᴴ‖ ≤ CM * CK := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hM hKMs (norm_nonneg _) hCM)
    have h3 : ‖KM * M * KMᴴ - R‖ ≤ (K * (CM * CK) + K * CK + CR * K) * e := by
      rw [e']
      refine (norm_add₃_le).trans (le_trans (add_le_add_three ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hKM1 hMK (norm_nonneg _) hKe))
        ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hMR hKMs (norm_nonneg _) hKe))
        ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul hR hKMs1 (norm_nonneg _) hCR)))
        (le_of_eq (by ring)))
    have h0 : 0 ≤ (K * (CM * CK) + K * CK + CR * K) * e := (norm_nonneg _).trans h3
    nlinarith [mul_le_mul hθs h3 (norm_nonneg _) zero_le_one]
  have a3 : ‖(ρ - c₀ * s₁ + c₀ * θs) • (KM * KMᴴ)‖ ≤ (K + ‖c₀‖ * K) * e * (CK * CK) := by
    refine (norm_smul_le _ _).trans (mul_le_mul ?_ hX₂ (norm_nonneg _) (by positivity))
    rw [show ρ - c₀ * s₁ + c₀ * θs = (ρ - c₀ * (1 - θs)) - c₀ * (s₁ - 1) by ring]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left hs1 (norm_nonneg c₀)
    nlinarith
  have a4 : ‖(c₀ * θs) • (1 - KM * KMᴴ)‖ ≤ ‖c₀‖ * ((K * CK + K) * e) := by
    refine (norm_smul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · rw [norm_mul]
      calc ‖c₀‖ * ‖θs‖ ≤ ‖c₀‖ * 1 := mul_le_mul_of_nonneg_left hθs (norm_nonneg _)
        _ = ‖c₀‖ := mul_one _
    · have e' : 1 - KM * KMᴴ = -((KM - 1) * KMᴴ + (KMᴴ - 1)) := by
        simp only [Matrix.sub_mul, Matrix.one_mul]; abel
      rw [e', norm_neg]
      exact (norm_add_le _ _).trans (le_trans (add_le_add ((Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul hKM1 hKMs (norm_nonneg _) hKe)) hKMs1) (le_of_eq (by ring)))
  rw [hd]
  refine (norm_add_le _ _).trans (le_trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add a1 a2)) a3)) a4) (le_of_eq (by ring)))

end BlockBand.Transmission.SourceMixing
