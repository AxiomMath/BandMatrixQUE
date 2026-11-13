module

public import BlockBand.Layers.OnePortMeanInputs
public import BlockBand.Layers.WeightedLayerNoise
public import BlockBand.Layers.MatchedScalar
public import BlockBand.Transmission.PositiveResolvent

/-!
# One-port passive mean: the deterministic reduction

The deterministic part of the proof of the passive mean bound `E LL* ⪯ (1 + Cδ₀ + CW⁻²) I`
(`OnePortPassiveMeanContract`).

Everything here is deterministic (no measure). Given the layer means
`Ḡ = E𝒢₁₁`, `ḡ₂`, `t₁ ≥ 0`, `t₂` and the matrix `U = E LL*` satisfying the five relations of
`OppPassiveMeanEquations` with error `ρ`, the a priori bounds `‖Ḡ‖, |ḡ₂| ≤ C₀` and the scalar domain
`δ₀ ≤ bη₀/2`, `opp_core_bound` proves `‖U‖ ≤ 1 + C₁(δ₀ + ρ)` for `ρ ≤ ρ₀`, with `ρ₀, C₁` depending
only on `b, η₀, C₀`. **No bound on `‖X‖` or on `Y = -Im X` is used**: `Y` enters only through
`y = W⁻¹ Tr M̄*YM̄ ≥ 0` and `y_R = W⁻¹ Tr R*YR ≥ 0`, with the favourable sign (Ward).

## Proof (written at the layer means)

1. `T̄ Ḡ = I + e₂`, `‖e₂‖ ≤ ρ ≤ 1/2`: `T̄` is invertible, `‖M̄‖ ≤ 2C₀`, `ḡ₁ = W⁻¹ Tr M̄ + ε₁`,
   `|ε₁| ≤ 2C₀ρ` (`opp_inv_of_mul_near_one`).
2. `ḡ₂(z - bḡ₁) = 1 + e`: `v̄ = (z - bḡ₁)⁻¹` exists, `|v̄| ≤ 2C₀`, `ḡ₂ = v̄ + ε₂`, `|ε₂| ≤ 2C₀ρ`,
   `h = |v̄|² ≥ (3 + C₀)⁻²`.
3. Ward identities (`opp_neg_im_trace_inv`, from `-Im Q⁻¹ = Q⁻*(Im Q)Q⁻¹`): with `σ = Im w̄`,
   `-Im W⁻¹Tr M̄ = σA + y`, and for `R = (z - X)⁻¹`, `-Im W⁻¹Tr R = ηA_R + y_R`, `y, y_R ≥ 0`.
4. Exact algebra: `s(1 - kA) = bh + k e₃ + b e₄` (`k = c + b²h`, trace equations) and
   `σ(1 - kA) = bhη + ky - k Im ε₁ - b Im ε₂` (the exact identity
   `(η - Im Ω)(1 - k_hA_M) = bhη + k_h y_M`, up to the `ε`'s). Since `t₁ ≥ 0` and
   `t₂ ≥ h - ρ > 0`, `s > 0`, hence `1 - kA > 0`; then `σ > 0` and `1 - kA ≥ ε₀ = bh₀η₀/(2C₀)`.
5. Scalar stability (a Herglotz/Ward bound, here `ηA_R ≤ -Im W⁻¹Tr R`):
   `(ḡ₁ - a)(1 - θ) = (φ - a) + ε₁ + bε₂τ`, `θ = (c + b²v̄a)τ`, `τ = W⁻¹Tr M̄R`, with
   `|τ|² ≤ A·A_R` (Cauchy–Schwarz) and `|θ| ≤ (kA + (1-b)²A_R)/2 ≤ 1 - b/4` because
   `kA ≤ 1` and `(1-b)²A_R ≤ (1-b) + δ₀/η ≤ 1 - b/2`. Hence `|ḡ₁ - a|, |Ω̄| ≤ C(δ₀ + ρ)`.
6. `s ≤ σ/η + Cρ = 1 - Im Ω̄/η + Cρ`, `KM̄ = I + Ω̄M̄`, and `‖U‖ ≤ s‖KM̄‖² + ρ ≤ 1 + C₁(δ₀ + ρ)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Transmission (matrixImaginaryPart)
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Matrix facts
-/

section MatrixFacts

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `Re Tr MM* = Σᵢⱼ |Mᵢⱼ|²`. -/
theorem opp_trace_mul_conjTranspose_re (M : Matrix n n ℂ) :
    (M * Mᴴ).trace.re = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show star (M i j) = conj (M i j) from rfl, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

omit [DecidableEq n] in
/-- Trace Cauchy–Schwarz: `|Tr MN|² ≤ Re Tr MM* · Re Tr NN*`. -/
theorem opp_norm_trace_mul_sq_le (M N : Matrix n n ℂ) :
    ‖(M * N).trace‖ ^ 2 ≤ (M * Mᴴ).trace.re * (N * Nᴴ).trace.re := by
  have h1 : ‖(M * N).trace‖ ≤ ∑ p : n × n, ‖M p.1 p.2‖ * ‖N p.2 p.1‖ := by
    rw [Fintype.sum_prod_type' (fun i j => ‖M i j‖ * ‖N j i‖)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_mul_le _ _)
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p : n × n => ‖M p.1 p.2‖)
    (fun p => ‖N p.2 p.1‖)
  have e1 : ∑ p : n × n, ‖M p.1 p.2‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 :=
    Fintype.sum_prod_type' (fun i j => ‖M i j‖ ^ 2)
  have e2 : ∑ p : n × n, ‖N p.2 p.1‖ ^ 2 = ∑ i, ∑ j, ‖N i j‖ ^ 2 := by
    rw [Fintype.sum_prod_type' (fun i j => ‖N j i‖ ^ 2), Finset.sum_comm]
  rw [e1, e2] at h2
  rw [opp_trace_mul_conjTranspose_re, opp_trace_mul_conjTranspose_re]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- **Inverse from an approximate right inverse.** If `‖TG - I‖ ≤ ρ ≤ 1/2` then `T` is invertible
and `‖T⁻¹‖ ≤ 2‖G‖`. -/
theorem opp_inv_of_mul_near_one {T G : Matrix n n ℂ} {ρ : ℝ} (h : ‖T * G - 1‖ ≤ ρ)
    (hρ : ρ ≤ 1 / 2) : IsUnit T.det ∧ ‖T⁻¹‖ ≤ 2 * ‖G‖ := by
  have hlt : ‖-(T * G - 1)‖ < 1 := by rw [norm_neg]; linarith
  have hu : IsUnit (1 - -(T * G - 1)) := (Units.oneSub _ hlt).isUnit
  rw [sub_neg_eq_add, add_sub_cancel] at hu
  have hT : IsUnit T := isUnit_of_mul_isUnit_left hu
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  refine ⟨hdet, ?_⟩
  have hinv : T⁻¹ = G - T⁻¹ * (T * G - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have hb : ‖T⁻¹‖ ≤ ‖G‖ + ‖T⁻¹‖ * ρ := by
    calc ‖T⁻¹‖ = ‖G - T⁻¹ * (T * G - 1)‖ := congrArg norm hinv
      _ ≤ ‖G‖ + ‖T⁻¹ * (T * G - 1)‖ := norm_sub_le _ _
      _ ≤ ‖G‖ + ‖T⁻¹‖ * ‖T * G - 1‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ ‖G‖ + ‖T⁻¹‖ * ρ := by gcongr
  nlinarith [norm_nonneg T⁻¹, norm_nonneg G]

/-- `‖PP*‖ ≤ ‖P‖²`. -/
theorem opp_norm_mul_conjTranspose_le (P : Matrix n n ℂ) : ‖P * Pᴴ‖ ≤ ‖P‖ ^ 2 := by
  calc ‖P * Pᴴ‖ ≤ ‖P‖ * ‖Pᴴ‖ := l2_opNorm_mul _ _
    _ = ‖P‖ ^ 2 := by rw [l2_opNorm_conjTranspose]; ring

end MatrixFacts

/-- `|W⁻¹ Tr M| ≤ ‖M‖`. -/
theorem opp_norm_ntrace_le {W : ℕ} (hW : 0 < W) (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  have h := tfl_trace_le M
  rw [Fintype.card_fin] at h
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖M.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) := by gcongr
    _ = ‖M‖ := by field_simp

/-!
## 2. Ward identities for `(w - X)⁻¹`, `X` passive
-/

/-- `Im(w - X) = Im w + (-Im X)`. -/
theorem opp_matrixImaginaryPart_smul_one_sub {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (w : ℂ) :
    matrixImaginaryPart (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      w.im • (1 : Matrix (Fin W) (Fin W) ℂ) + onePortDissipation X := by
  ext i j
  simp only [matrixImaginaryPart, onePortDissipation, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, conjTranspose_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    apply Complex.ext
    · simp; ring
    · simp
  · have hji : ¬ j = i := fun h => hij h.symm
    simp only [hij, hji, ite_false]
    apply Complex.ext <;> simp <;> ring

/-- **Ward identity** for `Q = w - X`: `-Im Tr Q⁻¹ = Im w · Re Tr Q⁻¹Q⁻* + Re Tr Q⁻*(-Im X)Q⁻¹`
(from `-Im Q⁻¹ = Q⁻*(Im Q)Q⁻¹`). -/
theorem opp_neg_im_trace_inv {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (w : ℂ)
    (hQ : IsUnit (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det) :
    -((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹.trace).im =
      w.im * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ *
          (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ᴴ).trace.re +
        ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ᴴ * onePortDissipation X *
          (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace.re := by
  set Q := w • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hQdef
  have h := BlockBand.Transmission.neg_matrixImaginaryPart_nonsing_inv Q hQ
  rw [hQdef, opp_matrixImaginaryPart_smul_one_sub, ← hQdef] at h
  have ht := congrArg Matrix.trace h
  rw [BlockBand.Transmission.trace_neg_matrixImaginaryPart, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul] at ht
  have hre := congrArg Complex.re ht
  rw [Complex.ofReal_re, Complex.add_re, Complex.real_smul, Complex.re_ofReal_mul] at hre
  rw [Matrix.trace_mul_comm Q⁻¹ Q⁻¹ᴴ]
  linarith

/-- The dissipation term of the Ward identity is nonnegative. -/
theorem opp_dissipation_term_nonneg {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : IsPassiveInput X) (Q : Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ (Qᴴ * onePortDissipation X * Q).trace.re :=
  wl_trace_re_nonneg (hX.conjTranspose_mul_mul_same Q)

/-- `Re Tr MM* ≥ 0`. -/
theorem opp_trace_self_nonneg {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) :
    0 ≤ (M * Mᴴ).trace.re :=
  wl_trace_re_nonneg (posSemidef_self_mul_conjTranspose M)

/-- `z - X` is invertible for passive `X` and `Im z > 0`. -/
theorem opp_isUnit_det_resolvent {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    {z : ℂ} (hz : 0 < z.im) : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det := by
  have him : matrixImaginaryPart (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      onePortDissipation X + z.im • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [opp_matrixImaginaryPart_smul_one_sub, add_comm]
  obtain ⟨hu, -, -⟩ := BlockBand.Transmission.passive_inverse_constructed _ _ hz hX him
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

/-!
## 3. Scalar steps
-/

/-- Step 1: from `‖T̄Ḡ - I‖ ≤ ρ ≤ 1/2`, `‖Ḡ‖ ≤ C₀`: `T̄` invertible, `‖M̄‖ ≤ 2C₀` and
`|W⁻¹Tr Ḡ - W⁻¹Tr M̄| ≤ 2C₀ρ`. -/
theorem opp_step_top {W : ℕ} (hW : 0 < W) {T G : Matrix (Fin W) (Fin W) ℂ} {ρ C₀ : ℝ}
    (h : ‖T * G - 1‖ ≤ ρ) (hρ : ρ ≤ 1 / 2) (hG : ‖G‖ ≤ C₀) :
    IsUnit T.det ∧ ‖T⁻¹‖ ≤ 2 * C₀ ∧
      ‖(W : ℂ)⁻¹ * G.trace - (W : ℂ)⁻¹ * T⁻¹.trace‖ ≤ 2 * C₀ * ρ := by
  obtain ⟨hdet, hM⟩ := opp_inv_of_mul_near_one h hρ
  have hM' : ‖T⁻¹‖ ≤ 2 * C₀ := hM.trans (by linarith)
  have e : (W : ℂ)⁻¹ * G.trace - (W : ℂ)⁻¹ * T⁻¹.trace =
      (W : ℂ)⁻¹ * (T⁻¹ * (T * G - 1)).trace := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul,
      Matrix.mul_one, Matrix.trace_sub, mul_sub]
  refine ⟨hdet, hM', ?_⟩
  rw [e]
  calc _ ≤ ‖T⁻¹ * (T * G - 1)‖ := opp_norm_ntrace_le hW _
    _ ≤ ‖T⁻¹‖ * ‖T * G - 1‖ := norm_mul_le _ _
    _ ≤ (2 * C₀) * ρ := mul_le_mul hM' h (norm_nonneg _) (by linarith [norm_nonneg T⁻¹])

/-- Step 2: from `|g₂q - 1| ≤ ρ ≤ 1/2`, `|g₂| ≤ C₀`: `q ≠ 0`, `|q⁻¹| ≤ 2C₀`, `|g₂ - q⁻¹| ≤ 2C₀ρ`. -/
theorem opp_step_port {g₂ q : ℂ} {ρ C₀ : ℝ} (h : ‖g₂ * q - 1‖ ≤ ρ) (hρ : ρ ≤ 1 / 2)
    (hg : ‖g₂‖ ≤ C₀) : q ≠ 0 ∧ ‖q⁻¹‖ ≤ 2 * C₀ ∧ ‖g₂ - q⁻¹‖ ≤ 2 * C₀ * ρ := by
  have hq1 : 1 / 2 ≤ ‖g₂‖ * ‖q‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (g₂ * q)
    rw [norm_sub_rev, norm_one, norm_mul] at h1
    linarith
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hq1
    linarith
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hinv : ‖q⁻¹‖ ≤ 2 * C₀ := by
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ hqn]
    nlinarith [norm_nonneg g₂]
  have e : g₂ - q⁻¹ = (g₂ * q - 1) * q⁻¹ := by field_simp
  refine ⟨hq, hinv, ?_⟩
  rw [e, norm_mul]
  calc ‖g₂ * q - 1‖ * ‖q⁻¹‖ ≤ ρ * (2 * C₀) :=
        mul_le_mul h hinv (norm_nonneg _) (by linarith [norm_nonneg (g₂ * q - 1)])
    _ = 2 * C₀ * ρ := by ring

/-- `-Im q⁻¹ = |q⁻¹|² Im q`. -/
theorem opp_neg_im_inv {q : ℂ} : -(q⁻¹).im = ‖q⁻¹‖ ^ 2 * q.im := by
  rw [Complex.inv_im, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  ring

/-- The exact scalar identity behind the stability of the mean branch:
`(g₁ - a)(1 - (c + b²va)τ) = (φ - a) + (g₁ - m) + b(g₂ - v)τ` whenever `v(z - bg₁) = 1`,
`a(z - ba) = 1` and `m - φ = (c(g₁ - a) + b(g₂ - a))τ`. -/
theorem opp_scalar_identity {a z g₁ g₂ v m φ τ b c : ℂ}
    (hv : v * (z - b * g₁) = 1) (ha : a * (z - b * a) = 1)
    (hm : m - φ = (c * (g₁ - a) + b * (g₂ - a)) * τ) :
    (g₁ - a) * (1 - (c + b ^ 2 * v * a) * τ) = (φ - a) + (g₁ - m) + b * (g₂ - v) * τ := by
  linear_combination hm + τ * b * a * hv - τ * b * v * ha

/-- `v - a = bva(g₁ - a)` whenever `v(z - bg₁) = 1` and `a(z - ba) = 1`. -/
theorem opp_port_diff {a z g₁ v b : ℂ} (hv : v * (z - b * g₁) = 1) (ha : a * (z - b * a) = 1) :
    v - a = b * v * a * (g₁ - a) := by
  linear_combination a * hv - v * ha

/-- AM–GM form of the contraction bound: if `s² ≤ AB`, then
`(c + b²p)s ≤ ((c + b²p²)A + (c + b²)B)/2`. -/
theorem opp_contraction_amgm {c b p s A B : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (hs : 0 ≤ s)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : s ^ 2 ≤ A * B) :
    (c + b ^ 2 * p) * s ≤ ((c + b ^ 2 * p ^ 2) * A + (c + b ^ 2) * B) / 2 := by
  have h1 : s ≤ (A + B) / 2 := by
    have : s ^ 2 ≤ ((A + B) / 2) ^ 2 := by nlinarith [sq_nonneg (A - B)]
    exact (pow_le_pow_iff_left₀ hs (by positivity) two_ne_zero).mp this
  have h2 : p * s ≤ (p ^ 2 * A + B) / 2 := by
    have : (p * s) ^ 2 ≤ ((p ^ 2 * A + B) / 2) ^ 2 := by
      have hps : (p * s) ^ 2 = p ^ 2 * s ^ 2 := by ring
      rw [hps]
      nlinarith [sq_nonneg (p ^ 2 * A - B), sq_nonneg p, mul_le_mul_of_nonneg_left h (sq_nonneg p)]
    exact (pow_le_pow_iff_left₀ (mul_nonneg hp hs) (by positivity) two_ne_zero).mp this
  nlinarith [sq_nonneg b, mul_le_mul_of_nonneg_left h1 hc,
    mul_le_mul_of_nonneg_left h2 (sq_nonneg b)]

/-- Final arithmetic: `s ≤ 1 + c_sΔ`, `P ≤ 1 + c_PΔ`, `ρ ≤ Δ ≤ D` give
`sP² + ρ ≤ 1 + C₁Δ`. -/
theorem opp_final_arith {s P ρ Δ cs cP D : ℝ} (hP0 : 0 ≤ P) (hΔ : 0 ≤ Δ)
    (hcs : 0 ≤ cs) (hcP : 0 ≤ cP) (hs : s ≤ 1 + cs * Δ) (hP : P ≤ 1 + cP * Δ) (hρ : ρ ≤ Δ)
    (hD : Δ ≤ D) :
    s * P ^ 2 + ρ ≤
      1 + (cs + 2 * cP + (cP ^ 2 + 2 * cs * cP) * D + cs * cP ^ 2 * D ^ 2 + 1) * Δ := by
  have hP2 : P ^ 2 ≤ (1 + cP * Δ) ^ 2 := pow_le_pow_left₀ hP0 hP 2
  have h1 : s * P ^ 2 ≤ (1 + cs * Δ) * (1 + cP * Δ) ^ 2 :=
    mul_le_mul hs hP2 (sq_nonneg _) (by positivity)
  have hΔ2 : Δ ^ 2 ≤ D * Δ := by nlinarith
  have hΔ3 : Δ ^ 3 ≤ D ^ 2 * Δ := by nlinarith [mul_le_mul_of_nonneg_left hD hΔ]
  have e : (1 + cs * Δ) * (1 + cP * Δ) ^ 2 =
      1 + (cs + 2 * cP) * Δ + (cP ^ 2 + 2 * cs * cP) * Δ ^ 2 + cs * cP ^ 2 * Δ ^ 3 := by ring
  have h2 : (cP ^ 2 + 2 * cs * cP) * Δ ^ 2 ≤ (cP ^ 2 + 2 * cs * cP) * (D * Δ) :=
    mul_le_mul_of_nonneg_left hΔ2 (by positivity)
  have h3 : cs * cP ^ 2 * Δ ^ 3 ≤ cs * cP ^ 2 * (D ^ 2 * Δ) :=
    mul_le_mul_of_nonneg_left hΔ3 (by positivity)
  nlinarith

/-!
## 4. Normalized Ward identity, resolvent difference, Cauchy–Schwarz
-/

/-- **Normalized Ward identity**: for `Q = w - X` invertible and `X` passive,
`-Im W⁻¹Tr Q⁻¹ = Im w · A_{Q⁻¹} + y` with `y = W⁻¹ Re Tr Q⁻*(-Im X)Q⁻¹ ≥ 0`. -/
theorem opp_ward_normalized {W : ℕ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (w : ℂ) (hQ : IsUnit (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det) :
    ∃ y : ℝ, 0 ≤ y ∧
      -((W : ℂ)⁻¹ * (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹.trace).im =
        w.im * oppNTr (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ + y := by
  have h := opp_neg_im_trace_inv X w hQ
  set Q := w • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hQdef
  refine ⟨(W : ℝ)⁻¹ * (Q⁻¹ᴴ * onePortDissipation X * Q⁻¹).trace.re,
    mul_nonneg (by positivity) (opp_dissipation_term_nonneg hX _), ?_⟩
  have hWinv : ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [hWinv, Complex.im_ofReal_mul, oppNTr]
  have e : -((W : ℝ)⁻¹ * (Q⁻¹.trace).im) = (W : ℝ)⁻¹ * (-(Q⁻¹.trace).im) := by ring
  rw [e, h]
  ring

/-- Algebraic resolvent difference: if `K = T + d` with `T, K` invertible, then
`T⁻¹ - K⁻¹ = d T⁻¹K⁻¹` and `K T⁻¹ = I + d T⁻¹`. -/
theorem opp_inv_sub_inv {n : Type*} [Fintype n] [DecidableEq n] {T K : Matrix n n ℂ} {d : ℂ}
    (hKT : K = T + d • (1 : Matrix n n ℂ)) (hT : IsUnit T.det) (hK : IsUnit K.det) :
    T⁻¹ - K⁻¹ = d • (T⁻¹ * K⁻¹) ∧ K * T⁻¹ = 1 + d • T⁻¹ := by
  have hTM : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hT
  have hMT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul _ hT
  have hKR : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv _ hK
  refine ⟨?_, ?_⟩
  · have e : T⁻¹ * (K - T) * K⁻¹ = T⁻¹ - K⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, hKR, Matrix.mul_sub, Matrix.mul_one,
        ← Matrix.mul_assoc, hMT, Matrix.one_mul]
    rw [← e, hKT, add_sub_cancel_left, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  · rw [hKT, Matrix.add_mul, hTM, Matrix.smul_mul, Matrix.one_mul]

/-- **Resolvent difference**: for `T = w - X`, `K = z - X` invertible,
`W⁻¹Tr T⁻¹ - W⁻¹Tr K⁻¹ = (z - w) W⁻¹Tr T⁻¹K⁻¹` and `K T⁻¹ = I + (z - w)T⁻¹`. -/
theorem opp_resolvent_diff {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (w z : ℂ)
    (hT : IsUnit (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det)
    (hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X).det) :
    (W : ℂ)⁻¹ * (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹.trace -
        (W : ℂ)⁻¹ * (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹.trace =
      (z - w) * ((W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ *
        (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace) ∧
    (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ =
      1 + (z - w) • (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ := by
  have hKT : z • (1 : Matrix (Fin W) (Fin W) ℂ) - X =
      (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X) + (z - w) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [sub_smul]; abel
  obtain ⟨h1, h2⟩ := opp_inv_sub_inv hKT hT hK
  refine ⟨?_, h2⟩
  rw [← mul_sub, ← Matrix.trace_sub, h1, Matrix.trace_smul, smul_eq_mul]
  ring

/-- `|W⁻¹ Tr MR|² ≤ A_M A_R`. -/
theorem opp_ntrace_cs {W : ℕ} (M R : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * (M * R).trace‖ ^ 2 ≤ oppNTr M * oppNTr R := by
  have h1 := opp_norm_trace_mul_sq_le M R
  rw [norm_mul, mul_pow, oppNTr, oppNTr, norm_inv, Complex.norm_natCast]
  have h2 : ((W : ℝ)⁻¹) ^ 2 * ‖(M * R).trace‖ ^ 2 ≤
      ((W : ℝ)⁻¹) ^ 2 * ((M * Mᴴ).trace.re * (R * Rᴴ).trace.re) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  calc ((W : ℝ)⁻¹) ^ 2 * ‖(M * R).trace‖ ^ 2 ≤ _ := h2
    _ = (W : ℝ)⁻¹ * (M * Mᴴ).trace.re * ((W : ℝ)⁻¹ * (R * Rᴴ).trace.re) := by ring

/-- `A_M ≥ 0`. -/
theorem opp_nTr_nonneg {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ oppNTr M :=
  mul_nonneg (by positivity) (opp_trace_self_nonneg M)

/-!
## 5. Constants of the reduction (depending on `b, η₀, C₀` only)
-/

/-- `h₀ = (3 + C₀)⁻²`, the lower bound for `h = |v̄|²`. -/
def oppH0 (C₀ : ℝ) : ℝ := 1 / (3 + C₀) ^ 2

/-- `k₀ = 1 + 4C₀²`, the upper bound for `k = c + b²h`. -/
def oppK0 (C₀ : ℝ) : ℝ := 1 + 4 * C₀ ^ 2

/-- The admissible error size `ρ₀`. -/
def oppRho0 (b η₀ C₀ : ℝ) : ℝ :=
  min (1 / 2) (min (oppH0 C₀ / 2) (min (b * oppH0 C₀ / (2 * (oppK0 C₀ + 1)))
    (b * oppH0 C₀ * η₀ / (4 * (oppK0 C₀ + 1) * C₀))))

/-- `ε₀ = bh₀η₀/(2C₀)`, the lower bound for `1 - kA`. -/
def oppEps0 (b η₀ C₀ : ℝ) : ℝ := b * oppH0 C₀ * η₀ / (2 * C₀)

/-- Constant in `|ḡ₁ - a| ≤ c_x(δ₀ + ρ)`. -/
def oppCx (b C₀ : ℝ) : ℝ := 4 / b * (1 + 2 * C₀ * (1 + b / (1 - 2 * b)))

/-- Constant in `|Ω̄| ≤ c_Ω(δ₀ + ρ)`. -/
def oppCOmega (b C₀ : ℝ) : ℝ := (1 + 2 * C₀) * oppCx b C₀ + 2 * C₀

/-- Constant in `s ≤ 1 + c_s(δ₀ + ρ)`. -/
def oppCs (b η₀ C₀ : ℝ) : ℝ :=
  oppCOmega b C₀ / η₀ + (oppK0 C₀ + 1) / oppEps0 b η₀ C₀ +
    (oppK0 C₀ + 1) * (2 * C₀) / (η₀ * oppEps0 b η₀ C₀)

/-- Constant in `‖KM̄‖ ≤ 1 + c_P(δ₀ + ρ)`. -/
def oppCP (b C₀ : ℝ) : ℝ := 2 * C₀ * oppCOmega b C₀

/-- The bound `δ₀ + ρ ≤ bη₀/2 + 1/2` on the scalar domain. -/
def oppDmax (b η₀ : ℝ) : ℝ := b * η₀ / 2 + 1 / 2

/-- The final constant `C₁`. -/
def oppC1 (b η₀ C₀ : ℝ) : ℝ :=
  oppCs b η₀ C₀ + 2 * oppCP b C₀ +
    (oppCP b C₀ ^ 2 + 2 * oppCs b η₀ C₀ * oppCP b C₀) * oppDmax b η₀ +
    oppCs b η₀ C₀ * oppCP b C₀ ^ 2 * oppDmax b η₀ ^ 2 + 1

theorem opp_constants_pos {b η₀ C₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hη₀ : 0 < η₀)
    (hC₀ : 1 ≤ C₀) :
    0 < oppH0 C₀ ∧ 0 < oppK0 C₀ ∧ 0 < oppRho0 b η₀ C₀ ∧ 0 < oppEps0 b η₀ C₀ ∧
      0 ≤ oppCx b C₀ ∧ 0 ≤ oppCOmega b C₀ ∧ 0 ≤ oppCs b η₀ C₀ ∧ 0 ≤ oppCP b C₀ ∧
      0 ≤ oppDmax b η₀ ∧ 0 ≤ oppC1 b η₀ C₀ := by
  have hC0 : 0 < C₀ := by linarith
  have hc : 0 < 1 - 2 * b := by linarith
  have hH : 0 < oppH0 C₀ := by unfold oppH0; positivity
  have hK : 0 < oppK0 C₀ := by unfold oppK0; positivity
  have hE : 0 < oppEps0 b η₀ C₀ := by unfold oppEps0; positivity
  have hX : 0 ≤ oppCx b C₀ := by unfold oppCx; positivity
  have hO : 0 ≤ oppCOmega b C₀ := by unfold oppCOmega; positivity
  have hS : 0 ≤ oppCs b η₀ C₀ := by unfold oppCs; positivity
  have hP : 0 ≤ oppCP b C₀ := by unfold oppCP; positivity
  have hD : 0 ≤ oppDmax b η₀ := by unfold oppDmax; positivity
  refine ⟨hH, hK, ?_, hE, hX, hO, hS, hP, hD, by unfold oppC1; positivity⟩
  unfold oppRho0
  exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))

/-!
## 6. The scalar steps of the reduction
-/

/-- **Positivity step** (written at the layer means). With `k = c + b²h`:
the trace equations give `s(1 - kA) = bh + O(ρ)`, so `s > 0` forces `1 - kA > 0`; the exact
identity `σ(1 - kA) = bhη + ky - k Im ε₁ - b Im ε₂` (`y ≥ 0`) then gives `σ > 0`,
`1 - kA ≥ ε₀` and `ηs - σ ≤ C ρ / ε₀`. -/
theorem opp_step_positivity {b η₀ C₀ η h A s t₁ t₂ σ y ε₁i ε₂i ρ : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hη₀ : 0 < η₀) (hC₀ : 1 ≤ C₀) (hηE : η₀ ≤ η)
    (hh₀h : oppH0 C₀ ≤ h) (hhC : h ≤ 4 * C₀ ^ 2) (hy0 : 0 ≤ y) (ht₁ : 0 ≤ t₁)
    (hs : s = oppS b t₁ t₂) (e3 : |t₁ - s * A| ≤ ρ) (e4 : |t₂ - (1 + b * t₁) * h| ≤ ρ)
    (hρ : ρ ≤ oppRho0 b η₀ C₀)
    (hσid : σ * (1 - (1 - 2 * b + b ^ 2 * h) * A) =
      b * h * η + (1 - 2 * b + b ^ 2 * h) * y - (1 - 2 * b + b ^ 2 * h) * ε₁i - b * ε₂i)
    (hε₁i : |ε₁i| ≤ 2 * C₀ * ρ) (hε₂i : |ε₂i| ≤ 2 * C₀ * ρ) (hσC : σ ≤ C₀) :
    0 < s ∧ (1 - 2 * b + b ^ 2 * h) * A ≤ 1 ∧
      η * s - σ ≤
        (η * ((oppK0 C₀ + 1) * ρ) + (oppK0 C₀ + 1) * (2 * C₀ * ρ)) / oppEps0 b η₀ C₀ := by
  obtain ⟨hH0, hK0, -, hE0, -⟩ := opp_constants_pos hb0 hb1 hη₀ hC₀
  have hC0 : 0 < C₀ := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 1 - 2 * b + b ^ 2 * h := ⟨_, rfl⟩
  rw [← hk] at hσid ⊢
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : ℝ, h₀ = oppH0 C₀ := ⟨_, rfl⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℝ, k₀ = oppK0 C₀ := ⟨_, rfl⟩
  rw [← hh₀] at hh₀h hH0
  rw [← hk₀] at hK0 ⊢
  have hρ' : ρ ≤ min (1 / 2) (min (h₀ / 2) (min (b * h₀ / (2 * (k₀ + 1)))
      (b * h₀ * η₀ / (4 * (k₀ + 1) * C₀)))) := by rw [hh₀, hk₀]; exact hρ
  have hρ3 : ρ ≤ b * h₀ / (2 * (k₀ + 1)) :=
    hρ'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρ4 : ρ ≤ b * h₀ * η₀ / (4 * (k₀ + 1) * C₀) :=
    hρ'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hρ1 : ρ ≤ h₀ / 2 := hρ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh0 : 0 < h := lt_of_lt_of_le hH0 hh₀h
  have hη0 : 0 < η := lt_of_lt_of_le hη₀ hηE
  have hbh : 0 ≤ b ^ 2 * h := mul_nonneg (sq_nonneg b) hh0.le
  have hk0 : 0 ≤ k := by rw [hk]; linarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb0, hb1]
  have hkk₀ : k ≤ k₀ := by
    have : b ^ 2 * h ≤ 1 * (4 * C₀ ^ 2) := mul_le_mul hb2 hhC hh0.le (by norm_num)
    rw [hk, hk₀, oppK0]; linarith
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans e3
  have e3' := abs_le.mp e3
  have e4' := abs_le.mp e4
  have hsid : s * (1 - k * A) = b * h + k * (t₁ - s * A) + b * (t₂ - (1 + b * t₁) * h) := by
    rw [hs, oppS, hk]; ring
  have ht₂ : h - ρ ≤ t₂ := by
    have := mul_nonneg (mul_nonneg hb0.le ht₁) hh0.le
    linarith [e4'.1]
  have ht₂0 : 0 < t₂ := by linarith
  have hs0 : 0 < s := by
    rw [hs, oppS]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b) ht₁
    have := mul_pos hb0 ht₂0
    linarith
  have hkρ : (k₀ + 1) * ρ ≤ b * h₀ / 2 := by
    have := mul_le_mul_of_nonneg_left hρ3 (by linarith : (0 : ℝ) ≤ k₀ + 1)
    have e : (k₀ + 1) * (b * h₀ / (2 * (k₀ + 1))) = b * h₀ / 2 := by field_simp
    linarith
  have i4 : k * ρ ≤ k₀ * ρ := mul_le_mul_of_nonneg_right hkk₀ hρ0
  have i5 : b * ρ ≤ ρ := mul_le_of_le_one_left hρ0 (by linarith)
  have hpos : 0 < 1 - k * A := by
    have h1 : b * h₀ / 2 ≤ s * (1 - k * A) := by
      rw [hsid]
      have i1 : k * (-ρ) ≤ k * (t₁ - s * A) := mul_le_mul_of_nonneg_left e3'.1 hk0
      have i2 : b * (-ρ) ≤ b * (t₂ - (1 + b * t₁) * h) := mul_le_mul_of_nonneg_left e4'.1 hb0.le
      have i3 : b * h₀ ≤ b * h := mul_le_mul_of_nonneg_left hh₀h hb0.le
      linarith
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_left hn hs0.le
    have : 0 < b * h₀ := mul_pos hb0 hH0
    linarith
  have hb1' := abs_le.mp hε₁i
  have hb2' := abs_le.mp hε₂i
  have hkε : k * ε₁i ≤ k₀ * (2 * C₀ * ρ) :=
    (mul_le_mul_of_nonneg_left hb1'.2 hk0).trans
      (mul_le_mul_of_nonneg_right hkk₀ (by positivity))
  have hbε : b * ε₂i ≤ 1 * (2 * C₀ * ρ) :=
    (mul_le_mul_of_nonneg_left hb2'.2 hb0.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hbhη : b * h₀ * η₀ ≤ b * h * η := by
    have := mul_le_mul hh₀h hηE hη₀.le hh0.le
    have := mul_le_mul_of_nonneg_left this hb0.le
    linarith
  have hρ4' : (k₀ + 1) * (2 * C₀ * ρ) ≤ b * h₀ * η₀ / 2 := by
    have := mul_le_mul_of_nonneg_left hρ4 (by positivity : (0 : ℝ) ≤ (k₀ + 1) * (2 * C₀))
    have e : (k₀ + 1) * (2 * C₀) * (b * h₀ * η₀ / (4 * (k₀ + 1) * C₀)) = b * h₀ * η₀ / 2 := by
      field_simp; ring
    linarith
  have hky := mul_nonneg hk0 hy0
  have hσlow : b * h₀ * η₀ / 2 ≤ σ * (1 - k * A) := by
    rw [hσid]; linarith
  have hε₀kA : oppEps0 b η₀ C₀ ≤ 1 - k * A := by
    rw [oppEps0, ← hh₀, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hσC hpos.le
    linarith
  refine ⟨hs0, by linarith, ?_⟩
  have hD1 : (η * s - σ) * (1 - k * A) ≤ η * ((k₀ + 1) * ρ) + (k₀ + 1) * (2 * C₀ * ρ) := by
    have e : (η * s - σ) * (1 - k * A) =
        η * (k * (t₁ - s * A) + b * (t₂ - (1 + b * t₁) * h)) - k * y + k * ε₁i + b * ε₂i := by
      linear_combination η * hsid - hσid
    rw [e]
    have i1 : k * (t₁ - s * A) + b * (t₂ - (1 + b * t₁) * h) ≤ (k₀ + 1) * ρ := by
      have := mul_le_mul_of_nonneg_left e3'.2 hk0
      have := mul_le_mul_of_nonneg_left e4'.2 hb0.le
      linarith
    have := mul_le_mul_of_nonneg_left i1 hη0.le
    linarith
  rw [le_div_iff₀ hE0]
  by_cases hneg : η * s - σ ≤ 0
  · have := mul_le_mul_of_nonneg_right hneg hE0.le
    have : 0 ≤ η * ((k₀ + 1) * ρ) + (k₀ + 1) * (2 * C₀ * ρ) := by positivity
    linarith
  · push Not at hneg
    have := mul_le_mul_of_nonneg_left hε₀kA hneg.le
    linarith

/-- **Ward/Herglotz step**: `ηA_R ≤ -Im W⁻¹Tr R ≤ -Im a + δ₀ = η/(1-b) + δ₀`, hence
`(1-b)²A_R ≤ 1 - b/2` on `δ₀ ≤ bη₀/2`. -/
theorem opp_step_AR {b η₀ η AR yR δ : ℝ} {φ a : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hη₀ : 0 < η₀) (hηE : η₀ ≤ η) (hηa : η = -(1 - b) * a.im) (hφim : -φ.im = η * AR + yR)
    (hyR0 : 0 ≤ yR) (hδ : δ = ‖φ - a‖) (hδb : δ ≤ b * η₀ / 2) :
    (1 - b) ^ 2 * AR ≤ 1 - b / 2 := by
  have hη0 : 0 < η := lt_of_lt_of_le hη₀ hηE
  have hφa : -φ.im ≤ -a.im + δ := by
    have := (Complex.abs_im_le_norm (φ - a)).trans (le_of_eq hδ.symm)
    rw [Complex.sub_im] at this
    linarith [neg_abs_le (φ.im - a.im)]
  have h1 : η * AR ≤ -a.im + δ := by linarith
  have h2 : (1 - b) * (-a.im) = η := by rw [hηa]; ring
  have h3 : δ ≤ b * η / 2 := by
    have := mul_le_mul_of_nonneg_left hηE hb0.le
    linarith
  have key : η * ((1 - b) ^ 2 * AR) ≤ η * (1 - b / 2) := by
    have h4 : (1 - b) ^ 2 * (η * AR) ≤ (1 - b) ^ 2 * (-a.im + δ) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h5 : (1 - b) ^ 2 * δ ≤ δ := by
      have hd : 0 ≤ δ := by rw [hδ]; exact norm_nonneg _
      have : (1 - b) ^ 2 ≤ 1 := by nlinarith only [hb0, hb1]
      exact mul_le_of_le_one_left hd this
    have h6 : (1 - b) ^ 2 * (-a.im) = (1 - b) * η := by rw [← h2]; ring
    have h7 : (1 - b) * η + b * η / 2 = η * (1 - b / 2) := by ring
    have h8 : η * ((1 - b) ^ 2 * AR) = (1 - b) ^ 2 * (η * AR) := by ring
    rw [h8, ← h7]
    have h9 : (1 - b) ^ 2 * (-a.im + δ) = (1 - b) ^ 2 * (-a.im) + (1 - b) ^ 2 * δ := by ring
    linarith
  exact le_of_mul_le_mul_left key hη0

/-- **Stability step** (scalar fixed point, only `δ₀` small): from the scalar identity,
`|θ| ≤ 1 - b/4` and `|τ| ≤ 1/c`, `|Ω̄| ≤ c_Ω(δ₀ + ρ)`. -/
theorem opp_step_stability {b C₀ ρ δ A AR : ℝ} {a z g₁ g₂ v m φ τ : ℂ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hC₀ : 1 ≤ C₀) (hρ0 : 0 ≤ ρ)
    (hna : ‖a‖ = 1) (hza : a * (z - (b : ℂ) * a) = 1) (hvq : v * (z - (b : ℂ) * g₁) = 1)
    (hmφ : m - φ = ((1 - 2 * (b : ℂ)) * (g₁ - a) + (b : ℂ) * (g₂ - a)) * τ)
    (hε₁ : ‖g₁ - m‖ ≤ 2 * C₀ * ρ) (hε₂ : ‖g₂ - v‖ ≤ 2 * C₀ * ρ) (hnv : ‖v‖ ≤ 2 * C₀)
    (hA0 : 0 ≤ A) (hAR0 : 0 ≤ AR) (hτCS : ‖τ‖ ^ 2 ≤ A * AR)
    (hkA : (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * A ≤ 1) (hARb : (1 - b) ^ 2 * AR ≤ 1 - b / 2)
    (hδ : δ = ‖φ - a‖) :
    ‖(1 - 2 * (b : ℂ)) * (g₁ - a) + (b : ℂ) * (g₂ - a)‖ ≤ oppCOmega b C₀ * (δ + ρ) := by
  have hC0 : 0 < C₀ := by linarith
  set c : ℝ := 1 - 2 * b with hc
  have hc0 : 0 < c := by linarith
  have hcC : (1 - 2 * (b : ℂ)) = ((c : ℝ) : ℂ) := by rw [hc]; push_cast; ring
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact norm_nonneg _
  -- `|c + b²va| ≤ c + b²|v|`
  have hca : ‖(1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a‖ ≤ c + b ^ 2 * ‖v‖ := by
    calc _ ≤ ‖(1 - 2 * (b : ℂ))‖ + ‖(b : ℂ) ^ 2 * v * a‖ := norm_add_le _ _
      _ = c + b ^ 2 * ‖v‖ := by
          rw [hcC, Complex.norm_real, Real.norm_of_nonneg hc0.le, norm_mul, norm_mul, hna,
            norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le, mul_one]
  -- the contraction
  have hamgm := opp_contraction_amgm (b := b) hc0.le (norm_nonneg v) (norm_nonneg τ) hA0 hAR0 hτCS
  have hcb : c + b ^ 2 = (1 - b) ^ 2 := by rw [hc]; ring
  rw [hcb] at hamgm
  have hcontr : (c + b ^ 2 * ‖v‖) * ‖τ‖ ≤ 1 - b / 4 := by
    have : (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * A = (c + b ^ 2 * ‖v‖ ^ 2) * A := by rw [hc]
    linarith
  have hθ : ‖((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * τ‖ ≤ 1 - b / 4 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hca (norm_nonneg _)).trans hcontr
  have hτc : ‖τ‖ ≤ 1 / c := by
    rw [le_div_iff₀ hc0]
    have : 0 ≤ b ^ 2 * ‖v‖ * ‖τ‖ := by positivity
    have e : (c + b ^ 2 * ‖v‖) * ‖τ‖ = ‖τ‖ * c + b ^ 2 * ‖v‖ * ‖τ‖ := by ring
    linarith
  -- the scalar identity
  have hid := opp_scalar_identity (c := 1 - 2 * (b : ℂ)) hvq hza hmφ
  have h1θ : b / 4 ≤ ‖1 - ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * τ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * τ)
    rw [norm_one] at this
    linarith
  have hxb : ‖g₁ - a‖ * (b / 4) ≤ δ + 2 * C₀ * ρ + b * (2 * C₀ * ρ) * (1 / c) := by
    have h1 : ‖g₁ - a‖ * ‖1 - ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * τ‖ =
        ‖(φ - a) + (g₁ - m) + (b : ℂ) * (g₂ - v) * τ‖ := by rw [← norm_mul, hid]
    have h2 : ‖(φ - a) + (g₁ - m) + (b : ℂ) * (g₂ - v) * τ‖ ≤
        δ + 2 * C₀ * ρ + b * (2 * C₀ * ρ) * (1 / c) := by
      calc _ ≤ ‖φ - a‖ + ‖g₁ - m‖ + ‖(b : ℂ) * (g₂ - v) * τ‖ := norm_add₃_le
        _ ≤ δ + 2 * C₀ * ρ + b * (2 * C₀ * ρ) * (1 / c) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
            gcongr
            exact le_of_eq hδ.symm
    calc ‖g₁ - a‖ * (b / 4) ≤ ‖g₁ - a‖ * ‖1 - ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * τ‖ :=
          mul_le_mul_of_nonneg_left h1θ (norm_nonneg _)
      _ ≤ _ := h1.le.trans h2
  have hxc : ‖g₁ - a‖ ≤ oppCx b C₀ * (δ + ρ) := by
    have hb4 : 0 < b / 4 := by positivity
    have h1 : ‖g₁ - a‖ ≤ (δ + 2 * C₀ * ρ + b * (2 * C₀ * ρ) * (1 / c)) / (b / 4) :=
      (le_div_iff₀ hb4).mpr hxb
    refine h1.trans ?_
    rw [div_le_iff₀ hb4, oppCx, ← hc]
    have e : 4 / b * (1 + 2 * C₀ * (1 + b / c)) * (δ + ρ) * (b / 4) =
        (1 + 2 * C₀ * (1 + b / c)) * (δ + ρ) := by field_simp
    rw [e]
    have : 0 ≤ 2 * C₀ * (1 + b / c) * δ := by positivity
    have e2 : b * (2 * C₀ * ρ) * (1 / c) = 2 * C₀ * (b / c) * ρ := by ring
    rw [e2]
    have e3 : (1 + 2 * C₀ * (1 + b / c)) * (δ + ρ) =
        δ + 2 * C₀ * ρ + 2 * C₀ * (b / c) * ρ + (ρ + 2 * C₀ * (1 + b / c) * δ) := by ring
    rw [e3]
    linarith
  -- `Ω̄ = (c + b²va)(ḡ₁ - a) + b ε₂`
  have hΩx : (1 - 2 * (b : ℂ)) * (g₁ - a) + (b : ℂ) * (g₂ - a) =
      ((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * (g₁ - a) + (b : ℂ) * (g₂ - v) := by
    have hpd := opp_port_diff hvq hza
    linear_combination (b : ℂ) * hpd
  rw [hΩx]
  have hcv : c + b ^ 2 * ‖v‖ ≤ 1 + 2 * C₀ := by
    have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb0, hb1]
    have : b ^ 2 * ‖v‖ ≤ 1 * (2 * C₀) := mul_le_mul hb2 hnv (norm_nonneg _) (by norm_num)
    linarith
  calc _ ≤ ‖((1 - 2 * (b : ℂ)) + (b : ℂ) ^ 2 * v * a) * (g₁ - a)‖ + ‖(b : ℂ) * (g₂ - v)‖ :=
        norm_add_le _ _
    _ ≤ (1 + 2 * C₀) * (oppCx b C₀ * (δ + ρ)) + 1 * (2 * C₀ * ρ) := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
        gcongr
        · exact hca.trans hcv
        · linarith
    _ ≤ oppCOmega b C₀ * (δ + ρ) := by
        rw [oppCOmega]
        have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * C₀) hδ0
        have e : ((1 + 2 * C₀) * oppCx b C₀ + 2 * C₀) * (δ + ρ) =
            (1 + 2 * C₀) * (oppCx b C₀ * (δ + ρ)) + 1 * (2 * C₀ * ρ) + 2 * C₀ * δ := by ring
        rw [e]; linarith

/-- **The `s` step**: `s ≤ σ/η + Cρ/ε₀` and `σ ≤ η + |Ω̄|` give `s ≤ 1 + c_s(δ₀ + ρ)`. -/
theorem opp_step_s {b η₀ C₀ η s σ ρ δ Ωn : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hη₀ : 0 < η₀)
    (hC₀ : 1 ≤ C₀) (hηE : η₀ ≤ η) (hρ0 : 0 ≤ ρ) (hδ0 : 0 ≤ δ)
    (hD : η * s - σ ≤
      (η * ((oppK0 C₀ + 1) * ρ) + (oppK0 C₀ + 1) * (2 * C₀ * ρ)) / oppEps0 b η₀ C₀)
    (hσ : σ ≤ η + Ωn) (hΩ : Ωn ≤ oppCOmega b C₀ * (δ + ρ)) :
    s ≤ 1 + oppCs b η₀ C₀ * (δ + ρ) := by
  obtain ⟨-, hK0, -, hE0, -, hO0, -⟩ := opp_constants_pos hb0 hb1 hη₀ hC₀
  have hC0 : 0 < C₀ := by linarith
  have hη0 : 0 < η := lt_of_lt_of_le hη₀ hηE
  set k₀ := oppK0 C₀
  set ε₀ := oppEps0 b η₀ C₀
  set cΩ := oppCOmega b C₀
  have hs' : s ≤ 1 + (cΩ * (δ + ρ)) / η + ((k₀ + 1) * ρ) / ε₀ +
      (k₀ + 1) * (2 * C₀ * ρ) / (η * ε₀) := by
    have : η * s ≤ η * (1 + (cΩ * (δ + ρ)) / η + ((k₀ + 1) * ρ) / ε₀ +
        (k₀ + 1) * (2 * C₀ * ρ) / (η * ε₀)) := by
      have e : η * (1 + (cΩ * (δ + ρ)) / η + ((k₀ + 1) * ρ) / ε₀ +
          (k₀ + 1) * (2 * C₀ * ρ) / (η * ε₀)) =
          η + cΩ * (δ + ρ) + (η * ((k₀ + 1) * ρ) + (k₀ + 1) * (2 * C₀ * ρ)) / ε₀ := by
        field_simp
        ring
      rw [e]; linarith
    exact le_of_mul_le_mul_left this hη0
  refine hs'.trans ?_
  rw [oppCs]
  have i1 : cΩ * (δ + ρ) / η ≤ cΩ * (δ + ρ) / η₀ :=
    div_le_div_of_nonneg_left (by positivity) hη₀ hηE
  have i2 : (k₀ + 1) * (2 * C₀ * ρ) / (η * ε₀) ≤ (k₀ + 1) * (2 * C₀ * ρ) / (η₀ * ε₀) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hηE hE0.le)
  have e : (cΩ / η₀ + (k₀ + 1) / ε₀ + (k₀ + 1) * (2 * C₀) / (η₀ * ε₀)) * (δ + ρ) =
      cΩ * (δ + ρ) / η₀ + (k₀ + 1) * (δ + ρ) / ε₀ +
        (k₀ + 1) * (2 * C₀ * (δ + ρ)) / (η₀ * ε₀) := by ring
  rw [e]
  have i3 : (k₀ + 1) * ρ / ε₀ ≤ (k₀ + 1) * (δ + ρ) / ε₀ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hE0.le
  have i4 : (k₀ + 1) * (2 * C₀ * ρ) / (η₀ * ε₀) ≤
      (k₀ + 1) * (2 * C₀ * (δ + ρ)) / (η₀ * ε₀) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)) (by positivity)
  linarith

/-!
## 7. The deterministic reduction
-/

/-- **Deterministic core of the passive mean** (written at the layer means). Let
`b ∈ (0,1/2)`, `η₀ > 0`, `C₀ ≥ 1`, `W ≥ 1`, `|E| ≤ 2` with `Im z_∂(E) ≥ η₀`, `X` passive with
`δ₀ = onePortDistance b E X ≤ bη₀/2`, and `Ḡ, ḡ₂, t₁ ≥ 0, t₂, U` with `‖Ḡ‖, |ḡ₂| ≤ C₀` satisfying
the five relations of `OppPassiveMeanEquations` with error `ρ ∈ [0, ρ₀]` (at `ḡ₁ = W⁻¹ Tr Ḡ`).
Then `‖U‖ ≤ 1 + C₁(δ₀ + ρ)`, `ρ₀ = oppRho0 b η₀ C₀`, `C₁ = oppC1 b η₀ C₀`. Uniform in `X`: no
bound on `‖X‖` or on `-Im X` is assumed. -/
theorem opp_core_bound {b η₀ C₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hη₀ : 0 < η₀)
    (hC₀ : 1 ≤ C₀) {W : ℕ} (hW : 0 < W) {E : ℝ} (hE : |E| ≤ 2)
    (hηE : η₀ ≤ (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ} (hX : IsPassiveInput X)
    (hδ : onePortDistance b E X ≤ b * η₀ / 2)
    {G U : Matrix (Fin W) (Fin W) ℂ} {g₂ : ℂ} {t₁ t₂ ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ oppRho0 b η₀ C₀) (hG : ‖G‖ ≤ C₀) (hg₂ : ‖g₂‖ ≤ C₀) (ht₁ : 0 ≤ t₁)
    (e1 : ‖oppTopMatrix b E X ((W : ℂ)⁻¹ * G.trace) g₂ * G - 1‖ ≤ ρ)
    (e2 : ‖g₂ * (boundaryZ b E - (b : ℂ) * ((W : ℂ)⁻¹ * G.trace)) - 1‖ ≤ ρ)
    (e3 : |t₁ - oppS b t₁ t₂ * oppNTr (oppTopMatrix b E X ((W : ℂ)⁻¹ * G.trace) g₂)⁻¹| ≤ ρ)
    (e4 : |t₂ - (1 + b * t₁) * ‖oppPortV b E ((W : ℂ)⁻¹ * G.trace)‖ ^ 2| ≤ ρ)
    (e5 : ‖U - ((oppS b t₁ t₂ : ℝ) : ℂ) •
          (((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
              (oppTopMatrix b E X ((W : ℂ)⁻¹ * G.trace) g₂)⁻¹) *
            ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) *
              (oppTopMatrix b E X ((W : ℂ)⁻¹ * G.trace) g₂)⁻¹)ᴴ)‖ ≤ ρ) :
    ‖U‖ ≤ 1 + oppC1 b η₀ C₀ * (onePortDistance b E X + ρ) := by
  obtain ⟨-, -, -, -, -, hO0, hS0, hP0, -, -⟩ := opp_constants_pos hb0 hb1 hη₀ hC₀
  have hC0 : 0 < C₀ := by linarith
  have hρ1 : ρ ≤ 1 / 2 := hρ.trans (min_le_left _ _)
  have hδ0 : 0 ≤ onePortDistance b E X := norm_nonneg _
  -- abbreviations
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ℂ, g₁ = (W : ℂ)⁻¹ * G.trace := ⟨_, rfl⟩
  rw [← hg₁] at e1 e2 e3 e4 e5
  have hng₁ : ‖g₁‖ ≤ C₀ := by rw [hg₁]; exact (opp_norm_ntrace_le hW G).trans hG
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = -(E : ℂ) - (1 - 2 * (b : ℂ)) * g₁ - (b : ℂ) * g₂ := ⟨_, rfl⟩
  have hTw : oppTopMatrix b E X g₁ g₂ = w • (1 : Matrix (Fin W) (Fin W) ℂ) - X := by
    rw [hw]; rfl
  rw [hTw] at e1 e3 e5
  -- Step 1 (top block) and Step 2 (port block)
  obtain ⟨hTu, hnM, hε₁⟩ := opp_step_top hW e1 hρ1 hG
  rw [← hg₁] at hε₁
  obtain ⟨hq0, hnv, hε₂⟩ := opp_step_port e2 hρ1 hg₂
  have hvdef : oppPortV b E g₁ = (boundaryZ b E - (b : ℂ) * g₁)⁻¹ := rfl
  rw [hvdef] at e4
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = (boundaryZ b E - (b : ℂ) * g₁)⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hnv hε₂ e4
  have hvq : v * (boundaryZ b E - (b : ℂ) * g₁) = 1 := by rw [hv]; exact inv_mul_cancel₀ hq0
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin W) (Fin W) ℂ, M = (w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hM] at hnM hε₁ e3 e5
  -- the matched point
  have hna : ‖matchedA E‖ = 1 := norm_matchedA hE
  have ha0 : matchedA E ≠ 0 := by intro h; rw [h, norm_zero] at hna; norm_num at hna
  have hza : matchedA E * (boundaryZ b E - (b : ℂ) * matchedA E) = 1 := by
    rw [boundaryZ, add_sub_cancel_right, mul_inv_cancel₀ ha0]
  have hzE : boundaryZ b E = -(E : ℂ) - (1 - (b : ℂ)) * matchedA E := boundaryZ_eq hE
  have hηa : (boundaryZ b E).im = -(1 - b) * (matchedA E).im := boundaryZ_im hE
  have hη0 : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ hηE
  -- bounds on `h = |v̄|²`
  have hnz : ‖boundaryZ b E‖ ≤ 3 := norm_boundaryZ_le hb0.le (by linarith) hE
  have hnq : ‖boundaryZ b E - (b : ℂ) * g₁‖ ≤ 3 + C₀ := by
    have hbg : ‖(b : ℂ) * g₁‖ ≤ C₀ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
      calc b * ‖g₁‖ ≤ 1 * C₀ := mul_le_mul (by linarith) hng₁ (norm_nonneg _) (by norm_num)
        _ = C₀ := one_mul _
    calc _ ≤ ‖boundaryZ b E‖ + ‖(b : ℂ) * g₁‖ := norm_sub_le _ _
      _ ≤ 3 + C₀ := add_le_add hnz hbg
  have hhv : ‖v‖ ^ 2 = 1 / ‖boundaryZ b E - (b : ℂ) * g₁‖ ^ 2 := by
    rw [hv, norm_inv, inv_pow, one_div]
  have hh₀h : oppH0 C₀ ≤ ‖v‖ ^ 2 := by
    rw [hhv, oppH0]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hnq 2)
  have hhC : ‖v‖ ^ 2 ≤ 4 * C₀ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg v) hnv 2
    have e : (2 * C₀) ^ 2 = 4 * C₀ ^ 2 := by ring
    linarith
  -- Step 3: Ward identities and the resolvent difference
  have hKu := opp_isUnit_det_resolvent hX hη0
  obtain ⟨y, hy0, hmim⟩ := opp_ward_normalized hX w hTu
  obtain ⟨yR, hyR0, hφim⟩ := opp_ward_normalized hX (boundaryZ b E) hKu
  obtain ⟨hmφ, hKM⟩ := opp_resolvent_diff X w (boundaryZ b E) hTu hKu
  rw [← hM] at hmim hmφ hKM
  have hzw : boundaryZ b E - w =
      (1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E) := by
    rw [hw, hzE]; ring
  rw [hzw] at hmφ hKM
  -- Step 4: the imaginary parts
  have hσe : w.im = (1 - 2 * b) * (-g₁.im) + b * (-g₂.im) := by
    rw [hw]; simp [Complex.mul_im]; ring
  have hσΩ : w.im = (boundaryZ b E).im -
      ((1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E)).im := by
    rw [← hzw]; simp
  have hu₁e : -g₁.im = w.im * oppNTr M + y - (g₁ - (W : ℂ)⁻¹ * M.trace).im := by
    have : g₁.im = ((W : ℂ)⁻¹ * M.trace).im + (g₁ - (W : ℂ)⁻¹ * M.trace).im := by
      rw [← Complex.add_im]; ring_nf
    linarith
  have hvim : -v.im = ‖v‖ ^ 2 * (boundaryZ b E - (b : ℂ) * g₁).im := by
    rw [hv]; exact opp_neg_im_inv
  have hqim : (boundaryZ b E - (b : ℂ) * g₁).im = (boundaryZ b E).im + b * (-g₁.im) := by
    simp [Complex.mul_im]; ring
  have hu₂e : -g₂.im = ‖v‖ ^ 2 * ((boundaryZ b E).im + b * (-g₁.im)) - (g₂ - v).im := by
    have : g₂.im = v.im + (g₂ - v).im := by rw [← Complex.add_im]; ring_nf
    rw [← hqim]; linarith
  have hσid : w.im * (1 - (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * oppNTr M) =
      b * ‖v‖ ^ 2 * (boundaryZ b E).im + (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * y -
        (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * (g₁ - (W : ℂ)⁻¹ * M.trace).im - b * (g₂ - v).im := by
    linear_combination hσe + (1 - 2 * b + b ^ 2 * ‖v‖ ^ 2) * hu₁e + b * hu₂e
  have hε₁i : |(g₁ - (W : ℂ)⁻¹ * M.trace).im| ≤ 2 * C₀ * ρ :=
    (Complex.abs_im_le_norm _).trans hε₁
  have hε₂i : |(g₂ - v).im| ≤ 2 * C₀ * ρ := (Complex.abs_im_le_norm _).trans hε₂
  have hσC : w.im ≤ C₀ := by
    rw [hσe]
    have h1 : -g₁.im ≤ C₀ := (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans hng₁)
    have h2 : -g₂.im ≤ C₀ := (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans hg₂)
    have i1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - 2 * b)
    have i2 := mul_le_mul_of_nonneg_left h2 hb0.le
    nlinarith only [i1, i2, hb0, hC0]
  -- Step 5: positivity; Step 6: `A_R`; Step 7: Cauchy–Schwarz; Step 8–12: stability
  obtain ⟨hs0, hkA, hD⟩ := opp_step_positivity hb0 hb1 hη₀ hC₀ hηE hh₀h hhC hy0 ht₁ rfl e3 e4
    hρ hσid hε₁i hε₂i hσC
  have hARb := opp_step_AR hb0 hb1 hη₀ hηE hηa hφim hyR0 rfl hδ
  have hτCS := opp_ntrace_cs M (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹
  have hΩ := opp_step_stability hb0 hb1 hC₀ hρ0 hna hza hvq hmφ hε₁ hε₂ hnv (opp_nTr_nonneg M)
    (opp_nTr_nonneg _) hτCS hkA hARb rfl
  -- Step 13: `s`
  have hσle : w.im ≤ (boundaryZ b E).im +
      ‖(1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E)‖ := by
    rw [hσΩ]
    linarith [neg_abs_le ((1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E)).im,
      Complex.abs_im_le_norm ((1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E))]
  have hsb := opp_step_s hb0 hb1 hη₀ hC₀ hηE hρ0 hδ0 hD hσle hΩ
  -- Step 14: `KM̄ = I + Ω̄M̄`
  have hPb : ‖(boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M‖ ≤
      1 + oppCP b C₀ * (onePortDistance b E X + ρ) := by
    rw [hKM]
    calc _ ≤ ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ +
          ‖(1 - 2 * (b : ℂ)) * (g₁ - matchedA E) + (b : ℂ) * (g₂ - matchedA E)‖ * ‖M‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_smul_le _ _)
      _ ≤ 1 + (oppCOmega b C₀ * (onePortDistance b E X + ρ)) * (2 * C₀) :=
          add_le_add lct_norm_one_le
            (mul_le_mul hΩ hnM (norm_nonneg _) (mul_nonneg hO0 (add_nonneg hδ0 hρ0)))
      _ = 1 + oppCP b C₀ * (onePortDistance b E X + ρ) := by rw [oppCP]; ring
  -- Step 15–16: conclusion
  have hU : ‖U‖ ≤ oppS b t₁ t₂ *
      ‖(boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M‖ ^ 2 + ρ := by
    have h1 := norm_sub_norm_le U (((oppS b t₁ t₂ : ℝ) : ℂ) •
      (((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M) *
        ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M)ᴴ))
    have h2 : ‖((oppS b t₁ t₂ : ℝ) : ℂ) •
        (((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M) *
          ((boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M)ᴴ)‖ ≤
        oppS b t₁ t₂ * ‖(boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * M‖ ^ 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hs0.le]
      exact mul_le_mul_of_nonneg_left (opp_norm_mul_conjTranspose_le _) hs0.le
    linarith
  have hΔD : onePortDistance b E X + ρ ≤ oppDmax b η₀ := by rw [oppDmax]; linarith
  have := opp_final_arith (norm_nonneg _) (add_nonneg hδ0 hρ0) hS0 hP0 hsb hPb
    (by linarith : ρ ≤ onePortDistance b E X + ρ) hΔD
  rw [oppC1]
  linarith

end BlockBand.Layers
