module

public import BlockBand.Palm.MomentFlow.AvgDyson
public import BlockBand.Palm.MomentFlow.EventHeightDet

/-!
# Averaged local law along the flow: deterministic ingredients

* `resolvent_quad_norm_compare`: `|v*((H - z)⁻¹ - (H' - z)⁻¹)v| ≤ ‖H - H'‖ ‖v‖²/(Im z)²`
  (operator norm `opB`).
* `norm_normalizedTrace_le_of_diag`: `|⟨A⟩| ≤ B` if every diagonal entry has `|A_kk| ≤ B`.
* `normalizedTrace_resolvent_compare`: `|⟨(H - z)⁻¹⟩ - ⟨(H' - z)⁻¹⟩| ≤ ‖H - H'‖/(Im z)²`.
* `normalizedTrace_resolvent_lipschitz`: `|⟨(H - z)⁻¹⟩ - ⟨(H - z')⁻¹⟩| ≤ |z - z'|/y²` for
  `Im z, Im z' ≥ y > 0`.
* `averagedControl_one_le`: the averaged control of the external local law with `B = 1` is at most
  `1/(N |Im z|)` (`⟨Γ_M⟩ ∈ {0, 1}`, `‖1‖_HS = 1`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm BlockBand.Palm.CoarseRelative
open BlockBand.Palm.GoodEvent BlockBand.External
open scoped ComplexConjugate

variable {N : ℕ}

/-- Norm version of `resolvent_quad_im_compare`. -/
theorem resolvent_quad_norm_compare {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {z : ℂ} (hz : 0 < z.im) (q : Fin N → ℂ) :
    ‖star q ⬝ᵥ (((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q)‖ ≤
      opB (H - H') * nsq q / z.im ^ 2 := by
  set X := H - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  set X' := H' - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hu := hermitian_shift_det_isUnit hH hz.ne'
  have hu' := hermitian_shift_det_isUnit hH' hz.ne'
  have hid : X⁻¹ - X'⁻¹ = X⁻¹ * (H' - H) * X'⁻¹ := by
    have e : H' - H = X' - X := by simp only [X, X']; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
  have hX : star q ⬝ᵥ ((X⁻¹ * (H' - H) * X'⁻¹) *ᵥ q) =
      star ((X⁻¹)ᴴ *ᵥ q) ⬝ᵥ ((H' - H) *ᵥ (X'⁻¹ *ᵥ q)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hXc : (X⁻¹)ᴴ = (H - (conj z) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ :=
    hermitian_resolvent_conjTranspose hH z
  have hzc : (conj z).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.2 hz.ne'
  have hb1 : l2Norm ((X⁻¹)ᴴ *ᵥ q) ≤ l2Norm q / z.im := by
    rw [hXc]
    have := l2Norm_resolvent_le hH hzc q
    rwa [Complex.conj_im, abs_neg, abs_of_pos hz] at this
  have hb2 : l2Norm (X'⁻¹ *ᵥ q) ≤ l2Norm q / z.im := by
    have := l2Norm_resolvent_le hH' hz.ne' q
    rwa [abs_of_pos hz] at this
  have hD : l2Norm ((H' - H) *ᵥ (X'⁻¹ *ᵥ q)) ≤ opB (H - H') * (l2Norm q / z.im) := by
    have := l2Norm_mulVec_le (H' - H) (X'⁻¹ *ᵥ q)
    rw [show H' - H = -(H - H') by abel, opB_neg] at this
    rw [show H' - H = -(H - H') by abel]
    exact this.trans (mul_le_mul_of_nonneg_left hb2 (opB_nonneg _))
  rw [hid, hX]
  refine (norm_dotProduct_le_l2 _ _).trans ?_
  have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
  have hl2 : l2Norm q * l2Norm q = nsq q := by
    rw [l2Norm_eq_sqrt_nsq]; exact Real.mul_self_sqrt hnn
  calc l2Norm ((X⁻¹)ᴴ *ᵥ q) * l2Norm ((H' - H) *ᵥ (X'⁻¹ *ᵥ q))
      ≤ (l2Norm q / z.im) * (opB (H - H') * (l2Norm q / z.im)) :=
        mul_le_mul hb1 hD (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hz.le)
    _ = opB (H - H') * nsq q / z.im ^ 2 := by rw [← hl2]; field_simp

theorem diag_eq_quad (A : Matrix (Fin N) (Fin N) ℂ) (k : Fin N) :
    A k k = star (Pi.single k (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single k (1 : ℂ)) := by
  classical
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

theorem nsq_single (k : Fin N) : nsq (Pi.single k (1 : ℂ)) = 1 := by
  classical
  unfold nsq
  rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem norm_normalizedTrace_le_of_diag (hN : 0 < N) {A : Matrix (Fin N) (Fin N) ℂ} {B : ℝ}
    (hA : ∀ k, ‖A k k‖ ≤ B) : ‖CEH.normalizedTrace A‖ ≤ B := by
  unfold CEH.normalizedTrace
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_mul, norm_inv, Complex.norm_natCast, Matrix.trace]
  have h : ‖∑ k, A.diag k‖ ≤ N * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖A.diag k‖ ≤ ∑ _k : Fin N, B := Finset.sum_le_sum fun k _ => hA k
      _ = N * B := by simp
  calc (N : ℝ)⁻¹ * ‖∑ k, A.diag k‖ ≤ (N : ℝ)⁻¹ * (N * B) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = B := by field_simp

/-- `|⟨(H - z)⁻¹⟩ - ⟨(H' - z)⁻¹⟩| ≤ ‖H - H'‖/(Im z)²`. -/
theorem normalizedTrace_resolvent_compare (hN : 0 < N) {H H' : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {z : ℂ} (hz : 0 < z.im) :
    ‖CEH.normalizedTrace ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
        CEH.normalizedTrace ((H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)‖ ≤
      opB (H - H') / z.im ^ 2 := by
  have e : CEH.normalizedTrace ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
      CEH.normalizedTrace ((H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) =
      CEH.normalizedTrace ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) := by
    unfold CEH.normalizedTrace; rw [Matrix.trace_sub, mul_sub]
  rw [e]
  refine norm_normalizedTrace_le_of_diag hN fun k => ?_
  rw [diag_eq_quad ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
    (H' - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) k]
  have := resolvent_quad_norm_compare hH hH' hz (Pi.single k (1 : ℂ))
  rwa [nsq_single, mul_one] at this

/-- `|⟨(H - z)⁻¹⟩ - ⟨(H - z')⁻¹⟩| ≤ |z - z'|/y²` for `Im z, Im z' ≥ y > 0`. -/
theorem normalizedTrace_resolvent_lipschitz (hN : 0 < N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hH : H.IsHermitian) {y : ℝ} (hy : 0 < y) {z z' : ℂ} (hz : y ≤ z.im) (hz' : y ≤ z'.im) :
    ‖CEH.normalizedTrace ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
        CEH.normalizedTrace ((H - z' • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)‖ ≤
      ‖z - z'‖ / y ^ 2 := by
  have h := resolvent_trace_lipschitz hH hN hy hz hz'
  rw [inv_pow, ← div_eq_mul_inv] at h
  exact h

/-- CEH's averaged control at `B = 1` is at most `1/(N |Im z|)`. -/
theorem averagedControl_one_le (hN : 0 < N) (M : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    CEH.averagedControl M 1 z ≤ 1 / ((N : ℝ) * |z.im|) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : CEH.normalizedTrace (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold CEH.normalizedTrace
    rw [Matrix.trace_one, Fintype.card_fin]
    have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hHS : CEH.normalizedHilbertSchmidt (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold CEH.normalizedHilbertSchmidt
    rw [Matrix.conjTranspose_one, Matrix.mul_one, h1, Complex.one_re, Real.sqrt_one]
  have hΓ : (CEH.normalizedTrace (CEH.gammaMatrix M)).re ≤ 1 := by
    unfold CEH.gammaMatrix
    have e : CEH.normalizedTrace ((CEH.normalizedTrace (CEH.imaginaryPart M))⁻¹ •
        CEH.imaginaryPart M) = (CEH.normalizedTrace (CEH.imaginaryPart M))⁻¹ *
          CEH.normalizedTrace (CEH.imaginaryPart M) := by
      unfold CEH.normalizedTrace
      rw [Matrix.trace_smul, smul_eq_mul]; ring
    rw [e]
    by_cases h0 : CEH.normalizedTrace (CEH.imaginaryPart M) = 0
    · rw [h0]; simp
    · rw [inv_mul_cancel₀ h0, Complex.one_re]
  unfold CEH.averagedControl
  simp only [Matrix.conjTranspose_one, Matrix.mul_one]
  rw [hHS, h1, Complex.one_re, div_one]
  have hs : Real.sqrt ((CEH.normalizedTrace (CEH.gammaMatrix M)).re) ≤ 1 :=
    Real.sqrt_le_one.2 hΓ
  have h0 : 0 ≤ 1 / ((N : ℝ) * |z.im|) := by positivity
  calc 1 / ((N : ℝ) * |z.im|) * Real.sqrt ((CEH.normalizedTrace (CEH.gammaMatrix M)).re)
      ≤ 1 / ((N : ℝ) * |z.im|) * 1 := mul_le_mul_of_nonneg_left hs h0
    _ = 1 / ((N : ℝ) * |z.im|) := mul_one _

end BlockBand.Palm.MomentFlow
