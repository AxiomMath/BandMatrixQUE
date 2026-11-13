module

public import BlockBand.Layers.StrictContraction

/-!
# Comparison solution of the two-port mean equations: existence, stability, branch

The deterministic comparison solution of the two-port Dyson equation near the matched point, the
uniformly bounded inverse of the difference equations, and the identification of the branch
selected by the layer means (from the proof of the layer-contraction lemma).

Setting (all statements deterministic, uniform in `W` and in the Hermitian two-port
`X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ`; constants chosen from `b ∈ (0, 1/2)` and the bulk
margin `κ > 0` first): `a = matchedA E`, `z_∂ = boundaryZ b E`, `z₀ = commonZ b E`, `c = 1 - 2b`,
`R = (z_∂ - X)⁻¹`, `d(X) = matchedDistance b E X`. Norms: complex modulus on `ℂ`, the sup norm on
`Fin 2 → ℂ` (`‖r‖ = max_i |r_i|`), Euclidean length `cmpSq` for vectors. No measure is involved.

## Main results

* `cmp_twoPort_stable` (separate ports, existence and stability): on `d(X) ≤ d_*` a solution `(m, u)` of
  `IsTwoPortSolution` with `Im m_i, Im u_i < 0`, `|m_i - a| + |u_i - a| ≤ C d(X)`, the outgoing
  contraction `|u_i - a| ≤ q_* d(X)` with `q_* < 1`, and residual stability
  `|m'_i - m_i| + |u'_i - u_i| ≤ C_B (‖r‖ + ‖r'‖)` on a ball of radius `ρ_B`.
* `cmp_commonPort_stable` (common port, existence and stability): the same for `IsCommonPortSolution`, with
  `|m_i - a|, |u₀ - a| ≤ C d(X)`; the linearized top coefficient is `(c + 2b²)/(1 - b) + O(ρ + d)`.
* `cmp_sep_branch`, `cmp_com_branch` (branch identification): for any `H`
  Hermitian and `Im z ≥ ζ₀ > 0`, `|z| ≤ 3`, an exact solution with `-Im m_i ≥ y₀` and an approximate
  solution (residuals `≤ η ≤ η₀`) with `-Im m̄_i ≥ y₀` are `C'' η`-close. This is global (no
  closeness assumed) and needs no port lower bound: `-Im ū ≥ -η` comes from the residual equation.
* `cmp_comparison_deterministic`: the deterministic part of `LayerComparisonContract`
  (existence, signs, closeness in both port cases) together with the branch clause.

## Method

Existence: Banach fixed point (`ContractingWith.exists_fixedPoint'`) for
`m ↦ tr[(H - diag(c m + b U(m)))⁻¹]` on the closed sup-norm ball of radius `ρ` around `a`, with
`H = -E - X`. The Lipschitz bound uses the trace difference
`tr_i M - tr_i M' = Σ_j P_ij(M, M') (σ_j - σ'_j)` (`cmp_trace_sub`), the perturbation estimate
`|P_ij(M, M') - Q_ij| ≤ 2ρ/y³` (`cmp_pair_near`, from row/column vector bounds of shifted inverses)
and, for separate ports, the margin `|c + b²a²| Σ_j |Q_ij| ≤ t < 1 - b` of the strict contraction bound
(`strictContraction_margin`); this also gives `q_* = b(1 + 2bρ)/(1 - t₁) < 1`. For the common port
the crude bound `(c + 2b²) Σ_j |Q_ij| ≤ (c + 2b²)((1-b)⁻¹ + O(d))` suffices
(`strictContraction_rowSum`).

Branch: the paper's weighted argument, in the form of one weighted contraction
(`cmp_branch_close`): weights `ω_i = √(-Im m_i) √(-Im tr_i M̄)` on the tops and
`κ_j = √(-Im σ_j) √(-Im σ̄_j)` on the shifts; Cauchy–Schwarz with the two imaginary identities
gives `|tr_i M - tr_i M̄| ≤ ω_i max_j |σ_j - σ̄_j| / κ_j` (`cmp_trace_sub_weighted`); a second
Cauchy–Schwarz shows that the port loses the fixed fraction `b|u||ũ| Im z / κ` to `Im z > 0`
(`cmp_sep_margin_real`, `cmp_com_margin_real`). The paper's "after two iterations" is realized by
substituting the port difference into the top difference in one step.

Constants depend only on `b, κ` (and `y₀` for the branch clause).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Layers

/-!
## 1. Shifted inverses `(H - diag σ)⁻¹` with `Im σ < 0` (any finite index type)
-/

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Squared Euclidean length `Σ_p |v_p|²` of a complex vector. -/
def cmpSq (v : n → ℂ) : ℝ := ∑ p, ‖v p‖ ^ 2

omit [DecidableEq n] in
theorem cmpSq_nonneg (v : n → ℂ) : 0 ≤ cmpSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Imaginary part of the quadratic form of `H - diag σ`, `H` Hermitian:
`Im ⟨v, (H - diag σ) v⟩ = -Σ_p Im σ_p |v_p|²`. -/
theorem cmp_im_form (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) (v : n → ℂ) :
    (star v ⬝ᵥ ((H - diagonal σ) *ᵥ v)).im = -∑ p, (σ p).im * ‖v p‖ ^ 2 := by
  have hHi : (star v ⬝ᵥ H *ᵥ v).im = 0 := hH.im_star_dotProduct_mulVec_self v
  rw [sub_mulVec, dotProduct_sub, Complex.sub_im, hHi, zero_sub]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Complex.im_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : star (v p) * (σ p * v p) = σ p * (((‖v p‖ ^ 2 : ℝ)) : ℂ) := by
    have := Complex.conj_mul' (v p)
    simp only [Complex.star_def] at *
    rw [show starRingEnd ℂ (v p) * (σ p * v p) = σ p * (starRingEnd ℂ (v p) * v p) by ring, this]
    push_cast; ring
  simp only [Pi.star_apply] at h ⊢
  rw [h, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re]
  ring

/-- **Invertibility.** `H` Hermitian and `Im σ_p < 0` for every `p` give
`det (H - diag σ) ≠ 0`. -/
theorem cmp_det_ne_zero (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) : (H - diagonal σ).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 := cmp_im_form H hH σ v
  rw [hAv, dotProduct_zero, Complex.zero_im] at h1
  have hsum : ∑ p, (-(σ p).im) * ‖v p‖ ^ 2 = 0 := by
    simp only [neg_mul, Finset.sum_neg_distrib]; linarith
  have hnn : ∀ p ∈ Finset.univ, 0 ≤ (-(σ p).im) * ‖v p‖ ^ 2 :=
    fun p _ => mul_nonneg (by linarith [hσ p]) (sq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  apply hv
  funext p
  have hp := hz p (Finset.mem_univ p)
  have hpos : 0 < -(σ p).im := by linarith [hσ p]
  have : ‖v p‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · linarith
    · exact h
  simpa using this

theorem cmp_inv_mul (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) : (H - diagonal σ)⁻¹ * (H - diagonal σ) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (cmp_det_ne_zero H hH σ hσ))

theorem cmp_mul_inv (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) : (H - diagonal σ) * (H - diagonal σ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (cmp_det_ne_zero H hH σ hσ))

/-- **Second resolvent identity.** `M - N = M diag(σ - σ') N` for `M = (H - diag σ)⁻¹`,
`N = (H - diag σ')⁻¹`. -/
theorem cmp_inv_sub_inv (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ σ' : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) (hσ' : ∀ p, (σ' p).im < 0) :
    (H - diagonal σ)⁻¹ - (H - diagonal σ')⁻¹ =
      (H - diagonal σ)⁻¹ * diagonal (σ - σ') * (H - diagonal σ')⁻¹ := by
  have h1 := cmp_inv_mul H hH σ hσ
  have h2 := cmp_mul_inv H hH σ' hσ'
  have hd : diagonal (σ - σ') = (H - diagonal σ') - (H - diagonal σ) := by
    rw [show diagonal (σ - σ') = diagonal σ - diagonal σ' from (diagonal_sub σ σ').symm]; abel
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1,
    Matrix.one_mul]

/-- The anti-Hermitian part: `M - Mᴴ = M (Tᴴ - T) Mᴴ = Mᴴ (Tᴴ - T) M` with `T = H - diag σ`,
`Tᴴ - T = diag(σ - σ̄)`. -/
private theorem cmp_sub_conj (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) :
    (H - diagonal σ)⁻¹ - (H - diagonal σ)⁻¹ᴴ =
        (H - diagonal σ)⁻¹ * diagonal (σ - star σ) * (H - diagonal σ)⁻¹ᴴ ∧
      (H - diagonal σ)⁻¹ - (H - diagonal σ)⁻¹ᴴ =
        (H - diagonal σ)⁻¹ᴴ * diagonal (σ - star σ) * (H - diagonal σ)⁻¹ := by
  set T := H - diagonal σ with hT
  set M := T⁻¹ with hM
  have hMT : M * T = 1 := cmp_inv_mul H hH σ hσ
  have hTM : T * M = 1 := cmp_mul_inv H hH σ hσ
  have hTh : Tᴴ = H - diagonal (star σ) := by
    rw [hT, conjTranspose_sub, hH.eq, diagonal_conjTranspose]
  have hd : diagonal (σ - star σ) = Tᴴ - T := by
    rw [hTh, hT, show diagonal (σ - star σ) = diagonal σ - diagonal (star σ) from
      (diagonal_sub σ (star σ)).symm]; abel
  have hThMh : Tᴴ * Mᴴ = 1 := by rw [← conjTranspose_mul, hMT, conjTranspose_one]
  have hMhTh : Mᴴ * Tᴴ = 1 := by rw [← conjTranspose_mul, hTM, conjTranspose_one]
  constructor
  · rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hThMh, Matrix.mul_one, hMT,
      Matrix.one_mul]
  · rw [hd, Matrix.mul_sub, Matrix.sub_mul, hMhTh, Matrix.one_mul, Matrix.mul_assoc, hTM,
      Matrix.mul_one]

/-- Entries of `A diag(d) B`. -/
theorem cmp_mul_diag_mul_apply (A B : Matrix n n ℂ) (d : n → ℂ) (p q : n) :
    (A * diagonal d * B) p q = ∑ k, A p k * d k * B k q := by
  rw [Matrix.mul_apply]; simp only [mul_diagonal]

private theorem cmp_im_term (w s : ℂ) :
    (w * (s - star s) * star w).im = 2 * s.im * ‖w‖ ^ 2 ∧
      (star w * (s - star s) * w).im = 2 * s.im * ‖w‖ ^ 2 := by
  have h1 : w * (s - star s) * star w = (((2 * s.im * ‖w‖ ^ 2 : ℝ)) : ℂ) * Complex.I := by
    have hw : w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hs : s - star s = ((2 * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring
    rw [show w * (s - star s) * star w = (s - star s) * (w * star w) by ring, hw, hs]
    push_cast; ring
  have h2 : star w * (s - star s) * w = w * (s - star s) * star w := by ring
  refine ⟨?_, ?_⟩ <;> [rw [h1]; rw [h2, h1]] <;>
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im] <;> ring

/-- **Row imaginary identity.** `-Im M_pp = Σ_q |M_pq|² (-Im σ_q)`. -/
theorem cmp_im_diag_row (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) (p : n) :
    -((H - diagonal σ)⁻¹ p p).im = ∑ q, ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 * (-(σ q).im) := by
  have h := congrArg (fun A => (A p p).im) (cmp_sub_conj H hH σ hσ).1
  simp only [cmp_mul_diag_mul_apply] at h
  rw [Matrix.sub_apply, conjTranspose_apply, Complex.sub_im, Complex.im_sum] at h
  simp only [Pi.sub_apply, Pi.star_apply, conjTranspose_apply, (cmp_im_term _ _).1] at h
  have hs : (star ((H - diagonal σ)⁻¹ p p)).im = -((H - diagonal σ)⁻¹ p p).im := by
    simp
  rw [hs] at h
  have : ∑ q, 2 * (σ q).im * ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 =
      -2 * ∑ q, ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 * (-(σ q).im) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_; ring
  linarith

/-- **Column imaginary identity.** `-Im M_pp = Σ_q |M_qp|² (-Im σ_q)`. -/
theorem cmp_im_diag_col (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ)
    (hσ : ∀ p, (σ p).im < 0) (p : n) :
    -((H - diagonal σ)⁻¹ p p).im = ∑ q, ‖(H - diagonal σ)⁻¹ q p‖ ^ 2 * (-(σ q).im) := by
  have h := congrArg (fun A => (A p p).im) (cmp_sub_conj H hH σ hσ).2
  simp only [cmp_mul_diag_mul_apply] at h
  rw [Matrix.sub_apply, conjTranspose_apply, Complex.sub_im, Complex.im_sum] at h
  simp only [Pi.sub_apply, Pi.star_apply, conjTranspose_apply, (cmp_im_term _ _).2] at h
  have hs : (star ((H - diagonal σ)⁻¹ p p)).im = -((H - diagonal σ)⁻¹ p p).im := by
    simp
  rw [hs] at h
  have : ∑ q, 2 * (σ q).im * ‖(H - diagonal σ)⁻¹ q p‖ ^ 2 =
      -2 * ∑ q, ‖(H - diagonal σ)⁻¹ q p‖ ^ 2 * (-(σ q).im) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_; ring
  linarith

/-- Elementary step: `y X ≤ s`, `s² ≤ X V`, `X ≥ 0`, `y > 0` give `y² X ≤ V`. -/
theorem cmp_sq_aux {y X s V : ℝ} (hy : 0 < y) (hX : 0 ≤ X) (hs : 0 ≤ s) (hV : 0 ≤ V)
    (h1 : y * X ≤ s) (h2 : s ^ 2 ≤ X * V) : y ^ 2 * X ≤ V := by
  rcases hX.lt_or_eq with hXp | hX0
  · have h3 : (y * X) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h4 : X * (y ^ 2 * X) ≤ X * V := by nlinarith
    exact le_of_mul_le_mul_left h4 hXp
  · rw [← hX0] at h2 ⊢
    have : s ^ 2 ≤ 0 := by simpa using h2
    have hs0 : s = 0 := by nlinarith
    simpa using hV

omit [DecidableEq n] in
/-- Cauchy–Schwarz for `|⟨x, v⟩|`. -/
theorem cmp_dot_le (x v : n → ℂ) :
    ‖star x ⬝ᵥ v‖ ^ 2 ≤ cmpSq x * cmpSq v := by
  have h1 : ‖star x ⬝ᵥ v‖ ≤ ∑ p, ‖x p‖ * ‖v p‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [norm_mul, Pi.star_apply, norm_star]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun p => ‖x p‖) (fun p => ‖v p‖)
  have h0 : 0 ≤ ‖star x ⬝ᵥ v‖ := norm_nonneg _
  calc ‖star x ⬝ᵥ v‖ ^ 2 ≤ (∑ p, ‖x p‖ * ‖v p‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ cmpSq x * cmpSq v := h2

/-- **Column vector bound.** `-Im σ_p ≥ y > 0` gives `y² |M v|² ≤ |v|²` for
`M = (H - diag σ)⁻¹`. -/
theorem cmp_mulVec_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (v : n → ℂ) :
    y ^ 2 * cmpSq ((H - diagonal σ)⁻¹ *ᵥ v) ≤ cmpSq v := by
  have hσ' : ∀ p, (σ p).im < 0 := fun p => by linarith [hσ p]
  set x := (H - diagonal σ)⁻¹ *ᵥ v with hx
  have hTx : (H - diagonal σ) *ᵥ x = v := by
    rw [hx, mulVec_mulVec, cmp_mul_inv H hH σ hσ', one_mulVec]
  have hform := cmp_im_form H hH σ x
  rw [hTx] at hform
  have hlow : y * cmpSq x ≤ (star x ⬝ᵥ v).im := by
    rw [hform, cmpSq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have := hσ p
    nlinarith [sq_nonneg ‖x p‖]
  have hup : (star x ⬝ᵥ v).im ≤ ‖star x ⬝ᵥ v‖ := Complex.im_le_norm _
  exact cmp_sq_aux hy (cmpSq_nonneg x) (norm_nonneg _) (cmpSq_nonneg v) (hlow.trans hup) (cmp_dot_le x v)

/-- **Row vector bound.** `-Im σ_p ≥ y > 0` gives `y² |v M|² ≤ |v|²`. -/
theorem cmp_vecMul_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (v : n → ℂ) :
    y ^ 2 * cmpSq (v ᵥ* (H - diagonal σ)⁻¹) ≤ cmpSq v := by
  have h := cmp_mulVec_le Hᵀ hH.transpose σ hy hσ v
  rwa [show (Hᵀ - diagonal σ)⁻¹ = ((H - diagonal σ)⁻¹)ᵀ by
    rw [transpose_nonsing_inv, transpose_sub, diagonal_transpose], mulVec_transpose] at h

/-- **Row mass bound.** `y² Σ_q |M_pq|² ≤ 1`. -/
theorem cmp_row_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (p : n) :
    y ^ 2 * ∑ q, ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 ≤ 1 := by
  have hσ' : ∀ p, (σ p).im < 0 := fun p => by linarith [hσ p]
  set M := (H - diagonal σ)⁻¹ with hM
  have hid := cmp_im_diag_row H hH σ hσ' p
  rw [← hM] at hid
  have hS0 : 0 ≤ ∑ q, ‖M p q‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow : y * ∑ q, ‖M p q‖ ^ 2 ≤ ‖M p p‖ := by
    calc y * ∑ q, ‖M p q‖ ^ 2 ≤ ∑ q, ‖M p q‖ ^ 2 * (-(σ q).im) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun q _ => by nlinarith [hσ q, sq_nonneg ‖M p q‖]
      _ = -(M p p).im := hid.symm
      _ ≤ ‖M p p‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm _)
  have hsq : ‖M p p‖ ^ 2 ≤ (∑ q, ‖M p q‖ ^ 2) * 1 := by
    rw [mul_one]
    exact Finset.single_le_sum (f := fun q => ‖M p q‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ p)
  exact cmp_sq_aux hy hS0 (norm_nonneg _) zero_le_one hlow hsq

/-- **Column mass bound.** `y² Σ_q |M_qp|² ≤ 1`. -/
theorem cmp_col_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (p : n) :
    y ^ 2 * ∑ q, ‖(H - diagonal σ)⁻¹ q p‖ ^ 2 ≤ 1 := by
  have hσ' : ∀ p, (σ p).im < 0 := fun p => by linarith [hσ p]
  set M := (H - diagonal σ)⁻¹ with hM
  have hid := cmp_im_diag_col H hH σ hσ' p
  rw [← hM] at hid
  have hS0 : 0 ≤ ∑ q, ‖M q p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlow : y * ∑ q, ‖M q p‖ ^ 2 ≤ ‖M p p‖ := by
    calc y * ∑ q, ‖M q p‖ ^ 2 ≤ ∑ q, ‖M q p‖ ^ 2 * (-(σ q).im) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun q _ => by nlinarith [hσ q, sq_nonneg ‖M q p‖]
      _ = -(M p p).im := hid.symm
      _ ≤ ‖M p p‖ := (neg_le_abs _).trans (Complex.abs_im_le_norm _)
  have hsq : ‖M p p‖ ^ 2 ≤ (∑ q, ‖M q p‖ ^ 2) * 1 := by
    rw [mul_one]
    exact Finset.single_le_sum (f := fun q => ‖M q p‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ p)
  exact cmp_sq_aux hy hS0 (norm_nonneg _) zero_le_one hlow hsq

/-- Diagonal entries: `y |M_pp| ≤ 1`. -/
theorem cmp_diag_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ : n → ℂ) {y : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (p : n) :
    y * ‖(H - diagonal σ)⁻¹ p p‖ ≤ 1 := by
  have h := cmp_row_le H hH σ hy hσ p
  have hsq : ‖(H - diagonal σ)⁻¹ p p‖ ^ 2 ≤ ∑ q, ‖(H - diagonal σ)⁻¹ p q‖ ^ 2 :=
    Finset.single_le_sum (f := fun q => ‖(H - diagonal σ)⁻¹ p q‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ p)
  have h2 : (y * ‖(H - diagonal σ)⁻¹ p p‖) ^ 2 ≤ 1 ^ 2 := by
    rw [mul_pow, one_pow]; nlinarith [sq_nonneg y]
  exact (pow_le_pow_iff_left₀ (by positivity) zero_le_one two_ne_zero).mp h2

/-- **Rows of `M - R`.** With `-Im σ, -Im σ⁰ ≥ y > 0` and `|σ_k - σ⁰_k| ≤ ε`:
`y⁴ Σ_q |(M - R)_pq|² ≤ ε²`, `M = (H - diag σ)⁻¹`, `R = (H - diag σ⁰)⁻¹`. -/
theorem cmp_row_sub_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ σ₀ : n → ℂ) {y ε : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (hσ₀ : ∀ p, y ≤ -(σ₀ p).im)
    (hε : ∀ k, ‖σ k - σ₀ k‖ ≤ ε) (p : n) :
    y ^ 4 * ∑ q, ‖((H - diagonal σ)⁻¹ - (H - diagonal σ₀)⁻¹) p q‖ ^ 2 ≤ ε ^ 2 := by
  have hσ' : ∀ p, (σ p).im < 0 := fun p => by linarith [hσ p]
  have hσ₀' : ∀ p, (σ₀ p).im < 0 := fun p => by linarith [hσ₀ p]
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε p)
  set M := (H - diagonal σ)⁻¹ with hM
  set w : n → ℂ := fun k => M p k * (σ - σ₀) k with hw
  have hrow : (fun q => (M - (H - diagonal σ₀)⁻¹) p q) = w ᵥ* (H - diagonal σ₀)⁻¹ := by
    funext q
    rw [hM, cmp_inv_sub_inv H hH σ σ₀ hσ' hσ₀', cmp_mul_diag_mul_apply]
    rfl
  have h1 := cmp_vecMul_le H hH σ₀ hy hσ₀ w
  rw [← hrow] at h1
  have h2 : cmpSq w ≤ ε ^ 2 * ∑ k, ‖M p k‖ ^ 2 := by
    rw [cmpSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hw]
    simp only [norm_mul, mul_pow, Pi.sub_apply]
    have := pow_le_pow_left₀ (norm_nonneg _) (hε k) 2
    nlinarith [sq_nonneg ‖M p k‖]
  have h3 := cmp_row_le H hH σ hy hσ p
  rw [← hM] at h3
  have hS : 0 ≤ cmpSq (fun q => (M - (H - diagonal σ₀)⁻¹) p q) := cmpSq_nonneg _
  calc y ^ 4 * ∑ q, ‖(M - (H - diagonal σ₀)⁻¹) p q‖ ^ 2
      = y ^ 2 * (y ^ 2 * cmpSq (fun q => (M - (H - diagonal σ₀)⁻¹) p q)) := by
        rw [cmpSq]; ring
    _ ≤ y ^ 2 * (ε ^ 2 * ∑ k, ‖M p k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = ε ^ 2 * (y ^ 2 * ∑ k, ‖M p k‖ ^ 2) := by ring
    _ ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ε ^ 2 := mul_one _

/-- **Columns of `N - R`.** Same hypotheses: `y⁴ Σ_p |(N - R)_pq|² ≤ ε²`. -/
theorem cmp_col_sub_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (σ σ₀ : n → ℂ) {y ε : ℝ}
    (hy : 0 < y) (hσ : ∀ p, y ≤ -(σ p).im) (hσ₀ : ∀ p, y ≤ -(σ₀ p).im)
    (hε : ∀ k, ‖σ k - σ₀ k‖ ≤ ε) (q : n) :
    y ^ 4 * ∑ p, ‖((H - diagonal σ)⁻¹ - (H - diagonal σ₀)⁻¹) p q‖ ^ 2 ≤ ε ^ 2 := by
  have hσ' : ∀ p, (σ p).im < 0 := fun p => by linarith [hσ p]
  have hσ₀' : ∀ p, (σ₀ p).im < 0 := fun p => by linarith [hσ₀ p]
  set R := (H - diagonal σ₀)⁻¹ with hR
  set w : n → ℂ := fun k => (σ - σ₀) k * R k q with hw
  have hcol : (fun p => ((H - diagonal σ)⁻¹ - R) p q) = (H - diagonal σ)⁻¹ *ᵥ w := by
    funext p
    rw [hR, cmp_inv_sub_inv H hH σ σ₀ hσ' hσ₀', cmp_mul_diag_mul_apply]
    simp only [mulVec, dotProduct, hw]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h1 := cmp_mulVec_le H hH σ hy hσ w
  rw [← hcol] at h1
  have h2 : cmpSq w ≤ ε ^ 2 * ∑ k, ‖R k q‖ ^ 2 := by
    rw [cmpSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [hw]
    simp only [norm_mul, mul_pow, Pi.sub_apply]
    have := pow_le_pow_left₀ (norm_nonneg _) (hε k) 2
    nlinarith [sq_nonneg ‖R k q‖]
  have h3 := cmp_col_le H hH σ₀ hy hσ₀ q
  rw [← hR] at h3
  calc y ^ 4 * ∑ p, ‖((H - diagonal σ)⁻¹ - R) p q‖ ^ 2
      = y ^ 2 * (y ^ 2 * cmpSq (fun p => ((H - diagonal σ)⁻¹ - R) p q)) := by
        rw [cmpSq]; ring
    _ ≤ y ^ 2 * (ε ^ 2 * ∑ k, ‖R k q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = ε ^ 2 * (y ^ 2 * ∑ k, ‖R k q‖ ^ 2) := by ring
    _ ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = ε ^ 2 := mul_one _

end General

/-!
## 2. Two-block traces: pair traces, masses, and the trace difference
-/

section Block

variable {W : ℕ}

/-- Block-constant extension of a two-component shift to the sites `Fin 2 × Fin W`. -/
def cmpExt (s : Fin 2 → ℂ) : Fin 2 × Fin W → ℂ := fun q => s q.1

/-- Mixed pair trace `P_ij(A, B) = W⁻¹ Σ_{x,y} A_(i,x)(j,y) B_(j,y)(i,x)`; `P(R,R) = Q`. -/
def cmpPair (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) : ℂ :=
  (W : ℂ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, A (i, x) (j, y) * B (j, y) (i, x)

theorem cmpPair_self (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    cmpPair R R i j = blockPairTrace R i j := rfl

/-- Row block mass `W⁻¹ Σ_{x,y} |A_(i,x)(j,y)|²`. -/
def cmpRowMass (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) : ℝ :=
  (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖A (i, x) (j, y)‖ ^ 2

/-- Column block mass `W⁻¹ Σ_{x,y} |B_(j,y)(i,x)|²`. -/
def cmpColMass (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) : ℝ :=
  (W : ℝ)⁻¹ * ∑ x : Fin W, ∑ y : Fin W, ‖B (j, y) (i, x)‖ ^ 2

theorem cmpRowMass_nonneg (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    0 ≤ cmpRowMass A i j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _)

theorem cmpColMass_nonneg (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    0 ≤ cmpColMass B i j :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _)

private theorem cmp_inv_W_mul_le (W : ℕ) {K : ℝ} (hK : 0 ≤ K) : (W : ℝ)⁻¹ * (W * K) ≤ K := by
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp [hK]
  · have : (0 : ℝ) < W := by exact_mod_cast h
    rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]

theorem cmp_im_blockTrace (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    (blockTrace M i).im = (W : ℝ)⁻¹ * ∑ x : Fin W, (M (i, x) (i, x)).im := by
  unfold blockTrace
  have : ((W : ℂ))⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul, Complex.im_sum]

/-- **Trace difference.** `tr_i(A diag(δ) B) = Σ_j P_ij(A,B) δ_j` for a block-constant `δ`. -/
theorem cmp_blockTrace_mul_diag_mul (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (δ : Fin 2 → ℂ) (i : Fin 2) :
    blockTrace (A * diagonal (cmpExt δ) * B) i = ∑ j, cmpPair A B i j * δ j := by
  unfold blockTrace cmpPair
  simp only [cmp_mul_diag_mul_apply, Fintype.sum_prod_type, cmpExt]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **Cauchy–Schwarz for pair traces.** `|P_ij(A,B)| ≤ √(A-row mass) √(B-column mass)`. -/
theorem cmp_pair_le_sqrt (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    ‖cmpPair A B i j‖ ≤ Real.sqrt (cmpRowMass A i j) * Real.sqrt (cmpColMass B i j) := by
  set S := ∑ x : Fin W, ∑ y : Fin W, ‖A (i, x) (j, y)‖ * ‖B (j, y) (i, x)‖ with hS
  set S1 := ∑ x : Fin W, ∑ y : Fin W, ‖A (i, x) (j, y)‖ ^ 2 with hS1
  set S2 := ∑ x : Fin W, ∑ y : Fin W, ‖B (j, y) (i, x)‖ ^ 2 with hS2
  have hSle : ‖cmpPair A B i j‖ ≤ (W : ℝ)⁻¹ * S := by
    unfold cmpPair
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rw [norm_mul]
  have hCS : S ^ 2 ≤ S1 * S2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin W × Fin W))
      (fun p => ‖A (i, p.1) (j, p.2)‖) (fun p => ‖B (j, p.2) (i, p.1)‖)
    simp only [← Finset.univ_product_univ, Finset.sum_product] at h
    exact h
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  refine hSle.trans ?_
  rw [cmpRowMass, cmpColMass, ← hS1, ← hS2, ← Real.sqrt_mul (mul_nonneg hW0 hS10)]
  rw [show (W : ℝ)⁻¹ * S = Real.sqrt (((W : ℝ)⁻¹ * S) ^ 2) from
    (Real.sqrt_sq (mul_nonneg hW0 hS0)).symm]
  apply Real.sqrt_le_sqrt
  have : ((W : ℝ)⁻¹ * S) ^ 2 = (W : ℝ)⁻¹ ^ 2 * S ^ 2 := by ring
  rw [this, show (W : ℝ)⁻¹ * S1 * ((W : ℝ)⁻¹ * S2) = (W : ℝ)⁻¹ ^ 2 * (S1 * S2) by ring]
  exact mul_le_mul_of_nonneg_left hCS (by positivity)

/-- Row block mass is bounded by the largest row mass. -/
theorem cmpRowMass_le (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ p, ∑ q, ‖A p q‖ ^ 2 ≤ K) (i j : Fin 2) : cmpRowMass A i j ≤ K := by
  unfold cmpRowMass
  refine le_trans ?_ (cmp_inv_W_mul_le W hK)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [show (W : ℝ) * K = ∑ _x : Fin W, K by simp]
  refine Finset.sum_le_sum fun x _ => le_trans ?_ (hA (i, x))
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun j' => ∑ y : Fin W, ‖A (i, x) (j', y)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- Column block mass is bounded by the largest column mass. -/
theorem cmpColMass_le (B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hB : ∀ q, ∑ p, ‖B p q‖ ^ 2 ≤ K) (i j : Fin 2) : cmpColMass B i j ≤ K := by
  unfold cmpColMass
  refine le_trans ?_ (cmp_inv_W_mul_le W hK)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [show (W : ℝ) * K = ∑ _x : Fin W, K by simp]
  refine Finset.sum_le_sum fun x _ => le_trans ?_ (hB (i, x))
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun j' => ∑ y : Fin W, ‖B (j', y) (i, x)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j)

/-- `|P_ij(A,B)| ≤ ρ_A ρ_B` from row bounds `ρ_A²` of `A` and column bounds `ρ_B²` of `B`. -/
theorem cmp_pair_le (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {ρA ρB : ℝ}
    (hρA : 0 ≤ ρA) (hρB : 0 ≤ ρB) (hA : ∀ p, ∑ q, ‖A p q‖ ^ 2 ≤ ρA ^ 2)
    (hB : ∀ q, ∑ p, ‖B p q‖ ^ 2 ≤ ρB ^ 2) (i j : Fin 2) :
    ‖cmpPair A B i j‖ ≤ ρA * ρB := by
  refine (cmp_pair_le_sqrt A B i j).trans ?_
  have h1 := Real.sqrt_le_sqrt (cmpRowMass_le A (sq_nonneg ρA) hA i j)
  have h2 := Real.sqrt_le_sqrt (cmpColMass_le B (sq_nonneg ρB) hB i j)
  rw [Real.sqrt_sq hρA] at h1
  rw [Real.sqrt_sq hρB] at h2
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hρA

/-- Bilinear splitting `P(M,N) - P(R,R) = P(M - R, N) + P(R, N - R)`. -/
theorem cmpPair_sub (M N R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    cmpPair M N i j - cmpPair R R i j = cmpPair (M - R) N i j + cmpPair R (N - R) i j := by
  unfold cmpPair
  rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.sub_apply]
  ring

end Block

/-!
## 3. Block-shifted inverses `(H - diag(s_i))⁻¹` on two blocks
-/

section BlockShift

variable {W : ℕ}

theorem cmp_le_inv {y t : ℝ} (hy : 0 < y) (h : y * t ≤ 1) : t ≤ y⁻¹ := by
  rw [← one_div, le_div_iff₀ hy]; linarith

theorem cmp_blockTrace_sub (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace (A - B) i = blockTrace A i - blockTrace B i := by
  unfold blockTrace
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rfl

theorem cmpExt_sub (s s' : Fin 2 → ℂ) :
    (cmpExt s : Fin 2 × Fin W → ℂ) - cmpExt s' = cmpExt (s - s') := rfl

/-- The block-shifted inverse `(H - diag(s_i 1_W))⁻¹`. -/
def cmpInv (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (s : Fin 2 → ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (H - diagonal (cmpExt s))⁻¹

variable (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
include hH

/-- **Trace difference** `tr_i M - tr_i M' = Σ_j P_ij(M, M') (s_j - s'_j)` for
`M = (H - diag s)⁻¹`, `M' = (H - diag s')⁻¹`, `Im s, Im s' < 0`. -/
theorem cmp_trace_sub (s s' : Fin 2 → ℂ) (hs : ∀ j, (s j).im < 0) (hs' : ∀ j, (s' j).im < 0)
    (i : Fin 2) :
    blockTrace (cmpInv H s) i - blockTrace (cmpInv H s') i =
      ∑ j, cmpPair (cmpInv H s) (cmpInv H s') i j * (s j - s' j) := by
  rw [← cmp_blockTrace_sub]
  unfold cmpInv
  rw [cmp_inv_sub_inv H hH (cmpExt s) (cmpExt s') (fun p => hs p.1) (fun p => hs' p.1),
    cmpExt_sub, cmp_blockTrace_mul_diag_mul]
  rfl

/-- Row mass bound `Σ_q |M_pq|² ≤ y⁻²`. -/
theorem cmp_inv_row (s : Fin 2 → ℂ) {y : ℝ} (hy : 0 < y) (hs : ∀ j, y ≤ -(s j).im)
    (p : Fin 2 × Fin W) : ∑ q, ‖cmpInv H s p q‖ ^ 2 ≤ y⁻¹ ^ 2 := by
  rw [inv_pow]
  exact cmp_le_inv (pow_pos hy 2) (cmp_row_le H hH (cmpExt s) hy (fun p => hs p.1) p)

/-- Column mass bound `Σ_p |M_pq|² ≤ y⁻²`. -/
theorem cmp_inv_col (s : Fin 2 → ℂ) {y : ℝ} (hy : 0 < y) (hs : ∀ j, y ≤ -(s j).im)
    (q : Fin 2 × Fin W) : ∑ p, ‖cmpInv H s p q‖ ^ 2 ≤ y⁻¹ ^ 2 := by
  rw [inv_pow]
  exact cmp_le_inv (pow_pos hy 2) (cmp_col_le H hH (cmpExt s) hy (fun p => hs p.1) q)

/-- Crude trace bound `|tr_i M| ≤ y⁻¹`. -/
theorem cmp_trace_le (s : Fin 2 → ℂ) {y : ℝ} (hy : 0 < y) (hs : ∀ j, y ≤ -(s j).im)
    (i : Fin 2) : ‖blockTrace (cmpInv H s) i‖ ≤ y⁻¹ := by
  unfold blockTrace
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hd : ∀ x : Fin W, ‖cmpInv H s (i, x) (i, x)‖ ≤ y⁻¹ := fun x =>
    cmp_le_inv hy (cmp_diag_le H hH (cmpExt s) hy (fun p => hs p.1) (i, x))
  have h1 : ‖∑ x : Fin W, cmpInv H s (i, x) (i, x)‖ ≤ W * y⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x : Fin W, ‖cmpInv H s (i, x) (i, x)‖ ≤ ∑ _x : Fin W, y⁻¹ :=
          Finset.sum_le_sum fun x _ => hd x
      _ = W * y⁻¹ := by simp
  calc (W : ℝ)⁻¹ * ‖∑ x : Fin W, cmpInv H s (i, x) (i, x)‖
      ≤ (W : ℝ)⁻¹ * (W * y⁻¹) := by gcongr
    _ ≤ y⁻¹ := cmp_inv_W_mul_le W (le_of_lt (inv_pos.mpr hy))

/-- **Row mass identity** `Σ_j A_ij (-Im s_j) = -Im tr_i M`. -/
theorem cmp_rowMass_im (s : Fin 2 → ℂ) (hs : ∀ j, (s j).im < 0) (i : Fin 2) :
    ∑ j, cmpRowMass (cmpInv H s) i j * (-(s j).im) = -(blockTrace (cmpInv H s) i).im := by
  rw [cmp_im_blockTrace, ← mul_neg, ← Finset.sum_neg_distrib]
  simp only [cmpRowMass, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := cmp_im_diag_row H hH (cmpExt s) (fun p => hs p.1) (i, x)
  rw [Fintype.sum_prod_type] at h
  unfold cmpInv
  rw [h]
  rfl

/-- **Column mass identity** `Σ_j Ā_ji (-Im s_j) = -Im tr_i M`. -/
theorem cmp_colMass_im (s : Fin 2 → ℂ) (hs : ∀ j, (s j).im < 0) (i : Fin 2) :
    ∑ j, cmpColMass (cmpInv H s) i j * (-(s j).im) = -(blockTrace (cmpInv H s) i).im := by
  rw [cmp_im_blockTrace, ← mul_neg, ← Finset.sum_neg_distrib]
  simp only [cmpColMass, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := cmp_im_diag_col H hH (cmpExt s) (fun p => hs p.1) (i, x)
  rw [Fintype.sum_prod_type] at h
  unfold cmpInv
  rw [h]
  rfl

/-- `|P_ij(M, M')| ≤ y⁻¹ y⁻¹`. -/
theorem cmp_pair_bound (s s' : Fin 2 → ℂ) {y : ℝ} (hy : 0 < y) (hs : ∀ j, y ≤ -(s j).im)
    (hs' : ∀ j, y ≤ -(s' j).im) (i j : Fin 2) :
    ‖cmpPair (cmpInv H s) (cmpInv H s') i j‖ ≤ y⁻¹ * y⁻¹ :=
  cmp_pair_le _ _ (inv_nonneg.mpr hy.le) (inv_nonneg.mpr hy.le) (cmp_inv_row H hH s hy hs)
    (cmp_inv_col H hH s' hy hs') i j

/-- **Perturbation of pair traces.** With `-Im s, -Im s', -Im s⁰ ≥ y > 0` and
`|s_j - s⁰_j|, |s'_j - s⁰_j| ≤ ε`: `|P_ij(M, M') - P_ij(R, R)| ≤ 2ε / y³`. -/
theorem cmp_pair_near (s s' s₀ : Fin 2 → ℂ) {y ε : ℝ} (hy : 0 < y) (hε : 0 ≤ ε)
    (hs : ∀ j, y ≤ -(s j).im) (hs' : ∀ j, y ≤ -(s' j).im) (hs₀ : ∀ j, y ≤ -(s₀ j).im)
    (hd : ∀ j, ‖s j - s₀ j‖ ≤ ε) (hd' : ∀ j, ‖s' j - s₀ j‖ ≤ ε) (i j : Fin 2) :
    ‖cmpPair (cmpInv H s) (cmpInv H s') i j - cmpPair (cmpInv H s₀) (cmpInv H s₀) i j‖ ≤
      2 * ε / y ^ 3 := by
  rw [cmpPair_sub]
  have hyi : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
  have hey : 0 ≤ ε / y ^ 2 := by positivity
  have hrowD : ∀ p, ∑ q, ‖(cmpInv H s - cmpInv H s₀) p q‖ ^ 2 ≤ (ε / y ^ 2) ^ 2 := fun p => by
    have := cmp_row_sub_le H hH (cmpExt s) (cmpExt s₀) hy (fun p => hs p.1) (fun p => hs₀ p.1)
      (fun k => hd k.1) p
    rw [div_pow, ← pow_mul, le_div_iff₀ (by positivity)]; unfold cmpInv; linarith
  have hcolD : ∀ q, ∑ p, ‖(cmpInv H s' - cmpInv H s₀) p q‖ ^ 2 ≤ (ε / y ^ 2) ^ 2 := fun q => by
    have := cmp_col_sub_le H hH (cmpExt s') (cmpExt s₀) hy (fun p => hs' p.1)
      (fun p => hs₀ p.1) (fun k => hd' k.1) q
    rw [div_pow, ← pow_mul, le_div_iff₀ (by positivity)]; unfold cmpInv; linarith
  have h1 := cmp_pair_le _ _ hey hyi hrowD (cmp_inv_col H hH s' hy hs') i j
  have h2 := cmp_pair_le _ _ hyi hey (cmp_inv_row H hH s₀ hy hs₀) hcolD i j
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / y ^ 2 * y⁻¹ + y⁻¹ * (ε / y ^ 2) := add_le_add h1 h2
    _ = 2 * ε / y ^ 3 := by field_simp; ring

/-- **Weighted trace difference** (the Cauchy–Schwarz step of the branch argument). If
`|s_j - s'_j| ≤ S √(-Im s_j) √(-Im s'_j)` for both blocks then
`|tr_i M - tr_i M'| ≤ √(-Im tr_i M) √(-Im tr_i M') S`. -/
theorem cmp_trace_sub_weighted (s s' : Fin 2 → ℂ) (hs : ∀ j, (s j).im < 0)
    (hs' : ∀ j, (s' j).im < 0) {S : ℝ} (hS : 0 ≤ S)
    (hδ : ∀ j, ‖s j - s' j‖ ≤ S * (Real.sqrt (-(s j).im) * Real.sqrt (-(s' j).im)))
    (i : Fin 2) :
    ‖blockTrace (cmpInv H s) i - blockTrace (cmpInv H s') i‖ ≤
      Real.sqrt (-(blockTrace (cmpInv H s) i).im) *
        Real.sqrt (-(blockTrace (cmpInv H s') i).im) * S := by
  rw [cmp_trace_sub H hH s s' hs hs' i, ← cmp_rowMass_im H hH s hs i,
    ← cmp_colMass_im H hH s' hs' i]
  set A := fun j => cmpRowMass (cmpInv H s) i j
  set B := fun j => cmpColMass (cmpInv H s') i j
  have hA : ∀ j, 0 ≤ A j := fun j => cmpRowMass_nonneg _ _ _
  have hB : ∀ j, 0 ≤ B j := fun j => cmpColMass_nonneg _ _ _
  have hy : ∀ j, 0 ≤ -(s j).im := fun j => by linarith [hs j]
  have hy' : ∀ j, 0 ≤ -(s' j).im := fun j => by linarith [hs' j]
  have hterm : ∀ j, ‖cmpPair (cmpInv H s) (cmpInv H s') i j * (s j - s' j)‖ ≤
      S * (Real.sqrt (A j * -(s j).im) * Real.sqrt (B j * -(s' j).im)) := fun j => by
    rw [norm_mul, Real.sqrt_mul (hA j), Real.sqrt_mul (hB j)]
    have h1 := cmp_pair_le_sqrt (cmpInv H s) (cmpInv H s') i j
    calc ‖cmpPair (cmpInv H s) (cmpInv H s') i j‖ * ‖s j - s' j‖
        ≤ (Real.sqrt (A j) * Real.sqrt (B j)) *
            (S * (Real.sqrt (-(s j).im) * Real.sqrt (-(s' j).im))) :=
          mul_le_mul h1 (hδ j) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hCS := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2))
    (f := fun j => A j * -(s j).im) (g := fun j => B j * -(s' j).im)
    (fun j => mul_nonneg (hA j) (hy j)) (fun j => mul_nonneg (hB j) (hy' j))
  calc ‖∑ j, cmpPair (cmpInv H s) (cmpInv H s') i j * (s j - s' j)‖
      ≤ ∑ j, ‖cmpPair (cmpInv H s) (cmpInv H s') i j * (s j - s' j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, S * (Real.sqrt (A j * -(s j).im) * Real.sqrt (B j * -(s' j).im)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = S * ∑ j, Real.sqrt (A j * -(s j).im) * Real.sqrt (B j * -(s' j).im) := by
        rw [Finset.mul_sum]
    _ ≤ S * (Real.sqrt (∑ j, A j * -(s j).im) * Real.sqrt (∑ j, B j * -(s' j).im)) :=
        mul_le_mul_of_nonneg_left hCS hS
    _ = _ := by ring

/-- **Separate-port Lipschitz core.** Shifts `σ, σ'` within `ρ` of `σ⁰` (all with
`-Im ≥ y₁`), `σ_j - σ'_j = κ_j δ_j + e_j` with `|κ_j - β| ≤ ρ`, `|β| ≤ 1`, and the margin
`|β| Σ_j |Q_ij| ≤ t` (`Q = P(R,R)`, `R = (H - diag σ⁰)⁻¹`). Then
`|tr_i M - tr_i M'| ≤ (t + ρ K₁) ‖δ‖ + 2 y₁⁻² ‖e‖`, `K₁ = 2/y₁² + 8/y₁³`. -/
theorem cmp_sep_core {y₁ ρ t : ℝ} (hy₁ : 0 < y₁) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (σ σ' σ₀ : Fin 2 → ℂ) (hσ : ∀ j, y₁ ≤ -(σ j).im) (hσ' : ∀ j, y₁ ≤ -(σ' j).im)
    (hσ₀ : ∀ j, y₁ ≤ -(σ₀ j).im) (hd : ∀ j, ‖σ j - σ₀ j‖ ≤ ρ) (hd' : ∀ j, ‖σ' j - σ₀ j‖ ≤ ρ)
    (β : ℂ) (hβ : ‖β‖ ≤ 1)
    (ht : ∀ i, ‖β‖ * ∑ j, ‖cmpPair (cmpInv H σ₀) (cmpInv H σ₀) i j‖ ≤ t)
    (κ δ e : Fin 2 → ℂ) (hκ : ∀ j, ‖κ j - β‖ ≤ ρ) (hdiff : ∀ j, σ j - σ' j = κ j * δ j + e j)
    (i : Fin 2) :
    ‖blockTrace (cmpInv H σ) i - blockTrace (cmpInv H σ') i‖ ≤
      (t + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3)) * ‖δ‖ + 2 * y₁⁻¹ ^ 2 * ‖e‖ := by
  have him : ∀ (τ : Fin 2 → ℂ), (∀ j, y₁ ≤ -(τ j).im) → ∀ j, (τ j).im < 0 :=
    fun τ h j => by linarith [h j]
  rw [cmp_trace_sub H hH σ σ' (him σ hσ) (him σ' hσ') i]
  set P := fun j => cmpPair (cmpInv H σ) (cmpInv H σ') i j with hP
  set Q := fun j => cmpPair (cmpInv H σ₀) (cmpInv H σ₀) i j with hQ
  have hPQ : ∀ j, ‖P j‖ ≤ ‖Q j‖ + 2 * ρ * y₁⁻¹ ^ 3 := fun j => by
    have := cmp_pair_near H hH σ σ' σ₀ hy₁ hρ0 hσ hσ' hσ₀ hd hd' i j
    rw [mul_div_assoc, div_eq_mul_inv, ← inv_pow] at this
    have h2 := norm_sub_norm_le (P j) (Q j)
    linarith
  have hPb : ∀ j, ‖P j‖ ≤ y₁⁻¹ ^ 2 := fun j => by
    rw [sq]; exact cmp_pair_bound H hH σ σ' hy₁ hσ hσ' i j
  have hQb : ∀ j, ‖Q j‖ ≤ y₁⁻¹ ^ 2 := fun j => by
    rw [sq]; exact cmp_pair_bound H hH σ₀ σ₀ hy₁ hσ₀ hσ₀ i j
  have hκb : ∀ j, ‖κ j‖ ≤ ‖β‖ + ρ := fun j => by
    have := norm_sub_norm_le (κ j) β; linarith [hκ j]
  have hδj : ∀ j, ‖δ j‖ ≤ ‖δ‖ := fun j => norm_le_pi_norm δ j
  have hej : ∀ j, ‖e j‖ ≤ ‖e‖ := fun j => norm_le_pi_norm e j
  have hterm : ∀ j, ‖P j * (σ j - σ' j)‖ ≤ ‖P j‖ * ‖κ j‖ * ‖δ‖ + ‖P j‖ * ‖e‖ := fun j => by
    rw [hdiff j, norm_mul]
    calc ‖P j‖ * ‖κ j * δ j + e j‖ ≤ ‖P j‖ * (‖κ j‖ * ‖δ‖ + ‖e‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (norm_add_le _ _).trans (add_le_add ?_ (hej j))
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hδj j) (norm_nonneg _)
      _ = _ := by ring
  have hsum := norm_sum_le Finset.univ (fun j => P j * (σ j - σ' j))
  rw [Fin.sum_univ_two] at hsum
  have ht0 := ht i
  rw [Fin.sum_univ_two] at ht0
  simp only [Fin.sum_univ_two]
  have hk0 : ‖P 0‖ * ‖κ 0‖ ≤ (‖Q 0‖ + 2 * ρ * y₁⁻¹ ^ 3) * (‖β‖ + ρ) :=
    mul_le_mul (hPQ 0) (hκb 0) (norm_nonneg _) (by positivity)
  have hk1 : ‖P 1‖ * ‖κ 1‖ ≤ (‖Q 1‖ + 2 * ρ * y₁⁻¹ ^ 3) * (‖β‖ + ρ) :=
    mul_le_mul (hPQ 1) (hκb 1) (norm_nonneg _) (by positivity)
  have hcoef : ‖P 0‖ * ‖κ 0‖ + ‖P 1‖ * ‖κ 1‖ ≤ t + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) := by
    have hQ01 : ‖Q 0‖ + ‖Q 1‖ ≤ 2 * y₁⁻¹ ^ 2 := by
      have := hQb 0; have := hQb 1; linarith
    have hb2 : ‖β‖ + ρ ≤ 2 := by linarith
    have hρy : 0 ≤ 2 * ρ * y₁⁻¹ ^ 3 := by positivity
    have hQ0 := norm_nonneg (Q 0)
    have hQ1 := norm_nonneg (Q 1)
    nlinarith [mul_le_mul_of_nonneg_left hb2 hρy, mul_le_mul_of_nonneg_left hQ01 hρ0]
  have hP01 : ‖P 0‖ + ‖P 1‖ ≤ 2 * y₁⁻¹ ^ 2 := by
    have := hPb 0; have := hPb 1; linarith
  have hδ0 := norm_nonneg δ
  have he0 := norm_nonneg e
  calc ‖P 0 * (σ 0 - σ' 0) + P 1 * (σ 1 - σ' 1)‖
      ≤ ‖P 0 * (σ 0 - σ' 0)‖ + ‖P 1 * (σ 1 - σ' 1)‖ := norm_add_le _ _
    _ ≤ (‖P 0‖ * ‖κ 0‖ + ‖P 1‖ * ‖κ 1‖) * ‖δ‖ + (‖P 0‖ + ‖P 1‖) * ‖e‖ := by
        have := hterm 0; have := hterm 1; nlinarith
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef hδ0)
        (mul_le_mul_of_nonneg_right hP01 he0)

/-- **Common-port Lipschitz core.** Shifts as in `cmp_sep_core`, `Σ_j |Q_ij| ≤ Λ`, and
`σ_j - σ'_j = c δ_j + γ (δ_0 + δ_1) + e_j` with `c ≥ 0`. Then
`|tr_i M - tr_i M'| ≤ (c + 2|γ|) (Λ + 4ρ/y₁³) ‖δ‖ + 2 y₁⁻² ‖e‖`. -/
theorem cmp_com_core {y₁ ρ Λ c : ℝ} (hy₁ : 0 < y₁) (hρ0 : 0 ≤ ρ) (hc : 0 ≤ c)
    (σ σ' σ₀ : Fin 2 → ℂ) (hσ : ∀ j, y₁ ≤ -(σ j).im) (hσ' : ∀ j, y₁ ≤ -(σ' j).im)
    (hσ₀ : ∀ j, y₁ ≤ -(σ₀ j).im) (hd : ∀ j, ‖σ j - σ₀ j‖ ≤ ρ) (hd' : ∀ j, ‖σ' j - σ₀ j‖ ≤ ρ)
    (hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv H σ₀) (cmpInv H σ₀) i j‖ ≤ Λ)
    (γ : ℂ) (δ e : Fin 2 → ℂ)
    (hdiff : ∀ j, σ j - σ' j = (c : ℂ) * δ j + γ * (δ 0 + δ 1) + e j) (i : Fin 2) :
    ‖blockTrace (cmpInv H σ) i - blockTrace (cmpInv H σ') i‖ ≤
      (c + 2 * ‖γ‖) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) * ‖δ‖ + 2 * y₁⁻¹ ^ 2 * ‖e‖ := by
  have him : ∀ (τ : Fin 2 → ℂ), (∀ j, y₁ ≤ -(τ j).im) → ∀ j, (τ j).im < 0 :=
    fun τ h j => by linarith [h j]
  rw [cmp_trace_sub H hH σ σ' (him σ hσ) (him σ' hσ') i]
  set P := fun j => cmpPair (cmpInv H σ) (cmpInv H σ') i j with hP
  set Q := fun j => cmpPair (cmpInv H σ₀) (cmpInv H σ₀) i j with hQ
  have hPQ : ∀ j, ‖P j‖ ≤ ‖Q j‖ + 2 * ρ * y₁⁻¹ ^ 3 := fun j => by
    have := cmp_pair_near H hH σ σ' σ₀ hy₁ hρ0 hσ hσ' hσ₀ hd hd' i j
    rw [mul_div_assoc, div_eq_mul_inv, ← inv_pow] at this
    have h2 := norm_sub_norm_le (P j) (Q j)
    linarith
  have hPb : ∀ j, ‖P j‖ ≤ y₁⁻¹ ^ 2 := fun j => by
    rw [sq]; exact cmp_pair_bound H hH σ σ' hy₁ hσ hσ' i j
  have hδj : ∀ j, ‖δ j‖ ≤ ‖δ‖ := fun j => norm_le_pi_norm δ j
  have hej : ∀ j, ‖e j‖ ≤ ‖e‖ := fun j => norm_le_pi_norm e j
  have hterm : ∀ j, ‖P j * (σ j - σ' j)‖ ≤ ‖P j‖ * ((c + 2 * ‖γ‖) * ‖δ‖) + ‖P j‖ * ‖e‖ :=
    fun j => by
    rw [hdiff j, norm_mul, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : ‖(c : ℂ) * δ j‖ ≤ c * ‖δ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (hδj j) hc
    have h2 : ‖γ * (δ 0 + δ 1)‖ ≤ 2 * ‖γ‖ * ‖δ‖ := by
      rw [norm_mul]
      have := (norm_add_le (δ 0) (δ 1)).trans (add_le_add (hδj 0) (hδj 1))
      nlinarith [norm_nonneg γ]
    calc ‖(c : ℂ) * δ j + γ * (δ 0 + δ 1) + e j‖
        ≤ ‖(c : ℂ) * δ j‖ + ‖γ * (δ 0 + δ 1)‖ + ‖e j‖ := norm_add₃_le
      _ ≤ c * ‖δ‖ + 2 * ‖γ‖ * ‖δ‖ + ‖e‖ := by linarith [hej j]
      _ = _ := by ring
  have hsum := norm_sum_le Finset.univ (fun j => P j * (σ j - σ' j))
  rw [Fin.sum_univ_two] at hsum
  have hΛi := hΛ i
  rw [Fin.sum_univ_two] at hΛi
  simp only [Fin.sum_univ_two]
  have hP01 : ‖P 0‖ + ‖P 1‖ ≤ 2 * y₁⁻¹ ^ 2 := by
    have := hPb 0; have := hPb 1; linarith
  have hP01' : ‖P 0‖ + ‖P 1‖ ≤ Λ + 4 * ρ * y₁⁻¹ ^ 3 := by
    have := hPQ 0; have := hPQ 1; linarith
  have hK : 0 ≤ (c + 2 * ‖γ‖) * ‖δ‖ := by positivity
  calc ‖P 0 * (σ 0 - σ' 0) + P 1 * (σ 1 - σ' 1)‖
      ≤ ‖P 0 * (σ 0 - σ' 0)‖ + ‖P 1 * (σ 1 - σ' 1)‖ := norm_add_le _ _
    _ ≤ (‖P 0‖ + ‖P 1‖) * ((c + 2 * ‖γ‖) * ‖δ‖) + (‖P 0‖ + ‖P 1‖) * ‖e‖ := by
        have := hterm 0; have := hterm 1; nlinarith
    _ ≤ (Λ + 4 * ρ * y₁⁻¹ ^ 3) * ((c + 2 * ‖γ‖) * ‖δ‖) + 2 * y₁⁻¹ ^ 2 * ‖e‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hP01' hK)
          (mul_le_mul_of_nonneg_right hP01 (norm_nonneg _))
    _ = _ := by ring

end BlockShift

/-!
## 4. The matched point: tops, shifts and the port maps
-/

section Matched

variable {W : ℕ}

/-- The Hermitian part `-E - X` of the top matrices. -/
def cmpTopH (E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  -((E : ℂ) • 1) - X

/-- Separate-port shifts `c m_j + b u_j`. -/
def cmpSepShift (b : ℝ) (m u : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun j => ((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u j

/-- Common-port shifts `c m_j + b u₀`. -/
def cmpComShift (b : ℝ) (m : Fin 2 → ℂ) (u₀ : ℂ) : Fin 2 → ℂ :=
  fun j => ((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀

theorem cmp_twoPortTop_inv (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m u : Fin 2 → ℂ) : (twoPortTop b E X m u)⁻¹ = cmpInv (cmpTopH E X) (cmpSepShift b m u) :=
  rfl

theorem cmp_commonPortTop_inv (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m : Fin 2 → ℂ) (u₀ : ℂ) :
    (commonPortTop b E X m u₀)⁻¹ = cmpInv (cmpTopH E X) (cmpComShift b m u₀) :=
  rfl

theorem cmpTopH_isHermitian (E : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) : (cmpTopH E X).IsHermitian := by
  unfold cmpTopH
  refine IsHermitian.sub ?_ hX
  refine IsHermitian.neg ?_
  rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- `R = (z_∂ - X)⁻¹` is the block-shifted inverse at the matched shift `(1-b) a`. -/
theorem cmp_resolvent_eq {b E : ℝ} (hE : |E| ≤ 2) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹ =
      cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E) := by
  unfold cmpInv cmpTopH
  congr 1
  rw [boundaryZ_eq hE]
  ext p q
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, diagonal_apply, cmpExt,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> ring

theorem cmpSepShift_const (b : ℝ) (a : ℂ) :
    cmpSepShift b (fun _ => a) (fun _ => a) = fun _ => (1 - (b : ℂ)) * a := by
  funext j; unfold cmpSepShift; push_cast; ring

theorem cmpComShift_const (b : ℝ) (a : ℂ) :
    cmpComShift b (fun _ => a) a = fun _ => (1 - (b : ℂ)) * a := by
  funext j; unfold cmpComShift; push_cast; ring

/-- **Port map near the matched point.** `|a| = 1`, `|e| ≤ 1/2`: `q = a⁻¹ - e ≠ 0`,
`|q⁻¹| ≤ 2` and `q⁻¹ - a = a e q⁻¹`. -/
theorem cmp_port {a e : ℂ} (ha : ‖a‖ = 1) (he : ‖e‖ ≤ 1 / 2) :
    a⁻¹ - e ≠ 0 ∧ ‖(a⁻¹ - e)⁻¹‖ ≤ 2 ∧ (a⁻¹ - e)⁻¹ - a = a * e * (a⁻¹ - e)⁻¹ := by
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hai : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha, inv_one]
  have hq : 1 / 2 ≤ ‖a⁻¹ - e‖ := by
    have := norm_sub_norm_le a⁻¹ e; linarith
  have hq0 : a⁻¹ - e ≠ 0 := by
    intro h; rw [h, norm_zero] at hq; linarith
  refine ⟨hq0, ?_, ?_⟩
  · rw [norm_inv]
    calc ‖a⁻¹ - e‖⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) hq
      _ = 2 := by norm_num
  · have hq1 : (a⁻¹ - e)⁻¹ * (a⁻¹ - e) = 1 := inv_mul_cancel₀ hq0
    have hq2 : a * (a⁻¹ - e) = 1 - a * e := by rw [mul_sub, mul_inv_cancel₀ ha0]
    linear_combination a * hq1 - (a⁻¹ - e)⁻¹ * hq2

/-- Difference of port values: `(z - b w)⁻¹ - (z - b w')⁻¹ = b (w - w') (z - b w)⁻¹ (z - b w')⁻¹`
when both denominators are nonzero. -/
theorem cmp_port_sub {z w w' : ℂ} {b : ℂ} (h : z - b * w ≠ 0) (h' : z - b * w' ≠ 0) :
    (z - b * w)⁻¹ - (z - b * w')⁻¹ = b * (w - w') * ((z - b * w)⁻¹ * (z - b * w')⁻¹) := by
  field_simp
  ring

/-- Generic port estimate: `|a| = 1`, `|e| ≤ 1/2`, `q = a⁻¹ - e`: `q ≠ 0`,
`|q⁻¹ - a| = |e| |q⁻¹|`, `|q⁻¹| ≤ 2`, `|q⁻¹| ≤ 1 + 2|e|`, `|q⁻¹ - a| ≤ 2|e|`. -/
theorem cmp_port' {a e : ℂ} (ha : ‖a‖ = 1) (he : ‖e‖ ≤ 1 / 2) :
    a⁻¹ - e ≠ 0 ∧ ‖(a⁻¹ - e)⁻¹ - a‖ = ‖e‖ * ‖(a⁻¹ - e)⁻¹‖ ∧ ‖(a⁻¹ - e)⁻¹‖ ≤ 2 ∧
      ‖(a⁻¹ - e)⁻¹‖ ≤ 1 + 2 * ‖e‖ ∧ ‖(a⁻¹ - e)⁻¹ - a‖ ≤ 2 * ‖e‖ := by
  obtain ⟨hq0, hq2, hid⟩ := cmp_port ha he
  have h1 : ‖(a⁻¹ - e)⁻¹ - a‖ = ‖e‖ * ‖(a⁻¹ - e)⁻¹‖ := by
    rw [hid, norm_mul, norm_mul, ha, one_mul]
  have h2 : ‖(a⁻¹ - e)⁻¹ - a‖ ≤ 2 * ‖e‖ := by
    rw [h1]; nlinarith [norm_nonneg e, norm_nonneg (a⁻¹ - e)⁻¹]
  refine ⟨hq0, h1, hq2, ?_, h2⟩
  have := norm_le_norm_add_norm_sub' ((a⁻¹ - e)⁻¹) a
  rw [ha] at this
  linarith

/-- Membership in the closed sup-norm ball around a constant vector. -/
theorem cmp_mem_ball_iff {a : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (m : Fin 2 → ℂ) :
    m ∈ Metric.closedBall (fun _ : Fin 2 => a) ρ ↔ ∀ j, ‖m j - a‖ ≤ ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hρ]
  rfl

/-- `-Im` lower bound transferred to a nearby shift. -/
theorem cmp_im_of_near {σ σ₀ : ℂ} {y ρ : ℝ} (h0 : 2 * y ≤ -σ₀.im) (hρ : ρ ≤ y)
    (hd : ‖σ - σ₀‖ ≤ ρ) : y ≤ -σ.im := by
  have := Complex.im_le_norm (σ - σ₀)
  rw [Complex.sub_im] at this
  linarith

/-- Uniform bulk constants: for `κ > 0` there is `α₀ ∈ (0, 1]` with `|E| < 2`, `|a| = 1` and
`Im a ≤ -α₀` on `bulkInterval κ` (`a = matchedA E`). -/
theorem cmp_bulk_setup {κ : ℝ} (hκ : 0 < κ) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ α₀ ≤ 1 ∧ ∀ E ∈ bulkInterval κ,
      |E| < 2 ∧ ‖matchedA E‖ = 1 ∧ (matchedA E).im ≤ -α₀ := by
  set κ' := min κ 1 with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  refine ⟨Real.sqrt (4 - (2 - κ') ^ 2) / 2, ?_, ?_, ?_⟩
  · have := Real.sqrt_pos.mpr (four_sub_sq_pos hκ'0 (by linarith)); linarith
  · have : Real.sqrt (4 - (2 - κ') ^ 2) ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · intro E hE
    have hE' : E ∈ bulkInterval κ' := ⟨by linarith [hE.1, min_le_left κ 1], by
      linarith [hE.2, min_le_left κ 1]⟩
    have habs := abs_lt_two_of_mem_bulkInterval hκ hE
    exact ⟨habs, norm_matchedA habs.le, by
      have := matchedA_im_le_of_mem_bulkInterval hE'; linarith⟩

/-- `|tr_i R - a| ≤ d(X)` for each block. -/
theorem cmp_le_matchedDistance (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (i : Fin 2) :
    ‖blockTrace ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X)⁻¹) i -
      matchedA E‖ ≤ matchedDistance b E X := by
  unfold matchedDistance
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

end Matched

/-!
## 5. Separate ports: existence, closeness, outgoing contraction, stability
-/

/-- Algebra of the separate shift around the matched point. -/
theorem cmpSepShift_sub_matched (b : ℝ) (a : ℂ) (m u : Fin 2 → ℂ) (j : Fin 2) :
    cmpSepShift b m u j - (1 - (b : ℂ)) * a =
      ((1 - 2 * b : ℝ) : ℂ) * (m j - a) + (b : ℂ) * (u j - a) := by
  unfold cmpSepShift; push_cast; ring

/-- Algebra of the common shift around the matched point. -/
theorem cmpComShift_sub_matched (b : ℝ) (a : ℂ) (m : Fin 2 → ℂ) (u₀ : ℂ) (j : Fin 2) :
    cmpComShift b m u₀ j - (1 - (b : ℂ)) * a =
      ((1 - 2 * b : ℝ) : ℂ) * (m j - a) + (b : ℂ) * (u₀ - a) := by
  unfold cmpComShift; push_cast; ring

theorem cmp_norm_real_mul {r : ℝ} (hr : 0 ≤ r) (x : ℂ) : ‖(r : ℂ) * x‖ = r * ‖x‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

/-- Port bounds for the separate port `u = (z - b w)⁻¹`, `z - b w = a⁻¹ - b (w - a)`. -/
theorem cmp_sep_port {a z w : ℂ} {b ρ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 ≤ b) (hbρ : b * ρ ≤ 1 / 2)
    (hzq : z - (b : ℂ) * w = a⁻¹ - (b : ℂ) * (w - a)) (hw : ‖w - a‖ ≤ ρ) :
    z - (b : ℂ) * w ≠ 0 ∧ ‖(z - (b : ℂ) * w)⁻¹ - a‖ = b * ‖w - a‖ * ‖(z - (b : ℂ) * w)⁻¹‖ ∧
      ‖(z - (b : ℂ) * w)⁻¹‖ ≤ 2 ∧ ‖(z - (b : ℂ) * w)⁻¹‖ ≤ 1 + 2 * b * ρ ∧
      ‖(z - (b : ℂ) * w)⁻¹ - a‖ ≤ 2 * b * ‖w - a‖ := by
  have hne : ‖(b : ℂ) * (w - a)‖ = b * ‖w - a‖ := cmp_norm_real_mul hb0 _
  have hbw : b * ‖w - a‖ ≤ b * ρ := mul_le_mul_of_nonneg_left hw hb0
  have he : ‖(b : ℂ) * (w - a)‖ ≤ 1 / 2 := by rw [hne]; linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := cmp_port' ha1 he
  rw [hzq]
  refine ⟨h1, by rw [h2, hne], h3, ?_, by rw [hne] at h5; linarith⟩
  rw [hne] at h4; linarith

/-- The separate shift stays within `ρ` of the matched shift when `m, u` do. -/
theorem cmp_sep_shift_near {b ρ : ℝ} {a : ℂ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (m u : Fin 2 → ℂ)
    (j : Fin 2) (hm : ‖m j - a‖ ≤ ρ) (hu : ‖u j - a‖ ≤ ρ) :
    ‖cmpSepShift b m u j - (1 - (b : ℂ)) * a‖ ≤ ρ := by
  rw [cmpSepShift_sub_matched]
  refine (norm_add_le _ _).trans ?_
  rw [cmp_norm_real_mul (by linarith) , cmp_norm_real_mul hb0]
  have h1 := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 1 - 2 * b by linarith)
  have h2 := mul_le_mul_of_nonneg_left hu hb0
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hm
  nlinarith

/-- **One comparison step, separate ports.** `M` uses the port map of `m`; `M'` uses
`u' = (z - b m')⁻¹ + e`. Then `|tr_i M - tr_i M'| ≤ t₁ ‖m - m'‖ + 2 y₁⁻² ‖e‖`. -/
theorem cmp_sep_step {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z β : ℂ} {b ρ y₁ t' t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w : ℂ, z - (b : ℂ) * w = a⁻¹ - (b : ℂ) * (w - a))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hβ : β = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2) (hβ1 : ‖β‖ ≤ 1)
    (hmarg : ∀ i, ‖β‖ * ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ t')
    (hcoef : t' + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) ≤ t₁)
    (m m' u' e : Fin 2 → ℂ) (hm : ∀ j, ‖m j - a‖ ≤ ρ) (hm' : ∀ j, ‖m' j - a‖ ≤ ρ)
    (hs' : ∀ j, ‖cmpSepShift b m' u' j - (1 - (b : ℂ)) * a‖ ≤ ρ)
    (hu' : ∀ j, u' j = (z - (b : ℂ) * m' j)⁻¹ + e j) (i : Fin 2) :
    ‖blockTrace (cmpInv H (cmpSepShift b m (fun j => (z - (b : ℂ) * m j)⁻¹))) i -
        blockTrace (cmpInv H (cmpSepShift b m' u')) i‖ ≤
      t₁ * ‖m - m'‖ + 2 * y₁⁻¹ ^ 2 * ‖e‖ := by
  have hbρ : b * ρ ≤ 1 / 2 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have h2b : 2 * b ≤ 1 := by linarith
  have hport := fun w (hw : ‖w - a‖ ≤ ρ) => cmp_sep_port ha1 hb0.le hbρ (hzq w) hw
  have hUa : ∀ j, ‖(z - (b : ℂ) * m j)⁻¹ - a‖ ≤ ρ := fun j => by
    have h := (hport _ (hm j)).2.2.2.2
    have := mul_le_mul h2b (hm j) (norm_nonneg _) zero_le_one
    linarith
  have hsm : ∀ j, ‖cmpSepShift b m (fun j => (z - (b : ℂ) * m j)⁻¹) j -
      (1 - (b : ℂ)) * a‖ ≤ ρ :=
    fun j => cmp_sep_shift_near hb0.le hb1.le m _ j (hm j) (hUa j)
  have hσ : ∀ j, y₁ ≤ -(cmpSepShift b m (fun j => (z - (b : ℂ) * m j)⁻¹) j).im :=
    fun j => cmp_im_of_near hσ₀im hρy (hsm j)
  have hσ' : ∀ j, y₁ ≤ -(cmpSepShift b m' u' j).im :=
    fun j => cmp_im_of_near hσ₀im hρy (hs' j)
  have hσ₀ : ∀ j : Fin 2, y₁ ≤ -((fun _ => (1 - (b : ℂ)) * a) j).im := fun _ => by
    simp only; linarith
  set κc : Fin 2 → ℂ := fun j => ((1 - 2 * b : ℝ) : ℂ) +
    (b : ℂ) ^ 2 * ((z - (b : ℂ) * m j)⁻¹ * (z - (b : ℂ) * m' j)⁻¹) with hκc
  have hdiff : ∀ j, cmpSepShift b m (fun j => (z - (b : ℂ) * m j)⁻¹) j -
      cmpSepShift b m' u' j = κc j * (m - m') j + (fun j => -(b : ℂ) * e j) j := fun j => by
    have hsub := cmp_port_sub (z := z) (b := (b : ℂ)) (hport _ (hm j)).1 (hport _ (hm' j)).1
    simp only [cmpSepShift, hκc, Pi.sub_apply, hu' j]
    rw [show ((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * (z - (b : ℂ) * m j)⁻¹ -
        (((1 - 2 * b : ℝ) : ℂ) * m' j + (b : ℂ) * ((z - (b : ℂ) * m' j)⁻¹ + e j)) =
        ((1 - 2 * b : ℝ) : ℂ) * (m j - m' j) + (b : ℂ) * ((z - (b : ℂ) * m j)⁻¹ -
          (z - (b : ℂ) * m' j)⁻¹) - (b : ℂ) * e j by ring, hsub]
    ring
  have hκ : ∀ j, ‖κc j - β‖ ≤ ρ := fun j => by
    obtain ⟨-, -, hU2, -, hUa1⟩ := hport _ (hm j)
    obtain ⟨-, -, -, -, hUa2⟩ := hport _ (hm' j)
    set U := (z - (b : ℂ) * m j)⁻¹
    set U' := (z - (b : ℂ) * m' j)⁻¹
    have hk : κc j - β = (b : ℂ) ^ 2 * (U * (U' - a) + a * (U - a)) := by
      simp only [hκc, hβ]; ring
    rw [hk, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have hb1' : 2 * b * ‖m j - a‖ ≤ 2 * b * ρ := mul_le_mul_of_nonneg_left (hm j) (by linarith)
    have hb2' : 2 * b * ‖m' j - a‖ ≤ 2 * b * ρ :=
      mul_le_mul_of_nonneg_left (hm' j) (by linarith)
    have h1 : ‖U * (U' - a) + a * (U - a)‖ ≤ 6 * b * ρ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, ha1, one_mul]
      have := mul_le_mul hU2 (hUa2.trans hb2') (norm_nonneg _) zero_le_two
      linarith
    have hb3 : b ^ 2 * (6 * b * ρ) ≤ ρ := by
      have hbb : b ^ 2 * (6 * b) ≤ 1 := by
        have : b ^ 2 ≤ 1 / 4 := by nlinarith
        have := mul_le_mul this (show 6 * b ≤ 3 by linarith) (by positivity) (by norm_num)
        linarith
      have := mul_le_mul_of_nonneg_right hbb hρ0.le
      linarith
    calc b ^ 2 * ‖U * (U' - a) + a * (U - a)‖ ≤ b ^ 2 * (6 * b * ρ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ ρ := hb3
  have hcore := cmp_sep_core H hH hy₁ hρ0.le (by linarith) _ _ (fun _ => (1 - (b : ℂ)) * a)
    hσ hσ' hσ₀ hsm hs' β hβ1 hmarg κc (m - m') (fun j => -(b : ℂ) * e j) hκ hdiff i
  have hecore : ‖(fun j => -(b : ℂ) * e j : Fin 2 → ℂ)‖ ≤ ‖e‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg e)).mpr fun j => ?_
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have := norm_le_pi_norm e j
    have := mul_le_mul_of_nonneg_right (show b ≤ 1 by linarith) (norm_nonneg (e j))
    linarith
  refine hcore.trans ?_
  have hy2 : 0 ≤ 2 * y₁⁻¹ ^ 2 := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hecore hy2)

/-- **Existence of the comparison solution, separate ports** (Banach fixed point on the
closed sup-norm ball of radius `ρ` around `(a, a)`). If `|tr_i R - a| ≤ d ≤ (1 - t₁) ρ` there is
a fixed point `m` of `m ↦ tr[(H - diag(c m + b (z - b m)⁻¹))⁻¹]` with `‖m - a‖ ≤ d/(1 - t₁)`. -/
theorem cmp_sep_exists {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z β : ℂ} {b ρ y₁ t' t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w : ℂ, z - (b : ℂ) * w = a⁻¹ - (b : ℂ) * (w - a))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hβ : β = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2) (hβ1 : ‖β‖ ≤ 1)
    (hmarg : ∀ i, ‖β‖ * ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ t')
    (hcoef : t' + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) ≤ t₁) (ht₁0 : 0 ≤ t₁) (ht₁1 : t₁ < 1) {d : ℝ} (hd0 : 0 ≤ d) (hdρ : d ≤ (1 - t₁) * ρ)
    (hR : ∀ i, ‖blockTrace (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i - a‖ ≤ d) :
    ∃ ms : Fin 2 → ℂ, (∀ i, blockTrace (cmpInv H (cmpSepShift b ms
        (fun j => (z - (b : ℂ) * ms j)⁻¹))) i = ms i) ∧
      ‖ms - fun _ => a‖ ≤ d / (1 - t₁) := by
  have h1t0 : 0 < 1 - t₁ := by linarith
  have hbρ : b * ρ ≤ 1 / 2 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have h2b : 2 * b ≤ 1 := by linarith
  have hUa : ∀ w : ℂ, ‖w - a‖ ≤ ρ → ‖(z - (b : ℂ) * w)⁻¹ - a‖ ≤ ρ := fun w hw => by
    have h := (cmp_sep_port ha1 hb0.le hbρ (hzq w) hw).2.2.2.2
    have := mul_le_mul h2b hw (norm_nonneg _) zero_le_one
    linarith
  obtain ⟨F, hF⟩ : ∃ F : (Fin 2 → ℂ) → (Fin 2 → ℂ), F = fun m i =>
      blockTrace (cmpInv H (cmpSepShift b m (fun j => (z - (b : ℂ) * m j)⁻¹))) i := ⟨_, rfl⟩
  have hstep : ∀ m m' : Fin 2 → ℂ, (∀ j, ‖m j - a‖ ≤ ρ) → (∀ j, ‖m' j - a‖ ≤ ρ) →
      ∀ i, ‖F m i - F m' i‖ ≤ t₁ * ‖m - m'‖ := fun m m' hm hm' i => by
    have h := cmp_sep_step H hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁ hzq hσ₀im hβ hβ1 hmarg hcoef
      m m' (fun j => (z - (b : ℂ) * m' j)⁻¹) 0 hm hm'
      (fun j => cmp_sep_shift_near hb0.le hb1.le m' _ j (hm' j) (hUa _ (hm' j)))
      (fun j => by simp) i
    rw [hF]
    simpa using h
  have hza : (z - (b : ℂ) * a)⁻¹ = a := by rw [hzq, sub_self, mul_zero, sub_zero, inv_inv]
  have hFa : ∀ i, ‖F (fun _ => a) i - a‖ ≤ d := fun i => by
    have h1 : (fun j : Fin 2 => (z - (b : ℂ) * (fun _ : Fin 2 => a) j)⁻¹) = fun _ => a := by
      funext j; exact hza
    rw [hF]
    simp only
    rw [h1, cmpSepShift_const]
    exact hR i
  have hconst : ∀ j : Fin 2, ‖(fun _ : Fin 2 => a) j - a‖ ≤ ρ := fun j => by simp [hρ0.le]
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin 2 → ℂ), S = Metric.closedBall (fun _ : Fin 2 => a) ρ :=
    ⟨_, rfl⟩
  have hmaps : Set.MapsTo F S S := fun m hm => by
    rw [hS, cmp_mem_ball_iff hρ0.le] at hm ⊢
    intro i
    have h1 := hstep m (fun _ => a) hm hconst i
    have h2 : ‖m - fun _ => a‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ0.le).mpr hm
    have h3 := hFa i
    have h4 := norm_sub_le_norm_sub_add_norm_sub (F m i) (F (fun _ => a) i) a
    have h5 := mul_le_mul_of_nonneg_left h2 ht₁0
    have h6 : t₁ * ρ + (1 - t₁) * ρ = ρ := by ring
    linarith
  have hcontr : ContractingWith (Real.toNNReal t₁) (hmaps.restrict F S S) := by
    refine ⟨Real.toNNReal_lt_one.mpr ht₁1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
      Set.MapsTo.val_restrict_apply, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ ht₁0]
    have hx : ∀ j, ‖(x : Fin 2 → ℂ) j - a‖ ≤ ρ :=
      (cmp_mem_ball_iff hρ0.le _).mp (hS ▸ x.2)
    have hy : ∀ j, ‖(y : Fin 2 → ℂ) j - a‖ ≤ ρ :=
      (cmp_mem_ball_iff hρ0.le _).mp (hS ▸ y.2)
    exact (pi_norm_le_iff_of_nonneg (mul_nonneg ht₁0 (norm_nonneg _))).mpr
      fun i => hstep _ _ hx hy i
  have hScomp : IsComplete S := by rw [hS]; exact Metric.isClosed_closedBall.isComplete
  have haS : (fun _ : Fin 2 => a) ∈ S := by rw [hS]; exact Metric.mem_closedBall_self hρ0.le
  obtain ⟨ms, hmsS, hfix, -⟩ := hcontr.exists_fixedPoint' hScomp hmaps haS (edist_ne_top _ _)
  have hms : ∀ j, ‖ms j - a‖ ≤ ρ := (cmp_mem_ball_iff hρ0.le ms).mp (hS ▸ hmsS)
  have hfix' : ∀ i, F ms i = ms i := fun i => congrFun hfix i
  refine ⟨ms, fun i => by have := hfix' i; rw [hF] at this; exact this, ?_⟩
  rw [le_div_iff₀ h1t0]
  have hD : ‖ms - fun _ => a‖ ≤ t₁ * ‖ms - fun _ => a‖ + d := by
    refine (pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg ht₁0 (norm_nonneg _)) hd0)).mpr
      fun i => ?_
    have h1 := hstep ms (fun _ => a) hms hconst i
    have h3 := hFa i
    have h4 := norm_sub_le_norm_sub_add_norm_sub (F ms i) (F (fun _ => a) i) a
    rw [hfix' i] at h1 h4
    show ‖ms i - a‖ ≤ _
    linarith
  linarith

/-- **Stability of the comparison solution, separate ports.** If `m` is the fixed point with
`|m_j - a| ≤ ρ/2` and `(m', u')` is within `ρ/4` of `(m, (z - b m)⁻¹)` and solves the equations
up to residuals `(r, r')`, then `|m'_i - m_i| + |u'_i - u_i| ≤ C_B (‖r‖ + ‖r'‖)` with
`C_B = 3(1 + 2y₁⁻²)/(1 - t₁) + 1`. -/
theorem cmp_sep_stab {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z β : ℂ} {b ρ y₁ t' t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w : ℂ, z - (b : ℂ) * w = a⁻¹ - (b : ℂ) * (w - a))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hβ : β = ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * a ^ 2) (hβ1 : ‖β‖ ≤ 1)
    (hmarg : ∀ i, ‖β‖ * ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ t')
    (hcoef : t' + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) ≤ t₁) (ht₁0 : 0 ≤ t₁) (ht₁1 : t₁ < 1)
    (ms : Fin 2 → ℂ) (hfix : ∀ i, blockTrace (cmpInv H (cmpSepShift b ms
        (fun j => (z - (b : ℂ) * ms j)⁻¹))) i = ms i) (hms : ∀ j, ‖ms j - a‖ ≤ ρ / 2)
    (m' u' r r' : Fin 2 → ℂ)
    (hnear : ∀ i, ‖m' i - ms i‖ ≤ ρ / 4 ∧ ‖u' i - (z - (b : ℂ) * ms i)⁻¹‖ ≤ ρ / 4)
    (heq : ∀ i, m' i = blockTrace (cmpInv H (cmpSepShift b m' u')) i + r i ∧
      u' i = (z - (b : ℂ) * m' i)⁻¹ + r' i) (i : Fin 2) :
    ‖m' i - ms i‖ + ‖u' i - (z - (b : ℂ) * ms i)⁻¹‖ ≤
      (3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) := by
  have h1t0 : 0 < 1 - t₁ := by linarith
  have hbρ : b * ρ ≤ 1 / 2 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have hport := fun w (hw : ‖w - a‖ ≤ ρ) => cmp_sep_port ha1 hb0.le hbρ (hzq w) hw
  have hms' : ∀ j, ‖ms j - a‖ ≤ ρ := fun j => (hms j).trans (by linarith)
  have hm' : ∀ j, ‖m' j - a‖ ≤ ρ := fun j => by
    have := norm_sub_le_norm_sub_add_norm_sub (m' j) (ms j) a
    linarith [(hnear j).1, hms j]
  have hu'a : ∀ j, ‖u' j - a‖ ≤ ρ := fun j => by
    have := norm_sub_le_norm_sub_add_norm_sub (u' j) ((z - (b : ℂ) * ms j)⁻¹) a
    have h1 := (hport _ (hms' j)).2.2.2.2
    have h2 := mul_le_mul_of_nonneg_left (hms j) (show 0 ≤ 2 * b by linarith)
    have h3 : 2 * b * (ρ / 2) ≤ ρ / 2 := by nlinarith
    linarith [(hnear j).2]
  have hu' : ∀ j, u' j = (z - (b : ℂ) * m' j)⁻¹ + r' j := fun j => (heq j).2
  have h := cmp_sep_step H hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁ hzq hσ₀im hβ hβ1 hmarg hcoef
    ms m' u' r' hms' hm' (fun j => cmp_sep_shift_near hb0.le hb1.le m' u' j (hm' j) (hu'a j))
    hu'
  have hy2 : 0 ≤ y₁⁻¹ ^ 2 := sq_nonneg _
  have hDb : ‖ms - m'‖ * (1 - t₁) ≤ ‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ := by
    have hD : ‖ms - m'‖ ≤ t₁ * ‖ms - m'‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ + ‖r‖ := by
      refine (pi_norm_le_iff_of_nonneg (add_nonneg (add_nonneg (mul_nonneg ht₁0
        (norm_nonneg _)) (mul_nonneg (by linarith) (norm_nonneg _))) (norm_nonneg _))).mpr
        fun k => ?_
      have h1 := h k
      rw [hfix k] at h1
      have h3 : ms k - m' k = (ms k - blockTrace (cmpInv H (cmpSepShift b m' u')) k) - r k := by
        rw [(heq k).1]; ring
      show ‖ms k - m' k‖ ≤ _
      rw [h3]
      have := norm_sub_le (ms k - blockTrace (cmpInv H (cmpSepShift b m' u')) k) (r k)
      have := norm_le_pi_norm r k
      linarith
    linarith
  have hD' : ‖ms - m'‖ ≤ (‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖) / (1 - t₁) := by
    rw [le_div_iff₀ h1t0]; exact hDb
  have hmi : ‖m' i - ms i‖ ≤ ‖ms - m'‖ := by
    rw [norm_sub_rev]; exact norm_le_pi_norm (ms - m') i
  have hui : ‖u' i - (z - (b : ℂ) * ms i)⁻¹‖ ≤ 2 * ‖m' i - ms i‖ + ‖r'‖ := by
    obtain ⟨hne, -, hU2, -, -⟩ := hport _ (hm' i)
    obtain ⟨hne', -, hU2', -, -⟩ := hport _ (hms' i)
    have hsub := cmp_port_sub (z := z) (b := (b : ℂ)) hne hne'
    have : u' i - (z - (b : ℂ) * ms i)⁻¹ =
        ((z - (b : ℂ) * m' i)⁻¹ - (z - (b : ℂ) * ms i)⁻¹) + r' i := by
      rw [hu' i]; ring
    rw [this, hsub]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h1 := mul_le_mul hU2 hU2' (norm_nonneg _) zero_le_two
    have h2 : b * ‖m' i - ms i‖ * (‖(z - (b : ℂ) * m' i)⁻¹‖ * ‖(z - (b : ℂ) * ms i)⁻¹‖) ≤
        b * ‖m' i - ms i‖ * (2 * 2) :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hb0.le (norm_nonneg _))
    have h3 : b * ‖m' i - ms i‖ * (2 * 2) ≤ 2 * ‖m' i - ms i‖ := by
      have := mul_le_mul_of_nonneg_right (show 4 * b ≤ 2 by linarith) (norm_nonneg (m' i - ms i))
      linarith
    linarith [norm_le_pi_norm r' i]
  have hr0 := norm_nonneg r
  have hr0' := norm_nonneg r'
  have hfin : ‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ ≤ (1 + 2 * y₁⁻¹ ^ 2) * (‖r‖ + ‖r'‖) := by
    have := mul_nonneg hy2 hr0
    nlinarith
  have hfin' : 3 * ((‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖) / (1 - t₁)) ≤
      3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖) := by
    rw [show 3 * ((‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖) / (1 - t₁)) =
        (3 * (‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖)) / (1 - t₁) by ring,
      show 3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖) =
        (3 * ((1 + 2 * y₁⁻¹ ^ 2) * (‖r‖ + ‖r'‖))) / (1 - t₁) by ring]
    exact div_le_div_of_nonneg_right (by linarith) h1t0.le
  have hfin'' : 3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖) + (‖r‖ + ‖r'‖) =
      (3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) := by ring
  linarith

/-- **Separate ports, (A)+(B).** `b ∈ (0, 1/2)` and `κ > 0` first; then `d_* > 0`, `C`,
`q_* ∈ [0, 1)`, `ρ_B > 0`, `C_B`; uniformly in `W ≥ 1`, Hermitian two-port `X`,
`E ∈ bulkInterval κ` with `d(X) ≤ d_*` (`d` at `z_∂`): there is a solution `(m, u)` of
the two-port Dyson equation with `Im m_i, Im u_i < 0`, `|m_i - a| + |u_i - a| ≤ C d(X)`, outgoing error
`|u_i - a| ≤ q_* d(X)`, and every `(m', u')` within `ρ_B` of `(m, u)` solving the equations up to
residuals `(r, r')` satisfies `|m'_i - m_i| + |u'_i - u_i| ≤ C_B (‖r‖ + ‖r'‖)` (sup norms). -/
theorem cmp_twoPort_stable : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C qstar ρB CB : ℝ, 0 < dstar ∧ 0 ≤ C ∧ 0 ≤ qstar ∧ qstar < 1 ∧ 0 < ρB ∧ 0 ≤ CB ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
        (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
        (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
        (∀ i, ‖u i - matchedA E‖ ≤ qstar * matchedDistance b E X) ∧
        ∀ m' u' r r' : Fin 2 → ℂ, (∀ i, ‖m' i - m i‖ ≤ ρB ∧ ‖u' i - u i‖ ≤ ρB) →
          (∀ i, m' i = blockTrace (twoPortTop b E X m' u')⁻¹ i + r i ∧
            u' i = (boundaryZ b E - (b : ℂ) * m' i)⁻¹ + r' i) →
          ∀ i, ‖m' i - m i‖ + ‖u' i - u i‖ ≤ CB * (‖r‖ + ‖r'‖) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨dm, t, hdm, htlt, hmargin⟩ := strictContraction_margin b hb0 hb1 κ hκ
  obtain ⟨q, -, hscal⟩ := strictContraction_scalar b hb0 hb1 κ hκ
  obtain ⟨t', ht'⟩ : ∃ x : ℝ, x = max t 0 := ⟨_, rfl⟩
  have ht'0 : 0 ≤ t' := ht' ▸ le_max_right _ _
  have htt' : t ≤ t' := ht' ▸ le_max_left _ _
  have ht'lt : t' < 1 - b := ht' ▸ max_lt htlt (by linarith)
  obtain ⟨y₁, hy₁⟩ : ∃ x : ℝ, x = (1 - b) * α₀ / 2 := ⟨_, rfl⟩
  have hy₁0 : 0 < y₁ := hy₁ ▸ div_pos (mul_pos (by linarith) hα₀) two_pos
  have hy₁α : y₁ < α₀ := by rw [hy₁]; nlinarith
  obtain ⟨K₁, hK₁⟩ : ∃ x : ℝ, x = 2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3 := ⟨_, rfl⟩
  have hyi0 : 0 < y₁⁻¹ := inv_pos.mpr hy₁0
  have hK₁0 : 0 < K₁ := by
    have := pow_pos hyi0 2; have := pow_pos hyi0 3; rw [hK₁]; linarith
  obtain ⟨g, hg⟩ : ∃ x : ℝ, x = 1 - b - t' := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith
  obtain ⟨t₁, ht₁⟩ : ∃ x : ℝ, x = (t' + 1 - b) / 2 := ⟨_, rfl⟩
  have h1t : 1 - t₁ = b + g / 2 := by rw [ht₁, hg]; ring
  have h1t0 : 0 < 1 - t₁ := by rw [h1t]; linarith
  have ht₁0 : 0 ≤ t₁ := by rw [ht₁]; linarith
  have ht₁1 : t₁ < 1 := by linarith
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = min (min y₁ (1 / 4)) (min (g / (4 * K₁)) (g / 4)) :=
    ⟨_, rfl⟩
  have hρ0 : 0 < ρ := hρ ▸ lt_min (lt_min hy₁0 (by norm_num))
    (lt_min (div_pos hg0 (by linarith)) (by linarith))
  have hρy : ρ ≤ y₁ := hρ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := hρ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρK' : ρ ≤ g / (4 * K₁) := hρ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hρg : ρ ≤ g / 4 := hρ ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hρK : ρ * K₁ ≤ g / 4 := by
    calc ρ * K₁ ≤ g / (4 * K₁) * K₁ := mul_le_mul_of_nonneg_right hρK' hK₁0.le
      _ = g / 4 := by field_simp
  have hcoef : t' + ρ * (2 * y₁⁻¹ ^ 2 + 8 * y₁⁻¹ ^ 3) ≤ t₁ := by
    rw [← hK₁, ht₁]; rw [hg] at hρK; linarith
  have hbρ : b * ρ ≤ 1 / 2 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  obtain ⟨dstar, hdstar⟩ : ∃ x : ℝ, x = min dm ((1 - t₁) * ρ / 2) := ⟨_, rfl⟩
  have hdstar0 : 0 < dstar := hdstar ▸ lt_min hdm (div_pos (mul_pos h1t0 hρ0) two_pos)
  have hdstar1 : dstar ≤ dm := hdstar ▸ min_le_left _ _
  have hdstar2 : dstar ≤ (1 - t₁) * ρ / 2 := hdstar ▸ min_le_right _ _
  have h1bρ : 0 ≤ 1 + 2 * b * ρ := by have := mul_pos hb0 hρ0; linarith
  have hy2 : 0 ≤ y₁⁻¹ ^ 2 := sq_nonneg _
  have hq1 : b * (1 + 2 * b * ρ) / (1 - t₁) < 1 := by
    rw [div_lt_one h1t0, h1t]
    have hb2 : b * b ≤ 1 / 4 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hb2 hρ0.le
    have h2 : g / 4 < g / 2 := by linarith
    nlinarith
  refine ⟨dstar, (1 + 2 * b) / (1 - t₁), b * (1 + 2 * b * ρ) / (1 - t₁), ρ / 4,
    3 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1, hdstar0, div_nonneg (by linarith) h1t0.le,
    div_nonneg (mul_nonneg hb0.le h1bρ) h1t0.le, hq1, by linarith,
    add_nonneg (div_nonneg (by linarith) h1t0.le) zero_le_one, ?_⟩
  intro W hW X hX E hE hd
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hβ1 : ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ ≤ 1 := by
    have h := (hscal E hE).1
    have : (1 - b) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hzq : ∀ w : ℂ, boundaryZ b E - (b : ℂ) * w = (matchedA E)⁻¹ - (b : ℂ) * (w - matchedA E) :=
    fun w => by unfold boundaryZ; ring
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hdρ : matchedDistance b E X ≤ (1 - t₁) * ρ / 2 := hd.trans hdstar2
  have hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * matchedA E).im := by
    have : ((1 - (b : ℂ)) * matchedA E).im = (1 - b) * (matchedA E).im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im]
      ring
    rw [this, hy₁]
    have := mul_le_mul_of_nonneg_left haim (show (0 : ℝ) ≤ 1 - b by linarith)
    linarith
  have hH : (cmpTopH E X).IsHermitian := cmpTopH_isHermitian E hX
  have hR := cmp_resolvent_eq (b := b) hEabs.le X
  have hmarg : ∀ i, ‖((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2‖ *
      ∑ j, ‖cmpPair (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E))
        (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i j‖ ≤ t' := fun i => by
    have := hmargin W hW X hX E hE (hd.trans hdstar1) i
    rw [hR] at this
    simp only [← cmpPair_self] at this
    linarith
  have hRd : ∀ i, ‖blockTrace (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i -
      matchedA E‖ ≤ matchedDistance b E X := fun i => by
    rw [← hR]; exact cmp_le_matchedDistance b E X i
  obtain ⟨ms, hfix, hDle⟩ := cmp_sep_exists (cmpTopH E X) hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁0 hzq
    hσ₀im rfl hβ1 hmarg hcoef ht₁0 ht₁1 hd0 (by linarith) hRd
  have hmsa : ∀ j, ‖ms j - matchedA E‖ ≤ matchedDistance b E X / (1 - t₁) := fun j =>
    (norm_le_pi_norm (ms - fun _ => matchedA E) j).trans hDle
  have hdt : matchedDistance b E X / (1 - t₁) ≤ ρ / 2 := by
    rw [div_le_iff₀ h1t0]; linarith
  have hms : ∀ j, ‖ms j - matchedA E‖ ≤ ρ := fun j => by linarith [hmsa j]
  have hport := fun w (hw : ‖w - matchedA E‖ ≤ ρ) => cmp_sep_port ha1 hb0.le hbρ (hzq w) hw
  have husa : ∀ j, ‖(boundaryZ b E - (b : ℂ) * ms j)⁻¹ - matchedA E‖ ≤ 2 * b * ‖ms j - matchedA E‖ :=
    fun j => (hport _ (hms j)).2.2.2.2
  refine ⟨ms, fun j => (boundaryZ b E - (b : ℂ) * ms j)⁻¹, fun i => ⟨?_, rfl⟩,
    fun i => ⟨?_, ?_⟩, fun i => ?_, fun i => ?_, ?_⟩
  · rw [cmp_twoPortTop_inv]; exact (hfix i).symm
  · have := Complex.im_le_norm (ms i - matchedA E)
    rw [Complex.sub_im] at this
    linarith [hms i]
  · have := Complex.im_le_norm ((boundaryZ b E - (b : ℂ) * ms i)⁻¹ - matchedA E)
    rw [Complex.sub_im] at this
    have h1 := husa i
    have h2 := mul_le_mul (show 2 * b ≤ 1 by linarith) (hms i) (norm_nonneg _) zero_le_one
    linarith
  · have h1 := husa i
    have h2 := hmsa i
    have h3 : (1 + 2 * b) * ‖ms i - matchedA E‖ ≤
        (1 + 2 * b) * (matchedDistance b E X / (1 - t₁)) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    calc ‖ms i - matchedA E‖ + ‖(boundaryZ b E - (b : ℂ) * ms i)⁻¹ - matchedA E‖
        ≤ (1 + 2 * b) * ‖ms i - matchedA E‖ := by linarith
      _ ≤ (1 + 2 * b) * (matchedDistance b E X / (1 - t₁)) := h3
      _ = (1 + 2 * b) / (1 - t₁) * matchedDistance b E X := by ring
  · obtain ⟨-, heq, -, hU, -⟩ := hport _ (hms i)
    show ‖(boundaryZ b E - (b : ℂ) * ms i)⁻¹ - matchedA E‖ ≤ _
    rw [heq]
    have h1 : b * ‖ms i - matchedA E‖ ≤ b * (matchedDistance b E X / (1 - t₁)) :=
      mul_le_mul_of_nonneg_left (hmsa i) hb0.le
    calc b * ‖ms i - matchedA E‖ * ‖(boundaryZ b E - (b : ℂ) * ms i)⁻¹‖
        ≤ b * (matchedDistance b E X / (1 - t₁)) * (1 + 2 * b * ρ) :=
          mul_le_mul h1 hU (norm_nonneg _) (mul_nonneg hb0.le (div_nonneg hd0 h1t0.le))
      _ = b * (1 + 2 * b * ρ) / (1 - t₁) * matchedDistance b E X := by ring
  · intro m' u' r r' hnear heq i
    refine cmp_sep_stab (cmpTopH E X) hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁0 hzq hσ₀im rfl hβ1 hmarg
      hcoef ht₁0 ht₁1 ms hfix (fun j => (hmsa j).trans hdt) m' u' r r' hnear (fun k => ?_) i
    rw [← cmp_twoPortTop_inv]; exact heq k

/-!
## 6. Common port: existence, closeness, stability
-/

/-- Port bounds for the common port `u₀ = (z₀ - b (w₀ + w₁))⁻¹`,
`z₀ - b (w₀ + w₁) = a⁻¹ - b ((w₀ - a) + (w₁ - a))`. -/
theorem cmp_com_port {a z w₀ w₁ : ℂ} {b ρ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 ≤ b)
    (hbρ : b * ρ ≤ 1 / 4)
    (hzq : z - (b : ℂ) * (w₀ + w₁) = a⁻¹ - (b : ℂ) * ((w₀ - a) + (w₁ - a)))
    (hw₀ : ‖w₀ - a‖ ≤ ρ) (hw₁ : ‖w₁ - a‖ ≤ ρ) :
    z - (b : ℂ) * (w₀ + w₁) ≠ 0 ∧ ‖(z - (b : ℂ) * (w₀ + w₁))⁻¹‖ ≤ 2 ∧
      ‖(z - (b : ℂ) * (w₀ + w₁))⁻¹‖ ≤ 1 + 4 * b * ρ ∧
      ‖(z - (b : ℂ) * (w₀ + w₁))⁻¹ - a‖ ≤ 4 * b * ρ := by
  have hne : ‖(b : ℂ) * ((w₀ - a) + (w₁ - a))‖ ≤ 2 * b * ρ := by
    rw [cmp_norm_real_mul hb0]
    have := (norm_add_le (w₀ - a) (w₁ - a)).trans (add_le_add hw₀ hw₁)
    have := mul_le_mul_of_nonneg_left this hb0
    linarith
  have he : ‖(b : ℂ) * ((w₀ - a) + (w₁ - a))‖ ≤ 1 / 2 := by linarith
  obtain ⟨h1, -, h3, h4, h5⟩ := cmp_port' ha1 he
  rw [hzq]
  exact ⟨h1, h3, by linarith, by linarith⟩

/-- The common shift stays within `ρ` of the matched shift when `|m_j - a| ≤ ρ` and
`|u₀ - a| ≤ 2ρ`. -/
theorem cmp_com_shift_near {b ρ : ℝ} {a : ℂ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (m : Fin 2 → ℂ)
    (u₀ : ℂ) (j : Fin 2) (hm : ‖m j - a‖ ≤ ρ) (hu : ‖u₀ - a‖ ≤ 2 * ρ) :
    ‖cmpComShift b m u₀ j - (1 - (b : ℂ)) * a‖ ≤ ρ := by
  rw [cmpComShift_sub_matched]
  refine (norm_add_le _ _).trans ?_
  rw [cmp_norm_real_mul (by linarith), cmp_norm_real_mul hb0]
  have h1 := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 1 - 2 * b by linarith)
  have h2 := mul_le_mul_of_nonneg_left hu hb0
  linarith

/-- **One comparison step, common port.** `M` uses the port map of `m`; `M'` uses
`u₀' = (z₀ - b(m'_0 + m'_1))⁻¹ + e`. With `Σ_j |Q_ij| ≤ Λ` and the coefficient bound
`(c + 2b²(1+2ρ)²)(Λ + 4ρ y₁⁻³) ≤ t₁`: `|tr_i M - tr_i M'| ≤ t₁ ‖m - m'‖ + 2 y₁⁻² |e|`. -/
theorem cmp_com_step {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z : ℂ} {b ρ y₁ Λ t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w₀ w₁ : ℂ, z - (b : ℂ) * (w₀ + w₁) = a⁻¹ - (b : ℂ) * ((w₀ - a) + (w₁ - a)))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ Λ)
    (hcoef : ((1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2)) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁)
    (m m' : Fin 2 → ℂ) (u₀' e : ℂ) (hm : ∀ j, ‖m j - a‖ ≤ ρ) (hm' : ∀ j, ‖m' j - a‖ ≤ ρ)
    (hs' : ∀ j, ‖cmpComShift b m' u₀' j - (1 - (b : ℂ)) * a‖ ≤ ρ)
    (hu' : u₀' = (z - (b : ℂ) * (m' 0 + m' 1))⁻¹ + e) (i : Fin 2) :
    ‖blockTrace (cmpInv H (cmpComShift b m (z - (b : ℂ) * (m 0 + m 1))⁻¹)) i -
        blockTrace (cmpInv H (cmpComShift b m' u₀')) i‖ ≤
      t₁ * ‖m - m'‖ + 2 * y₁⁻¹ ^ 2 * ‖e‖ := by
  have hbρ : b * ρ ≤ 1 / 4 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have hport := cmp_com_port ha1 hb0.le hbρ (hzq (m 0) (m 1)) (hm 0) (hm 1)
  have hport' := cmp_com_port ha1 hb0.le hbρ (hzq (m' 0) (m' 1)) (hm' 0) (hm' 1)
  have h4b : 4 * b * ρ ≤ 2 * ρ := by nlinarith
  have hsm : ∀ j, ‖cmpComShift b m (z - (b : ℂ) * (m 0 + m 1))⁻¹ j - (1 - (b : ℂ)) * a‖ ≤ ρ :=
    fun j => cmp_com_shift_near hb0.le hb1.le m _ j (hm j) (hport.2.2.2.trans h4b)
  have hσ : ∀ j, y₁ ≤ -(cmpComShift b m (z - (b : ℂ) * (m 0 + m 1))⁻¹ j).im :=
    fun j => cmp_im_of_near hσ₀im hρy (hsm j)
  have hσ' : ∀ j, y₁ ≤ -(cmpComShift b m' u₀' j).im :=
    fun j => cmp_im_of_near hσ₀im hρy (hs' j)
  have hσ₀ : ∀ j : Fin 2, y₁ ≤ -((fun _ => (1 - (b : ℂ)) * a) j).im := fun _ => by
    simp only; linarith
  set U := (z - (b : ℂ) * (m 0 + m 1))⁻¹ with hU
  set U' := (z - (b : ℂ) * (m' 0 + m' 1))⁻¹ with hU'
  set γ : ℂ := (b : ℂ) ^ 2 * (U * U') with hγ
  have hdiff : ∀ j, cmpComShift b m U j - cmpComShift b m' u₀' j =
      ((1 - 2 * b : ℝ) : ℂ) * (m - m') j + γ * ((m - m') 0 + (m - m') 1) +
        (fun _ => -(b : ℂ) * e) j := fun j => by
    have hsub := cmp_port_sub (z := z) (b := (b : ℂ)) hport.1 hport'.1
    simp only [cmpComShift, hγ, Pi.sub_apply, hu']
    rw [show ((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * U -
        (((1 - 2 * b : ℝ) : ℂ) * m' j + (b : ℂ) * (U' + e)) =
        ((1 - 2 * b : ℝ) : ℂ) * (m j - m' j) + (b : ℂ) * (U - U') - (b : ℂ) * e by ring,
      hU, hU', hsub]
    ring
  have hcore := cmp_com_core H hH hy₁ hρ0.le (by linarith : (0 : ℝ) ≤ 1 - 2 * b) _ _
    (fun _ => (1 - (b : ℂ)) * a) hσ hσ' hσ₀ hsm hs' hΛ γ (m - m') (fun _ => -(b : ℂ) * e)
    (by simpa using hdiff) i
  have hγb : ‖γ‖ ≤ b ^ 2 * (1 + 2 * ρ) ^ 2 := by
    rw [hγ, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h1 : ‖U‖ ≤ 1 + 2 * ρ := hport.2.2.1.trans (by linarith)
    have h2 : ‖U'‖ ≤ 1 + 2 * ρ := hport'.2.2.1.trans (by linarith)
    have := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    rw [sq (1 + 2 * ρ)]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hΛ0 : 0 ≤ Λ := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hΛ 0)
  have hecore : ‖(fun _ => -(b : ℂ) * e : Fin 2 → ℂ)‖ ≤ ‖e‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg e)).mpr fun j => ?_
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have := mul_le_mul_of_nonneg_right (show b ≤ 1 by linarith) (norm_nonneg e)
    linarith
  refine hcore.trans ?_
  have hK : (1 - 2 * b + 2 * ‖γ‖) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁ := by
    refine le_trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) hcoef
  have hy2 : 0 ≤ 2 * y₁⁻¹ ^ 2 := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hecore hy2)

/-- **Existence of the comparison solution, common port** (Banach fixed point). -/
theorem cmp_com_exists {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z : ℂ} {b ρ y₁ Λ t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w₀ w₁ : ℂ, z - (b : ℂ) * (w₀ + w₁) = a⁻¹ - (b : ℂ) * ((w₀ - a) + (w₁ - a)))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ Λ)
    (hcoef : ((1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2)) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁)
    (ht₁0 : 0 ≤ t₁) (ht₁1 : t₁ < 1) {d : ℝ} (hd0 : 0 ≤ d) (hdρ : d ≤ (1 - t₁) * ρ)
    (hR : ∀ i, ‖blockTrace (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i - a‖ ≤ d) :
    ∃ ms : Fin 2 → ℂ, (∀ i, blockTrace (cmpInv H (cmpComShift b ms
        (z - (b : ℂ) * (ms 0 + ms 1))⁻¹)) i = ms i) ∧
      ‖ms - fun _ => a‖ ≤ d / (1 - t₁) := by
  have h1t0 : 0 < 1 - t₁ := by linarith
  have hbρ : b * ρ ≤ 1 / 4 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have h4b : 4 * b * ρ ≤ 2 * ρ := by nlinarith
  have hUa : ∀ w : Fin 2 → ℂ, (∀ j, ‖w j - a‖ ≤ ρ) →
      ‖(z - (b : ℂ) * (w 0 + w 1))⁻¹ - a‖ ≤ 2 * ρ := fun w hw =>
    (cmp_com_port ha1 hb0.le hbρ (hzq (w 0) (w 1)) (hw 0) (hw 1)).2.2.2.trans h4b
  obtain ⟨F, hF⟩ : ∃ F : (Fin 2 → ℂ) → (Fin 2 → ℂ), F = fun m i =>
      blockTrace (cmpInv H (cmpComShift b m (z - (b : ℂ) * (m 0 + m 1))⁻¹)) i := ⟨_, rfl⟩
  have hstep : ∀ m m' : Fin 2 → ℂ, (∀ j, ‖m j - a‖ ≤ ρ) → (∀ j, ‖m' j - a‖ ≤ ρ) →
      ∀ i, ‖F m i - F m' i‖ ≤ t₁ * ‖m - m'‖ := fun m m' hm hm' i => by
    have h := cmp_com_step H hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁ hzq hσ₀im hΛ hcoef
      m m' ((z - (b : ℂ) * (m' 0 + m' 1))⁻¹) 0 hm hm'
      (fun j => cmp_com_shift_near hb0.le hb1.le m' _ j (hm' j) (hUa m' hm'))
      (by simp) i
    rw [hF]
    simpa using h
  have hza : (z - (b : ℂ) * (a + a))⁻¹ = a := by
    rw [hzq, sub_self, add_zero, mul_zero, sub_zero, inv_inv]
  have hFa : ∀ i, ‖F (fun _ => a) i - a‖ ≤ d := fun i => by
    rw [hF]
    simp only
    rw [hza, cmpComShift_const]
    exact hR i
  have hconst : ∀ j : Fin 2, ‖(fun _ : Fin 2 => a) j - a‖ ≤ ρ := fun j => by simp [hρ0.le]
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin 2 → ℂ), S = Metric.closedBall (fun _ : Fin 2 => a) ρ :=
    ⟨_, rfl⟩
  have hmaps : Set.MapsTo F S S := fun m hm => by
    rw [hS, cmp_mem_ball_iff hρ0.le] at hm ⊢
    intro i
    have h1 := hstep m (fun _ => a) hm hconst i
    have h2 : ‖m - fun _ => a‖ ≤ ρ := (pi_norm_le_iff_of_nonneg hρ0.le).mpr hm
    have h3 := hFa i
    have h4 := norm_sub_le_norm_sub_add_norm_sub (F m i) (F (fun _ => a) i) a
    have h5 := mul_le_mul_of_nonneg_left h2 ht₁0
    have h6 : t₁ * ρ + (1 - t₁) * ρ = ρ := by ring
    linarith
  have hcontr : ContractingWith (Real.toNNReal t₁) (hmaps.restrict F S S) := by
    refine ⟨Real.toNNReal_lt_one.mpr ht₁1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, Set.MapsTo.val_restrict_apply,
      Set.MapsTo.val_restrict_apply, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ ht₁0]
    have hx : ∀ j, ‖(x : Fin 2 → ℂ) j - a‖ ≤ ρ :=
      (cmp_mem_ball_iff hρ0.le _).mp (hS ▸ x.2)
    have hy : ∀ j, ‖(y : Fin 2 → ℂ) j - a‖ ≤ ρ :=
      (cmp_mem_ball_iff hρ0.le _).mp (hS ▸ y.2)
    exact (pi_norm_le_iff_of_nonneg (mul_nonneg ht₁0 (norm_nonneg _))).mpr
      fun i => hstep _ _ hx hy i
  have hScomp : IsComplete S := by rw [hS]; exact Metric.isClosed_closedBall.isComplete
  have haS : (fun _ : Fin 2 => a) ∈ S := by rw [hS]; exact Metric.mem_closedBall_self hρ0.le
  obtain ⟨ms, hmsS, hfix, -⟩ := hcontr.exists_fixedPoint' hScomp hmaps haS (edist_ne_top _ _)
  have hms : ∀ j, ‖ms j - a‖ ≤ ρ := (cmp_mem_ball_iff hρ0.le ms).mp (hS ▸ hmsS)
  have hfix' : ∀ i, F ms i = ms i := fun i => congrFun hfix i
  refine ⟨ms, fun i => by have := hfix' i; rw [hF] at this; exact this, ?_⟩
  rw [le_div_iff₀ h1t0]
  have hD : ‖ms - fun _ => a‖ ≤ t₁ * ‖ms - fun _ => a‖ + d := by
    refine (pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg ht₁0 (norm_nonneg _)) hd0)).mpr
      fun i => ?_
    have h1 := hstep ms (fun _ => a) hms hconst i
    have h3 := hFa i
    have h4 := norm_sub_le_norm_sub_add_norm_sub (F ms i) (F (fun _ => a) i) a
    rw [hfix' i] at h1 h4
    show ‖ms i - a‖ ≤ _
    linarith
  linarith

/-- **Stability of the comparison solution, common port.** `C_B = 5(1 + 2y₁⁻²)/(1 - t₁) + 1`. -/
theorem cmp_com_stab {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hH : H.IsHermitian)
    {a z : ℂ} {b ρ y₁ Λ t₁ : ℝ} (ha1 : ‖a‖ = 1) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁ : 0 < y₁)
    (hzq : ∀ w₀ w₁ : ℂ, z - (b : ℂ) * (w₀ + w₁) = a⁻¹ - (b : ℂ) * ((w₀ - a) + (w₁ - a)))
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * a).im)
    (hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv H (fun _ => (1 - (b : ℂ)) * a))
      (cmpInv H (fun _ => (1 - (b : ℂ)) * a)) i j‖ ≤ Λ)
    (hcoef : ((1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2)) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁)
    (ht₁0 : 0 ≤ t₁) (ht₁1 : t₁ < 1)
    (ms : Fin 2 → ℂ) (hfix : ∀ i, blockTrace (cmpInv H (cmpComShift b ms
        (z - (b : ℂ) * (ms 0 + ms 1))⁻¹)) i = ms i) (hms : ∀ j, ‖ms j - a‖ ≤ ρ / 2)
    (m' r : Fin 2 → ℂ) (u₀' r' : ℂ)
    (hnear : (∀ i, ‖m' i - ms i‖ ≤ ρ / 4) ∧ ‖u₀' - (z - (b : ℂ) * (ms 0 + ms 1))⁻¹‖ ≤ ρ / 4)
    (heq : (∀ i, m' i = blockTrace (cmpInv H (cmpComShift b m' u₀')) i + r i) ∧
      u₀' = (z - (b : ℂ) * (m' 0 + m' 1))⁻¹ + r') :
    (∀ i, ‖m' i - ms i‖ ≤ (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖)) ∧
      ‖u₀' - (z - (b : ℂ) * (ms 0 + ms 1))⁻¹‖ ≤
        (5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) := by
  have h1t0 : 0 < 1 - t₁ := by linarith
  have hbρ : b * ρ ≤ 1 / 4 := by
    have := mul_le_mul hb1.le hρ4 hρ0.le (by norm_num); linarith
  have hms' : ∀ j, ‖ms j - a‖ ≤ ρ := fun j => (hms j).trans (by linarith)
  have hm' : ∀ j, ‖m' j - a‖ ≤ ρ := fun j => by
    have := norm_sub_le_norm_sub_add_norm_sub (m' j) (ms j) a
    linarith [hnear.1 j, hms j]
  have hportS := cmp_com_port ha1 hb0.le hbρ (hzq (ms 0) (ms 1)) (hms' 0) (hms' 1)
  have hport' := cmp_com_port ha1 hb0.le hbρ (hzq (m' 0) (m' 1)) (hm' 0) (hm' 1)
  have hu'a : ‖u₀' - a‖ ≤ 2 * ρ := by
    have := norm_sub_le_norm_sub_add_norm_sub u₀' ((z - (b : ℂ) * (ms 0 + ms 1))⁻¹) a
    have hbρ2 : b * (ρ / 2) ≤ 1 / 4 := by nlinarith
    have hp2 := (cmp_com_port ha1 hb0.le hbρ2 (hzq (ms 0) (ms 1)) (hms 0) (hms 1)).2.2.2
    have h4b : 4 * b * (ρ / 2) ≤ ρ := by nlinarith
    linarith [hnear.2]
  have h := cmp_com_step H hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁ hzq hσ₀im hΛ hcoef
    ms m' u₀' r' hms' hm' (fun j => cmp_com_shift_near hb0.le hb1.le m' u₀' j (hm' j) hu'a)
    heq.2
  have hy2 : 0 ≤ y₁⁻¹ ^ 2 := sq_nonneg _
  have hDb : ‖ms - m'‖ * (1 - t₁) ≤ ‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ := by
    have hD : ‖ms - m'‖ ≤ t₁ * ‖ms - m'‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ + ‖r‖ := by
      refine (pi_norm_le_iff_of_nonneg (add_nonneg (add_nonneg (mul_nonneg ht₁0
        (norm_nonneg _)) (mul_nonneg (by linarith) (norm_nonneg _))) (norm_nonneg _))).mpr
        fun k => ?_
      have h1 := h k
      rw [hfix k] at h1
      have h3 : ms k - m' k = (ms k - blockTrace (cmpInv H (cmpComShift b m' u₀')) k) - r k := by
        rw [heq.1 k]; ring
      show ‖ms k - m' k‖ ≤ _
      rw [h3]
      have := norm_sub_le (ms k - blockTrace (cmpInv H (cmpComShift b m' u₀')) k) (r k)
      have := norm_le_pi_norm r k
      linarith
    linarith
  have hr0 := norm_nonneg r
  have hr0' := norm_nonneg r'
  have hfin : ‖r‖ + 2 * y₁⁻¹ ^ 2 * ‖r'‖ ≤ (1 + 2 * y₁⁻¹ ^ 2) * (‖r‖ + ‖r'‖) := by
    have := mul_nonneg hy2 hr0
    nlinarith
  have hD' : ‖ms - m'‖ ≤ (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1t0]; linarith
  have hmi : ∀ i, ‖m' i - ms i‖ ≤ ‖ms - m'‖ := fun i => by
    rw [norm_sub_rev]; exact norm_le_pi_norm (ms - m') i
  refine ⟨fun i => (hmi i).trans hD', ?_⟩
  have hsub := cmp_port_sub (z := z) (b := (b : ℂ)) hport'.1 hportS.1
  have hu : u₀' - (z - (b : ℂ) * (ms 0 + ms 1))⁻¹ =
      ((z - (b : ℂ) * (m' 0 + m' 1))⁻¹ - (z - (b : ℂ) * (ms 0 + ms 1))⁻¹) + r' := by
    rw [heq.2]; ring
  rw [hu, hsub]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hsum : ‖m' 0 + m' 1 - (ms 0 + ms 1)‖ ≤ 2 * ‖ms - m'‖ := by
    rw [show m' 0 + m' 1 - (ms 0 + ms 1) = (m' 0 - ms 0) + (m' 1 - ms 1) by ring]
    have := (norm_add_le _ _).trans (add_le_add (hmi 0) (hmi 1))
    linarith
  have h1 := mul_le_mul hport'.2.1 hportS.2.1 (norm_nonneg _) zero_le_two
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hsum hb0.le) h1
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hb0.le (by positivity))
  have h3 : b * (2 * ‖ms - m'‖) * (2 * 2) ≤ 4 * ‖ms - m'‖ := by
    have := mul_le_mul_of_nonneg_right (show 8 * b ≤ 4 by linarith) (norm_nonneg (ms - m'))
    linarith
  have h5 : 4 * ‖ms - m'‖ ≤ 4 * ((1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖)) := by linarith
  have h6 : 4 * ((1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖)) + ‖r'‖ ≤
      (5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) := by
    have hk : 0 ≤ (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖) :=
      mul_nonneg (div_nonneg (by linarith) h1t0.le) (by linarith)
    have : (5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) =
        5 * ((1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) * (‖r‖ + ‖r'‖)) + (‖r‖ + ‖r'‖) := by ring
    linarith
  linarith

/-- Instance-level common-port statement (fixed `W, X, E`), used by `cmp_commonPort_stable`. -/
theorem cmp_com_instance {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hX : X.IsHermitian) {b E ρ y₁ t₁ α₀ Λ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hEabs : |E| < 2) (ha1 : ‖matchedA E‖ = 1) (haim : (matchedA E).im ≤ -α₀)
    (hy₁α : y₁ < α₀) (hρ0 : 0 < ρ) (hρy : ρ ≤ y₁) (hρ4 : ρ ≤ 1 / 4) (hy₁0 : 0 < y₁)
    (ht₁0 : 0 ≤ t₁) (ht₁1 : t₁ < 1)
    (hdρ : matchedDistance b E X ≤ (1 - t₁) * ρ / 2)
    (hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * matchedA E).im)
    (hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E))
      (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i j‖ ≤ Λ)
    (hcoef : ((1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2)) * (Λ + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁) :
    ∃ (m : Fin 2 → ℂ) (u₀ : ℂ), IsCommonPortSolution b E X m u₀ ∧
        (∀ i, (m i).im < 0) ∧ u₀.im < 0 ∧
        (∀ i, ‖m i - matchedA E‖ ≤ (1 + 4 * b) / (1 - t₁) * matchedDistance b E X) ∧
        ‖u₀ - matchedA E‖ ≤ (1 + 4 * b) / (1 - t₁) * matchedDistance b E X ∧
        ∀ (m' r : Fin 2 → ℂ) (u₀' r' : ℂ), ((∀ i, ‖m' i - m i‖ ≤ ρ / 4) ∧ ‖u₀' - u₀‖ ≤ ρ / 4) →
          ((∀ i, m' i = blockTrace (commonPortTop b E X m' u₀')⁻¹ i + r i) ∧
            u₀' = (commonZ b E - (b : ℂ) * (m' 0 + m' 1))⁻¹ + r') →
          (∀ i, ‖m' i - m i‖ ≤ (5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖)) ∧
            ‖u₀' - u₀‖ ≤ (5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1) * (‖r‖ + ‖r'‖) := by
  have h1t0 : 0 < 1 - t₁ := by linarith
  have hzq : ∀ w₀ w₁ : ℂ, commonZ b E - (b : ℂ) * (w₀ + w₁) =
      (matchedA E)⁻¹ - (b : ℂ) * ((w₀ - matchedA E) + (w₁ - matchedA E)) :=
    fun w₀ w₁ => by unfold commonZ; ring
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hH : (cmpTopH E X).IsHermitian := cmpTopH_isHermitian E hX
  have hRd : ∀ i, ‖blockTrace (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i -
      matchedA E‖ ≤ matchedDistance b E X := fun i => by
    rw [← cmp_resolvent_eq hEabs.le X]; exact cmp_le_matchedDistance b E X i
  obtain ⟨ms, hfix, hDle⟩ := cmp_com_exists (cmpTopH E X) hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁0 hzq
    hσ₀im hΛ hcoef ht₁0 ht₁1 hd0 (by nlinarith) hRd
  have hmsa : ∀ j, ‖ms j - matchedA E‖ ≤ matchedDistance b E X / (1 - t₁) := fun j =>
    (norm_le_pi_norm (ms - fun _ => matchedA E) j).trans hDle
  have hdt : matchedDistance b E X / (1 - t₁) ≤ ρ / 2 := by
    rw [div_le_iff₀ h1t0]; linarith
  have hbd : b * (matchedDistance b E X / (1 - t₁)) ≤ 1 / 4 := by
    have := mul_le_mul hb1.le hdt (div_nonneg hd0 h1t0.le) (by norm_num); linarith
  have hu₀ := cmp_com_port ha1 hb0.le hbd (hzq (ms 0) (ms 1)) (hmsa 0) (hmsa 1)
  have hq0 : 0 ≤ matchedDistance b E X / (1 - t₁) := div_nonneg hd0 h1t0.le
  refine ⟨ms, (commonZ b E - (b : ℂ) * (ms 0 + ms 1))⁻¹, ⟨fun i => ?_, rfl⟩, fun i => ?_, ?_,
    fun i => ?_, ?_, ?_⟩
  · rw [cmp_commonPortTop_inv]; exact (hfix i).symm
  · have := Complex.im_le_norm (ms i - matchedA E)
    rw [Complex.sub_im] at this
    linarith [hmsa i]
  · have := Complex.im_le_norm ((commonZ b E - (b : ℂ) * (ms 0 + ms 1))⁻¹ - matchedA E)
    rw [Complex.sub_im] at this
    have h1 := hu₀.2.2.2
    have h2 := mul_le_mul_of_nonneg_left hdt (show 0 ≤ 4 * b by linarith)
    have h3 : 4 * b * (ρ / 2) ≤ ρ := by nlinarith
    linarith
  · have := mul_nonneg hb0.le hq0
    calc ‖ms i - matchedA E‖ ≤ (1 + 4 * b) * (matchedDistance b E X / (1 - t₁)) := by
          linarith [hmsa i]
      _ = (1 + 4 * b) / (1 - t₁) * matchedDistance b E X := by ring
  · have := mul_nonneg hb0.le hq0
    calc ‖(commonZ b E - (b : ℂ) * (ms 0 + ms 1))⁻¹ - matchedA E‖
        ≤ 4 * b * (matchedDistance b E X / (1 - t₁)) := hu₀.2.2.2
      _ ≤ (1 + 4 * b) * (matchedDistance b E X / (1 - t₁)) := by linarith
      _ = (1 + 4 * b) / (1 - t₁) * matchedDistance b E X := by ring
  · intro m' r u₀' r' hnear heq
    obtain ⟨h1, h2⟩ := cmp_com_stab (cmpTopH E X) hH ha1 hb0 hb1 hρ0 hρy hρ4 hy₁0 hzq hσ₀im hΛ
      hcoef ht₁0 ht₁1 ms hfix (fun j => (hmsa j).trans hdt) m' r u₀' r' hnear
      ⟨fun k => by rw [← cmp_commonPortTop_inv]; exact heq.1 k, heq.2⟩
    refine ⟨fun i => (h1 i).trans ?_, h2⟩
    have hk : 0 ≤ ‖r‖ + ‖r'‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
    refine mul_le_mul_of_nonneg_right ?_ hk
    have : (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) ≤ 5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg y₁⁻¹]) h1t0.le
    linarith

/-- **Common port, (A)+(B).** `b ∈ (0, 1/2)`, `κ > 0` first; then `d_* > 0`, `C`, `ρ_B > 0`,
`C_B`; uniformly in `W ≥ 1`, Hermitian two-port `X`, `E ∈ bulkInterval κ` with `d(X) ≤ d_*`:
there is a solution `(m, u₀)` of the common-port form of the two-port Dyson equation
(`z₀ = commonZ b E`) with `Im m_i, Im u₀ < 0`, `|m_i - a| ≤ C d(X)`, `|u₀ - a| ≤ C d(X)`, and every
`(m', u₀')` within `ρ_B` of `(m, u₀)` solving the equations up to residuals `(r, r')` satisfies
`|m'_i - m_i| ≤ C_B (‖r‖ + |r'|)` and `|u₀' - u₀| ≤ C_B (‖r‖ + |r'|)`. The linearized top
coefficient is `(c + 2b²)/(1-b) + O(ρ + d) < 1`. -/
theorem cmp_commonPort_stable : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ dstar C ρB CB : ℝ, 0 < dstar ∧ 0 ≤ C ∧ 0 < ρB ∧ 0 ≤ CB ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
      ∃ (m : Fin 2 → ℂ) (u₀ : ℂ), IsCommonPortSolution b E X m u₀ ∧
        (∀ i, (m i).im < 0) ∧ u₀.im < 0 ∧
        (∀ i, ‖m i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
        ‖u₀ - matchedA E‖ ≤ C * matchedDistance b E X ∧
        ∀ (m' r : Fin 2 → ℂ) (u₀' r' : ℂ), ((∀ i, ‖m' i - m i‖ ≤ ρB) ∧ ‖u₀' - u₀‖ ≤ ρB) →
          ((∀ i, m' i = blockTrace (commonPortTop b E X m' u₀')⁻¹ i + r i) ∧
            u₀' = (commonZ b E - (b : ℂ) * (m' 0 + m' 1))⁻¹ + r') →
          (∀ i, ‖m' i - m i‖ ≤ CB * (‖r‖ + ‖r'‖)) ∧ ‖u₀' - u₀‖ ≤ CB * (‖r‖ + ‖r'‖) := by
  intro b hb0 hb1 κ hκ
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨Cr, hCr⟩ := strictContraction_rowSum b hb0 hb1 κ hκ
  obtain ⟨C', hC'⟩ : ∃ x : ℝ, x = max Cr 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ le_max_right _ _
  have hCrC' : Cr ≤ C' := hC' ▸ le_max_left _ _
  have h1b : 0 < 1 - b := by linarith
  obtain ⟨L₀, hL₀⟩ : ∃ x : ℝ, x = (1 - b)⁻¹ := ⟨_, rfl⟩
  have hL₀0 : 0 < L₀ := hL₀ ▸ inv_pos.mpr h1b
  have hL₀2 : L₀ ≤ 2 := by
    rw [hL₀, inv_le_comm₀ h1b two_pos]; linarith
  obtain ⟨A₀, hA₀⟩ : ∃ x : ℝ, x = 1 - 2 * b + 2 * b ^ 2 := ⟨_, rfl⟩
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; nlinarith
  have hA₀1 : A₀ ≤ 1 := by rw [hA₀]; nlinarith
  obtain ⟨tc, htc⟩ : ∃ x : ℝ, x = A₀ * L₀ := ⟨_, rfl⟩
  have htc1 : tc < 1 := by
    rw [htc, hL₀, ← div_eq_mul_inv, div_lt_one h1b, hA₀]; nlinarith
  have htc0 : 0 ≤ tc := htc ▸ mul_nonneg hA₀0 hL₀0.le
  obtain ⟨g, hg⟩ : ∃ x : ℝ, x = 1 - tc := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; linarith
  have hg1 : g ≤ 1 := by rw [hg]; linarith
  obtain ⟨t₁, ht₁⟩ : ∃ x : ℝ, x = (1 + tc) / 2 := ⟨_, rfl⟩
  have h1t : 1 - t₁ = g / 2 := by rw [ht₁, hg]; ring
  have h1t0 : 0 < 1 - t₁ := by rw [h1t]; linarith
  have ht₁0 : 0 ≤ t₁ := by rw [ht₁]; linarith
  have ht₁1 : t₁ < 1 := by linarith
  obtain ⟨y₁, hy₁⟩ : ∃ x : ℝ, x = (1 - b) * α₀ / 2 := ⟨_, rfl⟩
  have hy₁0 : 0 < y₁ := hy₁ ▸ div_pos (mul_pos h1b hα₀) two_pos
  have hy₁α : y₁ < α₀ := by rw [hy₁]; nlinarith
  have hyi0 : 0 < y₁⁻¹ := inv_pos.mpr hy₁0
  have hy3 : 0 < y₁⁻¹ ^ 3 := pow_pos hyi0 3
  obtain ⟨ρ, hρ⟩ : ∃ x : ℝ, x = min (min y₁ (1 / 4)) (g / (8 * (4 * y₁⁻¹ ^ 3 + 9))) :=
    ⟨_, rfl⟩
  have hK0 : 0 < 8 * (4 * y₁⁻¹ ^ 3 + 9) := by linarith
  have hρ0 : 0 < ρ := hρ ▸ lt_min (lt_min hy₁0 (by norm_num)) (div_pos hg0 hK0)
  have hρy : ρ ≤ y₁ := hρ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / 4 := hρ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρg : ρ * (8 * (4 * y₁⁻¹ ^ 3 + 9)) ≤ g := by
    have h := hρ ▸ (min_le_right (min y₁ (1 / 4)) (g / (8 * (4 * y₁⁻¹ ^ 3 + 9))))
    rw [le_div_iff₀ hK0] at h; exact h
  have hρy3 : 4 * ρ * y₁⁻¹ ^ 3 ≤ g / 8 := by nlinarith
  have hρ9 : 9 * ρ ≤ g / 8 := by nlinarith
  obtain ⟨dstar, hdstar⟩ : ∃ x : ℝ, x = min ((1 - t₁) * ρ / 2) (g / (8 * (C' + 1))) :=
    ⟨_, rfl⟩
  have hdstar0 : 0 < dstar := hdstar ▸ lt_min (div_pos (mul_pos h1t0 hρ0) two_pos)
    (div_pos hg0 (by linarith))
  have hdstar1 : dstar ≤ (1 - t₁) * ρ / 2 := hdstar ▸ min_le_left _ _
  have hdstar2 : C' * dstar ≤ g / 8 := by
    have h := hdstar ▸ (min_le_right ((1 - t₁) * ρ / 2) (g / (8 * (C' + 1))))
    rw [le_div_iff₀ (by linarith)] at h
    nlinarith
  have hy2 : 0 ≤ y₁⁻¹ ^ 2 := sq_nonneg _
  have hcoefd : ∀ d : ℝ, 0 ≤ d → d ≤ dstar → ((1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2)) *
      ((L₀ + C' * d) + 4 * ρ * y₁⁻¹ ^ 3) ≤ t₁ := fun d hd0 hd => by
    have hCd : C' * d ≤ g / 8 := (mul_le_mul_of_nonneg_left hd hC'0).trans hdstar2
    have hCd0 : 0 ≤ C' * d := mul_nonneg hC'0 hd0
    have hf1 : (1 - 2 * b) + 2 * (b ^ 2 * (1 + 2 * ρ) ^ 2) ≤ A₀ + 3 * ρ := by
      rw [hA₀]
      have hb2 : b ^ 2 ≤ 1 / 4 := by
        have := pow_le_pow_left₀ hb0.le hb1.le 2; norm_num at this; linarith
      have h4' := mul_le_mul_of_nonneg_left hρ4 (show (0 : ℝ) ≤ 4 * ρ by linarith)
      have h4 : 4 * ρ + 4 * ρ ^ 2 ≤ 5 * ρ := by rw [sq]; linarith
      have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg b)
      have h6 := mul_le_mul_of_nonneg_right hb2 (show 0 ≤ 5 * ρ by linarith)
      have : (1 + 2 * ρ) ^ 2 = 1 + (4 * ρ + 4 * ρ ^ 2) := by ring
      rw [this]; linarith
    have h4ρ : 0 < 4 * ρ * y₁⁻¹ ^ 3 := mul_pos (mul_pos (by norm_num) hρ0) hy3
    have hf2 : 0 ≤ (L₀ + C' * d) + 4 * ρ * y₁⁻¹ ^ 3 := by linarith
    have h1 : A₀ * (C' * d + 4 * ρ * y₁⁻¹ ^ 3) ≤ 1 * (g / 8 + g / 8) :=
      mul_le_mul hA₀1 (by linarith) (by linarith) zero_le_one
    have h2 : 3 * ρ * (L₀ + C' * d + 4 * ρ * y₁⁻¹ ^ 3) ≤ 3 * ρ * (2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hexp : (A₀ + 3 * ρ) * ((L₀ + C' * d) + 4 * ρ * y₁⁻¹ ^ 3) = A₀ * L₀ +
        A₀ * (C' * d + 4 * ρ * y₁⁻¹ ^ 3) + 3 * ρ * (L₀ + C' * d + 4 * ρ * y₁⁻¹ ^ 3) := by ring
    have h3 := mul_le_mul_of_nonneg_right hf1 hf2
    have h7 : tc + g / 2 = t₁ := by rw [ht₁, hg]; ring
    rw [← htc] at hexp
    linarith
  refine ⟨dstar, (1 + 4 * b) / (1 - t₁), ρ / 4, 5 * (1 + 2 * y₁⁻¹ ^ 2) / (1 - t₁) + 1,
    hdstar0, div_nonneg (by linarith) h1t0.le, by linarith,
    add_nonneg (div_nonneg (by linarith) h1t0.le) zero_le_one, ?_⟩
  intro W hW X hX E hE hd
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hσ₀im : 2 * y₁ ≤ -((1 - (b : ℂ)) * matchedA E).im := by
    have : ((1 - (b : ℂ)) * matchedA E).im = (1 - b) * (matchedA E).im := by
      simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im]
      ring
    rw [this, hy₁]
    have := mul_le_mul_of_nonneg_left haim h1b.le
    linarith
  have hΛ : ∀ i, ∑ j, ‖cmpPair (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E))
      (cmpInv (cmpTopH E X) (fun _ => (1 - (b : ℂ)) * matchedA E)) i j‖ ≤
        L₀ + C' * matchedDistance b E X := fun i => by
    have := hCr W hW X hX E hE i
    rw [cmp_resolvent_eq hEabs.le X] at this
    simp only [← cmpPair_self] at this
    have := mul_le_mul_of_nonneg_right hCrC' hd0
    rw [hL₀]; linarith
  exact cmp_com_instance X hX hb0 hb1 hEabs ha1 haim hy₁α hρ0 hρy hρ4 hy₁0 ht₁0 ht₁1
    (hd.trans hdstar1) hσ₀im hΛ (hcoefd _ hd0 hd)

/-!
## 7. Branch identification: scalar inequalities
-/

/-- Two-term Cauchy–Schwarz in product form: `r_k² ≤ p_k q_k` gives
`(r₁ + r₂)² ≤ (p₁ + p₂)(q₁ + q₂)` (all nonnegative). -/
theorem cmp_cs2 {p₁ p₂ q₁ q₂ r₁ r₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hq₁ : 0 ≤ q₁)
    (hq₂ : 0 ≤ q₂) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (h₁ : r₁ ^ 2 ≤ p₁ * q₁)
    (h₂ : r₂ ^ 2 ≤ p₂ * q₂) : (r₁ + r₂) ^ 2 ≤ (p₁ + p₂) * (q₁ + q₂) := by
  have hX : 0 ≤ p₁ * q₂ := mul_nonneg hp₁ hq₂
  have hY : 0 ≤ p₂ * q₁ := mul_nonneg hp₂ hq₁
  have h3 : (r₁ * r₂) ^ 2 ≤ (p₁ * q₂) * (p₂ * q₁) := by
    rw [mul_pow]
    calc r₁ ^ 2 * r₂ ^ 2 ≤ (p₁ * q₁) * (p₂ * q₂) :=
          mul_le_mul h₁ h₂ (sq_nonneg _) (mul_nonneg hp₁ hq₁)
      _ = (p₁ * q₂) * (p₂ * q₁) := by ring
  have h4 : (2 * (r₁ * r₂)) ^ 2 ≤ (p₁ * q₂ + p₂ * q₁) ^ 2 := by
    nlinarith [sq_nonneg (p₁ * q₂ - p₂ * q₁)]
  have h5 : 2 * (r₁ * r₂) ≤ p₁ * q₂ + p₂ * q₁ :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
  nlinarith

/-- The generic margin step: `L + β ≤ G`, `β ≥ ε₀ G`, `L' ≤ (1+x) L`, `κ ≥ (1-θ) G`,
`x + θ ≤ ε₀/2` give `L' ≤ (1 - ε₀/2) κ`. -/
theorem cmp_weight_margin {L L' β G κ ε₀ x θ : ℝ} (hG : 0 ≤ G) (hLG : L + β ≤ G)
    (hβ : ε₀ * G ≤ β) (hL' : L' ≤ (1 + x) * L) (hκ : (1 - θ) * G ≤ κ) (hx : 0 ≤ x)
    (hθ : 0 ≤ θ) (hsum : x + θ ≤ ε₀ / 2) (hε : ε₀ ≤ 1) : L' ≤ (1 - ε₀ / 2) * κ := by
  have h1 : L ≤ (1 - ε₀) * G := by linarith
  have h2 : L' ≤ (1 + x) * ((1 - ε₀) * G) :=
    hL'.trans (mul_le_mul_of_nonneg_left h1 (by linarith))
  have h3 : (1 + x) * (1 - ε₀) ≤ (1 - ε₀ / 2) * (1 - θ) := by nlinarith
  have h4 : (1 + x) * ((1 - ε₀) * G) ≤ (1 - ε₀ / 2) * ((1 - θ) * G) := by
    have := mul_le_mul_of_nonneg_right h3 hG; linarith
  have h5 : (1 - ε₀ / 2) * ((1 - θ) * G) ≤ (1 - ε₀ / 2) * κ :=
    mul_le_mul_of_nonneg_left hκ (by linarith)
  linarith

/-- `√V ≤ (1 + x) √v` for `V ≤ v + η`, `v ≥ y₀ > 0`, `x = η / y₀`, `η ≥ 0`. -/
theorem cmp_sqrt_up {V v η y₀ : ℝ} (hy₀ : 0 < y₀) (hv : y₀ ≤ v) (hη : 0 ≤ η)
    (hV : V ≤ v + η) : Real.sqrt V ≤ (1 + η / y₀) * Real.sqrt v := by
  have hv0 : 0 ≤ v := hy₀.le.trans hv
  have hx : 0 ≤ η / y₀ := div_nonneg hη hy₀.le
  have h1 : η ≤ v * (η / y₀) := by
    rw [mul_div_assoc', le_div_iff₀ hy₀]; nlinarith
  have h2 : V ≤ ((1 + η / y₀) * Real.sqrt v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv0]; nlinarith
  calc Real.sqrt V ≤ Real.sqrt (((1 + η / y₀) * Real.sqrt v) ^ 2) := Real.sqrt_le_sqrt h2
    _ = (1 + η / y₀) * Real.sqrt v := Real.sqrt_sq (by positivity)

/-- `√Y ≥ (1 - θ) √y` for `Y ≥ y - e`, `y ≥ y₁ > 0`, `θ = e / y₁ ≤ 1`, `e ≥ 0`. -/
theorem cmp_sqrt_down {Y y e y₁ : ℝ} (hy₁ : 0 < y₁) (hy : y₁ ≤ y) (he : 0 ≤ e)
    (hθ : e / y₁ ≤ 1) (hY : y - e ≤ Y) : (1 - e / y₁) * Real.sqrt y ≤ Real.sqrt Y := by
  have hy0 : 0 ≤ y := hy₁.le.trans hy
  have hθ0 : 0 ≤ e / y₁ := div_nonneg he hy₁.le
  have h1 : y * (e / y₁) ≥ e := by
    rw [mul_div_assoc', ge_iff_le, le_div_iff₀ hy₁]; nlinarith
  have h2 : ((1 - e / y₁) * Real.sqrt y) ^ 2 ≤ Y := by
    rw [mul_pow, Real.sq_sqrt hy0]
    have : (1 - e / y₁) ^ 2 ≤ 1 - e / y₁ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hy0]
  calc (1 - e / y₁) * Real.sqrt y = Real.sqrt (((1 - e / y₁) * Real.sqrt y) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).symm
    _ ≤ Real.sqrt Y := Real.sqrt_le_sqrt h2

/-- Imaginary part of a port value: `-Im (q⁻¹) = |q⁻¹|² Im q`. -/
theorem cmp_neg_im_inv (q : ℂ) : -(q⁻¹).im = ‖q⁻¹‖ ^ 2 * q.im := by
  rw [Complex.inv_im, norm_inv, inv_pow, Complex.sq_norm]
  ring

/-- `|q⁻¹| ≤ 1/ζ` when `Im q ≥ ζ > 0`, and `|q⁻¹| ≥ 1/A` when `|q| ≤ A`. -/
theorem cmp_inv_bounds {q : ℂ} {ζ A : ℝ} (hζ : 0 < ζ) (hq : ζ ≤ q.im) (hA : ‖q‖ ≤ A) :
    ‖q⁻¹‖ ≤ ζ⁻¹ ∧ A⁻¹ ≤ ‖q⁻¹‖ := by
  have hq0 : 0 < ‖q‖ := lt_of_lt_of_le hζ (hq.trans (Complex.im_le_norm q))
  rw [norm_inv]
  exact ⟨inv_anti₀ hζ (hq.trans (Complex.im_le_norm q)), inv_anti₀ hq0 hA⟩

/-- Imaginary part of a real-coefficient combination. -/
theorem cmp_im_comb (c b : ℝ) (m u : ℂ) :
    -(((c : ℂ) * m + (b : ℂ) * u).im) = c * (-m.im) + b * (-u.im) := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- Real-variable core of the separate-port weighted margin. -/
theorem cmp_sep_margin_real {b ζ₀ y₀ y₁ η A Y ζ v vb Vb U Ut y yt yb : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ ζ) (hy₀ : 0 < y₀)
    (hy₁0 : 0 < y₁) (hη0 : 0 ≤ η) (hA0 : 0 < A) (hY0 : 0 < Y) (hθ1 : b * η / y₁ ≤ 1)
    (hsmall : η / y₀ + b * η / y₁ ≤ b * ζ₀ / A ^ 2 / Y / 2)
    (hv : y₀ ≤ v) (hvb : y₀ ≤ vb) (hVb : Vb ≤ vb + η)
    (hU0 : 0 ≤ U) (hU2 : A⁻¹ ≤ U) (hUt2 : A⁻¹ ≤ Ut)
    (hy : y = (1 - 2 * b) * v + b * U ^ 2 * ζ + b ^ 2 * U ^ 2 * v)
    (hyt : yt = (1 - 2 * b) * vb + b * Ut ^ 2 * ζ + b ^ 2 * Ut ^ 2 * vb)
    (hyt1 : y₁ ≤ yt) (hyY : y ≤ Y) (hytY : yt ≤ Y) (hyb : yt - b * η ≤ yb) :
    ((1 - 2 * b) + b ^ 2 * (U * Ut)) * (Real.sqrt v * Real.sqrt Vb) ≤
      (1 - b * ζ₀ / A ^ 2 / Y / 2) * (Real.sqrt y * Real.sqrt yb) := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hv0 : 0 ≤ v := hy₀.le.trans hv
  have hvb0 : 0 ≤ vb := hy₀.le.trans hvb
  have hζ0 : 0 < ζ := lt_of_lt_of_le hζ₀ hz
  have hUt0 : 0 ≤ Ut := (inv_nonneg.mpr hA0.le).trans hUt2
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyt0 : 0 ≤ yt := hy₁0.le.trans hyt1
  set ωt := Real.sqrt v * Real.sqrt vb with hωt
  have hωt0 : 0 ≤ ωt := by positivity
  have hωt2 : ωt ^ 2 = v * vb := by
    rw [hωt, mul_pow, Real.sq_sqrt hv0, Real.sq_sqrt hvb0]
  set P := (1 - 2 * b) + b ^ 2 * (U * Ut) with hP
  set β := b * U * Ut * ζ with hβ
  have hCS : (P * ωt + β) ^ 2 ≤ y * yt := by
    have e1 : ((1 - 2 * b) * ωt) ^ 2 ≤ ((1 - 2 * b) * v) * ((1 - 2 * b) * vb) :=
      le_of_eq (by rw [mul_pow, hωt2]; ring)
    have e2 : (b * U * Ut * ζ) ^ 2 ≤ (b * U ^ 2 * ζ) * (b * Ut ^ 2 * ζ) :=
      le_of_eq (by ring)
    have e3 : (b ^ 2 * (U * Ut) * ωt) ^ 2 ≤ (b ^ 2 * U ^ 2 * v) * (b ^ 2 * Ut ^ 2 * vb) :=
      le_of_eq (by rw [mul_pow, hωt2]; ring)
    have h12 := cmp_cs2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) e1 e2
    have h123 := cmp_cs2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) h12 e3
    rw [hy, hyt]
    calc (P * ωt + β) ^ 2 = ((1 - 2 * b) * ωt + b * U * Ut * ζ + b ^ 2 * (U * Ut) * ωt) ^ 2 := by
          rw [hP, hβ]; ring
      _ ≤ _ := h123
      _ = _ := by ring
  set G := Real.sqrt y * Real.sqrt yt with hG
  have hG0 : 0 ≤ G := by positivity
  have hG2 : G ^ 2 = y * yt := by rw [hG, mul_pow, Real.sq_sqrt hy0, Real.sq_sqrt hyt0]
  have hLG : P * ωt + β ≤ G := by
    have hPβ : 0 ≤ P * ωt + β := by positivity
    exact (pow_le_pow_iff_left₀ hPβ hG0 two_ne_zero).mp (hG2 ▸ hCS)
  have hGY : G ≤ Y := by
    have : G ^ 2 ≤ Y ^ 2 := by rw [hG2, sq]; exact mul_le_mul hyY hytY hyt0 hY0.le
    exact (pow_le_pow_iff_left₀ hG0 hY0.le two_ne_zero).mp this
  set β₀ := b * ζ₀ / A ^ 2 with hβ₀
  have hββ₀ : β₀ ≤ β := by
    rw [hβ₀, hβ]
    have h1 : A⁻¹ * A⁻¹ ≤ U * Ut := mul_le_mul hU2 hUt2 (by positivity) hU0
    have h2 : b * ζ₀ / A ^ 2 = b * (A⁻¹ * A⁻¹) * ζ₀ := by field_simp
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 hb0.le
    have h4 := mul_le_mul h3 hz (le_of_lt hζ₀) (by positivity)
    linarith
  have hβ0 : 0 ≤ β₀ := by positivity
  have hεG : β₀ / Y * G ≤ β := by
    have : β₀ / Y * G ≤ β₀ / Y * Y := mul_le_mul_of_nonneg_left hGY (by positivity)
    rw [div_mul_cancel₀ _ hY0.ne'] at this
    linarith
  have hε1 : β₀ / Y ≤ 1 := by
    rw [div_le_one hY0]
    have : β ≤ G := by have : 0 ≤ P * ωt := by positivity
                       linarith
    linarith
  -- perturbations
  have hVb' : Real.sqrt Vb ≤ (1 + η / y₀) * Real.sqrt vb := cmp_sqrt_up hy₀ hvb hη0 hVb
  have hL' : P * (Real.sqrt v * Real.sqrt Vb) ≤ (1 + η / y₀) * (P * ωt) := by
    have hP0 : 0 ≤ P := by positivity
    have := mul_le_mul_of_nonneg_left hVb' (mul_nonneg hP0 (Real.sqrt_nonneg v))
    rw [hωt]; nlinarith
  have hκ : (1 - b * η / y₁) * G ≤
      Real.sqrt y * Real.sqrt yb := by
    have := cmp_sqrt_down hy₁0 hyt1 (mul_nonneg hb0.le hη0) hθ1 hyb
    rw [hG]
    have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg y)
    linarith
  exact cmp_weight_margin hG0 hLG hεG hL' hκ (div_nonneg hη0 hy₀.le)
    (div_nonneg (mul_nonneg hb0.le hη0) hy₁0.le) hsmall hε1

/-- **Separate-port branch scalar step** (one block). Exact pair
`(m, u = (z - b m)⁻¹)`, approximate pair `(m̄, ū = (z - b m̄)⁻¹ + r')`; `V̄ ≤ -Im m̄ + η` is the
imaginary part of the approximate top trace. With `P = c + b² |u| |ũ|`, `ũ = (z - b m̄)⁻¹`:
`|σ - σ̄| ≤ P |m - m̄| + b η`, the weighted margin `P √v √V̄ ≤ (1 - ε₀/2) √y √ȳ`, and
`|ū - u| ≤ b ζ₀⁻² |m - m̄| + η`, where `σ = c m + b u`, `y = -Im σ` etc. -/
theorem cmp_sep_branch_scalar {b ζ₀ y₀ y₁ η A Y Vb : ℝ} {z m u mb ub r' : ℂ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3)
    (hy₀ : 0 < y₀) (hy₁ : y₁ = (1 - 2 * b) * y₀) (hη0 : 0 ≤ η)
    (hA : A = 4 + 2 / y₁) (hY : Y = 2 / y₁ + 1 / ζ₀ + 2)
    (hθ1 : b * η / y₁ ≤ 1)
    (hsmall : η / y₀ + b * η / y₁ ≤ b * ζ₀ / A ^ 2 / Y / 2)
    (hu : u = (z - (b : ℂ) * m)⁻¹) (hub : ub = (z - (b : ℂ) * mb)⁻¹ + r') (hr' : ‖r'‖ ≤ η)
    (hv : y₀ ≤ -m.im) (hvb : y₀ ≤ -mb.im) (hm : ‖m‖ ≤ 1 / y₁) (hmb : ‖mb‖ ≤ 2 / y₁ + 1)
    (hVb : Vb ≤ -mb.im + η) :
    ‖(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u) - (((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub)‖ ≤
        ((1 - 2 * b) + b ^ 2 * (‖u‖ * ‖(z - (b : ℂ) * mb)⁻¹‖)) * ‖m - mb‖ + b * η ∧
      ((1 - 2 * b) + b ^ 2 * (‖u‖ * ‖(z - (b : ℂ) * mb)⁻¹‖)) *
          (Real.sqrt (-m.im) * Real.sqrt Vb) ≤
        (1 - b * ζ₀ / A ^ 2 / Y / 2) *
          (Real.sqrt (-(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u).im) *
            Real.sqrt (-(((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub).im)) ∧
      ‖ub - u‖ ≤ b * ζ₀⁻¹ ^ 2 * ‖m - mb‖ + η := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hy₁0 : 0 < y₁ := by rw [hy₁]; exact mul_pos (by linarith) hy₀
  have hqim : (z - (b : ℂ) * m).im = z.im + b * (-m.im) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hqbim : (z - (b : ℂ) * mb).im = z.im + b * (-mb.im) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hv0 : 0 ≤ -m.im := hy₀.le.trans hv
  have hvb0 : 0 ≤ -mb.im := hy₀.le.trans hvb
  have hqζ : ζ₀ ≤ (z - (b : ℂ) * m).im := by
    rw [hqim]; have := mul_nonneg hb0.le hv0; linarith
  have hqbζ : ζ₀ ≤ (z - (b : ℂ) * mb).im := by
    rw [hqbim]; have := mul_nonneg hb0.le hvb0; linarith
  have hqA : ‖z - (b : ℂ) * m‖ ≤ A := by
    rw [hA]
    have h1 := norm_sub_le z ((b : ℂ) * m)
    rw [cmp_norm_real_mul hb0.le] at h1
    have h2 := mul_le_mul (show b ≤ 1 by linarith) hm (norm_nonneg _) zero_le_one
    have : 1 / y₁ ≤ 2 / y₁ := div_le_div_of_nonneg_right (by norm_num) hy₁0.le
    linarith
  have hqbA : ‖z - (b : ℂ) * mb‖ ≤ A := by
    rw [hA]
    have h1 := norm_sub_le z ((b : ℂ) * mb)
    rw [cmp_norm_real_mul hb0.le] at h1
    have h2 := mul_le_mul (show b ≤ 1 / 2 by linarith) hmb (norm_nonneg _) (by norm_num)
    have : 1 / 2 * (2 / y₁ + 1) = 1 / y₁ + 1 / 2 := by field_simp
    have : 1 / y₁ ≤ 2 / y₁ := div_le_div_of_nonneg_right (by norm_num) hy₁0.le
    linarith
  have hA0 : 0 < A := by rw [hA]; positivity
  have hq0 : z - (b : ℂ) * m ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hqζ; linarith
  have hqb0 : z - (b : ℂ) * mb ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hqbζ; linarith
  have hU1 : ‖u‖ ≤ ζ₀⁻¹ := by rw [hu]; exact (cmp_inv_bounds hζ₀ hqζ hqA).1
  have hU2 : A⁻¹ ≤ ‖u‖ := by rw [hu]; exact (cmp_inv_bounds hζ₀ hqζ hqA).2
  have hUt1 : ‖(z - (b : ℂ) * mb)⁻¹‖ ≤ ζ₀⁻¹ := (cmp_inv_bounds hζ₀ hqbζ hqbA).1
  have hUt2 : A⁻¹ ≤ ‖(z - (b : ℂ) * mb)⁻¹‖ := (cmp_inv_bounds hζ₀ hqbζ hqbA).2
  have hw : -u.im = ‖u‖ ^ 2 * (z.im + b * (-m.im)) := by rw [hu, cmp_neg_im_inv, hqim]
  have hwt : -((z - (b : ℂ) * mb)⁻¹).im = ‖(z - (b : ℂ) * mb)⁻¹‖ ^ 2 * (z.im + b * (-mb.im)) := by
    rw [cmp_neg_im_inv, hqbim]
  have hsub : u - (z - (b : ℂ) * mb)⁻¹ = (b : ℂ) * (m - mb) * (u * (z - (b : ℂ) * mb)⁻¹) := by
    rw [hu]; exact cmp_port_sub hq0 hqb0
  set ut := (z - (b : ℂ) * mb)⁻¹ with hut
  set U := ‖u‖ with hUdef
  set Ut := ‖ut‖ with hUtdef
  set v := -m.im with hvdef
  set vb := -mb.im with hvbdef
  have hU0 : 0 ≤ U := norm_nonneg _
  have hUt0 : 0 ≤ Ut := norm_nonneg _
  have hdiffu : ‖u - ut‖ = b * ‖m - mb‖ * (U * Ut) := by
    rw [hsub, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
  -- (a)
  have hA1 : ‖(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u) -
      (((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub)‖ ≤
        ((1 - 2 * b) + b ^ 2 * (U * Ut)) * ‖m - mb‖ + b * η := by
    have heq : (((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u) -
        (((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub) =
        ((1 - 2 * b : ℝ) : ℂ) * (m - mb) + (b : ℂ) * (u - ut) - (b : ℂ) * r' := by
      rw [hub]; ring
    rw [heq]
    have h1 := norm_sub_le (((1 - 2 * b : ℝ) : ℂ) * (m - mb) + (b : ℂ) * (u - ut)) ((b : ℂ) * r')
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * (m - mb)) ((b : ℂ) * (u - ut))
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le, hdiffu] at h2
    rw [cmp_norm_real_mul hb0.le] at h1
    have h3 := mul_le_mul_of_nonneg_left hr' hb0.le
    have e : (1 - 2 * b) * ‖m - mb‖ + b * (b * ‖m - mb‖ * (U * Ut)) =
        ((1 - 2 * b) + b ^ 2 * (U * Ut)) * ‖m - mb‖ := by ring
    linarith
  -- (d)
  have hD : ‖ub - u‖ ≤ b * ζ₀⁻¹ ^ 2 * ‖m - mb‖ + η := by
    have heq : ub - u = r' - (u - ut) := by rw [hub]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    rw [hdiffu]
    have h1 : U * Ut ≤ ζ₀⁻¹ * ζ₀⁻¹ := mul_le_mul hU1 hUt1 hUt0 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hb0.le (norm_nonneg (m - mb)))
    have e : b * ‖m - mb‖ * (ζ₀⁻¹ * ζ₀⁻¹) = b * ζ₀⁻¹ ^ 2 * ‖m - mb‖ := by ring
    linarith
  refine ⟨hA1, ?_, hD⟩
  -- (b): the weighted margin
  have hy : -(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u).im =
      (1 - 2 * b) * v + b * U ^ 2 * z.im + b ^ 2 * U ^ 2 * v := by
    rw [cmp_im_comb, hw]; ring
  set y := -(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u).im with hydef
  set yt := (1 - 2 * b) * vb + b * Ut ^ 2 * z.im + b ^ 2 * Ut ^ 2 * vb with hytdef
  have hyb : yt - b * η ≤ -(((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub).im := by
    have hrim : r'.im ≤ η := (le_abs_self r'.im).trans ((Complex.abs_im_le_norm r').trans hr')
    have key : -(((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub).im = yt - b * r'.im := by
      rw [cmp_im_comb, hub, Complex.add_im]
      have : -(ut.im + r'.im) = -ut.im - r'.im := by ring
      rw [this, hwt, hytdef]; ring
    rw [key]
    have := mul_le_mul_of_nonneg_left hrim hb0.le
    linarith
  have hζ0 : 0 < z.im := lt_of_lt_of_le hζ₀ hz
  have hyt1 : y₁ ≤ yt := by
    rw [hytdef, hy₁]
    have := mul_le_mul_of_nonneg_left hvb hc0
    have : 0 ≤ b * Ut ^ 2 * z.im := by positivity
    have : 0 ≤ b ^ 2 * Ut ^ 2 * vb := by positivity
    linarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyt0 : 0 ≤ yt := hy₁0.le.trans hyt1
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyY : y ≤ Y := by
    have h1 : y ≤ ‖((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u‖ := by
      rw [hydef]; exact (neg_le_abs _).trans (Complex.abs_im_le_norm _)
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * m) ((b : ℂ) * u)
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
    have h3 := mul_le_mul (show 1 - 2 * b ≤ 1 by linarith) hm (norm_nonneg _) zero_le_one
    have h4 := mul_le_mul (show b ≤ 1 by linarith) hU1 hU0 zero_le_one
    have : 1 / y₁ ≤ 2 / y₁ := div_le_div_of_nonneg_right (by norm_num) hy₁0.le
    rw [hY]; rw [one_div] at *; linarith
  have hytY : yt ≤ Y := by
    have h1 : yt = -(((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ut).im := by
      rw [cmp_im_comb, hwt, hytdef]; ring
    have h1' : yt ≤ ‖((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ut‖ := by
      rw [h1]; exact (neg_le_abs _).trans (Complex.abs_im_le_norm _)
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * mb) ((b : ℂ) * ut)
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
    have h3 := mul_le_mul (show 1 - 2 * b ≤ 1 by linarith) hmb (norm_nonneg _) zero_le_one
    have h4 := mul_le_mul (show b ≤ 1 by linarith) hUt1 hUt0 zero_le_one
    rw [hY]; rw [one_div] at *; linarith
  have hyb' := hyb
  exact cmp_sep_margin_real hb0 hb1 hζ₀ hz hy₀ hy₁0 hη0 hA0 (by rw [hY]; positivity) hθ1 hsmall
    hv hvb hVb hU0 hU2 hUt2 hy rfl hyt1 hyY hytY hyb'

/-- **Abstract weighted contraction** (the closing step of the paper). Errors `e_j ≥ 0`,
weights `ω_j ∈ [ω_lo, ω_hi]`, `κ_j ≥ κ_lo > 0`, shift differences `d_j ≤ Σ_k Γ_jk e_k + b η` with
weighted row sums `Σ_k Γ_jk ω_k ≤ (1 - ε/2) κ_j`, and the trace step
"`d_j ≤ S κ_j` for all `j` implies `e_i ≤ ω_i S + η`". Then
`e_i ≤ ω_hi (2/ε) (b/κ_lo + 1/ω_lo) η`. -/
theorem cmp_branch_close {e ω κ d : Fin 2 → ℝ} {Γ : Fin 2 → Fin 2 → ℝ}
    {ε b η ωlo ωhi κlo : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 2) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hωlo : 0 < ωlo) (hκlo : 0 < κlo) (he : ∀ j, 0 ≤ e j) (hω : ∀ j, ωlo ≤ ω j)
    (hωh : ∀ j, ω j ≤ ωhi) (hκ : ∀ j, κlo ≤ κ j) (hΓ : ∀ j k, 0 ≤ Γ j k)
    (hd : ∀ j, d j ≤ ∑ k, Γ j k * e k + b * η)
    (hΓω : ∀ j, ∑ k, Γ j k * ω k ≤ (1 - ε / 2) * κ j)
    (hKL : ∀ S : ℝ, 0 ≤ S → (∀ j, d j ≤ S * κ j) → ∀ i, e i ≤ ω i * S + η) (i : Fin 2) :
    e i ≤ ωhi * (2 / ε * ((b / κlo + 1 / ωlo) * η)) := by
  have hωpos : ∀ j, 0 < ω j := fun j => lt_of_lt_of_le hωlo (hω j)
  obtain ⟨ξ, hξ⟩ : ∃ x : ℝ, x = max (e 0 / ω 0) (e 1 / ω 1) := ⟨_, rfl⟩
  have heξ : ∀ j, e j ≤ ξ * ω j := fun j => by
    have h : e j / ω j ≤ ξ := by
      rw [hξ]
      fin_cases j
      · exact le_max_left _ _
      · exact le_max_right _ _
    exact (div_le_iff₀ (hωpos j)).mp h
  have hξ0 : 0 ≤ ξ := by
    rw [hξ]; exact (div_nonneg (he 0) (hωpos 0).le).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : ∃ x : ℝ, x = (1 - ε / 2) * ξ + b * η / κlo := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    have := mul_nonneg (show 0 ≤ 1 - ε / 2 by linarith) hξ0
    have : 0 ≤ b * η / κlo := by positivity
    linarith
  have hdS : ∀ j, d j ≤ S * κ j := fun j => by
    have h1 : ∑ k, Γ j k * e k ≤ ξ * ∑ k, Γ j k * ω k := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => by
        have := mul_le_mul_of_nonneg_left (heξ k) (hΓ j k); linarith
    have h2 := mul_le_mul_of_nonneg_left (hΓω j) hξ0
    have h3 : b * η ≤ b * η / κlo * κ j := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hκlo]
      exact mul_le_mul_of_nonneg_left (hκ j) (mul_nonneg hb hη)
    have e1 : S * κ j = ξ * ((1 - ε / 2) * κ j) + b * η / κlo * κ j := by rw [hS]; ring
    linarith [hd j]
  have hstep := hKL S hS0 hdS
  have hei : ∀ k, e k / ω k ≤ S + η / ωlo := fun k => by
    rw [div_le_iff₀ (hωpos k)]
    have h5 : η ≤ η / ωlo * ω k := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hωlo]
      exact mul_le_mul_of_nonneg_left (hω k) hη
    have := hstep k
    have e1 : (S + η / ωlo) * ω k = ω k * S + η / ωlo * ω k := by ring
    linarith
  have hξle : ξ ≤ S + η / ωlo := by rw [hξ]; exact max_le (hei 0) (hei 1)
  have hξb : ε / 2 * ξ ≤ (b / κlo + 1 / ωlo) * η := by
    have e1 : (b / κlo + 1 / ωlo) * η = b * η / κlo + η / ωlo := by ring
    rw [hS] at hξle
    linarith
  have hξb' : ξ ≤ 2 / ε * ((b / κlo + 1 / ωlo) * η) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hε0]; linarith
  have := heξ i
  have := mul_le_mul (hωh i) hξb' hξ0 ((hωlo.le).trans ((hω 0).trans (hωh 0)))
  linarith

/-- Imaginary-part bounds for the two shift families in the separate branch argument:
`-Im σ_j ≥ c y₀` for the exact pair and `-Im σ̄_j ≥ c y₀ / 2` for the approximate pair when
`η ≤ c y₀` (`b < 1/2`). -/
theorem cmp_sep_branch_im {b ζ₀ y₀ η : ℝ} {z : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hη0 : 0 ≤ η) (hηy : η ≤ (1 - 2 * b) * y₀)
    {m u mb ub r' : ℂ} (hu : u = (z - (b : ℂ) * m)⁻¹) (hub : ub = (z - (b : ℂ) * mb)⁻¹ + r')
    (hr' : ‖r'‖ ≤ η) (hv : y₀ ≤ -m.im) (hvb : y₀ ≤ -mb.im) (hy₀ : 0 < y₀) :
    (1 - 2 * b) * y₀ ≤ -(((1 - 2 * b : ℝ) : ℂ) * m + (b : ℂ) * u).im ∧
      (1 - 2 * b) * y₀ / 2 ≤ -(((1 - 2 * b : ℝ) : ℂ) * mb + (b : ℂ) * ub).im := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hqim : ∀ w : ℂ, (z - (b : ℂ) * w).im = z.im + b * (-w.im) := fun w => by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hwpos : ∀ w : ℂ, 0 ≤ -w.im → 0 ≤ -((z - (b : ℂ) * w)⁻¹).im := fun w hw => by
    rw [cmp_neg_im_inv, hqim]
    have := mul_nonneg hb0.le hw
    have : 0 < z.im := lt_of_lt_of_le hζ₀ hz
    positivity
  constructor
  · rw [cmp_im_comb, hu]
    have h1 := mul_nonneg hb0.le (hwpos m ((hy₀.le).trans hv))
    have h2 := mul_le_mul_of_nonneg_left hv hc0
    linarith
  · rw [cmp_im_comb, hub, Complex.add_im]
    have h1 := mul_nonneg hb0.le (hwpos mb ((hy₀.le).trans hvb))
    have h2 : r'.im ≤ η := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hr')
    have h3 := mul_le_mul_of_nonneg_left hvb hc0
    have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
    have h6 : b * η ≤ (1 - 2 * b) * y₀ / 2 := by
      have := mul_le_mul (show b ≤ 1 / 2 by linarith) hηy hη0 (by norm_num); linarith
    have e : b * -((z - (b : ℂ) * mb)⁻¹.im + r'.im) =
        b * -((z - (b : ℂ) * mb)⁻¹).im - b * r'.im := by ring
    rw [e]
    linarith

/-- Trace step of the branch argument (both port cases): the exact top `M` and the
approximate top `M̄`; if the shift differences are `≤ S √y_j √ȳ_j`, then
`|m_i - m̄_i| ≤ √v_i √V̄_i S + η` where `V̄_i = -Im tr_i M̄`. -/
theorem cmp_branch_trace_step {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) (σ σb m mb r : Fin 2 → ℂ) {η : ℝ} (hσ : ∀ j, (σ j).im < 0)
    (hσb : ∀ j, (σb j).im < 0) (htr : ∀ j, blockTrace (cmpInv H σ) j = m j)
    (happ : ∀ j, mb j = blockTrace (cmpInv H σb) j + r j) (hr : ‖r‖ ≤ η)
    (S : ℝ) (hS : 0 ≤ S)
    (hδ : ∀ j, ‖σ j - σb j‖ ≤ S * (Real.sqrt (-(σ j).im) * Real.sqrt (-(σb j).im)))
    (i : Fin 2) :
    ‖m i - mb i‖ ≤
      Real.sqrt (-(m i).im) * Real.sqrt (-(blockTrace (cmpInv H σb) i).im) * S + η := by
  have h1 := cmp_trace_sub_weighted H hH σ σb hσ hσb hS hδ i
  rw [htr i] at h1
  have h2 : m i - mb i = (m i - blockTrace (cmpInv H σb) i) - r i := by rw [happ i]; ring
  rw [h2]
  have := norm_sub_le (m i - blockTrace (cmpInv H σb) i) (r i)
  have := (norm_le_pi_norm r i).trans hr
  linarith

/-- The explicit branch constant `ε₀ = b ζ₀ / A² / Y`, `y₁ = c y₀`, `A = 4 + 2/y₁`,
`Y = 2/y₁ + 1/ζ₀ + 2`. -/
def cmpEps (b ζ₀ y₀ : ℝ) : ℝ :=
  b * ζ₀ / (4 + 2 / ((1 - 2 * b) * y₀)) ^ 2 / (2 / ((1 - 2 * b) * y₀) + 1 / ζ₀ + 2)

/-- The residual threshold `η₀ = min(1, y₁, y₀/2, ε₀ / (2 (1/y₀ + b/y₁)))`. -/
def cmpEta (b ζ₀ y₀ : ℝ) : ℝ :=
  min (min 1 ((1 - 2 * b) * y₀)) (min (y₀ / 2)
    (cmpEps b ζ₀ y₀ / (2 * (1 / y₀ + b / ((1 - 2 * b) * y₀)))))

/-- The branch constant `C'' = (1 + 2b ζ₀⁻²) (2/y₁) (2/ε₀) (2b/y₁ + 2/y₀) + 1`. -/
def cmpBranchC (b ζ₀ y₀ : ℝ) : ℝ :=
  (1 + 2 * b * ζ₀⁻¹ ^ 2) * (2 / ((1 - 2 * b) * y₀)) * (2 / cmpEps b ζ₀ y₀) *
    (2 * b / ((1 - 2 * b) * y₀) + 2 / y₀) + 1

/-- The common-port branch constant (same expression as `cmpBranchC`; the port bound uses
both blocks, `|ū₀ - u₀| ≤ b ζ₀⁻² (e₀ + e₁) + η ≤ 2b ζ₀⁻² E + η`). -/
def cmpComBranchC (b ζ₀ y₀ : ℝ) : ℝ := cmpBranchC b ζ₀ y₀

theorem cmpEps_pos {b ζ₀ y₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀)
    (hy₀ : 0 < y₀) : 0 < cmpEps b ζ₀ y₀ := by
  have : 0 < (1 - 2 * b) * y₀ := mul_pos (by linarith) hy₀
  unfold cmpEps; positivity

theorem cmpEta_pos {b ζ₀ y₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀)
    (hy₀ : 0 < y₀) : 0 < cmpEta b ζ₀ y₀ := by
  have h1 : 0 < (1 - 2 * b) * y₀ := mul_pos (by linarith) hy₀
  have h2 := cmpEps_pos hb0 hb1 hζ₀ hy₀
  unfold cmpEta
  exact lt_min (lt_min one_pos h1) (lt_min (by linarith) (by positivity))

/-- Consequences of `η ≤ η₀` used by both branch theorems. -/
theorem cmpEta_props {b ζ₀ y₀ η : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hy₀ : 0 < y₀)
    (hη0 : 0 ≤ η) (hη : η ≤ cmpEta b ζ₀ y₀) :
    η ≤ 1 ∧ η ≤ (1 - 2 * b) * y₀ ∧ η ≤ y₀ / 2 ∧ b * η / ((1 - 2 * b) * y₀) ≤ 1 ∧
      η / y₀ + b * η / ((1 - 2 * b) * y₀) ≤
        b * ζ₀ / (4 + 2 / ((1 - 2 * b) * y₀)) ^ 2 / (2 / ((1 - 2 * b) * y₀) + 1 / ζ₀ + 2) / 2 := by
  have hy₁0 : 0 < (1 - 2 * b) * y₀ := mul_pos (by linarith) hy₀
  unfold cmpEta at hη
  have hη1 : η ≤ 1 := hη.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hηy₁ : η ≤ (1 - 2 * b) * y₀ := hη.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hηy₀ : η ≤ y₀ / 2 := hη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηε := hη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hK : 0 < 2 * (1 / y₀ + b / ((1 - 2 * b) * y₀)) := by positivity
  refine ⟨hη1, hηy₁, hηy₀, ?_, ?_⟩
  · rw [div_le_one hy₁0]
    have := mul_le_mul (show b ≤ 1 by linarith) hηy₁ hη0 zero_le_one
    linarith
  · have := (le_div_iff₀ hK).mp hηε
    have e : η / y₀ + b * η / ((1 - 2 * b) * y₀) = η * (1 / y₀ + b / ((1 - 2 * b) * y₀)) := by
      ring
    rw [e]; unfold cmpEps at this; linarith

/-- **Branch identification, separate ports** (deterministic). `H` Hermitian,
`Im z ≥ ζ₀ > 0`, `|z| ≤ 3`. Let `(m, u)` solve the separate-port equations exactly
(`m_i = tr_i[(H - diag(c m + b u))⁻¹]`, `u_i = (z - b m_i)⁻¹`) with `-Im m_i ≥ y₀ > 0`, and let
`(m̄, ū)` solve them up to residuals `r, r'` (`‖r‖, ‖r'‖ ≤ η ≤ η₀`) with `-Im m̄_i ≥ y₀`. Then
`|m̄_i - m_i| + |ū_i - u_i| ≤ C'' η`, `η₀ = cmpEta b ζ₀ y₀`, `C'' = cmpBranchC b ζ₀ y₀`
(depending only on `b, ζ₀, y₀`; uniform in `W` and `H`). No closeness of `(m̄, ū)` to `(m, u)`
is assumed: this is the global weighted-contraction argument. -/
theorem cmp_sep_branch {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) {b ζ₀ y₀ η : ℝ} {z : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hy₀ : 0 < y₀) (hη0 : 0 ≤ η)
    (hη : η ≤ cmpEta b ζ₀ y₀)
    (m u : Fin 2 → ℂ)
    (hsol : ∀ i, m i = blockTrace (cmpInv H (cmpSepShift b m u)) i ∧
      u i = (z - (b : ℂ) * m i)⁻¹)
    (hv : ∀ i, y₀ ≤ -(m i).im)
    (mb ub r r' : Fin 2 → ℂ)
    (happ : ∀ i, mb i = blockTrace (cmpInv H (cmpSepShift b mb ub)) i + r i ∧
      ub i = (z - (b : ℂ) * mb i)⁻¹ + r' i)
    (hr : ‖r‖ ≤ η) (hr' : ‖r'‖ ≤ η) (hvb : ∀ i, y₀ ≤ -(mb i).im) (i : Fin 2) :
    ‖mb i - m i‖ + ‖ub i - u i‖ ≤ cmpBranchC b ζ₀ y₀ * η := by
  obtain ⟨hη1, hηy₁, hηy₀, hθ1, hsmall⟩ := cmpEta_props hb0 hb1 hy₀ hη0 hη
  have hy₁0 : 0 < (1 - 2 * b) * y₀ := mul_pos (by linarith) hy₀
  have hε0 := cmpEps_pos hb0 hb1 hζ₀ hy₀
  have hr'j : ∀ j, ‖r' j‖ ≤ η := fun j => (norm_le_pi_norm r' j).trans hr'
  have him := fun j => cmp_sep_branch_im hb0 hb1 hζ₀ hz hη0 hηy₁ (hsol j).2 (happ j).2 (hr'j j)
    (hv j) (hvb j) hy₀
  have hyσ : ∀ j, (1 - 2 * b) * y₀ ≤ -(cmpSepShift b m u j).im := fun j => (him j).1
  have hyσb : ∀ j, (1 - 2 * b) * y₀ / 2 ≤ -(cmpSepShift b mb ub j).im := fun j => (him j).2
  have hy₂0 : 0 < (1 - 2 * b) * y₀ / 2 := by positivity
  have hσim : ∀ j, (cmpSepShift b m u j).im < 0 := fun j => by linarith [hyσ j]
  have hσbim : ∀ j, (cmpSepShift b mb ub j).im < 0 := fun j => by linarith [hyσb j]
  have htrM : ∀ j, blockTrace (cmpInv H (cmpSepShift b m u)) j = m j := fun j => (hsol j).1.symm
  have hmb1 : ∀ j, ‖m j‖ ≤ 1 / ((1 - 2 * b) * y₀) := fun j => by
    rw [← htrM j, one_div]; exact cmp_trace_le H hH _ hy₁0 hyσ j
  have htrMb : ∀ j, ‖blockTrace (cmpInv H (cmpSepShift b mb ub)) j‖ ≤ 2 / ((1 - 2 * b) * y₀) :=
    fun j => by
    have := cmp_trace_le H hH _ hy₂0 hyσb j
    rwa [inv_div] at this
  have hrj : ∀ j, ‖r j‖ ≤ η := fun j => (norm_le_pi_norm r j).trans hr
  have hmbb : ∀ j, ‖mb j‖ ≤ 2 / ((1 - 2 * b) * y₀) + 1 := fun j => by
    rw [(happ j).1]
    have := norm_add_le (blockTrace (cmpInv H (cmpSepShift b mb ub)) j) (r j)
    linarith [htrMb j, hrj j]
  have hVb : ∀ j, -(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im = -(mb j).im + (r j).im :=
    fun j => by
    have e : blockTrace (cmpInv H (cmpSepShift b mb ub)) j = mb j - r j := by
      rw [(happ j).1]; ring
    rw [e, Complex.sub_im]; ring
  have hrim : ∀ j, |(r j).im| ≤ η := fun j => (Complex.abs_im_le_norm _).trans (hrj j)
  have hVbup : ∀ j, -(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im ≤ -(mb j).im + η :=
    fun j => by rw [hVb j]; linarith [le_abs_self (r j).im, hrim j]
  have hVblo : ∀ j, y₀ / 2 ≤ -(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im :=
    fun j => by rw [hVb j]; linarith [neg_abs_le (r j).im, hrim j, hvb j]
  have hVbhi : ∀ j, -(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im ≤
      2 / ((1 - 2 * b) * y₀) := fun j =>
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (htrMb j))
  have hsc := fun j => cmp_sep_branch_scalar hb0 hb1 hζ₀ hz hz3 hy₀ rfl hη0 rfl rfl hθ1 hsmall
    (hsol j).2 (happ j).2 (hr'j j) (hv j) (hvb j) (hmb1 j) (hmbb j) (hVbup j)
  -- weights and the abstract closing step
  have hsqrt_lo : ∀ {p q ℓ : ℝ}, 0 ≤ ℓ → 0 ≤ p → ℓ ^ 2 ≤ p * q →
      ℓ ≤ Real.sqrt p * Real.sqrt q := fun {p q ℓ} hℓ hp h => by
    calc ℓ = Real.sqrt (ℓ ^ 2) := (Real.sqrt_sq hℓ).symm
      _ ≤ Real.sqrt (p * q) := Real.sqrt_le_sqrt h
      _ = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp _
  have hsqrt_hi : ∀ {p q ℓ : ℝ}, 0 ≤ ℓ → 0 ≤ p → p * q ≤ ℓ ^ 2 →
      Real.sqrt p * Real.sqrt q ≤ ℓ := fun {p q ℓ} hℓ hp h => by
    calc Real.sqrt p * Real.sqrt q = Real.sqrt (p * q) := (Real.sqrt_mul hp _).symm
      _ ≤ Real.sqrt (ℓ ^ 2) := Real.sqrt_le_sqrt h
      _ = ℓ := Real.sqrt_sq hℓ
  have hωlo : ∀ j, y₀ / 2 ≤ Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im) := fun j => by
    refine hsqrt_lo (by linarith) ((hy₀.le).trans (hv j)) ?_
    have := mul_le_mul (hv j) (hVblo j) (by linarith) ((hy₀.le).trans (hv j))
    have : (y₀ / 2) ^ 2 ≤ y₀ * (y₀ / 2) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hωhi : ∀ j, Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im) ≤
        2 / ((1 - 2 * b) * y₀) := fun j => by
    have hv0 : 0 ≤ -(m j).im := (hy₀.le).trans (hv j)
    refine hsqrt_hi (by positivity) hv0 ?_
    have h1 : -(m j).im ≤ 1 / ((1 - 2 * b) * y₀) :=
      (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hmb1 j))
    have h2 := mul_le_mul h1 (hVbhi j) ((by linarith [hVblo j])) (by positivity)
    have h3 : 1 / ((1 - 2 * b) * y₀) * (2 / ((1 - 2 * b) * y₀)) ≤
        (2 / ((1 - 2 * b) * y₀)) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num)
        hy₁0.le) (by positivity)
    linarith
  have hκlo : ∀ j, (1 - 2 * b) * y₀ / 2 ≤ Real.sqrt (-(cmpSepShift b m u j).im) *
      Real.sqrt (-(cmpSepShift b mb ub j).im) := fun j => by
    refine hsqrt_lo hy₂0.le (by linarith [hyσ j]) ?_
    have := mul_le_mul (show (1 - 2 * b) * y₀ / 2 ≤ -(cmpSepShift b m u j).im by
      linarith [hyσ j]) (hyσb j) hy₂0.le (by linarith [hyσ j])
    rw [sq]; exact this
  have hε2 : cmpEps b ζ₀ y₀ ≤ 2 := by
    have h := (hsc 0).2.1
    by_contra hcon
    push Not at hcon
    have hneg : 1 - cmpEps b ζ₀ y₀ / 2 < 0 := by linarith
    have hκ0 := lt_of_lt_of_le hy₂0 (hκlo 0)
    have hP0 : 0 ≤ ((1 - 2 * b) + b ^ 2 * (‖u 0‖ * ‖(z - (b : ℂ) * mb 0)⁻¹‖)) *
        (Real.sqrt (-(m 0).im) * Real.sqrt (-(blockTrace (cmpInv H
          (cmpSepShift b mb ub)) 0).im)) := by
      have : 0 ≤ 1 - 2 * b := by linarith
      positivity
    have := mul_neg_of_neg_of_pos hneg hκ0
    unfold cmpEps at hneg this
    unfold cmpSepShift at this hκ0
    linarith
  obtain ⟨P, hP⟩ : ∃ P : Fin 2 → ℝ, P = fun j =>
      (1 - 2 * b) + b ^ 2 * (‖u j‖ * ‖(z - (b : ℂ) * mb j)⁻¹‖) := ⟨_, rfl⟩
  have hP0 : ∀ j, 0 ≤ P j := fun j => by
    rw [hP]; have : 0 ≤ 1 - 2 * b := by linarith
    positivity
  have hsumΓ : ∀ (j : Fin 2) (f : Fin 2 → ℝ),
      ∑ k, (if j = k then P j else 0) * f k = P j * f j := fun j f => by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]; simp
  have hdj : ∀ j, ‖cmpSepShift b m u j - cmpSepShift b mb ub j‖ ≤
      ∑ k, (if j = k then P j else 0) * ‖m k - mb k‖ + b * η := fun j => by
    rw [hsumΓ, hP]; exact (hsc j).1
  have hΓω : ∀ j, ∑ k, (if j = k then P j else 0) * (Real.sqrt (-(m k).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpSepShift b mb ub)) k).im)) ≤
        (1 - cmpEps b ζ₀ y₀ / 2) * (Real.sqrt (-(cmpSepShift b m u j).im) *
          Real.sqrt (-(cmpSepShift b mb ub j).im)) := fun j => by
    rw [hsumΓ, hP]; exact (hsc j).2.1
  have hclose := cmp_branch_close (e := fun j => ‖m j - mb j‖)
    (ω := fun j => Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpSepShift b mb ub)) j).im))
    (κ := fun j => Real.sqrt (-(cmpSepShift b m u j).im) * Real.sqrt (-(cmpSepShift b mb ub j).im))
    (d := fun j => ‖cmpSepShift b m u j - cmpSepShift b mb ub j‖)
    (Γ := fun j k => if j = k then P j else 0)
    (b := b) (η := η) hε0 hε2 hb0.le hη0 (by linarith : (0 : ℝ) < y₀ / 2) hy₂0
    (fun j => norm_nonneg _) hωlo hωhi hκlo
    (fun j k => by
      show 0 ≤ (if j = k then P j else 0)
      split_ifs
      · exact hP0 j
      · exact le_refl 0)
    hdj hΓω
    (fun S hS hδ k => cmp_branch_trace_step H hH _ _ m mb r hσim hσbim htrM
      (fun j => (happ j).1) hr S hS hδ k) i
  -- conclusion
  have hd := (hsc i).2.2
  have e1 : b / ((1 - 2 * b) * y₀ / 2) + 1 / (y₀ / 2) = 2 * b / ((1 - 2 * b) * y₀) + 2 / y₀ := by
    field_simp
  have hclose' : ‖m i - mb i‖ ≤ 2 / ((1 - 2 * b) * y₀) * (2 / cmpEps b ζ₀ y₀ *
      ((2 * b / ((1 - 2 * b) * y₀) + 2 / y₀) * η)) := by
    have := hclose; rw [e1] at this; exact this
  rw [norm_sub_rev (mb i) (m i)]
  obtain ⟨E, hE⟩ : ∃ x : ℝ, x = 2 / ((1 - 2 * b) * y₀) * (2 / cmpEps b ζ₀ y₀ *
      ((2 * b / ((1 - 2 * b) * y₀) + 2 / y₀) * η)) := ⟨_, rfl⟩
  rw [← hE] at hclose'
  have hC : cmpBranchC b ζ₀ y₀ * η = (1 + 2 * b * ζ₀⁻¹ ^ 2) * E + η := by
    rw [hE, cmpBranchC]; ring
  rw [hC]
  have hk : 0 ≤ b * ζ₀⁻¹ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hclose' hk
  have h2 : 0 ≤ E := (norm_nonneg _).trans hclose'
  have h3 : 0 ≤ b * ζ₀⁻¹ ^ 2 * E := mul_nonneg hk h2
  have e2 : (1 + 2 * b * ζ₀⁻¹ ^ 2) * E = E + b * ζ₀⁻¹ ^ 2 * E + b * ζ₀⁻¹ ^ 2 * E := by ring
  linarith

/-!
## 8. Branch identification, common port
-/

/-- Real-variable core of the common-port weighted margin (block `j`, values `vj, vbj, Vbj`;
both blocks `v₀, v₁, ...` enter through the common port). -/
theorem cmp_com_margin_real {b ζ₀ y₀ y₁ η A Y ζ vj vbj Vbj v₀ v₁ vb₀ vb₁ Vb₀ Vb₁ U Ut y yt yb : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ ζ) (hy₀ : 0 < y₀)
    (hy₁0 : 0 < y₁) (hη0 : 0 ≤ η) (hA0 : 0 < A) (hY0 : 0 < Y) (hθ1 : b * η / y₁ ≤ 1)
    (hsmall : η / y₀ + b * η / y₁ ≤ b * ζ₀ / A ^ 2 / Y / 2)
    (hvj : y₀ ≤ vj) (hvbj : y₀ ≤ vbj) (hVbj : Vbj ≤ vbj + η)
    (hv₀ : y₀ ≤ v₀) (hvb₀ : y₀ ≤ vb₀) (hVb₀ : Vb₀ ≤ vb₀ + η)
    (hv₁ : y₀ ≤ v₁) (hvb₁ : y₀ ≤ vb₁) (hVb₁ : Vb₁ ≤ vb₁ + η)
    (hU0 : 0 ≤ U) (hU2 : A⁻¹ ≤ U) (hUt2 : A⁻¹ ≤ Ut)
    (hy : y = (1 - 2 * b) * vj + b * U ^ 2 * ζ + b ^ 2 * U ^ 2 * v₀ + b ^ 2 * U ^ 2 * v₁)
    (hyt : yt = (1 - 2 * b) * vbj + b * Ut ^ 2 * ζ + b ^ 2 * Ut ^ 2 * vb₀ + b ^ 2 * Ut ^ 2 * vb₁)
    (hyt1 : y₁ ≤ yt) (hyY : y ≤ Y) (hytY : yt ≤ Y) (hyb : yt - b * η ≤ yb) :
    (1 - 2 * b) * (Real.sqrt vj * Real.sqrt Vbj) + b ^ 2 * (U * Ut) *
        (Real.sqrt v₀ * Real.sqrt Vb₀ + Real.sqrt v₁ * Real.sqrt Vb₁) ≤
      (1 - b * ζ₀ / A ^ 2 / Y / 2) * (Real.sqrt y * Real.sqrt yb) := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hnn : ∀ {t : ℝ}, y₀ ≤ t → 0 ≤ t := fun h => hy₀.le.trans h
  have hζ0 : 0 < ζ := lt_of_lt_of_le hζ₀ hz
  have hUt0 : 0 ≤ Ut := (inv_nonneg.mpr hA0.le).trans hUt2
  have hy0 : 0 ≤ y := by
    rw [hy]; have := hnn hvj; have := hnn hv₀; have := hnn hv₁; positivity
  have hyt0 : 0 ≤ yt := hy₁0.le.trans hyt1
  have hω2 : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → (Real.sqrt p * Real.sqrt q) ^ 2 = p * q :=
    fun hp hq => by rw [mul_pow, Real.sq_sqrt hp, Real.sq_sqrt hq]
  set ωj := Real.sqrt vj * Real.sqrt vbj with hωj
  set ω₀ := Real.sqrt v₀ * Real.sqrt vb₀ with hω₀
  set ω₁ := Real.sqrt v₁ * Real.sqrt vb₁ with hω₁
  set γ := b ^ 2 * (U * Ut) with hγ
  set β := b * U * Ut * ζ with hβ
  have hγ0 : 0 ≤ γ := by positivity
  set L := (1 - 2 * b) * ωj + γ * (ω₀ + ω₁) with hL
  have hL0 : 0 ≤ L := by positivity
  have hCS : (L + β) ^ 2 ≤ y * yt := by
    have e1 : ((1 - 2 * b) * ωj) ^ 2 ≤ ((1 - 2 * b) * vj) * ((1 - 2 * b) * vbj) :=
      le_of_eq (by rw [mul_pow, hωj, hω2 (hnn hvj) (hnn hvbj)]; ring)
    have e2 : (b * U * Ut * ζ) ^ 2 ≤ (b * U ^ 2 * ζ) * (b * Ut ^ 2 * ζ) := le_of_eq (by ring)
    have e3 : (γ * ω₀) ^ 2 ≤ (b ^ 2 * U ^ 2 * v₀) * (b ^ 2 * Ut ^ 2 * vb₀) :=
      le_of_eq (by rw [mul_pow, hω₀, hω2 (hnn hv₀) (hnn hvb₀), hγ]; ring)
    have e4 : (γ * ω₁) ^ 2 ≤ (b ^ 2 * U ^ 2 * v₁) * (b ^ 2 * Ut ^ 2 * vb₁) :=
      le_of_eq (by rw [mul_pow, hω₁, hω2 (hnn hv₁) (hnn hvb₁), hγ]; ring)
    have p1 := hnn hvj; have p2 := hnn hvbj; have p3 := hnn hv₀; have p4 := hnn hvb₀
    have p5 := hnn hv₁; have p6 := hnn hvb₁
    have h12 := cmp_cs2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) e1 e2
    have h34 := cmp_cs2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) e3 e4
    have h1234 := cmp_cs2 (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) h12 h34
    rw [hy, hyt]
    calc (L + β) ^ 2 = ((1 - 2 * b) * ωj + b * U * Ut * ζ + (γ * ω₀ + γ * ω₁)) ^ 2 := by
          rw [hL, hβ]; ring
      _ ≤ _ := h1234
      _ = _ := by ring
  set G := Real.sqrt y * Real.sqrt yt with hG
  have hG0 : 0 ≤ G := by positivity
  have hG2 : G ^ 2 = y * yt := by rw [hG, mul_pow, Real.sq_sqrt hy0, Real.sq_sqrt hyt0]
  have hLG : L + β ≤ G := by
    have hPβ : 0 ≤ L + β := by positivity
    exact (pow_le_pow_iff_left₀ hPβ hG0 two_ne_zero).mp (hG2 ▸ hCS)
  have hGY : G ≤ Y := by
    have : G ^ 2 ≤ Y ^ 2 := by rw [hG2, sq]; exact mul_le_mul hyY hytY hyt0 hY0.le
    exact (pow_le_pow_iff_left₀ hG0 hY0.le two_ne_zero).mp this
  have hββ₀ : b * ζ₀ / A ^ 2 ≤ β := by
    rw [hβ]
    have h1 : A⁻¹ * A⁻¹ ≤ U * Ut := mul_le_mul hU2 hUt2 (by positivity) hU0
    have h2 : b * ζ₀ / A ^ 2 = b * (A⁻¹ * A⁻¹) * ζ₀ := by field_simp
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 hb0.le
    have h4 := mul_le_mul h3 hz (le_of_lt hζ₀) (by positivity)
    linarith
  have hεG : b * ζ₀ / A ^ 2 / Y * G ≤ β := by
    have h0 : 0 ≤ b * ζ₀ / A ^ 2 := by positivity
    have : b * ζ₀ / A ^ 2 / Y * G ≤ b * ζ₀ / A ^ 2 / Y * Y :=
      mul_le_mul_of_nonneg_left hGY (by positivity)
    rw [div_mul_cancel₀ _ hY0.ne'] at this
    linarith
  have hε1 : b * ζ₀ / A ^ 2 / Y ≤ 1 := by
    rw [div_le_one hY0]; linarith
  have hx0 : 0 ≤ η / y₀ := div_nonneg hη0 hy₀.le
  have hup : ∀ {v vb Vb : ℝ}, y₀ ≤ v → y₀ ≤ vb → Vb ≤ vb + η →
      Real.sqrt v * Real.sqrt Vb ≤ (1 + η / y₀) * (Real.sqrt v * Real.sqrt vb) :=
    fun {v vb Vb} hv hvb hVb => by
    have := mul_le_mul_of_nonneg_left (cmp_sqrt_up hy₀ hvb hη0 hVb) (Real.sqrt_nonneg v)
    linarith
  have hL' : (1 - 2 * b) * (Real.sqrt vj * Real.sqrt Vbj) + γ *
      (Real.sqrt v₀ * Real.sqrt Vb₀ + Real.sqrt v₁ * Real.sqrt Vb₁) ≤ (1 + η / y₀) * L := by
    have h1 := mul_le_mul_of_nonneg_left (hup hvj hvbj hVbj) hc0
    have h2 := mul_le_mul_of_nonneg_left (add_le_add (hup hv₀ hvb₀ hVb₀) (hup hv₁ hvb₁ hVb₁)) hγ0
    rw [hL]
    have e : (1 + η / y₀) * ((1 - 2 * b) * ωj + γ * (ω₀ + ω₁)) =
        (1 - 2 * b) * ((1 + η / y₀) * ωj) +
          γ * ((1 + η / y₀) * ω₀ + (1 + η / y₀) * ω₁) := by ring
    rw [e]; linarith
  have hκ : (1 - b * η / y₁) * G ≤ Real.sqrt y * Real.sqrt yb := by
    have := cmp_sqrt_down hy₁0 hyt1 (mul_nonneg hb0.le hη0) hθ1 hyb
    rw [hG]
    have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg y)
    linarith
  exact cmp_weight_margin hG0 hLG hεG hL' hκ hx0
    (div_nonneg (mul_nonneg hb0.le hη0) hy₁0.le) hsmall hε1

/-- **Common-port branch scalar step.** Exact `(m, u₀ = (z - b(m₀+m₁))⁻¹)`, approximate
`(m̄, ū₀ = (z - b(m̄₀+m̄₁))⁻¹ + r')`. With `γ = b² |u₀| |ũ₀|`: shift differences
`|σ_j - σ̄_j| ≤ c |m_j - m̄_j| + γ (|m₀ - m̄₀| + |m₁ - m̄₁|) + b η`, the weighted margin, and
`|ū₀ - u₀| ≤ b ζ₀⁻² (|m₀ - m̄₀| + |m₁ - m̄₁|) + η`. -/
theorem cmp_com_branch_scalar {b ζ₀ y₀ y₁ η A Y : ℝ} {z u₀ ub r' : ℂ} {m mb : Fin 2 → ℂ}
    {Vb : Fin 2 → ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3)
    (hy₀ : 0 < y₀) (hy₁ : y₁ = (1 - 2 * b) * y₀) (hη0 : 0 ≤ η)
    (hA : A = 4 + 2 / y₁) (hY : Y = 2 / y₁ + 1 / ζ₀ + 2)
    (hθ1 : b * η / y₁ ≤ 1)
    (hsmall : η / y₀ + b * η / y₁ ≤ b * ζ₀ / A ^ 2 / Y / 2)
    (hu : u₀ = (z - (b : ℂ) * (m 0 + m 1))⁻¹) (hub : ub = (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r')
    (hr' : ‖r'‖ ≤ η) (hv : ∀ j, y₀ ≤ -(m j).im) (hvb : ∀ j, y₀ ≤ -(mb j).im)
    (hm : ∀ j, ‖m j‖ ≤ 1 / y₁) (hmb : ∀ j, ‖mb j‖ ≤ 2 / y₁ + 1)
    (hVb : ∀ j, Vb j ≤ -(mb j).im + η) :
    (∀ j, ‖(((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀) -
        (((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub)‖ ≤
      (1 - 2 * b) * ‖m j - mb j‖ + b ^ 2 * (‖u₀‖ * ‖(z - (b : ℂ) * (mb 0 + mb 1))⁻¹‖) *
        (‖m 0 - mb 0‖ + ‖m 1 - mb 1‖) + b * η) ∧
    (∀ j, (1 - 2 * b) * (Real.sqrt (-(m j).im) * Real.sqrt (Vb j)) +
        b ^ 2 * (‖u₀‖ * ‖(z - (b : ℂ) * (mb 0 + mb 1))⁻¹‖) *
          (Real.sqrt (-(m 0).im) * Real.sqrt (Vb 0) + Real.sqrt (-(m 1).im) * Real.sqrt (Vb 1)) ≤
      (1 - b * ζ₀ / A ^ 2 / Y / 2) *
        (Real.sqrt (-(((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀).im) *
          Real.sqrt (-(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub).im))) ∧
    ‖ub - u₀‖ ≤ b * ζ₀⁻¹ ^ 2 * (‖m 0 - mb 0‖ + ‖m 1 - mb 1‖) + η := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hy₁0 : 0 < y₁ := by rw [hy₁]; exact mul_pos (by linarith) hy₀
  have hnn : ∀ {t : ℝ}, y₀ ≤ t → 0 ≤ t := fun h => hy₀.le.trans h
  have hqim : ∀ w₀ w₁ : ℂ, (z - (b : ℂ) * (w₀ + w₁)).im = z.im + b * ((-w₀.im) + (-w₁.im)) :=
    fun w₀ w₁ => by
    simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hqζ : ζ₀ ≤ (z - (b : ℂ) * (m 0 + m 1)).im := by
    rw [hqim]; have := mul_nonneg hb0.le (add_nonneg (hnn (hv 0)) (hnn (hv 1))); linarith
  have hqbζ : ζ₀ ≤ (z - (b : ℂ) * (mb 0 + mb 1)).im := by
    rw [hqim]; have := mul_nonneg hb0.le (add_nonneg (hnn (hvb 0)) (hnn (hvb 1))); linarith
  have h12 : 1 / y₁ ≤ 2 / y₁ := div_le_div_of_nonneg_right (by norm_num) hy₁0.le
  have hqA : ‖z - (b : ℂ) * (m 0 + m 1)‖ ≤ A := by
    rw [hA]
    have h1 := norm_sub_le z ((b : ℂ) * (m 0 + m 1))
    rw [cmp_norm_real_mul hb0.le] at h1
    have h2 := (norm_add_le (m 0) (m 1)).trans (add_le_add (hm 0) (hm 1))
    have h3 := mul_le_mul (show b ≤ 1 / 2 by linarith) h2 (norm_nonneg _) (by norm_num)
    have : 1 / 2 * (1 / y₁ + 1 / y₁) = 1 / y₁ := by ring
    linarith
  have hqbA : ‖z - (b : ℂ) * (mb 0 + mb 1)‖ ≤ A := by
    rw [hA]
    have h1 := norm_sub_le z ((b : ℂ) * (mb 0 + mb 1))
    rw [cmp_norm_real_mul hb0.le] at h1
    have h2 := (norm_add_le (mb 0) (mb 1)).trans (add_le_add (hmb 0) (hmb 1))
    have h3 := mul_le_mul (show b ≤ 1 / 2 by linarith) h2 (norm_nonneg _) (by norm_num)
    have : 1 / 2 * (2 / y₁ + 1 + (2 / y₁ + 1)) = 2 / y₁ + 1 := by ring
    linarith
  have hA0 : 0 < A := by rw [hA]; positivity
  have hq0 : z - (b : ℂ) * (m 0 + m 1) ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hqζ; linarith
  have hqb0 : z - (b : ℂ) * (mb 0 + mb 1) ≠ 0 := fun h => by
    rw [h, Complex.zero_im] at hqbζ; linarith
  have hU1 : ‖u₀‖ ≤ ζ₀⁻¹ := by rw [hu]; exact (cmp_inv_bounds hζ₀ hqζ hqA).1
  have hU2 : A⁻¹ ≤ ‖u₀‖ := by rw [hu]; exact (cmp_inv_bounds hζ₀ hqζ hqA).2
  have hUt1 := (cmp_inv_bounds hζ₀ hqbζ hqbA).1
  have hUt2 := (cmp_inv_bounds hζ₀ hqbζ hqbA).2
  have hw : -u₀.im = ‖u₀‖ ^ 2 * (z.im + b * ((-(m 0).im) + (-(m 1).im))) := by
    rw [hu, cmp_neg_im_inv, hqim]
  have hwt : -((z - (b : ℂ) * (mb 0 + mb 1))⁻¹).im =
      ‖(z - (b : ℂ) * (mb 0 + mb 1))⁻¹‖ ^ 2 * (z.im + b * ((-(mb 0).im) + (-(mb 1).im))) := by
    rw [cmp_neg_im_inv, hqim]
  have hsub : u₀ - (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ =
      (b : ℂ) * ((m 0 + m 1) - (mb 0 + mb 1)) * (u₀ * (z - (b : ℂ) * (mb 0 + mb 1))⁻¹) := by
    rw [hu]; exact cmp_port_sub hq0 hqb0
  set ut := (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ with hut
  set U := ‖u₀‖ with hUdef
  set Ut := ‖ut‖ with hUtdef
  have hU0 : 0 ≤ U := norm_nonneg _
  have hUt0 : 0 ≤ Ut := norm_nonneg _
  set E := ‖m 0 - mb 0‖ + ‖m 1 - mb 1‖ with hEdef
  have hsum : ‖(m 0 + m 1) - (mb 0 + mb 1)‖ ≤ E := by
    rw [show (m 0 + m 1) - (mb 0 + mb 1) = (m 0 - mb 0) + (m 1 - mb 1) by ring]
    exact norm_add_le _ _
  have hdiffu : ‖u₀ - ut‖ ≤ b * E * (U * Ut) := by
    rw [hsub, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have := mul_le_mul_of_nonneg_left hsum hb0.le
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩
  · have heq : (((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀) -
        (((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub) =
        ((1 - 2 * b : ℝ) : ℂ) * (m j - mb j) + (b : ℂ) * (u₀ - ut) - (b : ℂ) * r' := by
      rw [hub]; ring
    rw [heq]
    have h1 := norm_sub_le (((1 - 2 * b : ℝ) : ℂ) * (m j - mb j) + (b : ℂ) * (u₀ - ut))
      ((b : ℂ) * r')
    have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * (m j - mb j)) ((b : ℂ) * (u₀ - ut))
    rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
    rw [cmp_norm_real_mul hb0.le] at h1
    have h3 := mul_le_mul_of_nonneg_left hr' hb0.le
    have h4 := mul_le_mul_of_nonneg_left hdiffu hb0.le
    have e : b * (b * E * (U * Ut)) = b ^ 2 * (U * Ut) * E := by ring
    linarith
  · have hy : -(((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀).im =
        (1 - 2 * b) * (-(m j).im) + b * U ^ 2 * z.im + b ^ 2 * U ^ 2 * (-(m 0).im) +
          b ^ 2 * U ^ 2 * (-(m 1).im) := by
      rw [cmp_im_comb, hw]; ring
    have hyt : -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ut).im =
        (1 - 2 * b) * (-(mb j).im) + b * Ut ^ 2 * z.im + b ^ 2 * Ut ^ 2 * (-(mb 0).im) +
          b ^ 2 * Ut ^ 2 * (-(mb 1).im) := by
      rw [cmp_im_comb, hwt]; ring
    have hyb : -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ut).im - b * η ≤
        -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub).im := by
      have hrim : r'.im ≤ η := (le_abs_self r'.im).trans ((Complex.abs_im_le_norm r').trans hr')
      have key : -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub).im =
          -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ut).im - b * r'.im := by
        rw [cmp_im_comb, cmp_im_comb, hub, Complex.add_im]; ring
      rw [key]
      have := mul_le_mul_of_nonneg_left hrim hb0.le
      linarith
    have hyt1 : y₁ ≤ -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ut).im := by
      rw [hyt, hy₁]
      have := mul_le_mul_of_nonneg_left (hvb j) hc0
      have := hnn (hvb 0); have := hnn (hvb 1)
      have : 0 ≤ b * Ut ^ 2 * z.im := by have := hζ₀.le.trans hz; positivity
      have : 0 ≤ b ^ 2 * Ut ^ 2 * (-(mb 0).im) := by positivity
      have : 0 ≤ b ^ 2 * Ut ^ 2 * (-(mb 1).im) := by positivity
      linarith
    have hnormY : ∀ (w x : ℂ) (Kw Kx : ℝ), ‖w‖ ≤ Kw → ‖x‖ ≤ Kx →
        -(((1 - 2 * b : ℝ) : ℂ) * w + (b : ℂ) * x).im ≤ Kw + Kx := fun w x Kw Kx hw hx => by
      have h1 := (neg_le_abs _).trans (Complex.abs_im_le_norm
        (((1 - 2 * b : ℝ) : ℂ) * w + (b : ℂ) * x))
      have h2 := norm_add_le (((1 - 2 * b : ℝ) : ℂ) * w) ((b : ℂ) * x)
      rw [cmp_norm_real_mul hc0, cmp_norm_real_mul hb0.le] at h2
      have h3 := mul_le_mul (show 1 - 2 * b ≤ 1 by linarith) hw (norm_nonneg _) zero_le_one
      have h4 := mul_le_mul (show b ≤ 1 by linarith) hx (norm_nonneg _) zero_le_one
      linarith
    have hyY := hnormY (m j) u₀ _ _ (hm j) hU1
    have hytY := hnormY (mb j) ut _ _ (hmb j) hUt1
    have hY' : 1 / y₁ + ζ₀⁻¹ ≤ Y := by rw [hY, one_div ζ₀]; linarith
    have hY'' : 2 / y₁ + 1 + ζ₀⁻¹ ≤ Y := by rw [hY, one_div ζ₀]; linarith
    exact cmp_com_margin_real hb0 hb1 hζ₀ hz hy₀ hy₁0 hη0 hA0 (by rw [hY]; positivity) hθ1 hsmall
      (hv j) (hvb j) (hVb j) (hv 0) (hvb 0) (hVb 0) (hv 1) (hvb 1) (hVb 1) hU0 hU2 hUt2 hy hyt
      hyt1 (hyY.trans hY') (hytY.trans hY'') hyb
  · have heq : ub - u₀ = r' - (u₀ - ut) := by rw [hub]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    have h1 : U * Ut ≤ ζ₀⁻¹ * ζ₀⁻¹ := mul_le_mul hU1 hUt1 hUt0 (by positivity)
    have hE0 : 0 ≤ E := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hb0.le hE0)
    have e : b * E * (ζ₀⁻¹ * ζ₀⁻¹) = b * ζ₀⁻¹ ^ 2 * E := by ring
    linarith

/-- Imaginary-part bounds for the common-port shifts in the branch argument. -/
theorem cmp_com_branch_im {b ζ₀ y₀ η : ℝ} {z : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hη0 : 0 ≤ η) (hηy : η ≤ (1 - 2 * b) * y₀)
    {m mb : Fin 2 → ℂ} {u₀ ub r' : ℂ} (hu : u₀ = (z - (b : ℂ) * (m 0 + m 1))⁻¹)
    (hub : ub = (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r') (hr' : ‖r'‖ ≤ η)
    (hv : ∀ j, y₀ ≤ -(m j).im) (hvb : ∀ j, y₀ ≤ -(mb j).im) (hy₀ : 0 < y₀) (j : Fin 2) :
    (1 - 2 * b) * y₀ ≤ -(((1 - 2 * b : ℝ) : ℂ) * m j + (b : ℂ) * u₀).im ∧
      (1 - 2 * b) * y₀ / 2 ≤ -(((1 - 2 * b : ℝ) : ℂ) * mb j + (b : ℂ) * ub).im := by
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hqim : ∀ w₀ w₁ : ℂ, (z - (b : ℂ) * (w₀ + w₁)).im = z.im + b * ((-w₀.im) + (-w₁.im)) :=
    fun w₀ w₁ => by
    simp only [Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hwpos : ∀ w₀ w₁ : ℂ, 0 ≤ -w₀.im → 0 ≤ -w₁.im →
      0 ≤ -((z - (b : ℂ) * (w₀ + w₁))⁻¹).im := fun w₀ w₁ h0 h1 => by
    rw [cmp_neg_im_inv, hqim]
    have := mul_nonneg hb0.le (add_nonneg h0 h1)
    have : 0 < z.im := lt_of_lt_of_le hζ₀ hz
    positivity
  constructor
  · rw [cmp_im_comb, hu]
    have h1 := mul_nonneg hb0.le (hwpos (m 0) (m 1) ((hy₀.le).trans (hv 0))
      ((hy₀.le).trans (hv 1)))
    have h2 := mul_le_mul_of_nonneg_left (hv j) hc0
    linarith
  · rw [cmp_im_comb, hub, Complex.add_im]
    have h1 := mul_nonneg hb0.le (hwpos (mb 0) (mb 1) ((hy₀.le).trans (hvb 0))
      ((hy₀.le).trans (hvb 1)))
    have h2 : r'.im ≤ η := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hr')
    have h3 := mul_le_mul_of_nonneg_left (hvb j) hc0
    have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
    have h6 : b * η ≤ (1 - 2 * b) * y₀ / 2 := by
      have := mul_le_mul (show b ≤ 1 / 2 by linarith) hηy hη0 (by norm_num); linarith
    have e : b * -((z - (b : ℂ) * (mb 0 + mb 1))⁻¹.im + r'.im) =
        b * -((z - (b : ℂ) * (mb 0 + mb 1))⁻¹).im - b * r'.im := by ring
    rw [e]
    linarith

/-- **Branch identification, common port** ("replace `w_j` by `w₀`").
Setting of `cmp_sep_branch` with the common-port equations
(`m_i = tr_i[(H - diag(c m + b u₀))⁻¹]`, `u₀ = (z - b(m₀ + m₁))⁻¹`), exact `(m, u₀)` with
`-Im m_i ≥ y₀`, approximate `(m̄, ū₀)` with residuals `‖r‖, |r'| ≤ η ≤ η₀` and `-Im m̄_i ≥ y₀`:
`|m̄_i - m_i| ≤ C'' η` and `|ū₀ - u₀| ≤ C'' η`, `C'' = cmpComBranchC b ζ₀ y₀`. -/
theorem cmp_com_branch {W : ℕ} (H : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hH : H.IsHermitian) {b ζ₀ y₀ η : ℝ} {z : ℂ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hy₀ : 0 < y₀) (hη0 : 0 ≤ η)
    (hη : η ≤ cmpEta b ζ₀ y₀)
    (m : Fin 2 → ℂ) (u₀ : ℂ)
    (hsol : (∀ i, m i = blockTrace (cmpInv H (cmpComShift b m u₀)) i) ∧
      u₀ = (z - (b : ℂ) * (m 0 + m 1))⁻¹)
    (hv : ∀ i, y₀ ≤ -(m i).im)
    (mb r : Fin 2 → ℂ) (ub r' : ℂ)
    (happ : (∀ i, mb i = blockTrace (cmpInv H (cmpComShift b mb ub)) i + r i) ∧
      ub = (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r')
    (hr : ‖r‖ ≤ η) (hr' : ‖r'‖ ≤ η) (hvb : ∀ i, y₀ ≤ -(mb i).im) :
    (∀ i, ‖mb i - m i‖ ≤ cmpComBranchC b ζ₀ y₀ * η) ∧ ‖ub - u₀‖ ≤ cmpComBranchC b ζ₀ y₀ * η := by
  obtain ⟨hη1, hηy₁, hηy₀, hθ1, hsmall⟩ := cmpEta_props hb0 hb1 hy₀ hη0 hη
  have hy₁0 : 0 < (1 - 2 * b) * y₀ := mul_pos (by linarith) hy₀
  have hε0 := cmpEps_pos hb0 hb1 hζ₀ hy₀
  have him := cmp_com_branch_im hb0 hb1 hζ₀ hz hη0 hηy₁ hsol.2 happ.2 hr' hv hvb hy₀
  have hyσ : ∀ j, (1 - 2 * b) * y₀ ≤ -(cmpComShift b m u₀ j).im := fun j => (him j).1
  have hyσb : ∀ j, (1 - 2 * b) * y₀ / 2 ≤ -(cmpComShift b mb ub j).im := fun j => (him j).2
  have hy₂0 : 0 < (1 - 2 * b) * y₀ / 2 := by positivity
  have hσim : ∀ j, (cmpComShift b m u₀ j).im < 0 := fun j => by linarith [hyσ j]
  have hσbim : ∀ j, (cmpComShift b mb ub j).im < 0 := fun j => by linarith [hyσb j]
  have htrM : ∀ j, blockTrace (cmpInv H (cmpComShift b m u₀)) j = m j := fun j => (hsol.1 j).symm
  have hmb1 : ∀ j, ‖m j‖ ≤ 1 / ((1 - 2 * b) * y₀) := fun j => by
    rw [← htrM j, one_div]; exact cmp_trace_le H hH _ hy₁0 hyσ j
  have htrMb : ∀ j, ‖blockTrace (cmpInv H (cmpComShift b mb ub)) j‖ ≤ 2 / ((1 - 2 * b) * y₀) :=
    fun j => by
    have := cmp_trace_le H hH _ hy₂0 hyσb j
    rwa [inv_div] at this
  have hrj : ∀ j, ‖r j‖ ≤ η := fun j => (norm_le_pi_norm r j).trans hr
  have hmbb : ∀ j, ‖mb j‖ ≤ 2 / ((1 - 2 * b) * y₀) + 1 := fun j => by
    rw [happ.1 j]
    have := norm_add_le (blockTrace (cmpInv H (cmpComShift b mb ub)) j) (r j)
    linarith [htrMb j, hrj j]
  have hVb : ∀ j, -(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im = -(mb j).im + (r j).im :=
    fun j => by
    have e : blockTrace (cmpInv H (cmpComShift b mb ub)) j = mb j - r j := by
      rw [happ.1 j]; ring
    rw [e, Complex.sub_im]; ring
  have hrim : ∀ j, |(r j).im| ≤ η := fun j => (Complex.abs_im_le_norm _).trans (hrj j)
  have hVbup : ∀ j, -(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im ≤ -(mb j).im + η :=
    fun j => by rw [hVb j]; linarith [le_abs_self (r j).im, hrim j]
  have hVblo : ∀ j, y₀ / 2 ≤ -(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im :=
    fun j => by rw [hVb j]; linarith [neg_abs_le (r j).im, hrim j, hvb j]
  have hVbhi : ∀ j, -(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im ≤
      2 / ((1 - 2 * b) * y₀) := fun j =>
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (htrMb j))
  obtain ⟨hsa, hsb, hsd⟩ := cmp_com_branch_scalar
    (Vb := fun j => -(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im)
    hb0 hb1 hζ₀ hz hz3 hy₀ rfl hη0 rfl rfl hθ1 hsmall hsol.2 happ.2 hr' hv hvb hmb1 hmbb hVbup
  have hsqrt_lo : ∀ {p q ℓ : ℝ}, 0 ≤ ℓ → 0 ≤ p → ℓ ^ 2 ≤ p * q →
      ℓ ≤ Real.sqrt p * Real.sqrt q := fun {p q ℓ} hℓ hp h => by
    calc ℓ = Real.sqrt (ℓ ^ 2) := (Real.sqrt_sq hℓ).symm
      _ ≤ Real.sqrt (p * q) := Real.sqrt_le_sqrt h
      _ = Real.sqrt p * Real.sqrt q := Real.sqrt_mul hp _
  have hsqrt_hi : ∀ {p q ℓ : ℝ}, 0 ≤ ℓ → 0 ≤ p → p * q ≤ ℓ ^ 2 →
      Real.sqrt p * Real.sqrt q ≤ ℓ := fun {p q ℓ} hℓ hp h => by
    calc Real.sqrt p * Real.sqrt q = Real.sqrt (p * q) := (Real.sqrt_mul hp _).symm
      _ ≤ Real.sqrt (ℓ ^ 2) := Real.sqrt_le_sqrt h
      _ = ℓ := Real.sqrt_sq hℓ
  have hωlo : ∀ j, y₀ / 2 ≤ Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im) := fun j => by
    refine hsqrt_lo (by linarith) ((hy₀.le).trans (hv j)) ?_
    have := mul_le_mul (hv j) (hVblo j) (by linarith) ((hy₀.le).trans (hv j))
    have : (y₀ / 2) ^ 2 ≤ y₀ * (y₀ / 2) := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hωhi : ∀ j, Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im) ≤
        2 / ((1 - 2 * b) * y₀) := fun j => by
    have hv0 : 0 ≤ -(m j).im := (hy₀.le).trans (hv j)
    refine hsqrt_hi (by positivity) hv0 ?_
    have h1 : -(m j).im ≤ 1 / ((1 - 2 * b) * y₀) :=
      (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (hmb1 j))
    have h2 := mul_le_mul h1 (hVbhi j) ((by linarith [hVblo j])) (by positivity)
    have h3 : 1 / ((1 - 2 * b) * y₀) * (2 / ((1 - 2 * b) * y₀)) ≤
        (2 / ((1 - 2 * b) * y₀)) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num)
        hy₁0.le) (by positivity)
    linarith
  have hκlo : ∀ j, (1 - 2 * b) * y₀ / 2 ≤ Real.sqrt (-(cmpComShift b m u₀ j).im) *
      Real.sqrt (-(cmpComShift b mb ub j).im) := fun j => by
    refine hsqrt_lo hy₂0.le (by linarith [hyσ j]) ?_
    have := mul_le_mul (show (1 - 2 * b) * y₀ / 2 ≤ -(cmpComShift b m u₀ j).im by
      linarith [hyσ j]) (hyσb j) hy₂0.le (by linarith [hyσ j])
    rw [sq]; exact this
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, x = b ^ 2 * (‖u₀‖ * ‖(z - (b : ℂ) * (mb 0 + mb 1))⁻¹‖) := ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  have hsumΓ : ∀ (j : Fin 2) (f : Fin 2 → ℝ),
      ∑ k, ((if j = k then 1 - 2 * b else 0) + γ) * f k =
        (1 - 2 * b) * f j + γ * (f 0 + f 1) := fun j f => by
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp <;> ring
  have hε2 : cmpEps b ζ₀ y₀ ≤ 2 := by
    have h := hsb 0
    by_contra hcon
    push Not at hcon
    have hneg : 1 - cmpEps b ζ₀ y₀ / 2 < 0 := by linarith
    have hκ0 := lt_of_lt_of_le hy₂0 (hκlo 0)
    have hP0 : 0 ≤ (1 - 2 * b) * (Real.sqrt (-(m 0).im) *
        Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) 0).im)) +
        b ^ 2 * (‖u₀‖ * ‖(z - (b : ℂ) * (mb 0 + mb 1))⁻¹‖) *
          (Real.sqrt (-(m 0).im) * Real.sqrt (-(blockTrace (cmpInv H
            (cmpComShift b mb ub)) 0).im) + Real.sqrt (-(m 1).im) *
            Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) 1).im)) := by
      positivity
    have := mul_neg_of_neg_of_pos hneg hκ0
    unfold cmpEps at hneg this
    unfold cmpComShift at this hκ0
    linarith
  have hdj : ∀ j, ‖cmpComShift b m u₀ j - cmpComShift b mb ub j‖ ≤
      ∑ k, ((if j = k then 1 - 2 * b else 0) + γ) * ‖m k - mb k‖ + b * η := fun j => by
    rw [hsumΓ, hγ]; exact hsa j
  have hΓω : ∀ j, ∑ k, ((if j = k then 1 - 2 * b else 0) + γ) * (Real.sqrt (-(m k).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) k).im)) ≤
        (1 - cmpEps b ζ₀ y₀ / 2) * (Real.sqrt (-(cmpComShift b m u₀ j).im) *
          Real.sqrt (-(cmpComShift b mb ub j).im)) := fun j => by
    rw [hsumΓ, hγ]; exact hsb j
  have hclose := fun i => cmp_branch_close (e := fun j => ‖m j - mb j‖)
    (ω := fun j => Real.sqrt (-(m j).im) *
      Real.sqrt (-(blockTrace (cmpInv H (cmpComShift b mb ub)) j).im))
    (κ := fun j => Real.sqrt (-(cmpComShift b m u₀ j).im) *
      Real.sqrt (-(cmpComShift b mb ub j).im))
    (d := fun j => ‖cmpComShift b m u₀ j - cmpComShift b mb ub j‖)
    (Γ := fun j k => (if j = k then 1 - 2 * b else 0) + γ)
    (b := b) (η := η) hε0 hε2 hb0.le hη0 (by linarith : (0 : ℝ) < y₀ / 2) hy₂0
    (fun j => norm_nonneg _) hωlo hωhi hκlo
    (fun j k => by
      show 0 ≤ (if j = k then 1 - 2 * b else 0) + γ
      split_ifs
      · linarith
      · linarith)
    hdj hΓω
    (fun S hS hδ k => cmp_branch_trace_step H hH _ _ m mb r hσim hσbim htrM
      happ.1 hr S hS hδ k) i
  have e1 : b / ((1 - 2 * b) * y₀ / 2) + 1 / (y₀ / 2) = 2 * b / ((1 - 2 * b) * y₀) + 2 / y₀ := by
    field_simp
  obtain ⟨E, hE⟩ : ∃ x : ℝ, x = 2 / ((1 - 2 * b) * y₀) * (2 / cmpEps b ζ₀ y₀ *
      ((2 * b / ((1 - 2 * b) * y₀) + 2 / y₀) * η)) := ⟨_, rfl⟩
  have hclose' : ∀ i, ‖m i - mb i‖ ≤ E := fun i => by
    have := hclose i; rw [e1, ← hE] at this; exact this
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hclose' 0)
  have hC : cmpComBranchC b ζ₀ y₀ * η = (1 + 2 * b * ζ₀⁻¹ ^ 2) * E + η := by
    rw [hE, cmpComBranchC, cmpBranchC]; ring
  have hk : 0 ≤ b * ζ₀⁻¹ ^ 2 := by positivity
  refine ⟨fun i => ?_, ?_⟩
  · rw [norm_sub_rev, hC]
    have := hclose' i
    have h3 : 0 ≤ 2 * b * ζ₀⁻¹ ^ 2 * E := by positivity
    have : E ≤ (1 + 2 * b * ζ₀⁻¹ ^ 2) * E := by nlinarith
    linarith
  · rw [hC]
    have h1 := mul_le_mul_of_nonneg_left (add_le_add (hclose' 0) (hclose' 1)) hk
    have e2 : b * ζ₀⁻¹ ^ 2 * (E + E) = 2 * b * ζ₀⁻¹ ^ 2 * E := by ring
    have : ‖ub - u₀‖ ≤ b * ζ₀⁻¹ ^ 2 * (‖m 0 - mb 0‖ + ‖m 1 - mb 1‖) + η := hsd
    nlinarith

/-!
## 9. The combined deterministic comparison statement
-/

/-- **Deterministic part of `LayerComparisonContract`, with the branch clause**.
`b ∈ (0, 1/2)`, `κ > 0` and a lower bound `y₀ > 0` first; then `d_* > 0`, `C`,
`η₀ > 0`, `C''`; uniformly in `W ≥ 1`, Hermitian two-port `X` and `E ∈ bulkInterval κ` with
`d(X) ≤ d_*`:
* separate ports: a solution `(m, u)` of the two-port Dyson equation with `Im m_i, Im u_i < 0` and
  `|m_i - a| + |u_i - a| ≤ C d(X)`; every `(m̄, ū)` solving the equations up to residuals
  `‖r‖, ‖r'‖ ≤ η ≤ η₀` with `-Im m̄_i ≥ y₀` satisfies `|m̄_i - m_i| + |ū_i - u_i| ≤ C'' η`;
* common port: a solution `(m, u₀)` with `Im m_i, Im u₀ < 0`, `|m_i - a|, |u₀ - a| ≤ C d(X)`;
  every approximate `(m̄, ū₀)` (residuals `≤ η ≤ η₀`, `-Im m̄_i ≥ y₀`) satisfies
  `|m̄_i - m_i|, |ū₀ - u₀| ≤ C'' η`.
Applied to the layer means with `η = C W⁻²` (residual bound of the conditional mean
equations, the trace–matrix lemma) and the lower bound `y₀` on `-Im` of the top layer means,
this gives the `C W⁻²` clauses of `LayerComparisonContract` for `W ≥ W₀`. -/
theorem cmp_comparison_deterministic : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ y₀ : ℝ, 0 < y₀ →
    ∃ dstar C η₀ C'' : ℝ, 0 < dstar ∧ 0 < η₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        (∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, (m i).im < 0 ∧ (u i).im < 0) ∧
          (∀ i, ‖m i - matchedA E‖ + ‖u i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ∀ (η : ℝ) (mb ub r r' : Fin 2 → ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, y₀ ≤ -(mb i).im) →
            (∀ i, mb i = blockTrace (twoPortTop b E X mb ub)⁻¹ i + r i ∧
              ub i = (boundaryZ b E - (b : ℂ) * mb i)⁻¹ + r' i) →
            ∀ i, ‖mb i - m i‖ + ‖ub i - u i‖ ≤ C'' * η) ∧
        (∃ (m : Fin 2 → ℂ) (u₀ : ℂ), IsCommonPortSolution b E X m u₀ ∧
          (∀ i, (m i).im < 0) ∧ u₀.im < 0 ∧
          (∀ i, ‖m i - matchedA E‖ ≤ C * matchedDistance b E X) ∧
          ‖u₀ - matchedA E‖ ≤ C * matchedDistance b E X ∧
          ∀ (η : ℝ) (mb r : Fin 2 → ℂ) (ub r' : ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, y₀ ≤ -(mb i).im) →
            ((∀ i, mb i = blockTrace (commonPortTop b E X mb ub)⁻¹ i + r i) ∧
              ub = (commonZ b E - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r') →
            (∀ i, ‖mb i - m i‖ ≤ C'' * η) ∧ ‖ub - u₀‖ ≤ C'' * η) := by
  intro b hb0 hb1 κ hκ y₀ hy₀
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  obtain ⟨ds, Cs, qs, ρs, CBs, hds0, hCs0, -, -, -, -, hsep⟩ := cmp_twoPort_stable b hb0 hb1 κ hκ
  obtain ⟨dc, Cc, ρc, CBc, hdc0, hCc0, -, -, hcom⟩ := cmp_commonPort_stable b hb0 hb1 κ hκ
  have hc : 0 < 1 - 2 * b := by linarith
  obtain ⟨y₀', hy₀'⟩ : ∃ x : ℝ, x = min y₀ (α₀ / 2) := ⟨_, rfl⟩
  have hy₀'0 : 0 < y₀' := hy₀' ▸ lt_min hy₀ (by linarith)
  have hy₀'1 : y₀' ≤ y₀ := hy₀' ▸ min_le_left _ _
  have hy₀'2 : y₀' ≤ α₀ / 2 := hy₀' ▸ min_le_right _ _
  obtain ⟨ζ₀, hζ₀⟩ : ∃ x : ℝ, x = (1 - 2 * b) * α₀ := ⟨_, rfl⟩
  have hζ₀0 : 0 < ζ₀ := hζ₀ ▸ mul_pos hc hα₀
  have hK : 0 < 2 * (Cs + Cc + 1) := by linarith
  refine ⟨min (min ds dc) (α₀ / (2 * (Cs + Cc + 1))), Cs + Cc, cmpEta b ζ₀ y₀',
    cmpBranchC b ζ₀ y₀', lt_min (lt_min hds0 hdc0) (div_pos hα₀ hK),
    cmpEta_pos hb0 hb1 hζ₀0 hy₀'0, ?_⟩
  intro W hW X hX E hE hd
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hds : matchedDistance b E X ≤ ds := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hdc : matchedDistance b E X ≤ dc := hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hdα : matchedDistance b E X ≤ α₀ / (2 * (Cs + Cc + 1)) := hd.trans (min_le_right _ _)
  have hCd : (Cs + Cc + 1) * matchedDistance b E X ≤ α₀ / 2 := by
    rw [le_div_iff₀ hK] at hdα
    linarith
  have hCsd : Cs * matchedDistance b E X ≤ α₀ / 2 := by
    have := mul_nonneg hCc0 hd0; nlinarith
  have hCcd : Cc * matchedDistance b E X ≤ α₀ / 2 := by
    have := mul_nonneg hCs0 hd0; nlinarith
  have hlow : ∀ w : ℂ, ‖w - matchedA E‖ ≤ α₀ / 2 → y₀' ≤ -w.im := fun w hw => by
    have := Complex.im_le_norm (w - matchedA E)
    rw [Complex.sub_im] at this
    linarith
  have hH := cmpTopH_isHermitian E hX
  have hEabs' := hEabs.le
  have hzs : ζ₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs', hζ₀]
    have := mul_le_mul_of_nonneg_left haim (show 0 ≤ 1 - b by linarith)
    nlinarith
  have hzc : ζ₀ ≤ (commonZ b E).im := by
    rw [commonZ_im hEabs', hζ₀]
    have := mul_le_mul_of_nonneg_left haim hc.le
    nlinarith
  have hzs3 := norm_boundaryZ_le hb0.le (by linarith) hEabs'
  have hzc3 := norm_commonZ_le hb0.le (by linarith) hEabs'
  constructor
  · obtain ⟨m, u, hsol, him, hclose, -, -⟩ := hsep W hW X hX E hE hds
    refine ⟨m, u, hsol, him, fun i => (hclose i).trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right (by linarith) hd0
    intro η mb ub r r' hη0 hη hr hr' hvb happ i
    have hv : ∀ i, y₀' ≤ -(m i).im := fun i => hlow _ (by
      have := hclose i; have := norm_nonneg (u i - matchedA E); linarith)
    exact cmp_sep_branch (cmpTopH E X) hH hb0 hb1 hζ₀0 hzs hzs3 hy₀'0 hη0 hη m u hsol hv
      mb ub r r' happ hr hr' (fun i => hy₀'1.trans (hvb i)) i
  · obtain ⟨m, u₀, hsol, him, hu₀im, hclose, hcloseu, -⟩ := hcom W hW X hX E hE hdc
    refine ⟨m, u₀, hsol, him, hu₀im, fun i => (hclose i).trans ?_, hcloseu.trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right (by linarith) hd0
    · exact mul_le_mul_of_nonneg_right (by linarith) hd0
    intro η mb r ub r' hη0 hη hr hr' hvb happ
    have hv : ∀ i, y₀' ≤ -(m i).im := fun i => hlow _ (by have := hclose i; linarith)
    have h := cmp_com_branch (cmpTopH E X) hH hb0 hb1 hζ₀0 hzc hzc3 hy₀'0 hη0 hη m u₀ hsol hv
      mb r ub r' happ hr hr' (fun i => hy₀'1.trans (hvb i))
    exact h

end BlockBand.Layers
