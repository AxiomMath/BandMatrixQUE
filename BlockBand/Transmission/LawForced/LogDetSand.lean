module

public import BlockBand.Transmission.LawForced.LogDetN
public import BlockBand.Transmission.Generator.PowerExpand

/-!
# `log det(I + wS)` expanded about a diagonal `D`, every admissible `w`

Let `D = diag(t)` (real `t`), `w` with `1 + wt_k > 0`, `R = diag((1+wt_k)⁻¹)`,
`R^{1/2} = diag((1+wt_k)^{-1/2})` (`rhalf`), `B = S − D` and `N = wR^{1/2}BR^{1/2}` (`nSand`).
* `one_add_nSand`: `I + N = R^{1/2}(I + wS)R^{1/2}` (exact);
* `trace_nSand`, `trace_nSand_sq`: `Tr N = w Tr(RB)`, `Tr N² = w² Tr(RBRB)`;
* `re_trace_sq_eq_frobSq`, `frobSq_nSand_le`: `Re Tr N² = ‖N‖²_HS ≤ w²ρ²‖B‖²_HS` (`ρ ≥ (1+wt_k)⁻¹`);

These give, in the sibling module, **`logDet_sand_expand`**: if moreover `S` is Hermitian,
`I + wS − c₀I ⪰ 0` and `m ≤ (1+wt_k)⁻¹`, `0 < c₀m ≤ 1`, then
```
|log Re det(I+wS) − Σ_k log(1+wt_k) − w Re Tr(RB) + (w²/2) Re Tr(RBRB)|
    ≤ 9/(c₀m) · √(w²ρ²‖B‖²_HS) · w²ρ²‖B‖²_HS.
```
Uses: `w = x ≥ 0` with `S ⪰ 0` (`c₀ = 1`, `m = 1/(1+x)`), and `w = −y`, `0 ≤ y < 1`, with `S ⪯ I`
(`c₀ = 1 − y`, `m = 1`); `ρ = 1` resp. `(1−y)⁻¹`. With `S = sand T (LL*)` and `D = diag t`
(the `ae_trace_pow_fresh` representation, `‖S‖ ≤ 1` a.s. by `ae_norm_sand_freshU_le`), the
remainder is `O(‖B‖³_HS)` and `E‖B‖³_HS = O((g+1)³W^{-3/2})` (as in `hs_moments_bulk`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix
open scoped ComplexOrder ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `R^{1/2} = diag((1+wt_k)^{-1/2})`. -/
def rhalf (w : ℝ) (t : n → ℝ) : Matrix n n ℂ :=
  diagonal fun k => ((Real.sqrt (1 + w * t k)⁻¹ : ℝ) : ℂ)

/-- `R = diag((1+wt_k)⁻¹)`. -/
def rres (w : ℝ) (t : n → ℝ) : Matrix n n ℂ := diagonal fun k => (((1 + w * t k)⁻¹ : ℝ) : ℂ)

/-- `D = diag(t)`. -/
def dmat (t : n → ℝ) : Matrix n n ℂ := diagonal fun k => ((t k : ℝ) : ℂ)

/-- `N = wR^{1/2}(S − D)R^{1/2}`. -/
def nSand (w : ℝ) (t : n → ℝ) (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (w : ℂ) • (rhalf w t * (S - dmat t) * rhalf w t)

variable {w : ℝ} {t : n → ℝ}

theorem rhalf_mul_rhalf (hd : ∀ k, 0 < 1 + w * t k) : rhalf w t * rhalf w t = rres w t := by
  rw [rhalf, rres, diagonal_mul_diagonal]
  congr 1; funext k
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (inv_nonneg.2 (hd k).le)]

theorem rhalf_one_add_rhalf (hd : ∀ k, 0 < 1 + w * t k) :
    rhalf w t * (1 + (w : ℂ) • dmat t) * rhalf w t = 1 := by
  have h : 1 + (w : ℂ) • dmat t = diagonal fun k => ((1 + w * t k : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [dmat]
    · simp [dmat, diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [h, rhalf, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext k
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_right_comm,
    Real.mul_self_sqrt (inv_nonneg.2 (hd k).le), inv_mul_cancel₀ (hd k).ne', Complex.ofReal_one]

theorem one_add_nSand (hd : ∀ k, 0 < 1 + w * t k) (S : Matrix n n ℂ) :
    1 + nSand w t S = rhalf w t * (1 + (w : ℂ) • S) * rhalf w t := by
  have hS : 1 + (w : ℂ) • S = (1 + (w : ℂ) • dmat t) + (w : ℂ) • (S - dmat t) := by
    rw [smul_sub]; abel
  rw [hS, mul_add, add_mul, rhalf_one_add_rhalf hd, nSand, mul_smul_comm, smul_mul_assoc]

theorem det_rhalf_sq (hd : ∀ k, 0 < 1 + w * t k) :
    (rhalf w t).det * (rhalf w t).det = ∏ k, (((1 + w * t k)⁻¹ : ℝ) : ℂ) := by
  rw [← det_mul, rhalf_mul_rhalf hd, rres, det_diagonal]

/-- `log Re det(I + N) = log Re det(I + wS) − Σ_k log(1 + wt_k)` when `Re det(I + wS) > 0`. -/
theorem log_det_one_add_nSand (hd : ∀ k, 0 < 1 + w * t k) (S : Matrix n n ℂ)
    (hpos : 0 < (1 + (w : ℂ) • S).det.re) :
    Real.log (1 + nSand w t S).det.re =
      Real.log (1 + (w : ℂ) • S).det.re - ∑ k, Real.log (1 + w * t k) := by
  have hdet : (1 + nSand w t S).det =
      (1 + (w : ℂ) • S).det * ∏ k, (((1 + w * t k)⁻¹ : ℝ) : ℂ) := by
    rw [one_add_nSand hd, det_mul, det_mul, mul_right_comm, det_rhalf_sq hd, mul_comm]
  have hre : (1 + nSand w t S).det.re =
      (1 + (w : ℂ) • S).det.re * ∏ k, (1 + w * t k)⁻¹ := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_mul_ofReal]
  rw [hre, Real.log_mul hpos.ne' (Finset.prod_ne_zero_iff.2 fun k _ =>
      (inv_pos.2 (hd k)).ne'), Real.log_prod fun k _ => (inv_pos.2 (hd k)).ne', sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_inv _

theorem trace_nSand (hd : ∀ k, 0 < 1 + w * t k) (S : Matrix n n ℂ) :
    (nSand w t S).trace = (w : ℂ) * (rres w t * (S - dmat t)).trace := by
  rw [nSand, trace_smul, smul_eq_mul, trace_mul_comm, ← Matrix.mul_assoc, rhalf_mul_rhalf hd]

theorem trace_nSand_sq (hd : ∀ k, 0 < 1 + w * t k) (S : Matrix n n ℂ) :
    (nSand w t S ^ 2).trace =
      (w : ℂ) ^ 2 * (rres w t * (S - dmat t) * rres w t * (S - dmat t)).trace := by
  set h := rhalf w t
  set B := S - dmat t
  have e : nSand w t S ^ 2 = (w : ℂ) ^ 2 • (h * B * (h * h) * B * h) := by
    rw [nSand, sq, smul_mul_smul_comm, ← sq]; simp only [Matrix.mul_assoc]; rfl
  rw [e, trace_smul, smul_eq_mul, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, rhalf_mul_rhalf hd,
    Matrix.mul_assoc (rres w t * B) h h, rhalf_mul_rhalf hd]

/-- `Re Tr N² = ‖N‖²_HS` for Hermitian `N`. -/
theorem re_trace_sq_eq_frobSq {N : Matrix n n ℂ} (hN : N.IsHermitian) :
    (N ^ 2).trace.re = Generator.frobSq N := by
  rw [sq, Matrix.trace, Generator.frobSq, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hN.apply j i, Complex.star_def, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

theorem frobSq_nSand_le {ρ : ℝ} (hd : ∀ k, 0 < 1 + w * t k) (hρ : ∀ k, (1 + w * t k)⁻¹ ≤ ρ)
    (S : Matrix n n ℂ) :
    Generator.frobSq (nSand w t S) ≤ w ^ 2 * ρ ^ 2 * Generator.frobSq (S - dmat t) := by
  unfold Generator.frobSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hs : ∀ k, Real.sqrt (1 + w * t k)⁻¹ ^ 2 = (1 + w * t k)⁻¹ := fun k =>
    Real.sq_sqrt (inv_nonneg.2 (hd k).le)
  have hρ0 : 0 ≤ ρ := (inv_nonneg.2 (hd i).le).trans (hρ i)
  have e : nSand w t S i j = (w : ℂ) * (((Real.sqrt (1 + w * t i)⁻¹ *
      Real.sqrt (1 + w * t j)⁻¹ : ℝ) : ℂ) * (S - dmat t) i j) := by
    simp only [nSand, rhalf, Matrix.smul_apply, smul_eq_mul, mul_diagonal, diagonal_mul,
      Complex.ofReal_mul]
    ring
  have hn : ‖nSand w t S i j‖ ^ 2 =
      w ^ 2 * ((1 + w * t i)⁻¹ * (1 + w * t j)⁻¹) * ‖(S - dmat t) i j‖ ^ 2 := by
    rw [e, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, mul_pow, sq_abs, hs, hs]
    ring
  rw [hn]
  have h1 : (1 + w * t i)⁻¹ * (1 + w * t j)⁻¹ ≤ ρ ^ 2 := by
    rw [sq]; exact mul_le_mul (hρ i) (hρ j) (inv_nonneg.2 (hd j).le) hρ0
  have h2 : 0 ≤ ‖(S - dmat t) i j‖ ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg w, mul_le_mul_of_nonneg_left h1 (sq_nonneg w)]

end BlockBand.Transmission.LawForced
