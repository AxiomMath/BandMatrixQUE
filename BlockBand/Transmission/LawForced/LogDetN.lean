module

public import BlockBand.Transmission.LawForced.LayerScalar
public import BlockBand.Transmission.Generator.Basic

/-!
# Second-order expansion of `log det(I + N)` for Hermitian `N ⪰ (c − 1)I`

* `det_one_add_smul_eq_prod`: `det(I + wH) = Π_k (1 + wλ_k(H))` for Hermitian `H`;
* `sum_log_eq_log_det`: `Σ_k log(1 + wλ_k(H)) = log Re det(I + wH)` when every `1 + wλ_k > 0`;
* **`abs_logDet_sub_le`**: for Hermitian `N` with eigenvalues `≥ c − 1` (`0 < c ≤ 1`),
  `|log Re det(I+N) − Re Tr N + Re Tr N²/2| ≤ (9/c)·√(Re Tr N²)·Re Tr N²`, i.e. `≤ 9‖N‖³_HS/c`.

No power series in `N` is used, so the bound is global (it is applied at `N = wR^{1/2}BR^{1/2}`
for every `w ≥ 0`, including `w ≥ 1`, and at `w = −y`, `y < 1`; `LogDetSand`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `det(I + wH) = Π_k (1 + wλ_k)` for Hermitian `H`. -/
theorem det_one_add_smul_eq_prod {H : Matrix n n ℂ} (hH : H.IsHermitian) (w : ℝ) :
    (1 + (w : ℂ) • H).det = ∏ k, ((1 + w * hH.eigenvalues k : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs : H = U * diagonal (fun k => (hH.eigenvalues k : ℂ)) * star U := hH.spectral_theorem
  have h1 : 1 + (w : ℂ) • H =
      U * diagonal (fun k => ((1 + w * hH.eigenvalues k : ℝ) : ℂ)) * star U := by
    have hd : diagonal (fun k => ((1 + w * hH.eigenvalues k : ℝ) : ℂ)) =
        1 + (w : ℂ) • diagonal (fun k => (hH.eigenvalues k : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
    rw [hd, mul_add, add_mul, mul_one, hUU, mul_smul_comm, smul_mul_assoc, ← hs]
  rw [h1, det_mul, det_mul, mul_right_comm, ← det_mul, hUU, det_one, one_mul, det_diagonal]

/-- `Σ_k log(1 + wλ_k) = log Re det(I + wH)` when every `1 + wλ_k > 0`. -/
theorem sum_log_eq_log_det {H : Matrix n n ℂ} (hH : H.IsHermitian) (w : ℝ)
    (hpos : ∀ k, 0 < 1 + w * hH.eigenvalues k) :
    ∑ k, Real.log (1 + w * hH.eigenvalues k) = Real.log (1 + (w : ℂ) • H).det.re := by
  rw [det_one_add_smul_eq_prod hH w, ← Complex.ofReal_prod, Complex.ofReal_re,
    Real.log_prod fun k _ => (hpos k).ne']

/-- **Global second-order expansion of `log det(I + N)`.** -/
theorem abs_logDet_sub_le {N : Matrix n n ℂ} (hN : N.IsHermitian) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) (hlow : ∀ k, c - 1 ≤ hN.eigenvalues k) :
    |Real.log (1 + N).det.re - N.trace.re + (N ^ 2).trace.re / 2| ≤
      9 / c * (Real.sqrt (N ^ 2).trace.re * (N ^ 2).trace.re) := by
  set ν := hN.eigenvalues
  have hpos : ∀ k, 0 < 1 + 1 * ν k := fun k => by linarith [hlow k]
  have hdet : Real.log (1 + N).det.re = ∑ k, Real.log (1 + ν k) := by
    have := sum_log_eq_log_det hN 1 hpos
    simp only [one_mul, Complex.ofReal_one, one_smul] at this
    exact this.symm
  have htr : N.trace.re = ∑ k, ν k := by
    have := Generator.trace_pow_re_eq hN 1
    simpa using this
  have hsq : (N ^ 2).trace.re = ∑ k, ν k ^ 2 := Generator.trace_pow_re_eq hN 2
  have hk : ∀ k, |ν k| ≤ Real.sqrt (∑ k, ν k ^ 2) := fun k => by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun k => ν k ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ k))
  rw [hdet, htr, hsq, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, Finset.mul_sum]
  have hS0 : 0 ≤ Real.sqrt (∑ k, ν k ^ 2) := Real.sqrt_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have h := abs_log_one_add_sub_le hc0 hc1 (hlow k)
  have h3 : |ν k| ^ 3 ≤ Real.sqrt (∑ k, ν k ^ 2) * ν k ^ 2 := by
    rw [pow_succ, ← sq_abs (ν k), mul_comm]
    exact mul_le_mul_of_nonneg_right (hk k) (sq_nonneg _)
  calc |Real.log (1 + ν k) - ν k + ν k ^ 2 / 2| ≤ 9 * |ν k| ^ 3 / c := by
        simpa [sub_add_eq_add_sub] using h
    _ ≤ 9 / c * (Real.sqrt (∑ k, ν k ^ 2) * ν k ^ 2) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by nlinarith) hc0.le

end BlockBand.Transmission.LawForced
