module

public import BlockBand.Transmission.FractionalBulk.Spectral
public import BlockBand.Transmission.Generator.Basic

/-!
# Fractional-trace interpolation between `Tr T` and `Tr T^{q/2}`

The paper uses `E P_q ≤ (E g)^{(q-p)/(1-p)}(E P_p)^{(1-q)/(1-p)}` for `p < q`. Here `p = q/2`, so
`θ = (q-p)/(1-p) = q/(2-q)`, and `θ + p(1-θ) = q`. To avoid Hölder in `L^r`, the bound is
written linearly: for `A, B > 0`,
`Tr T^q ≤ A^θ B^{1-θ} (θ Tr T / A + (1-θ) Tr T^{q/2} / B)`.
It follows eigenvalue by eigenvalue from weighted AM–GM (`Real.geom_mean_le_arith_mean2_weighted`).
Taking expectations with `E Tr T ≤ A` and `E Tr T^{q/2} ≤ B` gives `E Tr T^q ≤ A^θ B^{1-θ}`.

* `interpExp q = q/(2-q)`;
* `rpow_interp`: the scalar inequality for `λ ≥ 0`;
* **`fracTrace_interp`**: the matrix inequality for `T ⪰ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFractional

open Matrix BlockBand.Internal.Contracts.TransmissionPath
open scoped ComplexOrder

/-- `θ = q/(2-q)`. -/
def interpExp (q : ℝ) : ℝ := q / (2 - q)

theorem interpExp_mem {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < interpExp q ∧ interpExp q < 1 := by
  unfold interpExp
  refine ⟨div_pos hq0 (by linarith), ?_⟩
  rw [div_lt_one (by linarith)]; linarith

theorem interpExp_sum {q : ℝ} (hq1 : q < 1) :
    interpExp q + q / 2 * (1 - interpExp q) = q := by
  unfold interpExp
  have : (2 - q) ≠ 0 := by linarith
  field_simp
  ring

/-- **Scalar interpolation**: `λ^q ≤ A^θB^{1-θ}(θλ/A + (1-θ)λ^{q/2}/B)`. -/
theorem rpow_interp {q A B x : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hA : 0 < A) (hB : 0 < B)
    (hx : 0 ≤ x) :
    x ^ q ≤ A ^ interpExp q * B ^ (1 - interpExp q) *
      (interpExp q * (x / A) + (1 - interpExp q) * (x ^ (q / 2) / B)) := by
  obtain ⟨hθ0, hθ1⟩ := interpExp_mem hq0 hq1
  set θ := interpExp q
  have hAB : 0 < A ^ θ * B ^ (1 - θ) := by positivity
  have hgm := Real.geom_mean_le_arith_mean2_weighted hθ0.le (by linarith : 0 ≤ 1 - θ)
    (div_nonneg hx hA.le) (div_nonneg (Real.rpow_nonneg hx (q / 2)) hB.le) (by ring)
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hgm hAB.le)
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    rw [Real.zero_rpow hq0.ne', Real.zero_rpow (by positivity), zero_div, zero_div,
      Real.zero_rpow hθ0.ne', zero_mul, mul_zero]
  · rw [Real.div_rpow hx hA.le, Real.div_rpow (Real.rpow_nonneg hx _) hB.le,
      ← Real.rpow_mul hx]
    have e : x ^ q = x ^ θ * x ^ (q / 2 * (1 - θ)) := by
      rw [← Real.rpow_add hpos, interpExp_sum hq1]
    rw [e]
    have hA' : A ^ θ ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
    have hB' : B ^ (1 - θ) ≠ 0 := (Real.rpow_pos_of_pos hB _).ne'
    field_simp

/-- **Matrix interpolation**: for `T ⪰ 0` and `A, B > 0`,
`Tr T^q ≤ A^θB^{1-θ}(θ Tr T/A + (1-θ) Tr T^{q/2}/B)`. -/
theorem fracTrace_interp {W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ}
    (hT : T.PosSemidef) {q A B : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hA : 0 < A) (hB : 0 < B) :
    fracTrace q T ≤ A ^ interpExp q * B ^ (1 - interpExp q) *
      (interpExp q * (conductanceOf T / A) + (1 - interpExp q) * (fracTrace (q / 2) T / B)) := by
  have hg : conductanceOf T = ∑ i, hT.1.eigenvalues i := by
    have := Generator.trace_pow_re_eq hT.1 1
    simp only [pow_one] at this
    exact this
  rw [FractionalBulk.fracTrace_eq_sum_eigenvalues_psd hT, FractionalBulk.fracTrace_eq_sum_eigenvalues_psd hT,
    hg, Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => rpow_interp hq0 hq1 hA hB (hT.eigenvalues_nonneg i)

end BlockBand.Transmission.LawFractional
