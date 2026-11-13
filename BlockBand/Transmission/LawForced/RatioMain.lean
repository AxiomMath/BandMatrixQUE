module

public import BlockBand.Transmission.LawForced.RatioTerms

/-!
# The main terms of the one-layer `F_z` mean are `ratioDrift/W`

`RatioTerms` gives the mean of `linR + quadR + linR²/2` exactly. Its main terms, after the
inputs `1 − c ≈ ag` (`c = meanC`, `a = D₀/(2W)`, the second clause of `ubarMean_bulk` at
`G = gW hT Λ`),
`covQ(w) ≈ aΣ_{km}t_kr_kt_mr_m(2−t_k−t_m)` (`cov_cross_contract`) and
`covV ≈ 2aΣ_k t_k²Λ_k²(1−t_k)` (`cov_diag_contract`), are
```
a·[g Σ_k t_kΛ_k + Σ_i ((x_i²/2)Q(x_i) − (y_i²/2)Q(−y_i)) + Σ_k t_k²(1−t_k)Λ_k²],
Q(w) = Σ_{km} t_kr^w_kt_mr^w_m(2−t_k−t_m).
```
**`ratio_main_term`**: `F_z(traceMeasure T)` times this is exactly
`ratioDrift D₀ E 0 u z (traceMeasure T) / W` (`κ ≡ 0`), for `0 ⪯ T ⪯ I` and `z` in the chamber.
It combines `logDrift_eigen` (one weight point at a time) with
`ratioDrift_traceMeasure`. `sum_t_dualLam` is `Σ_k t_kΛ_k = Σ_i x_iS(x_i) + Σ_i y_iS(−y_i)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}

/-- `Q(w) = Σ_{km} t_kr_kt_mr_m(2 − t_k − t_m)`. -/
def quadMain (t : n → ℝ) (w : ℝ) : ℝ :=
  ∑ k, ∑ m, t k * (1 + w * t k)⁻¹ * (t m * (1 + w * t m)⁻¹) * (2 - t k - t m)

omit [DecidableEq n] in
theorem sum_t_dualLam (z : DualCoord p) (t : n → ℝ) :
    ∑ k, t k * dualLam z (t k) =
      ∑ i, z.1 i * ∑ k, t k / (1 + z.1 i * t k) + ∑ i, z.2 i * ∑ k, t k / (1 + -z.2 i * t k) := by
  simp only [dualLam, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun k i => t k * (z.2 i / (1 - z.2 i * t k)))]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  · ring
  · rw [neg_mul, ← sub_eq_add_neg]; ring

omit [DecidableEq n] in
theorem logDrift_eigen' (t : n → ℝ) {w : ℝ} (hw : ∀ k, 1 + w * t k ≠ 0) :
    w * (∑ k, t k) * (∑ k, t k / (1 + w * t k)) + w ^ 2 / 2 * quadMain t w =
      w * (1 + w) * (∑ k, t k / (1 + w * t k)) ^ 2 := by
  rw [← logDrift_eigen t hw, quadMain]
  simp only [div_eq_mul_inv]

/-- **The main terms are `ratioDrift/W`** (`κ ≡ 0`). -/
theorem ratio_main_term {z : DualCoord p} (hz : z ∈ dualChamber p) {T : Matrix n n ℂ}
    (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) (D0 E u Wr : ℝ) :
    transmissionRatio z.1 z.2 (traceMeasure T) * (D0 / (2 * Wr) *
      ((∑ k, h0.1.eigenvalues k) * ∑ k, h0.1.eigenvalues k * dualLam z (h0.1.eigenvalues k) +
        ∑ i, (z.1 i ^ 2 / 2 * quadMain h0.1.eigenvalues (z.1 i) -
          z.2 i ^ 2 / 2 * quadMain h0.1.eigenvalues (-z.2 i)) +
        ∑ k, h0.1.eigenvalues k ^ 2 * (1 - h0.1.eigenvalues k) *
          dualLam z (h0.1.eigenvalues k) ^ 2)) =
      ratioDrift D0 E (fun _ => 0) u z (traceMeasure T) / Wr := by
  set t := h0.1.eigenvalues
  have hm := eigenvalues_mem h0 h1
  have hx : ∀ i k, 1 + z.1 i * t k ≠ 0 := fun i k =>
    (pos_x (hz.2.2.1 i).le (hm k).1).ne'
  have hy : ∀ i k, 1 + -z.2 i * t k ≠ 0 := fun i k =>
    (pos_y (hz.2.2.2 i).2 (hz.2.2.2 i).1.le (hm k).2).ne'
  have ex := fun i => logDrift_eigen' t (hx i)
  have ey := fun i => logDrift_eigen' t (hy i)
  have hsum : (∑ k, t k) * ∑ k, t k * dualLam z (t k) +
      ∑ i, (z.1 i ^ 2 / 2 * quadMain t (z.1 i) - z.2 i ^ 2 / 2 * quadMain t (-z.2 i)) =
      ∑ i, z.1 i * (1 + z.1 i) * eigS h0.1 (z.1 i) ^ 2 +
        ∑ j, z.2 j * (1 - z.2 j) * eigS h0.1 (-z.2 j) ^ 2 := by
    rw [sum_t_dualLam, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    have e1 : ∀ i, z.1 i * (1 + z.1 i) * eigS h0.1 (z.1 i) ^ 2 =
        (∑ k, t k) * (z.1 i * ∑ k, t k / (1 + z.1 i * t k)) +
          z.1 i ^ 2 / 2 * quadMain t (z.1 i) := fun i => by
      rw [eigS, ← ex i]; ring
    have e2 : ∀ i, z.2 i * (1 - z.2 i) * eigS h0.1 (-z.2 i) ^ 2 =
        (∑ k, t k) * (z.2 i * ∑ k, t k / (1 + -z.2 i * t k)) -
          z.2 i ^ 2 / 2 * quadMain t (-z.2 i) := fun i => by
      have := ey i
      rw [neg_sq] at this
      rw [eigS]
      linear_combination this
    simp only [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [ratioDrift_traceMeasure D0 E (fun _ => 0) u hz h0 h1]
  have hκ : absorptionRate E (fun _ => 0) u = 0 := by simp [absorptionRate]
  rw [hκ, ← hsum]
  ring

end BlockBand.Transmission.LawForced
