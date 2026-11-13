module

public import BlockBand.Transmission.LawForced.DualPoint

/-!
# `𝒟_pF = F·(drift of log F + ½ bracket)` in eigenvalue form

For every finite measure `ν` on `[0,1]` and every chamber point `z = (x, y)`, with
`S_ν(w) = ∫(1+wt)⁻¹dν = −A₁(w)` (`A₁ = lkerInt1 ν`):

**`dualGenerator_ratioOn_bracket`**:
```
𝒟_pF_·(ν)(z) = (D₀/2)·F_z(ν)·[Σ_i x_i(1+x_i)S(x_i)² + Σ_j y_j(1−y_j)S(−y_j)²
                              + ∫ t(1−t)Λ_z(t)² dν(t)].
```
For `ν = traceMeasure T` (`ν = Σ_k t_kδ_{t_k}`) the first two sums are `(2/D₀)` times the
generator of `log F` and the integral is `Γ(log F)/D₀ = Σ_k t_k²(1−t_k)Λ_z(t_k)²`, the bracket of
the paper.
So the one-layer expansion only has to produce these two eigenvalue expressions: this file
removes the dual-coordinate derivatives from the target of `RatioDriftSummable`.

Proof: `dualGenerator_ratioOn` and `dual_point` integrated against `ν`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality

variable (ν : FiniteMeasure unitInterval) {p : ℕ}

theorem integrable_lker1_of {δ x : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + x * t) :
    Integrable (fun t : unitInterval => lker1 x (t : ℝ)) (ν : Measure unitInterval) :=
  Integrable.of_bound ((measurable_lker1 x).comp measurable_subtype_coe).aestronglyMeasurable
    (1 / δ) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_lker1_le hδ (h t t.2.1 t.2.2))

theorem integrable_lker2_of {δ x : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + x * t) :
    Integrable (fun t : unitInterval => lker2 x (t : ℝ)) (ν : Measure unitInterval) :=
  Integrable.of_bound ((measurable_lker2 x).comp measurable_subtype_coe).aestronglyMeasurable
    (1 / δ ^ 2) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_lker2_le hδ (h t t.2.1 t.2.2) t.2.1 t.2.2)

/-- `dualPoint` in the kernels `lker1 = −(1+wt)⁻¹`, `lker2 = t(1+wt)⁻²`. -/
theorem dualPoint_eq_lker (z : DualCoord p) (t : ℝ) :
    dualPoint z t =
      (∑ i, (z.1 i * (1 + z.1 i) * lker2 (z.1 i) t + dualDriftX z i * lker1 (z.1 i) t)) +
        ∑ j, (-(z.2 j * (1 - z.2 j)) * lker2 (-z.2 j) t +
          dualDriftY z j * lker1 (-z.2 j) t) := by
  unfold dualPoint lker1 lker2
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · simp only [div_eq_mul_inv, ← inv_pow]; ring
  · rw [show 1 + -z.2 i * t = 1 - z.2 i * t by ring]
    simp only [div_eq_mul_inv, ← inv_pow]; ring

/-- **The bracket integral**: `∫ t(1−t)Λ_z² dν` is the `ν`-linear part of `𝒟_pF/F`. -/
theorem integral_dualBracket {z : DualCoord p} (hz : z ∈ dualChamber p) :
    ∫ t, (t : ℝ) * (1 - t) * dualLam z t ^ 2 ∂(ν : Measure unitInterval) =
      (∑ i, (z.1 i * (1 + z.1 i) * lkerInt2 ν (z.1 i) + dualDriftX z i * lkerInt1 ν (z.1 i))) +
        ∑ j, (-(z.2 j * (1 - z.2 j)) * lkerInt2 ν (-z.2 j) +
          dualDriftY z j * lkerInt1 ν (-z.2 j)) := by
  have hx : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 : ℝ) ≤ 1 + z.1 i * t := fun i =>
    dom_nonneg_x (hz.2.2.1 i).le
  have hy : ∀ j, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 1 - z.2 j ≤ 1 + -z.2 j * t := fun j =>
    dom_neg_y (hz.2.2.2 j).1.le
  have hy1 : ∀ j, 0 < 1 - z.2 j := fun j => by linarith [(hz.2.2.2 j).2]
  have hI1 : ∀ i, Integrable (fun t : unitInterval =>
      z.1 i * (1 + z.1 i) * lker2 (z.1 i) t + dualDriftX z i * lker1 (z.1 i) t)
      (ν : Measure unitInterval) := fun i =>
    ((integrable_lker2_of ν one_pos (hx i)).const_mul _).add
      ((integrable_lker1_of ν one_pos (hx i)).const_mul _)
  have hI2 : ∀ j, Integrable (fun t : unitInterval =>
      -(z.2 j * (1 - z.2 j)) * lker2 (-z.2 j) t + dualDriftY z j * lker1 (-z.2 j) t)
      (ν : Measure unitInterval) := fun j =>
    ((integrable_lker2_of ν (hy1 j) (hy j)).const_mul _).add
      ((integrable_lker1_of ν (hy1 j) (hy j)).const_mul _)
  have hpt : ∀ t : unitInterval, (t : ℝ) * (1 - t) * dualLam z t ^ 2 =
      (∑ i, (z.1 i * (1 + z.1 i) * lker2 (z.1 i) t + dualDriftX z i * lker1 (z.1 i) t)) +
        ∑ j, (-(z.2 j * (1 - z.2 j)) * lker2 (-z.2 j) t +
          dualDriftY z j * lker1 (-z.2 j) t) := fun t => by
    rw [dual_point hz t.2.1 t.2.2, dualPoint_eq_lker]
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (integrable_finsetSum _ fun i _ => hI1 i)
      (integrable_finsetSum _ fun j _ => hI2 j),
    integral_finsetSum _ fun i _ => hI1 i, integral_finsetSum _ fun j _ => hI2 j]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_add ((integrable_lker2_of ν one_pos (hx i)).const_mul _)
        ((integrable_lker1_of ν one_pos (hx i)).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add ((integrable_lker2_of ν (hy1 j) (hy j)).const_mul _)
        ((integrable_lker1_of ν (hy1 j) (hy j)).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl

/-- **`𝒟_pF = F·(D₀/2)·[Σ x(1+x)S² + Σ y(1−y)S² + ∫ t(1−t)Λ²]`** on the chamber, for every
finite measure `ν` (`S = −lkerInt1 ν`; the squares do not see the sign). -/
theorem dualGenerator_ratioOn_bracket (D0 : ℝ) {z : DualCoord p} (hz : z ∈ dualChamber p) :
    dualGenerator D0 (ratioOn ν) z = D0 / 2 * ratioOn ν z *
      ((∑ i, z.1 i * (1 + z.1 i) * lkerInt1 ν (z.1 i) ^ 2) +
        (∑ j, z.2 j * (1 - z.2 j) * lkerInt1 ν (-z.2 j) ^ 2) +
        ∫ t, (t : ℝ) * (1 - t) * dualLam z t ^ 2 ∂(ν : Measure unitInterval)) := by
  rw [dualGenerator_ratioOn ν D0 (dualChamber_subset_ratioOpen hz), integral_dualBracket ν hz]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.sum_add_distrib, sub_eq_add_neg]
  ring

end BlockBand.Transmission.LawForced
