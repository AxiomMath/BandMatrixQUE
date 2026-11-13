module

public import BlockBand.Transmission.LawForced.DualBracket
public import BlockBand.Transmission.LawDuality.PowerBridge

/-!
# `ratioDrift` at a matrix state, in eigenvalues

For `0 ⪯ T ⪯ I` with eigenvalues `t_k` and `ν = traceMeasure T` put
`S_T(w) = Σ_k t_k/(1+wt_k)` (`eigS`). Then (**`ratioDrift_traceMeasure`**), on the chamber:
```
ratioDrift D₀ E κ u z ν = F_z(ν)·[(D₀/2)(Σ_i x_i(1+x_i)S_T(x_i)² + Σ_j y_j(1−y_j)S_T(−y_j)²
                                   + Σ_k t_k²(1−t_k)Λ_z(t_k)²) − h(u)R(z)].
```
This is the exact target of the one-layer expansion in `RatioDriftSummable`:
* `−(D₀/2)w(1+w)S_T(w)²` is the limit of `W` times the mean of the second-order expansion
  `wTr(R_wB) − (w²/2)Tr(R_wBR_wB)` of `log det(I + wT₊) − log det(I + wT)` (`LogDetExpand`), in the
  eigenbasis of `T` (`D = diag t`, `R_w = (I+wD)⁻¹`): **`logDrift_eigen`** says
  `w g S + (w²/2)Σ_{k,m} r_kr_mt_kt_m(2−t_k−t_m) = w(1+w)S²` (`r_k = (1+wt_k)⁻¹`, `g = Σt_k`),
  and the left side is `(2W/D₀)·[−w(c−1)S + (w²/2)E Tr(R_wBR_wB)]` at main order, with
  `c − 1 ≈ −D₀g/(2W)` (`E Tr(R_wB) ≈ (c−1)S`, `ubarMean_bulk`) and the PCB covariance
  `E B_kmB_mk ≈ (D₀/(2W))t_kt_m(2−t_k−t_m)`. Summed with signs (`−` for `x_i`, `+` for `−y_j`)
  this gives the first two sums;
* `(D₀/2)Σ_k t_k²(1−t_k)Λ_z(t_k)²` is half of `W` times the variance of the first-order term
  `−Σ_k B_kkΛ_z(t_k)` (`E B_kkB_mm ≈ δ_{km}(D₀/W)t_k²(1−t_k)`);
* `−h(u)R(z)` is the injection.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.LawDuality
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ} {p : ℕ}

/-- `S_T(w) = Σ_k t_k/(1+wt_k)`, `t_k` the eigenvalues of `T`. -/
def eigS (hT : T.IsHermitian) (w : ℝ) : ℝ := ∑ k, hT.eigenvalues k / (1 + w * hT.eigenvalues k)

/-- `∫ g d(traceMeasure T) = Σ_k t_k g(t_k)` for `0 ⪯ T ⪯ I` and `g` continuous on `[0,1]`. -/
theorem integral_traceMeasure_eq (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) {g : ℝ → ℝ}
    (hg : Continuous fun s : unitInterval => g s) :
    ∫ s, g s ∂(traceMeasure T : Measure unitInterval) =
      ∑ k, h0.1.eigenvalues k * g (h0.1.eigenvalues k) := by
  rw [integral_traceMeasure h0.1 (g := fun s : unitInterval => g s) hg]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨ha, hb⟩ := eigenvalues_mem h0 h1 k
  rw [Real.coe_toNNReal _ ha, toUnit, Set.coe_projIcc, min_eq_right hb, max_eq_right ha]

theorem continuous_inv_one_add {w δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + w * t) :
    Continuous fun s : unitInterval => (1 + w * (s : ℝ))⁻¹ :=
  (continuous_const.add (continuous_const.mul continuous_subtype_val)).inv₀ fun s =>
    (hδ.trans_le (h s s.2.1 s.2.2)).ne'

/-- `A₁(w) = −S_T(w)` at `ν = traceMeasure T`. -/
theorem lkerInt1_traceMeasure (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) {w δ : ℝ}
    (hδ : 0 < δ) (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + w * t) :
    lkerInt1 (traceMeasure T) w = -eigS h0.1 w := by
  unfold lkerInt1 lker1
  rw [integral_traceMeasure_eq h0 h1 (g := fun s => -(1 + w * s)⁻¹)
    (continuous_inv_one_add hδ h).neg, eigS, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [div_eq_mul_inv, mul_neg]

theorem continuous_bracket {z : DualCoord p} (hz : z ∈ dualChamber p) :
    Continuous fun s : unitInterval => (s : ℝ) * (1 - s) * dualLam z s ^ 2 := by
  have hx : ∀ i, Continuous fun s : unitInterval => z.1 i / (1 + z.1 i * (s : ℝ)) := fun i =>
    continuous_const.mul (continuous_inv_one_add one_pos (dom_nonneg_x (hz.2.2.1 i).le))
  have hy : ∀ j, Continuous fun s : unitInterval => z.2 j / (1 - z.2 j * (s : ℝ)) := fun j => by
    have hc := continuous_inv_one_add (by linarith [(hz.2.2.2 j).2])
      (dom_neg_y (hz.2.2.2 j).1.le)
    refine continuous_const.mul (hc.congr fun s => ?_)
    rw [neg_mul, ← sub_eq_add_neg]
  have hL : Continuous fun s : unitInterval => dualLam z s :=
    (continuous_finsetSum _ fun i _ => hx i).add (continuous_finsetSum _ fun j _ => hy j)
  exact (continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)).mul (hL.pow 2)

/-- **`ratioDrift` at `traceMeasure T` in eigenvalues.** -/
theorem ratioDrift_traceMeasure (D0 E : ℝ) (κ : ℝ → ℝ) (u : ℝ) {z : DualCoord p}
    (hz : z ∈ dualChamber p) (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) :
    ratioDrift D0 E κ u z (traceMeasure T) = transmissionRatio z.1 z.2 (traceMeasure T) *
      (D0 / 2 * ((∑ i, z.1 i * (1 + z.1 i) * eigS h0.1 (z.1 i) ^ 2) +
        (∑ j, z.2 j * (1 - z.2 j) * eigS h0.1 (-z.2 j) ^ 2) +
        ∑ k, h0.1.eigenvalues k ^ 2 * (1 - h0.1.eigenvalues k) *
          dualLam z (h0.1.eigenvalues k) ^ 2) -
        absorptionRate E κ u * ∑ i, (z.1 i + z.2 i)) := by
  unfold ratioDrift
  rw [dualGenerator_ratioOn_bracket _ D0 hz,
    integral_traceMeasure_eq h0 h1 (g := fun s => s * (1 - s) * dualLam z s ^ 2)
      (continuous_bracket hz)]
  have hx : ∀ i, lkerInt1 (traceMeasure T) (z.1 i) = -eigS h0.1 (z.1 i) := fun i =>
    lkerInt1_traceMeasure h0 h1 one_pos (dom_nonneg_x (hz.2.2.1 i).le)
  have hy : ∀ j, lkerInt1 (traceMeasure T) (-z.2 j) = -eigS h0.1 (-z.2 j) := fun j =>
    lkerInt1_traceMeasure h0 h1 (by linarith [(hz.2.2.2 j).2]) (dom_neg_y (hz.2.2.2 j).1.le)
  simp only [hx, hy, neg_sq]
  have hk : ∀ k, h0.1.eigenvalues k * (h0.1.eigenvalues k * (1 - h0.1.eigenvalues k) *
      dualLam z (h0.1.eigenvalues k) ^ 2) = h0.1.eigenvalues k ^ 2 * (1 - h0.1.eigenvalues k) *
      dualLam z (h0.1.eigenvalues k) ^ 2 := fun k => by ring
  simp only [hk]
  rw [ratioOn]
  ring

/-- **The drift of `log det(I + wT)` in eigenvalues** (pure algebra): with `r_k = (1+wt_k)⁻¹`,
`S = Σ t_kr_k`, `g = Σ t_k`:
`w g S + (w²/2) Σ_{k,m} r_kr_mt_kt_m(2 − t_k − t_m) = w(1+w)S²`. -/
theorem logDrift_eigen {ι : Type*} [Fintype ι] (t : ι → ℝ) {w : ℝ}
    (hw : ∀ k, 1 + w * t k ≠ 0) :
    w * (∑ k, t k) * (∑ k, t k / (1 + w * t k)) +
        w ^ 2 / 2 * ∑ k, ∑ m, (t k / (1 + w * t k)) * (t m / (1 + w * t m)) *
          (2 - t k - t m) =
      w * (1 + w) * (∑ k, t k / (1 + w * t k)) ^ 2 := by
  set S := ∑ k, t k / (1 + w * t k)
  have hK : w * ∑ k, t k / (1 + w * t k) * t k = ∑ k, t k - S := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hw k
    set d := 1 + w * t k with hd
    field_simp
    rw [hd]; ring
  have hQ : ∑ k, ∑ m, (t k / (1 + w * t k)) * (t m / (1 + w * t m)) * (2 - t k - t m) =
      2 * S ^ 2 - 2 * S * ∑ k, t k / (1 + w * t k) * t k := by
    set a : ι → ℝ := fun k => t k / (1 + w * t k)
    set b : ι → ℝ := fun k => t k / (1 + w * t k) * t k
    have inner : ∀ k, ∑ m, a k * a m * (2 - t k - t m) =
        (2 * a k - b k) * ∑ m, a m - a k * ∑ m, b m := fun k => by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by simp only [a, b]; ring
    rw [Finset.sum_congr rfl fun k _ => inner k, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hQ]
  linear_combination (-(w * S)) * hK

end BlockBand.Transmission.LawForced
