module

public import BlockBand.Transmission.LawDuality.RatioGen
public import BlockBand.Transmission.Dual.Generator

/-!
# Duality principle: bounds on `𝒟_p F_·(ν)` uniform in `ν`

* `abs_lkerInt1_le`, `abs_lkerInt2_le`: `|A₁| ≤ m/δ`, `|A₂| ≤ m/δ²` (`m = ν[0,1]`) when
  `1 + xt ≥ δ` on `[0,1]`; `δ = 1` at `x ≥ 0`, `δ = 1 − y` at `x = −y`, `0 ≤ y < 1`;
* `poly_mul_exp_le`: `(m² + m)e^{−cm} ≤ 2/c² + 1/c`, which absorbs the polynomial in the mass
  into `F ≤ e^{−cm}` (`transmissionRatio_le_exp_mass`, `c = x₀/(1+x₀) + y₀`);
* **`abs_dualGenerator_ratioOn_le`**: for `z` in the chamber and **every** `ν`,
  `|𝒟_pF_·(ν)(z)| ≤ |D₀|/2 · genCoef z · (2/c² + 1/c)`, with `genCoef` continuous on the chamber.

The sibling module derives the compact bounds `exists_bound_dualGenerator_ratioOn` and
`exists_bound_ratioDrift`: on every compact subset of the chamber, `𝒟_pF_·(ν)` and
`ratioDrift D₀ E κ u · ν` are bounded uniformly in `ν` (and in `u`, for an absorption profile `κ`).

The bounds are not uniform on the whole chamber: for `ν = mδ₁`, `0 < m < 1`, the `y`-part of
`𝒟_pF` grows like `m²(1−y)^{m−1}` as `y → 1`, so the duality
argument has to localize the dual in compacts of the chamber.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable (ν : FiniteMeasure unitInterval) {p : ℕ}

theorem abs_lkerInt1_le {δ x : ℝ} (hδ : 0 < δ) (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + x * t) :
    |lkerInt1 ν x| ≤ 1 / δ * (ν : Measure unitInterval).real univ := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure unitInterval))
    (f := fun t : unitInterval => lker1 x (t : ℝ)) (C := 1 / δ) (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_lker1_le hδ (h t t.2.1 t.2.2))
  rwa [Real.norm_eq_abs] at this

theorem abs_lkerInt2_le {δ x : ℝ} (hδ : 0 < δ) (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → δ ≤ 1 + x * t) :
    |lkerInt2 ν x| ≤ 1 / δ ^ 2 * (ν : Measure unitInterval).real univ := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure unitInterval))
    (f := fun t : unitInterval => lker2 x (t : ℝ)) (C := 1 / δ ^ 2)
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_lker2_le hδ (h t t.2.1 t.2.2) t.2.1 t.2.2)
  rwa [Real.norm_eq_abs] at this

theorem dom_nonneg_x {x : ℝ} (hx : 0 ≤ x) : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 1 ≤ 1 + x * t :=
  fun t ht _ => by nlinarith

theorem dom_neg_y {y : ℝ} (hy : 0 ≤ y) : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 1 - y ≤ 1 + -y * t :=
  fun t ht0 ht1 => by nlinarith

/-- `(m² + m)e^{−cm} ≤ 2/c² + 1/c`. -/
theorem poly_mul_exp_le {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) :
    Real.exp (-c * m) * (m ^ 2 + m) ≤ 2 / c ^ 2 + 1 / c := by
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hm)
  rw [neg_mul, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
  have e : (2 / c ^ 2 + 1 / c) * (1 + c * m + (c * m) ^ 2 / 2) =
      m ^ 2 + m + (2 / c ^ 2 + 2 * m / c + 1 / c + c * m ^ 2 / 2) := by
    field_simp; ring
  have hr : 0 ≤ 2 / c ^ 2 + 2 * m / c + 1 / c + c * m ^ 2 / 2 := by positivity
  calc m ^ 2 + m ≤ (2 / c ^ 2 + 1 / c) * (1 + c * m + (c * m) ^ 2 / 2) := by rw [e]; linarith
    _ ≤ (2 / c ^ 2 + 1 / c) * Real.exp (c * m) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := mul_comm _ _

/-- One coordinate term of the closed form. -/
theorem abs_term_le {a b A1 A2 m k σ : ℝ} (hk : 0 ≤ k) (hσ : |σ| = 1)
    (h1 : |A1| ≤ k * m) (h2 : |A2| ≤ k ^ 2 * m) :
    |a * (A1 ^ 2 + σ * A2) + b * A1| ≤ (|a| * k ^ 2 + |b| * k) * (m ^ 2 + m) := by
  have hA1sq : A1 ^ 2 ≤ k ^ 2 * m ^ 2 := by
    rw [← sq_abs]
    calc |A1| ^ 2 ≤ (k * m) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := by ring
  have e1 : |a * (A1 ^ 2 + σ * A2)| ≤ |a| * (k ^ 2 * (m ^ 2 + m)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
    calc |A1 ^ 2 + σ * A2| ≤ |A1 ^ 2| + |σ * A2| := abs_add_le _ _
      _ = A1 ^ 2 + |A2| := by rw [abs_of_nonneg (sq_nonneg _), abs_mul, hσ, one_mul]
      _ ≤ k ^ 2 * m ^ 2 + k ^ 2 * m := add_le_add hA1sq h2
      _ = _ := by ring
  have e2 : |b * A1| ≤ |b| * (k * (m ^ 2 + m)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg m]) hk)) (abs_nonneg b)
  calc _ ≤ |a * (A1 ^ 2 + σ * A2)| + |b * A1| := abs_add_le _ _
    _ ≤ _ := add_le_add e1 e2
    _ = _ := by ring

/-- The coefficient of the bound (continuous on the chamber). -/
def genCoef (z : DualCoord p) : ℝ :=
  ∑ i, (|z.1 i * (1 + z.1 i)| + |dualDriftX z i|) +
    ∑ j, (|z.2 j * (1 - z.2 j)| * ((1 - z.2 j)⁻¹) ^ 2 + |dualDriftY z j| * (1 - z.2 j)⁻¹)

/-- The exponential rate `c = x₀/(1+x₀) + y₀`. -/
def expRate (i0 : Fin p) (z : DualCoord p) : ℝ := z.1 i0 / (1 + z.1 i0) + z.2 i0

theorem expRate_pos {z : DualCoord p} (hz : z ∈ dualChamber p) (i0 : Fin p) :
    0 < expRate i0 z := by
  have h1 := hz.2.2.1 i0
  have h2 := (hz.2.2.2 i0).1
  unfold expRate; positivity

/-- **`|𝒟_pF_·(ν)(z)| ≤ |D₀|/2 · genCoef z · (2/c² + 1/c)` for every `ν`.** -/
theorem abs_dualGenerator_ratioOn_le (D0 : ℝ) {z : DualCoord p} (hz : z ∈ dualChamber p)
    (i0 : Fin p) :
    |dualGenerator D0 (ratioOn ν) z| ≤
      |D0| / 2 * genCoef z * (2 / expRate i0 z ^ 2 + 1 / expRate i0 z) := by
  set m := (ν : Measure unitInterval).real univ
  have hm : 0 ≤ m := measureReal_nonneg
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z.1 z.2 from hz)
  have hF : 0 < ratioOn ν z ∧ ratioOn ν z ≤ 1 := transmissionRatio_mem_vec hr ν
  have hFe : ratioOn ν z ≤ Real.exp (-expRate i0 z * m) := transmissionRatio_le_exp_mass hr i0 ν
  have hx : ∀ i, 0 ≤ z.1 i := fun i => (hz.2.2.1 i).le
  have hy0 : ∀ j, 0 ≤ z.2 j := fun j => (hz.2.2.2 j).1.le
  have hy1 : ∀ j, 0 < 1 - z.2 j := fun j => by linarith [(hz.2.2.2 j).2]
  have hS : |(∑ i, (z.1 i * (1 + z.1 i) * (lkerInt1 ν (z.1 i) ^ 2 + lkerInt2 ν (z.1 i)) +
        dualDriftX z i * lkerInt1 ν (z.1 i))) +
      ∑ j, (z.2 j * (1 - z.2 j) * (lkerInt1 ν (-z.2 j) ^ 2 - lkerInt2 ν (-z.2 j)) +
        dualDriftY z j * lkerInt1 ν (-z.2 j))| ≤ genCoef z * (m ^ 2 + m) := by
    unfold genCoef
    rw [add_mul, Finset.sum_mul, Finset.sum_mul]
    refine (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)))
    · have h := abs_term_le (a := z.1 i * (1 + z.1 i)) (b := dualDriftX z i) (σ := 1)
        zero_le_one abs_one
        (by simpa only [div_one] using abs_lkerInt1_le ν one_pos (dom_nonneg_x (hx i)))
        (by simpa only [one_pow, div_one] using abs_lkerInt2_le ν one_pos (dom_nonneg_x (hx i)))
      simpa only [one_mul, one_pow, mul_one] using h
    · have h := abs_term_le (a := z.2 j * (1 - z.2 j)) (b := dualDriftY z j) (σ := -1)
        (inv_nonneg.2 (hy1 j).le) (by simp)
        (by simpa only [one_div] using abs_lkerInt1_le ν (hy1 j) (dom_neg_y (hy0 j)))
        (by simpa only [one_div, inv_pow] using abs_lkerInt2_le ν (hy1 j) (dom_neg_y (hy0 j)))
      rw [show lkerInt1 ν (-z.2 j) ^ 2 - lkerInt2 ν (-z.2 j) =
        lkerInt1 ν (-z.2 j) ^ 2 + -1 * lkerInt2 ν (-z.2 j) by ring]
      exact h
  rw [dualGenerator_ratioOn ν D0 (dualChamber_subset_ratioOpen hz), abs_mul, abs_mul,
    abs_div, abs_two, abs_of_pos hF.1]
  have hc := expRate_pos hz i0
  have hpe := poly_mul_exp_le hc hm
  have hg : 0 ≤ genCoef z := by
    unfold genCoef
    exact add_nonneg (Finset.sum_nonneg fun i _ => by positivity)
      (Finset.sum_nonneg fun j _ => by have := hy1 j; positivity)
  calc |D0| / 2 * ratioOn ν z * |_| ≤ |D0| / 2 * ratioOn ν z * (genCoef z * (m ^ 2 + m)) :=
        mul_le_mul_of_nonneg_left hS (by have := hF.1; positivity)
    _ = |D0| / 2 * genCoef z * (ratioOn ν z * (m ^ 2 + m)) := by ring
    _ ≤ |D0| / 2 * genCoef z * (Real.exp (-expRate i0 z * m) * (m ^ 2 + m)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        exact hFe
    _ ≤ _ := mul_le_mul_of_nonneg_left hpe (by positivity)

end BlockBand.Transmission.LawDuality
