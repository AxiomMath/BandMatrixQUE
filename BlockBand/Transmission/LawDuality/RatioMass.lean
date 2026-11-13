module

public import BlockBand.Transmission.LawDuality.RatioBound

/-!
# Duality principle: a bound on `𝒟_q F_·(ν)` linear in the mass

`|𝒟_q F_·(ν)(z)| ≤ |D₀|/2 · (6q + 8q²)(1+M)²/ε² · ν[0,1]` (**`abs_dualGenerator_ratioOn_le_mass`**).

The uniform-in-`ν` constant of
`abs_dualGenerator_ratioOn_le` degenerates at the corners, but a constant times the mass does
not. Proof: in the closed form `dualGenerator_ratioOn` the singular drift terms regroup into
difference quotients of `φ(w) = w(1+w)A₁(w)` (`A₁ = lkerInt1`):
* same species: `2φ(w_i)Σ_{k≠i}(w_i − w_k)⁻¹ = Σ_{i,k}(φ(w_i) − φ(w_k))/(w_i − w_k)`
  (`two_mul_sum_erase_eq`), for `w = x` and for `w = −y`;
* cross terms: `−2Σ_{i,j}(φ(x_i) − φ(−y_j))/(x_i + y_j)`;
and `φ` is Lipschitz on `[ε−1, M]` with constant `2(1+M)²/ε² · ν[0,1]` (`abs_ratioPhi_sub_le`).
The quadratic terms `x(1+x)A₁(x)²` are absorbed by `F ≤ e^{−x m/(1+x)}`: `m²e^{−cm} ≤ m/c`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

/-!
## Algebra: symmetrization and difference quotients
-/

/-- `2 Σ_i g_i Σ_{k≠i} (w_i − w_k)⁻¹ = Σ_{i,k} (g_i − g_k)/(w_i − w_k)`. -/
theorem two_mul_sum_erase_eq {q : ℕ} (g w : Fin q → ℝ) :
    2 * ∑ i, g i * ∑ k ∈ Finset.univ.erase i, 1 / (w i - w k) =
      ∑ i, ∑ k, (g i - g k) / (w i - w k) := by
  have h1 : ∀ i, g i * ∑ k ∈ Finset.univ.erase i, 1 / (w i - w k) =
      ∑ k, g i / (w i - w k) := fun i => by
    rw [Finset.mul_sum, Finset.sum_erase _ (by simp)]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∑ i, ∑ k, g k / (w i - w k) = -∑ i, ∑ k, g i / (w i - w k) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show w k - w i = -(w i - w k) by ring, div_neg]
  simp_rw [h1, sub_div, Finset.sum_sub_distrib, h2]
  ring

/-- A difference quotient of a `C`-Lipschitz map is bounded by `C` (also at `a = b`). -/
theorem abs_div_sub_le {f : ℝ → ℝ} {a b C : ℝ} (hC : 0 ≤ C) (h : |f a - f b| ≤ C * |a - b|) :
    |(f a - f b) / (a - b)| ≤ C := by
  rcases eq_or_ne (a - b) 0 with hab | hab
  · rw [hab, div_zero, abs_zero]; exact hC
  · rw [abs_div, div_le_iff₀ (abs_pos.2 hab)]; exact h

/-- `m² e^{−cm} ≤ m / c`. -/
theorem sq_mul_exp_le {c m : ℝ} (hc : 0 < c) (hm : 0 ≤ m) :
    m ^ 2 * Real.exp (-c * m) ≤ m / c := by
  rw [le_div_iff₀ hc]
  have h1 : c * m ≤ Real.exp (c * m) := by linarith [Real.add_one_le_exp (c * m)]
  have h2 : Real.exp (-c * m) * Real.exp (c * m) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 ≤ Real.exp (-c * m) := (Real.exp_pos _).le
  calc m ^ 2 * Real.exp (-c * m) * c = m * (Real.exp (-c * m) * (c * m)) := by ring
    _ ≤ m * (Real.exp (-c * m) * Real.exp (c * m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) hm
    _ = m := by rw [h2, mul_one]

/-!
## The function `φ(w) = w(1+w)A₁(w)`
-/

variable (ν : FiniteMeasure unitInterval)

/-- `φ(w) = w(1+w)A₁(w)`; its difference quotients are the singular drift terms. -/
def ratioPhi (w : ℝ) : ℝ := w * (1 + w) * lkerInt1 ν w

theorem hasDerivAt_ratioPhi {w : ℝ} (hw : -1 < w) :
    HasDerivAt (ratioPhi ν) ((1 + 2 * w) * lkerInt1 ν w + w * (1 + w) * lkerInt2 ν w) w := by
  have h := ((hasDerivAt_id' w).mul ((hasDerivAt_id' w).const_add 1)).mul
    (hasDerivAt_lkerInt1 ν hw)
  show HasDerivAt (fun w => w * (1 + w) * lkerInt1 ν w) _ w
  convert h using 1
  simp only [Pi.mul_apply]
  ring

theorem one_add_mul_ge_of_mem {ε M w t : ℝ} (hε1 : ε ≤ 1) (hw : w ∈ Icc (ε - 1) M)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ε ≤ 1 + w * t :=
  one_add_mul_ge hε1 hw.1 ht0 ht1

/-- `φ` is Lipschitz on `[ε−1, M]` with constant `2(1+M)²/ε² · ν[0,1]`. -/
theorem abs_ratioPhi_sub_le {ε M : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 0 ≤ M) {a b : ℝ}
    (ha : a ∈ Icc (ε - 1) M) (hb : b ∈ Icc (ε - 1) M) :
    |ratioPhi ν a - ratioPhi ν b| ≤
      2 * (1 + M) ^ 2 / ε ^ 2 * (ν : Measure unitInterval).real univ * |a - b| := by
  set m := (ν : Measure unitInterval).real univ
  have hm : 0 ≤ m := measureReal_nonneg
  have hder : ∀ w ∈ Icc (ε - 1) M, HasDerivWithinAt (ratioPhi ν)
      ((1 + 2 * w) * lkerInt1 ν w + w * (1 + w) * lkerInt2 ν w) (Icc (ε - 1) M) w :=
    fun w hw => (hasDerivAt_ratioPhi ν (by linarith [hw.1])).hasDerivWithinAt
  have hbd : ∀ w ∈ Icc (ε - 1) M,
      ‖(1 + 2 * w) * lkerInt1 ν w + w * (1 + w) * lkerInt2 ν w‖ ≤ 2 * (1 + M) ^ 2 / ε ^ 2 * m := by
    intro w hw
    have hdom : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ε ≤ 1 + w * t := fun t ht0 ht1 =>
      one_add_mul_ge_of_mem hε1 hw ht0 ht1
    have h1 := abs_lkerInt1_le ν hε hdom
    have h2 := abs_lkerInt2_le ν hε hdom
    have hw1 : |1 + 2 * w| ≤ (1 + M) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [hw.1, hw.2]
    have hw2 : |w * (1 + w)| ≤ (1 + M) ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [hw.1, hw.2]
    have hεi : 1 / ε ≤ 1 / ε ^ 2 := by
      rw [div_le_div_iff₀ hε (by positivity)]; nlinarith
    rw [Real.norm_eq_abs]
    calc |(1 + 2 * w) * lkerInt1 ν w + w * (1 + w) * lkerInt2 ν w|
        ≤ |1 + 2 * w| * |lkerInt1 ν w| + |w * (1 + w)| * |lkerInt2 ν w| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ (1 + M) ^ 2 * (1 / ε * m) + (1 + M) ^ 2 * (1 / ε ^ 2 * m) := by
          gcongr
      _ ≤ (1 + M) ^ 2 * (1 / ε ^ 2 * m) + (1 + M) ^ 2 * (1 / ε ^ 2 * m) := by
          gcongr
      _ = 2 * (1 + M) ^ 2 / ε ^ 2 * m := by ring
  have := (convex_Icc (ε - 1) M).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd hb ha
  simpa only [Real.norm_eq_abs] using this

/-!
## Regrouping the closed form
-/

/-- `Σ_l (−y_j + y_l)⁻¹ = −Σ_l (y_j − y_l)⁻¹`. -/
theorem sum_erase_neg_eq {q : ℕ} (y : Fin q → ℝ) (j : Fin q) :
    ∑ l ∈ Finset.univ.erase j, 1 / (-y j - -y l) = -∑ l ∈ Finset.univ.erase j, 1 / (y j - y l) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show -y j - -y l = -(y j - y l) by ring, one_div_neg_eq_neg_one_div]

/-- **The regrouped closed form** (pure algebra, any `A₁, A₂`): with `φ(w) = w(1+w)A₁(w)` and
`w_j = −y_j`, the bracket of `dualGenerator_ratioOn` is quadratic part + linear part +
same-species and cross difference quotients of `φ`. -/
theorem closedForm_split {q : ℕ} (z : DualCoord q) (A1 A2 : ℝ → ℝ) :
    let φ : ℝ → ℝ := fun w => w * (1 + w) * A1 w
    ((∑ i, (z.1 i * (1 + z.1 i) * (A1 (z.1 i) ^ 2 + A2 (z.1 i)) +
        dualDriftX z i * A1 (z.1 i))) +
      ∑ j, (z.2 j * (1 - z.2 j) * (A1 (-z.2 j) ^ 2 - A2 (-z.2 j)) +
        dualDriftY z j * A1 (-z.2 j))) =
    ((∑ i, z.1 i * (1 + z.1 i) * A1 (z.1 i) ^ 2) + ∑ j, z.2 j * (1 - z.2 j) * A1 (-z.2 j) ^ 2) +
      ((∑ i, (z.1 i * (1 + z.1 i) * A2 (z.1 i) + (1 + 2 * z.1 i) * A1 (z.1 i))) +
        ∑ j, (-(z.2 j * (1 - z.2 j) * A2 (-z.2 j)) + (1 - 2 * z.2 j) * A1 (-z.2 j))) +
      (∑ i, ∑ k, (φ (z.1 i) - φ (z.1 k)) / (z.1 i - z.1 k)) +
      (∑ j, ∑ l, (φ (-z.2 j) - φ (-z.2 l)) / (-z.2 j - -z.2 l)) -
      2 * ∑ i, ∑ j, (φ (z.1 i) - φ (-z.2 j)) / (z.1 i - -z.2 j) := by
  intro φ
  have hx : ∀ i, z.1 i * (1 + z.1 i) * (A1 (z.1 i) ^ 2 + A2 (z.1 i)) +
      dualDriftX z i * A1 (z.1 i) =
      z.1 i * (1 + z.1 i) * A1 (z.1 i) ^ 2 +
        (z.1 i * (1 + z.1 i) * A2 (z.1 i) + (1 + 2 * z.1 i) * A1 (z.1 i)) +
        2 * (φ (z.1 i) * ∑ k ∈ Finset.univ.erase i, 1 / (z.1 i - z.1 k)) -
        2 * (φ (z.1 i) * ∑ j, 1 / (z.1 i + z.2 j)) := fun i => by
    unfold dualDriftX; simp only [φ]; ring
  have hy : ∀ j, z.2 j * (1 - z.2 j) * (A1 (-z.2 j) ^ 2 - A2 (-z.2 j)) +
      dualDriftY z j * A1 (-z.2 j) =
      z.2 j * (1 - z.2 j) * A1 (-z.2 j) ^ 2 +
        (-(z.2 j * (1 - z.2 j) * A2 (-z.2 j)) + (1 - 2 * z.2 j) * A1 (-z.2 j)) +
        2 * (φ (-z.2 j) * ∑ l ∈ Finset.univ.erase j, 1 / (-z.2 j - -z.2 l)) +
        2 * (φ (-z.2 j) * ∑ i, 1 / (z.1 i + z.2 j)) := fun j => by
    unfold dualDriftY; rw [sum_erase_neg_eq]; simp only [φ]; ring
  have hc : ∑ i, φ (z.1 i) * ∑ j, 1 / (z.1 i + z.2 j) -
      ∑ j, φ (-z.2 j) * ∑ i, 1 / (z.1 i + z.2 j) =
      ∑ i, ∑ j, (φ (z.1 i) - φ (-z.2 j)) / (z.1 i - -z.2 j) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j i => φ (-z.2 j) * (1 / (z.1 i + z.2 j))),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_neg_eq_add]; ring
  have hsx := two_mul_sum_erase_eq (fun i => φ (z.1 i)) z.1
  have hsy := two_mul_sum_erase_eq (fun j => φ (-z.2 j)) fun j => -z.2 j
  rw [Finset.sum_congr rfl fun i _ => hx i, Finset.sum_congr rfl fun j _ => hy j]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← hsx, ← hsy, ← hc]
  ring

/-!
## The bound
-/

theorem abs_sum_le_card {q : ℕ} (f : Fin q → ℝ) {C : ℝ} (h : ∀ i, |f i| ≤ C) :
    |∑ i, f i| ≤ q * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => h i).trans ?_)
  simp

theorem abs_sum_sum_le_card {q : ℕ} (f : Fin q → Fin q → ℝ) {C : ℝ}
    (h : ∀ i k, |f i k| ≤ C) : |∑ i, ∑ k, f i k| ≤ q ^ 2 * C := by
  refine (abs_sum_le_card _ fun i => abs_sum_le_card _ (h i)).trans ?_
  rw [sq, mul_assoc]

/-- **`|𝒟_q F_·(ν)(z)| ≤ |D₀|/2 · (6q + 8q²)(1+M)²/ε² · ν[0,1]`** on
`{z ∈ 𝒞_q : x_i ≤ M, y_j ≤ 1 − ε}`, for every finite measure `ν` (corners and collisions
included). -/
theorem abs_dualGenerator_ratioOn_le_mass (D0 : ℝ) {q : ℕ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {z : DualCoord q} (hz : z ∈ dualChamber q) (hxM : ∀ i, z.1 i ≤ M)
    (hyε : ∀ j, z.2 j ≤ 1 - ε) :
    |dualGenerator D0 (ratioOn ν) z| ≤
      |D0| / 2 * ((6 * q + 8 * q ^ 2) * ((1 + M) ^ 2 / ε ^ 2)) *
        (ν : Measure unitInterval).real univ := by
  set m := (ν : Measure unitInterval).real univ with hmdef
  have hm : 0 ≤ m := measureReal_nonneg
  set Λ := (1 + M) ^ 2 / ε ^ 2 with hΛdef
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  have hΛ1 : (1 + M) ^ 2 ≤ Λ := le_div_self (by positivity) hε2 hε21
  have hM1 : 1 ≤ (1 + M) ^ 2 := by nlinarith
  have hΛε : 1 / ε ≤ Λ := by
    rw [hΛdef, div_le_div_iff₀ hε hε2]; nlinarith
  have hΛ0 : 0 ≤ Λ := by positivity
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z.1 z.2 from hz)
  have hx : ∀ i, 0 < z.1 i := hz.2.2.1
  have hy0 : ∀ j, 0 < z.2 j := fun j => (hz.2.2.2 j).1
  have hy1 : ∀ j, 0 < 1 - z.2 j := fun j => by linarith [(hz.2.2.2 j).2]
  have hyε' : ∀ j, ε ≤ 1 - z.2 j := fun j => by linarith [hyε j]
  have hxI : ∀ i, z.1 i ∈ Icc (ε - 1) M := fun i => ⟨by linarith [hx i], hxM i⟩
  have hyI : ∀ j, -z.2 j ∈ Icc (ε - 1) M := fun j => ⟨by linarith [hyε j], by linarith [hy0 j]⟩
  have hDQ : ∀ a b, a ∈ Icc (ε - 1) M → b ∈ Icc (ε - 1) M →
      |(ratioPhi ν a - ratioPhi ν b) / (a - b)| ≤ 2 * Λ * m := fun a b ha hb =>
    abs_div_sub_le (by positivity) (by
      have := abs_ratioPhi_sub_le ν hε hε1 hM ha hb
      rw [hΛdef]; convert this using 2; ring)
  -- one-coordinate bounds
  have hA1x : ∀ i, |lkerInt1 ν (z.1 i)| ≤ m := fun i => by
    simpa only [div_one, one_mul] using abs_lkerInt1_le ν one_pos (dom_nonneg_x (hx i).le)
  have hA2x : ∀ i, |lkerInt2 ν (z.1 i)| ≤ m := fun i => by
    simpa only [one_pow, div_one, one_mul] using
      abs_lkerInt2_le ν one_pos (dom_nonneg_x (hx i).le)
  have hA1y : ∀ j, |lkerInt1 ν (-z.2 j)| ≤ m / (1 - z.2 j) := fun j => by
    have := abs_lkerInt1_le ν (hy1 j) (dom_neg_y (hy0 j).le)
    rwa [one_div_mul_eq_div] at this
  have hA2y : ∀ j, |lkerInt2 ν (-z.2 j)| ≤ m / (1 - z.2 j) ^ 2 := fun j => by
    have := abs_lkerInt2_le ν (hy1 j) (dom_neg_y (hy0 j).le)
    rwa [one_div_mul_eq_div] at this
  set F := ratioOn ν z with hFdef
  have hF : 0 < F ∧ F ≤ 1 := transmissionRatio_mem_vec hr ν
  have hFx : ∀ i, F ≤ Real.exp (-(z.1 i / (1 + z.1 i)) * m) := fun i =>
    (transmissionRatio_le_exp_mass hr i ν).trans (Real.exp_le_exp.2 (by
      have := hy0 i; nlinarith))
  have hFy : ∀ j, F ≤ Real.exp (-(z.2 j) * m) := fun j =>
    (transmissionRatio_le_exp_mass hr j ν).trans (Real.exp_le_exp.2 (by
      have : 0 ≤ z.1 j / (1 + z.1 j) := by have := hx j; positivity
      nlinarith))
  -- the quadratic part, absorbed by `F`
  have hQx : ∀ i, F * (z.1 i * (1 + z.1 i) * lkerInt1 ν (z.1 i) ^ 2) ≤ Λ * m := fun i => by
    have hxi := hx i
    have hc : 0 < z.1 i / (1 + z.1 i) := by positivity
    have hsq : lkerInt1 ν (z.1 i) ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA1x i) 2
    have he := sq_mul_exp_le hc hm
    calc F * (z.1 i * (1 + z.1 i) * lkerInt1 ν (z.1 i) ^ 2)
        ≤ Real.exp (-(z.1 i / (1 + z.1 i)) * m) * (z.1 i * (1 + z.1 i) * m ^ 2) := by
          gcongr
          · exact hFx i
      _ = z.1 i * (1 + z.1 i) * (m ^ 2 * Real.exp (-(z.1 i / (1 + z.1 i)) * m)) := by ring
      _ ≤ z.1 i * (1 + z.1 i) * (m / (z.1 i / (1 + z.1 i))) := by gcongr
      _ = (1 + z.1 i) ^ 2 * m := by field_simp
      _ ≤ (1 + M) ^ 2 * m := by gcongr; linarith [hxM i]
      _ ≤ Λ * m := by gcongr
  have hQy : ∀ j, F * (z.2 j * (1 - z.2 j) * lkerInt1 ν (-z.2 j) ^ 2) ≤ Λ * m := fun j => by
    have hyj := hy0 j
    have hyj1 := hy1 j
    have hsq : lkerInt1 ν (-z.2 j) ^ 2 ≤ (m / (1 - z.2 j)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA1y j) 2
    have he := sq_mul_exp_le hyj hm
    calc F * (z.2 j * (1 - z.2 j) * lkerInt1 ν (-z.2 j) ^ 2)
        ≤ Real.exp (-(z.2 j) * m) * (z.2 j * (1 - z.2 j) * (m / (1 - z.2 j)) ^ 2) := by
          gcongr
          · exact hFy j
      _ = z.2 j / (1 - z.2 j) * (m ^ 2 * Real.exp (-(z.2 j) * m)) := by field_simp
      _ ≤ z.2 j / (1 - z.2 j) * (m / z.2 j) := by gcongr
      _ = 1 / (1 - z.2 j) * m := by field_simp
      _ ≤ 1 / ε * m := by gcongr; exact hyε' j
      _ ≤ Λ * m := by gcongr
  -- the linear part
  have hLx : ∀ i, |z.1 i * (1 + z.1 i) * lkerInt2 ν (z.1 i) + (1 + 2 * z.1 i) * lkerInt1 ν (z.1 i)|
      ≤ 2 * Λ * m := fun i => by
    have hxi := hx i
    have hxMi := hxM i
    calc _ ≤ |z.1 i * (1 + z.1 i)| * |lkerInt2 ν (z.1 i)| +
          |1 + 2 * z.1 i| * |lkerInt1 ν (z.1 i)| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul (z.1 i * (1 + z.1 i)), abs_mul (1 + 2 * z.1 i)])
      _ ≤ (1 + M) ^ 2 * m + (1 + M) ^ 2 * m := by
          gcongr
          · rw [abs_of_pos (by positivity)]; nlinarith
          · exact hA2x i
          · rw [abs_of_pos (by positivity)]; nlinarith
          · exact hA1x i
      _ ≤ 2 * Λ * m := by nlinarith
  have hLy : ∀ j, |-(z.2 j * (1 - z.2 j) * lkerInt2 ν (-z.2 j)) +
      (1 - 2 * z.2 j) * lkerInt1 ν (-z.2 j)| ≤ 2 * Λ * m := fun j => by
    have hyj := hy0 j
    have hyj1 := hy1 j
    have hyy : z.2 j < 1 := by linarith
    calc _ ≤ |z.2 j * (1 - z.2 j)| * |lkerInt2 ν (-z.2 j)| +
          |1 - 2 * z.2 j| * |lkerInt1 ν (-z.2 j)| :=
          (abs_add_le _ _).trans_eq (by
            rw [abs_neg, abs_mul (z.2 j * (1 - z.2 j)), abs_mul (1 - 2 * z.2 j)])
      _ ≤ (z.2 j * (1 - z.2 j)) * (m / (1 - z.2 j) ^ 2) + 1 * (m / (1 - z.2 j)) := by
          gcongr
          · rw [abs_of_pos (by positivity)]
          · exact hA2y j
          · rw [abs_le]; constructor <;> linarith
          · exact hA1y j
      _ = (z.2 j + 1) * (1 / (1 - z.2 j) * m) := by field_simp
      _ ≤ 2 * (1 / ε * m) := by
          gcongr
          · linarith
          · exact hyε' j
      _ ≤ 2 * Λ * m := by nlinarith
  -- assemble
  rw [dualGenerator_ratioOn ν D0 (dualChamber_subset_ratioOpen hz), ← hFdef,
    closedForm_split z (lkerInt1 ν) (lkerInt2 ν)]
  simp only
  set Qx := ∑ i, z.1 i * (1 + z.1 i) * lkerInt1 ν (z.1 i) ^ 2
  set Qy := ∑ j, z.2 j * (1 - z.2 j) * lkerInt1 ν (-z.2 j) ^ 2
  set Lx := ∑ i, (z.1 i * (1 + z.1 i) * lkerInt2 ν (z.1 i) + (1 + 2 * z.1 i) * lkerInt1 ν (z.1 i))
  set Ly := ∑ j, (-(z.2 j * (1 - z.2 j) * lkerInt2 ν (-z.2 j)) +
    (1 - 2 * z.2 j) * lkerInt1 ν (-z.2 j))
  set Sx := ∑ i, ∑ k, (ratioPhi ν (z.1 i) - ratioPhi ν (z.1 k)) / (z.1 i - z.1 k)
  set Sy := ∑ j, ∑ l, (ratioPhi ν (-z.2 j) - ratioPhi ν (-z.2 l)) / (-z.2 j - -z.2 l)
  set Cr := ∑ i, ∑ j, (ratioPhi ν (z.1 i) - ratioPhi ν (-z.2 j)) / (z.1 i - -z.2 j)
  have hQx0 : 0 ≤ Qx := Finset.sum_nonneg fun i _ => by have := hx i; positivity
  have hQy0 : 0 ≤ Qy := Finset.sum_nonneg fun j _ => by
    have := hy0 j; have := hy1 j; positivity
  have hFQx : F * Qx ≤ q * (Λ * m) := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum fun i _ => hQx i).trans (by simp)
  have hFQy : F * Qy ≤ q * (Λ * m) := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum fun j _ => hQy j).trans (by simp)
  have hLx' : |Lx| ≤ q * (2 * Λ * m) := abs_sum_le_card _ hLx
  have hLy' : |Ly| ≤ q * (2 * Λ * m) := abs_sum_le_card _ hLy
  have h2 : 0 ≤ 2 * Λ * m := by positivity
  have hSx : |Sx| ≤ q ^ 2 * (2 * Λ * m) :=
    abs_sum_sum_le_card _ fun i k => hDQ _ _ (hxI i) (hxI k)
  have hSy : |Sy| ≤ q ^ 2 * (2 * Λ * m) :=
    abs_sum_sum_le_card _ fun j l => hDQ _ _ (hyI j) (hyI l)
  have hCr : |Cr| ≤ q ^ 2 * (2 * Λ * m) :=
    abs_sum_sum_le_card _ fun i j => hDQ _ _ (hxI i) (hyI j)
  have hrest : |Lx + Ly + Sx + Sy - 2 * Cr| ≤
      q * (2 * Λ * m) + q * (2 * Λ * m) + q ^ 2 * (2 * Λ * m) + q ^ 2 * (2 * Λ * m) +
        2 * (q ^ 2 * (2 * Λ * m)) := by
    have e1 := abs_sub (Lx + Ly + Sx + Sy) (2 * Cr)
    have e2 := abs_add_le (Lx + Ly + Sx) Sy
    have e3 := abs_add_le (Lx + Ly) Sx
    have e4 := abs_add_le Lx Ly
    rw [abs_mul, abs_two] at e1
    linarith
  have hS : F * |Qx + Qy + (Lx + Ly) + Sx + Sy - 2 * Cr| ≤
      (6 * q + 8 * q ^ 2) * Λ * m := by
    have e : Qx + Qy + (Lx + Ly) + Sx + Sy - 2 * Cr = (Qx + Qy) + (Lx + Ly + Sx + Sy - 2 * Cr) := by
      ring
    rw [e]
    have hFr : F * |Lx + Ly + Sx + Sy - 2 * Cr| ≤ |Lx + Ly + Sx + Sy - 2 * Cr| :=
      mul_le_of_le_one_left (abs_nonneg _) hF.2
    calc F * |Qx + Qy + (Lx + Ly + Sx + Sy - 2 * Cr)|
        ≤ F * (|Qx + Qy| + |Lx + Ly + Sx + Sy - 2 * Cr|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hF.1.le
      _ = F * Qx + F * Qy + F * |Lx + Ly + Sx + Sy - 2 * Cr| := by
          rw [abs_of_nonneg (add_nonneg hQx0 hQy0)]; ring
      _ ≤ _ := by nlinarith
  rw [abs_mul, abs_mul, abs_div, abs_two, abs_of_pos hF.1, mul_assoc]
  calc |D0| / 2 * (F * |Qx + Qy + (Lx + Ly) + Sx + Sy - 2 * Cr|)
      ≤ |D0| / 2 * ((6 * q + 8 * q ^ 2) * Λ * m) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

end BlockBand.Transmission.LawDuality
