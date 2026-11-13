module

public import BlockBand.Transmission.Dual.ExistsCalc

/-!
# Calculus of the face test functions

For `δ > 0`, `C, T ∈ ℝ` the test function on `ℝ × ℝ¹`
`faceFun δ C T (t, z) = −log(z + δ) + (z + δ) + C (T − t)`
is `C^∞` on `ℝ × {z > −δ}`, and its contract Itô drift is
`−C + b (1 − 1/(z+δ)) + ½ a / (z+δ)²` (`itoDrift_faceFun`). Since `−log w + w ≥ 1`, it is
nonnegative for `t ≤ T`, `C ≥ 0`, `z ≥ 0`.

**`faceDrift_le`** (the 1D entrance inequality): if `z ≥ 0`, `a ≤ 2z(b + Kz)` (i.e.
`a/(2z) − b ≤ Kz`) and `b ≥ c − Mz`, `b ≤ B`, then with `C = K + M + max B 0`
`−C + b(1 − 1/(z+δ)) + ½ a/(z+δ)² ≤ −cδ/(z+δ)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual.Exists
open scoped NNReal

/-- The face test function `−log(z + δ) + (z + δ) + C (T − t)`. -/
def faceFun (δ C T : ℝ) (p : ℝ × (Fin 1 → ℝ)) : ℝ :=
  -Real.log (p.2 0 + δ) + (p.2 0 + δ) + C * (T - p.1)

/-- The open set `{z > −δ}`. -/
def faceU (δ : ℝ) : Set (Fin 1 → ℝ) := {y | -δ < y 0}

theorem isOpen_faceU (δ : ℝ) : IsOpen (faceU δ) := isOpen_lt continuous_const (continuous_apply 0)

theorem measurable_faceFun (δ C T : ℝ) : Measurable (faceFun δ C T) := by
  unfold faceFun; fun_prop

theorem contDiffOn_faceFun (δ C T : ℝ) : ContDiffOn ℝ 2 (faceFun δ C T) (univ ×ˢ faceU δ) := by
  have h0 : ContDiff ℝ 2 fun p : ℝ × (Fin 1 → ℝ) => p.2 0 + δ :=
    ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd).add contDiff_const
  have h1 : ContDiff ℝ 2 fun p : ℝ × (Fin 1 → ℝ) => C * (T - p.1) :=
    contDiff_const.mul (contDiff_const.sub contDiff_fst)
  refine ((h0.contDiffOn.log fun p hp => ?_).neg.add h0.contDiffOn).add h1.contDiffOn
  have : -δ < p.2 0 := hp.2
  linarith

theorem contDiffAt_faceFun {δ C T : ℝ} {p : ℝ × (Fin 1 → ℝ)} (hp : -δ < p.2 0) :
    ContDiffAt ℝ 2 (faceFun δ C T) p :=
  (contDiffOn_faceFun δ C T).contDiffAt (((isOpen_univ.prod (isOpen_faceU δ))).mem_nhds
    ⟨mem_univ _, hp⟩)

/-- The one-dimensional profile along the space line. -/
theorem hasDerivAt_prof (w K : ℝ) {r : ℝ} (hr : 0 < w + r) :
    HasDerivAt (fun r : ℝ => -Real.log (w + r) + (w + r) + K) (-(w + r)⁻¹ + 1) r := by
  have h1 : HasDerivAt (fun r : ℝ => w + r) 1 r := (hasDerivAt_id r).const_add w
  have h2 := (h1.log hr.ne').neg.add h1
  simpa [div_eq_mul_inv] using h2.add_const K

theorem deriv_deriv_prof (w K : ℝ) (hw : 0 < w) :
    deriv (deriv fun r : ℝ => -Real.log (w + r) + (w + r) + K) 0 = (w ^ 2)⁻¹ := by
  have hev : deriv (fun r : ℝ => -Real.log (w + r) + (w + r) + K) =ᶠ[𝓝 0]
      fun r => -(w + r)⁻¹ + 1 := by
    have hc : ContinuousAt (fun r : ℝ => w + r) 0 := (continuous_const.add continuous_id).continuousAt
    have : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < w + r := hc.eventually (lt_mem_nhds (by simpa using hw))
    filter_upwards [this] with r hr using (hasDerivAt_prof w K hr).deriv
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun r : ℝ => w + r) 1 0 := (hasDerivAt_id 0).const_add w
  have h2 : HasDerivAt (fun r : ℝ => -(w + r)⁻¹ + 1) ((w ^ 2)⁻¹) 0 := by
    have := ((h1.inv (by simpa using hw.ne')).neg).add_const 1
    convert this using 1
    rw [add_zero, neg_div, neg_neg, one_div]
  exact h2.deriv

/-- **The contract Itô drift of the face test function.** -/
theorem itoDrift_faceFun {δ C T : ℝ} {y : Fin 1 → ℝ} (hy : 0 < y 0 + δ) (t : ℝ≥0)
    (b : Fin 1 → ℝ) (a : Matrix (Fin 1) (Fin 1) ℝ) :
    itoDrift (faceFun δ C T) y t b a =
      -C + b 0 * (1 - 1 / (y 0 + δ)) + 1 / 2 * a 0 0 * (1 / (y 0 + δ) ^ 2) := by
  have hc : ContDiffAt ℝ 2 (faceFun δ C T) ((t : ℝ), y) :=
    contDiffAt_faceFun (by simp only; linarith)
  have hd : DifferentiableAt ℝ (faceFun δ C T) ((t : ℝ), y) := hc.differentiableAt (by norm_num)
  have ht : partialTime (faceFun δ C T) ((t : ℝ), y) = -C := by
    unfold partialTime
    rw [fderiv_eq_deriv_line _ hd]
    have e : (fun r : ℝ => faceFun δ C T (((t : ℝ), y) + r • ((1 : ℝ), (0 : Fin 1 → ℝ)))) =
        fun r => (-Real.log (y 0 + δ) + (y 0 + δ) + C * (T - t)) + (-C) * r := by
      funext r; simp only [faceFun, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, mul_one, smul_zero, add_zero]; ring
    rw [e]
    have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (-C)).const_add
      (-Real.log (y 0 + δ) + (y 0 + δ) + C * (T - t))
    rw [mul_one] at h
    exact h.deriv
  have eline : (fun r : ℝ => faceFun δ C T (((t : ℝ), y) + r • ((0 : ℝ), Pi.single 0 1))) =
      fun r => -Real.log ((y 0 + δ) + r) + ((y 0 + δ) + r) + C * (T - t) := by
    funext r
    simp only [faceFun, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      mul_zero, add_zero, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, mul_one]
    ring_nf
  have hs : partialSpace (faceFun δ C T) ((t : ℝ), y) 0 = -(y 0 + δ)⁻¹ + 1 := by
    unfold partialSpace
    rw [fderiv_eq_deriv_line _ hd, eline]
    simpa using (hasDerivAt_prof (y 0 + δ) (C * (T - t)) (r := 0) (by simpa using hy)).deriv
  have hss : partialSpace2 (faceFun δ C T) ((t : ℝ), y) 0 0 = ((y 0 + δ) ^ 2)⁻¹ := by
    unfold partialSpace2
    rw [fderiv_fderiv_eq_deriv_line _ hc, eline]
    exact deriv_deriv_prof _ _ hy
  simp only [itoDrift, Fin.sum_univ_one, ht, hs, hss]
  ring

/-- **The one-dimensional entrance inequality for the drift.** -/
theorem faceDrift_le {z δ a b c K M B : ℝ} (hz : 0 ≤ z) (hδ : 0 < δ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (ha : a ≤ 2 * z * (b + K * z)) (hb : c - M * z ≤ b) (hB : b ≤ B) :
    -(K + M + max B 0) + b * (1 - 1 / (z + δ)) + 1 / 2 * a * (1 / (z + δ) ^ 2) ≤
      -(c * δ / (z + δ) ^ 2) := by
  have hw : 0 < z + δ := by linarith
  have hw2 : 0 < (z + δ) ^ 2 := by positivity
  have s1 : 1 / 2 * a - b * (z + δ) ≤ K * z ^ 2 - b * δ := by nlinarith [ha]
  have s2 : -(b * δ) ≤ -((c - M * z) * δ) := by nlinarith [mul_le_mul_of_nonneg_right hb hδ.le]
  have s3 : K * z ^ 2 + M * z * δ ≤ (K + M) * (z + δ) ^ 2 := by
    nlinarith [mul_nonneg hK (mul_nonneg hδ.le (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      hz) hδ.le)), mul_nonneg hM (add_nonneg (add_nonneg (mul_nonneg hz hz)
      (mul_nonneg hz hδ.le)) (mul_nonneg hδ.le hδ.le))]
  have key : 1 / 2 * a - b * (z + δ) ≤ (K + M) * (z + δ) ^ 2 - c * δ := by nlinarith
  have hBm : b ≤ max B 0 := hB.trans (le_max_left _ _)
  have e : b * (1 - 1 / (z + δ)) + 1 / 2 * a * (1 / (z + δ) ^ 2) =
      b + (1 / 2 * a - b * (z + δ)) / (z + δ) ^ 2 := by
    field_simp
    ring
  have e2 : ((K + M) * (z + δ) ^ 2 - c * δ) / (z + δ) ^ 2 = (K + M) - c * δ / (z + δ) ^ 2 := by
    field_simp
  have h3 : (1 / 2 * a - b * (z + δ)) / (z + δ) ^ 2 ≤ (K + M) - c * δ / (z + δ) ^ 2 := by
    rw [← e2]; exact div_le_div_of_nonneg_right key hw2.le
  linarith

/-- The face test function is bounded below by `C (T − t)` (`−log w + w ≥ 1`). -/
theorem faceFun_ge {δ C T : ℝ} {p : ℝ × (Fin 1 → ℝ)} (hp : 0 < p.2 0 + δ) :
    1 + C * (T - p.1) ≤ faceFun δ C T p := by
  unfold faceFun
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- Lower bound by `−log` near the face. -/
theorem neg_log_le_faceFun {δ C T : ℝ} {p : ℝ × (Fin 1 → ℝ)} (hp : 0 < p.2 0 + δ)
    (hCT : 0 ≤ C * (T - p.1)) : -Real.log (p.2 0 + δ) ≤ faceFun δ C T p := by
  unfold faceFun
  linarith

end BlockBand.Transmission.DualEntrance
