module
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A `C²` cutoff of `−log`

`cutH ε x = −log (cutS ε x)` with `cutS ε x = x T(x) + (ε/4)(1 − T(x))` and `T` a smooth
transition from `0` (at `x ≤ ε/4`) to `1` (at `x ≥ ε/2`). For `0 < ε`:
* `contDiff_cutH`: `cutH ε` is `C²` on `ℝ` (`cutS ε ≥ ε/4 > 0`);
* `cutH_eq`: `cutH ε x = −log x` for `x ≥ ε/2`, and the derivative formulas
  `fderiv_cutH`, `fderiv_fderiv_cutH` (`−v/a`, `v w/a²`) at `a > ε/2`;
* `cutH_le`: `cutH ε x ≤ −log (ε/4)`; `neg_log_le_cutH`: `−log (max x (ε/4)) ≤ cutH ε x`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Real Filter Topology Set

/-- The transition `T`. -/
def cutT (ε x : ℝ) : ℝ := smoothTransition ((x - ε / 4) / (ε / 4))

/-- The positive regularization `cutS ε x`. -/
def cutS (ε x : ℝ) : ℝ := x * cutT ε x + ε / 4 * (1 - cutT ε x)

/-- The cutoff of `−log`. -/
def cutH (ε x : ℝ) : ℝ := -Real.log (cutS ε x)

variable {ε : ℝ}

theorem cutT_eq_one (hε : 0 < ε) {x : ℝ} (hx : ε / 2 ≤ x) : cutT ε x = 1 := by
  refine smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (by positivity)]; linarith

theorem cutT_eq_zero (hε : 0 < ε) {x : ℝ} (hx : x ≤ ε / 4) : cutT ε x = 0 := by
  refine smoothTransition.zero_of_nonpos ?_
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem cutS_ge (hε : 0 < ε) (x : ℝ) : ε / 4 ≤ cutS ε x := by
  unfold cutS
  rcases le_or_gt x (ε / 4) with hx | hx
  · rw [cutT_eq_zero hε hx]; simp
  · nlinarith [smoothTransition.nonneg ((x - ε / 4) / (ε / 4)),
      smoothTransition.le_one ((x - ε / 4) / (ε / 4)), show cutT ε x =
        smoothTransition ((x - ε / 4) / (ε / 4)) from rfl]

theorem cutS_le_max (x : ℝ) : cutS ε x ≤ max x (ε / 4) := by
  unfold cutS
  have h0 := smoothTransition.nonneg ((x - ε / 4) / (ε / 4))
  have h1 := smoothTransition.le_one ((x - ε / 4) / (ε / 4))
  have e : cutT ε x = smoothTransition ((x - ε / 4) / (ε / 4)) := rfl
  rw [e]
  nlinarith [le_max_left x (ε / 4), le_max_right x (ε / 4)]

theorem cutS_eq (hε : 0 < ε) {x : ℝ} (hx : ε / 2 ≤ x) : cutS ε x = x := by
  rw [cutS, cutT_eq_one hε hx]; ring

theorem contDiff_cutH (hε : 0 < ε) : ContDiff ℝ 2 (cutH ε) := by
  have hT : ContDiff ℝ 2 (cutT ε) :=
    smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hS : ContDiff ℝ 2 (cutS ε) :=
    (contDiff_id.mul hT).add (contDiff_const.mul (contDiff_const.sub hT))
  exact (hS.log fun x => (lt_of_lt_of_le (by positivity) (cutS_ge hε x)).ne').neg

theorem cutH_eq (hε : 0 < ε) {x : ℝ} (hx : ε / 2 ≤ x) : cutH ε x = -Real.log x := by
  rw [cutH, cutS_eq hε hx]

theorem cutH_le (hε : 0 < ε) (x : ℝ) : cutH ε x ≤ -Real.log (ε / 4) := by
  unfold cutH
  have := Real.log_le_log (by positivity) (cutS_ge hε x)
  linarith

theorem neg_log_le_cutH (hε : 0 < ε) (x : ℝ) : -Real.log (max x (ε / 4)) ≤ cutH ε x := by
  unfold cutH
  have := Real.log_le_log (lt_of_lt_of_le (by positivity) (cutS_ge hε x)) (cutS_le_max x)
  linarith

theorem cutH_eventuallyEq (hε : 0 < ε) {a : ℝ} (ha : ε / 2 < a) :
    cutH ε =ᶠ[𝓝 a] fun x => -Real.log x :=
  (eventually_gt_nhds ha).mono fun _ hx => cutH_eq hε hx.le

theorem fderiv_neg_log {x : ℝ} (hx : 0 < x) :
    fderiv ℝ (fun y => -Real.log y) x = (-x⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  have h : HasDerivAt (fun y => -Real.log y) (-x⁻¹) x := (Real.hasDerivAt_log hx.ne').neg
  rw [h.hasFDerivAt.fderiv]
  ext; simp

theorem fderiv_cutH (hε : 0 < ε) {a : ℝ} (ha : ε / 2 < a) (v : ℝ) :
    fderiv ℝ (cutH ε) a v = -v / a := by
  rw [(cutH_eventuallyEq hε ha).fderiv_eq, fderiv_neg_log (by linarith)]
  simp; ring

theorem fderiv_fderiv_cutH (hε : 0 < ε) {a : ℝ} (ha : ε / 2 < a) (v w : ℝ) :
    fderiv ℝ (fderiv ℝ (cutH ε)) a v w = v * w / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have h1 : fderiv ℝ (cutH ε) =ᶠ[𝓝 a] fun x => (-x⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
    filter_upwards [(cutH_eventuallyEq hε ha).fderiv (𝕜 := ℝ), eventually_gt_nhds ha0] with x hx hx0
    rw [hx, fderiv_neg_log hx0]
  have hd : HasDerivAt (fun x : ℝ => -x⁻¹) (-(-(a ^ 2)⁻¹)) a :=
    (hasDerivAt_inv (𝕜 := ℝ) ha0.ne').neg
  have e := fderiv_smul_const (c := fun x : ℝ => -x⁻¹) hd.differentiableAt
    (ContinuousLinearMap.id ℝ ℝ)
  rw [h1.fderiv_eq, e, hd.hasFDerivAt.fderiv]
  simp [ContinuousLinearMap.smulRight_apply]
  field_simp

end BlockBand.SourceProcess.Stochastic.GramUniqueness
