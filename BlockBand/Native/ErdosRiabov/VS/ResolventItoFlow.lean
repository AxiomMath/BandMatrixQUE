module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false

/-!
# The saturated VS characteristic

* `vsSat δ t = t - (t - 1) ψ((t - 1)/δ)` with Mathlib's `C^∞` `Real.smoothTransition` `ψ`:
  `vsSat_of_le_one` (`c(t) = t` for `t ≤ 1`), `vsSat_le` (`c(t) ≤ 1 + δ` for all `t`),
  `contDiff_vsSat` (`C^n` for all finite `n`), `hasDerivAt_vsSat_of_le_one` (`c'(t) = 1` for
  `t ≤ 1`).
* `vsSpec z m c t = z + (1 - c t) m`: `vsSpec_im`, `hasDerivAt_vsSpec` (`ż = -c'(t) m`),
  `contDiff_vsSpec`, `vsSpec_of_le_one` (`= z + (1 - t) m` for `t ≤ 1`), `vsSpec_conj`.
* `half_le_abs_im_vsSpec`: for `Im z > 0`, `Im m > 0` and `δ = Im z / (2 Im m)`, every point of
  the saturated trajectory of `z` **and** of `z̄` (with `m̄`) satisfies `|Im z_{c(t)}| ≥ Im z / 2`
  for **all** `t ∈ ℝ` (the saturation range `[0, 1 + η/(2 Im m)]`); so the resolvent
  test functions are `C²` on all of `ℝ × ℝ^d`, as Itô's formula requires.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open Set
open scoped ComplexConjugate

/-!
### The smooth saturation
-/

/-- Smooth saturation: `vsSat δ t = t - (t - 1) ψ((t - 1)/δ)`, `ψ = Real.smoothTransition`. -/
def vsSat (δ t : ℝ) : ℝ := t - (t - 1) * Real.smoothTransition ((t - 1) / δ)

theorem vsSat_of_le_one {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ≤ 1) : vsSat δ t = t := by
  rw [vsSat, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ),
    mul_zero, sub_zero]

theorem vsSat_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : vsSat δ t ≤ 1 + δ := by
  rcases le_or_gt t 1 with ht | ht
  · rw [vsSat_of_le_one hδ.le ht]
    linarith
  · rcases le_or_gt δ (t - 1) with h | h
    · rw [vsSat, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith))]
      linarith
    · have h0 := Real.smoothTransition.nonneg ((t - 1) / δ)
      have h1 := Real.smoothTransition.le_one ((t - 1) / δ)
      have h2 : (t - 1) * (1 - Real.smoothTransition ((t - 1) / δ)) ≤ t - 1 :=
        mul_le_of_le_one_right (by linarith) (by linarith)
      rw [vsSat]
      nlinarith

theorem contDiff_vsSat (δ : ℝ) {n : ℕ} : ContDiff ℝ n (vsSat δ) := by
  unfold vsSat
  have hψ : ContDiff ℝ n Real.smoothTransition := Real.smoothTransition.contDiff
  exact contDiff_id.sub ((contDiff_id.sub contDiff_const).mul
    (hψ.comp ((contDiff_id.sub contDiff_const).div_const δ)))

theorem hasDerivAt_vsSat_of_le_one {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ≤ 1) :
    HasDerivAt (vsSat δ) 1 t := by
  have hd : DifferentiableAt ℝ (vsSat δ) t :=
    ((contDiff_vsSat δ (n := 1)).differentiable (by norm_num)) t
  have h1 : HasDerivWithinAt (vsSat δ) 1 (Iic 1) t :=
    (hasDerivAt_id t).hasDerivWithinAt.congr (fun s hs => vsSat_of_le_one hδ hs)
      (vsSat_of_le_one hδ ht)
  have h2 := hd.hasDerivAt.hasDerivWithinAt (s := Iic 1)
  have he := (uniqueDiffOn_Iic 1 t ht).eq_deriv _ h2 h1
  rw [← he]
  exact hd.hasDerivAt

/-!
### The saturated characteristic
-/

/-- The characteristic at the saturated time: `vsSpec z m c t = z + (1 - c(t)) m`. -/
def vsSpec (z m : ℂ) (c : ℝ → ℝ) (t : ℝ) : ℂ := z + ((1 - c t : ℝ) : ℂ) * m

theorem vsSpec_im (z m : ℂ) (c : ℝ → ℝ) (t : ℝ) :
    (vsSpec z m c t).im = z.im + (1 - c t) * m.im := by
  simp [vsSpec, Complex.mul_im]

theorem vsSpec_conj (z m : ℂ) (c : ℝ → ℝ) (t : ℝ) :
    vsSpec (conj z) (conj m) c t = conj (vsSpec z m c t) := by
  simp [vsSpec, map_add, map_mul, Complex.conj_ofReal]

theorem vsSpec_of_le_one (z m : ℂ) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ≤ 1) :
    vsSpec z m (vsSat δ) t = z + ((1 - t : ℝ) : ℂ) * m := by
  rw [vsSpec, vsSat_of_le_one hδ ht]

theorem hasDerivAt_vsSpec (z m : ℂ) {c : ℝ → ℝ} {c' t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (vsSpec z m c) (-(c' : ℂ) * m) t := by
  have h1 : HasDerivAt (fun s => ((1 - c s : ℝ) : ℂ)) (((-c' : ℝ)) : ℂ) t :=
    ((hasDerivAt_const t (1 : ℝ)).sub hc).ofReal_comp.congr_deriv (by simp)
  have h2 := (h1.mul_const m).const_add z
  refine h2.congr_deriv ?_
  push_cast
  ring

theorem contDiff_vsSpec (z m : ℂ) {c : ℝ → ℝ} {n : WithTop ℕ∞} (hc : ContDiff ℝ n c) :
    ContDiff ℝ n (vsSpec z m c) := by
  unfold vsSpec
  exact contDiff_const.add ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hc)).mul
    contDiff_const)

/-- The pattern choice: `z` or `z̄` according to a sign `b` (`true` = conjugate). -/
def patConj (b : Bool) (w : ℂ) : ℂ := if b then conj w else w

/-- **Uniform distance from the real axis** along the saturated trajectories of `z` and `z̄`:
for `Im z > 0`, `Im m > 0`, `δ = Im z / (2 Im m)`, all `t ∈ ℝ` and both signs,
`Im z / 2 ≤ |Im z_{c(t)}|`. -/
theorem half_le_abs_im_vsSpec {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) (b : Bool) (t : ℝ) :
    z.im / 2 ≤ |(vsSpec (patConj b z) (patConj b m) (vsSat (z.im / (2 * m.im))) t).im| := by
  have hδ : 0 < z.im / (2 * m.im) := div_pos hz (by linarith)
  have hle := vsSat_le hδ t
  have hkey : z.im / 2 ≤ (vsSpec z m (vsSat (z.im / (2 * m.im))) t).im := by
    rw [vsSpec_im]
    have hδm : z.im / (2 * m.im) * m.im = z.im / 2 := by field_simp
    nlinarith
  cases b
  · simp only [patConj, Bool.false_eq_true, ite_false]
    exact hkey.trans (le_abs_self _)
  · simp only [patConj, ite_true, vsSpec_conj, Complex.conj_im, abs_neg]
    exact hkey.trans (le_abs_self _)

theorem vsSpec_im_ne_zero {z m : ℂ} (hz : 0 < z.im) (hm : 0 < m.im) (b : Bool) (t : ℝ) :
    (vsSpec (patConj b z) (patConj b m) (vsSat (z.im / (2 * m.im))) t).im ≠ 0 :=
  abs_pos.mp ((half_pos hz).trans_le (half_le_abs_im_vsSpec hz hm b t))

end BlockBand.Native.ErdosRiabov.VS
