module

public import BlockBand.Diffusion.Comparison.RadialGaussDefs
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Elementary inequalities for `σ(s) = s / sinh s` and `cosh` (package K-B′)

All are one-variable facts. With `F(y) = cosh √y` (convex on `[0, ∞)`, `F'(ρ²) = 1/(2σ(ρ))`),
the two divided-difference bounds below are the tangent-line inequalities of `F` at the right
and at the left endpoint of `[δ², ρ²]`:

* `gc_cosh_sub_le` : `2σ(ρ)(cosh ρ - cosh δ) ≤ ρ² - δ²` for `0 ≤ δ ≤ ρ`;
* `gc_le_cosh_sub` : `ρ² - δ² ≤ 2σ(δ)(cosh ρ - cosh δ)` for `0 ≤ δ ≤ ρ`;
* `gc_sdivSinh_anti` : `σ` is antitone on `[0, ∞)`;
* `gc_sdivSinh_le_mul_exp` : `σ(δ) ≤ σ(ρ) e^{ρ - δ}` for `0 ≤ δ ≤ ρ` (`log σ` is `1`-Lipschitz).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open Set Real

theorem gc_sdivSinh_mul_sinh (t : ℝ) : gcSdivSinh t * Real.sinh t = t := by
  unfold gcSdivSinh
  split_ifs with h
  · simp [h]
  · exact div_mul_cancel₀ t (fun hs => h (Real.sinh_eq_zero.1 hs))

theorem gc_sdivSinh_of_ne {t : ℝ} (ht : t ≠ 0) : gcSdivSinh t = t / Real.sinh t := by
  simp [gcSdivSinh, ht]

theorem gc_sdivSinh_zero : gcSdivSinh 0 = 1 := by simp [gcSdivSinh]

theorem gc_convexOn_sinh : ConvexOn ℝ (Ici 0) Real.sinh := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) Real.continuous_sinh.continuousOn
    Real.differentiable_sinh.differentiableOn ?_
  rw [Real.deriv_sinh, interior_Ici]
  intro x hx y hy hxy
  exact Real.cosh_le_cosh.2 (by
    rw [abs_of_pos (mem_Ioi.1 hx), abs_of_pos (mem_Ioi.1 hy)]; exact hxy)

/-- `sinh t / t` is monotone: `u sinh t ≤ t sinh u` for `0 ≤ t ≤ u`. -/
theorem gc_mul_sinh_le {t u : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    u * Real.sinh t ≤ t * Real.sinh u := by
  rcases eq_or_lt_of_le (ht.trans htu) with hu | hu
  · subst hu
    have : t = 0 := le_antisymm htu ht
    simp [this]
  have ha : 0 ≤ t / u := div_nonneg ht hu.le
  have hb : 0 ≤ 1 - t / u := by rw [sub_nonneg, div_le_one hu]; exact htu
  have h := gc_convexOn_sinh.2 (mem_Ici.2 hu.le) (mem_Ici.2 le_rfl) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.sinh_zero] at h
  rw [div_mul_cancel₀ t hu.ne'] at h
  calc u * Real.sinh t ≤ u * (t / u * Real.sinh u) := by gcongr
    _ = t * Real.sinh u := by field_simp

/-- `σ` is antitone on `[0, ∞)`. -/
theorem gc_sdivSinh_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    gcSdivSinh t ≤ gcSdivSinh s := by
  rcases eq_or_lt_of_le hs with h0 | h0
  · subst h0
    rw [gc_sdivSinh_zero]
    exact gc_sdivSinh_le_one t
  have ht : 0 < t := h0.trans_le hst
  rw [gc_sdivSinh_of_ne ht.ne', gc_sdivSinh_of_ne h0.ne',
    div_le_div_iff₀ (Real.sinh_pos_iff.2 ht) (Real.sinh_pos_iff.2 h0)]
  have := gc_mul_sinh_le hs hst
  linarith

theorem gc_hasDerivAt_coshSub (s x : ℝ) :
    HasDerivAt (fun t => Real.cosh t - t ^ 2 / (2 * s)) (Real.sinh x - x / s) x := by
  have h := (Real.hasDerivAt_cosh x).sub ((hasDerivAt_pow 2 x).div_const (2 * s))
  convert h using 1
  rcases eq_or_ne s 0 with hs | hs
  · simp [hs]
  · field_simp
    ring

/-- Tangent line of `cosh √·` at the right endpoint:
`2σ(ρ)(cosh ρ - cosh δ) ≤ ρ² - δ²` for `0 ≤ δ ≤ ρ`. -/
theorem gc_cosh_sub_le {δ ρ : ℝ} (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ) :
    2 * gcSdivSinh ρ * (Real.cosh ρ - Real.cosh δ) ≤ ρ ^ 2 - δ ^ 2 := by
  set s := gcSdivSinh ρ with hs_def
  have hs : 0 < s := gc_sdivSinh_pos ρ
  have hanti : AntitoneOn (fun t => Real.cosh t - t ^ 2 / (2 * s)) (Icc 0 ρ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 ρ)
      (fun x _ => (gc_hasDerivAt_coshSub s x).continuousAt.continuousWithinAt)
      (fun x _ => (gc_hasDerivAt_coshSub s x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(gc_hasDerivAt_coshSub s x).deriv, sub_nonpos, le_div_iff₀ hs]
    have h1 : s ≤ gcSdivSinh x := gc_sdivSinh_anti hx.1.le hx.2.le
    have h2 := gc_sdivSinh_mul_sinh x
    have h3 : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx.1
    nlinarith
  have h := hanti ⟨hδ, hδρ⟩ ⟨hδ.trans hδρ, le_rfl⟩ hδρ
  simp only at h
  have : ρ ^ 2 / (2 * s) - δ ^ 2 / (2 * s) = (ρ ^ 2 - δ ^ 2) / (2 * s) := by ring
  have h' : Real.cosh ρ - Real.cosh δ ≤ (ρ ^ 2 - δ ^ 2) / (2 * s) := by linarith
  rw [le_div_iff₀ (by positivity)] at h'
  linarith

/-- Tangent line of `cosh √·` at the left endpoint:
`ρ² - δ² ≤ 2σ(δ)(cosh ρ - cosh δ)` for `0 ≤ δ ≤ ρ`. -/
theorem gc_le_cosh_sub {δ ρ : ℝ} (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ) :
    ρ ^ 2 - δ ^ 2 ≤ 2 * gcSdivSinh δ * (Real.cosh ρ - Real.cosh δ) := by
  set s := gcSdivSinh δ with hs_def
  have hs : 0 < s := gc_sdivSinh_pos δ
  have hmono : MonotoneOn (fun t => Real.cosh t - t ^ 2 / (2 * s)) (Ici δ) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici δ)
      (fun x _ => (gc_hasDerivAt_coshSub s x).continuousAt.continuousWithinAt)
      (fun x _ => (gc_hasDerivAt_coshSub s x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_of_le_of_lt hδ hx
    rw [(gc_hasDerivAt_coshSub s x).deriv, sub_nonneg, div_le_iff₀ hs]
    have h1 : gcSdivSinh x ≤ s := gc_sdivSinh_anti hδ hx.le
    have h2 := gc_sdivSinh_mul_sinh x
    have h3 : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx0
    nlinarith
  have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hδρ) hδρ
  simp only at h
  have h' : (ρ ^ 2 - δ ^ 2) / (2 * s) ≤ Real.cosh ρ - Real.cosh δ := by
    have : ρ ^ 2 / (2 * s) - δ ^ 2 / (2 * s) = (ρ ^ 2 - δ ^ 2) / (2 * s) := by ring
    linarith
  rw [div_le_iff₀ (by positivity)] at h'
  linarith

/-- `log σ` is `1`-Lipschitz from below: `σ(δ) ≤ σ(ρ) e^{ρ - δ}` for `0 ≤ δ ≤ ρ`. -/
theorem gc_sdivSinh_le_mul_exp {δ ρ : ℝ} (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ) :
    gcSdivSinh δ ≤ gcSdivSinh ρ * Real.exp (ρ - δ) := by
  rcases eq_or_lt_of_le (hδ.trans hδρ) with hρ | hρ
  · have h0 : δ = 0 := le_antisymm (hρ ▸ hδρ) hδ
    subst h0
    rw [← hρ]
    simp
  have hEρ : 0 < Real.exp ρ := Real.exp_pos ρ
  have hsρ : 0 < Real.sinh ρ := Real.sinh_pos_iff.2 hρ
  have hsinhρ : 2 * Real.sinh ρ = Real.exp ρ - Real.exp (-ρ) := by
    rw [Real.sinh_eq]; ring
  have hm : Real.exp (-ρ) = Real.exp (-2 * ρ) * Real.exp ρ := by
    rw [← Real.exp_add]; ring_nf
  rcases eq_or_lt_of_le hδ with h0 | h0
  · subst h0
    rw [gc_sdivSinh_zero, gc_sdivSinh_of_ne hρ.ne', sub_zero, div_mul_eq_mul_div,
      le_div_iff₀ hsρ, one_mul]
    have h1 := Real.add_one_le_exp (-2 * ρ)
    have h2 : Real.exp (-2 * ρ) * Real.exp ρ ≥ (-2 * ρ + 1) * Real.exp ρ :=
      mul_le_mul_of_nonneg_right h1 hEρ.le
    nlinarith
  have hsδ : 0 < Real.sinh δ := Real.sinh_pos_iff.2 h0
  have hsinhδ : 2 * Real.sinh δ = Real.exp δ - Real.exp (-δ) := by
    rw [Real.sinh_eq]; ring
  -- convexity of `exp` between `-2ρ` and `0`
  have ha : 0 ≤ δ / ρ := div_nonneg hδ hρ.le
  have hb : 0 ≤ 1 - δ / ρ := by rw [sub_nonneg, div_le_one hρ]; exact hδρ
  have hc := convexOn_exp.2 (mem_univ (-2 * ρ)) (mem_univ 0) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
  have he : δ / ρ * (-2 * ρ) = -2 * δ := by field_simp
  rw [he] at hc
  have hc' : ρ * Real.exp (-2 * δ) ≤ δ * Real.exp (-2 * ρ) + (ρ - δ) := by
    have := mul_le_mul_of_nonneg_left hc hρ.le
    have e1 : ρ * (δ / ρ * Real.exp (-2 * ρ) + (1 - δ / ρ)) =
        δ * Real.exp (-2 * ρ) + (ρ - δ) := by field_simp
    linarith
  rw [gc_sdivSinh_of_ne h0.ne', gc_sdivSinh_of_ne hρ.ne', div_mul_eq_mul_div,
    div_le_div_iff₀ hsδ hsρ]
  -- `δ sinh ρ ≤ ρ e^{ρ-δ} sinh δ`
  have hx1 : Real.exp (ρ - δ) * Real.exp δ = Real.exp ρ := by rw [← Real.exp_add]; ring_nf
  have hx2 : Real.exp (ρ - δ) * Real.exp (-δ) = Real.exp (-2 * δ) * Real.exp ρ := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have key : 2 * (δ * Real.sinh ρ) ≤ 2 * (ρ * Real.exp (ρ - δ) * Real.sinh δ) := by
    have e2 : 2 * (ρ * Real.exp (ρ - δ) * Real.sinh δ) =
        ρ * (Real.exp (ρ - δ) * Real.exp δ - Real.exp (ρ - δ) * Real.exp (-δ)) := by
      rw [← mul_sub, ← hsinhδ]; ring
    rw [e2, hx1, hx2, show 2 * (δ * Real.sinh ρ) = δ * (2 * Real.sinh ρ) by ring, hsinhρ, hm]
    have := mul_le_mul_of_nonneg_right hc' hEρ.le
    nlinarith
  linarith

end BlockBand.Diffusion
