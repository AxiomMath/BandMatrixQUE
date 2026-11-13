module

public import BlockBand.Endpoints.Response.PassDerivativeNorms

/-!
# Subharmonicity of `‖·‖^s` for the auxiliary disk pencil

* `norm_rpow_le_circleAverage`: for `h` analytic on a neighbourhood of `closedBall 0 r` and
  `s > 0`, `‖h 0‖^s ≤ circleAverage (‖h ·‖^s) 0 r`.
* `diskPencil Y Γ δ ζ = (1-ζ)(Y + iδ) + i(1+ζ)Γ` and `diskInv = (1-ζ) diskPencil⁻¹`;
  `diskInv 0 = (Y + iΓ + iδ)⁻¹`. For Hermitian `Y`, `Γ ⪰ ε'` (`ε' > 0`) and `δ > 0` the pencil
  is invertible on the closed unit disk (`diskPencil_isUnit`); hence the entries of `diskInv`
  are analytic there.
* `norm_diskInv_zero_rpow_le`: `‖(Y + iΓ + iδ)⁻¹‖^s ≤ circleAverage (‖diskInv ·‖^s) 0 1`
  (Euclidean operator norm).
* `diskInv_eq_of_sphere`: on the unit circle, `ζ ≠ 1`, `diskInv ζ = (Y + tΓ + iδ)⁻¹` with the
  real parameter `t = Re(i(1+ζ)/(1-ζ))`.

The positive height `δ` is the paper's "scalar positive height" that removes real
poles; strict positivity `Γ ⪰ ε'` is used only at the boundary point `ζ = 1` (`t = ∞`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix Complex Real Metric Filter MeasureTheory Set Interval
open scoped Matrix.Norms.L2Operator ComplexConjugate

/-!
### Scalar sub-mean-value inequality
-/

/-- **Sub-mean-value inequality for `‖h‖^s`**, `h` analytic near `closedBall 0 r`, `s > 0`
(subharmonicity of `‖h‖^s`; from Jensen's formula and Jensen's inequality for `exp`). -/
theorem norm_rpow_le_circleAverage {h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 r)) {s : ℝ} (hs : 0 < s) :
    ‖h 0‖ ^ s ≤ circleAverage (fun z => ‖h z‖ ^ s) 0 r := by
  by_cases h0 : h 0 = 0
  · rw [h0, norm_zero, Real.zero_rpow hs.ne']
    exact circleAverage_nonneg_of_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) _
  have habs : |r| = r := abs_of_pos hr
  have hh' : AnalyticOnNhd ℂ h (closedBall 0 |r|) := by rwa [habs]
  have hJ := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := r) hr.ne' hh' h0
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor h (closedBall 0 |r|) u : ℝ) *
      Real.log (r * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh' u
      · rcases eq_or_ne u 0 with rfl | hu0
        · simp
        · apply Real.log_nonneg
          rw [zero_sub, norm_neg]
          have hu' : ‖u‖ ≤ r := by simpa [habs] using hu
          have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu0
          rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
          exact hu'
    · simp [hu]
  have hlog : Real.log ‖h 0‖ ≤ circleAverage (fun z => Real.log ‖h z‖) 0 r := by
    rw [hJ]; linarith
  have hcod : (fun z => Real.exp (s * Real.log ‖h z‖)) =ᶠ[codiscreteWithin (sphere 0 |r|)]
      (fun z => ‖h z‖ ^ s) := by
    have hz := hh.preimage_zero_mem_codiscreteWithin (x := 0) h0 (by simp [hr.le])
      ((convex_closedBall 0 r).isConnected ⟨0, by simp [hr.le]⟩)
    have hz' : h ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |r|) := by
      rw [habs]
      exact Filter.codiscreteWithin_mono sphere_subset_closedBall hz
    filter_upwards [hz'] with z hz
    have hpos : 0 < ‖h z‖ := norm_pos_iff.2 hz
    rw [Real.rpow_def_of_pos hpos, mul_comm]
  have hint : CircleIntegrable (fun z => Real.log ‖h z‖) 0 r :=
    MeromorphicOn.circleIntegrable_log_norm (AnalyticOnNhd.meromorphicOn
      (hh'.mono sphere_subset_closedBall))
  have hcont : Continuous (fun θ : ℝ => h (circleMap 0 r θ)) := by
    have hc : ContinuousOn h (closedBall 0 r) := hh.continuousOn
    exact hc.comp_continuous (continuous_circleMap 0 r) fun θ => by
      simp [abs_of_pos hr]
  have hmeas : Measurable (fun θ : ℝ => Real.exp (s * Real.log ‖h (circleMap 0 r θ)‖)) :=
    Real.measurable_exp.comp (measurable_const.mul (Real.measurable_log.comp
      hcont.measurable.norm))
  have hexpint : IntervalIntegrable
      (fun θ : ℝ => Real.exp (s * Real.log ‖h (circleMap 0 r θ)‖)) volume 0 (2 * π) := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
      hh.continuousOn
    refine (intervalIntegrable_const (c := (max B 1) ^ s)).mono_fun
      hmeas.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
    have hB1 : ‖h (circleMap 0 r θ)‖ ≤ max B 1 :=
      (hB _ (by simp [abs_of_pos hr])).trans (le_max_left _ _)
    have hM : (1 : ℝ) ≤ max B 1 := le_max_right _ _
    show ‖Real.exp (s * Real.log ‖h (circleMap 0 r θ)‖)‖ ≤ |max B 1 ^ s|
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    rcases (norm_nonneg (h (circleMap 0 r θ))).eq_or_lt with h0' | hpos
    · rw [← h0', Real.log_zero, mul_zero, Real.exp_zero]
      exact Real.one_le_rpow hM hs.le
    · rw [mul_comm, ← Real.rpow_def_of_pos hpos]
      exact Real.rpow_le_rpow hpos.le hB1 hs.le
  have hJen : Real.exp (circleAverage (fun z => s * Real.log ‖h z‖) 0 r) ≤
      circleAverage (fun z => Real.exp (s * Real.log ‖h z‖)) 0 r := by
    rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
    have hI : volume (Ι (0 : ℝ) (2 * π)) ≠ 0 := by
      rw [uIoc_of_le two_pi_pos.le, Real.volume_Ioc]; simp [Real.pi_pos]
    have hI' : volume (Ι (0 : ℝ) (2 * π)) ≠ ⊤ := by
      rw [uIoc_of_le two_pi_pos.le, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    refine ConvexOn.map_set_average_le convexOn_exp Real.continuous_exp.continuousOn
      isClosed_univ hI hI' (ae_of_all _ fun _ => Set.mem_univ _) ?_ ?_
    · exact (intervalIntegrable_iff.1 hint).const_mul s
    · exact intervalIntegrable_iff.1 hexpint
  calc ‖h 0‖ ^ s = Real.exp (s * Real.log ‖h 0‖) := by
        rw [Real.rpow_def_of_pos (norm_pos_iff.2 h0), mul_comm]
    _ ≤ Real.exp (circleAverage (fun z => s * Real.log ‖h z‖) 0 r) := by
        have hsm : circleAverage (fun z => s * Real.log ‖h z‖) 0 r =
            s * circleAverage (fun z => Real.log ‖h z‖) 0 r := by
          simpa using circleAverage_fun_smul (a := s) (f := fun z => Real.log ‖h z‖) (c := 0)
            (R := r)
        rw [hsm]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog hs.le)
    _ ≤ _ := hJen
    _ = _ := circleAverage_congr_codiscreteWithin hcod hr.ne'

/-!
### The disk pencil
-/

section Pencil

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `diskPencil Y Γ δ ζ = (1-ζ)(Y + iδ) + i(1+ζ)Γ`; for `ζ ≠ 1` it is `(1-ζ)(Y + iδ + tΓ)` with
`t = i(1+ζ)/(1-ζ)` (the Cayley map from the disk to the upper half-plane). -/
def diskPencil (Y Γ : Matrix n n ℂ) (δ : ℝ) (ζ : ℂ) : Matrix n n ℂ :=
  (1 - ζ) • (Y + ((δ : ℂ) * I) • 1) + ((1 + ζ) * I) • Γ

/-- `diskInv Y Γ δ ζ = (1-ζ) diskPencil⁻¹ = (Y + iδ + tΓ)⁻¹`, `t = i(1+ζ)/(1-ζ)`. -/
def diskInv (Y Γ : Matrix n n ℂ) (δ : ℝ) (ζ : ℂ) : Matrix n n ℂ :=
  (1 - ζ) • (diskPencil Y Γ δ ζ)⁻¹

theorem diskInv_zero (Y Γ : Matrix n n ℂ) (δ : ℝ) :
    diskInv Y Γ δ 0 = (Y + I • Γ + ((δ : ℂ) * I) • 1)⁻¹ := by
  rw [diskInv, diskPencil, sub_zero, one_smul, one_smul, add_zero, one_mul, add_assoc,
    add_comm (((δ : ℂ) * I) • 1), ← add_assoc]

omit [DecidableEq n] in
theorem quad_im_eq_zero_of_isHermitian {K : Matrix n n ℂ} (hK : K.IsHermitian) (v : n → ℂ) :
    (star v ⬝ᵥ (K *ᵥ v)).im = 0 := by
  have h := star_dotProduct_conjTranspose_mulVec K v
  rw [hK.eq] at h
  have := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at this
  linarith

theorem diskPencil_quad (Y Γ : Matrix n n ℂ) (δ : ℝ) (ζ : ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (diskPencil Y Γ δ ζ *ᵥ v) =
      (1 - ζ) * (star v ⬝ᵥ (Y *ᵥ v) + ((δ : ℂ) * I) * (vecNormSq v : ℂ)) +
        ((1 + ζ) * I) * (star v ⬝ᵥ (Γ *ᵥ v)) := by
  rw [diskPencil, add_mulVec, smul_mulVec, smul_mulVec, add_mulVec, smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_add, dotProduct_smul,
    star_dotProduct_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- **The disk pencil is invertible on the closed unit disk**, for Hermitian `Y`, Hermitian
`Γ ⪰ ε'` (`ε' > 0`) and `δ > 0`. -/
theorem diskPencil_isUnit {Y Γ : Matrix n n ℂ} (hY : Y.IsHermitian) (hΓ : Γ.IsHermitian)
    {ε' : ℝ} (hε' : 0 < ε') (hΓpos : ∀ v, ε' * vecNormSq v ≤ (star v ⬝ᵥ (Γ *ᵥ v)).re)
    {δ : ℝ} (hδ : 0 < δ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) : IsUnit (diskPencil Y Γ δ ζ) := by
  refine mulVec_injective_iff_isUnit.1 fun v w hvw => ?_
  have h0 : diskPencil Y Γ δ ζ *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  set x := v - w with hx
  have hQ := diskPencil_quad Y Γ δ ζ x
  rw [h0, dotProduct_zero] at hQ
  have hy := quad_im_eq_zero_of_isHermitian hY x
  have hg := quad_im_eq_zero_of_isHermitian hΓ x
  have hgpos := hΓpos x
  have hn := vecNormSq_nonneg x
  set y := (star x ⬝ᵥ (Y *ᵥ x)).re
  set g := (star x ⬝ᵥ (Γ *ᵥ x)).re
  set N := vecNormSq x
  have hζ2 : ζ.re ^ 2 + ζ.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg ζ]
  have hre := congrArg Complex.re hQ
  have him := congrArg Complex.im hQ
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im, hy, hg] at hre him
  -- `Im(conj(1-ζ) Q) = |1-ζ|² δ N + (1-|ζ|²) g = 0`
  have hkey : ((1 - ζ.re) ^ 2 + ζ.im ^ 2) * (δ * N) + (1 - ζ.re ^ 2 - ζ.im ^ 2) * g = 0 := by
    linear_combination (-(1 - ζ.re)) * him + (-ζ.im) * hre
  have hgN : 0 ≤ g := le_trans (mul_nonneg hε'.le hn) hgpos
  have hN0 : N = 0 := by
    by_cases h1 : (1 - ζ.re) ^ 2 + ζ.im ^ 2 = 0
    · have hr1 : ζ.re = 1 := by nlinarith [sq_nonneg (1 - ζ.re), sq_nonneg ζ.im]
      have hi0 : ζ.im = 0 := by nlinarith [sq_nonneg (1 - ζ.re), sq_nonneg ζ.im]
      rw [hr1, hi0] at him
      have : g = 0 := by nlinarith
      nlinarith
    · have hpos : 0 < (1 - ζ.re) ^ 2 + ζ.im ^ 2 :=
        lt_of_le_of_ne (by positivity) (Ne.symm h1)
      have h2 : 0 ≤ (1 - ζ.re ^ 2 - ζ.im ^ 2) * g := mul_nonneg (by linarith) hgN
      have h3 : 0 ≤ ((1 - ζ.re) ^ 2 + ζ.im ^ 2) * (δ * N) := by positivity
      have h4 : ((1 - ζ.re) ^ 2 + ζ.im ^ 2) * (δ * N) = 0 := by linarith
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h hpos.ne'
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h hδ.ne'
        · exact h
  exact sub_eq_zero.1 (vecNormSq_eq_zero hN0)

/-- `diskInv` is analytic (as a matrix-valued map) wherever the pencil is invertible. -/
theorem analyticAt_diskInv (Y Γ : Matrix n n ℂ) (δ : ℝ) {ζ₀ : ℂ}
    (hU : IsUnit (diskPencil Y Γ δ ζ₀)) : AnalyticAt ℂ (diskInv Y Γ δ) ζ₀ := by
  have hP : AnalyticAt ℂ (diskPencil Y Γ δ) ζ₀ := by
    unfold diskPencil
    exact ((analyticAt_const.sub analyticAt_id).smul analyticAt_const).add
      (((analyticAt_const.add analyticAt_id).mul analyticAt_const).smul analyticAt_const)
  have hInv : AnalyticAt ℂ (fun ζ => Ring.inverse (diskPencil Y Γ δ ζ)) ζ₀ := by
    have h := analyticAt_inverse (𝕜 := ℂ) hU.unit
    rw [IsUnit.unit_spec] at h
    exact h.comp hP
  have he : diskInv Y Γ δ = fun ζ => (1 - ζ) • Ring.inverse (diskPencil Y Γ δ ζ) := by
    funext ζ
    rw [diskInv, nonsing_inv_eq_ringInverse]
  rw [he]
  exact (analyticAt_const.sub analyticAt_id).smul hInv

/-- The bilinear test `X ↦ u* X v` as a continuous linear functional. -/
def matrixTest (u v : n → ℂ) : Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => star u ⬝ᵥ (X *ᵥ v)
      map_add' := fun X Z => by rw [add_mulVec, dotProduct_add]
      map_smul' := fun c X => by
        rw [smul_mulVec, dotProduct_smul, RingHom.id_apply] }

omit [DecidableEq n] in
theorem matrixTest_apply (u v : n → ℂ) (X : Matrix n n ℂ) :
    matrixTest u v X = star u ⬝ᵥ (X *ᵥ v) := rfl

/-- **Sub-mean-value inequality for the disk pencil.** For Hermitian `Y`, Hermitian `Γ ⪰ ε'`
(`ε' > 0`), `δ > 0` and `s > 0`:
`‖(Y + iΓ + iδ)⁻¹‖^s ≤ circleAverage (‖diskInv ·‖^s) 0 1` (Euclidean operator norm). -/
theorem norm_diskInv_zero_rpow_le {Y Γ : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hΓ : Γ.IsHermitian) {ε' : ℝ} (hε' : 0 < ε')
    (hΓpos : ∀ v, ε' * vecNormSq v ≤ (star v ⬝ᵥ (Γ *ᵥ v)).re) {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) :
    ‖diskInv Y Γ δ 0‖ ^ s ≤ circleAverage (fun ζ => ‖diskInv Y Γ δ ζ‖ ^ s) 0 1 := by
  set h := diskInv Y Γ δ with hh
  have hAn : ∀ ζ ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ h ζ := fun ζ hζ =>
    analyticAt_diskInv Y Γ δ (diskPencil_isUnit hY hΓ hε' hΓpos hδ (by simpa using hζ))
  have hcontS : ContinuousOn (fun ζ => ‖h ζ‖ ^ s) (sphere (0 : ℂ) 1) := fun ζ hζ =>
    ((hAn ζ (sphere_subset_closedBall hζ)).continuousAt.norm.rpow_const
      (Or.inr hs.le)).continuousWithinAt
  set A := circleAverage (fun ζ => ‖h ζ‖ ^ s) 0 1 with hA
  have hA0 : 0 ≤ A := circleAverage_nonneg_of_nonneg fun x _ =>
    Real.rpow_nonneg (norm_nonneg _) _
  suffices hX : ‖h 0‖ ≤ A ^ (1 / s) by
    calc ‖h 0‖ ^ s ≤ (A ^ (1 / s)) ^ s := Real.rpow_le_rpow (norm_nonneg _) hX hs.le
      _ = A := by rw [← Real.rpow_mul hA0, one_div_mul_cancel hs.ne', Real.rpow_one]
  refine l2_opNorm_le_of_vecNormSq (Real.rpow_nonneg hA0 _) fun v => ?_
  set x := h 0 *ᵥ v with hx
  set X := vecNormSq x
  set V := vecNormSq v
  have hX0 : 0 ≤ X := vecNormSq_nonneg x
  have hV0 : 0 ≤ V := vecNormSq_nonneg v
  rcases hX0.eq_or_lt with hXe | hXpos
  · rw [← hXe]; positivity
  -- the scalar function `g ζ = x* h(ζ) v`
  set g : ℂ → ℂ := fun ζ => matrixTest x v (h ζ) with hg
  have hgAn : AnalyticOnNhd ℂ g (closedBall 0 1) := fun ζ hζ =>
    ((matrixTest x v).analyticAt _).comp (hAn ζ hζ)
  have hg0 : ‖g 0‖ = X := by
    simp only [hg, matrixTest_apply, ← hx, star_dotProduct_self, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_nonneg hX0
  have hgle : ∀ ζ, ‖g ζ‖ ^ s ≤ (Real.sqrt X * Real.sqrt V) ^ s * ‖h ζ‖ ^ s := by
    intro ζ
    rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ hs.le
    have h1 := norm_star_dotProduct_sq_le x (h ζ *ᵥ v)
    have h2 := vecNormSq_mulVec_le (h ζ) v
    have h3 : ‖g ζ‖ ^ 2 ≤ (Real.sqrt X * Real.sqrt V * ‖h ζ‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hV0]
      calc ‖g ζ‖ ^ 2 ≤ X * vecNormSq (h ζ *ᵥ v) := h1
        _ ≤ X * (‖h ζ‖ ^ 2 * V) := mul_le_mul_of_nonneg_left h2 hX0
        _ = X * V * ‖h ζ‖ ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3
  have hgcont : ContinuousOn (fun ζ => ‖g ζ‖ ^ s) (sphere (0 : ℂ) 1) := fun ζ hζ =>
    ((hgAn ζ (sphere_subset_closedBall hζ)).continuousAt.norm.rpow_const
      (Or.inr hs.le)).continuousWithinAt
  have hmain : X ^ s ≤ (Real.sqrt X * Real.sqrt V) ^ s * A := by
    calc X ^ s = ‖g 0‖ ^ s := by rw [hg0]
      _ ≤ circleAverage (fun ζ => ‖g ζ‖ ^ s) 0 1 := norm_rpow_le_circleAverage one_pos hgAn hs
      _ ≤ circleAverage (fun ζ => (Real.sqrt X * Real.sqrt V) ^ s * ‖h ζ‖ ^ s) 0 1 := by
          refine circleAverage_mono (hgcont.circleIntegrable zero_le_one) ?_
            fun ζ _ => hgle ζ
          exact (continuousOn_const.mul hcontS).circleIntegrable zero_le_one
      _ = _ := by
          simpa using circleAverage_fun_smul (a := (Real.sqrt X * Real.sqrt V) ^ s)
            (f := fun ζ => ‖h ζ‖ ^ s) (c := 0) (R := 1)
  -- `X^s = (√X)^s (√X)^s`, divide by `(√X)^s > 0`
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hXs : X ^ s = Real.sqrt X ^ s * Real.sqrt X ^ s := by
    rw [← Real.mul_rpow hsX.le hsX.le, Real.mul_self_sqrt hX0]
  rw [hXs, Real.mul_rpow hsX.le (Real.sqrt_nonneg _), mul_assoc] at hmain
  have h4 : Real.sqrt X ^ s ≤ Real.sqrt V ^ s * A :=
    le_of_mul_le_mul_left hmain (Real.rpow_pos_of_pos hsX s)
  have h5 : Real.sqrt X ≤ Real.sqrt V * A ^ (1 / s) := by
    have h6 := Real.rpow_le_rpow (Real.rpow_nonneg hsX.le s) h4 (one_div_pos.2 hs).le
    rwa [← Real.rpow_mul hsX.le, mul_one_div_cancel hs.ne', Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg (Real.sqrt_nonneg _) _) hA0, ← Real.rpow_mul
        (Real.sqrt_nonneg _), mul_one_div_cancel hs.ne', Real.rpow_one] at h6
  have h7 := pow_le_pow_left₀ hsX.le h5 2
  rwa [Real.sq_sqrt hX0, mul_pow, Real.sq_sqrt hV0, mul_comm] at h7

/-- On the unit circle, away from `ζ = 1`, the Cayley parameter `i(1+ζ)/(1-ζ)` is real. -/
theorem cayley_im_eq_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    (I * (1 + ζ) / (1 - ζ)).im = 0 := by
  have hz : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have := Complex.sq_norm ζ
    rw [Complex.normSq_apply, hζ] at this
    nlinarith
  have hd : (1 - ζ) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [div_sub_div_same, div_eq_zero_iff]
  left
  nlinarith

/-- **The disk pencil on the unit circle is a Hermitian pencil with a real parameter**: for
`‖ζ‖ = 1`, `ζ ≠ 1`, `diskInv Y Γ δ ζ = (Y + tΓ + iδ)⁻¹` with `t = Re(i(1+ζ)/(1-ζ))`. -/
theorem diskInv_eq_of_sphere (Y Γ : Matrix n n ℂ) (δ : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    diskInv Y Γ δ ζ = (Y + (((I * (1 + ζ) / (1 - ζ)).re : ℝ) : ℂ) • Γ +
      ((δ : ℂ) * I) • 1)⁻¹ := by
  have hd : (1 - ζ) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have ht : ((((I * (1 + ζ) / (1 - ζ)).re : ℝ) : ℂ)) = I * (1 + ζ) / (1 - ζ) :=
    Complex.ext (by simp) (by simp [cayley_im_eq_zero hζ h1])
  rw [ht]
  set K := Y + (I * (1 + ζ) / (1 - ζ)) • Γ + ((δ : ℂ) * I) • 1
  have hP : diskPencil Y Γ δ ζ = (1 - ζ) • K := by
    simp only [diskPencil, K, smul_add, smul_smul]
    rw [show (1 - ζ) * (I * (1 + ζ) / (1 - ζ)) = (1 + ζ) * I by field_simp]
    abel
  rw [diskInv, hP]
  by_cases hK : IsUnit K.det
  · have h2 := Matrix.inv_smul' K (Units.mk0 (1 - ζ) hd) hK
    simp only [Units.smul_def, Units.val_mk0] at h2
    rw [h2, smul_smul]
    simp [hd]
  · have hK' : ¬ IsUnit ((1 - ζ) • K).det := by
      rw [det_smul]
      intro hu
      exact hK (isUnit_of_mul_isUnit_right hu)
    rw [nonsing_inv_apply_not_isUnit _ hK, nonsing_inv_apply_not_isUnit _ hK', smul_zero]

end Pencil

end BlockBand.Endpoints
