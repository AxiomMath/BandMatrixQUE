module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Second derivatives along lines

Calculus lemmas used for the spectral curvature bound in indexed spectral convexity. For `f` of class `C²` at `x` (real normed space `E`):
* `hasDerivAt_deriv_line`: `s ↦ (d/ds) f(x + s a)` has derivative `D²f(x)[a,a]` at `0`;
* `iteratedFDeriv_two_nonneg_of_convexOn`: a function convex on a neighbourhood of `x` has
  `D²f(x)[a,a] ≥ 0`;
* `iteratedFDeriv_two_neg_log_clm`, `iteratedFDeriv_two_neg_log_sq_clm`,
  `iteratedFDeriv_two_sq_clm`: for a continuous linear functional `L`,
  `D²(-log L)(x)[a,a] = (La)²/(Lx)²`, `D²(-log L²)(x)[a,a] = 2(La)²/(Lx)²` (`Lx ≠ 0`) and
  `D²(cL²)(x)[a,a] = 2c(La)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `D²f(x)[a,a]` is the derivative at `0` of `s ↦ (d/ds) f(x + s a)` (for `f ∈ C²` at `x`). -/
theorem hasDerivAt_deriv_line {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (a : E) :
    HasDerivAt (deriv fun s : ℝ => f (x + s • a)) (iteratedFDeriv ℝ 2 f x (fun _ => a)) 0 := by
  have hp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • a) a s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hpc : Continuous fun s : ℝ => x + s • a := by fun_prop
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have ht : Tendsto (fun s : ℝ => x + s • a) (𝓝 0) (𝓝 x) := by simpa using hpc.tendsto 0
  have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (x + s • a) := ht.eventually hev
  have heq : (deriv fun s : ℝ => f (x + s • a)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (x + s • a) a :=
    hev'.mono fun s hs => ((hs.hasFDerivAt.comp_hasDerivAt s (hp s))).deriv
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD' : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • a)) (fderiv ℝ (fderiv ℝ f) x a) 0 := by
    have hD0 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • a) := by
      simpa using hD.hasFDerivAt
    exact hD0.comp_hasDerivAt (0 : ℝ) (hp 0)
  have h2 := hD'.clm_apply (hasDerivAt_const (0 : ℝ) a)
  rw [iteratedFDeriv_two_apply]
  simp only [map_zero, add_zero] at h2
  exact h2.congr_of_eventuallyEq heq

/-- Convexity on a neighbourhood gives a nonnegative second derivative. -/
theorem iteratedFDeriv_two_nonneg_of_convexOn {f : E → ℝ} {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) (hconv : ConvexOn ℝ U f) (hf : ContDiffAt ℝ 2 f x) (a : E) :
    0 ≤ iteratedFDeriv ℝ 2 f x (fun _ => a) := by
  have hpc : Continuous fun s : ℝ => x + s • a := by fun_prop
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U ∧ DifferentiableAt ℝ f y :=
    (Filter.inter_mem hU ((hf.eventually (by simp)).mono fun y hy =>
      hy.differentiableAt (by norm_num)))
  have ht : Tendsto (fun s : ℝ => x + s • a) (𝓝 0) (𝓝 x) := by simpa using hpc.tendsto 0
  have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), x + s • a ∈ U ∧ DifferentiableAt ℝ f (x + s • a) :=
    ht.eventually hev
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev'
  set I : Set ℝ := Ioo (-ε) ε
  have hI : ∀ s ∈ I, x + s • a ∈ U ∧ DifferentiableAt ℝ f (x + s • a) := fun s hs =>
    hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact hs)
  set v : ℝ → ℝ := fun s => f (x + s • a)
  have hvconv : ConvexOn ℝ I v := by
    refine ⟨convex_Ioo _ _, fun s hs r hr p q hp hq hpq => ?_⟩
    have h := hconv.2 (hI s hs).1 (hI r hr).1 hp hq hpq
    have hpt : p • (x + s • a) + q • (x + r • a) = x + (p • s + q • r) • a := by
      obtain rfl : q = 1 - p := by linarith
      simp only [smul_eq_mul]
      module
    simp only [v]
    rw [← hpt]
    exact h
  have hvd : ∀ s ∈ I, DifferentiableAt ℝ v s := fun s hs => by
    have hp : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hI s hs).2.hasFDerivAt.comp_hasDerivAt s hp).differentiableAt
  have hmono : MonotoneOn (deriv v) I := hvconv.monotoneOn_deriv hvd
  have h0 : (0 : ℝ) ∈ I := ⟨by linarith, hε⟩
  have hacc : AccPt (0 : ℝ) (𝓟 I) := by
    rw [accPt_iff_nhds]
    intro W hW
    obtain ⟨δ, hδ, hδW⟩ := Metric.mem_nhds_iff.1 hW
    refine ⟨min δ ε / 2, ⟨hδW ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      linarith [min_le_left δ ε, lt_min hδ hε]
    · constructor <;> linarith [min_le_right δ ε, lt_min hδ hε]
    · exact (by positivity : (0 : ℝ) < min δ ε / 2).ne'
  exact (hasDerivAt_deriv_line hf a).hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono

/-- `D²(-log L)(x)[a,a] = (La)²/(Lx)²` for a continuous linear functional with `Lx ≠ 0`. -/
theorem iteratedFDeriv_two_neg_log_clm (L : E →L[ℝ] ℝ) {x : E} (hx : L x ≠ 0) (a : E) :
    iteratedFDeriv ℝ 2 (fun y => -Real.log (L y)) x (fun _ => a) = (L a) ^ 2 / (L x) ^ 2 := by
  have hf : ContDiffAt ℝ 2 (fun y => -Real.log (L y)) x :=
    (L.contDiff.contDiffAt.log hx).neg
  have h1 := hasDerivAt_deriv_line hf a
  have hpc : Continuous fun s : ℝ => L x + s * L a := by fun_prop
  have ht : Tendsto (fun s : ℝ => L x + s * L a) (𝓝 0) (𝓝 (L x)) := by
    simpa using hpc.tendsto 0
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), L x + s * L a ≠ 0 := ht.eventually (isOpen_ne.mem_nhds hx)
  have heq : (deriv fun s : ℝ => -Real.log (L (x + s • a))) =ᶠ[𝓝 0]
      fun s => -(L a * (L x + s * L a)⁻¹) := by
    refine hev.mono fun s hs => ?_
    have hl : HasDerivAt (fun s : ℝ => L x + s * L a) (L a) s := by
      simpa using ((hasDerivAt_id s).mul_const (L a)).const_add (L x)
    have h := ((Real.hasDerivAt_log hs).comp s hl).neg
    simp only [map_add, map_smul, smul_eq_mul]
    convert h.deriv using 1
    · rfl
    · simp [mul_comm]
  have hl0 : HasDerivAt (fun s : ℝ => L x + s * L a) (L a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (L a)).const_add (L x)
  have h2 : HasDerivAt (fun s : ℝ => -(L a * (L x + s * L a)⁻¹))
      (-(L a * (-(L a) / (L x + 0 * L a) ^ 2))) 0 :=
    ((hl0.inv (by simpa using hx)).const_mul (L a)).neg
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  rw [h3]
  simp only [zero_mul, add_zero]
  field_simp

/-- `D²(c L²)(x)[a,a] = 2c(La)²` for a continuous linear functional `L` and a constant `c`. -/
theorem iteratedFDeriv_two_sq_clm (L : E →L[ℝ] ℝ) (c : ℝ) (x a : E) :
    iteratedFDeriv ℝ 2 (fun y => c * (L y) ^ 2) x (fun _ => a) = 2 * c * (L a) ^ 2 := by
  have hf : ContDiffAt ℝ 2 (fun y => c * (L y) ^ 2) x :=
    (contDiff_const.mul (L.contDiff.pow 2)).contDiffAt
  have h1 := hasDerivAt_deriv_line hf a
  have heq : (deriv fun s : ℝ => c * (L (x + s • a)) ^ 2) =
      fun s => c * (2 * (L x + s * L a) * L a) := by
    funext s
    have hl : HasDerivAt (fun s : ℝ => L x + s * L a) (L a) s := by
      simpa using ((hasDerivAt_id s).mul_const (L a)).const_add (L x)
    have h := (hl.pow 2).const_mul c
    simp only [map_add, map_smul, smul_eq_mul]
    convert h.deriv using 1
    simp
  have hl0 : HasDerivAt (fun s : ℝ => c * (2 * (L x + s * L a) * L a)) (c * (2 * L a * L a)) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (L a)).const_add (L x)).const_mul 2
    simpa using (this.mul_const (L a)).const_mul c
  rw [heq] at h1
  rw [h1.unique hl0]
  ring

/-- `D²(-log (L²))(x)[a,a] = 2(La)²/(Lx)²` for a continuous linear functional with `Lx ≠ 0`. -/
theorem iteratedFDeriv_two_neg_log_sq_clm (L : E →L[ℝ] ℝ) {x : E} (hx : L x ≠ 0) (a : E) :
    iteratedFDeriv ℝ 2 (fun y => -Real.log ((L y) ^ 2)) x (fun _ => a) =
      2 * ((L a) ^ 2 / (L x) ^ 2) := by
  have hfun : (fun y => -Real.log ((L y) ^ 2)) =
      (fun y => -Real.log (L y)) + (fun y => -Real.log (L y)) := by
    funext y
    simp only [Pi.add_apply, Real.log_pow]
    push_cast
    ring
  have hf : ContDiffAt ℝ 2 (fun y => -Real.log (L y)) x := (L.contDiff.contDiffAt.log hx).neg
  rw [hfun, iteratedFDeriv_add_apply hf hf, add_apply,
    iteratedFDeriv_two_neg_log_clm L hx a]
  ring

end BlockBand.DeterminantScore.SpectralConvexity
