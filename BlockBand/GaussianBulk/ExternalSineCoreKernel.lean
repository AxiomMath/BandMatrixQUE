module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineCoreKernelBound

/-!
# Joint continuity of the Johansson double contour kernel in `(d, u, v)`

The clause `Continuous (uncurry Kern)` of the external-source sine-kernel theorem, for the
double contour integral kernel of Johansson (his eq. (2.18)). Object: the kernel
`Johansson.kernel S d R L u v` (counterclockwise circle `|z| = R` about `0`, upward line
`Re w = L`, denominator `(2πi)² S`). Domain: `S > 0`, `0 < R < L`, arbitrary real `u, v`,
and every real source `d : Fin N → ℝ` with `|d_j| < R` for all `j` (repeated values allowed).

## Main results

All by dominated convergence with the explicit Gaussian majorant `kernelBoundConst`.

* `continuousAt_verticalIntegral`: the vertical integral is jointly continuous in
  `((d,u,v), z)` at every point with `Re z < L` and `z ∉ {d_j}`;
* `continuousOn_kernel`: `(d,u,v) ↦ kernel S d R L u v` is continuous on `{∀ j, |d_j| < R}`;
* `continuous_kernel`: `Continuous (uncurry (kernel S d R L))` for admissible contours;
* `circleIntegrable_verticalIntegral`: circle integrability for every admissible `d`
  (the field `circle_integrable` without the hypothesis `StrictMono d`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Filter Topology
open BlockBand.External
open scoped NNReal

/-- Parameter-space form of the vertical integrand: `q = ((d,u,v), z)`. -/
def verticalIntegrandParam {N : ℕ} (S : ℝ≥0) (L : ℝ)
    (q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ) (y : ℝ) : ℂ :=
  Complex.I * Johansson.kernelIntegrand S q.1.1 q.1.2.1 q.1.2.2 q.2 ((L : ℂ) + (y : ℂ) * Complex.I)

/-- Pointwise (in `y`) continuity of the vertical integrand in `((d,u,v), z)` away from its poles. -/
theorem continuousAt_verticalIntegrandParam {N : ℕ} (S : ℝ≥0) (L y : ℝ)
    (q0 : ((Fin N → ℝ) × ℝ × ℝ) × ℂ) (hz0L : q0.2.re < L) (hz0d : ∀ j, q0.2 ≠ (q0.1.1 j : ℂ)) :
    ContinuousAt (fun q => verticalIntegrandParam S L q y) q0 := by
  unfold verticalIntegrandParam Johansson.kernelIntegrand
  have hz : Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ => q.2) := continuous_snd
  have hd : ∀ j, Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ => ((q.1.1 j : ℝ) : ℂ)) :=
    fun j => Complex.continuous_ofReal.comp ((continuous_apply j).comp
      (continuous_fst.comp continuous_fst))
  have hexp : Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ =>
      Complex.exp ((((L : ℂ) + (y : ℂ) * Complex.I) ^ 2 -
        2 * ((q.1.2.2 : ℝ) : ℂ) * ((L : ℂ) + (y : ℂ) * Complex.I) - q.2 ^ 2 +
        2 * ((q.1.2.1 : ℝ) : ℂ) * q.2) / (2 * (S : ℂ)))) := by
    fun_prop
  have hw0 : ((L : ℂ) + (y : ℂ) * Complex.I) - q0.2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.mul
  · exact hexp.continuousAt.div (continuousAt_const.sub hz.continuousAt) hw0
  · apply tendsto_finsetProd
    intro j _
    exact (continuousAt_const.sub (hd j).continuousAt).div (hz.continuousAt.sub (hd j).continuousAt)
      (sub_ne_zero.mpr (hz0d j))

/-- Joint continuity of the vertical integral in `((d,u,v), z)` at every point with
`Re z < L` and `z ≠ d_j` for all `j` (dominated convergence). -/
theorem continuousAt_verticalIntegral {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (L : ℝ)
    (q0 : ((Fin N → ℝ) × ℝ × ℝ) × ℂ) (hz0L : q0.2.re < L) (hz0d : ∀ j, q0.2 ≠ (q0.1.1 j : ℂ)) :
    ContinuousAt (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ =>
      Johansson.verticalIntegral S q.1.1 q.1.2.1 q.1.2.2 L q.2) q0 := by
  have hSr : (0 : ℝ) < S := hS
  set B : ℝ := ‖q0‖ + 1 with hB
  set δ : ℝ := (L - q0.2.re) / 2 with hδ
  set c : Fin N → ℝ := fun j => ‖q0.2 - (q0.1.1 j : ℂ)‖ / 2 with hc
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hc0 : ∀ j, 0 < c j := fun j => by
    simp only [hc]
    exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz0d j))) two_pos
  have hcont : Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ => q) := continuous_id
  -- eventual neighbourhood conditions
  have E1 : ∀ᶠ q in 𝓝 q0, ∀ j, c j < ‖q.2 - (q.1.1 j : ℂ)‖ := by
    rw [Filter.eventually_all]
    intro j
    have hf : Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ => ‖q.2 - (q.1.1 j : ℂ)‖) :=
      (continuous_snd.sub (Complex.continuous_ofReal.comp ((continuous_apply j).comp
        (continuous_fst.comp continuous_fst)))).norm
    have h0 := hc0 j
    exact continuousAt_const.eventually_lt hf.continuousAt
      (by simp only [hc] at h0 ⊢; linarith)
  have E2 : ∀ᶠ q in 𝓝 q0, δ < L - q.2.re := by
    have hf : Continuous (fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ => L - q.2.re) :=
      continuous_const.sub (Complex.continuous_re.comp continuous_snd)
    exact continuousAt_const.eventually_lt hf.continuousAt (by simp only [hδ]; linarith)
  have E3 : ∀ᶠ q in 𝓝 q0, ‖q‖ < B :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by rw [hB]; linarith)
  have hbound : Integrable (fun y : ℝ =>
      kernelBoundConst S N L B δ c * Real.exp (-(1 / (4 * S)) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (4 * S))).const_mul _
  have key := continuousAt_of_dominated (μ := volume)
    (F := fun q y => verticalIntegrandParam S L q y) (x₀ := q0)
    (bound := fun y => kernelBoundConst S N L B δ c * Real.exp (-(1 / (4 * S)) * y ^ 2))
    (Filter.Eventually.of_forall fun q => by
      apply Measurable.aestronglyMeasurable
      unfold verticalIntegrandParam Johansson.kernelIntegrand
      fun_prop)
    (by
      filter_upwards [E1, E2, E3] with q h1 h2 h3
      refine Filter.Eventually.of_forall fun y => ?_
      unfold verticalIntegrandParam
      rw [norm_mul, Complex.norm_I, one_mul]
      have hq1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
      have hq12 : ‖q.1.2‖ ≤ ‖q.1‖ := norm_snd_le q.1
      have hq11 : ‖q.1.1‖ ≤ ‖q.1‖ := norm_fst_le q.1
      apply norm_kernelIntegrand_le S hS q.1.1 q.1.2.1 q.1.2.2 L y q.2 B δ c hc0
        (fun j => (h1 j).le) hδ0 h2.le
      · exact (norm_snd_le q).trans h3.le
      · have := norm_fst_le q.1.2
        rw [← Real.norm_eq_abs]; linarith
      · have := norm_snd_le q.1.2
        rw [← Real.norm_eq_abs]; linarith
      · intro j
        have := norm_le_pi_norm q.1.1 j
        rw [← Real.norm_eq_abs]; linarith)
    hbound
    (Filter.Eventually.of_forall fun y =>
      continuousAt_verticalIntegrandParam S L y q0 hz0L hz0d)
  exact key

/-- The circle-parametrized (2.18) integrand, on the domain `{∀ j, |d_j| < R}`, is jointly
continuous in the parameters and the angle. -/
theorem continuous_circleIntegrand {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (R L : ℝ) (hR : 0 < R)
    (hRL : R < L) :
    Continuous (fun x : {p : (Fin N → ℝ) × ℝ × ℝ // ∀ j, |p.1 j| < R} × ℝ =>
      deriv (circleMap 0 R) x.2 •
        Johansson.verticalIntegral S x.1.1.1 x.1.1.2.1 x.1.1.2.2 L (circleMap 0 R x.2)) := by
  simp_rw [deriv_circleMap]
  apply Continuous.smul (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const)
  rw [continuous_iff_continuousAt]
  rintro ⟨p, θ⟩
  have hinner : Continuous (fun x : {p : (Fin N → ℝ) × ℝ × ℝ // ∀ j, |p.1 j| < R} × ℝ =>
      ((x.1.1, circleMap 0 R x.2) : ((Fin N → ℝ) × ℝ × ℝ) × ℂ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_circleMap 0 R).comp continuous_snd)
  have hnorm : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
  have h1 : (circleMap 0 R θ).re ≤ ‖circleMap 0 R θ‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hzL : (circleMap 0 R θ).re < L := by rw [hnorm] at h1; linarith
  have hzd : ∀ j, circleMap 0 R θ ≠ ((p.1.1 j : ℝ) : ℂ) := by
    intro j h
    have := congrArg norm h
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs] at this
    have := p.2 j
    linarith
  exact ContinuousAt.comp (x := (p, θ))
    (f := fun x : {p : (Fin N → ℝ) × ℝ × ℝ // ∀ j, |p.1 j| < R} × ℝ =>
      ((x.1.1, circleMap 0 R x.2) : ((Fin N → ℝ) × ℝ × ℝ) × ℂ))
    (g := fun q : ((Fin N → ℝ) × ℝ × ℝ) × ℂ =>
      Johansson.verticalIntegral S q.1.1 q.1.2.1 q.1.2.2 L q.2)
    (continuousAt_verticalIntegral S hS L (p.1, circleMap 0 R θ) hzL hzd) hinner.continuousAt

/-- Joint continuity of the Johansson kernel in `(d, u, v)` on the source domain
`{∀ j, |d_j| < R}`, for `S > 0` and `0 < R < L`. -/
theorem continuousOn_kernel {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (R L : ℝ) (hR : 0 < R)
    (hRL : R < L) :
    ContinuousOn (fun p : (Fin N → ℝ) × ℝ × ℝ => Johansson.kernel S p.1 R L p.2.1 p.2.2)
      {p | ∀ j, |p.1 j| < R} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume)
    (f := fun (p : {p : (Fin N → ℝ) × ℝ × ℝ // ∀ j, |p.1 j| < R}) (θ : ℝ) =>
      deriv (circleMap 0 R) θ •
        Johansson.verticalIntegral S p.1.1 p.1.2.1 p.1.2.2 L (circleMap 0 R θ))
    (continuous_circleIntegrand S hS R L hR hRL) 0 (2 * Real.pi)
  have hpre : Continuous (fun p : {p : (Fin N → ℝ) × ℝ × ℝ // ∀ j, |p.1 j| < R} =>
      Complex.exp ((((p.1.2.2 : ℝ) : ℂ) ^ 2 - ((p.1.2.1 : ℝ) : ℂ) ^ 2) / (2 * (S : ℂ))) /
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 2) * (S : ℂ))) := by
    fun_prop
  refine (hpre.mul hint).congr (fun p => ?_)
  simp only [Set.domRestrict, Johansson.kernel, circleIntegral]
  rfl

/-- For admissible contours (`0 < R`, `|d_j| < R`, `R < L`) and `S > 0`, the
Johansson kernel `(u, v) ↦ kernel S d R L u v` is jointly continuous on `ℝ²`, for every real
source `d` (repeated values allowed). -/
theorem continuous_kernel {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ) (R L : ℝ)
    (hC : Johansson.AdmissibleContours d R L) :
    Continuous (Function.uncurry (Johansson.kernel S d R L)) := by
  obtain ⟨hR, hd, hRL⟩ := hC
  have h := continuousOn_kernel (N := N) S hS R L hR hRL
  have hmap : Continuous (fun x : ℝ × ℝ => ((d, x.1, x.2) : (Fin N → ℝ) × ℝ × ℝ)) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_snd)
  have h2 := h.comp_continuous hmap (fun x => hd)
  simp only [Function.comp_def] at h2
  exact h2

/-- Circle integrability of the vertical integral for every admissible source `d`
(repeated values allowed): the field `circle_integrable` without the hypothesis `StrictMono d`. -/
theorem circleIntegrable_verticalIntegral {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (R L : ℝ) (hC : Johansson.AdmissibleContours d R L) (u v : ℝ) :
    CircleIntegrable (Johansson.verticalIntegral S d u v L) 0 R := by
  obtain ⟨hR, hd, hRL⟩ := hC
  apply ContinuousOn.circleIntegrable hR.le
  intro z hz
  have hnorm : ‖z‖ = R := by simpa using hz
  have h1 : z.re ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hzL : z.re < L := by rw [hnorm] at h1; linarith
  have hzd : ∀ j, z ≠ ((d j : ℝ) : ℂ) := by
    intro j h
    have := congrArg norm h
    rw [hnorm, Complex.norm_real, Real.norm_eq_abs] at this
    have := hd j
    linarith
  have hc := continuousAt_verticalIntegral S hS L ((d, u, v), z) hzL hzd
  have hmap : Continuous (fun z' : ℂ => (((d, u, v), z') : ((Fin N → ℝ) × ℝ × ℝ) × ℂ)) := by
    fun_prop
  exact (hc.comp hmap.continuousAt).continuousWithinAt

end BlockBand.GaussianBulk
