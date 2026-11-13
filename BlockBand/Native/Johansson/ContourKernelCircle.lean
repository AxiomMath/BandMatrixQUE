module

public import BlockBand.Native.Johansson.Defs

/-!
# Johansson's formula (2.18): the circle integral at a fixed point of the line

For distinct real nodes `d` (`StrictMono d`, `N > 0`), admissible `R` (`0 < R`, `|d_j| < R`) and
`w ∈ ℂ` with `R < Re w`, the counterclockwise circle integral over `|z| = R` is
`∮ kernelIntegrand S d u v z w dz = 2πi Σ_j exp((w² - 2vw - d_j² + 2u d_j)/(2S)) ℓ_j(w)`
(`circle_integral_kernelIntegrand`), where `ℓ_j` is `lagrangeBasis d j` mapped to `ℂ`.
Proof: partial fractions `(∏_k (z - d_k))⁻¹ = Σ_j c_j (z - d_j)⁻¹` from `Lagrange.sum_basis`
(`circle_inv_prod_sub_eq_sum`), then Cauchy's formula `DiffContOnCl.circleIntegral_sub_inv_smul`
for each `j`; the numerator is holomorphic on the closed disk since `w` lies to its right.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory Polynomial Complex Metric
open BlockBand.External.Johansson
open scoped NNReal Real

theorem circle_eval_lagrangeBasis_map {N : ℕ} (d : Fin N → ℝ) (j : Fin N) (w : ℂ) :
    ((lagrangeBasis d j).map (algebraMap ℝ ℂ)).eval w =
      ∏ k ∈ Finset.univ.erase j, (((d j : ℂ) - d k)⁻¹ * (w - d k)) := by
  simp [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor, Polynomial.map_prod, eval_prod]

theorem circle_sum_eval_lagrangeBasis_map {N : ℕ} (hN : 0 < N) {d : Fin N → ℝ}
    (hd : Function.Injective d) (w : ℂ) :
    ∑ j, ((lagrangeBasis d j).map (algebraMap ℝ ℂ)).eval w = 1 := by
  have h := Lagrange.sum_basis (s := Finset.univ) (v := d) (hd.injOn)
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have := congrArg (fun P : ℝ[X] => (P.map (algebraMap ℝ ℂ)).eval w) h
  simpa [Polynomial.map_sum, eval_finsetSum, lagrangeBasis] using this

theorem circle_inv_prod_sub_eq_sum {N : ℕ} (hN : 0 < N) {d : Fin N → ℝ}
    (hd : Function.Injective d) (z : ℂ) (hz : ∀ k, z ≠ d k) :
    (∏ k, (z - d k))⁻¹ =
      ∑ j, (∏ k ∈ Finset.univ.erase j, ((d j : ℂ) - d k)⁻¹) * (z - d j)⁻¹ := by
  have hne : ∀ k, z - d k ≠ 0 := fun k => sub_ne_zero.mpr (hz k)
  have hP : ∏ k, (z - d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hne k
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Finset.mul_sum, ← circle_sum_eval_lagrangeBasis_map hN hd z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circle_eval_lagrangeBasis_map, Finset.prod_mul_distrib, ← Finset.mul_prod_erase _ _
    (Finset.mem_univ j)]
  field_simp [hne j]

theorem circle_integral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : CircleIntegrable (fun z => ∑ i ∈ s, f i z) c R := by
      have : ∀ i ∈ s, CircleIntegrable (f i) c R := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      unfold CircleIntegrable at this ⊢
      convert IntervalIntegrable.sum s this using 1
      ext θ; simp [Finset.sum_apply]
    rw [circleIntegral.integral_add (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem circle_integral_kernelIntegrand {N : ℕ} (hN : 0 < N) (S : ℝ≥0) {d : Fin N → ℝ}
    (hd : StrictMono d) {R L : ℝ} (hC : AdmissibleContours d R L) (u v : ℝ) (w : ℂ)
    (hw : R < w.re) :
    (∮ z in C(0, R), kernelIntegrand S d u v z w) =
      2 * π * I * ∑ j, cexp ((w ^ 2 - 2 * (v : ℂ) * w - (d j : ℂ) ^ 2 + 2 * (u : ℂ) * d j) /
        (2 * (S : ℂ))) * ((lagrangeBasis d j).map (algebraMap ℝ ℂ)).eval w := by
  obtain ⟨hR, hdR, _⟩ := hC
  set G : ℂ → ℂ := fun z => cexp ((w ^ 2 - 2 * (v : ℂ) * w - z ^ 2 + 2 * (u : ℂ) * z) /
    (2 * (S : ℂ))) / (w - z) * ∏ k, (w - d k)
  set c : Fin N → ℂ := fun j => ∏ k ∈ Finset.univ.erase j, ((d j : ℂ) - d k)⁻¹
  have hwz : ∀ z : ℂ, ‖z‖ ≤ R → w - z ≠ 0 := by
    intro z hz h
    have : w.re = z.re := by rw [sub_eq_zero] at h; rw [h]
    have := Complex.re_le_norm z
    linarith
  have hzd : ∀ z : ℂ, ‖z‖ = R → ∀ k, z ≠ d k := by
    intro z hz k h
    have := hdR k
    rw [h, Complex.norm_real, Real.norm_eq_abs] at hz
    linarith
  have hGd : DifferentiableOn ℂ G (closedBall 0 R) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.mul ?_ (differentiableAt_const _)
    refine DifferentiableAt.div ?_ (differentiableAt_const _ |>.sub differentiableAt_id)
      (hwz z hz)
    fun_prop
  have hGc : DiffContOnCl ℂ G (ball 0 R) := hGd.diffContOnCl_ball subset_rfl
  have heq : Set.EqOn (fun z => kernelIntegrand S d u v z w)
      (fun z => ∑ j, (z - d j)⁻¹ • (c j * G z)) (sphere 0 R) := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    simp only [kernelIntegrand, smul_eq_mul, G, c]
    rw [Finset.prod_div_distrib, div_eq_mul_inv (∏ k, (w - d k)),
      circle_inv_prod_sub_eq_sum hN hd.injective z (hzd z hz), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [circleIntegral.integral_congr hR.le heq, circle_integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdj : (d j : ℂ) ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hdR j
    have h := DiffContOnCl.circleIntegral_sub_inv_smul (hGc.const_smul (c j)) hdj
    simp only [Pi.smul_apply, smul_eq_mul] at h
    simp only [smul_eq_mul]
    rw [h]
    congr 1
    have hwd : w - d j ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp only [sub_re, ofReal_re, zero_re] at this
      have := hdR j
      have := le_abs_self (d j)
      linarith
    simp only [G, c, circle_eval_lagrangeBasis_map, Finset.prod_mul_distrib]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    field_simp
  · intro j _
    refine ContinuousOn.circleIntegrable hR.le ?_
    simp only [smul_eq_mul]
    refine ContinuousOn.mul ?_ (continuousOn_const.mul
      (hGd.continuousOn.mono sphere_subset_closedBall))
    refine (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_
    rw [mem_sphere, dist_zero_right] at hz
    exact sub_ne_zero.mpr (hzd z hz j)

end BlockBand.Native.Johansson
