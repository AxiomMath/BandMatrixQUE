module

public import Mathlib
public import BlockBand.GaussianCalculus.ProductDensity
public import BlockBand.Model.Construction.GaussianSmoothCutoff

/-!
# Multivariate weak Gaussian integration by parts

For `x ~ gaussianProduct v` and `g` the weak (distributional) `i`-th partial derivative of
`f`, `E[xᵢ f] = vᵢ E[g]` (`multivariateGaussianIBP_holds`). The proof tests the weak
derivative against tensor products of compactly supported cutoffs times the Gaussian density
and removes the cutoffs by dominated convergence.

Law: `gaussianProduct v` on `ι → ℝ`, finite `ι`. Weak derivatives are the distributional ones of
`HasWeakCoordPartial` (smooth compactly supported tests, Lebesgue measure). The hypotheses are three
Gaussian integrability conditions; a degenerate differentiated coordinate vanishes almost surely, so
both sides are then zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Model.Construction (gaussianSmoothCutoff exists_bound_deriv_gaussianSmoothCutoff
  gaussianSmoothCutoff_eventually contDiff_gaussianDensity hasDerivAt_gaussianDensity)
open scoped NNReal Topology ContDiff

/-- Dominated convergence for uniformly bounded scalar multipliers that are eventually
equal to a constant `L` at every point: `∫ aₙ • F → L • ∫ F` for every integrable `F`, on any
measure space, in any complete real normed target. -/
theorem tendsto_integral_smul_of_eventually_eq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X)
    (a : ℕ → X → ℝ) (L M : ℝ) (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (hM : ∀ n x, |a n x| ≤ M) (hL : ∀ x, ∀ᶠ n in atTop, a n x = L)
    {F : X → E} (hF : Integrable F μ) :
    Tendsto (fun n => ∫ x, a n x • F x ∂μ) atTop (𝓝 (L • ∫ x, F x ∂μ)) := by
  rw [← integral_smul]
  apply tendsto_integral_of_dominated_convergence (fun x => M * ‖F x‖)
  · exact fun n => (ha n).smul hF.aestronglyMeasurable
  · exact hF.norm.const_mul M
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM n x) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun x => by
      have he : (fun n => a n x • F x) =ᶠ[atTop] fun _ => L • F x := by
        filter_upwards [hL x] with n hn
        rw [hn]
      exact (tendsto_congr' he).mpr tendsto_const_nhds

/-- Integrability of a bounded measurable multiple of an integrable function. -/
theorem integrable_smul_of_bounded {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    (a : X → ℝ) (M : ℝ) (ha : AEStronglyMeasurable a μ) (hM : ∀ x, |a x| ≤ M)
    {F : X → E} (hF : Integrable F μ) : Integrable (fun x => a x • F x) μ := by
  apply (hF.norm.const_mul M).mono' (ha.smul hF.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖a x • F x‖ ≤ M * ‖F x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `coordPartial` of a tensor product `x ↦ ∏ⱼ ψⱼ (x j)` whose `i`-th factor has derivative
`d` at `x i`: it is `d · ∏_{j ≠ i} ψⱼ (x j)`. -/
theorem coordPartial_tensor (ψ : ι → ℝ → ℝ) (i : ι) (x : ι → ℝ) (d : ℝ)
    (hd : HasDerivAt (ψ i) d (x i)) :
    coordPartial (fun y => ∏ j, ψ j (y j)) i x = d * ∏ j ∈ Finset.univ.erase i, ψ j (x j) := by
  have hfun : (fun s => ∏ j, ψ j (Function.update x i s j)) =
      fun s => ψ i s * ∏ j ∈ Finset.univ.erase i, ψ j (x j) := by
    funext s
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold coordPartial
  rw [hfun]
  exact (hd.mul_const _).deriv

omit [DecidableEq ι] in
/-- A tensor product of compactly supported functions of the coordinates is compactly
supported, as soon as every factor vanishes outside `[-R, R]`. -/
theorem hasCompactSupport_tensor (ψ : ι → ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hψ : ∀ j s, R < |s| → ψ j s = 0) :
    HasCompactSupport (fun y : ι → ℝ => ∏ j, ψ j (y j)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR] at hx
  simp only [not_forall, not_le] at hx
  obtain ⟨j, hj⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) (hψ j (x j) (by simpa [Real.norm_eq_abs] using hj))

/-- The real clause with all variances nonzero. -/
theorem multivariateGaussianIBP_of_ne_zero {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : ι → ℝ≥0) (hv : ∀ j, v j ≠ 0) (i : ι) {f g : (ι → ℝ) → E}
    (hweak : HasWeakCoordPartial i f g)
    (hf : Integrable f (gaussianProduct v)) (hg : Integrable g (gaussianProduct v))
    (hcoord : Integrable (fun x => x i • f x) (gaussianProduct v)) :
    (∫ x, x i • f x ∂gaussianProduct v) = (v i : ℝ) • ∫ x, g x ∂gaussianProduct v := by
  have hvR : (v i : ℝ) ≠ 0 := by exact_mod_cast hv i
  let ρ : (ι → ℝ) → ℝ := productDensity v
  let F : (ι → ℝ) → E := fun x => ρ x • f x
  let D : (ι → ℝ) → E := fun x => ρ x • g x
  let C : (ι → ℝ) → E := fun x => ρ x • (x i • f x)
  have hF : Integrable F := (integrable_gaussianProduct_iff v hv f).mp hf
  have hD : Integrable D := (integrable_gaussianProduct_iff v hv g).mp hg
  have hC : Integrable C := (integrable_gaussianProduct_iff v hv _).mp hcoord
  let c : ℕ → ℝ → ℝ := fun n => gaussianSmoothCutoff n
  have hc_cont (n : ℕ) : Continuous (c n) := (gaussianSmoothCutoff n).continuous
  have hc_nonneg (n : ℕ) (s : ℝ) : 0 ≤ c n s := (gaussianSmoothCutoff n).nonneg
  have hc_le (n : ℕ) (s : ℝ) : c n s ≤ 1 := (gaussianSmoothCutoff n).le_one
  have hc_diff (n : ℕ) : ContDiff ℝ 1 (c n) := (gaussianSmoothCutoff n).contDiff
  let K : ℕ → (ι → ℝ) → ℝ := fun n x => ∏ j, c n (x j)
  let Q : ℕ → (ι → ℝ) → ℝ := fun n x => ∏ j ∈ Finset.univ.erase i, c n (x j)
  let err : ℕ → (ι → ℝ) → ℝ := fun n x => deriv (c n) (x i) * Q n x
  have hQ_nonneg (n : ℕ) (x : ι → ℝ) : 0 ≤ Q n x :=
    Finset.prod_nonneg fun j _ => hc_nonneg n (x j)
  have hQ_le (n : ℕ) (x : ι → ℝ) : Q n x ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => hc_nonneg n (x j)) fun j _ => hc_le n (x j)
  have hK_eq (n : ℕ) (x : ι → ℝ) : K n x = c n (x i) * Q n x :=
    (Finset.mul_prod_erase Finset.univ (fun j => c n (x j)) (Finset.mem_univ i)).symm
  have hρ_eq (x : ι → ℝ) : ρ x = gaussianPDFReal 0 (v i) (x i) *
      ∏ j ∈ Finset.univ.erase i, gaussianPDFReal 0 (v j) (x j) :=
    (Finset.mul_prod_erase Finset.univ (fun j => gaussianPDFReal 0 (v j) (x j))
      (Finset.mem_univ i)).symm
  have hK_cont (n : ℕ) : Continuous (K n) :=
    continuous_finsetProd _ fun j _ => (hc_cont n).comp (continuous_apply j)
  have hQ_cont (n : ℕ) : Continuous (Q n) :=
    continuous_finsetProd _ fun j _ => (hc_cont n).comp (continuous_apply j)
  have herr_cont (n : ℕ) : Continuous (err n) :=
    (((hc_diff n).continuous_deriv le_rfl).comp (continuous_apply i)).mul (hQ_cont n)
  have hK_bound (n : ℕ) (x : ι → ℝ) : |K n x| ≤ 1 := by
    rw [hK_eq, abs_of_nonneg (mul_nonneg (hc_nonneg n _) (hQ_nonneg n x))]
    exact (mul_le_mul (hc_le n _) (hQ_le n x) (hQ_nonneg n x) zero_le_one).trans_eq (one_mul 1)
  obtain ⟨B, hB0, hB⟩ := exists_bound_deriv_gaussianSmoothCutoff
  have herr_bound (n : ℕ) (x : ι → ℝ) : |err n x| ≤ B := by
    change |deriv (c n) (x i) * Q n x| ≤ B
    rw [abs_mul, abs_of_nonneg (hQ_nonneg n x)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hQ_le n x)).trans
      (by simpa only [Real.norm_eq_abs] using hB n (x i))
  have hev (x : ι → ℝ) : ∀ᶠ n in atTop, ∀ j, c n (x j) = 1 ∧ deriv (c n) (x j) = 0 :=
    Filter.eventually_all.mpr fun j => gaussianSmoothCutoff_eventually (x j)
  have hK_lim (x : ι → ℝ) : ∀ᶠ n in atTop, K n x = 1 := by
    filter_upwards [hev x] with n hn
    exact Finset.prod_eq_one fun j _ => (hn j).1
  have herr_lim (x : ι → ℝ) : ∀ᶠ n in atTop, err n x = 0 := by
    filter_upwards [hev x] with n hn
    change deriv (c n) (x i) * Q n x = 0
    rw [(hn i).2, zero_mul]
  have heq (n : ℕ) :
      -((v i : ℝ)⁻¹) • (∫ x, K n x • C x) + (∫ x, err n x • F x) =
        -(∫ x, K n x • D x) := by
    let ψ : ι → ℝ → ℝ := fun j s => gaussianPDFReal 0 (v j) s * c n s
    have hψ (j : ι) : ContDiff ℝ ∞ (ψ j) :=
      (contDiff_gaussianDensity 0 (v j)).mul (gaussianSmoothCutoff n).contDiff
    have hφ : ContDiff ℝ ∞ (fun y : ι → ℝ => ∏ j, ψ j (y j)) :=
      contDiff_prod fun j _ => (hψ j).comp (contDiff_apply ℝ ℝ j)
    have hφs : HasCompactSupport (fun y : ι → ℝ => ∏ j, ψ j (y j)) := by
      apply hasCompactSupport_tensor ψ (2 * ((n : ℝ) + 1)) (by positivity)
      intro j s hs
      have h0 : c n s = 0 := (gaussianSmoothCutoff n).zero_of_le_dist (by
        change 2 * ((n : ℝ) + 1) ≤ dist s 0
        rw [Real.dist_eq, sub_zero]
        exact hs.le)
      change gaussianPDFReal 0 (v j) s * c n s = 0
      rw [h0, mul_zero]
    have hda (s : ℝ) : HasDerivAt (ψ i)
        ((-(s / (v i : ℝ)) * gaussianPDFReal 0 (v i) s) * c n s +
          gaussianPDFReal 0 (v i) s * deriv (c n) s) s := by
      simpa only [sub_zero] using (hasDerivAt_gaussianDensity 0 (v i) (hv i) s).fun_mul
        (((hc_diff n).differentiable (by norm_num) s).hasDerivAt)
    have htest := hweak.2.2 _ hφ hφs
    have hleft (x : ι → ℝ) : coordPartial (fun y : ι → ℝ => ∏ j, ψ j (y j)) i x • f x =
        -((v i : ℝ)⁻¹) • (K n x • C x) + err n x • F x := by
      rw [coordPartial_tensor ψ i x _ (hda (x i)), Finset.prod_mul_distrib]
      change _ = -((v i : ℝ)⁻¹) • (K n x • (ρ x • (x i • f x))) +
        (deriv (c n) (x i) * Q n x) • (ρ x • f x)
      rw [hK_eq, hρ_eq]
      simp only [smul_smul, ← add_smul, div_eq_mul_inv]
      congr 1
      ring
    have hright (x : ι → ℝ) : (∏ j, ψ j (x j)) • g x = K n x • D x := by
      change (∏ j, gaussianPDFReal 0 (v j) (x j) * c n (x j)) • g x =
        (∏ j, c n (x j)) • (productDensity v x • g x)
      rw [Finset.prod_mul_distrib, smul_smul, productDensity, mul_comm]
    simp_rw [hleft, hright] at htest
    have hs : Integrable (fun x => -((v i : ℝ)⁻¹) • (K n x • C x)) :=
      (integrable_smul_of_bounded volume (K n) 1 (hK_cont n).aestronglyMeasurable
        (hK_bound n) hC).smul _
    rw [integral_add hs (integrable_smul_of_bounded volume (err n) B
      (herr_cont n).aestronglyMeasurable (herr_bound n) hF), integral_smul] at htest
    exact htest
  have hL := ((tendsto_integral_smul_of_eventually_eq volume K 1 1
      (fun n => (hK_cont n).aestronglyMeasurable) hK_bound hK_lim hC).const_smul
      (-((v i : ℝ)⁻¹))).add
    (tendsto_integral_smul_of_eventually_eq volume err 0 B
      (fun n => (herr_cont n).aestronglyMeasurable) herr_bound herr_lim hF)
  have hR := (tendsto_integral_smul_of_eventually_eq volume K 1 1
      (fun n => (hK_cont n).aestronglyMeasurable) hK_bound hK_lim hD).neg
  have hR' : Tendsto (fun n : ℕ => -((v i : ℝ)⁻¹) • (∫ x, K n x • C x) +
      (∫ x, err n x • F x)) atTop (𝓝 (-((1 : ℝ) • ∫ x, D x))) :=
    hR.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  have h := tendsto_nhds_unique hL hR'
  have h' : (v i : ℝ)⁻¹ • (∫ x, C x) = ∫ x, D x := by
    apply neg_inj.mp
    simpa only [one_smul, zero_smul, add_zero, neg_smul] using h
  have hscaled := congrArg (fun z : E => (v i : ℝ) • z) h'
  simp only [smul_smul, mul_inv_cancel₀ hvR, one_smul] at hscaled
  rw [integral_gaussianProduct_eq v hv, integral_gaussianProduct_eq v hv]
  exact hscaled

/-- Gaussian integration by parts, multivariate real clause (`MultivariateGaussianIBP`). Law
`gaussianProduct v` on `ι → ℝ` (finite `ι`, coordinate `j` centered of variance `v j`); all
coordinates other than the differentiated `i` have positive variance; `f g : (ι → ℝ) → E`, `E` a
complete real normed space, `g` the distributional (Lebesgue, smooth compact tests) weak `i`-th
partial of `f`; Gaussian integrability of `f`, `g`, `xᵢ f`. Conclusion `E[xᵢ f] = vᵢ E[g]`. If
`v i = 0` both sides vanish (`xᵢ = 0` a.s.); otherwise the cutoff argument above. -/
theorem multivariateGaussianIBP_holds : MultivariateGaussianIBP := by
  intro ι _ _ v E _ _ _ i f g hv hweak hf hg hcoord
  by_cases hi : v i = 0
  · have hz : (fun x : ι → ℝ => x i • f x) =ᵐ[gaussianProduct v] fun _ => 0 := by
      filter_upwards [ae_gaussianProduct_coord_eq_zero v i hi] with x hx
      rw [hx, zero_smul]
    rw [integral_congr_ae hz, integral_zero, hi, NNReal.coe_zero, zero_smul]
  · have hv' : ∀ j, v j ≠ 0 := fun j => by
      by_cases hj : j = i
      · exact hj ▸ hi
      · exact (hv j hj).ne'
    exact multivariateGaussianIBP_of_ne_zero v hv' i hweak hf hg hcoord

end BlockBand.GaussianCalculus
