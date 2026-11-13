module

public import Mathlib
public import BlockBand.PointProcess.Vague

/-!
# The Fejér pair kernel on mass profiles

This file supplies the mark functional used for the vanishing of block atoms: a continuous
functional `markPairKernel M` on the mass-profile space `MassProfile = P(T)` (weak topology,
`T = ℝ/ℤ`) which

* dominates `Σ_k p_k²` on every finite atomic profile `Σ_k p_k δ_{x_k}`
  (`sum_sq_le_markPairKernel`, uniformly in the cut-off `M`), and
* converges, as `M → ∞` and for every fixed profile `ν`, to the sum of the squared
  atom masses `markAtomSq ν = ∫ ν({r}) dν(r)` (`tendsto_markPairKernel`).

The kernel is `h_M(x) = ‖(M+1)⁻¹ Σ_{m=0}^{M} e^{2πimx}‖²` (`fejerBump`), with
`h_M(0) = 1`, `0 ≤ h_M ≤ 1`, and `h_M(x) → 0` for `x ≠ 0`. No hypothesis or native
input is used; everything is proved from Mathlib.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.PointProcess.BlockAtom

open MeasureTheory Filter
open scoped Topology

/-- The Fejér bump `h_M(x) = ‖(M+1)⁻¹ Σ_{m=0}^{M} e^{2πimx}‖²` on the unit torus
`T = ℝ/ℤ`, for a cut-off `M : ℕ`. It is the pair kernel of the mark functional. -/
def fejerBump (M : ℕ) (x : Torus) : ℝ :=
  ‖((M : ℂ) + 1)⁻¹ * ∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x‖ ^ 2

/-- Every Fourier character has modulus one on the torus. -/
lemma norm_fourier_apply (n : ℤ) (x : Torus) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The normalization `(M+1)⁻¹` has norm `(M+1)⁻¹`. -/
lemma norm_inv_natCast_add_one (M : ℕ) : ‖((M : ℂ) + 1)⁻¹‖ = ((M : ℝ) + 1)⁻¹ := by
  rw [norm_inv]
  congr 1
  have h : ((M : ℂ) + 1) = (((M + 1 : ℕ)) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_natCast]
  push_cast
  rfl

/-- On the torus, `e^{2πimx} = (e^{2πix})^m` for natural `m`. -/
lemma fourier_natCast_apply (m : ℕ) (x : Torus) :
    fourier (m : ℤ) x = (fourier 1 x) ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, fourier_add, ih, pow_succ]

/-- `e^{2πix} ≠ 1` for every nonzero point of the unit torus. -/
lemma fourier_one_ne_one {x : Torus} (hx : x ≠ 0) : fourier 1 x ≠ 1 := by
  intro h
  apply hx
  have h0 : fourier 1 (0 : Torus) = 1 := fourier_eval_zero 1
  rw [← h0, fourier_one, fourier_one] at h
  exact AddCircle.injective_toCircle one_ne_zero (Circle.ext h)

/-- The Fejér bump is continuous on the torus. -/
theorem continuous_fejerBump (M : ℕ) : Continuous (fejerBump M) := by
  unfold fejerBump
  fun_prop

/-- The Fejér bump is nonnegative. -/
theorem fejerBump_nonneg (M : ℕ) (x : Torus) : 0 ≤ fejerBump M x := by
  unfold fejerBump
  positivity

/-- The Fejér bump is at most one, uniformly in `M` and `x`, by the triangle
inequality. -/
theorem fejerBump_le_one (M : ℕ) (x : Torus) : fejerBump M x ≤ 1 := by
  unfold fejerBump
  have hsum : ‖∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x‖ ≤ (M : ℝ) + 1 := by
    refine (norm_sum_le _ _).trans ?_
    simp
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h1 : ‖((M : ℂ) + 1)⁻¹ * ∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x‖ ≤ 1 := by
    rw [norm_mul, norm_inv_natCast_add_one]
    calc ((M : ℝ) + 1)⁻¹ * ‖∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x‖
        ≤ ((M : ℝ) + 1)⁻¹ * ((M : ℝ) + 1) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  exact pow_le_one₀ (norm_nonneg _) h1

/-- The Fejér bump equals one at the origin, for every `M`. -/
theorem fejerBump_zero (M : ℕ) : fejerBump M 0 = 1 := by
  unfold fejerBump
  have hne : ((M : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero M
  simp only [fourier_eval_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  rw [inv_mul_cancel₀ hne, norm_one, one_pow]

/-- Pointwise decay of the Fejér bump off the origin: for fixed `x ≠ 0` in the torus,
`h_M(x) ≤ 4 / (|e^{2πix} - 1|² (M+1)²) → 0` as `M → ∞`. -/
theorem tendsto_fejerBump {x : Torus} (hx : x ≠ 0) :
    Tendsto (fun M => fejerBump M x) atTop (𝓝 0) := by
  set e : ℂ := fourier 1 x with he_def
  have he : e ≠ 1 := fourier_one_ne_one hx
  have he1 : 0 < ‖e - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hnorm : ‖e‖ = 1 := norm_fourier_apply 1 x
  set C : ℝ := 2 / ‖e - 1‖ with hC
  have hbound : ∀ M : ℕ, fejerBump M x ≤ (1 / ((M : ℝ) + 1) * C) ^ 2 := by
    intro M
    unfold fejerBump
    have hS : ∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x
        = (e ^ (M + 1) - 1) / (e - 1) := by
      simp_rw [fourier_natCast_apply]
      exact geom_sum_eq he (M + 1)
    have hSle : ‖∑ m ∈ Finset.range (M + 1), fourier (m : ℤ) x‖ ≤ C := by
      rw [hS, norm_div, hC]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow, hnorm, one_pow, norm_one]
      norm_num
    rw [norm_mul, norm_inv_natCast_add_one, ← one_div]
    gcongr
  have hlim : Tendsto (fun M : ℕ => (1 / ((M : ℝ) + 1) * C) ^ 2) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C).pow 2
    simpa using h
  exact squeeze_zero (fun M => fejerBump_nonneg M x) hbound hlim

/-- `G_M(ν) = ∫∫ h_M(r - r') dν(r) dν(r')`: the Fejér pair functional on mass
profiles `ν ∈ P(T)`, for a cut-off `M : ℕ`. This is the mark functional for the vanishing of
block atoms. -/
def markPairKernel (M : ℕ) (ν : MassProfile) : ℝ :=
  ∫ r, ∫ r', fejerBump M (r - r') ∂(ν : Measure Torus) ∂(ν : Measure Torus)

/-- The joint kernel `(r, r') ↦ h_M(r - r')` is continuous on `T × T`. -/
lemma continuous_fejerBump_sub (M : ℕ) :
    Continuous (fun p : Torus × Torus => fejerBump M (p.1 - p.2)) :=
  (continuous_fejerBump M).comp (continuous_fst.sub continuous_snd)

/-- The inner integral `r ↦ ∫ h_M(r - r') dν(r')` has absolute value at most one. -/
lemma norm_inner_le_one (M : ℕ) (ν : MassProfile) (r : Torus) :
    ‖∫ r', fejerBump M (r - r') ∂(ν : Measure Torus)‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure Torus))
    (f := fun r' => fejerBump M (r - r')) (C := 1) (ae_of_all _ fun r' => by
      rw [Real.norm_of_nonneg (fejerBump_nonneg _ _)]
      exact fejerBump_le_one _ _)
  simpa using h

/-- The inner integral is strongly measurable in the outer variable. -/
lemma stronglyMeasurable_inner (M : ℕ) (ν : MassProfile) :
    StronglyMeasurable (fun r => ∫ r', fejerBump M (r - r') ∂(ν : Measure Torus)) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : Torus × Torus => fejerBump M (p.1 - p.2))
    (continuous_fejerBump_sub M).stronglyMeasurable

/-- The pair functional as a single integral against the product measure `ν ⊗ ν`. -/
lemma markPairKernel_eq_integral_prod (M : ℕ) (ν : MassProfile) :
    markPairKernel M ν = ∫ p, fejerBump M (p.1 - p.2)
      ∂((ν : Measure Torus).prod (ν : Measure Torus)) := by
  have hint : Integrable (fun p : Torus × Torus => fejerBump M (p.1 - p.2))
      ((ν : Measure Torus).prod (ν : Measure Torus)) :=
    Integrable.of_bound (continuous_fejerBump_sub M).aestronglyMeasurable 1
      (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (fejerBump_nonneg _ _)]
        exact fejerBump_le_one _ _)
  rw [integral_prod _ hint]
  rfl

/-- The pair functional `G_M` is continuous on `P(T)` for the weak topology. Proof:
 `G_M(ν) = ∫ h_M(r - r') d(ν ⊗ ν)`, the map
`ν ↦ ν ⊗ ν` is weakly continuous, and `h_M(r - r')` is bounded continuous on `T × T`. -/
theorem continuous_markPairKernel (M : ℕ) : Continuous (markPairKernel M) := by
  let F : BoundedContinuousFunction (Torus × Torus) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨_, continuous_fejerBump_sub M⟩
  have h1 := ProbabilityMeasure.continuous_integral_boundedContinuousFunction F
  have h2 : Continuous fun ν : MassProfile => ν.prod ν :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have h3 := h1.comp h2
  convert h3 using 1
  funext ν
  rw [markPairKernel_eq_integral_prod]
  simp [F, ProbabilityMeasure.toMeasure_prod]

/-- `G_M(ν) ≥ 0` for every profile `ν`. -/
theorem markPairKernel_nonneg (M : ℕ) (ν : MassProfile) : 0 ≤ markPairKernel M ν :=
  integral_nonneg fun _ => integral_nonneg fun _ => fejerBump_nonneg _ _

/-- `G_M(ν) ≤ 1` for every profile `ν`, uniformly in `M`. -/
theorem markPairKernel_le_one (M : ℕ) (ν : MassProfile) : markPairKernel M ν ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure Torus))
    (f := fun r => ∫ r', fejerBump M (r - r') ∂(ν : Measure Torus)) (C := 1)
    (ae_of_all _ fun r => norm_inner_le_one M ν r)
  simp only [probReal_univ, mul_one] at h
  exact (le_abs_self _).trans (by simpa [markPairKernel] using h)

/-- The sum of the squared atom masses of a profile `ν ∈ P(T)`, written as
`∫ ν({r}) dν(r)` (equal to `Σ_k p_k²` for `ν = Σ_k p_k δ_{x_k} + diffuse part`). It is
the limit object of the mark functional. -/
def markAtomSq (ν : MassProfile) : ℝ :=
  ∫ r, (ν : Measure Torus).real {r} ∂(ν : Measure Torus)

/-- For fixed `r`, `∫ h_M(r - r') dν(r') → ν({r})` by dominated convergence. -/
lemma tendsto_inner (ν : MassProfile) (r : Torus) :
    Tendsto (fun M => ∫ r', fejerBump M (r - r') ∂(ν : Measure Torus)) atTop
      (𝓝 ((ν : Measure Torus).real {r})) := by
  rw [← integral_indicator_one (measurableSet_singleton r)]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun M => ((continuous_fejerBump M).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (integrable_const 1)
    (fun M => ae_of_all _ fun r' => by
      rw [Real.norm_of_nonneg (fejerBump_nonneg _ _)]
      exact fejerBump_le_one _ _)
    (ae_of_all _ fun r' => ?_)
  by_cases h : r' = r
  · subst h
    simp only [sub_self, fejerBump_zero]
    rw [Set.indicator_of_mem (Set.mem_singleton r'), Pi.one_apply]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem (by simpa using h)]
    exact tendsto_fejerBump (sub_ne_zero.mpr (Ne.symm h))

/-- `G_M(ν) → Σ (atom masses of ν)²` as `M → ∞`, for every fixed profile `ν`. -/
theorem tendsto_markPairKernel (ν : MassProfile) :
    Tendsto (fun M => markPairKernel M ν) atTop (𝓝 (markAtomSq ν)) :=
  tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun M => (stronglyMeasurable_inner M ν).aestronglyMeasurable)
    (integrable_const 1)
    (fun M => ae_of_all _ fun r => norm_inner_le_one M ν r)
    (ae_of_all _ fun r => tendsto_inner ν r)

/-- An atomless profile has `markAtomSq ν = 0`. -/
theorem markAtomSq_eq_zero_of_noAtoms (ν : MassProfile)
    (h : ∀ r : Torus, (ν : Measure Torus) {r} = 0) : markAtomSq ν = 0 := by
  unfold markAtomSq
  simp [Measure.real, h]

/-- Domination on finite atomic profiles: if `ν = Σ_i q_i δ_{g_i}` (finite index set,
`q_i ≥ 0`, distinct points `g_i`), then `Σ_i q_i² ≤ G_M(ν)` for every cut-off `M`. The proof writes
`G_M(ν) = Σ_{i,j} q_i q_j h_M(g_i - g_j)` and keeps the diagonal, `h_M(0) = 1`;
the off-diagonal terms are nonnegative, so injectivity of `g` is not needed (it is kept as
the unused hypothesis `_hg`). -/
theorem sum_sq_le_markPairKernel {ι : Type*} [Fintype ι] (M : ℕ) (ν : MassProfile)
    (q : ι → ℝ) (g : ι → Torus) (hq : ∀ i, 0 ≤ q i) (_hg : Function.Injective g)
    (hν : (ν : Measure Torus) = ∑ i, ENNReal.ofReal (q i) • Measure.dirac (g i)) :
    ∑ i, q i ^ 2 ≤ markPairKernel M ν := by
  have hint : ∀ (f : Torus → ℝ) (i : ι),
      Integrable f (ENNReal.ofReal (q i) • Measure.dirac (g i)) := fun f i =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hI : ∀ f : Torus → ℝ, ∫ r, f r ∂(ν : Measure Torus) = ∑ i, q i * f (g i) := by
    intro f
    rw [hν, integral_finsetSum_measure (fun i _ => hint f i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq i), smul_eq_mul]
  have hG : markPairKernel M ν = ∑ i, q i * ∑ j, q j * fejerBump M (g i - g j) := by
    unfold markPairKernel
    simp only [hI]
  rw [hG]
  refine Finset.sum_le_sum fun i _ => ?_
  have hdiag : q i ^ 2 = q i * (q i * fejerBump M (g i - g i)) := by
    rw [sub_self, fejerBump_zero]
    ring
  rw [hdiag]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (f := fun j => q j * fejerBump M (g i - g j))
      (fun j _ => mul_nonneg (hq j) (fejerBump_nonneg _ _)) (Finset.mem_univ i)) (hq i)

end BlockBand.PointProcess.BlockAtom
