module

public import Mathlib
public import BlockBand.GaussianCalculus.LpGradient
public import BlockBand.GaussianCalculus.PoincareIBP

/-!
# The Gaussian Poincaré inequality with constant one

Proof by rotation interpolation and Gaussian integration by parts. Put `g = f - E f`, `X, Y`
independent `μ`-vectors and `(X_θ, X'_θ) = pairRot θ (X, Y)`. With the real inner product of `ℂ`,
`E‖g‖² = E⟪g(X) - g(Y), g(X)⟫ = ∫₀^{π/2} E⟪Dg(X_θ)X'_θ, g(X)⟫ dθ` (fundamental theorem of
calculus and Fubini). For fixed `θ`, rotation invariance and the involution
`pairRot θ ∘ pairRot θ = id` turn the inner expectation into
`E⟪Dg(X)Y, g(sin θ X + cos θ Y)⟫`; coordinatewise Gaussian IBP in `Y` (`integral_coord_mul_eq`)
gives `cos θ ∑ᵢ vᵢ E⟪∂ᵢg(X), ∂ᵢg(sin θ X + cos θ Y)⟫`, bounded by `cos θ ∑ᵢ vᵢ E‖∂ᵢ g‖²`
since `sin θ X + cos θ Y ~ μ`. Finally `∫₀^{π/2} cos θ dθ = 1`. Every integrability fact
comes from the `L²` hypotheses (products of independent `L²` factors, and AM–GM).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianCalculus

open MeasureTheory ProbabilityTheory Set
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal InnerProductSpace

/-- `pairRot θ` is an involution. -/
theorem pairRot_pairRot {ι : Type} (θ : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    pairRot θ (pairRot θ z) = z := by
  ext i <;> simp only [pairRot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · linear_combination z.1 i * Real.sin_sq_add_cos_sq θ
  · linear_combination z.2 i * Real.sin_sq_add_cos_sq θ

/-- AM–GM for the real inner product on `ℂ`. -/
theorem norm_real_inner_le_half (a b : ℂ) : ‖⟪a, b⟫_ℝ‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- The real inner product of two `L²` complex functions is integrable. -/
theorem integrable_real_inner_of_memLp {α : Type*} [MeasurableSpace α] {P : Measure α}
    {a b : α → ℂ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    Integrable (fun z => ⟪a z, b z⟫_ℝ) P := by
  have ha2 := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hb2 := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  exact ((ha2.add hb2).div_const 2).mono' (ha.aestronglyMeasurable.inner hb.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => norm_real_inner_le_half (a z) (b z))

/-- `|E⟪a, b⟫| ≤ (E‖a‖² + E‖b‖²)/2` for `L²` complex functions. -/
theorem abs_integral_real_inner_le {α : Type*} [MeasurableSpace α] {P : Measure α}
    {a b : α → ℂ} (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    |∫ z, ⟪a z, b z⟫_ℝ ∂P| ≤ (∫ z, ‖a z‖ ^ 2 ∂P + ∫ z, ‖b z‖ ^ 2 ∂P) / 2 := by
  have ha2 := (memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hb2 := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  rw [← integral_add ha2 hb2, ← integral_div, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le ((ha2.add hb2).div_const 2)
    (Filter.Eventually.of_forall fun z => norm_real_inner_le_half (a z) (b z))

variable {ι : Type} [Fintype ι]

/-- Integrals against `μ ⊗ μ` are invariant under `pairRot θ`. -/
theorem integral_comp_pairRot (v : ι → ℝ≥0) (θ : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (φ : (ι → ℝ) × (ι → ℝ) → E)
    (hφ : AEStronglyMeasurable φ ((gaussianProduct v).prod (gaussianProduct v))) :
    ∫ z, φ (pairRot θ z) ∂(gaussianProduct v).prod (gaussianProduct v) =
      ∫ z, φ z ∂(gaussianProduct v).prod (gaussianProduct v) := by
  have hR := measurePreserving_pairRot v θ
  rw [← integral_map hR.measurable.aemeasurable (by rwa [hR.map_eq]), hR.map_eq]

/-- Integrals of functions of the first factor of `μ ⊗ μ`. -/
theorem integral_comp_fst_gaussianProduct (v : ι → ℝ≥0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ψ : (ι → ℝ) → E) (hψ : AEStronglyMeasurable ψ (gaussianProduct v)) :
    ∫ z, ψ z.1 ∂(gaussianProduct v).prod (gaussianProduct v) = ∫ x, ψ x ∂gaussianProduct v := by
  have hγ : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hμ : IsProbabilityMeasure (gaussianProduct v) := by
    unfold gaussianProduct
    infer_instance
  have hF : MeasurePreserving Prod.fst ((gaussianProduct v).prod (gaussianProduct v))
      (gaussianProduct v) := measurePreserving_fst
  rw [← integral_map hF.measurable.aemeasurable (by rwa [hF.map_eq]), hF.map_eq]

variable [DecidableEq ι]

set_option maxHeartbeats 1000000 in
/-- Poincaré inequality for centred functions. Law `μ = gaussianProduct v` (any variances, zero
allowed). For complex `C¹` `g` with `E g = 0` and `g`, all `∂ᵢ g` in `L²(μ)`,
`E‖g‖² ≤ ∑ᵢ vᵢ E‖∂ᵢ g‖²`. -/
theorem poincare_centered (v : ι → ℝ≥0) {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hg2 : MemLp g 2 (gaussianProduct v))
    (hP2 : ∀ i, MemLp (fun x => fderiv ℝ g x (Pi.single i 1)) 2 (gaussianProduct v))
    (hmean : ∫ x, g x ∂gaussianProduct v = 0) :
    ∫ x, ‖g x‖ ^ 2 ∂gaussianProduct v ≤
      ∑ i, (v i : ℝ) * ∫ x, ‖fderiv ℝ g x (Pi.single i 1)‖ ^ 2 ∂gaussianProduct v := by
  have hγ : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hμ : IsProbabilityMeasure (gaussianProduct v) := by
    unfold gaussianProduct
    infer_instance
  set μ := gaussianProduct v with hμdef
  set κ := μ.prod μ with hκdef
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  have hgc : Continuous g := hg.continuous
  let P : ι → (ι → ℝ) → ℂ := fun i x => fderiv ℝ g x (Pi.single i 1)
  let D : (ι → ℝ) × (ι → ℝ) → ℂ := fun z => fderiv ℝ g z.1 z.2
  have hPc (i : ι) : Continuous (P i) := hcont.clm_apply continuous_const
  have hDc : Continuous D := (hcont.comp continuous_fst).clm_apply continuous_snd
  have hrc : Continuous (fun q : ℝ × ((ι → ℝ) × (ι → ℝ)) => pairRot q.1 q.2) := continuous_pairRot
  have hrθ (θ : ℝ) : Continuous (fun z : (ι → ℝ) × (ι → ℝ) => pairRot θ z) :=
    hrc.comp (continuous_const.prodMk continuous_id)
  -- `L²` facts on `κ = μ ⊗ μ`.
  have hcoord (i : ι) : Integrable (fun y : ι → ℝ => (y i) ^ 2) μ := by
    have h1 : MemLp id 2 (gaussianReal 0 (v i)) := by
      simpa using memLp_id_gaussianReal (μ := 0) (v := v i) 2
    exact (h1.comp_measurePreserving
      (measurePreserving_eval (fun j => gaussianReal 0 (v j)) i)).integrable_sq
  have hL1 (i : ι) : MemLp (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i • P i z.1) 2 κ := by
    have hm : AEStronglyMeasurable (fun z : (ι → ℝ) × (ι → ℝ) => z.2 i • P i z.1) κ :=
      (((continuous_apply i).comp continuous_snd).smul
        ((hPc i).comp continuous_fst)).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
    have hPsq := (memLp_two_iff_integrable_sq_norm (hP2 i).aestronglyMeasurable).mp (hP2 i)
    convert hPsq.mul_prod (hcoord i) using 1
    funext z
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
  have hD2 : MemLp D 2 κ := by
    have hDeq : D = fun z => ∑ i, z.2 i • P i z.1 :=
      funext fun z => fderiv_apply_eq_sum g z.1 z.2
    rw [hDeq]
    exact memLp_finsetSum _ fun i _ => hL1 i
  have hg2κ : MemLp (fun z : (ι → ℝ) × (ι → ℝ) => g z.1) 2 κ :=
    hg2.comp_measurePreserving measurePreserving_fst
  have hgR (θ : ℝ) : MemLp (fun z => g (pairRot θ z).1) 2 κ :=
    hg2κ.comp_measurePreserving (measurePreserving_pairRot v θ)
  have hPκ (i : ι) : MemLp (fun z : (ι → ℝ) × (ι → ℝ) => P i z.1) 2 κ :=
    (hP2 i).comp_measurePreserving measurePreserving_fst
  have hPR (i : ι) (θ : ℝ) : MemLp (fun z => P i (pairRot θ z).1) 2 κ :=
    (hPκ i).comp_measurePreserving (measurePreserving_pairRot v θ)
  have hDR (θ : ℝ) : MemLp (fun z => D (pairRot θ z)) 2 κ :=
    hD2.comp_measurePreserving (measurePreserving_pairRot v θ)
  have hga : Integrable g μ := hg2.integrable (by norm_num)
  -- Step A: the variance as `E⟪g(X) - g(Y), g(X)⟫`.
  have hstepA : ∫ x, ‖g x‖ ^ 2 ∂μ = ∫ z, ⟪g z.1 - g z.2, g z.1⟫_ℝ ∂κ := by
    have hg2κ' : MemLp (fun z : (ι → ℝ) × (ι → ℝ) => g z.2) 2 κ :=
      hg2.comp_measurePreserving measurePreserving_snd
    have i1 := integrable_real_inner_of_memLp hg2κ hg2κ
    have i2 := integrable_real_inner_of_memLp hg2κ' hg2κ
    simp_rw [inner_sub_left]
    rw [integral_sub i1 i2]
    have e1 : ∫ z, ⟪g z.1, g z.1⟫_ℝ ∂κ = ∫ x, ‖g x‖ ^ 2 ∂μ := by
      rw [hκdef, hμdef, integral_comp_fst_gaussianProduct v (fun x => ⟪g x, g x⟫_ℝ)
        (hgc.inner hgc).aestronglyMeasurable]
      simp_rw [real_inner_self_eq_norm_sq]
    have e2 : ∫ z, ⟪g z.2, g z.1⟫_ℝ ∂κ = 0 := by
      rw [integral_prod _ i2]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero _ _)
      show ∫ y, ⟪g y, g x⟫_ℝ ∂μ = 0
      simp_rw [real_inner_comm (g x)]
      rw [integral_inner hga, hmean, inner_zero_right]
    rw [e1, e2, sub_zero]
  -- Step B: the fundamental theorem of calculus along the rotation.
  let ν : Measure ℝ := volume.restrict (Ioc 0 (Real.pi / 2))
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    change volume.restrict (Ioc (0 : ℝ) (Real.pi / 2)) univ < ⊤
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  let H : (ι → ℝ) × (ι → ℝ) → ℝ → ℝ := fun z θ => ⟪D (pairRot θ z), g z.1⟫_ℝ
  have hstepB (z : (ι → ℝ) × (ι → ℝ)) : ⟪g z.1 - g z.2, g z.1⟫_ℝ = ∫ θ, H z θ ∂ν := by
    have hcz : Continuous (fun θ : ℝ => pairRot θ z) :=
      continuous_pairRot.comp (continuous_id.prodMk continuous_const)
    have hc : Continuous (fun θ : ℝ => fderiv ℝ g (pairRot θ z).1 (pairRot θ z).2) :=
      (hcont.comp hcz.fst).clm_apply hcz.snd
    have hint : Integrable (fun θ : ℝ => fderiv ℝ g (pairRot θ z).1 (pairRot θ z).2) ν :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
        (hc.intervalIntegrable _ _)
    rw [sub_eq_integral_pairRot hg z, intervalIntegral.integral_of_le (by positivity),
      real_inner_comm, ← integral_inner hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun θ => real_inner_comm _ _)
  -- Step C: Fubini in `(z, θ)`.
  have hHint : Integrable (Function.uncurry H) (κ.prod ν) := by
    have hHc : Continuous (Function.uncurry H) :=
      (hDc.comp (hrc.comp (continuous_snd.prodMk continuous_fst))).inner
        (hgc.comp (continuous_fst.comp continuous_fst))
    have hA : Integrable (fun q : ((ι → ℝ) × (ι → ℝ)) × ℝ => ‖D (pairRot q.2 q.1)‖ ^ 2)
        (κ.prod ν) := by
      have hAc : Continuous (fun q : ((ι → ℝ) × (ι → ℝ)) × ℝ => ‖D (pairRot q.2 q.1)‖ ^ 2) :=
        (continuous_norm.comp (hDc.comp (hrc.comp (continuous_snd.prodMk continuous_fst)))).pow 2
      rw [integrable_prod_iff' hAc.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun θ =>
        (memLp_two_iff_integrable_sq_norm (hDR θ).aestronglyMeasurable).mp (hDR θ), ?_⟩
      have hconst (θ : ℝ) : ∫ z, ‖‖D (pairRot θ z)‖ ^ 2‖ ∂κ = ∫ z, ‖‖D z‖ ^ 2‖ ∂κ :=
        integral_comp_pairRot v θ (fun z => ‖‖D z‖ ^ 2‖)
          ((continuous_norm.comp ((continuous_norm.comp hDc).pow 2)).aestronglyMeasurable)
      exact (integrable_const (∫ z, ‖‖D z‖ ^ 2‖ ∂κ)).congr
        (Filter.Eventually.of_forall fun θ => (hconst θ).symm)
    have hB : Integrable (fun q : ((ι → ℝ) × (ι → ℝ)) × ℝ => ‖g q.1.1‖ ^ 2) (κ.prod ν) :=
      ((memLp_two_iff_integrable_sq_norm hg2κ.aestronglyMeasurable).mp hg2κ).comp_fst ν
    exact ((hA.add hB).div_const 2).mono' hHc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_real_inner_le_half _ _)
  have hswap : ∫ z, ∫ θ, H z θ ∂ν ∂κ = ∫ θ, ∫ z, H z θ ∂κ ∂ν := integral_integral_swap hHint
  -- Step D: for fixed `θ`, rotate back and integrate by parts in `Y`.
  have hJ (θ : ℝ) : ∫ z, H z θ ∂κ =
      Real.cos θ * ∑ i, (v i : ℝ) * ∫ z, ⟪P i z.1, P i (pairRot θ z).1⟫_ℝ ∂κ := by
    have e1 : ∫ z, H z θ ∂κ = ∫ w, ⟪D w, g (pairRot θ w).1⟫_ℝ ∂κ := by
      have h := integral_comp_pairRot v θ (fun w => ⟪D w, g (pairRot θ w).1⟫_ℝ)
        ((hDc.inner (hgc.comp (continuous_fst.comp (hrθ θ)))).aestronglyMeasurable)
      simp only [pairRot_pairRot] at h
      exact h
    have hΦ : Integrable (fun w => ⟪D w, g (pairRot θ w).1⟫_ℝ) κ :=
      integrable_real_inner_of_memLp hD2 (hgR θ)
    rw [e1, integral_prod _ hΦ]
    have hA (i : ι) : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
        ⟪z.2 i • P i z.1, g (pairRot θ z).1⟫_ℝ) κ :=
      integrable_real_inner_of_memLp (hL1 i) (hgR θ)
    have hB (i : ι) : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
        ⟪P i z.1, g (pairRot θ z).1⟫_ℝ) κ :=
      integrable_real_inner_of_memLp (hPκ i) (hgR θ)
    have hC (i : ι) : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
        ⟪P i z.1, P i (pairRot θ z).1⟫_ℝ) κ :=
      integrable_real_inner_of_memLp (hPκ i) (hPR i θ)
    have hA' : ∀ᵐ x ∂μ, ∀ i, Integrable (fun y : ι → ℝ =>
        ⟪y i • P i x, g (pairRot θ (x, y)).1⟫_ℝ) μ :=
      ae_all_iff.mpr fun i => (hA i).prod_right_ae
    have hB' : ∀ᵐ x ∂μ, ∀ i, Integrable (fun y : ι → ℝ =>
        ⟪P i x, g (pairRot θ (x, y)).1⟫_ℝ) μ :=
      ae_all_iff.mpr fun i => (hB i).prod_right_ae
    have hC' : ∀ᵐ x ∂μ, ∀ i, Integrable (fun y : ι → ℝ =>
        ⟪P i x, P i (pairRot θ (x, y)).1⟫_ℝ) μ :=
      ae_all_iff.mpr fun i => (hC i).prod_right_ae
    have hsec : ∀ᵐ x ∂μ, ∫ y, ⟪D (x, y), g (pairRot θ (x, y)).1⟫_ℝ ∂μ =
        Real.cos θ * ∑ i, (v i : ℝ) * ∫ y, ⟪P i x, P i (pairRot θ (x, y)).1⟫_ℝ ∂μ := by
      filter_upwards [hA', hB', hC'] with x hxA hxB hxC
      have hexpand : (fun y => ⟪D (x, y), g (pairRot θ (x, y)).1⟫_ℝ) =
          fun y => ∑ i, ⟪y i • P i x, g (pairRot θ (x, y)).1⟫_ℝ := by
        funext y
        change ⟪fderiv ℝ g x y, g (pairRot θ (x, y)).1⟫_ℝ = _
        rw [fderiv_apply_eq_sum g x y, sum_inner]
      rw [hexpand, integral_finsetSum _ fun i _ => hxA i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [real_inner_smul_left]
      have hderiv : ∀ (y : ι → ℝ) (t : ℝ),
          HasDerivAt (fun s => ⟪P i x, g (pairRot θ (x, Function.update y i s)).1⟫_ℝ)
            (Real.cos θ * ⟪P i x, P i (pairRot θ (x, Function.update y i t)).1⟫_ℝ) t := by
        intro y t
        have h1 : HasDerivAt (fun s => (pairRot θ (x, Function.update y i s)).1)
            (Real.cos θ • Pi.single i 1) t := by
          simp only [pairRot]
          exact ((hasDerivAt_update y i t).const_smul (Real.cos θ)).const_add _
        have h2 := (hd _).hasFDerivAt.comp_hasDerivAt t h1
        have h3 := (hasDerivAt_const t (P i x)).inner ℝ h2
        exact h3.congr_deriv (by
          simp only [ContinuousLinearMap.map_smul, real_inner_smul_right, inner_zero_left,
            add_zero, Function.comp_apply]
          rfl)
      have hcoordint : Integrable (fun y : ι → ℝ =>
          y i * ⟪P i x, g (pairRot θ (x, y)).1⟫_ℝ) μ := by
        simpa only [real_inner_smul_left] using hxA i
      rw [integral_coord_mul_eq v i
        (h := fun y => ⟪P i x, g (pairRot θ (x, y)).1⟫_ℝ)
        (h' := fun y => Real.cos θ * ⟪P i x, P i (pairRot θ (x, y)).1⟫_ℝ)
        hderiv (hxB i) ((hxC i).const_mul _) hcoordint, integral_const_mul]
      ring
    rw [integral_congr_ae hsec, integral_const_mul,
      integral_finsetSum _ fun i _ => ((hC i).integral_prod_left).const_mul _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_prod _ (hC i)]
  -- Step E: Cauchy–Schwarz (AM–GM) and rotation invariance of the marginal.
  have hK (i : ι) (θ : ℝ) :
      |∫ z, ⟪P i z.1, P i (pairRot θ z).1⟫_ℝ ∂κ| ≤ ∫ x, ‖P i x‖ ^ 2 ∂μ := by
    refine (abs_integral_real_inner_le (hPκ i) (hPR i θ)).trans (le_of_eq ?_)
    have hsq : Continuous (fun x => ‖P i x‖ ^ 2) := (continuous_norm.comp (hPc i)).pow 2
    have e1 : ∫ z, ‖P i z.1‖ ^ 2 ∂κ = ∫ x, ‖P i x‖ ^ 2 ∂μ :=
      integral_comp_fst_gaussianProduct v (fun x => ‖P i x‖ ^ 2) hsq.aestronglyMeasurable
    have e2 : ∫ z, ‖P i (pairRot θ z).1‖ ^ 2 ∂κ = ∫ z, ‖P i z.1‖ ^ 2 ∂κ :=
      integral_comp_pairRot v θ (fun z => ‖P i z.1‖ ^ 2)
        (hsq.comp continuous_fst).aestronglyMeasurable
    rw [e2, e1]
    ring
  set B := ∑ i, (v i : ℝ) * ∫ x, ‖P i x‖ ^ 2 ∂μ with hBdef
  have hJbound : ∀ᵐ θ ∂ν, ‖∫ z, H z θ ∂κ‖ ≤ Real.cos θ * B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [hJ θ, Real.norm_eq_abs, abs_mul, abs_of_nonneg hcos]
    refine mul_le_mul_of_nonneg_left ?_ hcos
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_left (hK i θ) (v i).2
  have hcosint : Integrable (fun θ => Real.cos θ * B) ν :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
      ((Real.continuous_cos.mul continuous_const).intervalIntegrable _ _)
  have hcos1 : ∫ θ, Real.cos θ ∂ν = 1 := by
    simp only [ν]
    rw [← intervalIntegral.integral_of_le (by positivity), integral_cos]
    simp
  calc ∫ x, ‖g x‖ ^ 2 ∂μ = ∫ z, ∫ θ, H z θ ∂ν ∂κ := by
        rw [hstepA]
        exact integral_congr_ae (Filter.Eventually.of_forall hstepB)
    _ = ∫ θ, ∫ z, H z θ ∂κ ∂ν := hswap
    _ ≤ ‖∫ θ, ∫ z, H z θ ∂κ ∂ν‖ := Real.le_norm_self _
    _ ≤ ∫ θ, Real.cos θ * B ∂ν := norm_integral_le_of_norm_le hcosint hJbound
    _ = B := by rw [integral_mul_const, hcos1, one_mul]

/-- **Gaussian Poincaré inequality** with constant `1`. Law `gaussianProduct v` on `ι → ℝ`
(finite `ι`, any variances, zero allowed); quantifiers and hypotheses as in `GaussianPoincare`:
complex `C¹` `f` with `f` and every `∂ᵢ f = Df(·) eᵢ` in `L²`. Conclusion
`E‖f - E f‖² ≤ ∑ᵢ vᵢ E‖∂ᵢ f‖²`. -/
theorem gaussianPoincare_holds : GaussianPoincare := by
  intro ι _ _ v f hf hf2 hP2
  have hγ : ∀ j, IsProbabilityMeasure (gaussianReal 0 (v j)) := fun j =>
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 (v j)
  have hμ : IsProbabilityMeasure (gaussianProduct v) := by
    unfold gaussianProduct
    infer_instance
  set m := ∫ y, f y ∂gaussianProduct v with hm
  have hfint : Integrable f (gaussianProduct v) := hf2.integrable (by norm_num)
  have hderiv (x : ι → ℝ) : fderiv ℝ (fun y => f y - m) x = fderiv ℝ f x := fderiv_sub_const m
  have h := poincare_centered v (g := fun x => f x - m) (hf.sub contDiff_const)
    (hf2.sub (memLp_const m)) (by simpa only [hderiv] using hP2)
    (by rw [integral_sub hfint (integrable_const m), integral_const]; simp [hm])
  simpa only [hderiv] using h

/-- Both Gaussian gradient inequalities: the Poincaré inequality (constant `1`) and the
dimension-free `L^p` gradient inequality with constant `C = 2π`. -/
theorem gaussianGradientInequalities_holds : GaussianGradientInequalities :=
  ⟨gaussianPoincare_holds, gaussianLpGradient_holds⟩

end BlockBand.GaussianCalculus
