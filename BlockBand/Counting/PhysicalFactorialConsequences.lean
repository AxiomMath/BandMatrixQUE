module
public import BlockBand.Counting.PSSSPhysicalCounting
public import BlockBand.Counting.FactorialExponential

/-!
# Unfolded factorial and exponential count bounds

For the deformed physical Gaussian ring, counts of the unfolded spectrum `N ρ (λ - E)` in
`[a,b]` satisfy factorial-moment bounds with constant `𝕂 = C / (sqrt c ρ)`, independent of
`N`.  Hence the unfolded count in `[-R,R]` has exponential moment at most
`exp (2 R 𝕂 (e^t - 1))`, in particular at bulk energy with `ρ` the semicircle density.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS BlockBand.Counting BlockBand.Foundations.Spectral

def physicalDeformedVersion (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (H : p.SiteMatrix) : HermitianMatrix p.Site :=
  ⟨(p.physicalHermitianVersion H).1 + A.1, (p.physicalHermitianVersion H).2.add A.2⟩

theorem measurable_physicalDeformedVersion (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) : Measurable (p.physicalDeformedVersion A) := by
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)).add measurable_const

def physicalUnfoldedEigenvalue (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (E rho : ℝ) (H : p.SiteMatrix) (i : Fin (Fintype.card p.Site)) : ℝ :=
  (p.N : ℝ) * rho * (increasingEigenvalue (p.physicalDeformedVersion A H).2 i - E)

theorem measurable_physicalUnfoldedEigenvalue (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho : ℝ) (i : Fin (Fintype.card p.Site)) :
    Measurable (fun H => p.physicalUnfoldedEigenvalue A E rho H i) :=
  (((BlockBand.Model.Construction.measurable_increasingEigenvalue i).comp
    (p.measurable_physicalDeformedVersion A)).sub_const E).const_mul _

def physicalUnfoldedIntervalCount (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (E rho a b : ℝ) (H : p.SiteMatrix) : ℕ :=
  eigenvalueCount (p.physicalUnfoldedEigenvalue A E rho H) (Set.Icc a b)

theorem physicalUnfoldedIntervalCount_eq (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho) (a b : ℝ) (H : p.SiteMatrix) :
    p.physicalUnfoldedIntervalCount A E rho a b H =
      p.physicalIntervalCount A (E + a / ((p.N : ℝ) * rho))
        (E + b / ((p.N : ℝ) * rho)) H := by
  exact eigenvalueCount_unfolding _ ((p.N : ℝ) * rho)
    (mul_pos (by exact_mod_cast p.N_pos) hrho) E a b

theorem physicalUnfoldedEigenvalue_eq (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho : ℝ) (H : p.SiteMatrix) (hH : H.IsHermitian)
    (i : Fin (Fintype.card p.Site)) :
    p.physicalUnfoldedEigenvalue A E rho H i =
      (p.N : ℝ) * rho * (increasingEigenvalue (hH.add A.2) i - E) := by
  simp only [physicalUnfoldedEigenvalue, physicalDeformedVersion, physicalHermitianVersion,
    p.gaussianReconstruction_gaussianExtraction H hH]

theorem measurable_physicalUnfoldedIntervalCount (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho a b : ℝ) :
    Measurable (p.physicalUnfoldedIntervalCount A E rho a b) := by
  classical
  have heq : p.physicalUnfoldedIntervalCount A E rho a b =
      fun H => ∑ i : Fin (Fintype.card p.Site),
        if p.physicalUnfoldedEigenvalue A E rho H i ∈ Set.Icc a b then 1 else 0 := by
    funext H
    simp [physicalUnfoldedIntervalCount, eigenvalueCount, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_Icc.preimage (p.measurable_physicalUnfoldedEigenvalue A E rho i))
    measurable_const measurable_const

theorem physicalUnfoldedIntervalCount_le_dimension (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho a b : ℝ) (H : p.SiteMatrix) :
    p.physicalUnfoldedIntervalCount A E rho a b H ≤ p.N := by
  simpa [physicalUnfoldedIntervalCount, Site, N] using eigenvalueCount_le_dimension
    (p.physicalUnfoldedEigenvalue A E rho H) (Set.Icc a b)

def physicalUnfoldedConstant (p : BlockBand.Parameters) (source : SourceContract.{0})
    (rho : ℝ) : ℝ := source.C / (Real.sqrt p.c * rho)

theorem physicalUnfoldedConstant_pos (p : BlockBand.Parameters) (source : SourceContract.{0})
    {rho : ℝ} (hrho : 0 < rho) : 0 < p.physicalUnfoldedConstant source rho :=
  div_pos source.C_pos (mul_pos (Real.sqrt_pos.mpr p.c_pos) hrho)

theorem GaussianRingModel.physicalUnfoldedIntervalCount_integrable {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho a b : ℝ) (r : ℕ) :
    Integrable (factorialCount (p.physicalUnfoldedIntervalCount A E rho a b) r)
      (model.law : Measure p.SiteMatrix) :=
  integrable_factorialCount _ (p.measurable_physicalUnfoldedIntervalCount A E rho a b)
    (p.physicalUnfoldedIntervalCount_le_dimension A E rho a b) r

/-- Factorial bound for unfolded counts: the factor `N` cancels from the physical
interval length under unfolding. -/
theorem GaussianRingModel.physicalUnfoldedIntervalCount_factorialBound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    (∫ H, factorialCount (p.physicalUnfoldedIntervalCount A E rho a b) r H
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (p.physicalUnfoldedConstant source rho * (b-a)) ^ r := by
  have hN : (p.N : ℝ) ≠ 0 := by exact_mod_cast p.N_pos.ne'
  have hq : 0 < (p.N : ℝ) * rho := mul_pos (by exact_mod_cast p.N_pos) hrho
  have h := model.physicalIntervalCount_factorialBound source A
    (E+a/((p.N : ℝ)*rho)) (E+b/((p.N : ℝ)*rho))
    (by linarith [div_le_div_of_nonneg_right hab hq.le]) r hr
  unfold FactorialMomentBound at h
  have hc : p.physicalUnfoldedIntervalCount A E rho a b =
      p.physicalIntervalCount A (E+a/((p.N : ℝ)*rho)) (E+b/((p.N : ℝ)*rho)) := by
    funext H
    exact p.physicalUnfoldedIntervalCount_eq A E rho hrho a b H
  rw [hc]
  convert h using 1
  congr 1
  unfold physicalUnfoldedConstant
  field_simp [hN, hrho.ne']
  ring

/-- The factorial bound at every order; order zero uses the probability normalization. -/
theorem GaussianRingModel.physicalUnfoldedIntervalCount_allOrder_bound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) :
    (∫ H, factorialCount (p.physicalUnfoldedIntervalCount A E rho a b) r H
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (p.physicalUnfoldedConstant source rho * (b-a)) ^ r := by
  cases r with
  | zero => simp [factorialCount]
  | succ r => exact model.physicalUnfoldedIntervalCount_factorialBound source A E rho hrho a b hab (r+1) (by omega)

/-- Exponential count bound with exponent `2 R 𝕂 (exp t - 1)`. -/
theorem GaussianRingModel.physicalUnfoldedIntervalCount_exponentialBound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    (∫ H, Real.exp (t * p.physicalUnfoldedIntervalCount A E rho (-R) R H)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      Real.exp (2*R*p.physicalUnfoldedConstant source rho*(Real.exp t-1)) := by
  have h := conditional_integral_exp_count_le_of_factorialMoments
    (model.law : Measure p.SiteMatrix) (p.physicalUnfoldedIntervalCount A E rho (-R) R)
    p.N (p.physicalUnfoldedConstant source rho * (R-(-R))) t
    (p.physicalUnfoldedIntervalCount_le_dimension A E rho (-R) R)
    (mul_nonneg (p.physicalUnfoldedConstant_pos source hrho).le (by linarith)) ht
    (fun r _ => model.physicalUnfoldedIntervalCount_integrable A E rho (-R) R r)
    (fun r _ => model.physicalUnfoldedIntervalCount_allOrder_bound source A E rho hrho
      (-R) R (by linarith) r)
  convert h using 1
  congr 1
  ring

/-- Exponential integrability is separate from the moment inequality. -/
theorem GaussianRingModel.physicalUnfoldedIntervalCount_exponentialIntegrable
    {p : BlockBand.Parameters} (model : p.GaussianRingModel)
    (A : HermitianMatrix p.Site) (E rho a b t : ℝ) :
    Integrable (fun H => Real.exp (t * p.physicalUnfoldedIntervalCount A E rho a b H))
      (model.law : Measure p.SiteMatrix) := by
  have hm : Measurable (fun H => Real.exp (t * p.physicalUnfoldedIntervalCount A E rho a b H)) :=
    (measurable_from_nat : Measurable (fun n : ℕ => Real.exp (t*n))).comp
      (p.measurable_physicalUnfoldedIntervalCount A E rho a b)
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (|t| * p.N))
  filter_upwards with H
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right (le_abs_self t) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (p.physicalUnfoldedIntervalCount_le_dimension A E rho a b H))
      (abs_nonneg t))

/-- Bulk-energy specialization with `ρ = semicircleDensity E`. -/
theorem GaussianRingModel.physicalUnfoldedIntervalCount_exponentialBound_semicircle
    {p : BlockBand.Parameters} (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E : ℝ) (hE : -2 < E ∧ E < 2)
    (R t : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    (∫ H, Real.exp (t * p.physicalUnfoldedIntervalCount A E (semicircleDensity E) (-R) R H)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      Real.exp (2*R*p.physicalUnfoldedConstant source (semicircleDensity E)*(Real.exp t-1)) :=
  model.physicalUnfoldedIntervalCount_exponentialBound source A E (semicircleDensity E)
    (semicircleDensity_pos hE) R t hR ht

end BlockBand.Parameters
