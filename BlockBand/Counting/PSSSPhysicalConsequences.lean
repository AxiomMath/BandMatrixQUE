module
public import BlockBand.Counting.PhysicalFactorialConsequences
public import BlockBand.Counting.ClosePairGrid

/-!
# The close-pair bound for the physical Gaussian ring

For the deformed physical Gaussian ring, the expected number of ordered pairs of unfolded
eigenvalues in `[-R,R]` at distance less than `a` is at most
`8 𝕂² R a + 16 𝕂² a²`, where `𝕂` is the unfolded PSSS constant.  The window moment and
integrability inputs are derived from the physical factorial-moment bound.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open MeasureTheory ProbabilityTheory
open BlockBand.External.PSSS BlockBand.Counting

def physicalClosePairCount (p : BlockBand.Parameters) (A : HermitianMatrix p.Site)
    (E rho R a : ℝ) (H : p.SiteMatrix) : ℕ :=
  (closePairIndices (p.physicalUnfoldedEigenvalue A E rho H) R a).card

theorem measurable_physicalClosePairCount (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho R a : ℝ) :
    Measurable (p.physicalClosePairCount A E rho R a) := by
  classical
  have heq : p.physicalClosePairCount A E rho R a = fun H =>
      ∑ ij ∈ orderedDistinctPairs (Finset.univ : Finset (Fin (Fintype.card p.Site))),
        if |p.physicalUnfoldedEigenvalue A E rho H ij.1| ≤ R ∧
          |p.physicalUnfoldedEigenvalue A E rho H ij.2| ≤ R ∧
          |p.physicalUnfoldedEigenvalue A E rho H ij.1 -
            p.physicalUnfoldedEigenvalue A E rho H ij.2| < a then 1 else 0 := by
    funext H
    simp [physicalClosePairCount, closePairIndices, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro ij _
  have hi := p.measurable_physicalUnfoldedEigenvalue A E rho ij.1
  have hj := p.measurable_physicalUnfoldedEigenvalue A E rho ij.2
  exact Measurable.ite
    ((measurableSet_le hi.abs measurable_const).inter
      ((measurableSet_le hj.abs measurable_const).inter
        (measurableSet_lt (hi.sub hj).abs measurable_const))) measurable_const measurable_const

theorem physicalClosePairCount_le_dimension_square (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho R a : ℝ) (H : p.SiteMatrix) :
    p.physicalClosePairCount A E rho R a H ≤
      Fintype.card (Fin (Fintype.card p.Site) × Fin (Fintype.card p.Site)) := by
  exact Finset.card_le_univ _

theorem GaussianRingModel.physicalClosePairCount_integrable {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (A : HermitianMatrix p.Site) (E rho R a : ℝ) :
    Integrable (fun H => (p.physicalClosePairCount A E rho R a H : ℝ))
      (model.law : Measure p.SiteMatrix) := by
  have hi := integrable_factorialCount (model.law : Measure p.SiteMatrix)
    (p.measurable_physicalClosePairCount A E rho R a)
    (p.physicalClosePairCount_le_dimension_square A E rho R a) 1
  change Integrable (fun H => ((p.physicalClosePairCount A E rho R a H).descFactorial 1 : ℝ))
    (model.law : Measure p.SiteMatrix) at hi
  simpa only [Nat.descFactorial_one] using hi

theorem physicalClosePairGridWindow_card (p : BlockBand.Parameters)
    (A : HermitianMatrix p.Site) (E rho R a : ℝ) (j : ℕ) (H : p.SiteMatrix) :
    (closePairGridWindow (p.physicalUnfoldedEigenvalue A E rho H) R a j).card =
      p.physicalUnfoldedIntervalCount A E rho (closePairGridLo R a j)
        (closePairGridHi R a j) H := by
  classical
  simp only [closePairGridWindow, physicalUnfoldedIntervalCount, eigenvalueCount, Set.mem_Icc]

/-- Expected number of ordered distinct close pairs, with the constants
`8 𝕂² R a + 16 𝕂² a²`.  All window moment and integrability inputs are
specialized from the physical factorial theorem. -/
theorem GaussianRingModel.physicalClosePairCount_bound {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E rho : ℝ) (hrho : 0 < rho)
    (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a) :
    (∫ H, (p.physicalClosePairCount A E rho R a H : ℝ)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      8*(p.physicalUnfoldedConstant source rho)^2*R*a +
        16*(p.physicalUnfoldedConstant source rho)^2*a^2 := by
  apply integral_closePairIndices_le_manuscript (model.law : Measure p.SiteMatrix)
    (p.physicalUnfoldedEigenvalue A E rho) hR ha
  · exact model.physicalClosePairCount_integrable A E rho R a
  · intro j
    have hi := model.physicalUnfoldedIntervalCount_integrable A E rho
      (closePairGridLo R a j) (closePairGridHi R a j) 2
    change Integrable (fun H =>
      ((p.physicalUnfoldedIntervalCount A E rho (closePairGridLo R a j)
        (closePairGridHi R a j) H).descFactorial 2 : ℝ)) (model.law : Measure p.SiteMatrix) at hi
    simpa only [p.physicalClosePairGridWindow_card A E rho R a j] using hi
  · intro j
    have hlen : closePairGridLo R a j ≤ closePairGridHi R a j := by
      unfold closePairGridHi
      linarith
    have h := model.physicalUnfoldedIntervalCount_factorialBound source A E rho hrho
      (closePairGridLo R a j) (closePairGridHi R a j) hlen 2 (by norm_num)
    change (∫ H, ((p.physicalUnfoldedIntervalCount A E rho (closePairGridLo R a j)
      (closePairGridHi R a j) H).descFactorial 2 : ℝ) ∂(model.law : Measure p.SiteMatrix)) ≤ _ at h
    rw [closePairGridHi_sub_lo] at h
    simp_rw [p.physicalClosePairGridWindow_card A E rho R a j]
    convert h using 1
    congr 1
    ring

/-- Bulk-energy physical ordered close-pair bound, with unfolding density the
semicircle density, from the same absolute constant `C`. -/
theorem GaussianRingModel.physicalClosePairCount_bound_semicircle {p : BlockBand.Parameters}
    (model : p.GaussianRingModel) (source : SourceContract.{0})
    (A : HermitianMatrix p.Site) (E : ℝ) (hE : -2 < E ∧ E < 2)
    (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a) :
    (∫ H, (p.physicalClosePairCount A E (semicircleDensity E) R a H : ℝ)
      ∂(model.law : Measure p.SiteMatrix)) ≤
      8*(p.physicalUnfoldedConstant source (semicircleDensity E))^2*R*a +
        16*(p.physicalUnfoldedConstant source (semicircleDensity E))^2*a^2 :=
  model.physicalClosePairCount_bound source A E (semicircleDensity E)
    (semicircleDensity_pos hE) R a hR ha

end BlockBand.Parameters
