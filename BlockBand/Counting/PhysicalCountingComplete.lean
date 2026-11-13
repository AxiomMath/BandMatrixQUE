module
public import BlockBand.Counting.PhysicalMarkedTightness
public import BlockBand.Counting.SimpleSpectralLimits

/-!
# The counting theorem for the physical Gaussian ring

For a family of physical realizations with fixed diagonal weight `c`, this file assembles
all clauses of the counting theorem: the factorial-moment bound on Borel subsets of
intervals, the exponential bound for unfolded counts, the close-pair bound, tightness of
the marked laws, and simplicity of the spectral locations of every subsequential weak
limit.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter BlockBand.Parameters BlockBand.External.PSSS
open scoped Topology

/-- Deformed eigenvalue count on any Borel set. -/
def physicalSpectralSetCount (p : Parameters) (A : HermitianMatrix p.Site)
    (J : Set ℝ) (H : p.SiteMatrix) : ℕ :=
  eigenCount ⟨(p.physicalHermitianVersion H).1+A.1,
    (p.physicalHermitianVersion H).2.add A.2⟩ J

theorem measurable_physicalSpectralSetCount (p : Parameters) (A : HermitianMatrix p.Site)
    (J : Set ℝ) (hJ : MeasurableSet J) : Measurable (physicalSpectralSetCount p A J) := by
  apply (measurable_nativeEigenCount J hJ).comp
  apply Measurable.subtype_mk
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact (((measurable_pi_apply y).comp (measurable_pi_apply x)).comp
    (measurable_subtype_coe.comp p.measurable_physicalHermitianVersion)).add measurable_const

/-- Any open, closed or half-open interval with endpoints `a`, `b` has the same exact bound;
more generally it holds on any Borel subset of that closed interval. -/
theorem physicalSpectralSetCount_factorialBound (p : Parameters) (model : p.GaussianRingModel)
    (source : SourceContract.{0}) (A : HermitianMatrix p.Site)
    (J : Set ℝ) (hJ : MeasurableSet J) (a b : ℝ) (hab : a≤b) (hsub : J⊆Icc a b)
    (r : ℕ) (hr : 1≤r) :
    (∫ H, factorialCount (physicalSpectralSetCount p A J) r H
      ∂(model.law : Measure p.SiteMatrix)) ≤
      (source.C/Real.sqrt p.c*(p.N : ℝ)*(b-a))^r := by
  have hi := integrable_factorialCount (model.law : Measure p.SiteMatrix)
    (measurable_physicalSpectralSetCount p A J hJ)
    (fun H=>eigenCount_le_dimension _ _) r
  have hmono (H : p.SiteMatrix) : physicalSpectralSetCount p A J H ≤ p.physicalIntervalCount A a b H := by
    classical
    unfold physicalSpectralSetCount Parameters.physicalIntervalCount eigenCount
    apply Finset.card_le_card
    intro α hα
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hα ⊢
    exact hsub hα
  exact (integral_mono hi (model.physicalIntervalCount_integrable A a b r)
    (fun H=>Nat.cast_le.mpr (Nat.descFactorial_le r (hmono H)))).trans
    (model.physicalIntervalCount_factorialBound source A a b hab r hr)

/-- Supplied weak limits of every fixed-b physical family are simple, without
critical-sequence or n/W conditions.
-/
theorem finiteRealization_marked_weakLimit_hasSimple (source : SourceContract.{0})
    (p : ℕ → Parameters) (R : ∀ j, FiniteRealization (p j))
    (hc : ∀ j, (p j).c=(p 0).c) (E : ℝ) (hrho : 0<semicircleDensity E)
    (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>(R j).markedLaw E) atTop (𝓝 ν)) :
    HasSimpleSpectralLocations ν := by
  apply hasSimpleSpectralLocations_of_Ioo_twoPoint_bounds ν
    ((p 0).physicalUnfoldedConstant source (semicircleDensity E))
  intro x y hxy
  apply marked_Ioo_twoPoint_le_of_weakLimit (fun j=>(R j).markedLaw E) ν hlim
  intro j
  simpa only [physicalUnfoldedConstant,hc j] using
    finiteRealization_markedLaw_Ioo_twoPoint_bound (R j) source E hrho x y hxy

/-- All clauses of the counting theorem for any family of physical realizations with
fixed diagonal weight `c`.  Each finite clause permits an arbitrary deterministic
deformation; the family dimensions are unconstrained by `n/W`. -/
theorem physical_counting (source : SourceContract.{0}) (p : ℕ → Parameters)
    (R : ∀ j, FiniteRealization (p j)) (hc : ∀ j, (p j).c=(p 0).c)
    (E : ℝ) (hrho : 0<semicircleDensity E) :
    (∀ j (A : HermitianMatrix (p j).Site) (J : Set ℝ), MeasurableSet J →
      ∀ a b : ℝ, a≤b → J⊆Icc a b → ∀ r : ℕ, 1≤r →
      (∫ H, factorialCount (physicalSpectralSetCount (p j) A J) r H
        ∂((R j).model.law : Measure (p j).SiteMatrix)) ≤
        (source.C/Real.sqrt (p j).c*((p j).N : ℝ)*(b-a))^r) ∧
    (∀ j (A : HermitianMatrix (p j).Site) (L t : ℝ), 0≤L → 0≤t →
      (∫ H, Real.exp (t*(p j).physicalUnfoldedIntervalCount A E (semicircleDensity E) (-L) L H)
        ∂((R j).model.law : Measure (p j).SiteMatrix)) ≤
        Real.exp (2*L*(p j).physicalUnfoldedConstant source (semicircleDensity E)*(Real.exp t-1))) ∧
    (∀ j (A : HermitianMatrix (p j).Site) (L a : ℝ), 0≤L → 0<a →
      (∫ H, ((p j).physicalClosePairCount A E (semicircleDensity E) L a H : ℝ)
        ∂((R j).model.law : Measure (p j).SiteMatrix)) ≤
        8*((p j).physicalUnfoldedConstant source (semicircleDensity E))^2*L*a+
          16*((p j).physicalUnfoldedConstant source (semicircleDensity E))^2*a^2) ∧
    IsTightMeasureSet (Set.range (fun j=>((R j).markedLaw E : Measure MarkedPointMeasure))) ∧
    (∀ (φ : ℕ → ℕ) (ν : ProbabilityMeasure MarkedPointMeasure),
      Tendsto (fun j=>(R (φ j)).markedLaw E) atTop (𝓝 ν) → HasSimpleSpectralLocations ν) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j A J hJ a b hab hsub r hr
    exact physicalSpectralSetCount_factorialBound (p j) (R j).model source A J hJ a b hab hsub r hr
  · intro j A L t hL ht
    exact (R j).model.physicalUnfoldedIntervalCount_exponentialBound source A E
      (semicircleDensity E) hrho L t hL ht
  · intro j A L a hL ha
    exact (R j).model.physicalClosePairCount_bound source A E (semicircleDensity E) hrho L a hL ha
  · exact finiteRealization_markedLaws_isTight source p R hc E hrho
  · intro φ ν hlim
    apply finiteRealization_marked_weakLimit_hasSimple source (fun j=>p (φ j))
      (fun j=>R (φ j)) _ E hrho ν hlim
    intro j
    exact (hc (φ j)).trans (hc (φ 0)).symm

end BlockBand.Counting
