module
public import BlockBand.QUE.Invariance.PhysicalRotationLimitBound

/-!
# Rotation invariance of the marked limit laws

Every weak limit of the marked laws of a physical family with diverging block count is invariant
under rotations of the marks (`finiteRealization_marked_weakLimit_rotation_invariant`); in
particular every critical subsequential marked limit is
(`criticalSequence_marked_weakLimit_rotation_invariant`).
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Invariance
open MeasureTheory Filter BlockBand.Model.Construction BlockBand.Counting
open scoped Topology

/-- Every compact marked test has one finite spectral support radius. -/
theorem exists_markedTest_spectral_radius
    (F : CompactlySupportedContinuousMap MarkedSpectralSpace ℝ) :
    ∃ R : ℝ, 0≤R ∧ ∀ z, z.1 ∉ Set.Icc (-R) R → F z=0 := by
  obtain ⟨N,hN⟩ := exists_nat_bound_markedCompact (tsupport F) F.hasCompactSupport
  refine ⟨N,Nat.cast_nonneg _,?_⟩
  intro z hz
  by_contra hF
  have ht : z ∈ tsupport F := subset_closure (show z ∈ Function.support F from hF)
  exact hz (abs_le.mp (hN z ht))

/-- Mark-rotation invariance of every weak limit of the marked laws of a physical family with
diverging block count. -/
theorem finiteRealization_marked_weakLimit_rotation_invariant
    (source : BlockBand.External.PSSS.SourceContract.{0}) (p : ℕ → Parameters)
    (R : ∀ j, FiniteRealization (p j)) (hc : ∀ j, (p j).c=(p 0).c)
    (E : ℝ) (hrho : 0<Parameters.semicircleDensity E)
    (hn : Tendsto (fun j=>((p j).n : ℝ)) atTop atTop)
    (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>(R j).markedLaw E) atTop (𝓝 ν)) :
    IsMarkRotationInvariant ν := by
  intro a F hf
  obtain ⟨x,rfl⟩ := Quotient.exists_rep a
  let a : Torus := QuotientAddGroup.mk x
  let laws := fun j=>(R j).markedLaw E
  let as := fun j=>physicalRotationApproximation (p j) x
  let g := markedLaplaceTest F hf
  obtain ⟨L,hL,hs⟩ := exists_markedTest_spectral_radius F
  have has : Tendsto as atTop (𝓝 a) := physicalRotationApproximation_tendsto p x hn
  have he := markedRotationTestError_tendsto_zero F L as a has
  let K := (p 0).physicalUnfoldedConstant source (Parameters.semicircleDensity E)*(2*L)
  have he' : Tendsto (fun j=>markedRotationTestError F L (as j) a*K) atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const K
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
  have hrot : Tendsto (fun j=>globalMarkedRotationLaw a (laws j)) atTop
      (𝓝 (globalMarkedRotationLaw a ν)) :=
    ((continuous_globalMarkedRotationLaw a).tendsto ν).comp hlim
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hrot) g
  have hzero : Tendsto (fun j=>
      |(∫ ξ, g ξ ∂(laws j : Measure MarkedPointMeasure))-
        ∫ ξ, g ξ ∂(globalMarkedRotationLaw a (laws j) : Measure MarkedPointMeasure)|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _=>abs_nonneg _) _ he'
    intro j
    have h := canonicalPhysicalMarkedLaw_laplace_rotation_error (p j) (R j).model
      source E L hrho hL F hf hs (as j) a
    rw [← finiteRealization_markedLaw_eq_canonical] at h
    have hi := finiteRealization_markedLaw_gridRotation (p j) (R j) E
      (⌊((p j).n : ℝ)*x⌋ : ZMod (p j).n)
    change globalMarkedRotationLaw (as j) (laws j)=laws j at hi
    rw [hi] at h
    simpa only [Parameters.physicalUnfoldedConstant,hc j,K,g,laws] using h
  have hd := h1.sub h2
  have heq := tendsto_nhds_unique hd.abs hzero
  have hint : (∫ ξ, g ξ ∂(ν : Measure MarkedPointMeasure)) =
      ∫ ξ, g ξ ∂(globalMarkedRotationLaw a ν : Measure MarkedPointMeasure) :=
    sub_eq_zero.mp (abs_eq_zero.mp heq)
  have hm : (∫ ξ, g ξ ∂(globalMarkedRotationLaw a ν : Measure MarkedPointMeasure)) =
      ∫ ξ, g (globalMarkedRotation a ξ) ∂(ν : Measure MarkedPointMeasure) :=
    integral_map (measurable_globalMarkedRotation a).aemeasurable g.continuous.aestronglyMeasurable
  rw [hm] at hint
  have hg (ξ : MarkedPointMeasure) : g (globalMarkedRotation a ξ) =
      Real.exp (-∫ z, F (z.1,z.2.map (Homeomorph.addLeft a)) ∂ξ.marked.measure) := by
    change Real.exp (-∫ z, F z ∂(globalMarkedRotation a ξ).marked.measure) = _
    rw [globalMarkedRotation_integral]
    rfl
  simp_rw [hg] at hint
  exact hint.symm

/-- Every weak limit of the marked laws along a subsequence of a critical sequence, for any family
of finite realizations, is mark-rotation invariant (from the PSSS source contract). -/
theorem criticalSequence_marked_weakLimit_rotation_invariant
    (source : BlockBand.External.PSSS.SourceContract.{0}) {τ : ℝ}
    (s : CriticalSequence τ) (hτ : 0<τ) (b E : ℝ) (hb : 0<b) (hb' : b<1/2)
    (hrho : 0<Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (ν : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j=>(R (φ j)).markedLaw E) atTop (𝓝 ν)) :
    IsMarkRotationInvariant ν := by
  apply finiteRealization_marked_weakLimit_rotation_invariant source
    (fun j=>s.parameters b hb hb' (φ j)) (fun j=>R (φ j)) (fun _=>rfl)
    E hrho _ ν hlim
  simpa only [CriticalSequence.parameters,Function.comp_def] using
    (criticalSequence_n_real_tendsto_atTop s hτ).comp hφ.tendsto_atTop

end BlockBand.QUE.Invariance
