module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Approx
public import BlockBand.Palm.ReferenceFlowHolds
public import BlockBand.SourceProcess.Stochastic.ItoNative.Main
public import Mathlib.Probability.Kernel.Representation

/-!
# Reference flow jointly measurable in the path: the kernel and its realization

* `measurable_measure_of_integral`: a map into probability measures on a pseudo-metrizable
  Borel space is measurable when all its integrals of bounded continuous functions are
  (closed sets form a generating π-system; their indicators are decreasing limits of bounded
  continuous functions, `HasOuterApproxClosed`).
* `measurable_refKernelOf`: under `RefKernelLawContinuity N`, for `a < c` and
  `a ≤ s ≤ u ≤ c`, `ω ↦ refKernelOf … ω` is `pathSigma F a a c`-measurable. On `simpleRatSet`, the
  integral of `φ` is the pointwise limit of the countably-valued measurable maps
  `ω ↦ ∫ φ d refKernelLaw a u s (gridCoeff n ω)` (continuity of the coefficients, grid
  approximation, and `RefKernelLawContinuity` on `[a, u] ⊆ [a, c]`).
* `exists_refKernel_realization`: a jointly measurable, contracting realization of the kernel law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory Set Filter Topology ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.ReferenceFlow
open BlockBand.Palm.MomentFlow (pathSigma)
open BlockBand.Palm.RelativeLocalization.StochasticBridge
open scoped NNReal ENNReal

/-!
## Measurability of measure-valued maps through integrals
-/

/-- **Measurability from integrals.** A map `κ` into probability measures on a pseudo-metrizable
Borel space is measurable when `ω ↦ ∫ φ dκ(ω)` is measurable for every bounded continuous real
`φ`. -/
theorem measurable_measure_of_integral {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    {κ : Ω → Measure X} [∀ ω, IsProbabilityMeasure (κ ω)]
    (h : ∀ φ : X → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Measurable fun ω => ∫ x, φ x ∂κ ω) :
    Measurable κ := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
    fun F hF => ?_
  have hF' : IsClosed F := hF
  refine ENNReal.measurable_of_tendsto
    (f := fun n ω => ∫⁻ x, (hF'.apprSeq n x : ℝ≥0∞) ∂κ ω) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => HasOuterApproxClosed.tendsto_lintegral_apprSeq hF' (κ ω))
  have e : (fun ω => ∫⁻ x, (hF'.apprSeq n x : ℝ≥0∞) ∂κ ω) =
      fun ω => ENNReal.ofReal (∫ x, (hF'.apprSeq n x : ℝ) ∂κ ω) := by
    funext ω
    exact lintegral_coe_eq_integral _
      (BoundedContinuousFunction.integrable_of_nnreal (κ ω) (hF'.apprSeq n))
  rw [e]
  refine (h _ (NNReal.continuous_coe.comp (hF'.apprSeq n).continuous)
    ⟨1, fun x => ?_⟩).ennreal_ofReal
  simp only [Function.comp_apply, NNReal.abs_eq]
  exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF' n x

/-- The Mathlib product σ-algebra `m ⊗ m'` is the `comap fst ⊔ comap snd` form used in
`ReferenceFlowStatement`. -/
theorem measurable_prod_iff_comap_sup {Ω Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (m : MeasurableSpace Ω) (g : Ω × Y → Z) :
    Measurable[m.prod inferInstance] g ↔
      Measurable[MeasurableSpace.comap Prod.fst m ⊔
        MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Y)] g :=
  Iff.rfl

/-!
## Matrices
-/

variable {N : ℕ}

/-- Matrices (product topology) are pseudo-metrizable. -/
theorem matrix_pseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin N → Fin N → ℂ))

/-- Matrices form a standard Borel space. -/
theorem matrix_standardBorelSpace : StandardBorelSpace (Matrix (Fin N) (Fin N) ℂ) :=
  inferInstanceAs (StandardBorelSpace (Fin N → Fin N → ℂ))

attribute [local instance] matrix_pseudoMetrizableSpace matrix_standardBorelSpace

/-- The closed set of matrices contracting at rate `ρ`: `‖M v‖₂ ≤ ρ ‖v‖₂` for all `v`. -/
def contractionSet (ρ : ℝ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {M | ∀ v : Fin N → ℂ, l2Norm (M *ᵥ v) ≤ ρ * l2Norm v}

/-- The contraction set is closed. -/
theorem isClosed_contractionSet (ρ : ℝ) : IsClosed (contractionSet (N := N) ρ) := by
  have e : contractionSet (N := N) ρ =
      ⋂ v : Fin N → ℂ, {M | l2Norm (M *ᵥ v) ≤ ρ * l2Norm v} := by
    ext M
    simp only [contractionSet, mem_ofPred_eq, mem_iInter]
  rw [e]
  refine isClosed_iInter fun v => isClosed_le ?_ continuous_const
  have hmv : Continuous fun M : Matrix (Fin N) (Fin N) ℂ => M *ᵥ v :=
    continuous_id.matrix_mulVec continuous_const
  have h : Continuous fun M : Matrix (Fin N) (Fin N) ℂ =>
      Real.sqrt (∑ k, ‖(M *ᵥ v) k‖ ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
      (continuous_norm.comp ((continuous_apply k).comp hmv)).pow 2)
  simpa only [l2Norm] using h

/-- The zero matrix lies in the contraction set of every rate `ρ ≥ 0`. -/
theorem zero_mem_contractionSet {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : Matrix (Fin N) (Fin N) ℂ) ∈ contractionSet ρ := by
  rw [contractionSet, mem_ofPred_eq]
  intro v
  simp only [l2Norm, Matrix.zero_mulVec, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
  exact mul_nonneg hρ (Real.sqrt_nonneg _)

/-!
## The kernel law
-/

/-- The kernel of `canonFlow` is measurable, also when the hypotheses fail (then it is constant). -/
theorem measurable_refKernel_canonFlow (a u s : ℝ) (r : ℝ → Fin N → Fin N → ℝ)
    (κ : ℝ → Fin N → ℝ) : Measurable (refKernel u (canonFlow a u r κ) s) := by
  by_cases h : a ≤ u ∧ Admissible a u r κ
  · exact measurable_refKernel (canonFlow_isRotationFlow h.1 h.2) s
  · have e : refKernel u (canonFlow a u r κ) s = fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ := by
      funext y
      simp only [refKernel, canonFlow, h, dite_false]
    rw [e]
    exact measurable_const

/-- `refKernelLaw` is a probability measure. -/
theorem isProbabilityMeasure_refKernelLaw (a u s : ℝ) (r : ℝ → Fin N → Fin N → ℝ)
    (κ : ℝ → Fin N → ℝ) : IsProbabilityMeasure (refKernelLaw a u s r κ) := by
  rw [refKernelLaw]
  infer_instance

section Contraction

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobeniusBorelSpace

/-- **Contraction of the `canonFlow` kernel** (`kernelContracts_of` with the Itô product rule):
for admissible coefficients on `[a, u]` and a damping floor `b ≤ κ` on `[a, u]`, a.s.
`‖K_s v‖₂² ≤ e^{−b(u−s)} ‖v‖₂²` for all `s ∈ [a, u]` and `v`. -/
theorem ae_contracts_canonFlow {a u : ℝ} (hau : a ≤ u) {r : ℝ → Fin N → Fin N → ℝ}
    {κ : ℝ → Fin N → ℝ} (h : Admissible a u r κ) {b : ℝ} (hb : ∀ x ∈ Icc a u, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) (Measure.dirac ()), ∀ s ∈ Icc a u, ∀ v : Fin N → ℂ,
      ∑ k, ‖(refKernel u (canonFlow a u r κ) s y *ᵥ v) k‖ ^ 2 ≤
        Real.exp (-(b * (u - s))) * ∑ k, ‖v k‖ ^ 2 :=
  kernelContracts_of (ItoNative.itoProductRuleFor_holds _) hau h.1 h.2.1 h.2.2.1 h.2.2.2.1
    (canonFlow_isRotationFlow hau h) b hb

end Contraction

/-- On simple paths the coefficients `(shortRate, refDamping)` are admissible on `[a, u]`,
`u ≤ c`. -/
theorem admissible_of_mem {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c u : ℝ}
    (hac : a ≤ c) (huc : u ≤ c) {ω : FlowSample N} (hω : ω ∈ RelativeDuhamel.simpleRatSet F a c) (b₀ : ℝ)
    (ℓ : ℕ) : Admissible a u (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) :=
  ⟨(continuousOn_shortRate_of_mem hF hac hω ℓ).mono (Icc_subset_Icc le_rfl huc),
    (continuousOn_refDamping_of_mem hF hac hω b₀ ℓ).mono (Icc_subset_Icc le_rfl huc),
    shortRate_comm F a ω ℓ, shortRate_nonneg F a ω ℓ, refDamping_nonneg F a b₀ ω ℓ⟩

open Classical in
/-- **The reference kernel law of a path.** For `ω ∈ simpleRatSet F a c`, the law
`refKernelLaw a u s` of the reference kernel with the path coefficients `(shortRate, refDamping)`;
otherwise the Dirac mass at the zero matrix. -/
def refKernelOf (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ) (s u : ℝ)
    (ω : FlowSample N) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  if ω ∈ RelativeDuhamel.simpleRatSet F a c then
    refKernelLaw a u s (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ)
  else Measure.dirac 0

/-- `refKernelOf` is a probability measure. -/
instance isProbabilityMeasure_refKernelOf (F : Matrix (Fin N) (Fin N) ℂ) (a c b₀ : ℝ) (ℓ : ℕ)
    (s u : ℝ) (ω : FlowSample N) : IsProbabilityMeasure (refKernelOf F a c b₀ ℓ s u ω) := by
  by_cases h : ω ∈ RelativeDuhamel.simpleRatSet F a c
  · rw [refKernelOf, ite_eq_left h]
    exact isProbabilityMeasure_refKernelLaw _ _ _ _ _
  · rw [refKernelOf, ite_eq_right h]
    infer_instance

open Classical in
/-- **Path measurability of the kernel law.** Under `RefKernelLawContinuity N`, for Hermitian
`F`, `a < c` and `a ≤ s ≤ u ≤ c`, the map `ω ↦ refKernelOf F a c b₀ ℓ s u ω` is measurable from
`(FlowSample N, pathSigma F a a c)` to the measures on matrices. -/
theorem measurable_refKernelOf (hJ3 : RefKernelLawContinuity N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (hac : a < c) (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s)
    (hsu : s ≤ u) (huc : u ≤ c) :
    Measurable[pathSigma F a a c] (refKernelOf F a c b₀ ℓ s u) := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have hS : MeasurableSet (RelativeDuhamel.simpleRatSet F a c) := RelativeDuhamel.measurableSet_simpleRatSet F hac.le
  refine measurable_measure_of_integral fun φ hφ hb => ?_
  have hgrid : ∀ n, Measurable fun ω => ∫ M, φ M ∂refKernelLaw a u s
      (gridRate F a c b₀ ℓ n ω) (gridDamp F a c b₀ ℓ n ω) := by
    intro n
    let H : CoeffCode N n → ℝ := fun z => ∫ M, φ M ∂refKernelLaw a u s
      (fun x => (codeCoeff a c n z x).1) (fun x => (codeCoeff a c n z x).2)
    exact (measurable_of_countable H).comp (measurable_coeffCode F hac.le b₀ ℓ n)
  have hconv : ∀ ω ∈ RelativeDuhamel.simpleRatSet F a c, Tendsto (fun n => ∫ M, φ M ∂refKernelLaw a u s
      (gridRate F a c b₀ ℓ n ω) (gridDamp F a c b₀ ℓ n ω)) atTop
      (𝓝 (∫ M, φ M ∂refKernelLaw a u s (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ))) :=
    fun ω hω => hJ3 a u s (has.trans hsu) ⟨has, hsu⟩ _ _ (fun n => gridRate F a c b₀ ℓ n ω)
      (fun n => gridDamp F a c b₀ ℓ n ω) (admissible_of_mem hF hac.le huc hω b₀ ℓ)
      (fun n => admissible_gridCoeff F a c b₀ ℓ n ω u)
      ((tendstoUniformlyOn_gridCoeff hF hac hω b₀ ℓ).mono (Icc_subset_Icc le_rfl huc)) φ hφ hb
  refine measurable_of_tendsto_metrizable (f := fun n ω => if ω ∈ RelativeDuhamel.simpleRatSet F a c then
      ∫ M, φ M ∂refKernelLaw a u s (gridRate F a c b₀ ℓ n ω) (gridDamp F a c b₀ ℓ n ω)
    else ∫ M, φ M ∂(Measure.dirac 0 : Measure (Matrix (Fin N) (Fin N) ℂ)))
    (fun n => Measurable.ite hS (hgrid n) measurable_const) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ RelativeDuhamel.simpleRatSet F a c
  · simp only [refKernelOf, ite_eq_left hω]
    exact hconv ω hω
  · simp only [refKernelOf, ite_eq_right hω]
    exact tendsto_const_nhds

/-- **The contraction set has full measure.** For Hermitian `F`, `a ≤ c`, `a ≤ s ≤ u ≤ c` and
every path `ω`, `refKernelOf … ω`-a.e. matrix contracts at rate `e^{−b₀N(u−s)/(2ℓ)}`. -/
theorem ae_mem_contractionSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) (b₀ : ℝ) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c)
    (ω : FlowSample N) :
    ∀ᵐ M ∂refKernelOf F a c b₀ ℓ s u ω,
      M ∈ contractionSet (Real.exp (-(b₀ * N * (u - s) / (2 * ℓ)))) := by
  have hC := (isClosed_contractionSet (N := N) (Real.exp (-(b₀ * N * (u - s) / (2 * ℓ)))))
    |>.measurableSet
  by_cases hω : ω ∈ RelativeDuhamel.simpleRatSet F a c
  · rw [refKernelOf, ite_eq_left hω, refKernelLaw,
      ae_map_iff (p := fun M => M ∈ contractionSet _)
        (measurable_refKernel_canonFlow _ _ _ _ _).aemeasurable hC]
    filter_upwards [ae_contracts_canonFlow (has.trans hsu) (admissible_of_mem hF hac huc hω b₀ ℓ)
      (b := b₀ * N / ℓ) fun _ _ _ => le_max_right _ _] with y hy
    rw [contractionSet, mem_ofPred_eq]
    intro v
    have h := hy s ⟨has, hsu⟩ v
    have e : Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) =
        Real.sqrt (Real.exp (-(b₀ * N / ℓ * (u - s)))) := by
      rw [← Real.exp_half]
      congr 1
      ring
    simp only [l2Norm]
    rw [e, ← Real.sqrt_mul (Real.exp_pos _).le]
    exact Real.sqrt_le_sqrt h
  · rw [refKernelOf, ite_eq_right hω]
    exact (ae_dirac_iff hC).2 (zero_mem_contractionSet (Real.exp_pos _).le)

open Classical in
/-- **Realization of the kernel law, jointly measurable and contracting.** Under
`RefKernelLawContinuity N`, for Hermitian `F`, `a < c` and `a ≤ s ≤ u ≤ c`, there is
`f : FlowSample N → unitInterval → Matrix` such that
* `(ω, t) ↦ f ω t` is measurable for `pathSigma F a a c ⊗ Borel(unitInterval)` (in the
  `comap fst ⊔ comap snd` form of `ReferenceFlowStatement`; see `measurable_prod_iff_comap_sup`);
* for every `ω`, the image of the uniform law under `f ω` is `refKernelOf F a c b₀ ℓ s u ω`;
* for every `ω, t, v`, `‖f ω t v‖₂ ≤ e^{−b₀N(u−s)/(2ℓ)} ‖v‖₂`. -/
theorem exists_refKernel_realization (hJ3 : RefKernelLawContinuity N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a < c) (b₀ : ℝ) (ℓ : ℕ)
    {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c) :
    ∃ f : FlowSample N → unitInterval → Matrix (Fin N) (Fin N) ℂ,
      Measurable[MeasurableSpace.comap Prod.fst (pathSigma F a a c) ⊔
          MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace unitInterval)]
        (fun p : FlowSample N × unitInterval => f p.1 p.2) ∧
      (∀ ω, volume.map (f ω) = refKernelOf F a c b₀ ℓ s u ω) ∧
      ∀ ω t (v : Fin N → ℂ),
        l2Norm (f ω t *ᵥ v) ≤ Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) * l2Norm v := by
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  let κ : Kernel (FlowSample N) (Matrix (Fin N) (Fin N) ℂ) :=
    ⟨refKernelOf F a c b₀ ℓ s u, measurable_refKernelOf hJ3 hF hac b₀ ℓ has hsu huc⟩
  have hκ : IsMarkovKernel κ := ⟨fun ω => isProbabilityMeasure_refKernelOf F a c b₀ ℓ s u ω⟩
  obtain ⟨f, hf, hfκ⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  have hfκ' : ∀ ω, volume.map (f ω) = refKernelOf F a c b₀ ℓ s u ω := hfκ
  set ρ := Real.exp (-(b₀ * N * (u - s) / (2 * ℓ))) with hρ
  have hC := (isClosed_contractionSet (N := N) ρ).measurableSet
  refine ⟨fun ω t => if f ω t ∈ contractionSet ρ then f ω t else 0, ?_, fun ω => ?_,
    fun ω t v => ?_⟩
  · exact Measurable.ite (hf hC) hf measurable_const
  · have hfω : Measurable (f ω) := hf.of_uncurry_left
    have hae : ∀ᵐ t ∂(volume : Measure unitInterval), f ω t ∈ contractionSet ρ := by
      have h := ae_mem_contractionSet hF hac.le b₀ ℓ has hsu huc ω
      rw [← hfκ' ω] at h
      exact (ae_map_iff hfω.aemeasurable hC).1 h
    rw [Measure.map_congr (g := f ω) (hae.mono fun t ht => ite_eq_left ht), hfκ' ω]
  · by_cases h : f ω t ∈ contractionSet ρ
    · simp only [ite_eq_left h]
      exact h v
    · simp only [ite_eq_right h]
      exact zero_mem_contractionSet (Real.exp_pos _).le v

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
