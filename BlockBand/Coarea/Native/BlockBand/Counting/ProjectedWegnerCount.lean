module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledPhysicalWegnerBoundary
public import BlockBand.Coarea.Native.BlockBand.Analysis.HermitianPoissonTrace
public import BlockBand.Coarea.Native.BlockBand.Spectral.Measurable.Counts

/-!
# The first-count consequence of the physical projected-Wegner estimate

This module formalizes the paper-native `r = 1` unsmoothing step.  On a
symmetric interval of half-width `η`, every enclosed eigenvalue contributes at
least `1 / (2η)` to the scalar Poisson trace.  Hence the sharp interval count
is at most `2η` times that trace.  Taking all physical blocks and zero absorber
then turns the unconditional Gaussian-ring projected-Wegner estimate into the
expected eigenvalue-count bound

`2 * η * π * (C / sqrt c) * W * n`.

Equivalently, an arbitrary nondegenerate interval `[a,b]` has expectation at
most `π * (C / sqrt c) * W * n * (b-a)`.  This is only the paper's first
counting moment.  No factorial-moment or higher-counting conclusion is made.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder ENNReal NNReal

universe u v

/-- Summing the unnormalized negative-imaginary diagonal traces over all
blocks gives the negative imaginary part of the full trace. -/
theorem sum_blockNegativeImaginaryTrace_eq_neg_trace_im
    {β : Type u} {ι : Type v} [Fintype β] [Fintype ι]
    (R : Matrix (β × ι) (β × ι) ℂ) :
    ∑ j : β, blockNegativeImaginaryTrace R j = -(R.trace).im := by
  simp [blockNegativeImaginaryTrace, Matrix.trace, Fintype.sum_prod_type]

/-- **Deterministic Poisson unsmoothing.**  Every eigenvalue in
`[e-η,e+η]` contributes at least `1/(2η)` to the Poisson trace at height `η`.
Multiplicity is retained through `orderedEigenvalue`. -/
theorem eigenCount_Icc_le_two_mul_poissonTrace
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : HermitianMatrix ι) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    (eigenCount A (Set.Icc (e - η) (e + η)) : ℝ) ≤
      2 * η *
        ∑ i : Fin (Fintype.card ι),
          η / ((orderedEigenvalue A i - e) ^ 2 + η ^ 2) := by
  classical
  have hcard :
      (eigenCount A (Set.Icc (e - η) (e + η)) : ℝ) =
      ∑ i ∈ Finset.univ.filter (fun i =>
        orderedEigenvalue A i ∈ Set.Icc (e - η) (e + η)), (1 : ℝ) := by
    rw [eigenCount_def]
    simp
  rw [hcard]
  calc
    (∑ i ∈ Finset.univ.filter (fun i =>
          orderedEigenvalue A i ∈ Set.Icc (e - η) (e + η)), (1 : ℝ)) ≤
        ∑ i ∈ Finset.univ.filter (fun i =>
          orderedEigenvalue A i ∈ Set.Icc (e - η) (e + η)),
          2 * η * (η /
            ((orderedEigenvalue A i - e) ^ 2 + η ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_Icc] at hi
      have hlo : -η ≤ orderedEigenvalue A i - e := by linarith [hi.1]
      have hhi : orderedEigenvalue A i - e ≤ η := by linarith [hi.2]
      have hsquare : (orderedEigenvalue A i - e) ^ 2 ≤ η ^ 2 := by
        nlinarith
      have hden : 0 < (orderedEigenvalue A i - e) ^ 2 + η ^ 2 := by
        nlinarith [sq_nonneg (orderedEigenvalue A i - e)]
      rw [show 2 * η *
          (η / ((orderedEigenvalue A i - e) ^ 2 + η ^ 2)) =
          (2 * η ^ 2) /
            ((orderedEigenvalue A i - e) ^ 2 + η ^ 2) by ring]
      rw [le_div_iff₀ hden]
      nlinarith
    _ ≤ ∑ i : Fin (Fintype.card ι),
          2 * η * (η /
            ((orderedEigenvalue A i - e) ^ 2 + η ^ 2)) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro i
      have hden : 0 < (orderedEigenvalue A i - e) ^ 2 + η ^ 2 := by
        nlinarith [sq_nonneg (orderedEigenvalue A i - e)]
      exact mul_nonneg (mul_nonneg (by norm_num) hη.le)
        (div_nonneg hη.le hden.le)
    _ = 2 * η *
        ∑ i : Fin (Fintype.card ι),
          η / ((orderedEigenvalue A i - e) ^ 2 + η ^ 2) := by
      rw [Finset.mul_sum]

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The physical Gaussian-ring Hamiltonian after a deterministic Hermitian
deformation, bundled as a Hermitian matrix. -/
def physicalDeformedHermitian
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (ω : M.Ω) :
    HermitianMatrix (Site p.n p.W) :=
  ⟨M.H ω + V, M.isHermitian ω |>.add hV⟩

/-- The all-block zero-absorber physical resolvent trace is exactly the
multiplicity-counted ordered Poisson sum. -/
theorem sum_blockNegativeImaginaryTrace_physical_eq_orderedPoisson
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (e : ℝ) {η : ℝ} (hη : 0 < η)
    (ω : M.Ω) :
    ∑ j : ZMod p.n, blockNegativeImaginaryTrace
        (physicalDeformedAbsorbedResolvent M V 0 e η ω) j =
      ∑ i : Fin (Fintype.card (Site p.n p.W)),
        η / ((orderedEigenvalue (physicalDeformedHermitian M V hV ω) i - e) ^ 2 +
          η ^ 2) := by
  rw [sum_blockNegativeImaginaryTrace_eq_neg_trace_im]
  unfold physicalDeformedAbsorbedResolvent physicalAbsorbedResolvent
  simpa [physicalDeformedHermitian] using
    neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
      (physicalDeformedHermitian M V hV ω) e hη

/-- Pointwise physical interval count is controlled by the all-block
zero-absorber resolvent trace. -/
theorem physical_eigenCount_Icc_le_projectedTrace
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (e : ℝ) {η : ℝ} (hη : 0 < η)
    (ω : M.Ω) :
    (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e - η) (e + η)) : ℝ) ≤
      2 * η *
        ∑ j : ZMod p.n, blockNegativeImaginaryTrace
          (physicalDeformedAbsorbedResolvent M V 0 e η ω) j := by
  rw [sum_blockNegativeImaginaryTrace_physical_eq_orderedPoisson
    M V hV e hη ω]
  exact eigenCount_Icc_le_two_mul_poissonTrace
    (physicalDeformedHermitian M V hV ω) e hη

/-- The physically deformed Hermitian matrix is measurable. -/
theorem measurable_physicalDeformedHermitian
    {p : Params} (M : Law p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) :
    Measurable (physicalDeformedHermitian M V hV) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact (M.measurable_entry x y).add measurable_const

/-- **Gaussian-ring first counting estimate.**  Taking all blocks and zero
absorber in the physical projected-Wegner theorem gives the exact symmetric
interval estimate

`E N_[e-η,e+η] ≤ 2 η π (C / sqrt c) W n`.

The trace and eigenvalue count are unnormalized and count multiplicity. -/
theorem expected_eigenCount_Icc_physical_le
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    ∫ ω, (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e - η) (e + η)) : ℝ) ∂M.P ≤
      2 * η *
        (Real.pi * (input.C / Real.sqrt p.c) *
          (p.W : ℝ) * (p.n : ℝ)) := by
  let g : ZMod p.n → M.Ω → ℝ := fun j ω =>
    blockNegativeImaginaryTrace
      (physicalDeformedAbsorbedResolvent M V 0 e η ω) j
  let T : M.Ω → ℝ := fun ω => ∑ j, g j ω
  have hzero : (0 : Matrix (Site p.n p.W) (Site p.n p.W) ℂ).PosSemidef :=
    Matrix.PosSemidef.zero
  have havg : SingleBlockAveraging M.P g
      (input.C / Real.sqrt p.c) (p.W : ℝ) :=
    (M.scaledPhysicalSchurMatrixData V 0 hV hzero e η hη).singleBlockAveraging
      input M hη
  let hproj : ProjectedTraceDecomposition g (Finset.univ : Finset (ZMod p.n)) :=
    { projectedTrace := T
      eq_sum := by
        funext ω
        simp [T, g] }
  have hTint : Integrable T M.P := hproj.integrable M.P havg
  have hTnonneg : 0 ≤ᵐ[M.P] T := by
    have hall : ∀ᵐ ω ∂M.P, ∀ j, 0 ≤ g j ω :=
      ae_all_iff.mpr havg.nonneg
    filter_upwards [hall] with ω hω
    exact Finset.sum_nonneg fun j _hj => hω j
  have hcountMeas : Measurable (fun ω =>
      (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e - η) (e + η)) : ℝ)) :=
    measurable_from_nat.comp
      ((measurable_eigenCount_Icc (e - η) (e + η)).comp
        (measurable_physicalDeformedHermitian M V hV))
  have hpoint : ∀ ω,
      (eigenCount (physicalDeformedHermitian M V hV ω)
          (Set.Icc (e - η) (e + η)) : ℝ) ≤ 2 * η * T ω := by
    intro ω
    simpa [T, g] using physical_eigenCount_Icc_le_projectedTrace
      M V hV e hη ω
  have hrhsInt : Integrable (fun ω => 2 * η * T ω) M.P :=
    hTint.const_mul (2 * η)
  have hcountInt : Integrable (fun ω =>
      (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e - η) (e + η)) : ℝ)) M.P := by
    apply hrhsInt.mono' hcountMeas.aestronglyMeasurable
    filter_upwards with ω
    have hcnonneg : 0 ≤
        (eigenCount (physicalDeformedHermitian M V hV ω)
          (Set.Icc (e - η) (e + η)) : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hcnonneg]
    exact hpoint ω
  calc
    (∫ ω, (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc (e - η) (e + η)) : ℝ) ∂M.P) ≤
        ∫ ω, 2 * η * T ω ∂M.P :=
      integral_mono_ae hcountInt hrhsInt (ae_of_all M.P hpoint)
    _ = 2 * η * ∫ ω, T ω ∂M.P := by rw [integral_const_mul]
    _ ≤ 2 * η *
        (Real.pi * (input.C / Real.sqrt p.c) *
          (p.W : ℝ) * (p.n : ℝ)) := by
      gcongr
      simpa [T, g] using
        projectedWegner_gaussianRing_physical input M V 0 hV hzero e hη
          (Finset.univ : Finset (ZMod p.n))

/-- Arbitrary closed-interval version of the physical first-count estimate. -/
theorem expected_eigenCount_arbitrary_Icc_physical_le
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (V : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) {a b : ℝ} (hab : a < b) :
    ∫ ω, (eigenCount (physicalDeformedHermitian M V hV ω)
        (Set.Icc a b) : ℝ) ∂M.P ≤
      Real.pi * (input.C / Real.sqrt p.c) *
        (p.W : ℝ) * (p.n : ℝ) * (b - a) := by
  let e := (a + b) / 2
  let η := (b - a) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have hset : Set.Icc (e - η) (e + η) = Set.Icc a b := by
    congr 2 <;> dsimp [e, η] <;> ring
  rw [← hset]
  have h := expected_eigenCount_Icc_physical_le input M V hV e hη
  dsimp [η] at h ⊢
  nlinarith

end GaussianRing
end CoareaNative.BlockBand
