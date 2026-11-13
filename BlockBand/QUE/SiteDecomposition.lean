module

public import BlockBand.Foundations.BlockDecomposition

/-!
# Block-to-site decomposition of the quadratic statistic

The centred site statistic splits into its block-average part and the within-block residual;
when the within-block mixed moments agree, the mixed term vanishes and the quadratic statistic is
the sum of the block-average and residual statistics (`statistic_decomposition`).

The measure is any `μ : Measure Ω`; sites are the finite product `B × A` with nonempty `A`. Tests
and masses are real, the baseline is a real scalar, and the quadratic norm is the real absolute
value squared. The mixed-moment equalities and the integrability are explicit hypotheses; all
conclusions are finite identities.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.QUE

open MeasureTheory
open scoped BigOperators
open BlockBand.Foundations.FiniteBlock

variable {Ω B A : Type*} [MeasurableSpace Ω] [Fintype B] [Fintype A] [Nonempty A]

/-- Centred linear site statistic, pointwise for a mass field. The physical baseline is `1/(nW)`;
arbitrary real baselines are allowed. -/
def fluctuation (mass : Ω → B × A → ℝ) (baseline : ℝ)
    (v : B × A → ℝ) (ω : Ω) : ℝ :=
  ∑ x : B × A, v x * (mass ω x - baseline)

/-- The expectation of the squared real fluctuation under the specified law. -/
def quadraticStatistic (μ : Measure Ω) (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) : ℝ :=
  ∫ ω, |fluctuation mass baseline v ω| ^ 2 ∂μ

omit [MeasurableSpace Ω] [Nonempty A] in
/-- Pointwise decomposition into the block-constant and centred parts (deterministic). -/
theorem fluctuation_decomposition (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (ω : Ω) :
    fluctuation mass baseline v ω =
      fluctuation mass baseline (constantPart v) ω +
        fluctuation mass baseline (centeredPart v) ω := by
  unfold fluctuation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [centeredPart]
  ring

/-- The within-block residual has zero total deterministic sum. -/
theorem sum_centered_sites (v : B × A → ℝ) :
    ∑ x : B × A, centeredPart v x = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [sum_centered, Finset.sum_const_zero]

omit [MeasurableSpace Ω] in
/-- The uniform baseline vanishes from the within-block statistic exactly. -/
theorem fluctuation_centered (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (ω : Ω) :
    fluctuation mass baseline (centeredPart v) ω =
      ∑ x : B × A, centeredPart v x * mass ω x := by
  unfold fluctuation
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, sum_centered_sites, zero_mul, sub_zero]

omit [MeasurableSpace Ω] in
/-- Pointwise multiplication of the residual by a block-measurable quantity
is a finite sum of coordinate mixed products. -/
theorem mixed_centered_expansion (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (F : Ω → ℝ) (ω : Ω) :
    F ω * fluctuation mass baseline (centeredPart v) ω =
      ∑ x : B × A, centeredPart v x * (F ω * mass ω x) := by
  rw [fluctuation_centered, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Equality of the coordinate mixed moments within a block gives a zero mixed term. `κ b` is the
common moment `E[F mass_(b,a)]`; in the physical model these equalities come from Haar or
block-unitary invariance. The integrability assumptions justify the finite integral expansion. -/
theorem mixed_term_zero (μ : Measure Ω) (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (F : Ω → ℝ) (κ : B → ℝ)
    (hint : ∀ x, Integrable (fun ω => F ω * mass ω x) μ)
    (hmoment : ∀ b a, (∫ ω, F ω * mass ω (b, a) ∂μ) = κ b) :
    (∫ ω, F ω * fluctuation mass baseline (centeredPart v) ω ∂μ) = 0 := by
  simp_rw [mixed_centered_expansion]
  rw [integral_finsetSum _ (fun x _ => (hint x).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [hmoment]
  simp_rw [← Finset.sum_mul, sum_centered]
  simp

/-- The same coordinate integrability implies integrability of the mixed term. -/
theorem integrable_mixed_term (μ : Measure Ω) (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (F : Ω → ℝ)
    (hint : ∀ x, Integrable (fun ω => F ω * mass ω x) μ) :
    Integrable (fun ω => F ω *
      fluctuation mass baseline (centeredPart v) ω) μ := by
  simp_rw [mixed_centered_expansion]
  exact integrable_finsetSum _ (fun x _ => (hint x).const_mul _)

/-- Decomposition of the quadratic site statistic into the block-average and centred residual
statistics, from the elementary expansion and the zero mixed term. Square-integrability is
assumed under the same measure `μ`. -/
theorem statistic_decomposition (μ : Measure Ω) (mass : Ω → B × A → ℝ)
    (baseline : ℝ) (v : B × A → ℝ) (κ : B → ℝ)
    (hblock : Integrable (fun ω =>
      |fluctuation mass baseline (constantPart v) ω| ^ 2) μ)
    (hcenter : Integrable (fun ω =>
      |fluctuation mass baseline (centeredPart v) ω| ^ 2) μ)
    (hint : ∀ x, Integrable (fun ω =>
      fluctuation mass baseline (constantPart v) ω * mass ω x) μ)
    (hmoment : ∀ b a, (∫ ω,
      fluctuation mass baseline (constantPart v) ω * mass ω (b, a) ∂μ) = κ b) :
    quadraticStatistic μ mass baseline v =
      quadraticStatistic μ mass baseline (constantPart v) +
        quadraticStatistic μ mass baseline (centeredPart v) := by
  have hmix := integrable_mixed_term μ mass baseline v
    (fluctuation mass baseline (constantPart v)) hint
  have hzero := mixed_term_zero μ mass baseline v
    (fluctuation mass baseline (constantPart v)) κ hint hmoment
  have hpoint (ω : Ω) : |fluctuation mass baseline v ω| ^ 2 =
      |fluctuation mass baseline (constantPart v) ω| ^ 2 +
      |fluctuation mass baseline (centeredPart v) ω| ^ 2 +
      2 * (fluctuation mass baseline (constantPart v) ω *
        fluctuation mass baseline (centeredPart v) ω) := by
    rw [fluctuation_decomposition]
    simp only [sq_abs]
    ring
  unfold quadraticStatistic
  simp_rw [hpoint]
  have hsum : Integrable (fun ω =>
      |fluctuation mass baseline (constantPart v) ω| ^ 2 +
      |fluctuation mass baseline (centeredPart v) ω| ^ 2) μ := hblock.add hcenter
  calc
    (∫ ω,
      |fluctuation mass baseline (constantPart v) ω| ^ 2 +
      |fluctuation mass baseline (centeredPart v) ω| ^ 2 +
      2 * (fluctuation mass baseline (constantPart v) ω *
        fluctuation mass baseline (centeredPart v) ω) ∂μ) =
        (∫ ω, |fluctuation mass baseline (constantPart v) ω| ^ 2 +
          |fluctuation mass baseline (centeredPart v) ω| ^ 2 ∂μ) +
        (∫ ω, 2 * (fluctuation mass baseline (constantPart v) ω *
          fluctuation mass baseline (centeredPart v) ω) ∂μ) :=
      integral_add hsum (hmix.const_mul 2)
    _ = (∫ ω, |fluctuation mass baseline (constantPart v) ω| ^ 2 ∂μ) +
        (∫ ω, |fluctuation mass baseline (centeredPart v) ω| ^ 2 ∂μ) := by
      rw [integral_add hblock hcenter, integral_const_mul, hzero]
      ring

end BlockBand.QUE
