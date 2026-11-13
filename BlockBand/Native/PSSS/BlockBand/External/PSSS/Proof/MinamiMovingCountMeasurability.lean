module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiInductionBase
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Modular measurability for moving finite spectral counts

The Minami first reduction has both a moving Hermitian matrix and the moving
symmetric interval `(-ξ,ξ)`.  This module isolates the finite-dimensional
measurability statements from the much larger canonical Schur expressions.
Downstream modules can therefore establish measurability of their named matrix
family once and compose with these lemmas, avoiding elaboration of one giant
nested-product proof.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory Set
open scoped ENNReal

universe u v

/-- The spectral multiplicity in a moving symmetric open interval is
measurable along a measurable Hermitian family and a measurable radius. -/
theorem measurable_eigenCount_Ioo_family
    {Ω : Type v} [MeasurableSpace Ω]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (H : Ω → HermitianMatrix ι) (hH : Measurable H)
    (xi : Ω → ℝ) (hxi : Measurable xi) :
    Measurable (fun ω =>
      (eigenCount (H ω) (Set.Ioo (-xi ω) (xi ω)) : ℝ≥0∞)) := by
  let bits : Ω → Fin (Fintype.card ι) → ℕ := fun ω i =>
    Set.indicator
      {q | -xi q < orderedEigenvalue (H q) i ∧
        orderedEigenvalue (H q) i < xi q}
      (fun _ => 1) ω
  have hbits : Measurable bits := by
    rw [measurable_pi_iff]
    intro i
    apply measurable_const.indicator
    exact (measurableSet_lt hxi.neg
      ((measurable_orderedEigenvalue i).comp hH)).inter
      (measurableSet_lt ((measurable_orderedEigenvalue i).comp hH) hxi)
  let decode : (Fin (Fintype.card ι) → ℕ) → ℕ := fun b => ∑ i, b i
  have hdecode : Measurable decode := Measurable.of_discrete
  have heq : (fun ω => eigenCount (H ω) (Set.Ioo (-xi ω) (xi ω))) =
      fun ω => decode (bits ω) := by
    funext ω
    classical
    rw [eigenCount_def, Finset.card_eq_sum_ones]
    simp only [decode, bits, Finset.sum_filter, Set.mem_Ioo,
      Set.indicator_apply, Set.mem_ofPred_eq]
  have hnat : Measurable
      (fun ω => eigenCount (H ω) (Set.Ioo (-xi ω) (xi ω))) := by
    rw [heq]
    exact hdecode.comp hbits
  exact (measurable_of_countable (f := fun n : ℕ => (n : ℝ≥0∞))).comp hnat

/-- Descending factorials of a measurable natural-valued function are
measurable after the canonical cast to `ℝ≥0∞`. -/
theorem Measurable.ennreal_descFactorial
    {Ω : Type v} [MeasurableSpace Ω] (n : Ω → ℕ) (hn : Measurable n)
    (r : ℕ) :
    Measurable (fun ω => (n ω).descFactorial r : Ω → ℝ≥0∞) := by
  exact (measurable_of_countable
    (f := fun q : ℕ => (q.descFactorial r : ℝ≥0∞))).comp hn

/-- Every finite spectral descending-factorial weight is finite in
`ℝ≥0∞`; no integrability or boundedness assumption is used. -/
theorem ennreal_descFactorial_ne_top (n r : ℕ) :
    (n.descFactorial r : ℝ≥0∞) ≠ ⊤ := by
  exact ENNReal.natCast_ne_top _

end PSSSNative.BlockBand.PSSS
