module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFullCompressionFatou
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCanonicalSelectedFormula
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiMovingCountMeasurability

/-!
# Normalized PSSS kernel

This is the kernel of formula (2.13) of
arXiv:1608.02922.  The predecessor is the fixed-target `Icc a b` factorial of
the full original public deformation's ambient compression.  Only the
auxiliary multiplicity uses `Ioo (-xi) xi`.  The energy `1/π`, standard Cauchy,
and Poisson-radial factors are kept as separate factors.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 700000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The five variables are the fixed exterior, selected block, energy, Cauchy
parameter, and positive radial parameter. -/
abbrev CorrectedSelectedParameters {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  ((((BlockProductDisintegration.ExteriorSample dims j ×
    BlockProductDisintegration.SelectedSample dims j) × ℝ) × ℝ) × ℝ)

/-- Auxiliary Hermitian family in the fixed-target reduction. -/
def correctedSelectedAuxiliaryHermitian
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (p : CorrectedSelectedParameters dims j) :
    HermitianMatrix (Fin (dims j)) :=
  addHermitian
    (publicGUERealBackground
      (publicFrozenCanonicalHermitian A₀ j p.1.1.1.1 p.1.1.2 eta)
      (canonicalFrozenAbsorber
        (frozenSelectedA A₀ j p.1.1.1.1)
        (frozenSelectedB A₀ j p.1.1.1.1)
        (frozenSelectedC A₀ j p.1.1.1.1)
        (frozenSelectedD A₀ j p.1.1.1.1) p.1.1.2 eta)
      (publicFrozenCanonicalAbsorber_posSemidef A₀ j p.1.1.1.1 p.1.1.2
        heta) p.1.2)
    (p.1.1.1.2 ⟨j, by simp⟩)

/-- The auxiliary multiplicity alone uses the open radial interval. -/
def correctedSelectedAuxiliaryOpenCount
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (p : CorrectedSelectedParameters dims j) : ℝ≥0∞ :=
  (eigenCount (correctedSelectedAuxiliaryHermitian A₀ j heta p)
    (Set.Ioo (-p.2) p.2) : ℝ≥0∞)

/-- Joint measurability of the auxiliary Hermitian family. -/
theorem measurable_correctedSelectedAuxiliaryHermitian
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) :
    Measurable (correctedSelectedAuxiliaryHermitian A₀ j heta) := by
  let bg := fun p : CorrectedSelectedParameters dims j =>
    publicFrozenCanonicalBackground A₀ j ((p.1.1.1.1, p.1.1.2), eta)
  let q := fun p : CorrectedSelectedParameters dims j =>
    publicFrozenCanonicalAbsorber A₀ j ((p.1.1.1.1, p.1.1.2), eta)
  let V := fun p : CorrectedSelectedParameters dims j =>
    (p.1.1.1.2 ⟨j, by simp⟩).1
  have hbg : Measurable bg :=
    (measurable_publicFrozenCanonicalBackground dims A₀ j).comp (by fun_prop)
  have hq : Measurable q :=
    (measurable_publicFrozenCanonicalAbsorber dims A₀ j).comp (by fun_prop)
  have hV : Measurable V := measurable_subtype_coe.comp
    ((measurable_pi_apply (⟨j, by simp⟩ : {i : Fin k // ¬ i ≠ j})).comp
      (measurable_snd.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst))))
  apply Measurable.subtype_mk
  change Measurable (fun p => bg p + (p.1.2 : ℂ) • q p + V p)
  rw [Matrix.measurable_iff]
  intro x y
  exact ((Matrix.measurable_iff.mp hbg x y).add
    ((Complex.continuous_ofReal.measurable.comp
      (measurable_snd.comp measurable_fst)).mul
        (Matrix.measurable_iff.mp hq x y))).add
    (Matrix.measurable_iff.mp hV x y)

/-- Joint measurability of the open auxiliary count. -/
theorem measurable_correctedSelectedAuxiliaryOpenCount
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) :
    Measurable (correctedSelectedAuxiliaryOpenCount A₀ j heta) := by
  exact measurable_eigenCount_Ioo_family
    (correctedSelectedAuxiliaryHermitian A₀ j heta)
    (measurable_correctedSelectedAuxiliaryHermitian dims A₀ j heta)
    (fun p : CorrectedSelectedParameters dims j => p.2) measurable_snd

end PSSSNative.BlockBand.PSSS
