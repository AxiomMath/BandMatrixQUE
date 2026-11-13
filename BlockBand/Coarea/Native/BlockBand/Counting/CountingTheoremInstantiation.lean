module

public import BlockBand.Coarea.Native.BlockBand.Counting.CountingTheorem
public import BlockBand.Coarea.Native.BlockBand.Counting.UnfoldedMarkedConfiguration
public import BlockBand.Coarea.Native.BlockBand.Counting.LocalPointMeasureStateSpace

/-!
# Concrete common-state precursor for the counting theorem

Finite unfolded configurations of arbitrary cardinality are embedded into the
same consistent local-window state space, with trivial `Unit` marks.  The
module then gives the exact Prokhorov subsequence conclusion from explicit
compact containment and local-count tails.  No weak limit is assumed and no
canonical vague topology is claimed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u

/-- A minimal determining family used by the common-state embedding.  The
empty restriction has integer mass automatically.  Richer determining
families require the separate boundary/restriction interfaces formalized in
`IntegerPointMeasureClosure`. -/
def unitWindowDeterminingFamily (_n : ℕ) (_ : Unit) :
    Set (MarkedSpectralSpace Unit) := ∅

/-- A finite configuration of any size embeds in the common bundled state
space, so the target type does not depend on the number of points. -/
def finiteMarkedLocalPointState
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) :
    LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily :=
  ⟨finiteMarkedLocalWindowEncoding x,
    finiteMarkedLocalWindowEncoding_consistent x,
    by
      intro n k
      refine ⟨0, ?_⟩
      simp [unitWindowDeterminingFamily]⟩

/-- The underlying encoding of the common-state embedding is definitionally
the finite configuration's local-window encoding. -/
theorem finiteMarkedLocalPointState_encoding
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) :
    (finiteMarkedLocalPointState x).encoding =
      finiteMarkedLocalWindowEncoding x := rfl

/-- A concrete unfolded BlockGUE sample maps into the common state space,
independently of its matrix dimension. -/
def BlockGUE.unfoldedLocalPointState
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω) :
    LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily :=
  finiteMarkedLocalPointState
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω)

/-- Explicit interface for the measurability and compact-containment facts
needed to turn the concrete sample map into a law.  These are topology-specific
and are not consequences of PSSS factorial bounds alone. -/
structure CountingCommonStateInput
    (μs : ℕ → ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily)) where
  localCount : LocalPointMeasureStateSpace Unit Unit
    unitWindowDeterminingFamily → ENNReal
  compactSet : ℕ → Set (LocalPointMeasureStateSpace Unit Unit
    unitWindowDeterminingFamily)
  compact : ∀ m, IsCompact (compactSet m)
  complement_subset : ∀ m, (compactSet m)ᶜ ⊆
    {x | (m : ENNReal) ≤ localCount x}
  tailConstant : ENNReal
  tailConstant_ne_top : tailConstant ≠ ⊤
  localCountTail : ∀ i m, (μs i : Measure _)
    {x | (m : ENNReal) ≤ localCount x} ≤
      tailConstant / (m : ENNReal)

/-- The common-state laws have a weakly convergent subsequence, constructed by
Prokhorov rather than supplied as an assumption. -/
theorem exists_countingCommonState_weak_subsequence
    [T2Space (LocalPointMeasureStateSpace Unit Unit
      unitWindowDeterminingFamily)]
    [BorelSpace (LocalPointMeasureStateSpace Unit Unit
      unitWindowDeterminingFamily)]
    [FirstCountableTopology (ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily))]
    (μs : ℕ → ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily))
    (input : CountingCommonStateInput μs) :
    ∃ μ : ProbabilityMeasure
        (LocalPointMeasureStateSpace Unit Unit unitWindowDeterminingFamily),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  exact exists_weaklyConvergent_subsequence_localPointMeasureStateSpace
    μs input.localCount input.compactSet input.compact
    input.complement_subset input.tailConstant input.tailConstant_ne_top
    input.localCountTail

/-- The unconditional finite-matrix part of the paper's counting theorem:
PSSS supplies every falling-factorial interval-count estimate.  This statement
requires no weak limit or topology-specific input. -/
theorem counting_factorialCount_unconditional
    (psss : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) (hr : 1 ≤ r) :
    ∫ ω, ((BlockGUE.intervalCount M A₀ (Set.Icc a b) ω).descFactorial r : ℝ) ∂M.P
      ≤ (psss.C * (Fintype.card (BlockGUE.Index d) : ℝ) * (b - a)) ^ r :=
  psss_factorialCount psss hd M A₀ a b hab r hr

/-- The unfolded exponential local-count estimate, also requiring no weak
limit.  Its only mathematical input is the external PSSS factorial-count
interface together with the displayed unfolding normalization. -/
theorem counting_unfoldedExponential_unconditional
    (psss : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R t : ℝ) (hL : 0 < L) (hρ : 0 < ρ)
    (hR : 0 ≤ R)
    (hdim : (Fintype.card (BlockGUE.Index d) : ℝ) ≤ L)
    (ht : 0 ≤ t) :
    ∫ ω, Real.exp
      (t * (BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω : ℝ)) ∂M.P
      ≤ Real.exp (2 * R * (psss.C / ρ) * (Real.exp t - 1)) :=
  psss_unfoldedCountExponential psss hd M A₀ e L ρ R t
    hL hρ hR hdim ht

end CoareaNative.BlockBand
