module

public import BlockBand.SourceProcess.SourcePins.AtomSet
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `atomSet p R` is weakly closed

`isClosed_atomSet`: let an ultrafilter `u` on `𝓜_f[0,1]` converge to `ν` and contain
`atomSet p R`. Each measure of the set carries a chosen sequence. These sequences lie in the
compact space `[0,1]^ℕ`, so their image ultrafilter converges to some `z`. Antitonicity and the
partial sums `Σ_{i<n} t_i^p ≤ R` pass to `z`. For a test `f` vanishing on `[0,x]`, the integrals
`∫ f dη` converge to `∫ f dν` (weak convergence) and equal the finite cut sums, which converge to
the cut sum of `z`. No metrizability is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourcePins

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ENNReal NNReal BoundedContinuousFunction

/-- The sequence chosen for a measure of `atomSet p R` (zero outside), as a point of `[0,1]^ℕ`. -/
def atomSeq (p R : ℝ) (η : FiniteMeasure unitInterval) : ℕ → unitInterval := by
  classical
  exact if h : η ∈ atomSet p R then fun i => toUnit (h.choose i) else fun _ => 0

theorem atomSeq_spec {p R : ℝ} {η : FiniteMeasure unitInterval} (h : η ∈ atomSet p R) :
    PBound p R (fun i => (atomSeq p R η i : ℝ)) ∧ AgreeCut p R η (fun i => (atomSeq p R η i : ℝ)) := by
  have he : (fun i => (atomSeq p R η i : ℝ)) = h.choose := by
    funext i
    simp only [atomSeq, dite_eq_left h]
    exact coe_toUnit_of_mem (h.choose_spec.1.2.1 i).1 (h.choose_spec.1.2.1 i).2
  rw [he]
  exact h.choose_spec

/-- **`S_R` is weakly closed.** -/
theorem isClosed_atomSet {p R : ℝ} (hp : 0 < p) : IsClosed (atomSet p R) := by
  rw [isClosed_iff_ultrafilter]
  intro ν u hu hmem
  obtain ⟨z, -, hz⟩ := isCompact_univ.ultrafilter_le_nhds (u.map (atomSeq p R)) (by simp)
  have hτ : Tendsto (atomSeq p R) u (𝓝 z) := hz
  have hτi : ∀ i, Tendsto (fun η => (atomSeq p R η i : ℝ)) u (𝓝 (z i : ℝ)) := fun i =>
    (continuous_subtype_val.tendsto _).comp (((continuous_apply i).tendsto _).comp hτ)
  have hev : ∀ᶠ η in (u : Filter (FiniteMeasure unitInterval)), η ∈ atomSet p R := hmem
  refine ⟨fun i => (z i : ℝ), ⟨fun i j hij => ?_, fun i => (z i).2, fun n => ?_⟩, ?_⟩
  · exact le_of_tendsto_of_tendsto (hτi j) (hτi i) (hev.mono fun η hη => (atomSeq_spec hη).1.1 hij)
  · refine le_of_tendsto (tendsto_finsetSum _ fun i _ => (hτi i).rpow_const (Or.inr hp.le)) ?_
    exact hev.mono fun η hη => (atomSeq_spec hη).1.2.2 n
  · intro x hx f hf
    have h1 : Tendsto (fun η : FiniteMeasure unitInterval => ∫ y, f y ∂(η : Measure unitInterval))
        u (𝓝 (∫ y, f y ∂(ν : Measure unitInterval))) :=
      ((FiniteMeasure.continuous_integral_boundedContinuousFunction f).tendsto ν).mono_left hu
    have h2 : Tendsto (fun η => ∑ i ∈ Finset.range (cutIdx p R x),
        (atomSeq p R η i : ℝ) * f (toUnit (atomSeq p R η i : ℝ))) u
        (𝓝 (∑ i ∈ Finset.range (cutIdx p R x), (z i : ℝ) * f (toUnit (z i : ℝ)))) :=
      tendsto_finsetSum _ fun i _ => (hτi i).mul
        ((f.continuous.tendsto _).comp ((continuous_toUnit.tendsto _).comp (hτi i)))
    exact tendsto_nhds_unique_of_eventuallyEq h1 h2
      (hev.mono fun η hη => (atomSeq_spec hη).2 x hx f hf)

end BlockBand.SourceProcess.SourcePins
