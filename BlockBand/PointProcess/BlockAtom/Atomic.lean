module

public import Mathlib
public import BlockBand.PointProcess.Vague
public import BlockBand.Model.Construction.MarkedStateTopology

/-!
# Locally finite integer-valued measures are carried by their atoms

The point process of a critical limit is a `VaguePointMeasure`, i.e. a Borel measure that is
finite on compacts and takes values in `ℕ ∪ {∞}` on measurable sets. On a second-countable,
locally compact Hausdorff space such a measure gives zero mass to the (not necessarily
measurable) set of its non-atoms `{x | ξ {x} = 0}`. This is used for the vanishing of block
atoms.

Proof: the space is metrizable and σ-compact, so the locally finite measure `ξ` is outer
regular; for a non-atom `x` there is an open `U ∋ x` with `ξ U < 1`, hence `ξ U = 0` by
integrality. Second countability (`measure_null_of_locally_null`) then gives that the
non-atom set is null. Integrals of functions vanishing on atoms are therefore zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.PointProcess.BlockAtom

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]

/-- Measure: any `VaguePointMeasure` `ξ` (locally finite, `ℕ ∪ {∞}`-valued Borel measure) on a
second-countable, locally compact Hausdorff Borel space `X`. Conclusion: every non-atom
`x` (`ξ {x} = 0`) has an open neighbourhood of `ξ`-mass exactly zero. -/
theorem exists_isOpen_measure_eq_zero_of_singleton (ξ : VaguePointMeasure X) {x : X}
    (hx : ξ.measure {x} = 0) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ξ.measure U = 0 := by
  have : MetrizableSpace X := metrizableSpace_of_t3_secondCountable X
  have hlt : ξ.measure {x} < 1 := by rw [hx]; exact zero_lt_one
  obtain ⟨U, hxU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt (μ := ξ.measure) {x} 1 hlt
  refine ⟨U, hUo, hxU rfl, ?_⟩
  rcases ξ.integer_valued U hUo.measurableSet with h | ⟨n, hn⟩
  · rw [h] at hU; exact absurd hU (not_lt.2 le_top)
  · rw [hn] at hU ⊢
    have : n < 1 := by exact_mod_cast hU
    simp [Nat.lt_one_iff.1 this]

/-- Measure: any `VaguePointMeasure` `ξ` on a second-countable, locally compact Hausdorff Borel
space `X`. Conclusion: `ξ` is carried by its atoms, i.e. the set `{x | ξ {x} = 0}` is
`ξ`-null (no measurability of that set is required). -/
theorem ae_measure_singleton_ne_zero (ξ : VaguePointMeasure X) :
    ∀ᵐ x ∂ξ.measure, ξ.measure {x} ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨U, hUo, hxU, hU⟩ := exists_isOpen_measure_eq_zero_of_singleton ξ hx
  exact ⟨U, mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hxU), hU⟩

/-- Measure: any `VaguePointMeasure` `ξ` on a second-countable, locally compact Hausdorff Borel
space `X`. For every `f : X → ℝ≥0∞` (no measurability needed) vanishing at every atom of
`ξ`, the lower Lebesgue integral `∫⁻ f dξ` is zero. -/
theorem lintegral_eq_zero_of_atoms (ξ : VaguePointMeasure X) (f : X → ENNReal)
    (hf : ∀ x, ξ.measure {x} ≠ 0 → f x = 0) : ∫⁻ x, f x ∂ξ.measure = 0 := by
  have h : f =ᵐ[ξ.measure] 0 :=
    (ae_measure_singleton_ne_zero ξ).mono fun x hx => hf x hx
  rw [lintegral_congr_ae h]
  simp

/-- Measure: any `VaguePointMeasure` `ξ` on a second-countable, locally compact Hausdorff Borel
space `X`. For every `f : X → ℝ` (no measurability or integrability needed) vanishing at
every atom of `ξ`, the Bochner integral `∫ f dξ` is zero. -/
theorem integral_eq_zero_of_atoms (ξ : VaguePointMeasure X) (f : X → ℝ)
    (hf : ∀ x, ξ.measure {x} ≠ 0 → f x = 0) : ∫ x, f x ∂ξ.measure = 0 := by
  have h : f =ᵐ[ξ.measure] 0 :=
    (ae_measure_singleton_ne_zero ξ).mono fun x hx => hf x hx
  rw [integral_congr_ae h]
  simp

/-- Instantiation on the marked spectral space `ℝ × P(T)` (weak topology on `P(T)`, with the
Giry measurable structure, which is Borel by
`Model.Construction.markedSpectralSpace_borelSpace`): every marked point measure is carried
by its atoms. -/
theorem markedSpectral_ae_atom (ξ : VaguePointMeasure MarkedSpectralSpace) :
    ∀ᵐ x ∂ξ.measure, ξ.measure {x} ≠ 0 := by
  have : BorelSpace MarkedSpectralSpace := Model.Construction.markedSpectralSpace_borelSpace
  exact ae_measure_singleton_ne_zero ξ

end BlockBand.PointProcess.BlockAtom
