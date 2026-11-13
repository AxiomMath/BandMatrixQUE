module

public import BlockBand.SourceProcess.ComplexConstruct.Values
public import BlockBand.SourceProcess.ComplexConstruct.Tight
public import BlockBand.SourceProcess.ComplexConstruct.Prokhorov

/-!
# `ComplexSourceConstruction` from the hypotheses

`complexSourceConstruction_of_pins`. `TransmissionLawContract.law` at `κ ≡ 0` gives `(P, μ)`. At
one source-free start `s₀`, `iterated_values` shows that `E_W Φ` converges for every `Φ`; with
`ComplexSourceTight`, `exists_weak_limit_of_tight` (Prokhorov) gives the limit law `ν`. For every
start `s` and test `Φ`, `iterated_values` gives the realized values `Ψ`, `Λ` and a limit `L` of
`Λ`, and `L = ∫Φdν` because both are limits of `E_W Φ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

/-- A source-free start below all birth times. -/
theorem exists_start {np : ℕ} {τ : Fin np → ℝ} (hτ : ∀ j, 0 < τ j) :
    ∃ s : ℝ, 0 < s ∧ ∀ j, s < τ j := by
  classical
  set A : Finset ℝ := insert 1 (Finset.univ.image τ)
  have hA : A.Nonempty := Finset.insert_nonempty _ _
  have hpos : 0 < A.min' hA := by
    obtain ⟨x, hx, hxe⟩ : ∃ x ∈ A, A.min' hA = x := ⟨_, Finset.min'_mem A hA, rfl⟩
    rw [hxe]
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact hτ j
  refine ⟨A.min' hA / 2, half_pos hpos, fun j => ?_⟩
  have : A.min' hA ≤ τ j :=
    Finset.min'_le A (τ j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem τ (by simp)))
  linarith

/-- The expectation is the integral against the law. -/
theorem integral_physLaw (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) (W : ℕ) :
    ∫ y, Φ y ∂physLaw b E T τ m W = physExpectation b E T τ m Φ W := by
  unfold physLaw physExpectation
  exact integral_map (measurable_complexSourceData b E W _ τ m).aemeasurable
    Φ.continuous.aestronglyMeasurable

/-- **`ComplexSourceConstruction` from the hypotheses.** -/
theorem complexSourceConstruction_of_pins (hTL : TransmissionLawContract)
    (hA1 : EntranceAtomic) (hA2 : SeqExtraction) (hU : ComplexFiniteUniqueness)
    (hEx : ComplexModelExists) (hCap : ComplexCapRemoval) (hCut : ComplexCutoffRemoval)
    (hPA : ComplexPhysicalApproximation) (hTi : ComplexSourceTight) :
    ComplexSourceConstruction := by
  intro b E np τ m T hD
  obtain ⟨hb0, hb1, hE1, hE2, -, hτ, -⟩ := id hD
  obtain ⟨Ω, mΩ, P, μ, hlim, -⟩ := hTL.law b hb0 hb1 E hE1 hE2 _ isAbsorptionProfile_zero'
  have hval := fun {s : ℝ} (hs : 0 < s) (hsτ : ∀ j, s < τ j) Φ =>
    iterated_values hA1 hA2 hU hEx hCap hCut hPA hD hlim hs hsτ Φ
  obtain ⟨s₀, hs₀, hs₀τ⟩ := exists_start hτ
  let μW : ℕ → ProbabilityMeasure (SourceData np) := fun W => ⟨physLaw b E T τ m W, inferInstance⟩
  obtain ⟨ν, hν⟩ := exists_weak_limit_of_tight μW (hTi b E np τ m T hD) fun Φ => by
    obtain ⟨-, -, -, -, L, -, hL⟩ := hval hs₀ hs₀τ Φ
    refine ⟨L, ?_⟩
    simpa only [μW, ProbabilityMeasure.coe_mk, integral_physLaw] using hL
  have hν' : ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
      Tendsto (physExpectation b E T τ m Φ) atTop (𝓝 (∫ y, Φ y ∂(ν : Measure (SourceData np)))) :=
    fun Φ => by simpa only [μW, ProbabilityMeasure.coe_mk, integral_physLaw] using hν Φ
  refine ⟨ν, ⟨inferInstance, hν'⟩, Ω, mΩ, P, μ, hlim, fun s hs hsτ Φ => ?_⟩
  obtain ⟨Ψ, hR, Λ, hΛ, L, hL, hphys⟩ := hval hs hsτ Φ
  have hLeq : L = ∫ y, Φ y ∂(ν : Measure (SourceData np)) := tendsto_nhds_unique hphys (hν' Φ)
  exact ⟨Ψ, hR, Λ, hΛ, hLeq ▸ hL⟩

end BlockBand.SourceProcess.ComplexConstruct
