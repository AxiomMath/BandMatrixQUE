module

public import BlockBand.Coarea.Native.BlockBand.Probability.VagueCountLawConvergence
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Natural-valued local restriction count laws

This module supplies the scalar encoding bridge left explicit by
`VagueCountLawConvergence`.  A nonnegative real is decoded to the unique
natural number when it belongs to the closed natural lattice, and to zero
otherwise.  For restriction masses which are almost surely natural-valued,
re-encoding the resulting `ProbabilityMeasure ℕ` recovers the original
`NNReal` mass law exactly.

The weak-convergence theorem below is support-aware: although the total decoder
is not continuous on all of `NNReal`, Portmanteau applies because every law is
supported on the closed natural lattice.  This is precisely the hypothesis
provided for local restriction masses by `NaturalRestrictionLawClosureInput`.
The final constructor packages this convergence together with explicit
finite-volume exponential moment hypotheses into the paper-facing
`PaperCountingWeakExponentialUIInput`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

universe u v

/-- Decode the closed natural lattice in `NNReal`, with the harmless default
zero away from that lattice. -/
def nnrealNaturalPart (x : NNReal) : ℕ := by
  classical
  exact if x ∈ Set.range ((↑) : ℕ → NNReal) then ⌊x⌋₊ else 0

/-- The natural-lattice decoder is measurable. -/
theorem measurable_nnrealNaturalPart : Measurable nnrealNaturalPart := by
  classical
  unfold nnrealNaturalPart
  exact Measurable.ite isClosed_range_natCast_nnreal.measurableSet
    Nat.measurable_floor measurable_const

@[simp] theorem nnrealNaturalPart_natCast (n : ℕ) :
    nnrealNaturalPart (n : NNReal) = n := by
  simp [nnrealNaturalPart, Nat.floor_natCast]

/-- On its intended closed carrier, decoding and re-encoding are inverse. -/
theorem natCast_nnrealNaturalPart_eq {x : NNReal}
    (hx : x ∈ Set.range ((↑) : ℕ → NNReal)) :
    (nnrealNaturalPart x : NNReal) = x := by
  obtain ⟨n, rfl⟩ := hx
  simp

/-- The scalar natural count law extracted from one local restriction mass. -/
def naturalRestrictionCountLaw
    {κ : Type u}
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (n : ℕ) (k : κ) : ProbabilityMeasure ℕ :=
  μ.map (nnrealNaturalPart ∘ localRestrictionMass sets n k)

/-- Re-encoding an almost surely natural-valued restriction count recovers its
`NNReal` local-mass law exactly. -/
theorem naturalRestrictionCountLaw_map_natCast
    {κ : Type u}
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (n : ℕ) (k : κ)
    (hnatural : ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      localRestrictionMass sets n k ν ∈
        Set.range ((↑) : ℕ → NNReal)) :
    (naturalRestrictionCountLaw μ sets n k).map
        ((↑) : ℕ → NNReal) =
      localRestrictionMassLaw μ sets n k := by
  apply Subtype.ext
  change Measure.map ((↑) : ℕ → NNReal)
      (Measure.map (nnrealNaturalPart ∘ localRestrictionMass sets n k) μ) =
    Measure.map (localRestrictionMass sets n k) μ
  rw [Measure.map_map]
  · apply Measure.map_congr
    filter_upwards [hnatural] with ν hν
    exact natCast_nnrealNaturalPart_eq hν
  · exact measurable_from_nat
  · exact measurable_nnrealNaturalPart.comp
      (measurable_localRestrictionMass sets hsets n k)

/-- The natural cast is a closed topological embedding into `NNReal`. -/
theorem isClosedEmbedding_natCast_nnreal :
    IsClosedEmbedding ((↑) : ℕ → NNReal) := by
  refine ⟨?_, isClosed_range_natCast_nnreal⟩
  apply NNReal.isClosedEmbedding_coe.isEmbedding.of_comp_iff.mp
  convert Nat.isClosedEmbedding_coe_real.isEmbedding using 1
  funext n
  exact NNReal.coe_natCast n

/-- Mapping probability laws along the natural cast is itself a topological
embedding.  Hence convergence of encoded laws reflects convergence of the
original discrete laws. -/
theorem isEmbedding_map_natCast_probabilityMeasure :
    IsEmbedding (fun μ : ProbabilityMeasure ℕ =>
      μ.map ((↑) : ℕ → NNReal)) := by
  have hfinite : IsEmbedding (fun μ : FiniteMeasure ℕ =>
      μ.map ((↑) : ℕ → NNReal)) :=
    FiniteMeasure.Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
      ((↑) : ℕ → NNReal) isClosedEmbedding_natCast_nnreal
  have hcomp : IsEmbedding (fun μ : ProbabilityMeasure ℕ =>
      (μ.map ((↑) : ℕ → NNReal)).toFiniteMeasure) := by
    convert hfinite.comp (ProbabilityMeasure.toFiniteMeasure_isEmbedding ℕ) using 1
    funext μ
    rfl
  exact (ProbabilityMeasure.toFiniteMeasure_isEmbedding NNReal).of_comp_iff.mp
    hcomp

/-- Weak convergence of `NNReal` encodings reflects weak convergence of the
underlying natural-valued laws. -/
theorem tendsto_of_tendsto_map_natCast
    {α : Type v} {L : Filter α}
    {μs : α → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (h : Tendsto (fun i => (μs i).map ((↑) : ℕ → NNReal)) L
      (𝓝 (μ.map ((↑) : ℕ → NNReal)))) :
    Tendsto μs L (𝓝 μ) := by
  exact isEmbedding_map_natCast_probabilityMeasure.tendsto_nhds_iff.mpr h

/-- Natural-valued local restriction mass laws converge as laws on
`ℕ`.  The proof combines exact re-encoding with the closed-embedding
reflection theorem, avoiding any false global continuity claim for the
decoder. -/
theorem tendsto_naturalRestrictionCountLaw
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} {α : Type v} {L : Filter α}
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    {sets : ℕ → κ → Set (MarkedSpectralSpace Unit)}
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (hmass : ∀ n k, Tendsto
      (fun i => localRestrictionMassLaw (μs i) sets n k) L
      (𝓝 (localRestrictionMassLaw μ sets n k)))
    (happrox : ∀ i n k,
      ∀ᵐ ν ∂(μs i : Measure VagueRationalWindowState),
        localRestrictionMass sets n k ν ∈
          Set.range ((↑) : ℕ → NNReal))
    (hlimit : ∀ n k,
      ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
        localRestrictionMass sets n k ν ∈
          Set.range ((↑) : ℕ → NNReal))
    (n : ℕ) (k : κ) :
    Tendsto (fun i => naturalRestrictionCountLaw (μs i) sets n k) L
      (𝓝 (naturalRestrictionCountLaw μ sets n k)) := by
  apply tendsto_of_tendsto_map_natCast
  simpa only [naturalRestrictionCountLaw_map_natCast _ sets hsets n k
      (happrox _ n k),
    naturalRestrictionCountLaw_map_natCast μ sets hsets n k (hlimit n k)]
    using hmass n k

/-- `NaturalRestrictionLawClosureInput` supplies convergence of its
natural-number count laws. -/
theorem NaturalRestrictionLawClosureInput.count_laws_tendsto
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u} {α : Type v} {L : Filter α} [NeBot L]
    {μs : α → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    {sets : ℕ → κ → Set (MarkedSpectralSpace Unit)}
    (input : NaturalRestrictionLawClosureInput L μs μ sets)
    (n : ℕ) (k : κ) :
    Tendsto (fun i => naturalRestrictionCountLaw (μs i) sets n k) L
      (𝓝 (naturalRestrictionCountLaw μ sets n k)) := by
  apply tendsto_naturalRestrictionCountLaw input.sets_measurable
    input.mass_laws_tendsto
  · intro i n k
    exact (input.approximants_natural i).mono fun ν hν => hν n k
  · intro n k
    exact input.limit_mass_natural_ae n k

/-- Exponential moments of an almost surely natural-valued `NNReal`
restriction mass are exactly the exponential moments of its decoded natural
count law: the natural number and its real cast have the same exponent. -/
theorem integral_exp_naturalRestrictionCountLaw
    {κ : Type u}
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (n : ℕ) (k : κ)
    (hnatural : ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      localRestrictionMass sets n k ν ∈
        Set.range ((↑) : ℕ → NNReal))
    (t : ℝ) :
    ∫ m : ℕ, Real.exp (t * m)
        ∂(naturalRestrictionCountLaw μ sets n k : Measure ℕ) =
      ∫ x : NNReal, Real.exp (t * (x : ℝ))
        ∂(localRestrictionMassLaw μ sets n k : Measure NNReal) := by
  rw [← naturalRestrictionCountLaw_map_natCast μ sets hsets n k hnatural]
  change (∫ m : ℕ, Real.exp (t * m)
      ∂(naturalRestrictionCountLaw μ sets n k : Measure ℕ)) =
    ∫ x : NNReal, Real.exp (t * (x : ℝ))
      ∂Measure.map ((↑) : ℕ → NNReal)
        (naturalRestrictionCountLaw μ sets n k : Measure ℕ)
  have hmeas : AEStronglyMeasurable
      (fun x : NNReal => Real.exp (t * (x : ℝ)))
      (Measure.map ((↑) : ℕ → NNReal)
        (naturalRestrictionCountLaw μ sets n k : Measure ℕ)) :=
    (Real.measurable_exp.comp
      (measurable_const.mul continuous_subtype_val.measurable)).aestronglyMeasurable
  rw [integral_map measurable_from_nat.aemeasurable hmeas]
  simp only [NNReal.coe_natCast]

/-- Integrability of the encoded `NNReal` exponential observable transports
back to the natural count law. -/
theorem integrable_exp_naturalRestrictionCountLaw
    {κ : Type u}
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → κ → Set (MarkedSpectralSpace Unit))
    (hsets : ∀ n k, MeasurableSet (sets n k))
    (n : ℕ) (k : κ)
    (hnatural : ∀ᵐ ν ∂(μ : Measure VagueRationalWindowState),
      localRestrictionMass sets n k ν ∈
        Set.range ((↑) : ℕ → NNReal))
    (t : ℝ)
    (hint : Integrable (fun x : NNReal => Real.exp (t * (x : ℝ)))
      (localRestrictionMassLaw μ sets n k : Measure NNReal)) :
    Integrable (fun m : ℕ => Real.exp (t * m))
      (naturalRestrictionCountLaw μ sets n k : Measure ℕ) := by
  rw [← naturalRestrictionCountLaw_map_natCast μ sets hsets n k hnatural] at hint
  exact (integrable_map_measure
    ((Real.measurable_exp.comp
      (measurable_const.mul continuous_subtype_val.measurable)).aestronglyMeasurable)
    measurable_from_nat.aemeasurable).mp hint

/-- A natural-valued restriction-law closure plus uniform exponential moments
of the `NNReal` mass laws gives the complete scalar Portmanteau input on
`ProbabilityMeasure ℕ`. -/
def NaturalRestrictionLawClosureInput.toIntegerCountWeakExponentialInput
    [OpensMeasurableSpace VagueRationalWindowState]
    {κ : Type u}
    {μs : ℕ → ProbabilityMeasure VagueRationalWindowState}
    {μ : ProbabilityMeasure VagueRationalWindowState}
    {sets : ℕ → κ → Set (MarkedSpectralSpace Unit)}
    (input : NaturalRestrictionLawClosureInput atTop μs μ sets)
    (n : ℕ) (k : κ) (t B : ℝ) (ht : 0 < t) (hB : 0 ≤ B)
    (hintegrable : ∀ i, Integrable
      (fun x : NNReal => Real.exp (t * (x : ℝ)))
      (localRestrictionMassLaw (μs i) sets n k : Measure NNReal))
    (hle : ∀ i,
      ∫ x : NNReal, Real.exp (t * (x : ℝ))
          ∂(localRestrictionMassLaw (μs i) sets n k : Measure NNReal) ≤ B) :
    IntegerCountWeakExponentialInput
      (fun i => naturalRestrictionCountLaw (μs i) sets n k)
      (naturalRestrictionCountLaw μ sets n k) where
  law_tendsto := input.count_laws_tendsto n k
  exponent := t
  exponent_pos := ht
  bound := B
  bound_nonneg := hB
  approximating_exp_integrable := fun i =>
    integrable_exp_naturalRestrictionCountLaw (μs i) sets
      input.sets_measurable n k
      ((input.approximants_natural i).mono fun ν hν => hν n k)
      t (hintegrable i)
  approximating_exp_le := fun i => by
    rw [integral_exp_naturalRestrictionCountLaw (μs i) sets
      input.sets_measurable n k
      ((input.approximants_natural i).mono fun ν hν => hν n k) t]
    exact hle i

/-- Paper-family constructor for translated interval families indexed by their
ordered endpoints.  The remaining assumptions are exactly the quantitative
finite-volume exponential estimate (`t`, `B`, integrability, and the bound);
weak convergence of the natural count laws is derived rather than supplied. -/
def NaturalRestrictionLawClosureInput.toPaperCountingWeakExponentialUIInput
    [OpensMeasurableSpace VagueRationalWindowState]
    (μs : ℕ → ProbabilityMeasure VagueRationalWindowState)
    (μ : ProbabilityMeasure VagueRationalWindowState)
    (sets : ℕ → (ℝ × ℝ) → Set (MarkedSpectralSpace Unit))
    (input : NaturalRestrictionLawClosureInput atTop μs μ sets)
    (t B : ℕ → ℝ → ℝ → ℝ)
    (ht : ∀ n a b, a < b → 0 < t n a b)
    (hB : ∀ n a b, a < b → 0 ≤ B n a b)
    (hintegrable : ∀ i n a b, a < b → Integrable
      (fun x : NNReal => Real.exp (t n a b * (x : ℝ)))
      (localRestrictionMassLaw (μs i) sets n (a, b) : Measure NNReal))
    (hle : ∀ i n a b, a < b →
      ∫ x : NNReal, Real.exp (t n a b * (x : ℝ))
          ∂(localRestrictionMassLaw (μs i) sets n (a, b) : Measure NNReal) ≤
        B n a b) :
    PaperCountingWeakExponentialUIInput
      (fun i n a b => naturalRestrictionCountLaw (μs i) sets n (a, b))
      (fun n a b => naturalRestrictionCountLaw μ sets n (a, b)) where
  weakExponential := fun n a b hab =>
    input.toIntegerCountWeakExponentialInput n (a, b)
      (t n a b) (B n a b) (ht n a b hab) (hB n a b hab)
      (fun i => hintegrable i n a b hab)
      (fun i => hle i n a b hab)

end CoareaNative.BlockBand
