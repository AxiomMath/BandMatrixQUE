module

public import BlockBand.Native.ErdosRiabov.BlockBand.Conventions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Nat

/-!
# Critical sequences, uniform constants, and critical-first endpoint contracts

The integer sequences use admissible dimensions `n ≥ 4`, `W ≥ 1`, real ratio
`n/W`, and `W → ∞`. The ratio may be zero: the QUE regime includes bounded `n`,
so divergence of `n` is deliberately not a structure field. Fixed variance, bulk
margins, energy, finite test families and quantitative parameters are passed in an
external `fixed` value, chosen before the uniform constant or asymptotic sequence.

`UniformEstimate` is a quantified inequality, not a statement that any model
satisfies it. Its expected-observable specialization integrates each deterministic
index separately; it does not put a supremum inside an expectation. Likewise the
endpoint contracts describe a critical family followed by a ratio limit. They
assert no diagonal or arbitrary simultaneous endpoint convergence. Probability-law
and marked-process topologies enter through the arbitrary target topology here; no
probability law or QUE theorem is constructed.

Stochastic domination is the convention `StochasticDominationConvention`; no closure laws
for it are proved here.
-/

@[expose] public section

namespace ERNative.BlockBand

open Filter Topology MeasureTheory

/-- An admissible integer sequence with
`W → ∞` and real `n/W → τ`. No rate, parity, subsequence, positive-`τ` premise,
or `n → ∞` premise is imposed. Positive finite critical-law theorems separately
require `0 < τ`; the same dimensions also represent the zero-ratio QUE regime. -/
structure CriticalSequence (τ : ℝ) where
  n : ℕ → ℕ
  W : ℕ → ℕ
  n_ge_four : ∀ j, 4 ≤ n j
  W_ge_one : ∀ j, 1 ≤ W j
  width_tendsto : Tendsto W atTop atTop
  ratio_tendsto : Tendsto (fun j => (n j : ℝ) / (W j : ℝ)) atTop (𝓝 τ)

namespace CriticalSequence

/-- The ratio is real division, not truncated division of naturals. -/
noncomputable def ratio {τ : ℝ} (s : CriticalSequence τ) (j : ℕ) : ℝ :=
  (s.n j : ℝ) / (s.W j : ℝ)

/-- Specialize a sequence to the finite `ModelParameters` at an index, with the same externally
fixed admissible variance `b`.
No Gaussian law is constructed.
-/
def parameters {τ : ℝ} (s : CriticalSequence τ) (b : ℝ)
    (hb : 0 < b) (hbhalf : b < 1 / 2) (j : ℕ) : Conventions.ModelParameters where
  n := s.n j
  W := s.W j
  b := b
  n_ge_four := s.n_ge_four j
  W_ge_one := s.W_ge_one j
  b_pos := hb
  b_lt_half := hbhalf

/-- A concrete zero-ratio sequence with the block count fixed at four.
This witnesses that `CriticalSequence 0` does not secretly force `n → ∞`. -/
noncomputable def boundedBlocks : CriticalSequence 0 where
  n := fun _ => 4
  W := fun j => j + 1
  n_ge_four := fun _ => le_rfl
  W_ge_one := fun j => Nat.le_add_left 1 j
  width_tendsto := tendsto_add_atTop_nat 1
  ratio_tendsto := by
    have hW : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.div_atTop hW

/-- The zero-ratio witness retains bounded block count at every index. -/
@[simp] theorem boundedBlocks_n (j : ℕ) : boundedBlocks.n j = 4 := rfl

end CriticalSequence

/-- One nonnegative real constant is chosen for each
already-fixed parameter package, before all admissible integer dimensions and all
stated deterministic indices. `scale` and `remainder` are separate so an exact
finite-size remainder need not be multiplied by the uniform constant. The predicate
contains neither a stochastic-loss power nor a model-specific estimate. -/
def UniformEstimate {κ : Type*} {ι : κ → ℕ → ℕ → Type*}
    (admissible : κ → ℕ → ℕ → Prop)
    (observable scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ) : Prop :=
  ∀ fixed : κ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n W : ℕ, admissible fixed n W →
    ∀ i : ι fixed n W, observable fixed n W i ≤ C * scale fixed n W i + remainder fixed n W i

/-- Unpack the constant after `fixed` but before dimensions/tests.
A constant depending on a deterministic index does not satisfy this conclusion. -/
theorem UniformEstimate.bound {κ : Type*} {ι : κ → ℕ → ℕ → Type*}
    {admissible : κ → ℕ → ℕ → Prop}
    {observable scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ}
    (h : UniformEstimate admissible observable scale remainder) (fixed : κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n W : ℕ, admissible fixed n W → ∀ i : ι fixed n W,
      observable fixed n W i ≤ C * scale fixed n W i + remainder fixed n W i := h fixed

/-- Restricting a uniform bound to an eventually admissible critical
sequence preserves one constant for every deterministic test along that sequence.
No convergence of the observable is asserted here. -/
theorem UniformEstimate.along {κ : Type*} {ι : κ → ℕ → ℕ → Type*}
    {admissible : κ → ℕ → ℕ → Prop}
    {observable scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ}
    (h : UniformEstimate admissible observable scale remainder)
    (fixed : κ) {τ : ℝ} (s : CriticalSequence τ)
    (hs : ∀ᶠ j in atTop, admissible fixed (s.n j) (s.W j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j in atTop, ∀ i : ι fixed (s.n j) (s.W j),
      observable fixed (s.n j) (s.W j) i ≤
        C * scale fixed (s.n j) (s.W j) i + remainder fixed (s.n j) (s.W j) i := by
  obtain ⟨C, hC, hbound⟩ := h fixed
  refine ⟨C, hC, ?_⟩
  filter_upwards [hs] with j hj
  exact hbound _ _ hj

/-- A uniform estimate of
expectations at separately fixed deterministic indices. Integrability is explicit,
so a default zero Bochner integral cannot impersonate an expected estimate. There
is no supremum of random test values inside the integral. Dimensions, laws and
observables may vary with the displayed finite parameters. -/
noncomputable def UniformExpectedEstimate {κ Ω : Type*} [MeasurableSpace Ω]
    {ι : κ → ℕ → ℕ → Type*} (admissible : κ → ℕ → ℕ → Prop)
    (μ : κ → ℕ → ℕ → ProbabilityMeasure Ω)
    (X : (fixed : κ) → (n W : ℕ) → ι fixed n W → Ω → ℝ)
    (scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ) : Prop :=
  (∀ fixed n W, admissible fixed n W → ∀ i, Integrable (X fixed n W i) (μ fixed n W)) ∧
    UniformEstimate admissible
      (fun fixed n W i => ∫ ω, X fixed n W i ω ∂(μ fixed n W)) scale remainder

/-- The same constant bounds each deterministic-index expectation;
the test index is quantified outside, and after, the choice of uniform constant. -/
theorem UniformExpectedEstimate.bound {κ Ω : Type*} [MeasurableSpace Ω]
    {ι : κ → ℕ → ℕ → Type*} {admissible : κ → ℕ → ℕ → Prop}
    {μ : κ → ℕ → ℕ → ProbabilityMeasure Ω}
    {X : (fixed : κ) → (n W : ℕ) → ι fixed n W → Ω → ℝ}
    {scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ}
    (h : UniformExpectedEstimate admissible μ X scale remainder) (fixed : κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n W, admissible fixed n W → ∀ i : ι fixed n W,
      (∫ ω, X fixed n W i ω ∂(μ fixed n W)) ≤
        C * scale fixed n W i + remainder fixed n W i := h.2 fixed

/-- The expected estimate's explicit integrability assumption is reusable
at each admissible finite model, independently of its inequality. -/
theorem UniformExpectedEstimate.integrable {κ Ω : Type*} [MeasurableSpace Ω]
    {ι : κ → ℕ → ℕ → Type*} {admissible : κ → ℕ → ℕ → Prop}
    {μ : κ → ℕ → ℕ → ProbabilityMeasure Ω}
    {X : (fixed : κ) → (n W : ℕ) → ι fixed n W → Ω → ℝ}
    {scale remainder : (fixed : κ) → (n W : ℕ) → ι fixed n W → ℝ}
    (h : UniformExpectedEstimate admissible μ X scale remainder)
    (fixed : κ) (n W : ℕ) (ha : admissible fixed n W) (i : ι fixed n W) :
    Integrable (X fixed n W i) (μ fixed n W) := h.1 fixed n W ha i

/-- One limit family is fixed before
quantifying over every admissible sequence at each positive finite ratio. This
contracts full-sequence convergence to a sequence-independent target, not merely
the existence of some subsequential limit. The target topology is an explicit
parameter, so a law-space topology is not confused with a sample-space topology. -/
def CriticalFamilyTendsto {κ X : Type*} [TopologicalSpace X]
    (finite : κ → ℕ → ℕ → X) (critical : κ → ℝ → X) : Prop :=
  ∀ fixed τ, 0 < τ → ∀ s : CriticalSequence τ,
    Tendsto (fun j => finite fixed (s.n j) (s.W j)) atTop (𝓝 (critical fixed τ))

/-- Specialize the sequence-independent family at already-fixed
parameters and ratio, without extracting or choosing a subsequence. -/
theorem CriticalFamilyTendsto.along {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X}
    (h : CriticalFamilyTendsto finite critical) (fixed : κ)
    {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) :
    Tendsto (fun j => finite fixed (s.n j) (s.W j)) atTop (𝓝 (critical fixed τ)) :=
  h fixed τ hτ s

/-- First establish
the positive finite-ratio critical family, then take `τ ↓ 0` within `τ > 0`.
This conjunction does not assert a simultaneous `W → ∞`, `n/W → 0` limit of the
finite family. Fixed parameters and finite test families belong in `κ`. -/
def CriticalThenSmallRatio {κ X : Type*} [TopologicalSpace X]
    (finite : κ → ℕ → ℕ → X) (critical : κ → ℝ → X) (endpoint : κ → X) : Prop :=
  CriticalFamilyTendsto finite critical ∧
    ∀ fixed, Tendsto (critical fixed) (𝓝[Set.Ioi 0] 0) (𝓝 (endpoint fixed))

/-- The large-ratio endpoint also follows the already
constructed critical family. Its outer real-parameter filter is `atTop`, not the
integer width filter of any particular finite model. No joint endpoint limit is added. -/
def CriticalThenLargeRatio {κ X : Type*} [TopologicalSpace X]
    (finite : κ → ℕ → ℕ → X) (critical : κ → ℝ → X) (endpoint : κ → X) : Prop :=
  CriticalFamilyTendsto finite critical ∧
    ∀ fixed, Tendsto (critical fixed) atTop (𝓝 (endpoint fixed))

/-- Extract only the outer small-ratio
limit after the critical family, retaining the right-sided domain. -/
theorem CriticalThenSmallRatio.outer {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X} {endpoint : κ → X}
    (h : CriticalThenSmallRatio finite critical endpoint) (fixed : κ) :
    Tendsto (critical fixed) (𝓝[Set.Ioi 0] 0) (𝓝 (endpoint fixed)) := h.2 fixed

/-- Extract only the outer large-ratio critical-law limit. -/
theorem CriticalThenLargeRatio.outer {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℕ → ℕ → X} {critical : κ → ℝ → X} {endpoint : κ → X}
    (h : CriticalThenLargeRatio finite critical endpoint) (fixed : κ) :
    Tendsto (critical fixed) atTop (𝓝 (endpoint fixed)) := h.2 fixed

/-- An inner limit at each fixed outer parameter, followed by the
outer limit. The intermediate family is explicit. This contract deliberately
provides no convergence along a diagonal with varying outer parameter. -/
def IteratedLimit {A B X : Type*} [TopologicalSpace X]
    (inner : Filter A) (outer : Filter B)
    (finite : B → A → X) (middle : B → X) (target : X) : Prop :=
  (∀ b, Tendsto (finite b) inner (𝓝 (middle b))) ∧ Tendsto middle outer (𝓝 target)

/-- Post-critical regularizations: extract the inner limit while holding its
outer parameter fixed; no uniformity in the outer parameter is inserted. -/
theorem IteratedLimit.inner {A B X : Type*} [TopologicalSpace X]
    {l : Filter A} {m : Filter B} {finite : B → A → X} {middle : B → X} {target : X}
    (h : IteratedLimit l m finite middle target) (b : B) :
    Tendsto (finite b) l (𝓝 (middle b)) := h.1 b

/-- Post-critical regularizations: the outer limit applies to the intermediate
family, not the original finite model along a moving parameter. -/
theorem IteratedLimit.outer {A B X : Type*} [TopologicalSpace X]
    {l : Filter A} {m : Filter B} {finite : B → A → X} {middle : B → X} {target : X}
    (h : IteratedLimit l m finite middle target) : Tendsto middle m (𝓝 target) := h.2

/-- At fixed finite family size
`p`, all smoothing heights are positive and fixed before the integer critical
limit. Afterwards they approach zero from above. Different coordinates may
approach zero at different rates; no smoothing-width diagonal is claimed. -/
def CriticalThenUnsmoothing {κ X : Type*} [TopologicalSpace X] (p : ℕ)
    (finite : κ → (Fin p → ℝ) → ℕ → ℕ → X)
    (smoothed : κ → (Fin p → ℝ) → ℝ → X) (unsmoothed : κ → ℝ → X) : Prop :=
  (∀ fixed δ, (∀ i, 0 < δ i) → ∀ τ, 0 < τ → ∀ s : CriticalSequence τ,
    Tendsto (fun j => finite fixed δ (s.n j) (s.W j)) atTop (𝓝 (smoothed fixed δ τ))) ∧
  ∀ fixed τ, 0 < τ → Tendsto (fun δ => smoothed fixed δ τ)
    (𝓝[ {δ : Fin p → ℝ | ∀ i, 0 < δ i} ] (fun _ => 0)) (𝓝 (unsmoothed fixed τ))

/-- Specialize the critical limit at an already-fixed
finite smoothing family, preserving positivity and the fixed order `p`. -/
theorem CriticalThenUnsmoothing.inner {κ X : Type*} [TopologicalSpace X] {p : ℕ}
    {finite : κ → (Fin p → ℝ) → ℕ → ℕ → X}
    {smoothed : κ → (Fin p → ℝ) → ℝ → X} {unsmoothed : κ → ℝ → X}
    (h : CriticalThenUnsmoothing p finite smoothed unsmoothed)
    (fixed : κ) (δ : Fin p → ℝ) (hδ : ∀ i, 0 < δ i)
    {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) :
    Tendsto (fun j => finite fixed δ (s.n j) (s.W j)) atTop (𝓝 (smoothed fixed δ τ)) :=
  h.1 fixed δ hδ τ hτ s

/-- After the critical family, remove the smoothing;
this only acts on the limiting family, never on a moving finite-width observable. -/
theorem CriticalThenUnsmoothing.outer {κ X : Type*} [TopologicalSpace X] {p : ℕ}
    {finite : κ → (Fin p → ℝ) → ℕ → ℕ → X}
    {smoothed : κ → (Fin p → ℝ) → ℝ → X} {unsmoothed : κ → ℝ → X}
    (h : CriticalThenUnsmoothing p finite smoothed unsmoothed) (fixed : κ)
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun δ => smoothed fixed δ τ)
      (𝓝[ {δ : Fin p → ℝ | ∀ i, 0 < δ i} ] (fun _ => 0)) (𝓝 (unsmoothed fixed τ)) :=
  h.2 fixed τ hτ

/-- Critical limsup-error passages: every tolerance is fixed first; an
outer cutoff/smoothing parameter is then eventually good. At each such fixed
outer parameter, one sufficiently late index works for all deterministic tests.
The late index is allowed to depend on the outer parameter, so no diagonal bound
is implied. This avoids totalized `limsup` values when boundedness is unproved. -/
def UniformIteratedError {B ι : Type*} (outer : Filter B) (error : B → ℕ → ι → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ b in outer,
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, |error b j i| ≤ η

/-- Small-channel leakage and regularization errors: unpack one tolerance
without exchanging the outer parameter and its inner asymptotic cutoff. -/
theorem UniformIteratedError.bound {B ι : Type*} {outer : Filter B}
    {error : B → ℕ → ι → ℝ} (h : UniformIteratedError outer error)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ b in outer,
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ i, |error b j i| ≤ η := h η hη

/-- Fix positive absorption
`δ`, take the critical integer limit at each fixed positive finite `τ`, then
`τ → ∞`, and only then `δ ↓ 0`. Partitions and collar choices belong in the
already-fixed finite-model data. This three-stage contract has no diagonal conclusion. -/
def CriticalThenLargeThenUnsmoothing {κ X : Type*} [TopologicalSpace X]
    (finite : κ → ℝ → ℕ → ℕ → X) (critical : κ → ℝ → ℝ → X)
    (large : κ → ℝ → X) (target : κ → X) : Prop :=
  (∀ fixed δ, 0 < δ → ∀ τ, 0 < τ → ∀ s : CriticalSequence τ,
    Tendsto (fun j => finite fixed δ (s.n j) (s.W j)) atTop (𝓝 (critical fixed δ τ))) ∧
  (∀ fixed δ, 0 < δ → Tendsto (critical fixed δ) atTop (𝓝 (large fixed δ))) ∧
  ∀ fixed, Tendsto (large fixed) (𝓝[Set.Ioi 0] 0) (𝓝 (target fixed))

/-- Extract the final unsmoothing step, acting only
on the post-critical, post-large-ratio family. -/
theorem CriticalThenLargeThenUnsmoothing.outer {κ X : Type*} [TopologicalSpace X]
    {finite : κ → ℝ → ℕ → ℕ → X} {critical : κ → ℝ → ℝ → X}
    {large : κ → ℝ → X} {target : κ → X}
    (h : CriticalThenLargeThenUnsmoothing finite critical large target) (fixed : κ) :
    Tendsto (large fixed) (𝓝[Set.Ioi 0] 0) (𝓝 (target fixed)) := h.2.2 fixed

end ERNative.BlockBand
