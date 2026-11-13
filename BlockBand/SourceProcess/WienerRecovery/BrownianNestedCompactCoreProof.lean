module

public import BlockBand.SourceProcess.WienerRecovery.BrownianCylinderTightnessClosure

/-!
# Compact-core criteria for continuity at the empty set of the Brownian cylinder content

Three compact-core conditions on decreasing sequences of Brownian cylinders whose contents
stay above a positive threshold `r`; each implies `BrownianCylinderContinuityAtEmpty`.

* `BrownianCylinderPositiveNestedCompactCore`: nested nonempty compact cores. It is
  equivalent to continuity at the empty set
  (`brownianCylinderContinuityAtEmpty_of_positiveNestedCompactCore`,
  `positiveNestedCompactCore_of_brownianCylinderContinuityAtEmpty`).
* `BrownianCylinderQuantitativeCompactCore`: finite-dimensional compact cores in one
  coordinate box, with marginal losses `ε n` of total less than `r`.
* `BrownianCylinderOnceChargedCompactCore`: one global coordinate-box loss `β` and
  summable inside-box losses `δ n`, with `β + Σ δ n < r`.

Product compactness and Cantor's intersection theorem turn these data into continuity at
the empty set. No projective-limit measure and no nonemptiness of the lifted cores is
assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH
namespace BrownianNestedCompactCoreProof

open scoped NNReal Topology ENNReal
open Filter Set MeasureTheory ProbabilityTheory
open ScalarWienerRealizationClosure
open ScalarWienerMeasureConstruction
open BrownianCylinderTightnessClosure

/-- Nested nonempty compact cores inside every decreasing sequence of Brownian cylinders
whose contents stay above a positive threshold. -/
def BrownianCylinderPositiveNestedCompactCore : Prop :=
  ∀ (A : ℕ → Set BrownianRawPath),
    (∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ)) →
    Antitone A →
    ∀ r : ℝ≥0∞, 0 < r → (∀ n, r < brownianCylinderContent (A n)) →
      ∃ K : ℕ → Set BrownianRawPath,
        (∀ n, K n ⊆ A n) ∧
        (∀ n, K (n + 1) ⊆ K n) ∧
        (∀ n, (K n).Nonempty) ∧
        IsCompact (K 0) ∧
        (∀ n, IsClosed (K n))

/-- `BrownianCylinderPositiveNestedCompactCore` implies continuity at the empty set. -/
theorem brownianCylinderContinuityAtEmpty_of_positiveNestedCompactCore
    (hcore : BrownianCylinderPositiveNestedCompactCore) :
    BrownianCylinderContinuityAtEmpty := by
  intro A hAcyl hAanti hAempty
  have hcontent : Antitone (fun n => brownianCylinderContent (A n)) := by
    intro n m hnm
    exact addContent_mono isSetSemiring_measurableCylinders
      (hAcyl m) (hAcyl n) (hAanti hnm)
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hcontent]
  intro ε hε
  by_contra h
  push Not at h
  rcases hcore A hAcyl hAanti ε hε h with
    ⟨K, hKA, hKanti, hKnonempty, hKcompact, hKclosed⟩
  have hKi : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hKanti hKnonempty hKcompact hKclosed
  rcases hKi with ⟨ω, hω⟩
  have hωA : ω ∈ ⋂ n, A n := by
    simp only [mem_iInter] at hω ⊢
    intro n
    exact hKA n (hω n)
  rw [hAempty] at hωA
  exact hωA

/-- Conversely, continuity at the empty set gives
`BrownianCylinderPositiveNestedCompactCore`: choose one point of the nonempty total
intersection and use singleton cores. -/
theorem positiveNestedCompactCore_of_brownianCylinderContinuityAtEmpty
    (hcont : BrownianCylinderContinuityAtEmpty) :
    BrownianCylinderPositiveNestedCompactCore := by
  intro A hAcyl hAanti r hr hlower
  have hInter : (⋂ n, A n).Nonempty := by
    by_contra h
    have hEmpty : (⋂ n, A n) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hcontent : Antitone (fun n => brownianCylinderContent (A n)) := by
      intro n m hnm
      exact addContent_mono isSetSemiring_measurableCylinders
        (hAcyl m) (hAcyl n) (hAanti hnm)
    have hzero := hcont A hAcyl hAanti hEmpty
    rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hcontent] at hzero
    rcases hzero r hr with ⟨n, hn⟩
    exact (not_lt_of_ge hn) (hlower n)
  rcases hInter with ⟨ω, hω⟩
  have hω' : ∀ n, ω ∈ A n := by
    simpa only [Set.mem_iInter] using hω
  refine ⟨fun _ => {ω}, ?_, ?_, ?_, isCompact_singleton, ?_⟩
  · intro n x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hω' n
  · intro n
    exact Set.Subset.rfl
  · intro n
    exact Set.singleton_nonempty ω
  · intro n
    exact isClosed_singleton

/-- Coordinatewise compact box in the unrestricted Brownian path product. -/
def coordinateCompactBox (q : NNReal → Set ℝ) : Set BrownianRawPath :=
  Set.pi Set.univ q

/-- Tychonoff compactness of a coordinatewise compact Brownian path box. -/
theorem isCompact_coordinateCompactBox {q : NNReal → Set ℝ}
    (hq : ∀ t, IsCompact (q t)) :
    IsCompact (coordinateCompactBox q) := by
  simpa [coordinateCompactBox, Set.pi] using isCompact_pi_infinite hq

/-- A lifted compact finite-coordinate core is closed in the raw path product. -/
theorem isClosed_cylinder_of_isCompact
    (I : Finset NNReal) {C : Set (I → ℝ)} (hC : IsCompact C) :
    IsClosed (cylinder I C : Set BrownianRawPath) := by
  rw [show cylinder I C =
      (fun ω : BrownianRawPath => fun i : I => ω i) ⁻¹' C by rfl]
  exact hC.isClosed.preimage I.continuous_restrict

/-- Replace coordinates outside their prescribed compact fibers by fixed
chosen points.  On coordinates already in the compact box this operation is
the identity. -/
def compactifyIntoBox (q : NNReal → Set ℝ) (hq : ∀ t, (q t).Nonempty)
    (ω : BrownianRawPath) : BrownianRawPath := by
  classical
  exact fun t => if h : ω t ∈ q t then ω t else Classical.choose (hq t)

/-- Compactification always lands in the prescribed coordinatewise box. -/
theorem compactifyIntoBox_mem (q : NNReal → Set ℝ) (hq : ∀ t, (q t).Nonempty)
    (ω : BrownianRawPath) : compactifyIntoBox q hq ω ∈ coordinateCompactBox q := by
  intro t ht
  simp only [compactifyIntoBox]
  split_ifs with h
  · exact h
  · exact Classical.choose_spec (hq t)

/-- Compactification does not change a coordinate already in its compact fiber. -/
theorem compactifyIntoBox_apply_of_mem (q : NNReal → Set ℝ)
    (hq : ∀ t, (q t).Nonempty) (ω : BrownianRawPath) {t : NNReal}
    (ht : ω t ∈ q t) : compactifyIntoBox q hq ω t = ω t := by
  simp [compactifyIntoBox, ht]

/-- The cumulative lift of the first `n+1` finite-dimensional compact cores. -/
def cumulativeLiftedCore
    (I : ℕ → Finset NNReal) (C : ∀ n, Set (I n → ℝ)) (n : ℕ) :
    Set BrownianRawPath :=
  ⋂ j ∈ Finset.range (n + 1), cylinder (I j) (C j)

/-- Finite-stage compact-containment data that charges the marginal core loss at every
stage: for every decreasing cylinder sequence with common positive lower mass `r`, finite
supports `I n`, measurable bases `S n` and compact cores `C n` in one coordinatewise
compact box, with marginal losses `ε n` of total less than `r`. If the box has positive
tail mass, that loss enters every `ε n`; `BrownianCylinderOnceChargedCompactCore` charges
it once. -/
def BrownianCylinderQuantitativeCompactCore : Prop :=
  ∀ (A : ℕ → Set BrownianRawPath),
    (∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ)) →
    Antitone A →
    ∀ r : ℝ≥0∞, 0 < r → (∀ n, r < brownianCylinderContent (A n)) →
      ∃ (I : ℕ → Finset NNReal) (S C : ∀ n, Set (I n → ℝ))
          (q : NNReal → Set ℝ) (ε : ℕ → ℝ≥0∞),
        (∑' n, ε n) < r ∧
        (∀ n, MeasurableSet (S n)) ∧
        (∀ n, A n = cylinder (I n) (S n)) ∧
        (∀ n, C n ⊆ S n) ∧
        (∀ n, IsCompact (C n)) ∧
        (∀ n, BrownianReal.projectiveFamily (I n) (S n \ C n) ≤ ε n) ∧
        (∀ t, IsCompact (q t)) ∧
        (∀ t, (q t).Nonempty) ∧
        (∀ n x, x ∈ C n → ∀ i : I n, x i ∈ q i)

/-- The coordinate box induced on one finite cylinder support. -/
def finiteCoordinateCompactBox (q : NNReal → Set ℝ) (I : Finset NNReal) :
    Set (I → ℝ) :=
  Set.pi Set.univ fun i => q i

/-- The cumulative lift of the coordinate-box constraints through stage
`n`.  Its complement is the one global loss charged in
`BrownianCylinderOnceChargedCompactCore`. -/
def cumulativeLiftedBox
    (I : ℕ → Finset NNReal) (q : NNReal → Set ℝ) (n : ℕ) :
    Set BrownianRawPath :=
  ⋂ j ∈ Finset.range (n + 1), cylinder (I j) (finiteCoordinateCompactBox q (I j))

/-- Once-charged finite-stage compact-containment data.

For a decreasing cylinder sequence with common positive lower mass `r`, `β`
controls escape from one coordinatewise compact box through every finite
cumulative support.  This is a *single global loss*: it occurs once, rather
than once per stage.  Inside that box, `C n` is a compact subset of the
measurable cylinder base and has additional loss at most `δ n`; these
additional losses have total strictly below `r - β`.

The subsequent finite union bound is therefore `β + ∑ j ≤ n, δ j`.  No
nonemptiness or compatibility of lifted cores is assumed. -/
def BrownianCylinderOnceChargedCompactCore : Prop :=
  ∀ (A : ℕ → Set BrownianRawPath),
    (∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ)) →
    Antitone A →
    ∀ r : ℝ≥0∞, 0 < r → (∀ n, r < brownianCylinderContent (A n)) →
      ∃ (I : ℕ → Finset NNReal) (S C : ∀ n, Set (I n → ℝ))
          (q : NNReal → Set ℝ) (β : ℝ≥0∞) (δ : ℕ → ℝ≥0∞),
        β < r ∧
        (∑' n, δ n) < r - β ∧
        (∀ n, MeasurableSet (S n)) ∧
        (∀ n, A n = cylinder (I n) (S n)) ∧
        (∀ n, C n ⊆ S n ∩ finiteCoordinateCompactBox q (I n)) ∧
        (∀ n, IsCompact (C n)) ∧
        (∀ n, BrownianReal.projectiveFamily (I n)
          ((S n ∩ finiteCoordinateCompactBox q (I n)) \ C n) ≤ δ n) ∧
        (∀ t, IsCompact (q t)) ∧
        (∀ t, (q t).Nonempty) ∧
        (∀ n, brownianCylinderContent
          (A n \ cumulativeLiftedBox I q n) ≤ β)

/-- The content lost by replacing a measurable cylinder base by one of its
compact subsets is exactly the corresponding finite-dimensional marginal loss. -/
theorem brownianCylinderContent_sdiff_compactCore
    {A : Set BrownianRawPath} (I : Finset NNReal) {S C : Set (I → ℝ)}
    (hS : MeasurableSet S) (hC : IsCompact C) (hA : A = cylinder I S) :
    brownianCylinderContent (A \ cylinder I C) =
      BrownianReal.projectiveFamily I (S \ C) := by
  have hSC : MeasurableSet (S \ C) := hS.diff hC.isClosed.measurableSet
  rw [hA]
  have heq : cylinder I S \ cylinder I C =
      (cylinder I (S \ C) : Set BrownianRawPath) := by
    ext ω
    rfl
  rw [heq]
  exact brownianCylinderContent_cylinder I (S \ C) hSC

/-- The individual marginal core-loss estimates imply the cumulative finite
union bound.  This is an ordinary finite-subadditivity argument in the cylinder
set ring, not an additional compactness or nonemptiness assumption. -/
theorem brownianCylinderContent_sdiff_cumulativeLiftedCore_le
    {A : ℕ → Set BrownianRawPath}
    (hAcyl : ∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ))
    (hAanti : Antitone A)
    {I : ℕ → Finset NNReal} {S C : ∀ n, Set (I n → ℝ)}
    {ε : ℕ → ℝ≥0∞}
    (hSmeas : ∀ n, MeasurableSet (S n))
    (hArep : ∀ n, A n = cylinder (I n) (S n))
    (hCcompact : ∀ n, IsCompact (C n))
    (hmarginalLoss : ∀ n,
      BrownianReal.projectiveFamily (I n) (S n \ C n) ≤ ε n)
    (n : ℕ) :
    brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
      ∑ j ∈ Finset.range (n + 1), ε j := by
  let E : ℕ → Set BrownianRawPath := fun j => A j \ cylinder (I j) (C j)
  have hcoreCyl : ∀ j, cylinder (I j) (C j) ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    intro j
    apply cylinder_mem_measurableCylinders
    exact (hCcompact j).isClosed.measurableSet
  have hEmem : ∀ j, E j ∈ measurableCylinders (fun _ : NNReal => ℝ) := by
    intro j
    exact isSetRing_measurableCylinders.sdiff_mem (hAcyl j) (hcoreCyl j)
  have hDmem : cumulativeLiftedCore I C n ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    apply isSetRing_measurableCylinders.biInter_mem (Finset.range (n + 1))
    · exact ⟨0, by simp⟩
    · intro j hj
      exact hcoreCyl j
  have hdiffmem : A n \ cumulativeLiftedCore I C n ∈
      measurableCylinders (fun _ : NNReal => ℝ) :=
    isSetRing_measurableCylinders.sdiff_mem (hAcyl n) hDmem
  have hsubset : A n \ cumulativeLiftedCore I C n ⊆
      ⋃ j ∈ Finset.range (n + 1), E j := by
    intro ω hω
    simp only [cumulativeLiftedCore, Set.mem_sdiff, Set.mem_iInter,
      not_forall] at hω
    rcases hω.2 with ⟨j, hj⟩
    rcases hj with ⟨hjrange, hjcore⟩
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjrange, ?_⟩⟩
    exact ⟨hAanti (Nat.le_of_lt_succ (Finset.mem_range.mp hjrange)) hω.1, hjcore⟩
  calc
    brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
        brownianCylinderContent (⋃ j ∈ Finset.range (n + 1), E j) :=
      addContent_mono isSetSemiring_measurableCylinders hdiffmem
        (isSetRing_measurableCylinders.biUnion_mem _ fun j _ => hEmem j) hsubset
    _ ≤ ∑ j ∈ Finset.range (n + 1), brownianCylinderContent (E j) :=
      addContent_biUnion_le isSetRing_measurableCylinders
        (fun j _ => hEmem j)
    _ ≤ ∑ j ∈ Finset.range (n + 1), ε j := by
      gcongr with j hj
      exact (brownianCylinderContent_sdiff_compactCore (I j)
        (hSmeas j) (hCcompact j) (hArep j)).le.trans (hmarginalLoss j)

/-- The cumulative union bound charges the coordinate-box escape
only once, then adds the stagewise inside-box losses. -/
theorem brownianCylinderContent_sdiff_cumulativeLiftedCore_le_onceCharged
    {A : ℕ → Set BrownianRawPath}
    (hAcyl : ∀ n, A n ∈ measurableCylinders (fun _ : NNReal => ℝ))
    (hAanti : Antitone A)
    {I : ℕ → Finset NNReal} {S C : ∀ n, Set (I n → ℝ)}
    {q : NNReal → Set ℝ} {β : ℝ≥0∞} {δ : ℕ → ℝ≥0∞}
    (hSmeas : ∀ n, MeasurableSet (S n))
    (hArep : ∀ n, A n = cylinder (I n) (S n))
    (hCcompact : ∀ n, IsCompact (C n))
    (hqcompact : ∀ t, IsCompact (q t))
    (hinsideLoss : ∀ n, BrownianReal.projectiveFamily (I n)
      ((S n ∩ finiteCoordinateCompactBox q (I n)) \ C n) ≤ δ n)
    (hboxLoss : ∀ n, brownianCylinderContent
      (A n \ cumulativeLiftedBox I q n) ≤ β)
    (n : ℕ) :
    brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
      β + ∑ j ∈ Finset.range (n + 1), δ j := by
  let Q : ℕ → Set BrownianRawPath := fun j =>
    cylinder (I j) (finiteCoordinateCompactBox q (I j))
  let G : Set BrownianRawPath := A n \ cumulativeLiftedBox I q n
  let E : ℕ → Set BrownianRawPath := fun j =>
    (A j ∩ Q j) \ cylinder (I j) (C j)
  have hQcompact : ∀ j, IsCompact (finiteCoordinateCompactBox q (I j)) := by
    intro j
    simpa [finiteCoordinateCompactBox, Set.pi] using
      (isCompact_pi_infinite fun i : I j => hqcompact i)
  have hQcyl : ∀ j, Q j ∈ measurableCylinders (fun _ : NNReal => ℝ) := by
    intro j
    apply cylinder_mem_measurableCylinders
    exact (hQcompact j).isClosed.measurableSet
  have hcoreCyl : ∀ j, cylinder (I j) (C j) ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    intro j
    apply cylinder_mem_measurableCylinders
    exact (hCcompact j).isClosed.measurableSet
  have hboxCyl : cumulativeLiftedBox I q n ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    apply isSetRing_measurableCylinders.biInter_mem (Finset.range (n + 1))
    · exact ⟨0, by simp⟩
    · intro j hj
      exact hQcyl j
  have hGmem : G ∈ measurableCylinders (fun _ : NNReal => ℝ) :=
    isSetRing_measurableCylinders.sdiff_mem (hAcyl n) hboxCyl
  have hEmem : ∀ j, E j ∈ measurableCylinders (fun _ : NNReal => ℝ) := by
    intro j
    exact isSetRing_measurableCylinders.sdiff_mem
      (isSetRing_measurableCylinders.inter_mem (hAcyl j) (hQcyl j))
      (hcoreCyl j)
  have hDmem : cumulativeLiftedCore I C n ∈
      measurableCylinders (fun _ : NNReal => ℝ) := by
    apply isSetRing_measurableCylinders.biInter_mem (Finset.range (n + 1))
    · exact ⟨0, by simp⟩
    · intro j hj
      exact hcoreCyl j
  have hdiffmem : A n \ cumulativeLiftedCore I C n ∈
      measurableCylinders (fun _ : NNReal => ℝ) :=
    isSetRing_measurableCylinders.sdiff_mem (hAcyl n) hDmem
  have hsubset : A n \ cumulativeLiftedCore I C n ⊆
      G ∪ ⋃ j ∈ Finset.range (n + 1), E j := by
    intro ω hω
    by_cases hωbox : ω ∈ cumulativeLiftedBox I q n
    · right
      simp only [cumulativeLiftedCore, Set.mem_sdiff, Set.mem_iInter,
        not_forall] at hω
      rcases hω.2 with ⟨j, hjrange, hjcore⟩
      refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjrange, ?_⟩⟩
      refine ⟨⟨hAanti (Nat.le_of_lt_succ (Finset.mem_range.mp hjrange)) hω.1,
        ?_⟩, hjcore⟩
      simp only [cumulativeLiftedBox, Set.mem_iInter] at hωbox
      exact hωbox j hjrange
    · left
      exact ⟨hω.1, hωbox⟩
  have hUmem : (⋃ j ∈ Finset.range (n + 1), E j) ∈
      measurableCylinders (fun _ : NNReal => ℝ) :=
    isSetRing_measurableCylinders.biUnion_mem _ fun j _ => hEmem j
  calc
    brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
        brownianCylinderContent
          (G ∪ ⋃ j ∈ Finset.range (n + 1), E j) :=
      addContent_mono isSetSemiring_measurableCylinders hdiffmem
        (isSetRing_measurableCylinders.union_mem hGmem hUmem) hsubset
    _ ≤ brownianCylinderContent G +
        brownianCylinderContent (⋃ j ∈ Finset.range (n + 1), E j) :=
      addContent_union_le isSetRing_measurableCylinders hGmem hUmem
    _ ≤ β + ∑ j ∈ Finset.range (n + 1),
        brownianCylinderContent (E j) := by
      exact add_le_add (hboxLoss n)
        (addContent_biUnion_le isSetRing_measurableCylinders
          (fun j _ => hEmem j))
    _ ≤ β + ∑ j ∈ Finset.range (n + 1), δ j := by
      gcongr with j hj
      have hAjQ : A j ∩ Q j =
          cylinder (I j) (S j ∩ finiteCoordinateCompactBox q (I j)) := by
        rw [hArep j]
        rfl
      exact (brownianCylinderContent_sdiff_compactCore (I j)
        ((hSmeas j).inter (hQcompact j).isClosed.measurableSet)
        (hCcompact j) hAjQ).le.trans (hinsideLoss j)

/-- Every cumulative finite intersection of the quantitative compact cores
is nonempty.  This is derived, rather than assumed: emptiness would make the
whole mass of `A n` part of the discarded mass, contradicting the common lower
bound and the partial-sum bound. -/
theorem cumulativeLiftedCore_nonempty_of_loss
    {A : ℕ → Set BrownianRawPath} {r : ℝ≥0∞}
    (hlower : ∀ n, r < brownianCylinderContent (A n))
    {I : ℕ → Finset NNReal} {C : ∀ n, Set (I n → ℝ)} {ε : ℕ → ℝ≥0∞}
    (hεsum : (∑' n, ε n) < r)
    (hloss : ∀ n, brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
      ∑ j ∈ Finset.range (n + 1), ε j) (n : ℕ) :
    (cumulativeLiftedCore I C n).Nonempty := by
  by_contra h
  have hempty : cumulativeLiftedCore I C n = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hpartial : (∑ j ∈ Finset.range (n + 1), ε j) ≤ ∑' j, ε j := by
    exact ENNReal.sum_le_tsum (Finset.range (n + 1))
  have hle : brownianCylinderContent (A n) ≤ ∑' j, ε j := by
    calc
      brownianCylinderContent (A n) =
          brownianCylinderContent (A n \ cumulativeLiftedCore I C n) := by
            rw [hempty, Set.sdiff_empty]
      _ ≤ ∑ j ∈ Finset.range (n + 1), ε j := hloss n
      _ ≤ ∑' j, ε j := hpartial
  exact (not_lt_of_ge hle) (hεsum.trans (hlower n))

/-- Nonemptiness from the once-charged budget: the coordinate-box loss occurs
once, and the partial inside-box sum is bounded by the remaining budget
`r - β`. -/
theorem cumulativeLiftedCore_nonempty_of_onceChargedLoss
    {A : ℕ → Set BrownianRawPath} {r β : ℝ≥0∞}
    (hlower : ∀ n, r < brownianCylinderContent (A n))
    {I : ℕ → Finset NNReal} {C : ∀ n, Set (I n → ℝ)} {δ : ℕ → ℝ≥0∞}
    (hβ : β < r)
    (hδsum : (∑' n, δ n) < r - β)
    (hloss : ∀ n, brownianCylinderContent
      (A n \ cumulativeLiftedCore I C n) ≤
        β + ∑ j ∈ Finset.range (n + 1), δ j)
    (n : ℕ) :
    (cumulativeLiftedCore I C n).Nonempty := by
  have hβtop : β ≠ ∞ :=
    (lt_top_iff_ne_top.mp (hβ.trans_le le_top))
  have hbudget : β + ∑' j, δ j < r := by
    calc
      β + ∑' j, δ j < β + (r - β) :=
        ENNReal.add_lt_add_left hβtop hδsum
      _ = r := add_tsub_cancel_of_le (le_of_lt hβ)
  by_contra h
  have hempty : cumulativeLiftedCore I C n = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp h
  have hpartial : (∑ j ∈ Finset.range (n + 1), δ j) ≤ ∑' j, δ j :=
    ENNReal.sum_le_tsum (Finset.range (n + 1))
  have hle : brownianCylinderContent (A n) ≤ β + ∑' j, δ j := by
    calc
      brownianCylinderContent (A n) =
          brownianCylinderContent (A n \ cumulativeLiftedCore I C n) := by
            rw [hempty, Set.sdiff_empty]
      _ ≤ β + ∑ j ∈ Finset.range (n + 1), δ j := hloss n
      _ ≤ β + ∑' j, δ j := by
        simpa [add_comm] using add_le_add_left hpartial β
  exact (not_lt_of_ge hle) (hbudget.trans (hlower n))

/-- `BrownianCylinderQuantitativeCompactCore` implies continuity at the empty set. -/
theorem brownianCylinderContinuityAtEmpty_of_quantitativeCompactCore
    (hcore : BrownianCylinderQuantitativeCompactCore) :
    BrownianCylinderContinuityAtEmpty := by
  intro A hAcyl hAanti hAempty
  have hcontent : Antitone (fun n => brownianCylinderContent (A n)) := by
    intro n m hnm
    exact addContent_mono isSetSemiring_measurableCylinders
      (hAcyl m) (hAcyl n) (hAanti hnm)
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hcontent]
  intro r hr
  by_contra h
  push Not at h
  rcases hcore A hAcyl hAanti r hr h with
    ⟨I, S, C, q, ε, hεsum, hSmeas, hArep, hCS, hCcompact,
      hmarginalLoss, hqcompact, hqnonempty, hCq⟩
  have hcumulativeLoss : ∀ n,
      brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
        ∑ j ∈ Finset.range (n + 1), ε j :=
    brownianCylinderContent_sdiff_cumulativeLiftedCore_le
      hAcyl hAanti hSmeas hArep hCcompact hmarginalLoss
  let K : ℕ → Set BrownianRawPath := fun n =>
    coordinateCompactBox q ∩ cumulativeLiftedCore I C n
  have hKnonempty : ∀ n, (K n).Nonempty := by
    intro n
    rcases cumulativeLiftedCore_nonempty_of_loss h hεsum hcumulativeLoss n with
      ⟨ω, hω⟩
    refine ⟨compactifyIntoBox q hqnonempty ω,
      compactifyIntoBox_mem q hqnonempty ω, ?_⟩
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hω ⊢
    intro j hj
    have hωj : ω ∈ cylinder (I j) (C j) := hω j hj
    change (fun i : I j => compactifyIntoBox q hqnonempty ω i) ∈ C j
    have hrestrict : (fun i : I j => compactifyIntoBox q hqnonempty ω i) =
        fun i : I j => ω i := by
      funext i
      exact compactifyIntoBox_apply_of_mem q hqnonempty ω (hCq j _ hωj i)
    rw [hrestrict]
    exact hωj
  have hKanti : ∀ n, K (n + 1) ⊆ K n := by
    intro n ω hω
    change ω ∈ coordinateCompactBox q ∩ cumulativeLiftedCore I C (n + 1) at hω
    change ω ∈ coordinateCompactBox q ∩ cumulativeLiftedCore I C n
    refine ⟨hω.1, ?_⟩
    have hcore := hω.2
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hcore ⊢
    intro j hj
    exact hcore j (Finset.mem_range.mpr
      (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self (n + 1))))
  have hKclosed : ∀ n, IsClosed (K n) := by
    intro n
    apply (isCompact_coordinateCompactBox hqcompact).isClosed.inter
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hj
    exact isClosed_cylinder_of_isCompact (I j) (hCcompact j)
  have hKcompact : IsCompact (K 0) :=
    (isCompact_coordinateCompactBox hqcompact).of_isClosed_subset
      (hKclosed 0) Set.inter_subset_left
  have hKi : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hKanti hKnonempty hKcompact hKclosed
  rcases hKi with ⟨ω, hω⟩
  have hωA : ω ∈ ⋂ n, A n := by
    simp only [Set.mem_iInter] at hω ⊢
    intro n
    rw [hArep n]
    apply hCS n
    have hncore := (hω n).2
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hncore
    exact hncore n (by simp)
  rw [hAempty] at hωA
  exact hωA

/-- `BrownianCylinderOnceChargedCompactCore` implies the Carathéodory
continuity-at-empty condition.

The proof does not assume any lifted core is nonempty.  The estimate
`β + ∑ j ≤ n, δ j < r` proves finite-stage nonemptiness.  Coordinate
compactification then places those finite intersections in one compact product
box, and the Cantor intersection argument supplies a path in every member of
the allegedly empty decreasing cylinder sequence. -/
theorem brownianCylinderContinuityAtEmpty_of_onceChargedCompactCore
    (hcore : BrownianCylinderOnceChargedCompactCore) :
    BrownianCylinderContinuityAtEmpty := by
  intro A hAcyl hAanti hAempty
  have hcontent : Antitone (fun n => brownianCylinderContent (A n)) := by
    intro n m hnm
    exact addContent_mono isSetSemiring_measurableCylinders
      (hAcyl m) (hAcyl n) (hAanti hnm)
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hcontent]
  intro r hr
  by_contra h
  push Not at h
  rcases hcore A hAcyl hAanti r hr h with
    ⟨I, S, C, q, β, δ, hβ, hδsum, hSmeas, hArep, hCS, hCcompact,
      hinsideLoss, hqcompact, hqnonempty, hboxLoss⟩
  have hcumulativeLoss : ∀ n,
      brownianCylinderContent (A n \ cumulativeLiftedCore I C n) ≤
        β + ∑ j ∈ Finset.range (n + 1), δ j :=
    brownianCylinderContent_sdiff_cumulativeLiftedCore_le_onceCharged
      hAcyl hAanti hSmeas hArep hCcompact hqcompact hinsideLoss hboxLoss
  let K : ℕ → Set BrownianRawPath := fun n =>
    coordinateCompactBox q ∩ cumulativeLiftedCore I C n
  have hKnonempty : ∀ n, (K n).Nonempty := by
    intro n
    rcases cumulativeLiftedCore_nonempty_of_onceChargedLoss
        h hβ hδsum hcumulativeLoss n with ⟨ω, hω⟩
    refine ⟨compactifyIntoBox q hqnonempty ω,
      compactifyIntoBox_mem q hqnonempty ω, ?_⟩
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hω ⊢
    intro j hj
    have hωj : ω ∈ cylinder (I j) (C j) := hω j hj
    change (fun i : I j => compactifyIntoBox q hqnonempty ω i) ∈ C j
    have hrestrict : (fun i : I j => compactifyIntoBox q hqnonempty ω i) =
        fun i : I j => ω i := by
      funext i
      apply compactifyIntoBox_apply_of_mem q hqnonempty ω
      exact (hCS j hωj).2 i (Set.mem_univ i)
    rw [hrestrict]
    exact hωj
  have hKanti : ∀ n, K (n + 1) ⊆ K n := by
    intro n ω hω
    change ω ∈ coordinateCompactBox q ∩ cumulativeLiftedCore I C (n + 1) at hω
    change ω ∈ coordinateCompactBox q ∩ cumulativeLiftedCore I C n
    refine ⟨hω.1, ?_⟩
    have hcore := hω.2
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hcore ⊢
    intro j hj
    exact hcore j (Finset.mem_range.mpr
      (lt_trans (Finset.mem_range.mp hj) (Nat.lt_succ_self (n + 1))))
  have hKclosed : ∀ n, IsClosed (K n) := by
    intro n
    apply (isCompact_coordinateCompactBox hqcompact).isClosed.inter
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hj
    exact isClosed_cylinder_of_isCompact (I j) (hCcompact j)
  have hKcompact : IsCompact (K 0) :=
    (isCompact_coordinateCompactBox hqcompact).of_isClosed_subset
      (hKclosed 0) Set.inter_subset_left
  have hKi : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hKanti hKnonempty hKcompact hKclosed
  rcases hKi with ⟨ω, hω⟩
  have hωA : ω ∈ ⋂ n, A n := by
    simp only [Set.mem_iInter] at hω ⊢
    intro n
    rw [hArep n]
    apply (hCS n).trans Set.inter_subset_left
    have hncore := (hω n).2
    simp only [cumulativeLiftedCore, Set.mem_iInter] at hncore
    exact hncore n (by simp)
  rw [hAempty] at hωA
  exact hωA

end BrownianNestedCompactCoreProof
end BlockBand.SourceProcess.WienerRecovery.CEH
