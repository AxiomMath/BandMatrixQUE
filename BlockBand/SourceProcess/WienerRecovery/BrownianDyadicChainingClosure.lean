module

public import BlockBand.SourceProcess.WienerRecovery.BrownianKolmogorovChentsovClosure
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Dyadic Borel–Cantelli and chaining closure

This module supplies the countable probabilistic and deterministic layer used after
finite-level Brownian increment estimates.  A geometric bound on the measure of the
bad event at level `n` is summable in `ENNReal`, hence Borel–Cantelli gives eventual
avoidance almost surely.  The same statement, applied to successive approximants,
combines with a summable deterministic modulus to give an almost-sure Cauchy sequence.

The declarations are independent of raw-path continuity.  In particular, they do not by
themselves give `BrownianContinuousModificationExists`: that also requires choosing the
dyadic approximants on each compact interval, extending their limits, and proving
measurability and fixed-time identification.  The only Brownian-specific input needed
by that specialization is the finite-level union estimate
`measureReal_iUnion_abs_brownianIncrement_ge_le`, specialized here as
`measureReal_dyadicBadLevel_le` (and hence, for the canonical raw measure, the hypothesis
`BrownianCylinderContinuityAtEmpty`, proved as `brownianCylinderContinuityAtEmpty`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.WienerRecovery.CEH

open scoped ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace BrownianDyadicChainingClosure

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open BrownianKolmogorovChentsovClosure

/-- The left endpoint of edge `k` in the level-`n` dyadic partition of
`[0,T]`. -/
def dyadicLeft (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) : NNReal :=
  T * (k.1 : NNReal) / (2 ^ n : ℕ)

/-- The right endpoint of edge `k` in the level-`n` dyadic partition of
`[0,T]`. -/
def dyadicRight (T : NNReal) (n : ℕ) (k : Fin (2 ^ n)) : NNReal :=
  T * ((k.1 + 1 : ℕ) : NNReal) / (2 ^ n : ℕ)

/-- The level-`n` bad event for the dyadic increment modulus `ε n` on the
compact interval `[0,T]`. -/
def dyadicBadLevel (B : NNReal → Ω → ℝ) (T : NNReal)
    (ε : ℕ → ℝ) (n : ℕ) : Set Ω :=
  ⋃ k : Fin (2 ^ n),
    {ω | ε n ≤ |B (dyadicLeft T n k) ω - B (dyadicRight T n k) ω|}

/-- The Brownian finite-level union estimate specialized to every edge of the
level-`n` dyadic partition of a compact interval. -/
theorem measureReal_dyadicBadLevel_le
    {P : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (T : NNReal) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (n : ℕ) :
    P.real (dyadicBadLevel B T ε n) ≤
      ∑ k : Fin (2 ^ n), 2 * Real.exp
        (-(ε n) ^ 2 /
          (2 * (nndist (dyadicLeft T n k).1
            (dyadicRight T n k).1 : ℝ))) := by
  exact measureReal_iUnion_abs_brownianIncrement_ge_le hB
    (dyadicLeft T n) (dyadicRight T n) (hε n)

/-- The same compact-dyadic estimate for the canonical raw coordinate process.
Its only measure-construction hypothesis is the cylinder-content continuity
condition `BrownianCylinderContinuityAtEmpty`. -/
theorem measureReal_rawCoordinate_dyadicBadLevel_le
    (hcont : ScalarWienerMeasureConstruction.BrownianCylinderContinuityAtEmpty)
    (T : NNReal) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (n : ℕ) :
    (ScalarWienerMeasureConstruction.brownianRawMeasure hcont).real
        (dyadicBadLevel ScalarWienerMeasureConstruction.rawCoordinateProcess T ε n) ≤
      ∑ k : Fin (2 ^ n), 2 * Real.exp
        (-(ε n) ^ 2 /
          (2 * (nndist (dyadicLeft T n k).1
            (dyadicRight T n k).1 : ℝ))) := by
  exact measureReal_dyadicBadLevel_le
    (ScalarWienerMeasureConstruction.isPreBrownianReal_rawCoordinateProcess hcont)
    T ε hε n

/-- A geometric upper bound on level-event measures is summable as an
`ENNReal` series.  This is the exact finiteness premise of first
Borel–Cantelli. -/
theorem tsum_measure_ne_top_of_geometric_bound
    (E : ℕ → Set Ω) {C q : ENNReal}
    (hC : C ≠ ∞) (hq : q < 1)
    (hE : ∀ n, μ (E n) ≤ C * q ^ n) :
    (∑' n, μ (E n)) ≠ ∞ := by
  have hle : (∑' n, μ (E n)) ≤ ∑' n, C * q ^ n :=
    ENNReal.tsum_le_tsum hE
  refine ne_of_lt (hle.trans_lt ?_)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) (tsum_geometric_lt_top.2 hq)

/-- First Borel–Cantelli with a geometric level envelope: almost every sample
avoids every bad level from some point onward. -/
theorem ae_eventually_notMem_of_geometric_bound
    (E : ℕ → Set Ω) {C q : ENNReal}
    (hC : C ≠ ∞) (hq : q < 1)
    (hE : ∀ n, μ (E n) ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ E n :=
  ae_eventually_notMem
    (tsum_measure_ne_top_of_geometric_bound E hC hq hE)

/-- A finite family of bad edges at each level can be packaged as one level
bad event.  Eventual avoidance of the union is exactly an eventual uniform
bound over all edges of that level. -/
theorem ae_eventually_forall_not_of_geometric_iUnion_bound
    (m : ℕ → ℕ) (E : ∀ n, Fin (m n) → Set Ω)
    {C q : ENNReal} (hC : C ≠ ∞) (hq : q < 1)
    (hE : ∀ n, μ (⋃ i, E n i) ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ i, ω ∉ E n i := by
  filter_upwards
    [ae_eventually_notMem_of_geometric_bound
      (fun n => ⋃ i, E n i) hC hq hE] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_iUnion, not_exists] using hn

/-- A geometric envelope for the dyadic level events yields the
almost-sure eventual uniform dyadic modulus on `[0,T]`.  The strict inequality
is a consequence of avoiding the closed bad event `ε n ≤ |Δ|`. -/
theorem ae_eventually_dyadic_modulus_of_geometric_bound
    (B : NNReal → Ω → ℝ) (T : NNReal) (ε : ℕ → ℝ)
    {C q : ENNReal} (hC : C ≠ ∞) (hq : q < 1)
    (hbad : ∀ n, μ (dyadicBadLevel B T ε n) ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |B (dyadicLeft T n k) ω - B (dyadicRight T n k) ω| < ε n := by
  filter_upwards
    [ae_eventually_notMem_of_geometric_bound
      (dyadicBadLevel B T ε) hC hq hbad] with ω hω
  filter_upwards [hω] with n hn
  intro k
  have hk : ω ∉ {ω | ε n ≤
      |B (dyadicLeft T n k) ω - B (dyadicRight T n k) ω|} := by
    intro hmem
    apply hn
    exact Set.mem_iUnion.2 ⟨k, hmem⟩
  simpa only [Set.mem_ofPred_eq, not_le] using hk

/-- Deterministic chaining lemma allowing finitely many exceptional initial
levels.  A summable bound on all sufficiently late successive distances makes
the whole sequence Cauchy. -/
theorem cauchySeq_of_eventually_dist_le_of_summable
    {X : Type*} [PseudoMetricSpace X] (u : ℕ → X) (d : ℕ → ℝ)
    (hd : Summable d)
    (hu : ∀ᶠ n in atTop, dist (u n) (u n.succ) ≤ d n) :
    CauchySeq u := by
  rw [eventually_atTop] at hu
  obtain ⟨N, hN⟩ := hu
  apply (cauchySeq_shift N).1
  apply cauchySeq_of_dist_le_of_summable (fun n => d (n + N))
  · intro n
    simpa [Nat.add_assoc, Nat.succ_eq_add_one, Nat.add_comm N 1,
      Nat.add_left_comm] using hN (n + N) (Nat.le_add_left N n)
  · exact hd.comp_injective (fun _ _ h => Nat.add_right_cancel h)

/-- Borel–Cantelli plus deterministic chaining.  If the failure of the
successive-step modulus has geometrically decaying probability and the modulus
itself is summable, then almost every approximating chain is Cauchy.  This is
the abstract form used for nested dyadic approximants on a compact interval. -/
theorem ae_cauchySeq_of_geometric_badStep_bound
    {X : Type*} [PseudoMetricSpace X]
    (u : Ω → ℕ → X) (d : ℕ → ℝ) (hd : Summable d)
    {C q : ENNReal} (hC : C ≠ ∞) (hq : q < 1)
    (hbad : ∀ n,
      μ {ω | d n < dist (u ω n) (u ω n.succ)} ≤ C * q ^ n) :
    ∀ᵐ ω ∂μ, CauchySeq (u ω) := by
  filter_upwards
    [ae_eventually_notMem_of_geometric_bound
      (fun n => {ω | d n < dist (u ω n) (u ω n.succ)}) hC hq hbad]
      with ω hω
  apply cauchySeq_of_eventually_dist_le_of_summable (u ω) d hd
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_lt] using hn

end BrownianDyadicChainingClosure

end BlockBand.SourceProcess.WienerRecovery.CEH
