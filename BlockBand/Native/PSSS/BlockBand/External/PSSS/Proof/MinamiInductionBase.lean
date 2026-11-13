module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerEndpointLimit
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneCompression

/-!
# Base and deterministic core of the PSSS factorial-count induction

This module starts the Minami chain of PSSS (Peled–Schenker–Shamis–Sodin)
immediately after the sharp multiblock Wegner estimate.  It fixes the concrete
public product of normalized GUE blocks and records:

* the order-indexed factorial assertion used by the induction;
* its order-one proof from the completed sharp Wegner theorem;
* the exact successor-factorial splitting identity; and
* the endpoint-stable rank-one comparison used at the successor step.

The interval is always the same closed interval `Icc a b`.  In particular, the
rank-one limit theorem below retains the endpoint hypotheses and the canonical
extra zero of the ambient projector compression.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators

universe u

/-- The exact splitting used at the order-`r` to order-`r+1` step:
`(N)_{r+1} = N (N-1)_r`.  This formulation is valid also for `N = 0`, so no
positivity side condition is hidden in the induction. -/
theorem descFactorial_succ_split (N r : ℕ) :
    N.descFactorial (r + 1) = N * (N - 1).descFactorial r := by
  cases N with
  | zero => simp
  | succ N => simpa using Nat.succ_descFactorial_succ N r

/-- Positive rank-one interlacing bounds the predecessor factorial appearing
after `descFactorial_succ_split`.  The interval is not enlarged or opened. -/
theorem rankOne_predecessorFactorial_le {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (v : EuclideanSpace ℂ ι)
    {τ : ℝ} (hτ : 0 ≤ τ) {a b : ℝ} (_hab : a ≤ b) (r : ℕ) :
    (eigenCount K (Set.Icc a b) - 1).descFactorial r ≤
      (eigenCount (rankOneShift K v τ) (Set.Icc a b)).descFactorial r := by
  exact descFactorial_rankOne_le K v hτ (Set.Icc a b) (ordConnected_Icc) r

/-- Endpoint-stable passage of the predecessor factorial to positive
rank-one compression.  The extra zero is kept explicitly, exactly as in the
proved compression theorem; no endpoint-avoidance hypothesis is dropped. -/
theorem eventually_rankOne_predecessorFactorial_eq_compression {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1)
    {a b : ℝ} (hab : a ≤ b)
    (ha : eigenCount (compressHermitian K v) {a} = (if a = 0 then 1 else 0))
    (hb : eigenCount (compressHermitian K v) {b} = (if b = 0 then 1 else 0))
    (r : ℕ) :
    ∀ᶠ τ : ℝ in atTop,
      (eigenCount (rankOneShift K v τ) (Set.Icc a b)).descFactorial r =
        (eigenCount (compressHermitian K v) (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r := by
  filter_upwards [eigenCount_rankOne_eventually_eq K v hv hab ha hb] with τ hτ
  congr 1
  omega

end PSSSNative.BlockBand.PSSS
