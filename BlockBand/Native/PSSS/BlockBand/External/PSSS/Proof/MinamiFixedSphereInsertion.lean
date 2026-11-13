module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedSelectedPredecessor
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.UniformVectorOperatorCorollary

/-!
# Sphere insertion before fixed-target compression

PSSS (2.13), `l:formula` in arXiv:1608.02922, first inserts an independent
uniform direction while the predecessor is still the factorial count of the
full original public deformation on fixed `Icc a b`.  That weight is constant
in the direction.  Only afterwards may rank-one interlacing/Fatou replace it
by a compression predecessor.  This order is essential: the analogous bound
for an arbitrary direction-dependent weight is false.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 400000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder
open scoped Matrix.Norms.L2Operator

/-- The order-`r` predecessor before sphere insertion: the descending
factorial of the full public deformation count minus one on the fixed target
interval.  This is the predecessor in the successor split
`(N)_{r+1} = N (N-1)_r` in PSSS formula (2.13). -/
def fullPublicFixedPredecessorWeight
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (r : ℕ)
    (G : BlockGUE.PublicBlockSample dims) : ℝ≥0∞ :=
  (((eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) - 1).descFactorial r :
    ℕ) : ℝ≥0∞)

/-- A direction-independent nonnegative weight can be inserted under any
measurable event whose doubled probability is at least one. -/
theorem ennreal_le_two_mul_setLIntegral_const_of_one_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω)
    (W : ℝ≥0∞) (hlarge : 1 ≤ 2 * μ E) :
    W ≤ 2 * ∫⁻ _ in E, W ∂μ := by
  calc
    W = W * 1 := by simp
    _ ≤ W * (2 * μ E) := by gcongr
    _ = 2 * ∫⁻ _ in E, W ∂μ := by
      rw [setLIntegral_const E W]
      ring

/-- **Correct sphere insertion.**  The full fixed-target public predecessor is
inserted before compression, using exactly the APSSS large-vector event and
its source normalization `‖Q‖/(10√N)`. -/
theorem fullPublicFixedPredecessorWeight_le_two_uniformSphere_large
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ) (r : ℕ)
    (G : BlockGUE.PublicBlockSample dims) (j : Fin k) (hj : 0 < dims j)
    (Q : Matrix (Fin (dims j)) (Fin (dims j)) ℂ) :
    fullPublicFixedPredecessorWeight A₀ a b r G ≤
      2 * ∫⁻ _ in
        {v | ‖Q‖ / (10 * Real.sqrt (dims j)) ≤
          ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
            EuclideanSpace ℂ (Fin (dims j)))‖},
        fullPublicFixedPredecessorWeight A₀ a b r G
      ∂uniformSphere (dims j) := by
  let E : Set (EuclideanSpace ℂ (Fin (dims j))) :=
    {v | ‖Q‖ / (10 * Real.sqrt (dims j)) ≤
      ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
        EuclideanSpace ℂ (Fin (dims j)))‖}
  apply ennreal_le_two_mul_setLIntegral_const_of_one_le
    (uniformSphere (dims j)) E _
  simpa [E] using one_le_two_mul_uniformSphere_large hj Q

/-- Endpoint-stable codimension-one interlacing bounds the
successor predecessor `(N_I - 1)_r` by the canonical-zero-subtracted ambient
compression predecessor. -/
theorem fullPublicFixedPredecessorWeight_le_compression
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims)
    (u : EuclideanSpace ℂ (BlockGUE.Index dims)) (hu : ‖u‖ = 1)
    {a b : ℝ} (hab : a ≤ b)
    (ha : eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {a} =
      (if a = 0 then 1 else 0))
    (hb : eigenCount (compressHermitian (publicBlockDeformation A₀ G) u) {b} =
      (if b = 0 then 1 else 0)) (r : ℕ) :
    fullPublicFixedPredecessorWeight A₀ a b r G ≤
      (((eigenCount
        (compressHermitian (publicBlockDeformation A₀ G) u) (Set.Icc a b) -
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0)).descFactorial r : ℕ) :
        ℝ≥0∞) := by
  let K := publicBlockDeformation A₀ G
  obtain ⟨τ, hcompress, hτ⟩ := ((
    eventually_rankOne_predecessorFactorial_eq_compression
      K u hu hab ha hb r).and (eventually_ge_atTop (0 : ℝ))).exists
  unfold fullPublicFixedPredecessorWeight
  exact_mod_cast (rankOne_predecessorFactorial_le K u hτ hab r).trans_eq hcompress

end PSSSNative.BlockBand.PSSS
