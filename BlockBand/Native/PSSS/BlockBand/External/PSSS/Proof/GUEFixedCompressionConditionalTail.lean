module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.GUEFixedCompressionTail
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Scalar Gaussian branch and fixed-compression conditional assembly

This module proves the one-dimensional Gaussian small-interval bound
uniformly in its center.  It then records the product decomposition of
the standardized first-row law and the union-bound assembly of the scalar and
quadratic Schur branches.  The compression remains deterministic throughout.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set

/-- Uniform small-interval estimate for a standard real Gaussian, with the
explicit (deliberately non-sharp) density-one constant `2`. -/
theorem gaussianReal_smallInterval (c ε : ℝ) (_hε : 0 ≤ ε) :
    gaussianReal 0 1 {x | |x - c| ≤ ε} ≤ ENNReal.ofReal (2 * ε) := by
  have hset : {x : ℝ | |x - c| ≤ ε} = Set.Icc (c - ε) (c + ε) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset]
  calc
    gaussianReal 0 1 (Set.Icc (c - ε) (c + ε)) ≤
        volume (Set.Icc (c - ε) (c + ε)) :=
      gaussianReal_zero_one_le_volume _
    _ = ENNReal.ofReal (2 * ε) := by
      rw [Real.volume_Icc]
      congr 1
      linarith

/-- Scalar half of the Schur split.  Its bound is uniform in the deterministic
center and has the exact factor-four loss resulting from `t/2`. -/
theorem gaussianReal_scalarSchurBranch (c t : ℝ) (ht : 0 < t) :
    gaussianReal 0 1 {g | t / 2 * |g - c| ≤ 1} ≤
      ENNReal.ofReal (4 / t) := by
  have hevent : {g : ℝ | t / 2 * |g - c| ≤ 1} =
      {g | |g - c| ≤ 2 / t} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h
    · apply (le_div_iff₀ ht).2
      nlinarith
    · have h' := (le_div_iff₀ ht).1 h
      nlinarith
  rw [hevent]
  convert gaussianReal_smallInterval c (2 / t) (by positivity) using 1
  congr 1
  ring

/-- The first-row product measure splits into its diagonal standard Gaussian
and all realified row coordinates. -/
theorem measurePreserving_concreteFirstRow_split (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Unit ⊕ (Fin n × Fin 2) => ℝ))
      (Measure.pi fun _ : ConcreteFirstRowCoordinate n => gaussianReal 0 1)
      ((Measure.pi fun _ : Unit => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin n × Fin 2 => gaussianReal 0 1)) := by
  exact measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ (Fin n × Fin 2) => gaussianReal 0 1)

end PSSSNative.BlockBand.PSSS
