module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiPublicWeightedTraceDisintegration
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedEventTonelli
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFirstReductionAssembly

/-!
# Fixed-predecessor bridge to the corrected Minami kernel

This module bridges the weighted selected regulated trace to the corrected
auxiliary kernel without specializing any mesh cell to the regulated resolvent itself.
The predecessor stays `(N_[a,b] - 1).descFactorial r` until it is bounded by
the fixed-`Icc a b` ambient-compression predecessor.  Only the auxiliary
multiplicity uses `Ioo (-xi) xi`, and the inverse event in the later mesh is
the generic cell-midpoint inverse.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1500000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Generic midpoint sphere insertion for one corrected mesh cell.  The
large-image event is formed from the cell-midpoint inverse, never from the
regulated resolvent itself.  The public predecessor is direction-independent
when the sphere event is inserted and is replaced by the fixed compression
predecessor only afterwards, almost everywhere in the sphere direction. -/
theorem occupied_fullPredecessor_le_two_midpointSphere_fixedPredecessor
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e t xi : ℝ) {eta : ℝ} (heta : 0 < eta)
    {a b : ℝ} (hab : a ≤ b) (M r : ℕ) (n : Fin (2 ^ M))
    (hend : ∀ᵐ φ ∂uniformSphere (dims j),
      ‖φ‖ = 1 ∧
        eigenCount
            (compressHermitian
              (publicBlockDeformation A₀
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
              (selectedAmbientDirection j φ)) {a} =
            (if a = 0 then 1 else 0) ∧
          eigenCount
            (compressHermitian
              (publicBlockDeformation A₀
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
              (selectedAmbientDirection j φ)) {b} =
            (if b = 0 then 1 else 0)) :
    let H := correctedSelectedAuxiliaryHermitian A₀ j heta
      ((((Gext, Gj), e), t), xi)
    let Q := (H.1 -
      (correctedMinamiCellMidpoint xi M n : ℂ) •
        (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹
    let O : ℝ≥0∞ :=
      Set.indicator {_u : Unit |
        gridCellOccupied H (-xi) (correctedMinamiCellWidth xi M) n}
        (fun _ => (1 : ℝ≥0∞)) ()
    let W := fullPublicFixedPredecessorWeight A₀ a b r
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
    O * W ≤
      2 * ∫⁻ φ,
        O *
          Set.indicator {v : EuclideanSpace ℂ (Fin (dims j)) |
              ‖Q‖ / (10 * Real.sqrt (dims j)) ≤
                ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
                  EuclideanSpace ℂ (Fin (dims j)))‖}
            (fun _ => (1 : ℝ≥0∞)) φ *
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
        ∂uniformSphere (dims j) := by
  dsimp only
  let H := correctedSelectedAuxiliaryHermitian A₀ j heta
    ((((Gext, Gj), e), t), xi)
  let Q : Matrix (Fin (dims j)) (Fin (dims j)) ℂ := (H.1 -
    (correctedMinamiCellMidpoint xi M n : ℂ) •
      (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹
  let E : Set (EuclideanSpace ℂ (Fin (dims j))) :=
    {v | ‖Q‖ / (10 * Real.sqrt (dims j)) ≤
      ‖(WithLp.toLp 2 (Q *ᵥ WithLp.ofLp v) :
        EuclideanSpace ℂ (Fin (dims j)))‖}
  let O : ℝ≥0∞ :=
    Set.indicator {_u : Unit |
      gridCellOccupied H (-xi) (correctedMinamiCellWidth xi M) n}
      (fun _ => (1 : ℝ≥0∞)) ()
  let W := fullPublicFixedPredecessorWeight A₀ a b r
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
  have hE : MeasurableSet E := by
    apply measurableSet_le
    · exact measurable_const
    · fun_prop
  have hsphere : W ≤ 2 * ∫⁻ φ, E.indicator (fun _ => W) φ
      ∂uniformSphere (dims j) := by
    have h := fullPublicFixedPredecessorWeight_le_two_uniformSphere_large
      A₀ a b r
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      j (hd j) Q
    change W ≤ 2 * ∫⁻ _ in E, W ∂uniformSphere (dims j) at h
    rw [← lintegral_indicator hE] at h
    exact h
  have hreplace : ∀ᵐ φ ∂uniformSphere (dims j),
      E.indicator (fun _ => W) φ ≤
        E.indicator (fun φ =>
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)) φ := by
    filter_upwards [hend] with φ hφ
    have hu : ‖selectedAmbientDirection j φ‖ = 1 := by simpa using hφ.1
    have hpred := fullPublicFixedPredecessorWeight_le_compression
      A₀ ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      (selectedAmbientDirection j φ) hu hab hφ.2.1 hφ.2.2 r
    rw [← fixedSelectedPredecessorWeight_eq_literal_compression
      A₀ j φ hφ.1 a b r Gext Gj] at hpred
    exact Set.indicator_le_indicator hpred
  by_cases hocc :
      gridCellOccupied H (-xi) (correctedMinamiCellWidth xi M) n
  · have hmain := hsphere.trans
      (mul_le_mul_right (lintegral_mono_ae hreplace) 2)
    simpa [H, Q, E, W, Set.indicator, hocc] using hmain
  · simp [H, Set.indicator, hocc]

end PSSSNative.BlockBand.PSSS
