module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedDeterministicCell

/-!
# Finite corrected auxiliary mesh with the fixed-target predecessor

This is the finite-`M` estimate in the source-faithful PSSS reduction.  The
auxiliary spectrum is partitioned into half-open cells covering
`Ioo (-xi) xi`, while every summand retains exactly the fixed-target
`fixedSelectedPredecessorWeight` on `Icc a b`.  In particular, the weight is
independent of energy, Cauchy parameter, radius, and mesh resolution.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The fixed-target weighted selected-block estimate after shifting only the
auxiliary inverse event to a cell midpoint. -/
theorem correctedSelected_uniformSphere_weighted_shifted_cell :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      (Gext : BlockProductDisintegration.ExteriorSample dims j)
      (e t a b c : ℝ) (r : ℕ) (δ : ℝ), 0 < δ →
      (∫⁻ φ, ∫⁻ Gj,
        Set.indicator
          {Gj : BlockProductDisintegration.SelectedSample dims j |
            1 / (5 * Real.sqrt (dims j) * δ) ≤
              ‖(WithLp.toLp 2
                (((correctedSelectedAuxiliaryBackground A₀ j heta Gext e t).1 +
                    (Gj ⟨j, by simp⟩).1 -
                    (c : ℂ) • (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹ *ᵥ
                  WithLp.ofLp φ) : EuclideanSpace ℂ (Fin (dims j)))‖}
          (fun _ => (1 : ℝ≥0∞)) Gj *
            fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
      ENNReal.ofReal (5 * C * dims j * δ) *
        ∫⁻ φ, ∫⁻ Gj,
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j) := by
  obtain ⟨C, hC, hcell⟩ := selectedBlock_uniformSphere_weighted_cell
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A₀ eta heta Gext e t a b c r δ hδ
  let A : HermitianMatrix (Fin (dims j)) :=
    energyShiftHermitian
      (correctedSelectedAuxiliaryBackground A₀ j heta Gext e t) c
  let F : EuclideanSpace ℂ (Fin (dims j)) →
      Matrix (Fin (dims j)) (Fin (dims j)) ℂ → ℝ≥0∞ := fun φ P =>
    fixedTargetPredecessorWeight A₀ j φ a b r (Gext, P)
  have hF : ∀ φ, Measurable (F φ) := by
    intro φ
    exact (measurable_fixedTargetPredecessorWeight dims A₀ j φ a b r).comp
      (measurable_const.prodMk measurable_id)
  have h := hcell dims hd j A F hF δ hδ
  simpa only [A, F, fixedSelectedPredecessorWeight, energyShiftHermitian,
    addHermitian, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- A fixed corrected auxiliary cell midpoint is almost surely outside the
selected GUE spectrum. -/
theorem ae_selectedBlock_correctedAuxiliary_shift_isUnit
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t c : ℝ) :
    ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
      IsUnit
        ((correctedSelectedAuxiliaryBackground A₀ j heta Gext e t).1 +
          (Gj ⟨j, by simp⟩).1 -
          (c : ℂ) • (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ)) := by
  let A := correctedSelectedAuxiliaryBackground A₀ j heta Gext e t
  have hdet := ae_publicGUE_det_energyShift_add_ne_zero (hd j) A c
  have hdet' :=
    (measurePreserving_selectedMeasure_eval dims hd j).quasiMeasurePreserving.ae hdet
  filter_upwards [hdet'] with Gj hGj
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  simpa only [A] using hGj

/-- **Complete corrected finite-`M` bound.**  The half-open auxiliary cell and
large-direction indicators cost exactly `10 C d_j xi`; the right-hand weight
is the fixed-target full-compression predecessor and has no moving endpoint. -/
theorem correctedSelected_occupiedLargeImage_weighted_finiteMesh :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      (Gext : BlockProductDisintegration.ExteriorSample dims j)
      (e t a b xi : ℝ), 0 < xi → ∀ (M r : ℕ),
      (∑ n : Fin (2 ^ M),
        ∫⁻ φ, ∫⁻ Gj,
          let H := correctedSelectedAuxiliaryHermitian A₀ j heta
            ((((Gext, Gj), e), t), xi)
          let w := correctedMinamiCellWidth xi M
          let W := fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          Set.indicator {_u : Unit | gridCellOccupied H (-xi) w n}
              (fun _ => (1 : ℝ≥0∞)) () *
            Set.indicator
              {v : EuclideanSpace ℂ (Fin (dims j)) |
                ‖(H.1 - ((correctedMinamiCellMidpoint xi M n : ℝ) : ℂ) •
                    (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹‖ /
                    (10 * Real.sqrt (dims j)) ≤
                  ‖(WithLp.toLp 2
                    ((H.1 - ((correctedMinamiCellMidpoint xi M n : ℝ) : ℂ) •
                      (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹ *ᵥ
                        WithLp.ofLp v) : EuclideanSpace ℂ (Fin (dims j)))‖}
              (fun _ => (1 : ℝ≥0∞)) φ * W
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j)) ≤
        ENNReal.ofReal (10 * C * dims j * xi) *
          ∫⁻ φ, ∫⁻ Gj,
            fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
  obtain ⟨C, hC, hcell⟩ := correctedSelected_uniformSphere_weighted_shifted_cell
  refine ⟨C, hC, ?_⟩
  intro k dims hd j A₀ eta heta Gext e t a b xi hxi M r
  let W : ℝ≥0∞ := ∫⁻ φ, ∫⁻ Gj,
    fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
    ∂BlockProductDisintegration.selectedMeasure dims hd j
    ∂uniformSphere (dims j)
  have hw : 0 < correctedMinamiCellWidth xi M :=
    div_pos (mul_pos (by norm_num) hxi) (by positivity)
  calc
    _ ≤ ∑ n : Fin (2 ^ M),
        ∫⁻ φ, ∫⁻ Gj,
          Set.indicator
            {Gj : BlockProductDisintegration.SelectedSample dims j |
              1 / (5 * Real.sqrt (dims j) * correctedMinamiCellWidth xi M) ≤
                ‖(WithLp.toLp 2
                  (((correctedSelectedAuxiliaryBackground A₀ j heta Gext e t).1 +
                    (Gj ⟨j, by simp⟩).1 -
                    (correctedMinamiCellMidpoint xi M n : ℂ) •
                      (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))⁻¹ *ᵥ
                    WithLp.ofLp φ) : EuclideanSpace ℂ (Fin (dims j)))‖}
            (fun _ => (1 : ℝ≥0∞)) Gj *
              fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j) := by
      apply Finset.sum_le_sum
      intro n hn
      apply lintegral_mono
      intro φ
      apply lintegral_mono_ae
      filter_upwards
        [ae_selectedBlock_correctedAuxiliary_shift_isUnit dims hd j A₀ heta
          Gext e t (correctedMinamiCellMidpoint xi M n)] with Gj hunit
      have hdet := corrected_indicator_cell_largeImage_mul_weight_le_inverseVector
        (hd j)
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi))
        (-xi) (correctedMinamiCellWidth xi M) hw n φ
        (fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)) (by
          change IsUnit
            ((correctedSelectedAuxiliaryBackground A₀ j heta Gext e t).1 +
              (Gj ⟨j, by simp⟩).1 -
              (correctedMinamiCellMidpoint xi M n : ℂ) •
                (1 : Matrix (Fin (dims j)) (Fin (dims j)) ℂ))
          exact hunit)
      simpa [Set.indicator, correctedMinamiCellMidpoint,
        correctedSelectedAuxiliaryHermitian, addHermitian,
        correctedSelectedAuxiliaryBackground] using hdet
    _ ≤ ∑ _n : Fin (2 ^ M),
        ENNReal.ofReal
          (5 * C * dims j * correctedMinamiCellWidth xi M) * W := by
      apply Finset.sum_le_sum
      intro n hn
      exact hcell dims hd j A₀ heta Gext e t a b
        (correctedMinamiCellMidpoint xi M n) r
        (correctedMinamiCellWidth xi M) hw
    _ = ENNReal.ofReal (10 * C * dims j * xi) * W := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← mul_assoc,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      calc
        ((2 ^ M : ℕ) : ℝ) *
            (5 * C * dims j * correctedMinamiCellWidth xi M) =
            5 * C * dims j *
              (((2 ^ M : ℕ) : ℝ) * correctedMinamiCellWidth xi M) := by ring
        _ = 5 * C * dims j * (2 * xi) := by
          rw [corrected_card_mul_minamiCellWidth]
        _ = 10 * C * dims j * xi := by ring

end PSSSNative.BlockBand.PSSS
