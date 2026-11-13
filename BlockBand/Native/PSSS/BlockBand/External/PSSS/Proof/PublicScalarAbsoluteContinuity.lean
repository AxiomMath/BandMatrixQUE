module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicGUECoordinateTransport
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Absolute continuity of heterogeneous public scalar Gaussians

The flattened public block law is a finite product of centered real Gaussians
whose variances depend on the block and on whether a coordinate is diagonal
or off-diagonal.  This module proves that such a heterogeneous finite product
is absolutely continuous with respect to the ambient product Lebesgue measure.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open MeasureTheory ProbabilityTheory

/-- Absolute continuity is stable under an arbitrary finite dependent product.
Both families are assumed sigma-finite so that the standard product
reassociation equivalence applies at every induction step. -/
theorem pi_absolutelyContinuous_pi_fin :
    ∀ (n : ℕ) (μ ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
      [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
  | zero =>
      intro μ ν _ _ h
      have hμν : μ = ν := Subsingleton.elim _ _
      rw [hμν]
  | succ n ih =>
      intro μ ν _ _ h
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have htail :
          Measure.pi (fun j : Fin n => μ (Fin.succ j)) ≪
            Measure.pi (fun j : Fin n => ν (Fin.succ j)) :=
        ih (fun j => μ (Fin.succ j)) (fun j => ν (Fin.succ j))
          (fun j => h (Fin.succ j))
      have hprod :
          (μ 0).prod (Measure.pi fun j : Fin n => μ (Fin.succ j)) ≪
            (ν 0).prod (Measure.pi fun j : Fin n => ν (Fin.succ j)) :=
        (h 0).prod htail
      have hmapped : Measure.map e (Measure.pi μ) ≪
          Measure.map e (Measure.pi ν) := by
        rw [(measurePreserving_piFinSuccAbove μ 0).map_eq,
          (measurePreserving_piFinSuccAbove ν 0).map_eq]
        simpa using hprod
      have hback := hmapped.map e.symm.measurable
      simpa [Measure.map_map] using hback

/-- Every flattened public scalar variance is strictly positive. -/
theorem publicScalarVariance_pos {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ j, 0 < d j) (s : BlockGUE.PublicScalarIndex d) :
    0 < BlockGUE.publicScalarVariance d hd s := by
  rcases s with ⟨j, c⟩
  unfold BlockGUE.publicScalarVariance
  rw [← NNReal.coe_pos]
  change 0 < (hermitianGUEFinCoordinateVariance (d j) (1 / (d j : ℝ))
    _ (hermitianCoordinateEquivFin (d j) c) : ℝ)
  rcases c with i | c
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inl]
    exact one_div_pos.mpr (by exact_mod_cast hd j)
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inr]
    exact div_pos (one_div_pos.mpr (by exact_mod_cast hd j)) (by norm_num)

/-- The heterogeneous flattened public scalar product is absolutely
continuous with respect to product Lebesgue measure. -/
theorem publicScalarMeasure_absolutelyContinuous {k : ℕ}
    (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) :
    BlockGUE.publicScalarMeasure d hd ≪
      (volume : Measure (BlockGUE.PublicScalarSample d)) := by
  let e := Fintype.equivFin (BlockGUE.PublicScalarIndex d)
  let E : (BlockGUE.PublicScalarSample d) ≃ᵐ
      (Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) e
  have hcoord : ∀ i : Fin (Fintype.card (BlockGUE.PublicScalarIndex d)),
      gaussianReal 0 (BlockGUE.publicScalarVariance d hd (e.symm i)) ≪ volume := by
    intro i
    exact gaussianReal_absolutelyContinuous 0
      (ne_of_gt (publicScalarVariance_pos d hd (e.symm i)))
  have hfin := pi_absolutelyContinuous_pi_fin
    (Fintype.card (BlockGUE.PublicScalarIndex d))
    (fun i => gaussianReal 0 (BlockGUE.publicScalarVariance d hd (e.symm i)))
    (fun _ => (volume : Measure ℝ)) hcoord
  have hmapped : Measure.map E (BlockGUE.publicScalarMeasure d hd) ≪
      Measure.map E (volume : Measure (BlockGUE.PublicScalarSample d)) := by
    have hμ :
        Measure.map E (BlockGUE.publicScalarMeasure d hd) =
          Measure.pi (fun i =>
            gaussianReal 0 (BlockGUE.publicScalarVariance d hd (e.symm i))) := by
      simpa [BlockGUE.publicScalarMeasure, E] using
        (Measure.pi_map_piCongrLeft e
          (fun i => gaussianReal 0
            (BlockGUE.publicScalarVariance d hd (e.symm i))))
    have hvol : Measure.map E
        (volume : Measure (BlockGUE.PublicScalarSample d)) =
          (volume : Measure
            (Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) → ℝ)) :=
      by
        simpa [E, MeasureTheory.volume_pi] using
          (Measure.pi_map_piCongrLeft e
            (fun _ : Fin (Fintype.card (BlockGUE.PublicScalarIndex d)) =>
              (volume : Measure ℝ)))
    rw [hμ, hvol]
    simpa [MeasureTheory.volume_pi] using hfin
  have hback := hmapped.map E.symm.measurable
  simpa [Measure.map_map] using hback

end PSSSNative.BlockBand.PSSS
