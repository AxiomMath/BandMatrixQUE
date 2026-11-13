module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedFiniteMesh
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiSelectedBlockSimplicity

/-!
# Grid limit and Fatou passage for the open auxiliary count

Only the auxiliary multiplicity is counted on `Ioo (-xi) xi`.  The dyadic
mesh has exactly `2^M` half-open cells of width `2 xi / 2^M`.  The weight is
the fixed-target `Icc a b` compression predecessor and is independent of the
mesh scale.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 900000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The symmetric mesh width tends to zero. -/
theorem tendsto_correctedMinamiCellWidth_zero (xi : ℝ) :
    Tendsto (correctedMinamiCellWidth xi) atTop (𝓝 0) := by
  have hpow : Tendsto (fun M : ℕ => (1 / 2 : ℝ) ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun M : ℕ => correctedMinamiCellWidth xi M) =
      fun M => (2 * xi) * (1 / 2 : ℝ) ^ M := by
    funext M
    simp only [correctedMinamiCellWidth]
    rw [one_div, inv_pow]
    ring
  change Tendsto (fun M => correctedMinamiCellWidth xi M) atTop (𝓝 0)
  rw [heq]
  simpa using tendsto_const_nhds.mul hpow

/-- Every sufficiently fine mesh separates a simple spectrum. -/
theorem eventually_correctedMinamiCellWidth_le_gaps {N : ℕ} (xi : ℝ)
    (H : HermitianMatrix (Fin N))
    (hinj : Function.Injective (orderedEigenvalue H)) :
    ∀ᶠ M : ℕ in atTop, ∀ i j, i ≠ j →
      correctedMinamiCellWidth xi M ≤
        |orderedEigenvalue H i - orderedEigenvalue H j| := by
  have hw := tendsto_correctedMinamiCellWidth_zero xi
  simp only [eventually_all]
  intro i j hij
  have hgap : 0 < |orderedEigenvalue H i - orderedEigenvalue H j| :=
    abs_pos.mpr (sub_ne_zero.mpr (hinj.ne hij))
  filter_upwards [hw.eventually_lt_const hgap] with M hM
  exact hM.le

/-- A simple spectrum's open radial count is eventually bounded by the
symmetric occupied-cell mesh. -/
theorem eventually_eigenCount_Ioo_le_correctedGridOccupied {N : ℕ}
    (H : HermitianMatrix (Fin N)) {xi : ℝ} (hxi : 0 < xi)
    (hinj : Function.Injective (orderedEigenvalue H)) :
    ∀ᶠ M : ℕ in atTop,
      eigenCount H (Set.Ioo (-xi) xi) ≤
        gridOccupiedCount H (-xi) (correctedMinamiCellWidth xi M) (2 ^ M) := by
  filter_upwards
    [eventually_correctedMinamiCellWidth_le_gaps xi H hinj] with M hsep
  have hw : 0 < correctedMinamiCellWidth xi M :=
    div_pos (mul_pos (by norm_num) hxi) (by positivity)
  have hend : -xi + ((2 ^ M : ℕ) : ℝ) * correctedMinamiCellWidth xi M = xi := by
    rw [corrected_card_mul_minamiCellWidth]
    ring
  calc
    eigenCount H (Set.Ioo (-xi) xi) ≤ eigenCount H (Set.Ico (-xi) xi) :=
      eigenCount_mono H Set.Ioo_subset_Ico_self
    _ = eigenCount H (Set.Ico (-xi)
        (-xi + ((2 ^ M : ℕ) : ℝ) * correctedMinamiCellWidth xi M)) := by rw [hend]
    _ ≤ gridOccupiedCount H (-xi) (correctedMinamiCellWidth xi M) (2 ^ M) :=
      eigenCount_Ico_le_gridOccupiedCount_of_separated H (-xi)
        (correctedMinamiCellWidth xi M) hw hsep

/-- The finite-mesh occupied count. -/
def correctedSelectedGridOccupiedCount
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t xi : ℝ) (M : ℕ)
    (Gj : BlockProductDisintegration.SelectedSample dims j) : ℕ :=
  gridOccupiedCount
    (correctedSelectedAuxiliaryHermitian A₀ j heta
      ((((Gext, Gj), e), t), xi))
    (-xi) (correctedMinamiCellWidth xi M) (2 ^ M)

/-- A simple auxiliary spectrum eventually has at least as many
occupied mesh cells as eigenvalues in the open radial interval. -/
theorem eventually_correctedSelected_openCount_le_gridOccupied
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e t : ℝ) {xi : ℝ} (hxi : 0 < xi)
    (hinj : Function.Injective (orderedEigenvalue
      (correctedSelectedAuxiliaryHermitian A₀ j heta
        ((((Gext, Gj), e), t), xi)))) :
    ∀ᶠ M : ℕ in atTop,
      eigenCount
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) ≤
      correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj := by
  simpa only [correctedSelectedGridOccupiedCount] using
    eventually_eigenCount_Ioo_le_correctedGridOccupied
      (correctedSelectedAuxiliaryHermitian A₀ j heta
        ((((Gext, Gj), e), t), xi)) hxi hinj

/-- The preceding eventual inequality retains any fixed nonnegative weight. -/
theorem eventually_correctedSelected_openCount_mul_weight_le_gridOccupied
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (e t : ℝ) {xi : ℝ} (hxi : 0 < xi)
    (hinj : Function.Injective (orderedEigenvalue
      (correctedSelectedAuxiliaryHermitian A₀ j heta
        ((((Gext, Gj), e), t), xi)))) (W : ℝ≥0∞) :
    ∀ᶠ M : ℕ in atTop,
      (eigenCount
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi)) (Set.Ioo (-xi) xi) : ℝ≥0∞) * W ≤
      (correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M Gj : ℝ≥0∞) * W := by
  filter_upwards
    [eventually_correctedSelected_openCount_le_gridOccupied
      A₀ j heta Gext Gj e t hxi hinj] with M hM
  gcongr

/-- For fixed exterior and parameters, the auxiliary family has a
simple spectrum for almost every selected public GUE block. -/
theorem ae_selectedBlock_correctedAuxiliary_orderedEigenvalue_injective
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t xi : ℝ) :
    ∀ᵐ Gj ∂BlockProductDisintegration.selectedMeasure dims hd j,
      Function.Injective (orderedEigenvalue
        (correctedSelectedAuxiliaryHermitian A₀ j heta
          ((((Gext, Gj), e), t), xi))) := by
  let A := correctedSelectedAuxiliaryBackground A₀ j heta Gext e t
  have hs := ae_selectedBlock_addHermitian_orderedEigenvalue_injective
    dims hd j A
  filter_upwards [hs] with Gj hGj
  simpa only [correctedSelectedAuxiliaryHermitian,
    correctedSelectedAuxiliaryBackground, addHermitian, A] using hGj

/-- The occupied count is measurable in the selected sample. -/
theorem measurable_correctedSelectedGridOccupiedCount
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e t xi : ℝ) (M : ℕ) :
    Measurable (correctedSelectedGridOccupiedCount
      A₀ j heta Gext e t xi M) := by
  let A := correctedSelectedAuxiliaryBackground A₀ j heta Gext e t
  have heval : Measurable (fun Gj :
      BlockProductDisintegration.SelectedSample dims j =>
      Gj ⟨j, by simp⟩) := measurable_pi_apply _
  have h := (measurable_gridOccupiedCount_addHermitian A (-xi)
    (correctedMinamiCellWidth xi M) (2 ^ M)).comp heval
  rw [show correctedSelectedGridOccupiedCount A₀ j heta Gext e t xi M =
      fun Gj => gridOccupiedCount (addHermitian A (Gj ⟨j, by simp⟩))
        (-xi) (correctedMinamiCellWidth xi M) (2 ^ M) by
    funext Gj
    unfold correctedSelectedGridOccupiedCount correctedSelectedAuxiliaryHermitian
    congr 2]
  exact h

end PSSSNative.BlockBand.PSSS
