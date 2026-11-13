module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerPositiveAbsorber
public import BlockBand.Native.PSSS.BlockBand.Analysis.ProjectedWegnerSchur

/-!
# Selected-block reindexing for the public multiblock Wegner argument

The block index set is split into one selected block and the rest, and the selected factor of the
product disintegration is identified with a normalized GUE block. The negative imaginary part of
a trace is the sum over blocks of the negative imaginary parts of the diagonal block traces.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The fiber over `j` is canonically equivalent to `Fin (dims j)`. -/
def selectedSigmaFiberEquiv {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    Fin (dims j) ≃ {x : BlockGUE.Index dims // x.1 = j} where
  toFun a := ⟨⟨j, a⟩, rfl⟩
  invFun x := x.2 ▸ x.1.2
  left_inv a := rfl
  right_inv x := by
    rcases x with ⟨⟨i, a⟩, hi⟩
    cases hi
    rfl

/-- Put the selected Sigma fiber first and all other block coordinates second. -/
def selectedBlockSplitEquiv {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    Fin (dims j) ⊕ {x : BlockGUE.Index dims // x.1 ≠ j} ≃
      BlockGUE.Index dims :=
  (selectedSigmaFiberEquiv dims j).sumCongr
    (Equiv.refl {x : BlockGUE.Index dims // x.1 ≠ j}) |>.trans
      (Equiv.sumCompl (fun x : BlockGUE.Index dims => x.1 = j))

@[simp] theorem selectedBlockSplitEquiv_inl {k : ℕ} (dims : Fin k → ℕ)
    (j : Fin k) (a : Fin (dims j)) :
    selectedBlockSplitEquiv dims j (Sum.inl a) = ⟨j, a⟩ := rfl

@[simp] theorem selectedBlockSplitEquiv_inr {k : ℕ} (dims : Fin k → ℕ)
    (j : Fin k) (x : {x : BlockGUE.Index dims // x.1 ≠ j}) :
    selectedBlockSplitEquiv dims j (Sum.inr x) = x := rfl

/-- Recombining the exterior and singleton-selected samples recovers the
selected coordinate. -/
theorem split_symm_apply_selected {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) :
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) j =
      Gj ⟨j, by simp⟩ := by
  unfold BlockProductDisintegration.split
  simp

/-- Recombining the split samples leaves every exterior coordinate equal to
its fixed exterior value.
-/
theorem split_symm_apply_exterior {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j)
    (q : {i : Fin k // i ≠ j}) :
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) q.1 = Gext q := by
  unfold BlockProductDisintegration.split
  rw [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  dsimp
  rw [dite_eq_left q.property]

/-- Evaluation at the unique selected singleton coordinate transports the
selected product measure to the public normalized GUE factor. -/
theorem measurePreserving_selectedMeasure_eval {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k) :
    MeasurePreserving
      (fun G : BlockProductDisintegration.SelectedSample dims j =>
        G ⟨j, by simp⟩)
      (BlockProductDisintegration.selectedMeasure dims hd j)
      (PSSSNative.BlockBand.GUE (dims j) (1 / (dims j : ℝ)) :
        Measure (HermitianMatrix (Fin (dims j)))) := by
  unfold BlockProductDisintegration.selectedMeasure
  simpa using
    (measurePreserving_eval
      (fun q : {i : Fin k // ¬ i ≠ j} =>
        (PSSSNative.BlockBand.GUE (dims q.1)
          (1 / (dims q.1 : ℝ)) :
          Measure (HermitianMatrix (Fin (dims q.1))))) ⟨j, by simp⟩)

/-- Exact singleton selected-measure transport for nonnegative integration. -/
theorem lintegral_selectedMeasure_eval {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (f : HermitianMatrix (Fin (dims j)) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ G, f (G ⟨j, by simp⟩)
      ∂BlockProductDisintegration.selectedMeasure dims hd j) =
      ∫⁻ V, f V
        ∂(PSSSNative.BlockBand.GUE (dims j) (1 / (dims j : ℝ)) :
          Measure (HermitianMatrix (Fin (dims j)))) := by
  exact (measurePreserving_selectedMeasure_eval dims hd j).lintegral_comp hf

/-- The full trace is the sum of the traces of all diagonal sigma fibers. -/
theorem trace_eq_sum_blockTraces {k : ℕ} {dims : Fin k → ℕ}
    (M : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) :
    M.trace = ∑ j : Fin k,
      (M.submatrix (fun a : Fin (dims j) => ⟨j, a⟩)
        (fun a : Fin (dims j) => ⟨j, a⟩)).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Fintype.sum_sigma' (fun j a => M ⟨j, a⟩ ⟨j, a⟩)

/-- The negative imaginary trace decomposes blockwise, with no loss or dimension factor. It is
applied before the conditioned `π C d_j` estimate for each selected block. -/
theorem neg_im_trace_eq_sum_selectedBlock {k : ℕ} {dims : Fin k → ℕ}
    (M : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) :
    -(M.trace.im) = ∑ j : Fin k,
      -((M.submatrix (fun a : Fin (dims j) => ⟨j, a⟩)
        (fun a : Fin (dims j) => ⟨j, a⟩)).trace.im) := by
  rw [trace_eq_sum_blockTraces]
  simp

end PSSSNative.BlockBand.PSSS
