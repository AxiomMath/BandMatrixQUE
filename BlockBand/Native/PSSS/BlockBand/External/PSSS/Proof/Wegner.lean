module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOSLimit
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.PublicBlockProductAdapter

/-!
# Product disintegration for the multiblock Wegner estimate

This module fixes the exact public normalized-GUE product formulation of the
Wegner bound of PSSS (Peled–Schenker–Shamis–Sodin) and proves the
measure-theoretic disintegration which exposes one block while fixing all other
blocks.  The selected factor is retained as a singleton dependent Pi-type: its
unique coordinate has exactly law `GUE_{d_j}(1/d_j)`, with no change of
normalization.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators

/-- Deterministic deformation by an assembled public block sample. -/
def publicBlockDeformation {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (G : BlockGUE.PublicBlockSample dims) :
    HermitianMatrix (BlockGUE.Index dims) :=
  ⟨A₀.1 + (BlockGUE.publicBlockDiagonal G).1,
    A₀.2.add (BlockGUE.publicBlockDiagonal G).2⟩

/-- The multiplicity count of a publicly assembled deformed block family is
measurable in the complete block sample. -/
theorem measurable_publicBlockDeformation_eigenCount_Icc {k : ℕ}
    (dims : Fin k → ℕ) (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) :
    Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b)) := by
  apply (measurable_eigenCount_Icc a b).comp
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact measurable_const.add
    ((BlockGUE.measurable_hermitianMatrix_entry x y).comp
      (BlockGUE.measurable_publicBlockDiagonal dims))

/-- The sharp multiblock Wegner assertion in the concrete public block-product
representation.  Its law is the product of `GUE_{d_j}(1/d_j)` and
its deformation is the deterministic matrix plus the assembled block diagonal
sample. -/
def WegnerBound (C : ℝ) : Prop :=
  ∀ ⦃k : ℕ⦄ (dims : Fin k → ℕ), ∀ (hd : ∀ j, 0 < dims j),
  ∀ (A₀ : HermitianMatrix (BlockGUE.Index dims)) (a b : ℝ), a ≤ b →
  (∫⁻ G, (eigenCount (publicBlockDeformation A₀ G) (Set.Icc a b) : ℝ≥0∞)
    ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ENNReal.ofReal (C * (∑ j, (dims j : ℝ)) * (b - a))

namespace BlockProductDisintegration

/-- Samples of every block except the selected block `j`. -/
abbrev ExteriorSample {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  ∀ q : {i : Fin k // i ≠ j}, HermitianMatrix (Fin (dims q.1))

/-- The selected block retained as a singleton dependent Pi-type. -/
abbrev SelectedSample {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :=
  ∀ q : {i : Fin k // ¬ i ≠ j}, HermitianMatrix (Fin (dims q.1))

/-- Product law of all blocks other than `j`. -/
def exteriorMeasure {k : ℕ} (dims : Fin k → ℕ)
    (_hd : ∀ i, 0 < dims i) (j : Fin k) : Measure (ExteriorSample dims j) :=
  Measure.pi fun q =>
    (GUE (dims q.1) (1 / (dims q.1 : ℝ)) :
      Measure (HermitianMatrix (Fin (dims q.1))))

/-- Singleton product law containing exactly block `j`. -/
def selectedMeasure {k : ℕ} (dims : Fin k → ℕ)
    (_hd : ∀ i, 0 < dims i) (j : Fin k) : Measure (SelectedSample dims j) :=
  Measure.pi fun q =>
    (GUE (dims q.1) (1 / (dims q.1 : ℝ)) :
      Measure (HermitianMatrix (Fin (dims q.1))))

instance instIsProbabilityMeasureExteriorMeasure {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k) :
    IsProbabilityMeasure (exteriorMeasure dims hd j) := by
  unfold exteriorMeasure
  infer_instance

instance instIsProbabilityMeasureSelectedMeasure {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k) :
    IsProbabilityMeasure (selectedMeasure dims hd j) := by
  unfold selectedMeasure
  infer_instance

/-- Measurable split of a block family into the exterior and the selected
singleton factor. -/
def split {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    BlockGUE.PublicBlockSample dims ≃ᵐ
      ExteriorSample dims j × SelectedSample dims j := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd
    (fun i : Fin k => HermitianMatrix (Fin (dims i))) (fun i => i ≠ j)

/-- The coordinate split transports the public block product to the
product of the exterior law and the selected singleton-block law. -/
theorem measurePreserving_split {k : ℕ} (dims : Fin k → ℕ)
    (hd : ∀ i, 0 < dims i) (j : Fin k) :
    MeasurePreserving (split dims j)
      (BlockGUE.publicBlockProductMeasure dims hd)
      ((exteriorMeasure dims hd j).prod (selectedMeasure dims hd j)) := by
  classical
  simpa [split, BlockGUE.publicBlockProductMeasure, exteriorMeasure,
    selectedMeasure] using
    (measurePreserving_piEquivPiSubtypeProd
      (fun i : Fin k =>
        (GUE (dims i) (1 / (dims i : ℝ)) :
          Measure (HermitianMatrix (Fin (dims i)))))
      (fun i => i ≠ j))

/-- Exact Tonelli disintegration of the public block product, with the selected
block integrated in the inner integral and every exterior block fixed in the
outer integral. -/
theorem lintegral_publicBlockProduct_eq_iterated {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (F : BlockGUE.PublicBlockSample dims → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd) =
      ∫⁻ Gext, ∫⁻ Gj, F ((split dims j).symm (Gext, Gj))
          ∂selectedMeasure dims hd j
        ∂exteriorMeasure dims hd j := by
  have hchange := (measurePreserving_split dims hd j).lintegral_comp_emb
    (split dims j).measurableEmbedding
    (fun p => F ((split dims j).symm p))
  have hmeas : Measurable (fun p => F ((split dims j).symm p)) :=
    hF.comp (split dims j).symm.measurable
  calc
    (∫⁻ G, F G ∂BlockGUE.publicBlockProductMeasure dims hd) =
        ∫⁻ p, F ((split dims j).symm p)
          ∂((exteriorMeasure dims hd j).prod (selectedMeasure dims hd j)) := by
      simpa using hchange
    _ = ∫⁻ Gext, ∫⁻ Gj, F ((split dims j).symm (Gext, Gj))
          ∂selectedMeasure dims hd j
        ∂exteriorMeasure dims hd j := by
      exact MeasureTheory.lintegral_prod _ hmeas.aemeasurable

end BlockProductDisintegration
end PSSSNative.BlockBand.PSSS
