module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiFixedPredecessorAverageBound

/-!
# Joint measurability of the corrected fixed-target predecessor

These modular lemmas expose the dependence on the sphere direction needed for
the sphere/exterior Tonelli swap.  They concern only the fixed target
`Icc a b` full ambient compression.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 2000000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- The finite-dimensional orthogonal projector is measurable in its vector. -/
theorem measurable_orthProj {N : ℕ} :
    Measurable (orthProj : EuclideanSpace ℂ (Fin N) →
      Matrix (Fin N) (Fin N) ℂ) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [orthProj, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  fun_prop

/-- The ambient orthogonal projector is measurable in its vector. -/
theorem measurable_orthogonalProjector {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (orthogonalProjector :
      EuclideanSpace ℂ ι → Matrix ι ι ℂ) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [orthogonalProjector, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  fun_prop

/-- Pointwise multiplication of jointly measurable finite matrices is measurable. -/
theorem Measurable.matrix_mul {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    {A B : Ω → Matrix ι ι ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun p => A p * B p) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro z _
  exact (Matrix.measurable_iff.mp hA x z).mul (Matrix.measurable_iff.mp hB z y)

/-- Conjugate transpose preserves measurability of finite matrix families. -/
theorem Measurable.matrix_conjTranspose {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun p => (A p)ᴴ) := by
  rw [Matrix.measurable_iff]
  intro x y
  exact Complex.continuous_conj.measurable.comp (Matrix.measurable_iff.mp hA y x)

/-- Extension by zero into the selected ambient block is measurable. -/
theorem measurable_selectedAmbientDirection
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    Measurable (selectedAmbientDirection j :
      EuclideanSpace ℂ (Fin (dims j)) → EuclideanSpace ℂ (BlockGUE.Index dims)) := by
  apply (WithLp.measurable_toLp 2 _).comp
  rw [measurable_pi_iff]
  intro x
  by_cases hx : x.1 = j
  · simp only [hx, dite_true]
    exact (measurable_pi_apply (X := fun _ : Fin (dims j) => ℂ) (hx ▸ x.2)).comp
      (WithLp.measurable_ofLp 2 _)
  · simp only [hx, dite_false]
    exact measurable_const

/-- Projection of the selected Hermitian block is jointly measurable in the
sphere direction and the split public sample. -/
theorem measurable_joint_selectedProjectedMatrix
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k) :
    Measurable (fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      orthProj p.1 * (p.2.2 ⟨j, by simp⟩).1 * orthProj p.1) := by
  let P := fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) => orthProj p.1
  let V := fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      (p.2.2 ⟨j, by simp⟩).1
  have hP : Measurable P := measurable_orthProj.comp measurable_fst
  have hV : Measurable V := measurable_subtype_coe.comp
    ((measurable_pi_apply (⟨j, by simp⟩ : {i : Fin k // ¬ i ≠ j})).comp
      (measurable_snd.comp measurable_snd))
  change Measurable (fun p => P p * V p * P p)
  exact Measurable.matrix_mul (Measurable.matrix_mul hP hV) hP

/-- The reconstructed full ambient compression is jointly measurable in the
sphere direction and the split public sample. -/
theorem measurable_joint_reconstructedFullCompression_selected
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k) :
    Measurable (fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      reconstructedFullCompression A₀ j p.1 p.2.1
        (orthProj p.1 * (p.2.2 ⟨j, by simp⟩).1 * orthProj p.1)) := by
  let X := fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      orthProj p.1 * (p.2.2 ⟨j, by simp⟩).1 * orthProj p.1
  let H := fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      (reconstructedFullDeformation A₀ j p.2.1 (X p)).1
  let P := fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      orthogonalProjector (selectedAmbientDirection j p.1)
  have hX : Measurable X := measurable_joint_selectedProjectedMatrix dims j
  have hH : Measurable H := measurable_subtype_coe.comp
    ((measurable_reconstructedFullDeformation dims A₀ j).comp
      ((measurable_fst.comp measurable_snd).prodMk hX))
  have hu : Measurable (fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      selectedAmbientDirection j p.1) :=
    (measurable_selectedAmbientDirection dims j).comp measurable_fst
  have hP : Measurable P := by
    simpa only [P, Function.comp_def] using
      (measurable_orthogonalProjector (ι := BlockGUE.Index dims)).comp hu
  apply Measurable.subtype_mk
  change Measurable (fun p => P p * H p * (P p)ᴴ)
  exact Measurable.matrix_mul (Measurable.matrix_mul hP hH)
    (Measurable.matrix_conjTranspose hP)

/-- Full joint measurability of the selected fixed-target predecessor in the
sphere direction, exterior sample, and selected sample. -/
theorem measurable_joint_fixedSelectedPredecessorWeight
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (a b : ℝ) (r : ℕ) :
    Measurable (fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      fixedSelectedPredecessorWeight A₀ j p.1 a b r p.2) := by
  have hH := measurable_joint_reconstructedFullCompression_selected dims A₀ j
  have hc : Measurable (fun p : EuclideanSpace ℂ (Fin (dims j)) ×
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) =>
      eigenCount
        (reconstructedFullCompression A₀ j p.1 p.2.1
          (orthProj p.1 * (p.2.2 ⟨j, by simp⟩).1 * orthProj p.1))
        (Set.Icc a b)) := (measurable_eigenCount_Icc a b).comp hH
  unfold fixedSelectedPredecessorWeight fixedTargetPredecessorWeight
  exact Measurable.ennreal_descFactorial _ (by fun_prop) r

end PSSSNative.BlockBand.PSSS
