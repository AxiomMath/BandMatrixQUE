module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerGlobalTrace

/-!
# Tonelli assembly for the public block Wegner estimate

Matrix determinants, adjugates and inverses depend measurably on the entries. The regulated
resolvent trace of the public block deformation, and each selected-block part of it, is
measurable in the sample; by Tonelli the expected full trace is at most the sum over blocks of the
iterated exterior/selected integrals of the selected-block traces.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

lemma Measurable.matrix_det {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) : Measurable (fun x => (M x).det) := by
  simp_rw [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i hi
  exact hM.eval_matrix (i := _) (j := _)

lemma Measurable.matrix_adjugate {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) : Measurable (fun x => (M x).adjugate) := by
  rw [Matrix.measurable_iff]
  intro i j
  simp_rw [Matrix.adjugate_apply]
  apply Measurable.matrix_det
  rw [Matrix.measurable_iff]
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact measurable_const
  · exact hM.eval_matrix (i := _) (j := _)

lemma Measurable.matrix_inv {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {M : α → Matrix ι ι ℂ}
    (hM : Measurable M) : Measurable (fun x => (M x)⁻¹) := by
  rw [show (fun x => (M x)⁻¹) = fun x =>
      Ring.inverse (M x).det • (M x).adjugate by
    funext x
    rw [Matrix.inv_def]]
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.smul_apply, Ring.inverse_eq_inv]
  exact (Measurable.matrix_det hM).inv.mul
    ((Measurable.matrix_adjugate hM).eval_matrix (i := i) (j := j))

/-- Positive part of the selected projected negative-imaginary regulated trace. -/
def publicBlockRegulatedSelectedTrace {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (e eta : ℝ) (G : BlockGUE.PublicBlockSample dims) : ℝ≥0∞ :=
  let M := (publicBlockDeformation A₀ G).1 -
    (e : ℂ) • (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) +
    Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
      (BlockGUE.Index dims) ℂ))
  ENNReal.ofReal (-((M⁻¹).submatrix
    (fun a : Fin (dims j) => ⟨j, a⟩)
    (fun a : Fin (dims j) => ⟨j, a⟩)).trace.im)

/-- Positive part of the full negative-imaginary regulated trace. -/
def publicBlockRegulatedTrace {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (e eta : ℝ)
    (G : BlockGUE.PublicBlockSample dims) : ℝ≥0∞ :=
  let M := (publicBlockDeformation A₀ G).1 -
    (e : ℂ) • (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) +
    Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
      (BlockGUE.Index dims) ℂ))
  ENNReal.ofReal (-(M⁻¹).trace.im)

/-- Each selected projected negative-imaginary regulated resolvent trace is
measurable in the public block sample. -/
theorem measurable_publicBlockRegulatedSelectedTrace {k : ℕ}
    (dims : Fin k → ℕ) (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (j : Fin k) (e eta : ℝ) :
    Measurable (publicBlockRegulatedSelectedTrace A₀ j e eta) := by
  unfold publicBlockRegulatedSelectedTrace
  apply Measurable.ennreal_ofReal
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  have hD : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      (publicBlockDeformation A₀ G).1) := by
    rw [Matrix.measurable_iff]
    intro i l
    exact measurable_const.add
      ((BlockGUE.measurable_hermitianMatrix_entry i l).comp
        (BlockGUE.measurable_publicBlockDiagonal dims))
  have hM : Measurable (fun G : BlockGUE.PublicBlockSample dims =>
      (publicBlockDeformation A₀ G).1 -
        (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
          (BlockGUE.Index dims) ℂ) +
        Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
          (BlockGUE.Index dims) ℂ))) := by
    rw [Matrix.measurable_iff]
    intro i l
    exact ((hD.eval_matrix (i := i) (j := l)).sub measurable_const).add measurable_const
  have hi := Measurable.matrix_inv hM
  exact measurable_neg.comp
    (Complex.measurable_im.comp (Finset.measurable_sum Finset.univ fun i _ =>
      hi.eval_matrix (i := ⟨j, i⟩) (j := ⟨j, i⟩)))

/-- The positive part of a finite real sum is bounded by the sum of the
positive parts, with no sign hypothesis on the summands. -/
lemma ofReal_finsetSum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ENNReal.ofReal_add_le.trans (add_le_add_right ih _)

/-- Exact public-product Tonelli disintegration for one selected projected
regulated trace. -/
theorem lintegral_publicBlockRegulatedSelectedTrace_eq_iterated {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (e eta : ℝ) :
    (∫⁻ G, publicBlockRegulatedSelectedTrace A₀ j e eta G
      ∂BlockGUE.publicBlockProductMeasure dims hd) =
    ∫⁻ Gext, ∫⁻ Gj,
      publicBlockRegulatedSelectedTrace A₀ j e eta
        ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
  exact BlockProductDisintegration.lintegral_publicBlockProduct_eq_iterated
    dims hd j _ (measurable_publicBlockRegulatedSelectedTrace dims A₀ j e eta)

/-- The expected regulated full trace is bounded by the sum over blocks of the disintegrated
selected-block averages. -/
theorem lintegral_publicBlockRegulatedTrace_le_sum_iterated {k : ℕ}
    (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (e eta : ℝ) :
    (∫⁻ G, publicBlockRegulatedTrace A₀ e eta G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ∑ j : Fin k, ∫⁻ Gext, ∫⁻ Gj,
      publicBlockRegulatedSelectedTrace A₀ j e eta
        ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
  calc
    _ ≤ ∫⁻ G, ∑ j : Fin k, publicBlockRegulatedSelectedTrace A₀ j e eta G
        ∂BlockGUE.publicBlockProductMeasure dims hd := by
      apply lintegral_mono
      intro G
      unfold publicBlockRegulatedTrace publicBlockRegulatedSelectedTrace
      dsimp only
      rw [neg_im_publicBlockRegulatedTrace_eq_sum]
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        ofReal_finsetSum_le Finset.univ (fun j : Fin k =>
          -(((((((publicBlockDeformation A₀ G).1 -
            (e : ℂ) • (1 : Matrix (BlockGUE.Index dims)
              (BlockGUE.Index dims) ℂ)) +
            Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
              (BlockGUE.Index dims) ℂ)))⁻¹).submatrix
                (fun a : Fin (dims j) => ⟨j, a⟩)
                (fun a : Fin (dims j) => ⟨j, a⟩)).trace).im))
    _ = ∑ j : Fin k, ∫⁻ G, publicBlockRegulatedSelectedTrace A₀ j e eta G
        ∂BlockGUE.publicBlockProductMeasure dims hd := by
      rw [MeasureTheory.lintegral_finsetSum]
      intro j hj
      exact measurable_publicBlockRegulatedSelectedTrace dims A₀ j e eta
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact lintegral_publicBlockRegulatedSelectedTrace_eq_iterated
        dims hd A₀ j e eta

end PSSSNative.BlockBand.PSSS
