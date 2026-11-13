module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerTonelliAssembly

/-!
# Selected-block identification and averaging at a fixed exterior

With the exterior blocks fixed, the regulated selected trace of the public block deformation is
the trace of a selected block of a regulated full block matrix. Averaging over the selected GUE
block and using the single-block density of states bounds its expectation by `π C₀ dims j`; summing
over blocks gives the Wegner-type bound `π C₀ ∑ⱼ dims j` for the full regulated trace.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

section FrozenBlocks

variable {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)

abbrev frozenSelectedA : Matrix (Fin (dims j)) (Fin (dims j)) ℂ :=
  (frozenExteriorReindexed A₀ j Gext).submatrix Sum.inl Sum.inl

abbrev frozenSelectedB : Matrix (Fin (dims j))
    {x : BlockGUE.Index dims // x.1 ≠ j} ℂ :=
  (frozenExteriorReindexed A₀ j Gext).submatrix Sum.inl Sum.inr

abbrev frozenSelectedC : Matrix {x : BlockGUE.Index dims // x.1 ≠ j}
    (Fin (dims j)) ℂ :=
  (frozenExteriorReindexed A₀ j Gext).submatrix Sum.inr Sum.inl

abbrev frozenSelectedD : Matrix {x : BlockGUE.Index dims // x.1 ≠ j}
    {x : BlockGUE.Index dims // x.1 ≠ j} ℂ :=
  (frozenExteriorReindexed A₀ j Gext).submatrix Sum.inr Sum.inr

/-- The four fixed blocks reconstruct the reindexed exterior matrix. -/
theorem frozenExteriorReindexed_eq_fromBlocks :
    frozenExteriorReindexed A₀ j Gext = Matrix.fromBlocks
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext) := by
  ext (x | x) (y | y) <;> rfl

/-- The fixed four-block matrix is Hermitian. -/
theorem frozenExteriorReindexed_isHermitian :
    (Matrix.fromBlocks (frozenSelectedA A₀ j Gext)
      (frozenSelectedB A₀ j Gext) (frozenSelectedC A₀ j Gext)
      (frozenSelectedD A₀ j Gext)).IsHermitian := by
  rw [← frozenExteriorReindexed_eq_fromBlocks]
  exact (publicBlockDeformation A₀
    (frozenExteriorPublicSample dims j Gext)).2.submatrix _

end FrozenBlocks

/-- With the exterior fixed, the selected projected regulated trace is
the integrand of the fixed-exterior Schur averaging theorem
`lintegral_frozenSelectedBlock_le_of_singleBlockDOS`.
-/
theorem publicBlockRegulatedSelectedTrace_split_eq_frozen {k : ℕ}
    {dims : Fin k → ℕ} (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (j : Fin k) (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (Gj : BlockProductDisintegration.SelectedSample dims j) (e eta : ℝ) :
    publicBlockRegulatedSelectedTrace A₀ j e eta
      ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) =
    ENNReal.ofReal (-(((((frozenFullRegulated
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
      (Gj ⟨j, by simp⟩).1 e eta)⁻¹).submatrix Sum.inl Sum.inl).trace).im)) := by
  unfold publicBlockRegulatedSelectedTrace
  dsimp only
  let M := (publicBlockDeformation A₀
    ((BlockProductDisintegration.split dims j).symm (Gext, Gj))).1 -
      (e : ℂ) • (1 : Matrix (BlockGUE.Index dims) (BlockGUE.Index dims) ℂ) +
      Complex.I • (eta • (1 : Matrix (BlockGUE.Index dims)
        (BlockGUE.Index dims) ℂ))
  have hp := reindexed_publicBlockDeformation_split_eq_add_selected
    A₀ j Gext Gj
  rw [frozenExteriorReindexed_eq_fromBlocks] at hp
  have hreg : M.submatrix (selectedBlockSplitEquiv dims j)
      (selectedBlockSplitEquiv dims j) = frozenFullRegulated
        (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
        (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
        (Gj ⟨j, by simp⟩).1 e eta := by
    dsimp [M]
    ext (x | x) (y | y)
    · have hxy := congrArg (fun H => H (Sum.inl x) (Sum.inl y)) hp
      simpa [frozenFullRegulated, Matrix.fromBlocks, Matrix.one_apply] using hxy
    · have hxy := congrArg (fun H => H (Sum.inl x) (Sum.inr y)) hp
      simp only [Matrix.submatrix_apply, selectedBlockSplitEquiv_inl,
        selectedBlockSplitEquiv_inr] at hxy
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, selectedBlockSplitEquiv_inl,
        selectedBlockSplitEquiv_inr]
      rw [hxy]
      have hne : (⟨j, x⟩ : BlockGUE.Index dims) ≠ y := by
        intro h
        exact y.property (congrArg Sigma.fst h).symm
      simp [frozenFullRegulated, Matrix.fromBlocks, hne]
    · have hxy := congrArg (fun H => H (Sum.inr x) (Sum.inl y)) hp
      simp only [Matrix.submatrix_apply, selectedBlockSplitEquiv_inl,
        selectedBlockSplitEquiv_inr] at hxy
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, selectedBlockSplitEquiv_inl,
        selectedBlockSplitEquiv_inr]
      rw [hxy]
      have hne : (x : BlockGUE.Index dims) ≠ ⟨j, y⟩ := by
        intro h
        exact x.property (congrArg Sigma.fst h)
      simp [frozenFullRegulated, Matrix.fromBlocks, hne]
    · have hxy := congrArg (fun H => H (Sum.inr x) (Sum.inr y)) hp
      simp only [Matrix.submatrix_apply, selectedBlockSplitEquiv_inr] at hxy
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, selectedBlockSplitEquiv_inr]
      rw [hxy]
      by_cases h : x = y
      · subst y
        simp [frozenFullRegulated, Matrix.fromBlocks]
      · have hval : (x : BlockGUE.Index dims) ≠ y := by
          intro h'
          exact h (Subtype.ext h')
        simp [frozenFullRegulated, Matrix.fromBlocks, h, hval]
  change ENNReal.ofReal
      (-((((M⁻¹).submatrix (fun a : Fin (dims j) => ⟨j, a⟩)
        (fun a : Fin (dims j) => ⟨j, a⟩)).trace).im)) = _
  rw [selected_inv_submatrix_eq_reindexed, hreg]

/-- The fixed-exterior selected-block integrand is measurable in its Hermitian
perturbation.
-/
theorem measurable_frozenSelectedBlockTrace {N : ℕ}
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin N) n ℂ)
    (C : Matrix n (Fin N) ℂ) (D : Matrix n n ℂ) (e eta : ℝ) :
    Measurable (fun V : HermitianMatrix (Fin N) => ENNReal.ofReal
      (-(((((frozenFullRegulated A B C D V.1 e eta)⁻¹).submatrix
        Sum.inl Sum.inl).trace).im))) := by
  apply Measurable.ennreal_ofReal
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  have hM : Measurable (fun V : HermitianMatrix (Fin N) =>
      frozenFullRegulated A B C D V.1 e eta) := by
    rw [Matrix.measurable_iff]
    intro i l
    rcases i with i | i <;> rcases l with l | l
    · simp only [frozenFullRegulated, Matrix.fromBlocks, Matrix.add_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
      exact ((measurable_const.add
        (measurable_subtype_coe.eval_matrix (i := i) (j := l))).sub
          measurable_const).add measurable_const
    · simp [frozenFullRegulated, Matrix.fromBlocks]
    · simp [frozenFullRegulated, Matrix.fromBlocks]
    · simp [frozenFullRegulated, Matrix.fromBlocks, Matrix.one_apply]
  have hi := Measurable.matrix_inv hM
  exact measurable_neg.comp
    (Complex.measurable_im.comp (Finset.measurable_sum Finset.univ fun i _ =>
      hi.eval_matrix (i := Sum.inl i) (j := Sum.inl i)))

/-- For every fixed exterior sample, the selected singleton average has the
sharp `π C d_j` bound.
-/
theorem lintegral_frozenExterior_selected_le_of_singleBlockDOS {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    (Gext : BlockProductDisintegration.ExteriorSample dims j)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫⁻ Gj, publicBlockRegulatedSelectedTrace A₀ j e eta
        ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
      ∂BlockProductDisintegration.selectedMeasure dims hd j) ≤
      ENNReal.ofReal (Real.pi * C₀ * dims j) := by
  let f : HermitianMatrix (Fin (dims j)) → ℝ≥0∞ := fun V => ENNReal.ofReal
    (-(((((frozenFullRegulated
      (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
      (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
      V.1 e eta)⁻¹).submatrix Sum.inl Sum.inl).trace).im))
  have hf : Measurable f := measurable_frozenSelectedBlockTrace _ _ _ _ e eta
  calc
    _ = ∫⁻ Gj, f (Gj ⟨j, by simp⟩)
        ∂BlockProductDisintegration.selectedMeasure dims hd j := by
      apply lintegral_congr
      intro Gj
      exact publicBlockRegulatedSelectedTrace_split_eq_frozen A₀ j Gext Gj e eta
    _ = ∫⁻ V, f V
        ∂(PSSSNative.BlockBand.GUE (dims j)
          (1 / (dims j : ℝ)) : Measure (HermitianMatrix (Fin (dims j)))) :=
      lintegral_selectedMeasure_eval dims hd j f hf
    _ ≤ ENNReal.ofReal (Real.pi * C₀ * dims j) := by
      exact lintegral_frozenSelectedBlock_le_of_singleBlockDOS hC₀ hDOS
        (hd j) (frozenSelectedA A₀ j Gext) (frozenSelectedB A₀ j Gext)
        (frozenSelectedC A₀ j Gext) (frozenSelectedD A₀ j Gext)
        (frozenExteriorReindexed_isHermitian A₀ j Gext) e heta

/-- **Global regulated trace bound.** Public product disintegration and the
fixed-exterior Schur estimate give the exact sharp block sum, with no lost dimension
or normalization factor.
-/
theorem lintegral_publicBlockRegulatedTrace_le_of_singleBlockDOS {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀)
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (e : ℝ)
    {eta : ℝ} (heta : 0 < eta) :
    (∫⁻ G, publicBlockRegulatedTrace A₀ e eta G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
      ENNReal.ofReal (Real.pi * C₀ * ∑ j, (dims j : ℝ)) := by
  refine (lintegral_publicBlockRegulatedTrace_le_sum_iterated
    dims hd A₀ e eta).trans ?_
  calc
    _ ≤ ∑ j : Fin k, ENNReal.ofReal (Real.pi * C₀ * dims j) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        (∫⁻ Gext, ∫⁻ Gj, publicBlockRegulatedSelectedTrace A₀ j e eta
            ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
            ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j) ≤
          ∫⁻ _Gext, ENNReal.ofReal (Real.pi * C₀ * dims j)
            ∂BlockProductDisintegration.exteriorMeasure dims hd j := by
              apply lintegral_mono
              intro Gext
              exact lintegral_frozenExterior_selected_le_of_singleBlockDOS
                hC₀ hDOS dims hd A₀ j Gext e heta
        _ = ENNReal.ofReal (Real.pi * C₀ * dims j) := by simp
    _ = ENNReal.ofReal (Real.pi * C₀ * ∑ j, (dims j : ℝ)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        rw [Finset.mul_sum]
      · intro j hj
        positivity

end PSSSNative.BlockBand.PSSS
