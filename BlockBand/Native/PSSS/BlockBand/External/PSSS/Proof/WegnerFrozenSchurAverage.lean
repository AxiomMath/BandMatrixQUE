module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.WegnerSelectedBlockSchur
public import BlockBand.Native.PSSS.BlockBand.Analysis.PositiveResolvent

/-!
# Fixed-exterior Schur separation for the public block Wegner estimate

For a Hermitian block matrix with a positive scalar regulator, the selected block of the regulated
inverse is `(V + A₀ + i (Q + η))⁻¹` with `A₀` Hermitian and `Q` positive semidefinite, obtained from
the Schur complement of the exterior block. With the single-block density of states, the GUE
average over `V` of `-Im tr` of this selected block is at most `π C₀ N`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Scalar-regulated exterior block. -/
def frozenExteriorRegulated {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) (e eta : ℝ) : Matrix n n ℂ :=
  D - (e : ℂ) • (1 : Matrix n n ℂ) +
    Complex.I • (eta • (1 : Matrix n n ℂ))

/-- Full block matrix with a selected Hermitian perturbation and scalar
regulator. -/
def frozenFullRegulated {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (V : Matrix m m ℂ) (e eta : ℝ) :
    Matrix (Sum m n) (Sum m n) ℂ :=
  Matrix.fromBlocks (A + V) B C D -
    (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ) +
    Complex.I • (eta • (1 : Matrix (Sum m n) (Sum m n) ℂ))

lemma frozenFullRegulated_eq_fromBlocks {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (V : Matrix m m ℂ) (e eta : ℝ) :
    frozenFullRegulated A B C D V e eta =
      Matrix.fromBlocks
        (A + V - (e : ℂ) • (1 : Matrix m m ℂ) +
          Complex.I • (eta • (1 : Matrix m m ℂ))) B C
        (frozenExteriorRegulated D e eta) := by
  classical
  ext (i | i) (j | j) <;>
    simp [frozenFullRegulated, frozenExteriorRegulated, Matrix.fromBlocks,
      Matrix.one_apply]

/-- A positive scalar regulator makes the fixed exterior compression
invertible pointwise.
-/
theorem isUnit_frozenExteriorRegulated {n : Type*} [Fintype n]
    [DecidableEq n] (D : Matrix n n ℂ) (hD : D.IsHermitian)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    IsUnit (frozenExteriorRegulated D e eta) := by
  apply isUnit_add_I_smul_of_posDef
  · exact hD.sub (Matrix.isHermitian_one.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal e)))
  · exact Matrix.PosDef.one.smul heta

/-- A positive scalar regulator makes the full selected-perturbation matrix
invertible for every Hermitian selected perturbation; no exceptional set is
needed. -/
theorem isUnit_frozenFullRegulated {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hH : (Matrix.fromBlocks A B C D).IsHermitian)
    (V : Matrix m m ℂ) (hV : V.IsHermitian) (e : ℝ)
    {eta : ℝ} (heta : 0 < eta) :
    IsUnit (frozenFullRegulated A B C D V e eta) := by
  let HV := Matrix.fromBlocks (A + V) B C D
  have hparts := Matrix.isHermitian_fromBlocks_iff.mp hH
  have hHV : HV.IsHermitian :=
    Matrix.IsHermitian.fromBlocks (hparts.1.add hV) hparts.2.1 hparts.2.2.2
  apply isUnit_add_I_smul_of_posDef
  · exact hHV.sub (Matrix.isHermitian_one.smul
      (isSelfAdjoint_iff.mpr (Complex.conj_ofReal e)))
  · exact Matrix.PosDef.one.smul heta

/-- **Fixed-exterior Schur separation.** The selected block of every regulated inverse
is a resolvent of `V + A₀` with one fixed positive-semidefinite absorber `Q`.
Both `A₀` and `Q` depend only on the fixed exterior/background data, never on
`V`.
-/
theorem exists_frozenSchur_background_absorber {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hH : (Matrix.fromBlocks A B C D).IsHermitian)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ (A₀ Q : Matrix m m ℂ), A₀.IsHermitian ∧ Q.PosSemidef ∧
      ∀ (V : Matrix m m ℂ), V.IsHermitian →
      ((frozenFullRegulated A B C D V e eta)⁻¹).submatrix
          Sum.inl Sum.inl =
        (V + A₀ + Complex.I •
          (Q + eta • (1 : Matrix m m ℂ)))⁻¹ := by
  let Ar : Matrix m m ℂ :=
    A - (e : ℂ) • (1 : Matrix m m ℂ) +
      Complex.I • (eta • (1 : Matrix m m ℂ))
  let Dr := frozenExteriorRegulated D e eta
  have hparts := Matrix.isHermitian_fromBlocks_iff.mp hH
  have hDu : IsUnit Dr := isUnit_frozenExteriorRegulated D hparts.2.2.2 e heta
  let _ : Invertible Dr := hDu.invertible
  let S := schurComplement₂₂ Ar B C Dr
  let A₀ := matrixHermitianPart S
  let Q := matrixImaginaryPart S - (eta : ℂ) • (1 : Matrix m m ℂ)
  have hzeroU : IsUnit (frozenFullRegulated A B C D 0 e eta) :=
    isUnit_frozenFullRegulated A B C D hH 0 Matrix.isHermitian_zero e heta
  let _ : Invertible (frozenFullRegulated A B C D 0 e eta) := hzeroU.invertible
  have hshape0 : frozenFullRegulated A B C D 0 e eta =
      Matrix.fromBlocks Ar B C Dr := by
    simpa [Ar, Dr] using
      frozenFullRegulated_eq_fromBlocks A B C D 0 e eta
  let _ : Invertible (Matrix.fromBlocks Ar B C Dr) := by
    rw [← hshape0]
    infer_instance
  have him : (matrixImaginaryPart (Matrix.fromBlocks Ar B C Dr) -
      (eta : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef := by
    rw [← hshape0]
    have hbase : (Matrix.fromBlocks A B C D -
        (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).IsHermitian :=
      hH.sub (Matrix.isHermitian_one.smul
        (isSelfAdjoint_iff.mpr (Complex.conj_ofReal e)))
    rw [show frozenFullRegulated A B C D 0 e eta =
        (Matrix.fromBlocks A B C D -
          (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)) +
          Complex.I • (eta • (1 : Matrix (Sum m n) (Sum m n) ℂ)) by
      ext (i | i) (j | j) <;> simp [frozenFullRegulated, Matrix.fromBlocks]]
    change (matrixImaginaryPart
      ((Matrix.fromBlocks A B C D -
        (e : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)) +
        Complex.I • ((eta : ℂ) •
          (1 : Matrix (Sum m n) (Sum m n) ℂ))) -
      (eta : ℂ) • (1 : Matrix (Sum m n) (Sum m n) ℂ)).PosSemidef
    rw [matrixImaginaryPart_add_I_smul _ _ hbase
      (Matrix.isHermitian_one.smul
        (isSelfAdjoint_iff.mpr (Complex.conj_ofReal eta)))]
    simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Sum m n) (Sum m n) ℂ).PosSemidef)
  have hQ : Q.PosSemidef := by
    dsimp [Q, S]
    exact (exposedBlock_trace_eq_schur_and_regulator_posSemidef
      Ar B C Dr heta.le him).2
  refine ⟨A₀, Q, matrixHermitianPart_isHermitian S, hQ, ?_⟩
  intro V hV
  have hVU : IsUnit (frozenFullRegulated A B C D V e eta) :=
    isUnit_frozenFullRegulated A B C D hH V hV e heta
  let _ : Invertible (frozenFullRegulated A B C D V e eta) := hVU.invertible
  have hshapeV : frozenFullRegulated A B C D V e eta =
      Matrix.fromBlocks (Ar + V) B C Dr := by
    rw [frozenFullRegulated_eq_fromBlocks]
    congr 1
    dsimp [Ar]
    noncomm_ring
  let _ : Invertible (Matrix.fromBlocks (Ar + V) B C Dr) := by
    rw [← hshapeV]
    infer_instance
  rw [hshapeV, nonsing_inv_fromBlocks_submatrix₁₁_eq_schurComplement₂₂]
  congr 1
  have hS : schurComplement₂₂ (Ar + V) B C Dr = V + S := by
    simp [schurComplement₂₂, S]
    noncomm_ring
  have hSA : S = A₀ + Complex.I •
      (Q + eta • (1 : Matrix m m ℂ)) := by
    rw [show S = A₀ + Complex.I • matrixImaginaryPart S from
      matrix_eq_hermitianPart_add_I_imaginaryPart S]
    congr 2
    simp [Q]
  rw [hS, hSA]
  abel

/-- **Conditioned selected-block averaging.** After arbitrary exterior blocks
and couplings are fixed, averaging only the selected public normalized GUE
block bounds its projected negative-imaginary resolvent trace by `π C N`.
This is the exact one-block estimate needed before summing the block traces.
-/
theorem lintegral_frozenSelectedBlock_le_of_singleBlockDOS {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hDOS : SingleBlockDOS C₀) {N : ℕ} (hN : 0 < N)
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin N) n ℂ)
    (C : Matrix n (Fin N) ℂ) (D : Matrix n n ℂ)
    (hH : (Matrix.fromBlocks A B C D).IsHermitian)
    (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫⁻ V : HermitianMatrix (Fin N), ENNReal.ofReal
      (-(((((frozenFullRegulated A B C D V.1 e eta)⁻¹).submatrix
        Sum.inl Sum.inl).trace).im))
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) ≤
      ENNReal.ofReal (Real.pi * C₀ * N) := by
  obtain ⟨A₀, Q, hA₀, hQ, hsep⟩ :=
    exists_frozenSchur_background_absorber A B C D hH e heta
  have hbound := lintegral_publicGUE_absorbedTrace_le_of_singleBlockDOS
    hC₀ hDOS hN ⟨A₀, hA₀⟩ Q hQ heta
  calc
    (∫⁻ V : HermitianMatrix (Fin N), ENNReal.ofReal
      (-(((((frozenFullRegulated A B C D V.1 e eta)⁻¹).submatrix
        Sum.inl Sum.inl).trace).im))
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) =
      ∫⁻ V : HermitianMatrix (Fin N),
        ENNReal.ofReal (publicGUEAbsorbedTrace ⟨A₀, hA₀⟩ V Q eta)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N))) := by
      apply lintegral_congr
      intro V
      rw [hsep V.1 V.2]
      congr 4
      abel
    _ ≤ ENNReal.ofReal (Real.pi * C₀ * N) := hbound

end PSSSNative.BlockBand.PSSS
