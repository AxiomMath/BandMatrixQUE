module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedLaw
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEExistence

/-!
# Deterministic MDE bridge for the replicated CEH dimension

A deformation spectrum is repeated in the tensor coordinate and flattened to
`Fin (N*d)`.  Its normalized scalar Dyson equation is exactly the original
one.  Consequently the unconditional upper solution is unchanged, while the
diagonal deformation, MDE pencil, and MDE matrix become Kronecker
replicates after reindexing to `Fin N × Fin d`.  All statements below are
finite-dimensional identities; no random-matrix estimate is asserted.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate
open PencilAdapter

/-- The paper's repeated deformation spectrum, on the tensor index. -/
def replicatedSpectrumOn {N : ℕ} (d : ℕ) (f : Spectrum N) :
    Fin N × Fin d → ℝ := fun p => f p.1

/-- The same repeated spectrum in the flattened `Fin (N*d)` convention used
by the scalar MDE API. -/
def replicatedSpectrum {N : ℕ} (d : ℕ) (f : Spectrum N) :
    Spectrum (N * d) := fun k => replicatedSpectrumOn d f
      (replicatedIndexEquiv N d k)

@[simp] theorem replicatedSpectrum_at_equiv {N d : ℕ} (f : Spectrum N)
    (p : Fin N × Fin d) :
    replicatedSpectrum d f ((replicatedIndexEquiv N d).symm p) = f p.1 := by
  simp [replicatedSpectrum, replicatedSpectrumOn, replicatedIndexEquiv]

/-- Repeating a function in the tensor coordinate does not change its
normalized average. -/
theorem replicated_average {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (a : Fin N → ℂ) :
    CEHNative.BlockBand.CEH.average
      (fun k : Fin (N * d) => a (replicatedIndexEquiv N d k).1) =
    CEHNative.BlockBand.CEH.average a := by
  unfold CEHNative.BlockBand.CEH.average
  rw [← (replicatedIndexEquiv N d).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp
  rw [Finset.mul_sum]

/-- Scalar MDE entries repeat exactly in the tensor coordinate. -/
@[simp] theorem replicated_entry_at_equiv {N d : ℕ} (f : Spectrum N)
    (s : ℝ) (z m : ℂ) (p : Fin N × Fin d) :
    CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m
        ((replicatedIndexEquiv N d).symm p) =
      CEHNative.BlockBand.CEH.entry f s z m p.1 := by
  simp [CEHNative.BlockBand.CEH.entry]

/-- The repeated scalar Dyson equation is equivalent to the original one at a
positive replication size. -/
theorem replicated_isSolution_iff {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) (s : ℝ) (z m : ℂ) :
    CEHNative.BlockBand.CEH.IsSolution
        (replicatedSpectrum d f) s z m ↔
      CEHNative.BlockBand.CEH.IsSolution f s z m := by
  unfold CEHNative.BlockBand.CEH.IsSolution
  have havg : CEHNative.BlockBand.CEH.average
      (CEHNative.BlockBand.CEH.entry (replicatedSpectrum d f) s z m) =
      CEHNative.BlockBand.CEH.average
        (CEHNative.BlockBand.CEH.entry f s z m) := by
    calc
      _ = CEHNative.BlockBand.CEH.average
          (fun k : Fin (N * d) =>
            CEHNative.BlockBand.CEH.entry f s z m
              (replicatedIndexEquiv N d k).1) := by
            congr 1
      _ = _ := replicated_average hN hd _
  rw [havg]

/-- The unconditional upper solution is invariant under finite replication. -/
theorem replicated_upperSolution {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (f : Spectrum N) {s : ℝ} (hs : 0 < s) (z : ℂ) (hz : 0 < z.im) :
    CEHNative.BlockBand.CEH.upperSolution (Nat.mul_pos hN hd)
        (replicatedSpectrum d f) hs z hz =
      CEHNative.BlockBand.CEH.upperSolution hN f hs z hz := by
  symm
  apply CEHNative.BlockBand.CEH.eq_upperSolution
    (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs hz
  exact (replicated_isSolution_iff hN hd f s z _).2
    (CEHNative.BlockBand.CEH.upperSolution_isSolution
      hN f hs z hz)

/-- The replicated diagonal deformation is `F ⊗ I_d` after
reindexing to the tensor coordinate. -/
theorem reindex_deformationMatrix_replicated {N d : ℕ} (f : Spectrum N) :
    Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (deformationMatrix (replicatedSpectrum d f)) =
      tensorReplicate d (deformationMatrix f) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [deformationMatrix, tensorReplicate, Matrix.kronecker,
      Matrix.reindex_apply, replicatedSpectrum_at_equiv]
  · have he : (replicatedIndexEquiv N d).symm p ≠
        (replicatedIndexEquiv N d).symm q := fun h => hpq
          ((replicatedIndexEquiv N d).symm.injective h)
    have hor : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
      by_cases hfirst : p.1 = q.1
      · right
        intro hsecond
        exact hpq (Prod.ext hfirst hsecond)
      · exact Or.inl hfirst
    rcases hor with hfirst | hsecond
    · simp [deformationMatrix, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hfirst]
    · simp [deformationMatrix, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hsecond]

/-- The deterministic MDE pencil tensor-replicates for every proposed scalar
mean. -/
theorem reindex_mdePencil_replicated {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ) :
    Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdePencil (replicatedSpectrum d f) lambda z m) =
      tensorReplicate d (mdePencil f lambda z m) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [mdePencil, tensorReplicate, Matrix.kronecker,
      Matrix.reindex_apply, replicatedSpectrum_at_equiv]
  · have he : (replicatedIndexEquiv N d).symm p ≠
        (replicatedIndexEquiv N d).symm q := fun h => hpq
          ((replicatedIndexEquiv N d).symm.injective h)
    have hor : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
      by_cases hfirst : p.1 = q.1
      · right
        intro hsecond
        exact hpq (Prod.ext hfirst hsecond)
      · exact Or.inl hfirst
    rcases hor with hfirst | hsecond
    · simp [mdePencil, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hfirst]
    · simp [mdePencil, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hsecond]

/-- The deterministic MDE matrix tensor-replicates for every proposed scalar
mean. -/
theorem reindex_mdeMatrix_replicated {N d : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ) :
    Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z m) =
      tensorReplicate d (mdeMatrix f lambda z m) := by
  ext p q
  by_cases hpq : p = q
  · subst q
    simp [mdeMatrix, tensorReplicate, Matrix.kronecker,
      Matrix.reindex_apply, replicated_entry_at_equiv]
  · have he : (replicatedIndexEquiv N d).symm p ≠
        (replicatedIndexEquiv N d).symm q := fun h => hpq
          ((replicatedIndexEquiv N d).symm.injective h)
    have hor : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
      by_cases hfirst : p.1 = q.1
      · right
        intro hsecond
        exact hpq (Prod.ext hfirst hsecond)
      · exact Or.inl hfirst
    rcases hor with hfirst | hsecond
    · simp [mdeMatrix, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hfirst]
    · simp [mdeMatrix, tensorReplicate, Matrix.kronecker,
        Matrix.reindex_apply, he, hsecond]

/-- In particular, the replicated upper-branch MDE matrix is exactly the tensor
replicate of the original upper-branch matrix. -/
theorem reindex_mdeMatrix_replicated_upperSolution
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda) (z : ℂ) (hz : 0 < z.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z
          (CEHNative.BlockBand.CEH.upperSolution
            (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs z hz)) =
      tensorReplicate d
        (mdeMatrix f lambda z
          (CEHNative.BlockBand.CEH.upperSolution hN f hs z hz)) := by
  dsimp only
  rw [replicated_upperSolution hN hd]
  exact reindex_mdeMatrix_replicated f lambda z _

/-- Normalized traces of replicated MDE matrices agree exactly. -/
theorem productNTrace_reindex_mdeMatrix_replicated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ) :
    productNTrace
        (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
          (mdeMatrix (replicatedSpectrum d f) lambda z m)) =
      NTrace (mdeMatrix f lambda z m) := by
  rw [reindex_mdeMatrix_replicated]
  exact productNTrace_tensorReplicate hN hd _

/-- The normalized trace of a product of two replicated MDE matrices agrees
with the original normalized trace. -/
theorem productNTrace_reindex_mdeMatrix_mul_replicated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (z₁ m₁ z₂ m₂ : ℂ) :
    productNTrace
      (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
          (mdeMatrix (replicatedSpectrum d f) lambda z₁ m₁) *
       Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
          (mdeMatrix (replicatedSpectrum d f) lambda z₂ m₂)) =
      NTrace (mdeMatrix f lambda z₁ m₁ * mdeMatrix f lambda z₂ m₂) := by
  rw [reindex_mdeMatrix_replicated, reindex_mdeMatrix_replicated,
    ← tensorReplicate_mul]
  exact productNTrace_tensorReplicate hN hd _

/-- Hence the two-body stability denominator is exactly invariant under
replication. -/
theorem stabilityDenominator_reindex_mdeMatrix_replicated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (z₁ m₁ z₂ m₂ : ℂ) :
    stabilityDenominator (lambda : ℂ)
      (productNTrace
        (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
            (mdeMatrix (replicatedSpectrum d f) lambda z₁ m₁) *
         Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
            (mdeMatrix (replicatedSpectrum d f) lambda z₂ m₂))) =
    stabilityDenominator (lambda : ℂ)
      (NTrace (mdeMatrix f lambda z₁ m₁ * mdeMatrix f lambda z₂ m₂)) := by
  rw [productNTrace_reindex_mdeMatrix_mul_replicated hN hd]

/-- The deterministic two-resolvent comparison constructed from replicated
MDE matrices is itself the tensor replicate of the original one. -/
theorem productTwoResolventApprox_reindex_mdeMatrix_replicated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ m₁ z₂ m₂ : ℂ) :
    productTwoResolventApprox (lambda : ℂ)
      (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z₁ m₁))
      (tensorReplicate d A)
      (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z₂ m₂)) =
    tensorReplicate d
      (twoResolventApprox (lambda : ℂ)
        (mdeMatrix f lambda z₁ m₁) A (mdeMatrix f lambda z₂ m₂)) := by
  rw [reindex_mdeMatrix_replicated, reindex_mdeMatrix_replicated]
  exact productTwoResolventApprox_tensorReplicate hN hd _ _ _ _

/-- The preceding deterministic comparison specializes to the unconditional
upper solutions at dimensions `N` and `N*d`, with no additional input. -/
theorem productTwoResolventApprox_replicated_upperSolution
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let mr₁ := CEHNative.BlockBand.CEH.upperSolution
      (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs z₁ hz₁
    let mr₂ := CEHNative.BlockBand.CEH.upperSolution
      (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs z₂ hz₂
    let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₂ hz₂
    productTwoResolventApprox (lambda : ℂ)
      (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z₁ mr₁))
      (tensorReplicate d A)
      (Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
        (mdeMatrix (replicatedSpectrum d f) lambda z₂ mr₂)) =
    tensorReplicate d
      (twoResolventApprox (lambda : ℂ)
        (mdeMatrix f lambda z₁ m₁) A (mdeMatrix f lambda z₂ m₂)) := by
  dsimp only
  rw [replicated_upperSolution hN hd, replicated_upperSolution hN hd]
  exact productTwoResolventApprox_reindex_mdeMatrix_replicated
    hN hd f lambda A z₁ _ z₂ _

/-- The deterministic positive-chain comparison for the replicated upper MDE
matrices reduces exactly to the four ordinary adjoint constellations. -/
theorem productNTrace_replicated_upperMDE_positiveChain_eq_fourfold
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (A : Matrix (Fin N) (Fin N) ℂ)
    (z₁ z₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) :
    let hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambda
    let mr₁ := CEHNative.BlockBand.CEH.upperSolution
      (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs z₁ hz₁
    let mr₂ := CEHNative.BlockBand.CEH.upperSolution
      (Nat.mul_pos hN hd) (replicatedSpectrum d f) hs z₂ hz₂
    let m₁ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₁ hz₁
    let m₂ := CEHNative.BlockBand.CEH.upperSolution hN f hs z₂ hz₂
    let MR₁ := Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
      (mdeMatrix (replicatedSpectrum d f) lambda z₁ mr₁)
    let MR₂ := Matrix.reindex (replicatedIndexEquiv N d) (replicatedIndexEquiv N d)
      (mdeMatrix (replicatedSpectrum d f) lambda z₂ mr₂)
    let M₁ := mdeMatrix f lambda z₁ m₁
    let M₂ := mdeMatrix f lambda z₂ m₂
    productNTrace
      (CEHNative.BlockBand.matrixImaginaryPart MR₁ * tensorReplicate d A *
        CEHNative.BlockBand.matrixImaginaryPart MR₂ *
        (tensorReplicate d A)ᴴ) =
      NTrace ((-(1 / 4 : ℂ)) •
        (M₁ * A * M₂ * Aᴴ + M₁ᴴ * A * M₂ᴴ * Aᴴ -
          M₁ * A * M₂ᴴ * Aᴴ - M₁ᴴ * A * M₂ * Aᴴ)) := by
  dsimp only
  rw [replicated_upperSolution hN hd, replicated_upperSolution hN hd,
    reindex_mdeMatrix_replicated, reindex_mdeMatrix_replicated]
  exact productNTrace_replicated_positiveChain_eq_fourfold hN hd _ _ _

end CEHNative.BlockBand.External.CEH
