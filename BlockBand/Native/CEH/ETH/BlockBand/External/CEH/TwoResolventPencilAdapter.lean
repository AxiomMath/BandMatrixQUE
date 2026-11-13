module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventObservables
public import BlockBand.Native.CEH.BlockBand.External.CEH.MDE

/-!
# Concrete CEH MDE and resolvent pencils

This module connects the scalar finite-dimensional CEH MDE to the matrix
pencils used by the exact two-resolvent identities.  The coupling `lambda` is
real and nonnegative, the self-energy is `lambda ^ 2`, and the deformation and
noise matrices are Hermitian.  The lower-half-plane objects are obtained by
conjugate transpose, rather than postulated independently.

The final four theorems are the `++`, `+-`, `-+`, and `--` versions of the
exact algebraic identity CEH (5.20).  They contain no local-law estimate,
stochastic domination, Gaussian integration by parts, or assumption packaging
CEH Lemma 5.6.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix
open scoped BigOperators ComplexConjugate

namespace PencilAdapter

abbrev Spectrum (N : ℕ) := CEHNative.BlockBand.CEH.DeformationSpectrum N

/-- The diagonal deterministic deformation with eigenvalues `f`. -/
def deformationMatrix {N : ℕ} (f : Spectrum N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => (f i : ℂ)

/-- The matrix MDE solution whose diagonal entries solve the scalar CEH MDE. -/
def mdeMatrix {N : ℕ} (f : Spectrum N) (lambda : ℝ) (z m : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (CEHNative.BlockBand.CEH.entry f (lambda ^ 2) z m)

/-- The inverse MDE pencil `H₀-z-λ²m`. -/
def mdePencil {N : ℕ} (f : Spectrum N) (lambda : ℝ) (z m : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i =>
    (f i : ℂ) - z - ((lambda ^ 2 : ℝ) : ℂ) * m

/-- The random Hermitian matrix `H₀+λW`. -/
def deformedMatrix {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (W : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  deformationMatrix f + (lambda : ℂ) • W

/-- CEH's random inverse pencil `H₀+λW-z`. -/
def resolventPencil {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (W : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  deformedMatrix f lambda W - z • (1 : Matrix (Fin N) (Fin N) ℂ)

/-- CEH's resolvent `(H₀+λW-z)⁻¹`. -/
def resolvent {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (W : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (resolventPencil f lambda W z)⁻¹

/-- Upper spectral parameter `E+iη`. -/
def plusParameter (E eta : ℝ) : ℂ := (E : ℂ) + Complex.I * eta

/-- Lower spectral parameter `E-iη`. -/
def minusParameter (E eta : ℝ) : ℂ := (E : ℂ) - Complex.I * eta

@[simp] theorem star_plusParameter (E eta : ℝ) :
    star (plusParameter E eta) = minusParameter E eta := by
  apply Complex.ext <;> simp [plusParameter, minusParameter]

/-- The diagonal deformation is Hermitian. -/
theorem deformationMatrix_isHermitian {N : ℕ} (f : Spectrum N) :
    (deformationMatrix f).IsHermitian := by
  rw [Matrix.IsHermitian, deformationMatrix, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- A real coupling preserves Hermiticity of the deformed matrix. -/
theorem deformedMatrix_isHermitian {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian) :
    (deformedMatrix f lambda W).IsHermitian := by
  exact (deformationMatrix_isHermitian f).add
    (hW.smul (RCLike.conj_ofReal lambda))

/-- The scalar MDE equation identifies the normalized trace of its diagonal
matrix lift with the scalar mean. -/
theorem NTrace_mdeMatrix {N : ℕ} (hN : 0 < N) (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ)
    (hm : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z m) :
    NTrace (mdeMatrix f lambda z m) = m := by
  calc
    NTrace (mdeMatrix f lambda z m) =
        CEHNative.BlockBand.CEH.average
          (CEHNative.BlockBand.CEH.entry f (lambda ^ 2) z m) := by
      rw [mdeMatrix]
      unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
        CEHNative.BlockBand.CEH.average
      rw [Matrix.trace_diagonal]
      have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp
    _ = m := hm.1.symm

/-- The lifted scalar MDE matrix is a left inverse of its concrete pencil. -/
theorem mdeMatrix_mul_mdePencil {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (z m : ℂ)
    (hz : 0 < z.im) (hm : 0 < m.im) :
    mdeMatrix f lambda z m * mdePencil f lambda z m = 1 := by
  have hheight : 0 < CEHNative.BlockBand.CEH.effectiveHeight
      (lambda ^ 2) z m := by
    unfold CEHNative.BlockBand.CEH.effectiveHeight
    exact add_pos_of_pos_of_nonneg hz
      (mul_nonneg (pow_nonneg hlambda 2) hm.le)
  ext i j
  by_cases hij : i = j
  · subst j
    have hne := CEHNative.BlockBand.CEH.denominator_ne_zero f hheight i
    change (↑(f i) - z - (↑(lambda ^ 2) : ℂ) * m) ≠ 0 at hne
    push_cast at hne
    simp [mdeMatrix, mdePencil, CEHNative.BlockBand.CEH.entry, hne]
  · simp [mdeMatrix, mdePencil, hij]

/-- The random pencil is invertible away from the real axis. -/
theorem isUnit_det_resolventPencil {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (resolventPencil f lambda W z).det := by
  let H := deformedMatrix f lambda W
  have hH : H.IsHermitian := deformedMatrix_isHermitian f lambda W hW
  have hu := CEHNative.BlockBand.isUnit_resolventPencil H hH hz
  have hpencil : resolventPencil f lambda W z =
      -(z • (1 : Matrix (Fin N) (Fin N) ℂ) - H) := by
    simp [resolventPencil, H]
  rw [hpencil]
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    ((IsUnit.neg_iff (z • (1 : Matrix (Fin N) (Fin N) ℂ) - H)).2
      hu)

/-- The concrete resolvent is a right inverse of its random pencil. -/
theorem resolventPencil_mul_resolvent {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    resolventPencil f lambda W z * resolvent f lambda W z = 1 := by
  exact Matrix.mul_nonsing_inv _
    (isUnit_det_resolventPencil f lambda W hW hz)

/-- Exact difference between the MDE and random inverse pencils. -/
theorem mdePencil_sub_resolventPencil {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (W : Matrix (Fin N) (Fin N) ℂ)
    (z m : ℂ)
    (hm : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z m) :
    mdePencil f lambda z m - resolventPencil f lambda W z =
      (-(lambda : ℂ)) • W -
        ((lambda : ℂ) ^ 2 * NTrace (mdeMatrix f lambda z m)) •
          (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [NTrace_mdeMatrix hN f lambda z m hm]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [mdePencil, resolventPencil, deformedMatrix, deformationMatrix]
    ring
  · simp [mdePencil, resolventPencil, deformedMatrix, deformationMatrix, hij]

/-- MDE matrices at conjugate spectral data are conjugate transposes. -/
theorem mdeMatrix_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ) :
    (mdeMatrix f lambda z m)ᴴ = mdeMatrix f lambda (star z) (star m) := by
  rw [mdeMatrix, mdeMatrix, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp [CEHNative.BlockBand.CEH.entry]

/-- MDE inverse pencils obey the same adjoint relation. -/
theorem mdePencil_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z m : ℂ) :
    (mdePencil f lambda z m)ᴴ = mdePencil f lambda (star z) (star m) := by
  rw [mdePencil, mdePencil, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

/-- Random pencils at conjugate spectral parameters are adjoints. -/
theorem resolventPencil_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z : ℂ) :
    (resolventPencil f lambda W z)ᴴ =
      resolventPencil f lambda W (star z) := by
  rw [resolventPencil, resolventPencil, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul]
  rw [(deformedMatrix_isHermitian f lambda W hW).eq]
  simp

/-- Resolvents at conjugate spectral parameters are adjoints. -/
theorem resolvent_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z : ℂ) :
    (resolvent f lambda W z)ᴴ = resolvent f lambda W (star z) := by
  rw [resolvent, resolvent, Matrix.conjTranspose_nonsing_inv,
    resolventPencil_conjTranspose f lambda W hW z]

/-- Explicit plus/minus form of the MDE-matrix adjoint relation. -/
theorem mdeMatrix_plus_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda E eta : ℝ) (m : ℂ) :
    (mdeMatrix f lambda (plusParameter E eta) m)ᴴ =
      mdeMatrix f lambda (minusParameter E eta) (star m) := by
  rw [mdeMatrix_conjTranspose, star_plusParameter]

/-- Explicit plus/minus form of the MDE-pencil adjoint relation. -/
theorem mdePencil_plus_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda E eta : ℝ) (m : ℂ) :
    (mdePencil f lambda (plusParameter E eta) m)ᴴ =
      mdePencil f lambda (minusParameter E eta) (star m) := by
  rw [mdePencil_conjTranspose, star_plusParameter]

/-- Explicit plus/minus form of the random-resolvent adjoint relation. -/
theorem resolvent_plus_conjTranspose {N : ℕ} (f : Spectrum N)
    (lambda E eta : ℝ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W.IsHermitian) :
    (resolvent f lambda W (plusParameter E eta))ᴴ =
      resolvent f lambda W (minusParameter E eta) := by
  rw [resolvent_conjTranspose f lambda W hW, star_plusParameter]

/-- Normalized trace commutes with conjugate transpose. -/
theorem NTrace_conjTranspose {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    NTrace Xᴴ = star (NTrace X) := by
  unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
  rw [Matrix.trace_conjTranspose]
  simp

/-- The normalized trace of two lifted MDE matrices is the scalar normalized
pairing of their diagonal entries. -/
theorem NTrace_mdeMatrix_mul {N : ℕ} (f : Spectrum N)
    (lambda : ℝ) (z₁ m₁ z₂ m₂ : ℂ) :
    NTrace (mdeMatrix f lambda z₁ m₁ * mdeMatrix f lambda z₂ m₂) =
      CEHNative.BlockBand.CEH.average (fun i =>
        CEHNative.BlockBand.CEH.entry f (lambda ^ 2) z₁ m₁ i *
          CEHNative.BlockBand.CEH.entry f (lambda ^ 2) z₂ m₂ i) := by
  unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
    CEHNative.BlockBand.CEH.average mdeMatrix
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  ring

@[simp] theorem mdeEntry_star {N : ℕ} (f : Spectrum N)
    (s : ℝ) (z m : ℂ) (i : Fin N) :
    CEHNative.BlockBand.CEH.entry f s (star z) (star m) i =
      star (CEHNative.BlockBand.CEH.entry f s z m i) := by
  simp [CEHNative.BlockBand.CEH.entry]

theorem average_star {N : ℕ} (a : Fin N → ℂ) :
    CEHNative.BlockBand.CEH.average (fun i => star (a i)) =
      star (CEHNative.BlockBand.CEH.average a) := by
  unfold CEHNative.BlockBand.CEH.average
  simp

/-- The four matrix adjoint constellations have nonvanishing concrete MDE
stability denominators.  This uses the already-proved scalar MDE norm
inequality, not a probabilistic or local-law assumption. -/
theorem constellation_stability_ne_zero {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (c₁ c₂ : AdjointChoice) :
    stabilityDenominator (lambda : ℂ)
      (NTrace (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
        chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))) ≠ 0 := by
  by_cases hzero : lambda = 0
  · subst lambda
    simp [stabilityDenominator]
  have hlambdaPos : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hzero)
  have hs : 0 < lambda ^ 2 := sq_pos_of_pos hlambdaPos
  have hlt : lambda ^ 2 *
      ‖NTrace (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
        chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))‖ < 1 := by
    cases c₁ <;> cases c₂
    · simpa [chooseAdjoint, NTrace_mdeMatrix_mul] using
        (CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
          hN f hs hz₁ hz₂ hm₁ hm₂ false)
    · simp only [chooseAdjoint_plain, chooseAdjoint_adjoint]
      rw [mdeMatrix_conjTranspose, NTrace_mdeMatrix_mul]
      simp_rw [mdeEntry_star]
      simpa using
        (CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
          hN f hs hz₁ hz₂ hm₁ hm₂ true)
    · have h := CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
          hN f hs hz₂ hz₁ hm₂ hm₁ true
      simp only [chooseAdjoint_plain, chooseAdjoint_adjoint]
      rw [mdeMatrix_conjTranspose, NTrace_mdeMatrix_mul]
      simp_rw [mdeEntry_star]
      simpa [mul_comm] using h
    · have h := CEHNative.BlockBand.CEH.mixed_average_norm_lt_inv
          hN f hs hz₁ hz₂ hm₁ hm₂ false
      simp only [chooseAdjoint_adjoint]
      rw [mdeMatrix_conjTranspose, mdeMatrix_conjTranspose,
        NTrace_mdeMatrix_mul]
      simp_rw [mdeEntry_star]
      rw [show (fun i =>
          star (CEHNative.BlockBand.CEH.entry
            f (lambda ^ 2) z₁ m₁ i) *
          star (CEHNative.BlockBand.CEH.entry
            f (lambda ^ 2) z₂ m₂ i)) =
          (fun i => star
            (CEHNative.BlockBand.CEH.entry
              f (lambda ^ 2) z₁ m₁ i *
             CEHNative.BlockBand.CEH.entry
              f (lambda ^ 2) z₂ m₂ i)) by
            funext i
            simp]
      rw [average_star, norm_star]
      simpa using h
  intro hden
  have heq :
      (lambda : ℂ) ^ 2 *
        NTrace (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
          chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂)) = 1 := by
    simpa [stabilityDenominator] using (sub_eq_zero.mp hden).symm
  have hnorm := congrArg norm heq
  rw [norm_mul, norm_one] at hnorm
  have hpowNorm : ‖(lambda : ℂ) ^ 2‖ = lambda ^ 2 := by
    rw [norm_pow]
    simp [abs_of_nonneg hlambda]
  rw [hpowNorm] at hnorm
  nlinarith

/-- The exact CEH MDE/resolvent premises hold simultaneously for the upper
objects and their lower-half-plane adjoints. -/
theorem constellation_pencil_premises {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z m : ℂ) (hz : 0 < z.im)
    (hm : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z m)
    (c : AdjointChoice) :
    chooseAdjoint c (mdeMatrix f lambda z m) *
        chooseAdjoint c (mdePencil f lambda z m) = 1 ∧
      chooseAdjoint c (resolventPencil f lambda W z) *
        chooseAdjoint c (resolvent f lambda W z) = 1 ∧
      chooseAdjoint c (mdePencil f lambda z m) -
          chooseAdjoint c (resolventPencil f lambda W z) =
        (-(lambda : ℂ)) • W -
          ((lambda : ℂ) ^ 2 * NTrace (chooseAdjoint c (mdeMatrix f lambda z m))) •
            (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hMQ := mdeMatrix_mul_mdePencil f lambda hlambda z m hz hm.2
  have hPG := resolventPencil_mul_resolvent f lambda W hW (ne_of_gt hz)
  have hD := mdePencil_sub_resolventPencil hN f lambda W z m hm
  cases c with
  | plain => exact ⟨hMQ, hPG, hD⟩
  | adjoint =>
      constructor
      · have h := congrArg Matrix.conjTranspose hMQ
        have h' := (mul_eq_one_comm.mp
          (by simpa [Matrix.conjTranspose_mul] using h))
        simpa [chooseAdjoint] using h'
      constructor
      · have h := congrArg Matrix.conjTranspose hPG
        have h' := (mul_eq_one_comm.mp
          (by simpa [Matrix.conjTranspose_mul] using h))
        simpa [chooseAdjoint] using h'
      · have hDc := congrArg Matrix.conjTranspose hD
        simpa [chooseAdjoint, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
          hW.eq, NTrace_conjTranspose] using hDc

/-- Proposition asserting the exact CEH underlined identity for a chosen
adjoint constellation. -/
def ConcreteBasicIdentity {N : ℕ} (f : Spectrum N) (lambda : ℝ)
    (W : Matrix (Fin N) (Fin N) ℂ) (z₁ m₁ z₂ m₂ : ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (c₁ c₂ : AdjointChoice) : Prop :=
    twoBodyStability (lambda : ℂ)
        (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁))
        (chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))
        (chooseAdjoint c₁ (resolvent f lambda W z₁) * A *
          chooseAdjoint c₂ (resolvent f lambda W z₂) -
          twoResolventApprox (lambda : ℂ)
            (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁)) A
            (chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))) =
      chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) * A *
          (chooseAdjoint c₂ (resolvent f lambda W z₂) -
            chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂)) -
        chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
          underlinedTwoResolventWord (lambda : ℂ) W
            (chooseAdjoint c₁ (resolvent f lambda W z₁)) A
            (chooseAdjoint c₂ (resolvent f lambda W z₂)) +
        ((lambda : ℂ) ^ 2 * NTrace
          (chooseAdjoint c₁ (resolvent f lambda W z₁) * A *
            chooseAdjoint c₂ (resolvent f lambda W z₂))) •
          (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
            (chooseAdjoint c₂ (resolvent f lambda W z₂) -
              chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))) +
        ((lambda : ℂ) ^ 2 * NTrace
          (chooseAdjoint c₁ (resolvent f lambda W z₁) -
            chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁))) •
          (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁) *
            chooseAdjoint c₁ (resolvent f lambda W z₁) * A *
            chooseAdjoint c₂ (resolvent f lambda W z₂))

/-- Both adjoint choices satisfy the exact CEH underlined basic identity. -/
theorem concrete_basicIdentity {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (A : Matrix (Fin N) (Fin N) ℂ) (c₁ c₂ : AdjointChoice) :
    ConcreteBasicIdentity f lambda W z₁ m₁ z₂ m₂ A c₁ c₂ := by
  obtain ⟨hMQ, hPG, hD⟩ :=
    constellation_pencil_premises hN f lambda hlambda W hW z₁ m₁ hz₁ hm₁ c₁
  have hstable := constellation_stability_ne_zero hN f lambda hlambda
    z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ c₁ c₂
  unfold ConcreteBasicIdentity
  exact twoResolvent_basicIdentity (lambda : ℂ)
    (chooseAdjoint c₁ (resolventPencil f lambda W z₁))
    (chooseAdjoint c₁ (mdePencil f lambda z₁ m₁)) W
    (chooseAdjoint c₁ (resolvent f lambda W z₁))
    (chooseAdjoint c₁ (mdeMatrix f lambda z₁ m₁)) A
    (chooseAdjoint c₂ (resolvent f lambda W z₂))
    (chooseAdjoint c₂ (mdeMatrix f lambda z₂ m₂))
    hMQ hPG hD hstable

/-- Concrete `++` underlined identity. -/
theorem concrete_basicIdentity_pp {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ConcreteBasicIdentity f lambda W z₁ m₁ z₂ m₂ A .plain .plain :=
  concrete_basicIdentity hN f lambda hlambda W hW z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ A
    .plain .plain

/-- Concrete `+-` underlined identity. -/
theorem concrete_basicIdentity_pm {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ConcreteBasicIdentity f lambda W z₁ m₁ z₂ m₂ A .plain .adjoint :=
  concrete_basicIdentity hN f lambda hlambda W hW z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ A
    .plain .adjoint

/-- Concrete `-+` underlined identity. -/
theorem concrete_basicIdentity_mp {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ConcreteBasicIdentity f lambda W z₁ m₁ z₂ m₂ A .adjoint .plain :=
  concrete_basicIdentity hN f lambda hlambda W hW z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ A
    .adjoint .plain

/-- Concrete `--` underlined identity. -/
theorem concrete_basicIdentity_mm {N : ℕ} (hN : 0 < N)
    (f : Spectrum N) (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (W : Matrix (Fin N) (Fin N) ℂ) (hW : W.IsHermitian)
    (z₁ m₁ z₂ m₂ : ℂ) (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    (hm₁ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₁ m₁)
    (hm₂ : CEHNative.BlockBand.CEH.IsSolution f (lambda ^ 2) z₂ m₂)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    ConcreteBasicIdentity f lambda W z₁ m₁ z₂ m₂ A .adjoint .adjoint :=
  concrete_basicIdentity hN f lambda hlambda W hW z₁ m₁ z₂ m₂ hz₁ hz₂ hm₁ hm₂ A
    .adjoint .adjoint

end PencilAdapter
end CEHNative.BlockBand.External.CEH
