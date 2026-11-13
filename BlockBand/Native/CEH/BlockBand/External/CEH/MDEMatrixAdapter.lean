module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDEAnalyticity
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Trace

/-!
# Hermitian-matrix adapter for the finite-dimensional scalar MDE

This file diagonalizes an arbitrary finite Hermitian deformation and applies the
unconditional scalar Dyson branches constructed in `MDEExistence` and
`MDEAnalyticity`.  The zero-dimensional case is treated separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- The real spectrum canonically supplied by the finite-dimensional spectral theorem. -/
def hermitianSpectrum {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian) :
    DeformationSpectrum N := hF.eigenvalues

/-- Transport a diagonal matrix from the eigenbasis of a Hermitian matrix. -/
def spectralLift {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    (d : Fin N → ℂ) : LocalETHMatrix N :=
  Unitary.conjStarAlgAut ℂ _ hF.eigenvectorUnitary (Matrix.diagonal d)

/-- Unitary spectral transport preserves the normalized trace. -/
theorem normalizedTrace_spectralLift {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (d : Fin N → ℂ) :
    Conventions.normalizedTrace (spectralLift hF d) = average d := by
  unfold spectralLift Conventions.normalizedTrace average
  rw [Matrix.trace_map, Matrix.trace_diagonal]
  simp [div_eq_mul_inv, mul_comm]

/-- The spectral lift of the eigenvalue function is the original Hermitian matrix. -/
theorem spectralLift_eigenvalues {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) :
    spectralLift hF (fun i => (hermitianSpectrum hF i : ℂ)) = F := by
  simpa [spectralLift, hermitianSpectrum, Function.comp_def] using hF.spectral_theorem.symm

/-- The matrix imaginary part of a diagonal matrix is the diagonal of the scalar
imaginary parts. -/
theorem imPart_diagonal {N : ℕ} (d : Fin N → ℂ) :
    localETHImPart (Matrix.diagonal d) =
      Matrix.diagonal (fun i => ((d i).im : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [localETHImPart, Matrix.diagonal, smul_eq_mul, Complex.ext_iff]
    ring
  · simp [localETHImPart, Matrix.diagonal, hij, Ne.symm hij]

/-- Scalar multiplication and matrix imaginary part commute with spectral transport. -/
theorem smul_imPart_spectralLift {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (r : ℝ) (d : Fin N → ℂ) :
    ((r : ℂ) • localETHImPart (spectralLift hF d)) =
      spectralLift hF (fun i => ((r * (d i).im : ℝ) : ℂ)) := by
  let e := Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary
  have himap : localETHImPart (e (Matrix.diagonal d)) =
      e (localETHImPart (Matrix.diagonal d)) := by
    unfold localETHImPart
    simp only [← Matrix.star_eq_conjTranspose]
    rw [← map_star, ← map_sub, ← map_smul]
  rw [show spectralLift hF d = e (Matrix.diagonal d) by rfl, himap]
  rw [imPart_diagonal, ← map_smul]
  apply congrArg e
  ext i j
  simp [Matrix.diagonal, smul_eq_mul]

/-- The scalar mean selected in the half-plane containing `z`; it is totalized by zero
on the real axis and in dimension zero. -/
def hermitianMDEMean {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) (z : ℂ) : ℂ :=
  if _hN : 0 < N then
    if _hz : 0 < z.im then upperBranch _hN (hermitianSpectrum hF) hs z
    else if _hz' : z.im < 0 then lowerBranch _hN (hermitianSpectrum hF) hs z else 0
  else 0

/-- The unconditional Hermitian matrix Dyson branch, reconstructed by the spectral theorem. -/
def hermitianMDEBranch {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s : ℝ} (hs : 0 < s) (z : ℂ) : LocalETHMatrix N :=
  if _hN : 0 < N then
    spectralLift hF
      (entry (hermitianSpectrum hF) s z (hermitianMDEMean hF hs z))
  else 0

/-- On the upper half-plane the selected mean is the unconditional upper scalar branch. -/
theorem hermitianMDEMean_of_im_pos {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    hermitianMDEMean hF hs z = upperBranch hN (hermitianSpectrum hF) hs z := by
  simp [hermitianMDEMean, hN, hz]

/-- On the lower half-plane the selected mean is the conjugated lower scalar branch. -/
theorem hermitianMDEMean_of_im_neg {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im < 0) :
    hermitianMDEMean hF hs z = lowerBranch hN (hermitianSpectrum hF) hs z := by
  simp [hermitianMDEMean, hN, hz, not_lt.mpr hz.le]

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- Nonzero effective height suffices to exclude every scalar denominator. -/
theorem denominator_ne_zero_of_height_ne {N : ℕ} (f : DeformationSpectrum N)
    {s : ℝ} {z m : ℂ} (hh : effectiveHeight s z m ≠ 0) (i : Fin N) :
    (f i : ℂ) - z - (s : ℂ) * m ≠ 0 := by
  intro h
  apply hh
  have him := congrArg Complex.im h
  simp [effectiveHeight] at him ⊢
  linarith

/-- A negative effective height gives the lower Herglotz sign entrywise. -/
theorem entry_im_neg {N : ℕ} (f : DeformationSpectrum N) {s : ℝ}
    {z m : ℂ} (hh : effectiveHeight s z m < 0) (i : Fin N) :
    (entry f s z m i).im < 0 := by
  rw [entry_im]
  exact div_neg_of_neg_of_pos hh (Complex.normSq_pos.mpr
    (denominator_ne_zero_of_height_ne f hh.ne i))

/-- The diagonal resolvent is a one-sided inverse before transport out of the eigenbasis. -/
theorem spectralLift_entry_inverse {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (s : ℝ) (z m : ℂ)
    (hh : effectiveHeight s z m ≠ 0) :
    (F - (z + (s : ℂ) * m) • (1 : LocalETHMatrix N)) *
        spectralLift hF (entry (hermitianSpectrum hF) s z m) = 1 := by
  rw (occs := .pos [1]) [← spectralLift_eigenvalues hF]
  let e := Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary
  change (e (Matrix.diagonal (fun i => (hermitianSpectrum hF i : ℂ))) -
      (z + (s : ℂ) * m) • (1 : LocalETHMatrix N)) *
      e (Matrix.diagonal (entry (hermitianSpectrum hF) s z m)) = 1
  rw [← map_one e, ← map_smul e, ← map_sub e, ← map_mul e]
  apply_fun e.symm
  simp only [e.symm_apply_apply]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, Matrix.mul_apply, entry]
    field_simp [denominator_ne_zero_of_height_ne (hermitianSpectrum hF) hh i]
    ring
  · simp [Matrix.diagonal, Matrix.mul_apply, hij]

/-- The normalized trace of the constructed matrix is its selected scalar mean. -/
theorem normalizedTrace_hermitianMDEBranch {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) :
    Conventions.normalizedTrace (hermitianMDEBranch hF hs z) =
      hermitianMDEMean hF hs z := by
  rw [hermitianMDEBranch, dite_eq_left hN, normalizedTrace_spectralLift]
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · rw [hermitianMDEMean_of_im_neg hF hN hs hzneg]
    exact (lowerBranch_isLowerSolution hN (hermitianSpectrum hF) hs hzneg).1.symm
  · rw [hermitianMDEMean_of_im_pos hF hN hs hzpos]
    exact (upperBranch_isSolution hN (hermitianSpectrum hF) hs hzpos).1.symm

/-- In positive dimension, the reconstructed branch satisfies the one-sided matrix
Dyson inverse equation on both half-planes. -/
theorem hermitianMDEBranch_inv {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) :
    (F - (z + (s : ℂ) * Conventions.normalizedTrace
      (hermitianMDEBranch hF hs z)) • (1 : LocalETHMatrix N)) *
      hermitianMDEBranch hF hs z = 1 := by
  rw [normalizedTrace_hermitianMDEBranch hF hN hs hz]
  rw [hermitianMDEBranch, dite_eq_left hN]
  apply spectralLift_entry_inverse hF s z (hermitianMDEMean hF hs z)
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hm := (lowerBranch_isLowerSolution hN (hermitianSpectrum hF) hs hzneg).2
    rw [hermitianMDEMean_of_im_neg hF hN hs hzneg]
    unfold effectiveHeight
    nlinarith
  · have hm := (upperBranch_isSolution hN (hermitianSpectrum hF) hs hzpos).2
    rw [hermitianMDEMean_of_im_pos hF hN hs hzpos]
    unfold effectiveHeight
    nlinarith

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- The reconstructed matrix has the MDE sign in every non-real spectral parameter. -/
theorem hermitianMDEBranch_pos {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) :
    (((z.im : ℝ) : ℂ) • localETHImPart (hermitianMDEBranch hF hs z)).PosDef := by
  rw [hermitianMDEBranch, dite_eq_left hN,
    smul_imPart_spectralLift hF z.im]
  unfold spectralLift
  rw [Unitary.conjStarAlgAut_apply]
  apply (Unitary.isUnit_coe.posDef_star_right_conjugate_iff).2
  apply Matrix.PosDef.diagonal
  intro i
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hm := lowerBranch_isLowerSolution hN (hermitianSpectrum hF) hs hzneg
    have hh : effectiveHeight s z (hermitianMDEMean hF hs z) < 0 := by
      rw [hermitianMDEMean_of_im_neg hF hN hs hzneg]
      unfold effectiveHeight
      nlinarith [hm.2]
    have hi := entry_im_neg (hermitianSpectrum hF) hh i
    exact_mod_cast mul_pos_of_neg_of_neg hzneg hi
  · have hm := upperBranch_isSolution hN (hermitianSpectrum hF) hs hzpos
    have hh : 0 < effectiveHeight s z (hermitianMDEMean hF hs z) := by
      rw [hermitianMDEMean_of_im_pos hF hN hs hzpos]
      unfold effectiveHeight
      nlinarith [hm.2]
    have hi := entry_im_pos (hermitianSpectrum hF) hh i
    exact_mod_cast mul_pos hzpos hi

/-- In dimension zero the unique empty matrix satisfies the matrix MDE contract. -/
theorem empty_isLocalETHMDESolution {F : LocalETHMatrix 0} (s : ℝ) (z : ℂ)
    (M : LocalETHMatrix 0) : IsLocalETHMDESolution s F z M := by
  constructor
  · exact Subsingleton.elim _ _
  · have hdiag : (Matrix.diagonal (fun i : Fin 0 => (1 : ℂ))).PosDef :=
      Matrix.PosDef.diagonal (fun i => Fin.elim0 i)
    exact Eq.mp (congrArg Matrix.PosDef (Subsingleton.elim _ _)) hdiag

/-- The spectral construction is an unconditional matrix MDE solution for every
non-real parameter, including the empty `N = 0` matrix algebra. -/
theorem hermitianMDEBranch_isSolution {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≠ 0) :
    IsLocalETHMDESolution s F z (hermitianMDEBranch hF hs z) := by
  by_cases hN : 0 < N
  · exact ⟨hermitianMDEBranch_inv hF hN hs hz,
      hermitianMDEBranch_pos hF hN hs hz⟩
  · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    exact empty_isLocalETHMDESolution s z _

/-- The Hermitian spectral construction supplies the branch expected by the
published local-ETH interface, without a matrix-solution assumption. -/
theorem hermitianMDEBranch_isLocalETHMDEBranch {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) :
    IsLocalETHMDEBranch s F (hermitianMDEBranch hF hs) :=
  fun _ hz => hermitianMDEBranch_isSolution hF hs hz

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- Trace commutes with taking the matrix imaginary part. -/
theorem trace_imPart {N : ℕ} (M : LocalETHMatrix N) :
    Matrix.trace (localETHImPart M) = ((Matrix.trace M).im : ℂ) := by
  unfold localETHImPart
  rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_conjTranspose]
  apply Complex.ext <;> simp [smul_eq_mul]
  ring

/-- The sign condition forces the normalized trace to lie in the same half-plane
as the spectral parameter in positive dimension. -/
theorem normalizedTrace_im_sign {N : ℕ} (hN : 0 < N) {s : ℝ}
    {F M : LocalETHMatrix N} {z : ℂ} (hM : IsLocalETHMDESolution s F z M) :
    0 < z.im * (Conventions.normalizedTrace M).im := by
  let _ : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have htr := hM.pos.trace_pos
  have htrace : Matrix.trace
      (((z.im : ℝ) : ℂ) • localETHImPart M) =
      ((N : ℝ) * (z.im * (Conventions.normalizedTrace M).im) : ℝ) := by
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Matrix.trace_smul, trace_imPart]
    unfold Conventions.normalizedTrace
    apply Complex.ext
    · simp [smul_eq_mul, Complex.mul_im, Complex.mul_re]
      field_simp
    · simp [smul_eq_mul]
  rw [htrace] at htr
  have hreal : 0 < (N : ℝ) * (z.im * (Conventions.normalizedTrace M).im) := by
    exact_mod_cast htr
  rcases mul_pos_iff.mp hreal with h | h
  · exact h.2
  · have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    exact (not_lt_of_ge hNr.le h.1).elim

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- Every matrix MDE solution is diagonal in the Hermitian eigenbasis and is the
entrywise scalar resolvent at its own normalized trace. -/
theorem eq_spectralLift_entry_of_isSolution {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) {M : LocalETHMatrix N}
    (hM : IsLocalETHMDESolution s F z M) :
    M = spectralLift hF
      (entry (hermitianSpectrum hF) s z (Conventions.normalizedTrace M)) := by
  have hsign := normalizedTrace_im_sign hN hM
  have hh : effectiveHeight s z (Conventions.normalizedTrace M) ≠ 0 := by
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · have hmneg : (Conventions.normalizedTrace M).im < 0 := by
        by_contra h
        have hmnonneg : 0 ≤ (Conventions.normalizedTrace M).im := le_of_not_gt h
        have : z.im * (Conventions.normalizedTrace M).im ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hzneg.le hmnonneg
        linarith
      unfold effectiveHeight
      nlinarith
    · have hmpos : 0 < (Conventions.normalizedTrace M).im := by
        by_contra h
        have hmnonpos : (Conventions.normalizedTrace M).im ≤ 0 := le_of_not_gt h
        have : z.im * (Conventions.normalizedTrace M).im ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hzpos.le hmnonpos
        linarith
      unfold effectiveHeight
      nlinarith
  exact Matrix.right_inv_eq_right_inv hM.inv
    (spectralLift_entry_inverse hF s z (Conventions.normalizedTrace M) hh)

/-- A Hermitian matrix MDE solution is unique at each non-real parameter. -/
theorem isLocalETHMDESolution_unique {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≠ 0)
    {M : LocalETHMatrix N} (hM : IsLocalETHMDESolution s F z M) :
    M = hermitianMDEBranch hF hs z := by
  by_cases hN : 0 < N
  · let m := Conventions.normalizedTrace M
    have hdiag := eq_spectralLift_entry_of_isSolution hF hN hs hz hM
    have hfixed : m = average (entry (hermitianSpectrum hF) s z m) := by
      calc
        m = Conventions.normalizedTrace
            (spectralLift hF (entry (hermitianSpectrum hF) s z m)) := by
              simpa [m] using congrArg Conventions.normalizedTrace hdiag
        _ = average (entry (hermitianSpectrum hF) s z m) :=
          normalizedTrace_spectralLift hF _
    have hsign := normalizedTrace_im_sign hN hM
    have hmean : m = hermitianMDEMean hF hs z := by
      rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · have hmneg : m.im < 0 := by
          by_contra h
          have hmnonneg : 0 ≤ m.im := le_of_not_gt h
          have : z.im * m.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hzneg.le hmnonneg
          simpa [m] using (not_lt_of_ge this hsign)
        rw [hermitianMDEMean_of_im_neg hF hN hs hzneg]
        exact lowerSolution_unique hN (hermitianSpectrum hF) hs hzneg
          ⟨hfixed, hmneg⟩
          (lowerBranch_isLowerSolution hN (hermitianSpectrum hF) hs hzneg)
      · have hmpos : 0 < m.im := by
          by_contra h
          have hmnonpos : m.im ≤ 0 := le_of_not_gt h
          have : z.im * m.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hzpos.le hmnonpos
          simpa [m] using (not_lt_of_ge this hsign)
        rw [hermitianMDEMean_of_im_pos hF hN hs hzpos]
        exact solution_unique hN (hermitianSpectrum hF) hs hzpos
          ⟨hfixed, hmpos⟩
          (upperBranch_isSolution hN (hermitianSpectrum hF) hs hzpos)
    calc
      M = spectralLift hF (entry (hermitianSpectrum hF) s z m) := by
        simpa [m] using hdiag
      _ = spectralLift hF
          (entry (hermitianSpectrum hF) s z (hermitianMDEMean hF hs z)) := by
        rw [hmean]
      _ = hermitianMDEBranch hF hs z := by
        rw [hermitianMDEBranch, dite_eq_left hN]
  · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    exact Subsingleton.elim _ _

/-- Existence and uniqueness of the matrix MDE solution, with no supplied matrix
solution or branch certificate. -/
theorem existsUnique_isLocalETHMDESolution {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≠ 0) :
    ∃! M : LocalETHMatrix N, IsLocalETHMDESolution s F z M := by
  refine ⟨hermitianMDEBranch hF hs z,
    hermitianMDEBranch_isSolution hF hs hz, ?_⟩
  intro M hM
  exact isLocalETHMDESolution_unique hF hs hz hM

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- Multiplication under spectral transport is pointwise multiplication on the diagonal. -/
theorem normalizedTrace_spectralLift_mul {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (a b : Fin N → ℂ) :
    Conventions.normalizedTrace (spectralLift hF a * spectralLift hF b) =
      average (fun i => a i * b i) := by
  let e := Unitary.conjStarAlgAut ℂ (LocalETHMatrix N) hF.eigenvectorUnitary
  change Conventions.normalizedTrace (e (Matrix.diagonal a) * e (Matrix.diagonal b)) = _
  rw [← map_mul, show e (Matrix.diagonal a * Matrix.diagonal b) =
    spectralLift hF (fun i => a i * b i) by
      apply congrArg e
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal, Matrix.mul_apply]
      · simp [Matrix.diagonal, Matrix.mul_apply, hij]]
  exact normalizedTrace_spectralLift hF _

/-- The matrix stability trace is exactly the scalar stability denominator. -/
theorem matrix_stability_eq_scalar {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (_hz : z.im ≠ 0) :
    1 - (s : ℂ) * Conventions.normalizedTrace
        (hermitianMDEBranch hF hs z * hermitianMDEBranch hF hs z) =
      stabilityDenominator (hermitianSpectrum hF) s z
        (hermitianMDEMean hF hs z) := by
  rw [hermitianMDEBranch, dite_eq_left hN,
    normalizedTrace_spectralLift_mul]
  simp [stabilityDenominator, pow_two]

/-- The published matrix density is the absolute imaginary part of the selected
scalar branch, with exactly the CEH normalization. -/
theorem localETHMDEDensity_hermitianMDEBranch {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z.im ≠ 0) :
    localETHMDEDensity (hermitianMDEBranch hF hs z) =
      |(hermitianMDEMean hF hs z).im| / Real.pi := by
  simp [localETHMDEDensity,
    normalizedTrace_hermitianMDEBranch hF hN hs hz]

/-- On the upper half-plane the matrix density agrees with the scalar density. -/
theorem localETHMDEDensity_eq_density {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    localETHMDEDensity (hermitianMDEBranch hF hs z) =
      density (upperBranch hN (hermitianSpectrum hF) hs z) := by
  rw [localETHMDEDensity_hermitianMDEBranch hF hN hs hz.ne',
    hermitianMDEMean_of_im_pos hF hN hs hz]
  unfold density
  rw [abs_of_pos (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz).2]

/-- The matrix stability denominator is nonzero, inherited from scalar uniqueness. -/
theorem matrix_stability_ne_zero {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    1 - (s : ℂ) * Conventions.normalizedTrace
        (hermitianMDEBranch hF hs z * hermitianMDEBranch hF hs z) ≠ 0 := by
  rw [matrix_stability_eq_scalar hF hN hs hz.ne',
    hermitianMDEMean_of_im_pos hF hN hs hz]
  exact stabilityDenominator_ne_zero hN (hermitianSpectrum hF) hs hz
    (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz)

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix
open scoped ComplexConjugate ComplexOrder Topology

/-- Entry formula for unitary spectral transport. -/
theorem spectralLift_apply {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (d : Fin N → ℂ) (i j : Fin N) :
    spectralLift hF d i j = ∑ k, (hF.eigenvectorUnitary : LocalETHMatrix N) i k *
      d k * star ((hF.eigenvectorUnitary : LocalETHMatrix N) j k) := by
  simp [spectralLift, Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.diagonal]

/-- The matrix branch is entrywise analytic in the upper half-plane. -/
theorem analyticAt_hermitianMDEBranch_apply_of_im_pos {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) (i j : Fin N) :
    AnalyticAt ℂ (fun w => hermitianMDEBranch hF hs w i j) z := by
  let u : ℂ → ℂ := upperBranch hN (hermitianSpectrum hF) hs
  have hu : AnalyticAt ℂ u z := analyticAt_upperBranch hN (hermitianSpectrum hF) hs hz
  have hsol := upperBranch_isSolution hN (hermitianSpectrum hF) hs hz
  have hh : 0 < effectiveHeight s z (u z) := by
    unfold effectiveHeight u
    nlinarith [hsol.2]
  have hentry (k : Fin N) : AnalyticAt ℂ
      (fun w => entry (hermitianSpectrum hF) s w (u w) k) z :=
    analyticAt_entry (hermitianSpectrum hF) s u k hu
      (denominator_ne_zero (hermitianSpectrum hF) hh k)
  have hspectral : AnalyticAt ℂ (fun w =>
      spectralLift hF (fun k => entry (hermitianSpectrum hF) s w (u w) k) i j) z := by
    simp only [spectralLift_apply]
    have hsum : ∀ t : Finset (Fin N), AnalyticAt ℂ (fun w =>
        ∑ k ∈ t, (hF.eigenvectorUnitary : LocalETHMatrix N) i k *
          entry (hermitianSpectrum hF) s w (u w) k *
          star ((hF.eigenvectorUnitary : LocalETHMatrix N) j k)) z := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
      | @insert k t hkt iht =>
          simp only [Finset.sum_insert hkt]
          exact ((analyticAt_const.mul (hentry k)).mul analyticAt_const).add iht
    simpa using hsum Finset.univ
  apply hspectral.congr
  have hevent : ∀ᶠ w in 𝓝 z, 0 < w.im :=
    (Complex.continuous_im.tendsto z) (Ioi_mem_nhds hz)
  filter_upwards [hevent] with w hw
  simp [hermitianMDEBranch, hN, hermitianMDEMean, hw, u]

/-- Entrywise analyticity in the lower half-plane follows from the conjugated scalar branch. -/
theorem analyticAt_hermitianMDEBranch_apply_of_im_neg {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im < 0) (i j : Fin N) :
    AnalyticAt ℂ (fun w => hermitianMDEBranch hF hs w i j) z := by
  let l : ℂ → ℂ := lowerBranch hN (hermitianSpectrum hF) hs
  have hl : AnalyticAt ℂ l z := analyticAt_lowerBranch hN (hermitianSpectrum hF) hs hz
  have hsol := lowerBranch_isLowerSolution hN (hermitianSpectrum hF) hs hz
  have hh : effectiveHeight s z (l z) < 0 := by
    unfold effectiveHeight l
    nlinarith [hsol.2]
  have hentry (k : Fin N) : AnalyticAt ℂ
      (fun w => entry (hermitianSpectrum hF) s w (l w) k) z :=
    analyticAt_entry (hermitianSpectrum hF) s l k hl
      (denominator_ne_zero_of_height_ne (hermitianSpectrum hF) hh.ne k)
  have hspectral : AnalyticAt ℂ (fun w =>
      spectralLift hF (fun k => entry (hermitianSpectrum hF) s w (l w) k) i j) z := by
    simp only [spectralLift_apply]
    have hsum : ∀ t : Finset (Fin N), AnalyticAt ℂ (fun w =>
        ∑ k ∈ t, (hF.eigenvectorUnitary : LocalETHMatrix N) i k *
          entry (hermitianSpectrum hF) s w (l w) k *
          star ((hF.eigenvectorUnitary : LocalETHMatrix N) j k)) z := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
      | @insert k t hkt iht =>
          simp only [Finset.sum_insert hkt]
          exact ((analyticAt_const.mul (hentry k)).mul analyticAt_const).add iht
    simpa using hsum Finset.univ
  apply hspectral.congr
  have hevent : ∀ᶠ w in 𝓝 z, w.im < 0 :=
    (Complex.continuous_im.tendsto z) (Iio_mem_nhds hz)
  filter_upwards [hevent] with w hw
  simp [hermitianMDEBranch, hN, hermitianMDEMean, hw, not_lt.mpr hw.le, l]

/-- Hence every entry of the unconditional matrix branch is continuous off the real axis. -/
theorem continuousAt_hermitianMDEBranch_apply {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im ≠ 0) (i j : Fin N) :
    ContinuousAt (fun w => hermitianMDEBranch hF hs w i j) z := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · exact (analyticAt_hermitianMDEBranch_apply_of_im_neg hF hN hs hzneg i j).continuousAt
  · exact (analyticAt_hermitianMDEBranch_apply_of_im_pos hF hN hs hzpos i j).continuousAt

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Matrix
open scoped ComplexConjugate ComplexOrder

/-- On the upper half-plane the matrix `Γ` is the unitary transport of the
pointwise scalar `gamma`. -/
theorem localETHGamma_hermitianMDEBranch {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    localETHGamma (hermitianMDEBranch hF hs z) =
      spectralLift hF (fun i =>
        (gamma (hermitianSpectrum hF) s z
          (upperBranch hN (hermitianSpectrum hF) hs z) i : ℂ)) := by
  let m := upperBranch hN (hermitianSpectrum hF) hs z
  have hmpos : 0 < m.im :=
    (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz).2
  rw [localETHGamma,
    normalizedTrace_hermitianMDEBranch hF hN hs hz.ne',
    hermitianMDEBranch, dite_eq_left hN,
    hermitianMDEMean_of_im_pos hF hN hs hz]
  change ((m.im : ℂ))⁻¹ •
      localETHImPart (spectralLift hF (entry (hermitianSpectrum hF) s z m)) = _
  have hinv : ((m.im : ℂ))⁻¹ = (((m.im)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hinv, smul_imPart_spectralLift hF (m.im)⁻¹]
  apply congrArg (spectralLift hF)
  funext i
  simp [m, gamma]
  field_simp [hmpos.ne']

/-- Consequently the normalized trace of the matrix `Γ` is one. -/
theorem normalizedTrace_localETHGamma_eq_one {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (hN : 0 < N) {s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : 0 < z.im) :
    Conventions.normalizedTrace
      (localETHGamma (hermitianMDEBranch hF hs z)) = 1 := by
  rw [localETHGamma_hermitianMDEBranch hF hN hs hz,
    normalizedTrace_spectralLift]
  have havg := average_gamma_eq_one hN (hermitianSpectrum hF)
    (upperBranch_isSolution hN (hermitianSpectrum hF) hs hz)
  unfold averageReal at havg
  unfold average
  have hc := congrArg (fun x : ℝ => (x : ℂ)) havg
  simpa using hc

end CEHNative.BlockBand.CEH
