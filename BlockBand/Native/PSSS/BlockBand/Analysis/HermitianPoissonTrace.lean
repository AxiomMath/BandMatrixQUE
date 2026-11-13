module

public import BlockBand.Native.PSSS.BlockBand.Analysis.CauchyPoissonUpperHalfPlane
public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Hermitian resolvent traces as finite Poisson sums

The negative imaginary trace of a regulated Hermitian resolvent is the multiplicity-counted sum of
Poisson kernels over the eigenvalues, and its Cauchy average over the backgrounds `A + tQ` is the
resolvent with the absorber `Q` added to the regulator.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Matrix

namespace PSSSNative.BlockBand

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The complex trace of the scalar-regulated Hermitian resolvent is the
multiplicity-counted sum of its scalar resolvents. -/
theorem trace_nonsing_inv_sub_smul_one_add_I_eq_sum_eigenvalues
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e η : ℝ) (hη : η ≠ 0) :
    ((A - (e : ℂ) • (1 : Matrix ι ι ℂ) +
      Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace =
      ∑ i, (((hA.eigenvalues i : ℂ) - e + Complex.I * η)⁻¹) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  let D' : Matrix ι ι ℂ :=
    diagonal (fun i => (hA.eigenvalues i : ℂ) - e + Complex.I * η)
  have hinside : D - (e : ℂ) • (1 : Matrix ι ι ℂ) +
      Complex.I • (η • (1 : Matrix ι ι ℂ)) = D' := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, D']
    · simp [D, D', hij]
  have hshape :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        star (hA.eigenvectorUnitary : Matrix ι ι ℂ) -
        (e : ℂ) • (1 : Matrix ι ι ℂ) +
        Complex.I • (η • (1 : Matrix ι ι ℂ)) =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) * D' *
        star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
    change Φ D - (e : ℂ) • (1 : Matrix ι ι ℂ) +
      Complex.I • (η • (1 : Matrix ι ι ℂ)) = Φ D'
    have hfix : Φ (η • (1 : Matrix ι ι ℂ)) =
        η • (1 : Matrix ι ι ℂ) := by
      change Φ ((η : ℂ) • (1 : Matrix ι ι ℂ)) =
        (η : ℂ) • (1 : Matrix ι ι ℂ)
      rw [map_smul, map_one]
    have hmap := congrArg Φ hinside
    simp only [map_add, map_sub, map_smul, map_one, hfix] at hmap
    exact hmap
  rw [hshape]
  change (Φ D')⁻¹.trace = _
  have hD' : IsUnit D' := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp only [D', det_diagonal]
    apply isUnit_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp only [ne_eq]
    intro hz
    have him := congrArg Complex.im hz
    simp at him
    exact hη him
  have hinvmap : Ring.inverse (Φ D') = Φ (Ring.inverse D') := by
    apply (hD'.map Φ).mul_left_cancel
    calc
      Φ D' * Ring.inverse (Φ D') = 1 := by
        rw [Ring.inverse_of_isUnit (hD'.map Φ)]
        exact Units.mul_inv (hD'.map Φ).unit
      _ = Φ 1 := (map_one Φ).symm
      _ = Φ (D' * Ring.inverse D') := by
        congr 1
        rw [Ring.inverse_of_isUnit hD']
        exact (Units.mul_inv hD'.unit).symm
      _ = Φ D' * Φ (Ring.inverse D') := map_mul Φ _ _
  rw [Matrix.nonsing_inv_eq_ringInverse, hinvmap,
    ← Matrix.nonsing_inv_eq_ringInverse]
  change (Φ (D'⁻¹)).trace = _
  simp only [Φ, Unitary.conjStarAlgAut_apply]
  have hU :
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
          (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.property
  rw [trace_mul_cycle, hU, one_mul]
  rw [trace]
  apply Finset.sum_congr rfl
  intro i hi
  have hscalar :
      (hA.eigenvalues i : ℂ) - e + Complex.I * η ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp at him
    exact hη him
  have hmul := congrArg (fun M : Matrix ι ι ℂ => M i i)
    (D'.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det D').mp hD'))
  simp only [Matrix.mul_apply, D', diagonal_apply, one_apply] at hmul
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, ite_true] at hmul
  simp only [Finset.mem_univ, ite_true] at hmul
  change D'⁻¹ i i =
    ((hA.eigenvalues i : ℂ) - e + Complex.I * η)⁻¹
  calc
    D'⁻¹ i i =
        1 * ((hA.eigenvalues i : ℂ) - e + Complex.I * η)⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ (a := D'⁻¹ i i) (b := 1) hscalar).mpr
        (by simpa [mul_comm] using hmul)
    _ = _ := one_mul _

/-- **Scalar Hermitian Poisson trace identity.** For a Hermitian matrix `A`,
energy `e`, and regulator `η > 0`, the negative imaginary trace of the
resolvent of `A - e I` is the multiplicity-counted Poisson-kernel sum over the
real eigenvalues of `A`.  This is the exact finite-dimensional spectral
identity used in the projected-Wegner argument. -/
theorem neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_sum_poisson
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    -(((A - (e : ℂ) • (1 : Matrix ι ι ℂ) +
      Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im =
      ∑ i, η / ((hA.eigenvalues i - e) ^ 2 + η ^ 2) := by
  rw [trace_nonsing_inv_sub_smul_one_add_I_eq_sum_eigenvalues
    A hA e η hη.ne']
  change -(Complex.imAddGroupHom
    (∑ i, (((hA.eigenvalues i : ℂ) - e + Complex.I * η)⁻¹))) =
      ∑ i, η / ((hA.eigenvalues i - e) ^ 2 + η ^ 2)
  rw [map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change -(((hA.eigenvalues i : ℂ) - e + Complex.I * η)⁻¹).im =
    η / ((hA.eigenvalues i - e) ^ 2 + η ^ 2)
  rw [Complex.inv_im]
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_sub, zero_mul,
    one_mul]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_sub, zero_mul,
    one_mul]
  ring

/-- Increasing-order form of the finite-dimensional Hermitian Poisson trace
identity.  The sum is indexed by `Fin (card ι)` and therefore records every
eigenvalue with algebraic multiplicity, including repeated eigenvalues. -/
theorem neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_ordered_poisson
    (A : HermitianMatrix ι) (e : ℝ) {η : ℝ} (hη : 0 < η) :
    -((((A : Matrix ι ι ℂ) - (e : ℂ) • (1 : Matrix ι ι ℂ) +
      Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im =
      ∑ j : Fin (Fintype.card ι),
        η / ((orderedEigenvalue A j - e) ^ 2 + η ^ 2) := by
  rw [neg_im_trace_nonsing_inv_sub_smul_one_add_I_eq_sum_poisson
    (A : Matrix ι ι ℂ) A.property e hη]
  let E : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  let R : Equiv.Perm (Fin (Fintype.card ι)) := Fin.revPerm
  apply Fintype.sum_equiv (E.trans R)
  intro i
  simp [Matrix.IsHermitian.eigenvalues, orderedEigenvalue, E, R]

/-- The noncommuting Cauchy–Poisson identity with both boundary and absorbed
resolvents expanded.  It turns a Cauchy average over the real Hermitian
backgrounds `A + tQ` into the resolvent with the absorber `Q` added to the
regulator; no commutation hypothesis between `A` and `Q` occurs. -/
theorem integral_standardCauchyWeight_mul_neg_im_real_background_resolvent
    (A Q : Matrix ι ι ℂ) (hA : A.IsHermitian) (hQ : Q.PosSemidef)
    {η : ℝ} (hη : 0 < η) :
    (∫ t : ℝ, standardCauchyWeight t *
      (-(((A + (t : ℂ) • Q +
        Complex.I • (η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im)) =
      -(((A + Complex.I •
        (Q + η • (1 : Matrix ι ι ℂ)))⁻¹).trace).im := by
  simpa only [cauchyResolventTrace, cauchyResolventPencil_ofReal,
    cauchyResolventPencil_I] using
    integral_standardCauchyWeight_mul_neg_im_cauchyResolventTrace_eq_I
      A Q hA hQ hη

end PSSSNative.BlockBand
