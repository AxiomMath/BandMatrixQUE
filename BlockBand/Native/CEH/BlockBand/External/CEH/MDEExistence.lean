module

public import BlockBand.Native.CEH.BlockBand.External.CEH.MDE
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Existence of the finite-dimensional scalar MDE branch

This file constructs the scalar Dyson branch from the finite spectrum itself.  The
cleared equation is used only as an existence device; poles introduced by clearing
are controlled by their imaginary part, so repeated eigenvalues require no
simplicity assumption.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CEHNative.BlockBand.CEH

open Polynomial Set
open scoped ComplexConjugate

/-- The monic polynomial whose zeros are the shifted poles `fᵢ-z`. -/
def polePolynomial {N : ℕ} (f : DeformationSpectrum N) (z : ℂ) : ℂ[X] :=
  ∏ i : Fin N, (X - C ((f i : ℂ) - z))

/-- The sum of the products obtained by omitting one shifted pole. -/
def omittedPolePolynomial {N : ℕ} (f : DeformationSpectrum N) (z : ℂ) : ℂ[X] :=
  ∑ i : Fin N, ∏ j ∈ (Finset.univ.erase i), (X - C ((f j : ℂ) - z))

/-- Cleared equation for `w = s m`.  Its degree is `N+1`, including when poles
coincide. -/
def dysonPolynomial {N : ℕ} (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) : ℂ[X] :=
  X * polePolynomial f z + C ((s : ℂ) / (N : ℂ)) * omittedPolePolynomial f z

@[simp] theorem polePolynomial_zero (f : DeformationSpectrum 0) (z : ℂ) :
    polePolynomial f z = 1 := by
  simp [polePolynomial]

@[simp] theorem omittedPolePolynomial_zero (f : DeformationSpectrum 0) (z : ℂ) :
    omittedPolePolynomial f z = 0 := by
  simp [omittedPolePolynomial]

/-- In dimension zero the algebraic Dyson equation has the unique value zero. -/
theorem average_entry_eq_zero_of_dimension_zero (f : DeformationSpectrum 0)
    (s : ℝ) (z m : ℂ) : average (entry f s z m) = 0 := by
  simp [average]

/-- The dimension-zero equation is handled separately: it has algebraic solution
`0`, but no upper-half-plane `IsSolution`, since that predicate intentionally
includes strict positivity of the imaginary part. -/
theorem dimension_zero_algebraic_solution_iff (f : DeformationSpectrum 0)
    (s : ℝ) (z m : ℂ) : m = average (entry f s z m) ↔ m = 0 := by
  rw [average_entry_eq_zero_of_dimension_zero]

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set
open scoped ComplexConjugate

@[simp] theorem eval_polePolynomial {N : ℕ} (f : DeformationSpectrum N)
    (z w : ℂ) :
    (polePolynomial f z).eval w = ∏ i : Fin N, (w - ((f i : ℂ) - z)) := by
  change (evalRingHom w) (∏ i : Fin N, (X - C ((f i : ℂ) - z))) = _
  rw [map_prod]
  simp

@[simp] theorem eval_omittedPolePolynomial {N : ℕ} (f : DeformationSpectrum N)
    (z w : ℂ) :
    (omittedPolePolynomial f z).eval w =
      ∑ i : Fin N, ∏ j ∈ (Finset.univ.erase i),
        (w - ((f j : ℂ) - z)) := by
  change (evalRingHom w) (∑ i : Fin N, ∏ j ∈ (Finset.univ.erase i),
    (X - C ((f j : ℂ) - z))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_prod]
  simp

@[simp] theorem eval_dysonPolynomial {N : ℕ} (f : DeformationSpectrum N)
    (s : ℝ) (z w : ℂ) :
    (dysonPolynomial f s z).eval w =
      w * ∏ i : Fin N, (w - ((f i : ℂ) - z)) +
        ((s : ℂ) / (N : ℂ)) *
          ∑ i : Fin N, ∏ j ∈ (Finset.univ.erase i),
            (w - ((f j : ℂ) - z)) := by
  simp [dysonPolynomial]

/-- A non-pole zero of the cleared polynomial gives the algebraic MDE after the
change of variables `w = s m`. -/
theorem algebraic_mde_of_dysonPolynomial_root {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : s ≠ 0) {z w : ℂ}
    (hpole : ∀ i, w ≠ (f i : ℂ) - z)
    (hroot : (dysonPolynomial f s z).eval w = 0) :
    w / (s : ℂ) = average (entry f s z (w / (s : ℂ))) := by
  rw [eval_dysonPolynomial] at hroot
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hdiff : ∀ i, w - ((f i : ℂ) - z) ≠ 0 := fun i => sub_ne_zero.mpr (hpole i)
  unfold average entry
  simp only [mul_div_cancel₀ _ hsc]
  simp_rw [show ∀ i, (f i : ℂ) - z - w = -(w - ((f i : ℂ) - z)) by
    intro i; ring, inv_neg, Finset.sum_neg_distrib]
  field_simp [hNc, hsc, hdiff]
  let P : ℂ := ∏ i : Fin N, (w - ((f i : ℂ) - z))
  let B : ℂ := ∑ i : Fin N, ∏ j ∈ Finset.univ.erase i,
    (w - ((f j : ℂ) - z))
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hdiff i)
  have hsum : (∑ i : Fin N, (w - ((f i : ℂ) - z))⁻¹) * P = B := by
    simp only [P, B, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.prod_erase_mul _ _ hi]
    field_simp [hdiff i]
  apply mul_right_cancel₀ hP
  simp only [one_div]
  field_simp [hNc] at hroot
  have hw : w * (N : ℂ) * P = -((s : ℂ) * B) := by
    dsimp [P, B]
    linear_combination hroot
  calc
    w * (N : ℂ) * P = -((s : ℂ) * B) := hw
    _ = -((s : ℂ) * ∑ i : Fin N, (w - ((f i : ℂ) - z))⁻¹) * P := by
      linear_combination ((s : ℂ)) * hsum

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set

 theorem polePolynomial_monic {N : ℕ} (f : DeformationSpectrum N) (z : ℂ) :
    (polePolynomial f z).Monic := by
  unfold polePolynomial
  exact monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)

 theorem polePolynomial_natDegree {N : ℕ} (f : DeformationSpectrum N) (z : ℂ) :
    (polePolynomial f z).natDegree = N := by
  unfold polePolynomial
  simpa using natDegree_finsetProd_X_sub_C_eq_card
    (Finset.univ : Finset (Fin N)) (fun i => (f i : ℂ) - z)

 theorem omittedPolePolynomial_natDegree_le {N : ℕ}
    (f : DeformationSpectrum N) (z : ℂ) :
    (omittedPolePolynomial f z).natDegree ≤ N - 1 := by
  unfold omittedPolePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  simpa using (natDegree_finsetProd_X_sub_C_eq_card
    (Finset.univ.erase i) (fun j => (f j : ℂ) - z)).le

 theorem dysonPolynomial_lower_natDegree {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) :
    (C ((s : ℂ) / (N : ℂ)) * omittedPolePolynomial f z).natDegree <
      (X * polePolynomial f z).natDegree := by
  rw [(monic_X.natDegree_mul (polePolynomial_monic f z)), natDegree_X,
    polePolynomial_natDegree]
  apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
  apply lt_of_le_of_lt (omittedPolePolynomial_natDegree_le f z)
  omega

 theorem dysonPolynomial_monic {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) :
    (dysonPolynomial f s z).Monic := by
  unfold dysonPolynomial
  exact (monic_X.mul (polePolynomial_monic f z)).add_of_left
    (degree_lt_degree (dysonPolynomial_lower_natDegree hN f s z))

 theorem dysonPolynomial_natDegree {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) :
    (dysonPolynomial f s z).natDegree = N + 1 := by
  unfold dysonPolynomial
  rw [natDegree_add_eq_left_of_natDegree_lt
    (dysonPolynomial_lower_natDegree hN f s z)]
  rw [monic_X.natDegree_mul (polePolynomial_monic f z), natDegree_X,
    polePolynomial_natDegree]
  omega

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set

 theorem polePolynomial_nextCoeff {N : ℕ} (f : DeformationSpectrum N) (z : ℂ) :
    (polePolynomial f z).nextCoeff = -∑ i : Fin N, ((f i : ℂ) - z) := by
  unfold polePolynomial
  simpa using prod_X_sub_C_nextCoeff (s := (Finset.univ : Finset (Fin N)))
    (fun i => (f i : ℂ) - z)

 theorem dysonPolynomial_nextCoeff {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) :
    (dysonPolynomial f s z).nextCoeff = -∑ i : Fin N, ((f i : ℂ) - z) := by
  rw [nextCoeff, dysonPolynomial_natDegree hN]
  simp only [show N + 1 ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
  rw [dysonPolynomial, coeff_add]
  have hright : (C ((s : ℂ) / (N : ℂ)) * omittedPolePolynomial f z).coeff N = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    apply lt_of_le_of_lt (natDegree_C_mul_le _ _)
    exact (omittedPolePolynomial_natDegree_le f z).trans_lt (Nat.sub_lt hN Nat.zero_lt_one)
  rw [hright, add_zero]
  have hc := coeff_X_mul (polePolynomial f z) (N - 1)
  rw [show N - 1 + 1 = N by omega] at hc
  rw [hc]
  have hn := polePolynomial_nextCoeff f z
  rw [nextCoeff, polePolynomial_natDegree, ite_eq_right hN.ne'] at hn
  exact hn

 theorem dyson_roots_sum {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) (s : ℝ) (z : ℂ) :
    (dysonPolynomial f s z).roots.sum = ∑ i : Fin N, ((f i : ℂ) - z) := by
  have hsplits : (dysonPolynomial f s z).Splits := IsAlgClosed.splits _
  have hv := hsplits.nextCoeff_eq_neg_sum_roots_of_monic
    (dysonPolynomial_monic hN f s z)
  rw [dysonPolynomial_nextCoeff hN] at hv
  exact (neg_injective hv).symm

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set

/-- The algebraic equation itself forces the Herglotz sign whenever its effective
height is positive. -/
theorem algebraic_solution_im_pos_of_effectiveHeight_pos {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} {z m : ℂ}
    (heq : m = average (entry f s z m))
    (hheight : 0 < effectiveHeight s z m) : 0 < m.im := by
  have him : m.im = averageReal (fun i => (entry f s z m i).im) :=
    (congrArg Complex.im heq).trans (average_im hN _)
  rw [him]
  unfold averageReal
  apply div_pos
  · exact Finset.sum_pos (fun i _ => entry_im_pos f hheight i)
      ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  · exact_mod_cast hN

/-- Every zero of the cleared polynomial is either on/below the shifted pole
line, or is in the upper half-plane.  This remains true with repeated poles. -/
theorem dysonPolynomial_root_im_le_or_pos {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z w : ℂ}
    (hroot : (dysonPolynomial f s z).eval w = 0) :
    w.im ≤ -z.im ∨ 0 < w.im := by
  by_cases hpole : ∃ i, w = (f i : ℂ) - z
  · rcases hpole with ⟨i, rfl⟩
    left
    simp
  · have hpole' : ∀ i, w ≠ (f i : ℂ) - z := by simpa only [not_exists] using hpole
    have heq := algebraic_mde_of_dysonPolynomial_root hN f hs.ne' hpole' hroot
    by_cases hw : 0 < w.im
    · exact Or.inr hw
    · left
      have hsc : (0 : ℝ) < s := hs
      by_contra hle
      have himdiv : (w / (s : ℂ)).im = w.im / s := by
        simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          Complex.normSq_ofReal]
        field_simp; ring
      have hheight : 0 < effectiveHeight s z (w / (s : ℂ)) := by
        rw [effectiveHeight, himdiv, mul_div_cancel₀ _ hs.ne']
        linarith
      have hmpos := algebraic_solution_im_pos_of_effectiveHeight_pos hN f heq hheight
      rw [himdiv] at hmpos
      have : 0 < w.im := ((div_pos_iff.mp hmpos).resolve_right (by
        intro hneg
        exact (not_lt_of_ge hs.le) hneg.2)).1
      exact hw this

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set

/-- The root-count argument: a monic degree `N+1` cleared equation cannot put
all roots on or below the shifted pole line, because their Vieta sum has
imaginary part only `-N Im z`. -/
theorem exists_dysonPolynomial_root_im_pos {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    ∃ w : ℂ, (dysonPolynomial f s z).eval w = 0 ∧ 0 < w.im := by
  let p := dysonPolynomial f s z
  have hpmonic : p.Monic := dysonPolynomial_monic hN f s z
  have hpne : p ≠ 0 := hpmonic.ne_zero
  have hcard : p.roots.card = N + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, dysonPolynomial_natDegree hN]
  have himsum : (p.roots.map Complex.im).sum = -(N : ℝ) * z.im := by
    change (p.roots.map (⇑Complex.imAddGroupHom)).sum = _
    rw [← map_multiset_sum Complex.imAddGroupHom]
    rw [dyson_roots_sum hN]
    simp
  by_contra hex
  push Not at hex
  have hall : ∀ w ∈ p.roots, w.im ≤ -z.im := by
    intro w hw
    have hroot : p.eval w = 0 := by
      exact (mem_roots hpne).mp hw
    exact (dysonPolynomial_root_im_le_or_pos hN f hs hroot).resolve_right (not_lt_of_ge (hex w hroot))
  have hsumle : (p.roots.map Complex.im).sum ≤ (p.roots.card : ℝ) * (-z.im) := by
    have aux : ∀ r : Multiset ℂ, (∀ w ∈ r, w.im ≤ -z.im) →
        (r.map Complex.im).sum ≤ (r.card : ℝ) * (-z.im) := by
      intro r
      induction r using Multiset.induction_on with
      | empty => simp
      | @cons a r ih =>
          intro hr
          simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
            Nat.cast_add, Nat.cast_one]
          have ha := hr a (Multiset.mem_cons_self (s := r) a)
          have ht : ∀ w ∈ r, w.im ≤ -z.im := by
            intro w hw
            exact hr w (Multiset.mem_cons_of_mem hw)
          have hi := ih ht
          nlinarith
    exact aux p.roots hall
  rw [himsum, hcard] at hsumle
  norm_num at hsumle
  nlinarith

/-- Unconditional existence of the finite-dimensional upper Herglotz solution. -/
theorem exists_solution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    ∃ m : ℂ, IsSolution f s z m := by
  obtain ⟨w, hroot, hw⟩ := exists_dysonPolynomial_root_im_pos hN f hs hz
  have hpole : ∀ i, w ≠ (f i : ℂ) - z := by
    intro i hi
    have him := congrArg Complex.im hi
    simp at him
    linarith
  refine ⟨w / (s : ℂ), algebraic_mde_of_dysonPolynomial_root hN f hs.ne' hpole hroot, ?_⟩
  have himdiv : (w / (s : ℂ)).im = w.im / s := by
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal]
    field_simp; ring
  rw [himdiv]
  exact div_pos hw hs

/-- Existence and uniqueness, with no solution certificate in the input. -/
theorem existsUnique_solution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : 0 < z.im) :
    ∃! m : ℂ, IsSolution f s z m := by
  obtain ⟨m, hm⟩ := exists_solution hN f hs hz
  exact ⟨m, hm, fun m' hm' => solution_unique hN f hs hz hm' hm⟩

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.CEH

open Polynomial Set Filter
open scoped ComplexConjugate Topology

/-- The upper Herglotz branch, constructed from unconditional existence. -/
noncomputable def upperSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (z : ℂ) (hz : 0 < z.im) : ℂ :=
  Classical.choose (existsUnique_solution hN f hs hz).exists

 theorem upperSolution_isSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) (z : ℂ) (hz : 0 < z.im) :
    IsSolution f s z (upperSolution hN f hs z hz) :=
  Classical.choose_spec (existsUnique_solution hN f hs hz).exists

 theorem eq_upperSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z m : ℂ}
    (hz : 0 < z.im) (hm : IsSolution f s z m) :
    m = upperSolution hN f hs z hz :=
  (existsUnique_solution hN f hs hz).unique hm
    (upperSolution_isSolution hN f hs z hz)

/-- Algebraic scalar-MDE solutions commute with complex conjugation because the
finite deformation spectrum and variance are real. -/
theorem star_average_entry {N : ℕ} (f : DeformationSpectrum N)
    (s : ℝ) (z m : ℂ) :
    star (average (entry f s z m)) = average (entry f s (star z) (star m)) := by
  unfold average
  change (starRingEnd ℂ) ((∑ i, entry f s z m i) / (N : ℂ)) = _
  rw [map_div₀]
  congr 1
  · rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [entry, map_sub, map_mul]
  · simp

/-- Lower-half-plane version of the scalar Dyson equation. -/
def IsLowerSolution {N : ℕ} (f : DeformationSpectrum N) (s : ℝ)
    (z m : ℂ) : Prop :=
  m = average (entry f s z m) ∧ m.im < 0

/-- Existence in the lower half-plane follows by conjugating the upper branch. -/
theorem exists_lowerSolution {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z.im < 0) :
    ∃ m : ℂ, IsLowerSolution f s z m := by
  have hzstar : 0 < (star z).im := by simp; linarith
  let u := upperSolution hN f hs (star z) hzstar
  have hu := upperSolution_isSolution hN f hs (star z) hzstar
  refine ⟨star u, ?_, ?_⟩
  · calc
      star u = star (average (entry f s (star z) u)) := congrArg star (by simpa [u] using hu.1)
      _ = average (entry f s (star (star z)) (star u)) := star_average_entry f s (star z) u
      _ = average (entry f s z (star u)) := by simp
  · have hup : 0 < u.im := by simpa [u] using hu.2
    simpa using hup

/-- Lower-half-plane uniqueness, again by conjugation. -/
theorem lowerSolution_unique {N : ℕ} (hN : 0 < N)
    (f : DeformationSpectrum N) {s : ℝ} (hs : 0 < s) {z m₁ m₂ : ℂ}
    (hz : z.im < 0) (hm₁ : IsLowerSolution f s z m₁)
    (hm₂ : IsLowerSolution f s z m₂) : m₁ = m₂ := by
  have hzstar : 0 < (star z).im := by simp; linarith
  have hstar (m : ℂ) (hm : IsLowerSolution f s z m) :
      IsSolution f s (star z) (star m) := by
    refine ⟨?_, ?_⟩
    · calc
        star m = star (average (entry f s z m)) := congrArg star hm.1
        _ = average (entry f s (star z) (star m)) := star_average_entry f s z m
    · simp
      linarith [hm.2]
  have h := solution_unique hN f hs hzstar (hstar m₁ hm₁) (hstar m₂ hm₂)
  exact star_injective h

end CEHNative.BlockBand.CEH
