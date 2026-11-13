module

public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# Monic discriminant algebra

Discriminants of monic polynomials commute with coefficient homomorphisms, and a monic complex
polynomial has vanishing discriminant exactly when it is not separable; this is the algebra
behind the almost-sure simplicity of the physical spectrum.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Parameters
open Matrix Polynomial

/-- Polynomial discriminants of monic polynomials commute with coefficient
homomorphisms into a nontrivial ring. -/
theorem Polynomial.discr_map_of_monic {R S : Type*}
    [CommRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (p : R[X]) (hp : p.Monic) :
    (p.map f).discr = f p.discr := by
  rw [Polynomial.discr, Polynomial.discr]
  have hd : (p.map f).natDegree = p.natDegree := hp.natDegree_map f
  let e : Fin ((p.map f).natDegree - 1 + (p.map f).natDegree) ≃
      Fin (p.natDegree - 1 + p.natDegree) := finCongr (by omega)
  have hm : (p.map f).sylvesterDeriv.reindex e e =
      (p.sylvesterDeriv).map f := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.reindex_apply, Matrix.submatrix, Polynomial.sylvesterDeriv,
      Polynomial.sylvester, e, hd]
    split_ifs <;> simp_all [Matrix.updateRow_apply, Fin.addCases]
    split_ifs <;> simp_all
  rw [← Matrix.det_reindex_self e, hm, map_mul, map_pow, map_neg, map_one, hd]
  change (RingHom.mapMatrix f p.sylvesterDeriv).det * _ = _
  rw [RingHom.map_det]

/-- A monic separable polynomial over a field has nonzero discriminant. -/
theorem Polynomial.discr_ne_zero_of_monic_separable
    {p : ℂ[X]} (hp : p.Monic) (hsep : p.Separable) : p.discr ≠ 0 := by
  by_cases hdeg : p.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg]
    intro h
    have hC := Polynomial.discr_C (1 : ℂ)
    rw [show (1 : ℂ[X]) = Polynomial.C 1 by simp, hC] at h
    exact one_ne_zero h
  · have hpos : 0 < p.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
    have hr : IsUnit (p.resultant p.derivative) :=
      (Polynomial.isUnit_resultant_iff_isCoprime hp).2 hsep
    rw [Polynomial.natDegree_derivative] at hr
    have heq := Polynomial.resultant_deriv hpos
    rw [hp.leadingCoeff, mul_one] at heq
    intro hd
    rw [hd, mul_zero] at heq
    exact hr.ne_zero heq

/-- For a monic complex polynomial, vanishing of the discriminant is exactly
failure of separability, i.e. the algebraic repeated-root condition. -/
theorem Polynomial.discr_eq_zero_iff_not_separable
    {p : ℂ[X]} (hp : p.Monic) :
    p.discr = 0 ↔ ¬p.Separable := by
  constructor
  · intro hd hsep
    exact (Polynomial.discr_ne_zero_of_monic_separable hp hsep) hd
  · intro hnsep
    by_contra hd
    by_cases hdeg : p.natDegree = 0
    · rw [Polynomial.eq_one_of_monic_natDegree_zero hp hdeg] at hnsep
      exact hnsep Polynomial.separable_one
    · have hpos : 0 < p.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
      have heq := Polynomial.resultant_deriv hpos
      rw [hp.leadingCoeff, mul_one] at heq
      have hrneFixed :
          p.resultant p.derivative p.natDegree (p.natDegree - 1) ≠ 0 := by
        rw [heq]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hd
      have hrne : p.resultant p.derivative ≠ 0 := by
        rw [Polynomial.natDegree_derivative]
        exact hrneFixed
      have hrunit : IsUnit (p.resultant p.derivative) :=
        (isUnit_iff_ne_zero.mpr hrne)
      exact hnsep ((Polynomial.isUnit_resultant_iff_isCoprime hp).mp hrunit)

end BlockBand.Parameters
