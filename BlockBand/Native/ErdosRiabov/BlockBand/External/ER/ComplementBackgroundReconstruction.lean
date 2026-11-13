module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.StrictCoordinateDisintegration

/-!
# Reconstruction of a deleted Gaussian-ring coordinate

This module gives the missing measurable factorization of the Hermitian matrix
with one strict upper coordinate removed.  The factor is the tuple of all
remaining upper entries, not the original sample.  Consequently the selected
real/imaginary pair is independent of the entire reconstructed background.

No local law, stochastic domination, moment estimate, or Ward estimate is
assumed.

Source: Erdős–Riabov, arXiv:2506.06441v1, coordinate conditioning in the
fluctuation-averaging proof of Theorem 3.3.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERComplementBackgroundReconstruction

open Matrix MeasureTheory ProbabilityTheory
open ERProductCoordinateAnalysis ERGaussianCoordinate
open ERStrictCoordinateDisintegration

local instance (p : Params) : NeZero p.n := p.nNeZero
local instance (p : Params) : Finite (UpperPair p) :=
  Finite.of_injective Subtype.val Subtype.val_injective
local instance (p : Params) : Fintype (UpperPair p) := Fintype.ofFinite _
local instance (p : Params) : DecidableEq (UpperPair p) := Classical.decEq _

/-- Antisymmetry of the canonical order on sites. -/
theorem siteLE_antisymm {p : Params} {x y : Site p.n p.W}
    (hxy : siteLE p x y) (hyx : siteLE p y x) : x = y := by
  apply p.siteIndexEquiv.injective
  apply Fin.ext
  exact le_antisymm hxy hyx

/-- The canonical upper representative of an ordered or reversed matrix
entry. -/
def upperPairFor (p : Params) (x y : Site p.n p.W) : UpperPair p :=
  if h : siteLE p x y then ⟨(x, y), h⟩ else
    ⟨(y, x), by
      unfold siteLE at h ⊢
      exact Nat.le_of_lt (Nat.lt_of_not_ge h)⟩

@[simp] theorem upperPairFor_of_siteLE {p : Params} {x y : Site p.n p.W}
    (h : siteLE p x y) : (upperPairFor p x y).1 = (x, y) := by
  simp [upperPairFor, h]

@[simp] theorem upperPairFor_of_not_siteLE {p : Params} {x y : Site p.n p.W}
    (h : ¬ siteLE p x y) : (upperPairFor p x y).1 = (y, x) := by
  simp [upperPairFor, h]

/-- Read a nonselected upper entry from the complementary tuple. -/
def complementValue {p : Params} (q r : UpperPair p) (hr : r ≠ q)
    (u : (s : (Finset.univ.erase q : Finset (UpperPair p))) → ℂ) : ℂ :=
  u ⟨r, by simp [hr]⟩

/-- Hermitian reconstruction of the matrix whose selected strict upper entry
and its conjugate have been set to zero. -/
def reconstructOffdiagBackground (p : Params) (q : UpperPair p)
    (u : (r : (Finset.univ.erase q : Finset (UpperPair p))) → ℂ) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  fun i j =>
    let r := upperPairFor p i j
    if hr : r = q then 0
    else if _hij : siteLE p i j then
      if i = j then ((complementValue q r hr u).re : ℂ)
      else complementValue q r hr u
    else starRingEnd ℂ (complementValue q r hr u)

/-- Reconstruction from complementary upper entries is measurable as a
matrix-valued map. -/
theorem measurable_reconstructOffdiagBackground {p : Params} (q : UpperPair p) :
    Measurable (reconstructOffdiagBackground p q) := by
  apply Matrix.measurable_iff.mpr
  intro i j
  unfold reconstructOffdiagBackground complementValue
  fun_prop

/-- A strict upper pair cannot also be upper triangular after reversal. -/
theorem not_siteLE_reverse_of_ne {p : Params} (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) : ¬ siteLE p q.1.2 q.1.1 := by
  intro h
  exact hne (siteLE_antisymm q.2 h)

/-- Away from the selected entry and its transpose, deleting a coordinate
does not change a matrix entry. -/
theorem offdiagBackground_apply_of_ne
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ)
    {x y i j : ι} (hxy : (i, j) ≠ (x, y)) (hyx : (i, j) ≠ (y, x)) :
    offdiagBackground H x y i j = H i j := by
  have hxy' : i ≠ x ∨ j ≠ y := by
    by_cases hix : i = x
    · right
      intro hjy
      exact hxy (Prod.ext hix hjy)
    · exact Or.inl hix
  have hyx' : i ≠ y ∨ j ≠ x := by
    by_cases hiy : i = y
    · right
      intro hjx
      exact hyx (Prod.ext hiy hjx)
    · exact Or.inl hiy
  rcases hxy' with hix | hjy
  · rcases hyx' with hiy | hjx
    · simp [offdiagBackground, realDirection, imaginaryDirection,
        hix.symm, hiy.symm]
    · simp [offdiagBackground, realDirection, imaginaryDirection,
        hix.symm, hjx.symm]
  · rcases hyx' with hiy | hjx
    · simp [offdiagBackground, realDirection, imaginaryDirection,
        hjy.symm, hiy.symm]
    · simp [offdiagBackground, realDirection, imaginaryDirection,
        hjy.symm, hjx.symm]

/-- Both orientations of a deleted strict Hermitian coordinate vanish. -/
theorem offdiagBackground_apply_reverse
    {ι : Type*} [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) {x y : ι} (hxy : x ≠ y) :
    offdiagBackground H x y y x = 0 := by
  have hb := offdiagBackground_isHermitian H hH x y
  rw [← hb.apply y x, offdiagBackground_apply H hxy]
  simp

/-- A diagonal entry of a Hermitian complex matrix is its real part. -/
theorem hermitian_diag_eq_re
    {ι : Type*} (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (i : ι) :
    ((H i i).re : ℂ) = H i i := by
  have h := hH.apply i i
  apply Complex.ext
  · simp
  · have him : -(H i i).im = (H i i).im := by
      simpa using congrArg Complex.im h
    simp only [Complex.ofReal_im]
    linarith

/-- The complement reconstruction agrees exactly with deleting the selected
coordinate from any Hermitian matrix. -/
theorem reconstruct_complement_eq_offdiagBackground
    {p : Params} (H : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hH : H.IsHermitian) (q : UpperPair p) (hne : q.1.1 ≠ q.1.2) :
    reconstructOffdiagBackground p q
      (fun r : (Finset.univ.erase q : Finset (UpperPair p)) =>
        H r.1.1.1 r.1.1.2) =
      offdiagBackground H q.1.1 q.1.2 := by
  ext i j
  by_cases hij : siteLE p i j
  · have hup : (upperPairFor p i j).1 = (i, j) := upperPairFor_of_siteLE hij
    by_cases hr : upperPairFor p i j = q
    · have hpair : (i, j) = q.1 := by simpa [hup] using congrArg Subtype.val hr
      have hi : i = q.1.1 := congrArg Prod.fst hpair
      have hj : j = q.1.2 := congrArg Prod.snd hpair
      subst i; subst j
      simp [reconstructOffdiagBackground, hr, offdiagBackground_apply H hne]
    · have hneij : (i, j) ≠ q.1 := by
        intro heq
        apply hr
        apply Subtype.ext
        simpa [hup]
      have hnerev : (i, j) ≠ (q.1.2, q.1.1) := by
        intro heq
        have hyx : siteLE p q.1.2 q.1.1 := by
          have hi := congrArg Prod.fst heq
          have hj := congrArg Prod.snd heq
          simp only at hi hj
          subst i
          subst j
          exact hij
        exact (not_siteLE_reverse_of_ne q hne) hyx
      rw [offdiagBackground_apply_of_ne H hneij hnerev]
      by_cases heq : i = j
      · subst j
        simpa [reconstructOffdiagBackground, hr, hij, complementValue] using
          hermitian_diag_eq_re H hH i
      · simp [reconstructOffdiagBackground, hr, hij, heq, complementValue]
  · have hji : siteLE p j i := by
      unfold siteLE at hij ⊢
      omega
    have hup : (upperPairFor p i j).1 = (j, i) := upperPairFor_of_not_siteLE hij
    by_cases hr : upperPairFor p i j = q
    · have hpair : (j, i) = q.1 := by simpa [hup] using congrArg Subtype.val hr
      have hj : j = q.1.1 := congrArg Prod.fst hpair
      have hi : i = q.1.2 := congrArg Prod.snd hpair
      subst i; subst j
      simpa [reconstructOffdiagBackground, hr] using
        (offdiagBackground_apply_reverse H hH hne).symm
    · have hneji : (j, i) ≠ q.1 := by
        intro heq
        apply hr
        apply Subtype.ext
        simpa [hup]
      have hnxy : (i, j) ≠ q.1 := by
        intro heq
        have hi := congrArg Prod.fst heq
        have hj := congrArg Prod.snd heq
        simp only at hi hj
        subst i
        subst j
        exact hij q.2
      rw [offdiagBackground_apply_of_ne H hnxy (by
        intro heq
        apply hneji
        apply Prod.ext
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq)]
      simpa [reconstructOffdiagBackground, hr, hij, complementValue] using
        hH.apply i j

/-- Pointwise factorization of the removed background through the
complementary upper-entry tuple. -/
theorem Law.reconstruct_complementTuple_eq_offdiagBackground
    {p : Params} (M : Law p) (q : UpperPair p) (hne : q.1.1 ≠ q.1.2)
    (ω : M.Ω) :
    reconstructOffdiagBackground p q
      (complementTuple (upperEntryFamily M) q ω) =
      offdiagBackground (M.H ω) q.1.1 q.1.2 := by
  exact reconstruct_complement_eq_offdiagBackground
    (M.H ω) (M.isHermitian ω) q hne

/-- The strict selected coordinate pair is independent of the full Hermitian
background reconstructed from all remaining upper entries. -/
theorem Law.offdiagPair_indep_background
    {p : Params} (M : Law p) (q : UpperPair p) (hne : q.1.1 ≠ q.1.2) :
    IndepFun
      (fun ω => ((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im))
      (fun ω => offdiagBackground (M.H ω) q.1.1 q.1.2) M.P := by
  have h := (Law.offdiagPair_indep_complement M q).comp measurable_id
    (measurable_reconstructOffdiagBackground q)
  simpa only [id_eq, Function.comp_def,
    Law.reconstruct_complementTuple_eq_offdiagBackground M q hne] using h

/-- The removed background is measurable, through its complement factorization. -/
theorem Law.measurable_offdiagBackground_via_complement
    {p : Params} (M : Law p) (q : UpperPair p) (hne : q.1.1 ≠ q.1.2) :
    Measurable (fun ω => offdiagBackground (M.H ω) q.1.1 q.1.2) := by
  rw [← funext (Law.reconstruct_complementTuple_eq_offdiagBackground M q hne)]
  exact (measurable_reconstructOffdiagBackground q).comp
    (measurable_singletonTuple_complementTuple
      (upperEntryFamily M) q (measurable_upperEntryFamily M)).2

/-- Exact strict-coordinate/background product law, now with the concrete
Hermitian background rather than an abstract complementary tuple. -/
theorem Law.offdiagGaussian_background_productLaw
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2) :
    M.P.map (fun ω =>
      (((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im),
        offdiagBackground (M.H ω) q.1.1 q.1.2)) =
      ((gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩).prod
       (gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩)).prod
       (M.P.map (fun ω =>
         offdiagBackground (M.H ω) q.1.1 q.1.2)) := by
  have hprod := IndepFun.map_prod_eq_prod_map_map
    (((Complex.measurable_re.comp
      (M.measurable_entry q.1.1 q.1.2)).prodMk
      (Complex.measurable_im.comp
        (M.measurable_entry q.1.1 q.1.2))).aemeasurable)
    ((Law.measurable_offdiagBackground_via_complement M q hne).aemeasurable)
    (Law.offdiagPair_indep_background M q hne)
  have hprod' :
      M.P.map (fun ω =>
        (((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im),
          offdiagBackground (M.H ω) q.1.1 q.1.2)) =
        (M.P.map (fun ω =>
          ((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im))).prod
        (M.P.map (fun ω =>
          offdiagBackground (M.H ω) q.1.1 q.1.2)) := by
    simpa only [Function.comp_def] using hprod
  rw [Law.offdiagPair_gaussian_productLaw M q.1.1 q.1.2 q.2 hne] at hprod'
  exact hprod'

/-- Arbitrary jointly background-dependent tests may be transferred from the
matrix law to the exact two-real-Gaussian/product-background law.  In
particular, resolvent monomials need not factor into separate functions. -/
theorem Law.integral_offdiagGaussian_background
    {p : Params} (M : Law p) (q : UpperPair p)
    (hne : q.1.1 ≠ q.1.2)
    {Φ : ((ℝ × ℝ) ×
      Matrix (Site p.n p.W) (Site p.n p.W) ℂ) → ℂ}
    (hΦ : AEStronglyMeasurable Φ
      (((gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩).prod
       (gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩)).prod
       (M.P.map (fun ω =>
         offdiagBackground (M.H ω) q.1.1 q.1.2)))) :
    (∫ ω, Φ
      (((M.H ω q.1.1 q.1.2).re, (M.H ω q.1.1 q.1.2).im),
        offdiagBackground (M.H ω) q.1.1 q.1.2) ∂M.P) =
      ∫ v, Φ v ∂
      (((gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩).prod
       (gaussianReal 0
        ⟨ERProfile.siteCovariance p q.1.1 q.1.2 / 2,
          div_nonneg (varianceProfile_nonneg p q.1.1 q.1.2) (by norm_num)⟩)).prod
       (M.P.map (fun ω =>
         offdiagBackground (M.H ω) q.1.1 q.1.2))) := by
  symm
  rw [← Law.offdiagGaussian_background_productLaw M q hne] at hΦ ⊢
  apply integral_map
  · exact ((((Complex.measurable_re.comp
      (M.measurable_entry q.1.1 q.1.2)).prodMk
      (Complex.measurable_im.comp
        (M.measurable_entry q.1.1 q.1.2))).prodMk
      (Law.measurable_offdiagBackground_via_complement M q hne))).aemeasurable
  · exact hΦ

end ERComplementBackgroundReconstruction
end GaussianRing
end ERNative.BlockBand
