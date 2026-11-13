module

public import BlockBand.Coarea.Native.BlockBand.Counting.NormalizedDiagonalBlockGUE

/-!
# Transport between the two finite upper-triangular orderings

The ring law and singleton BlockGUE law select upper entries using different
finite linear enumerations.  This module orients each singleton pair in the
ring order, proves that this reindexing is injective, and transports mutual
independence through the possible conjugation and `sqrt c` rescaling.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

/-- Embed a singleton BlockGUE index into physical block `j`. -/
def singletonSite {p : Params} (j : ZMod p.n)
    (x : BlockGUE.Index (singletonBlockSize p.W)) : Site p.n p.W :=
  (j, x.2)

/-- The singleton-site embedding is injective. -/
theorem singletonSite_injective {p : Params} (j : ZMod p.n) :
    Function.Injective (singletonSite j) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  have h₁ : x₁ = y₁ := Subsingleton.elim _ _
  subst y₁
  have h₂ : x₂ = y₂ :=
    Fin.ext (congrArg (fun z : Site p.n p.W => z.2.val) h)
  subst y₂
  rfl

/-- The canonical BlockGUE order is antisymmetric. -/
theorem BlockGUE.index_eq_of_le_le {W : ℕ}
    {x y : BlockGUE.Index (singletonBlockSize W)}
    (hxy : BlockGUE.indexLE (singletonBlockSize W) x y)
    (hyx : BlockGUE.indexLE (singletonBlockSize W) y x) : x = y := by
  apply Fintype.equivFin (BlockGUE.Index (singletonBlockSize W)) |>.injective
  apply Fin.ext
  exact Nat.le_antisymm hxy hyx

/-- Orient a singleton BlockGUE upper pair in the physical ring's upper order. -/
def ringUpperPairOfSingleton {p : Params} (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W)) : UpperPair p :=
  if h : siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2) then
    ⟨(singletonSite j q.1.1, singletonSite j q.1.2), h⟩
  else
    ⟨(singletonSite j q.1.2, singletonSite j q.1.1),
      siteLE_reverse_of_not p _ _ h⟩

@[simp] theorem ringUpperPairOfSingleton_val_of_siteLE
    {p : Params} (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W))
    (h : siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2)) :
    (ringUpperPairOfSingleton j q).1 =
      (singletonSite j q.1.1, singletonSite j q.1.2) := by
  simp [ringUpperPairOfSingleton, h]

@[simp] theorem ringUpperPairOfSingleton_val_of_not_siteLE
    {p : Params} (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W))
    (h : ¬ siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2)) :
    (ringUpperPairOfSingleton j q).1 =
      (singletonSite j q.1.2, singletonSite j q.1.1) := by
  simp [ringUpperPairOfSingleton, h]

/-- Sorting singleton upper pairs into the ring order loses no information. -/
theorem ringUpperPairOfSingleton_injective {p : Params} (j : ZMod p.n) :
    Function.Injective (ringUpperPairOfSingleton j) := by
  intro q r hqr
  rcases q with ⟨⟨x, y⟩, hxy⟩
  rcases r with ⟨⟨u, v⟩, huv⟩
  have hval := congrArg Subtype.val hqr
  by_cases h₁ : siteLE p (singletonSite j x) (singletonSite j y)
  · by_cases h₂ : siteLE p (singletonSite j u) (singletonSite j v)
    · have hpair :
          (singletonSite j x, singletonSite j y) =
            (singletonSite j u, singletonSite j v) := by
          simpa [ringUpperPairOfSingleton, h₁, h₂] using hval
      have hx : x = u := singletonSite_injective j (Prod.mk.inj hpair).1
      have hy : y = v := singletonSite_injective j (Prod.mk.inj hpair).2
      subst u; subst v; rfl
    · have hpair :
          (singletonSite j x, singletonSite j y) =
            (singletonSite j v, singletonSite j u) := by
          simpa [ringUpperPairOfSingleton, h₁, h₂] using hval
      have hxv : x = v := singletonSite_injective j (Prod.mk.inj hpair).1
      have hyu : y = u := singletonSite_injective j (Prod.mk.inj hpair).2
      have hyx : BlockGUE.indexLE (singletonBlockSize p.W) y x := by
        simpa [hxv, hyu] using huv
      have hxy' : x = y := BlockGUE.index_eq_of_le_le hxy hyx
      subst y
      simp_all

  · by_cases h₂ : siteLE p (singletonSite j u) (singletonSite j v)
    · have hpair :
          (singletonSite j y, singletonSite j x) =
            (singletonSite j u, singletonSite j v) := by
          simpa [ringUpperPairOfSingleton, h₁, h₂] using hval
      have hyu : y = u := singletonSite_injective j (Prod.mk.inj hpair).1
      have hxv : x = v := singletonSite_injective j (Prod.mk.inj hpair).2
      have hyx : BlockGUE.indexLE (singletonBlockSize p.W) y x := by
        simpa [hyu, hxv] using huv
      have hxy' : x = y := BlockGUE.index_eq_of_le_le hxy hyx
      subst y
      simp_all
    · have hpair :
          (singletonSite j y, singletonSite j x) =
            (singletonSite j v, singletonSite j u) := by
          simpa [ringUpperPairOfSingleton, h₁, h₂] using hval
      have hy : y = v := singletonSite_injective j (Prod.mk.inj hpair).1
      have hx : x = u := singletonSite_injective j (Prod.mk.inj hpair).2
      subst u; subst v; rfl

/-- The scalar transport from the physical upper entry to the normalized
singleton entry.  Reversing the physical orientation introduces conjugation. -/
def singletonUpperTransform {p : Params} (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W)) : ℂ → ℂ :=
  if siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2) then
    fun z => ((Real.sqrt p.c)⁻¹ : ℂ) * z
  else
    fun z => ((Real.sqrt p.c)⁻¹ : ℂ) * star z

/-- Every scalar upper-coordinate transport is measurable. -/
theorem measurable_singletonUpperTransform {p : Params} (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W)) :
    Measurable (singletonUpperTransform j q) := by
  by_cases h : siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2)
  · simpa [singletonUpperTransform, h] using
      (continuous_const_mul ((Real.sqrt p.c)⁻¹ : ℂ)).measurable
  · rw [singletonUpperTransform, ite_eq_right h]
    change Measurable
      ((fun z : ℂ => ((Real.sqrt p.c)⁻¹ : ℂ) * z) ∘ star)
    exact ((continuous_const_mul ((Real.sqrt p.c)⁻¹ : ℂ)).comp
      Complex.continuous_conj).measurable

/-- A normalized singleton upper entry factors through the corresponding
physical-ring upper coordinate. -/
theorem Law.normalizedSingletonBlock_upper_factorization
    {p : Params} (M : Law p) (j : ZMod p.n)
    (q : BlockGUE.UpperPair (singletonBlockSize p.W)) (ω : M.Ω) :
    M.normalizedSingletonBlock j ω q.1.1 q.1.2 =
      singletonUpperTransform j q
        (M.H ω (ringUpperPairOfSingleton j q).1.1
          (ringUpperPairOfSingleton j q).1.2) := by
  by_cases h : siteLE p (singletonSite j q.1.1) (singletonSite j q.1.2)
  · rw [normalizedSingletonBlock_apply,
      ringUpperPairOfSingleton_val_of_siteLE j q h]
    change ((Real.sqrt p.c)⁻¹ : ℂ) *
      M.H ω (singletonSite j q.1.1) (singletonSite j q.1.2) = _
    simp [singletonUpperTransform, h]
  · have hHerm := congrFun
      (congrFun (M.H_hermitian ω) (singletonSite j q.1.1))
      (singletonSite j q.1.2)
    simp only [Matrix.conjTranspose_apply] at hHerm
    rw [normalizedSingletonBlock_apply,
      ringUpperPairOfSingleton_val_of_not_siteLE j q h]
    change ((Real.sqrt p.c)⁻¹ : ℂ) *
      M.H ω (singletonSite j q.1.1) (singletonSite j q.1.2) = _
    simp [singletonUpperTransform, h, hHerm]

/-- The normalized singleton upper entries are mutually independent, with no
compatibility assumption between the two opaque finite orderings. -/
theorem Law.normalizedDiagonalBlockUpperIndependence
    {p : Params} (M : Law p) (j : ZMod p.n) :
    NormalizedDiagonalBlockUpperIndependence M j := by
  refine ⟨?_⟩
  have hrestrict := iIndepFun.precomp
    (ringUpperPairOfSingleton_injective j) M.upper_independent
  have htransport := hrestrict.comp (fun q => singletonUpperTransform j q)
    (measurable_singletonUpperTransform j)
  simpa only [Function.comp_def,
    M.normalizedSingletonBlock_upper_factorization j] using htransport

/-- Within one block, two unequal sigma indices have unequal internal
coordinates. -/
theorem BlockGUE.snd_ne_of_ne_of_fst_eq {W : ℕ}
    {x y : BlockGUE.Index (singletonBlockSize W)}
    (hne : x ≠ y) (hfst : x.1 = y.1) : x.2 ≠ y.2 := by
  rintro h₂
  apply hne
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only at hfst h₂
  subst y₁
  subst y₂
  rfl

/-- Hermitian symmetry of the normalized singleton block, in the orientation
used to transfer scalar component statements. -/
theorem Law.normalizedSingletonBlock_eq_star_swap
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    M.normalizedSingletonBlock j ω x y =
      star (M.normalizedSingletonBlock j ω y x) := by
  exact (congrFun
    (congrFun (M.normalizedSingletonBlock_isHermitian j ω) x) y).symm

/-- The real component is unchanged when the singleton entry is reversed. -/
theorem Law.normalizedSingletonBlock_re_swap
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    (M.normalizedSingletonBlock j ω x y).re =
      (M.normalizedSingletonBlock j ω y x).re := by
  rw [M.normalizedSingletonBlock_eq_star_swap j ω x y]
  change ((starRingEnd ℂ) (M.normalizedSingletonBlock j ω y x)).re =
    (M.normalizedSingletonBlock j ω y x).re
  exact Complex.conj_re _

/-- The imaginary component changes sign when the singleton entry is reversed. -/
theorem Law.normalizedSingletonBlock_im_swap
    {p : Params} (M : Law p) (j : ZMod p.n) (ω : M.Ω)
    (x y : BlockGUE.Index (singletonBlockSize p.W)) :
    (M.normalizedSingletonBlock j ω x y).im =
      -(M.normalizedSingletonBlock j ω y x).im := by
  rw [M.normalizedSingletonBlock_eq_star_swap j ω x y]
  change ((starRingEnd ℂ) (M.normalizedSingletonBlock j ω y x)).im =
    -(M.normalizedSingletonBlock j ω y x).im
  exact Complex.conj_im _

/-- Component independence is valid in the BlockGUE upper ordering, even when
that ordering reverses the physical ring orientation. -/
theorem Law.normalizedSingletonBlock_components_independent_indexLE
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (_hindex : BlockGUE.indexLE (singletonBlockSize p.W) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    IndepFun (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (fun ω => (M.normalizedSingletonBlock j ω x y).im) M.P := by
  have h₂ : x.2 ≠ y.2 := BlockGUE.snd_ne_of_ne_of_fst_eq hne hfst
  by_cases hphysical : siteLE p (singletonSite j x) (singletonSite j y)
  · exact M.normalizedSingletonBlock_components_independent j x y hphysical h₂
  · have hreverse := siteLE_reverse_of_not p
      (singletonSite j x) (singletonSite j y) hphysical
    have hind := M.normalizedSingletonBlock_components_independent j y x
      hreverse h₂.symm
    have hind' := hind.neg_right
    rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).re) =
        (fun ω => (M.normalizedSingletonBlock j ω y x).re) by
      funext ω
      exact M.normalizedSingletonBlock_re_swap j ω x y]
    rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).im) =
        -(fun ω => (M.normalizedSingletonBlock j ω y x).im) by
      funext ω
      exact M.normalizedSingletonBlock_im_swap j ω x y]
    exact hind'

/-- The real component has the required centered Gaussian law in the BlockGUE
upper ordering. -/
theorem Law.normalizedSingletonBlock_offdiag_re_law_indexLE
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (_hindex : BlockGUE.indexLE (singletonBlockSize p.W) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).re)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P := by
  have h₂ : x.2 ≠ y.2 := BlockGUE.snd_ne_of_ne_of_fst_eq hne hfst
  by_cases hphysical : siteLE p (singletonSite j x) (singletonSite j y)
  · exact M.normalizedSingletonBlock_offdiag_re_law j x y hphysical h₂
  · have hreverse := siteLE_reverse_of_not p
      (singletonSite j x) (singletonSite j y) hphysical
    have hlaw := M.normalizedSingletonBlock_offdiag_re_law j y x
      hreverse h₂.symm
    rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).re) =
        (fun ω => (M.normalizedSingletonBlock j ω y x).re) by
      funext ω
      exact M.normalizedSingletonBlock_re_swap j ω x y]
    simpa [BlockGUE.entryVariance, hfst] using hlaw

/-- The imaginary component has the required centered Gaussian law in the
BlockGUE upper ordering. -/
theorem Law.normalizedSingletonBlock_offdiag_im_law_indexLE
    {p : Params} (M : Law p) (j : ZMod p.n)
    (x y : BlockGUE.Index (singletonBlockSize p.W))
    (_hindex : BlockGUE.indexLE (singletonBlockSize p.W) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    HasLaw (fun ω => (M.normalizedSingletonBlock j ω x y).im)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (singletonBlockSize p.W) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (singletonBlockSize_pos p.W_pos) x y) (by norm_num)⟩) M.P := by
  have h₂ : x.2 ≠ y.2 := BlockGUE.snd_ne_of_ne_of_fst_eq hne hfst
  by_cases hphysical : siteLE p (singletonSite j x) (singletonSite j y)
  · exact M.normalizedSingletonBlock_offdiag_im_law j x y hphysical h₂
  · have hreverse := siteLE_reverse_of_not p
      (singletonSite j x) (singletonSite j y) hphysical
    have hlaw := M.normalizedSingletonBlock_offdiag_im_law j y x
      hreverse h₂.symm
    have hneg := gaussianReal_neg hlaw
    rw [show (fun ω => (M.normalizedSingletonBlock j ω x y).im) =
        -(fun ω => (M.normalizedSingletonBlock j ω y x).im) by
      funext ω
      exact M.normalizedSingletonBlock_im_swap j ω x y]
    simpa [BlockGUE.entryVariance, hfst] using hneg

/-- The complete ordering transport is a theorem of the physical Gaussian ring
law; it requires no compatibility assumption between the ring and BlockGUE
enumerations. -/
theorem Law.normalizedDiagonalBlockGUEOrderingTransport
    {p : Params} (M : Law p) (j : ZMod p.n) :
    NormalizedDiagonalBlockGUEOrderingTransport M j where
  upper_independent :=
    (M.normalizedDiagonalBlockUpperIndependence j).upper_independent
  offdiag_components_independent :=
    M.normalizedSingletonBlock_components_independent_indexLE j
  offdiag_re_law :=
    M.normalizedSingletonBlock_offdiag_re_law_indexLE j
  offdiag_im_law :=
    M.normalizedSingletonBlock_offdiag_im_law_indexLE j

/-- Unconditional standard singleton-BlockGUE coupling for a normalized
physical diagonal block. -/
def Law.normalizedDiagonalBlockGUECoupling
    {p : Params} (M : Law p) (j : ZMod p.n) :
    NormalizedDiagonalBlockGUECoupling M j :=
  GaussianRing.normalizedDiagonalBlockGUECoupling M j
    (M.normalizedDiagonalBlockGUEOrderingTransport j)

end GaussianRing
end CoareaNative.BlockBand
