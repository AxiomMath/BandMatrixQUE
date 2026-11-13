module

public import BlockBand.Coarea.Native.BlockBand.Counting.NormalizedDiagonalBlockGUEOrdering
public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalMultiBlockCountTransport

/-!
# Simultaneous normalization of all physical diagonal blocks

This module extracts every diagonal `W × W` block of the Gaussian ring at once and
rescales by `sqrt c`.  It constructs the resulting multi-block GUE law directly from
`GaussianRing.Law`.

The key simultaneous step injectively reorients the global `BlockGUE.UpperPair`
coordinates into the physical upper-triangular family.  Within-block entries are
rescaled (and conjugated if the two opaque orderings disagree), while cross-block
entries are sent through the constant-zero transform.  Coordinatewise measurable
transformation of the ring's mutually independent upper family therefore proves the
full global independence field without an extra hypothesis.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- Embed the joint normalized block index into the physical ring sites. -/
def allDiagonalSite {p : Params}
    (x : BlockGUE.Index (physicalBlockSizes p)) : Site p.n p.W :=
  ((x.1 : ZMod p.n), x.2)

/-- The joint normalized index embeds injectively into physical ring sites. -/
theorem allDiagonalSite_injective {p : Params} :
    Function.Injective (@allDiagonalSite p) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  have houterZ : (x₁ : ZMod p.n) = (y₁ : ZMod p.n) :=
    congrArg Prod.fst h
  have houterVal := congrArg ZMod.val houterZ
  have houter : x₁ = y₁ := by
    apply Fin.ext
    simpa [ZMod.val_natCast_of_lt x₁.isLt,
      ZMod.val_natCast_of_lt y₁.isLt] using houterVal
  subst y₁
  have hinner : x₂ = y₂ := Fin.ext (congrArg (fun z : Site p.n p.W => z.2.val) h)
  subst y₂
  rfl

/-- Forget the outer block label and regard an internal coordinate as an index of a
singleton block. -/
def singletonIndexOfAll {p : Params}
    (x : BlockGUE.Index (physicalBlockSizes p)) :
    BlockGUE.Index (singletonBlockSize p.W) :=
  ⟨0, x.2⟩

/-- Simultaneously extract and normalize all physical diagonal blocks, setting every
cross-block entry to zero.  The normalization is the paper's identity
`H_{jj} = sqrt(c) G_j`. -/
def Law.normalizedAllDiagonalBlocks {p : Params} (M : Law p) (ω : M.Ω) :
    Matrix (BlockGUE.Index (physicalBlockSizes p))
      (BlockGUE.Index (physicalBlockSizes p)) ℂ :=
  fun x y => if x.1 = y.1 then
    ((Real.sqrt p.c)⁻¹ : ℂ) * M.H ω (allDiagonalSite x) (allDiagonalSite y)
  else 0

/-- Entrywise form on one diagonal block. -/
@[simp] theorem Law.normalizedAllDiagonalBlocks_apply_of_fst_eq
    {p : Params} (M : Law p) (ω : M.Ω)
    (x y : BlockGUE.Index (physicalBlockSizes p)) (h : x.1 = y.1) :
    M.normalizedAllDiagonalBlocks ω x y =
      ((Real.sqrt p.c)⁻¹ : ℂ) * M.H ω (allDiagonalSite x) (allDiagonalSite y) := by
  simp [Law.normalizedAllDiagonalBlocks, h]

/-- Cross-block entries vanish pointwise, rather than merely almost surely. -/
@[simp] theorem Law.normalizedAllDiagonalBlocks_apply_of_fst_ne
    {p : Params} (M : Law p) (ω : M.Ω)
    (x y : BlockGUE.Index (physicalBlockSizes p)) (h : x.1 ≠ y.1) :
    M.normalizedAllDiagonalBlocks ω x y = 0 := by
  simp [Law.normalizedAllDiagonalBlocks, h]

/-- The simultaneous normalized matrix is measurable. -/
theorem Law.measurable_normalizedAllDiagonalBlocks
    {p : Params} (M : Law p) :
    Measurable M.normalizedAllDiagonalBlocks := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases h : x.1 = y.1
  · simp only [Law.normalizedAllDiagonalBlocks, h, ite_true]
    exact (M.measurable_entry _ _).const_mul _
  · simp only [Law.normalizedAllDiagonalBlocks, h, ite_false]
    exact measurable_const

/-- Simultaneous diagonal-block extraction preserves Hermitian symmetry. -/
theorem Law.normalizedAllDiagonalBlocks_isHermitian
    {p : Params} (M : Law p) (ω : M.Ω) :
    (M.normalizedAllDiagonalBlocks ω).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext x y
  by_cases h : x.1 = y.1
  · have hH := congrFun (congrFun (M.H_hermitian ω) (allDiagonalSite x))
      (allDiagonalSite y)
    simp only [Matrix.conjTranspose_apply] at hH
    rw [Matrix.conjTranspose_apply,
      M.normalizedAllDiagonalBlocks_apply_of_fst_eq ω y x h.symm,
      M.normalizedAllDiagonalBlocks_apply_of_fst_eq ω x y h]
    rw [star_mul', hH]
    congr 1
    norm_num
  · have hyx : y.1 ≠ x.1 := Ne.symm h
    simp [Law.normalizedAllDiagonalBlocks, h, hyx]

/-- The exact block-diagonal conclusion required by `BlockGUE.Law`. -/
theorem Law.normalizedAllDiagonalBlocks_block_diagonal
    {p : Params} (M : Law p) (x y : BlockGUE.Index (physicalBlockSizes p))
    (h : x.1 ≠ y.1) :
    ∀ᵐ ω ∂M.P, M.normalizedAllDiagonalBlocks ω x y = 0 := by
  exact Filter.Eventually.of_forall fun ω =>
    M.normalizedAllDiagonalBlocks_apply_of_fst_ne ω x y h

/-- On one outer block, simultaneous extraction is exactly the previously constructed
normalized singleton block. -/
theorem Law.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock
    {p : Params} (M : Law p) (ω : M.Ω)
    (x y : BlockGUE.Index (physicalBlockSizes p)) (h : x.1 = y.1) :
    M.normalizedAllDiagonalBlocks ω x y =
      M.normalizedSingletonBlock (x.1 : ZMod p.n) ω
        (singletonIndexOfAll x) (singletonIndexOfAll y) := by
  rw [M.normalizedAllDiagonalBlocks_apply_of_fst_eq ω x y h,
    normalizedSingletonBlock_apply]
  simp only [allDiagonalSite, singletonIndexOfAll]
  rw [h]

/-- Unequal indices in the same outer block have unequal internal coordinates. -/
theorem snd_ne_of_ne_of_fst_eq_all {p : Params}
    {x y : BlockGUE.Index (physicalBlockSizes p)}
    (hne : x ≠ y) (hfst : x.1 = y.1) : x.2 ≠ y.2 := by
  rintro h₂
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only at hfst h₂
  subst y₁
  subst y₂
  exact hne rfl

/-- The global diagonal entries have the exact PSSS Gaussian normalization. -/
theorem Law.normalizedAllDiagonalBlocks_diagonal_re_law
    {p : Params} (M : Law p)
    (x : BlockGUE.Index (physicalBlockSizes p)) :
    HasLaw (fun ω => (M.normalizedAllDiagonalBlocks ω x x).re)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (physicalBlockSizes p) x x,
          BlockGUE.entryVariance_nonneg (physicalBlockSizes_pos p) x x⟩) M.P := by
  rw [show (fun ω => (M.normalizedAllDiagonalBlocks ω x x).re) =
      (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω
        (singletonIndexOfAll x) (singletonIndexOfAll x)).re) by
    funext ω
    rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x x rfl]]
  simpa [BlockGUE.entryVariance, physicalBlockSizes, singletonBlockSize] using
    M.normalizedSingletonBlock_diagonal_re_law
      (x.1 : ZMod p.n) (singletonIndexOfAll x)

/-- The global diagonal entries are real almost surely. -/
theorem Law.normalizedAllDiagonalBlocks_diagonal_im_zero
    {p : Params} (M : Law p)
    (x : BlockGUE.Index (physicalBlockSizes p)) :
    ∀ᵐ ω ∂M.P, (M.normalizedAllDiagonalBlocks ω x x).im = 0 := by
  filter_upwards [
    M.normalizedSingletonBlock_diagonal_im_zero
      (x.1 : ZMod p.n) (singletonIndexOfAll x)] with ω hω
  rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x x rfl]
  exact hω

/-- Inside one physical block, real and imaginary parts of a strict upper entry remain
independent.  The proof is insensitive to the unrelated global and singleton
enumerations. -/
theorem Law.normalizedAllDiagonalBlocks_offdiag_components_independent
    {p : Params} (M : Law p)
    (x y : BlockGUE.Index (physicalBlockSizes p))
    (_hindex : BlockGUE.indexLE (physicalBlockSizes p) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    IndepFun (fun ω => (M.normalizedAllDiagonalBlocks ω x y).re)
      (fun ω => (M.normalizedAllDiagonalBlocks ω x y).im) M.P := by
  let sx := singletonIndexOfAll x
  let sy := singletonIndexOfAll y
  have hsne : sx ≠ sy := by
    intro h
    apply snd_ne_of_ne_of_fst_eq_all hne hfst
    apply Fin.ext
    exact congrArg (fun z : BlockGUE.Index (singletonBlockSize p.W) => z.2.val) h
  have hsfirst : sx.1 = sy.1 := Subsingleton.elim _ _
  have hre : (fun ω => (M.normalizedAllDiagonalBlocks ω x y).re) =
      (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).re) := by
    funext ω
    rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x y hfst]
  have him : (fun ω => (M.normalizedAllDiagonalBlocks ω x y).im) =
      (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).im) := by
    funext ω
    rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x y hfst]
  rw [hre, him]
  by_cases hs : BlockGUE.indexLE (singletonBlockSize p.W) sx sy
  · exact M.normalizedSingletonBlock_components_independent_indexLE
      (x.1 : ZMod p.n) sx sy hs hsne hsfirst
  · have hrev : BlockGUE.indexLE (singletonBlockSize p.W) sy sx := by
      unfold BlockGUE.indexLE at hs ⊢
      omega
    have hind := M.normalizedSingletonBlock_components_independent_indexLE
      (x.1 : ZMod p.n) sy sx hrev hsne.symm hsfirst.symm
    have hind' := hind.neg_right
    rw [show (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).re) =
        (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sy sx).re) by
      funext ω
      exact M.normalizedSingletonBlock_re_swap (x.1 : ZMod p.n) ω sx sy]
    rw [show (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).im) =
        -(fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sy sx).im) by
      funext ω
      exact M.normalizedSingletonBlock_im_swap (x.1 : ZMod p.n) ω sx sy]
    exact hind'

/-- Every within-block strict upper real component has variance `1/(2W)` in the
simultaneous normalization. -/
theorem Law.normalizedAllDiagonalBlocks_offdiag_re_law
    {p : Params} (M : Law p)
    (x y : BlockGUE.Index (physicalBlockSizes p))
    (_hindex : BlockGUE.indexLE (physicalBlockSizes p) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    HasLaw (fun ω => (M.normalizedAllDiagonalBlocks ω x y).re)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (physicalBlockSizes p) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (physicalBlockSizes_pos p) x y) (by norm_num)⟩) M.P := by
  let sx := singletonIndexOfAll x
  let sy := singletonIndexOfAll y
  have hsne : sx ≠ sy := by
    intro h
    apply snd_ne_of_ne_of_fst_eq_all hne hfst
    apply Fin.ext
    exact congrArg (fun z : BlockGUE.Index (singletonBlockSize p.W) => z.2.val) h
  have hsfirst : sx.1 = sy.1 := Subsingleton.elim _ _
  rw [show (fun ω => (M.normalizedAllDiagonalBlocks ω x y).re) =
      (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).re) by
    funext ω
    rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x y hfst]]
  by_cases hs : BlockGUE.indexLE (singletonBlockSize p.W) sx sy
  · simpa [BlockGUE.entryVariance, physicalBlockSizes, singletonBlockSize,
      hfst, hsfirst] using
      M.normalizedSingletonBlock_offdiag_re_law_indexLE
        (x.1 : ZMod p.n) sx sy hs hsne hsfirst
  · have hrev : BlockGUE.indexLE (singletonBlockSize p.W) sy sx := by
      unfold BlockGUE.indexLE at hs ⊢
      omega
    have hlaw := M.normalizedSingletonBlock_offdiag_re_law_indexLE
      (x.1 : ZMod p.n) sy sx hrev hsne.symm hsfirst.symm
    rw [show (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).re) =
        (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sy sx).re) by
      funext ω
      exact M.normalizedSingletonBlock_re_swap (x.1 : ZMod p.n) ω sx sy]
    simpa [BlockGUE.entryVariance, physicalBlockSizes, singletonBlockSize,
      hfst, hsfirst] using hlaw

/-- Every within-block strict upper imaginary component has variance `1/(2W)` in the
simultaneous normalization. -/
theorem Law.normalizedAllDiagonalBlocks_offdiag_im_law
    {p : Params} (M : Law p)
    (x y : BlockGUE.Index (physicalBlockSizes p))
    (_hindex : BlockGUE.indexLE (physicalBlockSizes p) x y)
    (hne : x ≠ y) (hfst : x.1 = y.1) :
    HasLaw (fun ω => (M.normalizedAllDiagonalBlocks ω x y).im)
      (gaussianReal 0
        ⟨BlockGUE.entryVariance (physicalBlockSizes p) x y / 2,
          div_nonneg (BlockGUE.entryVariance_nonneg
            (physicalBlockSizes_pos p) x y) (by norm_num)⟩) M.P := by
  let sx := singletonIndexOfAll x
  let sy := singletonIndexOfAll y
  have hsne : sx ≠ sy := by
    intro h
    apply snd_ne_of_ne_of_fst_eq_all hne hfst
    apply Fin.ext
    exact congrArg (fun z : BlockGUE.Index (singletonBlockSize p.W) => z.2.val) h
  have hsfirst : sx.1 = sy.1 := Subsingleton.elim _ _
  rw [show (fun ω => (M.normalizedAllDiagonalBlocks ω x y).im) =
      (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).im) by
    funext ω
    rw [M.normalizedAllDiagonalBlocks_eq_normalizedSingletonBlock ω x y hfst]]
  by_cases hs : BlockGUE.indexLE (singletonBlockSize p.W) sx sy
  · simpa [BlockGUE.entryVariance, physicalBlockSizes, singletonBlockSize,
      hfst, hsfirst] using
      M.normalizedSingletonBlock_offdiag_im_law_indexLE
        (x.1 : ZMod p.n) sx sy hs hsne hsfirst
  · have hrev : BlockGUE.indexLE (singletonBlockSize p.W) sy sx := by
      unfold BlockGUE.indexLE at hs ⊢
      omega
    have hlaw := M.normalizedSingletonBlock_offdiag_im_law_indexLE
      (x.1 : ZMod p.n) sy sx hrev hsne.symm hsfirst.symm
    have hneg := gaussianReal_neg hlaw
    rw [show (fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sx sy).im) =
        -(fun ω => (M.normalizedSingletonBlock (x.1 : ZMod p.n) ω sy sx).im) by
      funext ω
      exact M.normalizedSingletonBlock_im_swap (x.1 : ZMod p.n) ω sx sy]
    simpa [BlockGUE.entryVariance, physicalBlockSizes, singletonBlockSize,
      hfst, hsfirst] using hneg

/-- Orient a global BlockGUE upper pair in the physical ring ordering. -/
def ringUpperPairOfAll {p : Params}
    (q : BlockGUE.UpperPair (physicalBlockSizes p)) : UpperPair p :=
  if h : siteLE p (allDiagonalSite q.1.1) (allDiagonalSite q.1.2) then
    ⟨(allDiagonalSite q.1.1, allDiagonalSite q.1.2), h⟩
  else
    ⟨(allDiagonalSite q.1.2, allDiagonalSite q.1.1),
      siteLE_reverse_of_not p _ _ h⟩

/-- The simultaneous orientation map loses no upper-triangular coordinate. -/
theorem ringUpperPairOfAll_injective {p : Params} :
    Function.Injective (@ringUpperPairOfAll p) := by
  intro q r hqr
  rcases q with ⟨⟨x, y⟩, hxy⟩
  rcases r with ⟨⟨u, v⟩, huv⟩
  have hval := congrArg Subtype.val hqr
  have index_eq_of_le_le :
      ∀ {a b : BlockGUE.Index (physicalBlockSizes p)},
        BlockGUE.indexLE (physicalBlockSizes p) a b →
        BlockGUE.indexLE (physicalBlockSizes p) b a → a = b := by
    intro a b hab hba
    apply (Fintype.equivFin (BlockGUE.Index (physicalBlockSizes p))).injective
    apply Fin.ext
    exact Nat.le_antisymm hab hba
  by_cases h₁ : siteLE p (allDiagonalSite x) (allDiagonalSite y)
  · by_cases h₂ : siteLE p (allDiagonalSite u) (allDiagonalSite v)
    · have hp : (allDiagonalSite x, allDiagonalSite y) =
          (allDiagonalSite u, allDiagonalSite v) := by
        simpa [ringUpperPairOfAll, h₁, h₂] using hval
      have hx := allDiagonalSite_injective (Prod.mk.inj hp).1
      have hy := allDiagonalSite_injective (Prod.mk.inj hp).2
      subst u; subst v; rfl
    · have hp : (allDiagonalSite x, allDiagonalSite y) =
          (allDiagonalSite v, allDiagonalSite u) := by
        simpa [ringUpperPairOfAll, h₁, h₂] using hval
      have hxv := allDiagonalSite_injective (Prod.mk.inj hp).1
      have hyu := allDiagonalSite_injective (Prod.mk.inj hp).2
      have hyx : BlockGUE.indexLE (physicalBlockSizes p) y x := by
        simpa [hxv, hyu] using huv
      have hxy' := index_eq_of_le_le hxy hyx
      subst y
      simp_all
  · by_cases h₂ : siteLE p (allDiagonalSite u) (allDiagonalSite v)
    · have hp : (allDiagonalSite y, allDiagonalSite x) =
          (allDiagonalSite u, allDiagonalSite v) := by
        simpa [ringUpperPairOfAll, h₁, h₂] using hval
      have hyu := allDiagonalSite_injective (Prod.mk.inj hp).1
      have hxv := allDiagonalSite_injective (Prod.mk.inj hp).2
      have hyx : BlockGUE.indexLE (physicalBlockSizes p) y x := by
        simpa [hyu, hxv] using huv
      have hxy' := index_eq_of_le_le hxy hyx
      subst y
      simp_all
    · have hp : (allDiagonalSite y, allDiagonalSite x) =
          (allDiagonalSite v, allDiagonalSite u) := by
        simpa [ringUpperPairOfAll, h₁, h₂] using hval
      have hy := allDiagonalSite_injective (Prod.mk.inj hp).1
      have hx := allDiagonalSite_injective (Prod.mk.inj hp).2
      subst u; subst v; rfl

/-- Scalar transformation from an oriented physical upper entry to a simultaneous
normalized block entry.  Cross-block coordinates are deterministically zero. -/
def allDiagonalUpperTransform {p : Params}
    (q : BlockGUE.UpperPair (physicalBlockSizes p)) : ℂ → ℂ :=
  if q.1.1.1 = q.1.2.1 then
    if siteLE p (allDiagonalSite q.1.1) (allDiagonalSite q.1.2) then
      fun z => ((Real.sqrt p.c)⁻¹ : ℂ) * z
    else
      fun z => ((Real.sqrt p.c)⁻¹ : ℂ) * star z
  else fun _ => 0

/-- Every global coordinate transform is measurable, including constant-zero
cross-block transforms. -/
theorem measurable_allDiagonalUpperTransform {p : Params}
    (q : BlockGUE.UpperPair (physicalBlockSizes p)) :
    Measurable (allDiagonalUpperTransform q) := by
  by_cases hb : q.1.1.1 = q.1.2.1
  · by_cases ho : siteLE p (allDiagonalSite q.1.1) (allDiagonalSite q.1.2)
    · simpa [allDiagonalUpperTransform, hb, ho] using
        (continuous_const_mul ((Real.sqrt p.c)⁻¹ : ℂ)).measurable
    · simp only [allDiagonalUpperTransform, hb, ite_true, ho, ite_false]
      change Measurable
        ((fun z : ℂ => ((Real.sqrt p.c)⁻¹ : ℂ) * z) ∘ star)
      exact
        ((continuous_const_mul ((Real.sqrt p.c)⁻¹ : ℂ)).comp
          Complex.continuous_conj).measurable
  · simp [allDiagonalUpperTransform, hb]

/-- Every simultaneous normalized upper entry factors through a distinct physical ring
upper coordinate followed by its measurable scalar transform. -/
theorem Law.normalizedAllDiagonalBlocks_upper_factorization
    {p : Params} (M : Law p)
    (q : BlockGUE.UpperPair (physicalBlockSizes p)) (ω : M.Ω) :
    M.normalizedAllDiagonalBlocks ω q.1.1 q.1.2 =
      allDiagonalUpperTransform q
        (M.H ω (ringUpperPairOfAll q).1.1 (ringUpperPairOfAll q).1.2) := by
  by_cases hb : q.1.1.1 = q.1.2.1
  · by_cases ho : siteLE p (allDiagonalSite q.1.1) (allDiagonalSite q.1.2)
    · simp [Law.normalizedAllDiagonalBlocks, allDiagonalUpperTransform,
        ringUpperPairOfAll, hb, ho]
    · have hH := congrFun
        (congrFun (M.H_hermitian ω) (allDiagonalSite q.1.1))
        (allDiagonalSite q.1.2)
      simp only [Matrix.conjTranspose_apply] at hH
      simp [Law.normalizedAllDiagonalBlocks, allDiagonalUpperTransform,
        ringUpperPairOfAll, hb, ho, hH]
  · simp [Law.normalizedAllDiagonalBlocks, allDiagonalUpperTransform,
      hb]

/-- The entire normalized block-diagonal upper family is mutually independent.

The proof reindexes the physical upper family injectively, then applies a measurable
coordinatewise transform.  Cross-block entries cause no gap: their transform is the
constant-zero function, so they are adjoined as deterministic independent
coordinates. -/
theorem Law.normalizedAllDiagonalBlocks_upper_independent
    {p : Params} (M : Law p) :
    @iIndepFun M.Ω (BlockGUE.UpperPair (physicalBlockSizes p)) M.mΩ
      (fun _ => ℂ) (fun _ => Complex.measurableSpace)
      (fun q ω => M.normalizedAllDiagonalBlocks ω q.1.1 q.1.2) M.P := by
  have hrestrict := iIndepFun.precomp ringUpperPairOfAll_injective M.upper_independent
  have htransport := hrestrict.comp
    (fun q => allDiagonalUpperTransform q)
    measurable_allDiagonalUpperTransform
  simpa only [Function.comp_def,
    M.normalizedAllDiagonalBlocks_upper_factorization] using htransport

/-- The simultaneous normalized physical diagonal blocks form the exact multi-block
GUE law used by PSSS, with no additional independence hypothesis. -/
def Law.normalizedAllDiagonalBlocksGUE
    {p : Params} (M : Law p) :
    BlockGUE.Law (physicalBlockSizes p) (physicalBlockSizes_pos p) where
  Ω := M.Ω
  mΩ := M.mΩ
  P := M.P
  probability := M.probability
  G := M.normalizedAllDiagonalBlocks
  hermitian := M.normalizedAllDiagonalBlocks_isHermitian
  measurable_entry := fun x y =>
    (Matrix.measurable_iff.mp M.measurable_normalizedAllDiagonalBlocks) x y
  block_diagonal := M.normalizedAllDiagonalBlocks_block_diagonal
  upper_independent := M.normalizedAllDiagonalBlocks_upper_independent
  diagonal_im_zero := M.normalizedAllDiagonalBlocks_diagonal_im_zero
  diagonal_re_law := M.normalizedAllDiagonalBlocks_diagonal_re_law
  offdiag_components_independent :=
    M.normalizedAllDiagonalBlocks_offdiag_components_independent
  offdiag_re_law := M.normalizedAllDiagonalBlocks_offdiag_re_law
  offdiag_im_law := M.normalizedAllDiagonalBlocks_offdiag_im_law

end GaussianRing
end CoareaNative.BlockBand
