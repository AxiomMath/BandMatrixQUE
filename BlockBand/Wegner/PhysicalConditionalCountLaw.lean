module

public import Mathlib
public import BlockBand.Wegner.ConditionalCount
public import BlockBand.Internal.Contracts.Inputs

/-!
# The fresh `R`-diagonal blocks of the physical ring as a block-GUE law

Law: the physical ring law `model.law` on `p.SiteMatrix`, every admissible `p`, every
set `R` of blocks (empty allowed). The sites of `R` are reindexed by `siteEquiv p R` as
`Σ j : Fin |R|, Fin W`. The normalized blocks `c^{-1/2} H_jj`, `j ∈ R` (`freshNoise`, a
submatrix of the diagonal matrix of all blocks) form a `BlockGUE.Law`
(`freshLaw`) with blocks of size `W` and the Peled–Schenker–Shamis–Sodin (PSSS) normalization
`GUE_W(1/W)`; every field is derived from the lemmas from which the law of all diagonal blocks
(`model.nativeBlockGUELaw`) is built.
Hence `freshNoise_hasLaw`: its law is exactly `canonicalMatrixMeasure`. No estimate and no
cited input is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Counting
open BlockBand.Internal.Contracts.Inputs (BlockSites withoutFreshBlocks subsystemCount)
open scoped NNReal

namespace PhysicalFresh

variable (p : Parameters) (R : Finset (ZMod p.n))

/-!
## Reindexing the sites of `R`
-/

/-- `|R|` blocks of size `W`. -/
abbrev sizes : Fin R.card → ℕ := fun _ => p.W

theorem sizes_pos : ∀ j, 0 < sizes p R j := fun _ => p.W_pos

/-- The sites of `R` as a block index `Σ j : Fin |R|, Fin W`. -/
def siteEquiv : Index (sizes p R) ≃ BlockSites p R where
  toFun x := ⟨((R.equivFin.symm x.1).1, x.2), (R.equivFin.symm x.1).2⟩
  invFun s := ⟨R.equivFin ⟨s.1.1, s.2⟩, s.1.2⟩
  left_inv x := by
    rcases x with ⟨j, a⟩
    simp
  right_inv s := by
    rcases s with ⟨⟨k, a⟩, hk⟩
    simp

theorem siteEquiv_block_iff (x y : Index (sizes p R)) :
    (siteEquiv p R x).1.1 = (siteEquiv p R y).1.1 ↔ x.1 = y.1 := by
  simp [siteEquiv]

/-- The ambient (all-block) index of an `R`-site. -/
def nativeSite (x : Index (sizes p R)) : p.NativeIndex :=
  p.nativeSiteEquiv.symm (siteEquiv p R x).1

theorem nativeSiteEquiv_nativeSite (x : Index (sizes p R)) :
    p.nativeSiteEquiv (nativeSite p R x) = (siteEquiv p R x).1 :=
  Equiv.apply_symm_apply _ _

theorem nativeSite_injective : Function.Injective (nativeSite p R) :=
  p.nativeSiteEquiv.symm.injective.comp (Subtype.val_injective.comp (siteEquiv p R).injective)

theorem nativeSite_block_iff (x y : Index (sizes p R)) :
    (nativeSite p R x).1 = (nativeSite p R y).1 ↔ x.1 = y.1 := by
  rw [← p.nativeSiteEquiv_block_eq, nativeSiteEquiv_nativeSite, nativeSiteEquiv_nativeSite,
    siteEquiv_block_iff]

/-!
## The normalized fresh blocks as a `BlockGUE.Law`
-/

/-- The normalized `R`-diagonal blocks `c^{-1/2} H_jj`, `j ∈ R`, reindexed. -/
def freshNoise (H : p.SiteMatrix) : Matrix (Index (sizes p R)) (Index (sizes p R)) ℂ :=
  (p.nativeDiagonalMatrix H).submatrix (nativeSite p R) (nativeSite p R)

theorem freshNoise_isHermitian (H : p.SiteMatrix) : (freshNoise p R H).IsHermitian :=
  (p.nativeDiagonalMatrix_isHermitian H).submatrix _

theorem measurable_freshNoise : Measurable (freshNoise p R) := by
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  exact measurable_pi_iff.mp (measurable_pi_iff.mp p.measurable_nativeDiagonalMatrix
    (nativeSite p R x)) (nativeSite p R y)

theorem indexLE_antisymm' {k : ℕ} (d : Fin k → ℕ) (x y : Index d)
    (h1 : indexLE d x y) (h2 : indexLE d y x) : x = y :=
  (Fintype.equivFin (Index d)).injective (Fin.ext (Nat.le_antisymm h1 h2))

theorem indexLE_of_not {k : ℕ} (d : Fin k → ℕ) {x y : Index d} (h : ¬indexLE d x y) :
    indexLE d y x := by
  unfold indexLE at h ⊢
  omega

/-- The ambient upper pair carrying an `R` upper pair (sorted in the ambient order). -/
def nativePair (q : UpperPair (sizes p R)) : p.NativeUpperPair :=
  if h : indexLE p.nativeBlockSizes (nativeSite p R q.1.1) (nativeSite p R q.1.2) then
    ⟨(nativeSite p R q.1.1, nativeSite p R q.1.2), h⟩
  else
    ⟨(nativeSite p R q.1.2, nativeSite p R q.1.1), indexLE_of_not _ h⟩

theorem nativePair_injective : Function.Injective (nativePair p R) := by
  rintro ⟨⟨x, y⟩, hxy⟩ ⟨⟨x', y'⟩, hxy'⟩ he
  have hinj := nativeSite_injective p R
  have h1 := congrArg (fun r : p.NativeUpperPair => r.1.1) he
  have h2 := congrArg (fun r : p.NativeUpperPair => r.1.2) he
  by_cases h : indexLE p.nativeBlockSizes (nativeSite p R x) (nativeSite p R y) <;>
  by_cases h' : indexLE p.nativeBlockSizes (nativeSite p R x') (nativeSite p R y') <;>
  simp only [nativePair, h, h', ↓reduceDIte] at h1 h2
  · have e1 := hinj h1
    have e2 := hinj h2
    subst e1 e2
    rfl
  · have e1 := hinj h1
    have e2 := hinj h2
    subst e1 e2
    have e : x = y := indexLE_antisymm' (sizes p R) x y hxy hxy'
    subst e
    rfl
  · have e1 := hinj h1
    have e2 := hinj h2
    subst e1 e2
    have e : x = y := indexLE_antisymm' (sizes p R) x y hxy hxy'
    subst e
    rfl
  · have e1 := hinj h1
    have e2 := hinj h2
    subst e1 e2
    rfl

/-- Identity or conjugation, according to the ambient orientation of an upper pair. -/
def pairFlip (q : UpperPair (sizes p R)) : ℂ → ℂ :=
  if indexLE p.nativeBlockSizes (nativeSite p R q.1.1) (nativeSite p R q.1.2) then id else star

theorem measurable_pairFlip (q : UpperPair (sizes p R)) : Measurable (pairFlip p R q) := by
  unfold pairFlip
  split_ifs
  · exact measurable_id
  · exact continuous_star.measurable

theorem freshNoise_upper (H : p.SiteMatrix) (q : UpperPair (sizes p R)) :
    freshNoise p R H q.1.1 q.1.2 =
      pairFlip p R q (p.nativeDiagonalMatrix H (nativePair p R q).1.1 (nativePair p R q).1.2) := by
  by_cases h : indexLE p.nativeBlockSizes (nativeSite p R q.1.1) (nativeSite p R q.1.2)
  · simp only [pairFlip, nativePair, h, ↓reduceIte, ↓reduceDIte]
    rfl
  · simp only [pairFlip, nativePair, h, ↓reduceIte, ↓reduceDIte]
    exact ((p.nativeDiagonalMatrix_isHermitian H).apply _ _).symm

theorem entryVariance_eq (x y : Index (sizes p R)) :
    entryVariance (sizes p R) x y =
      entryVariance p.nativeBlockSizes (nativeSite p R x) (nativeSite p R y) := by
  unfold entryVariance
  simp only [nativeSite_block_iff]

theorem entryVariance_symm_native (x y : p.NativeIndex) :
    entryVariance p.nativeBlockSizes x y = entryVariance p.nativeBlockSizes y x := by
  unfold entryVariance
  by_cases h : x.1 = y.1
  · simp [h]
  · simp [h, Ne.symm h]

local instance gaussianReal_isProbability' (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) :=
  ProbabilityTheory.instIsProbabilityMeasureGaussianReal μ v

theorem hasLaw_gaussian_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {v w : ℝ≥0} (h : HasLaw X (gaussianReal 0 v) P) (hvw : (v : ℝ) = w) :
    HasLaw X (gaussianReal 0 w) P := by
  have : v = w := NNReal.eq hvw
  subst this
  exact h

variable {p} in
/-- The normalized `R`-diagonal blocks under the physical law, with every
`BlockGUE.Law` field proved from the law of all diagonal blocks (`model.nativeBlockGUELaw`). -/
def freshLaw (model : p.GaussianRingModel) (R : Finset (ZMod p.n)) :
    Law.{0} (sizes p R) (sizes_pos p R) where
  Ω := p.SiteMatrix
  mΩ := inferInstance
  P := (model.law : Measure p.SiteMatrix)
  probability := inferInstance
  G := freshNoise p R
  hermitian := freshNoise_isHermitian p R
  measurable_entry := fun x y =>
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp (measurable_freshNoise p R))
  block_diagonal := by
    intro x y hxy
    filter_upwards with H
    have hn : (nativeSite p R x).1 ≠ (nativeSite p R y).1 :=
      fun h => hxy ((nativeSite_block_iff p R x y).mp h)
    simp only [freshNoise, Matrix.submatrix_apply, Parameters.nativeDiagonalMatrix, hn, ite_false]
  upper_independent := by
    have h := (model.iIndepFun_nativeDiagonal_upper.precomp (nativePair_injective p R)).comp
      (fun q => pairFlip p R q) (fun q => measurable_pairFlip p R q)
    convert h using 1
    funext q H
    exact freshNoise_upper p R H q
  diagonal_im_zero := fun x => Filter.Eventually.of_forall
    (fun H => p.nativeDiagonalMatrix_diagonal_im_zero H (nativeSite p R x))
  diagonal_re_law := fun x =>
    hasLaw_gaussian_congr (model.nativeDiagonal_re_hasLaw (nativeSite p R x))
      (entryVariance_eq p R x x).symm
  offdiag_components_independent := by
    intro x y hxy hne hb
    have nb : (nativeSite p R x).1 = (nativeSite p R y).1 := (nativeSite_block_iff p R x y).mpr hb
    have nne : nativeSite p R x ≠ nativeSite p R y := fun h => hne (nativeSite_injective p R h)
    by_cases hle : indexLE p.nativeBlockSizes (nativeSite p R x) (nativeSite p R y)
    · exact model.nativeOffdiag_components_independent ⟨(nativeSite p R x, nativeSite p R y), hle⟩ nb nne
    · have hle' : indexLE p.nativeBlockSizes (nativeSite p R y) (nativeSite p R x) := by
        exact indexLE_of_not _ hle
      have h := (model.nativeOffdiag_components_independent ⟨(nativeSite p R y, nativeSite p R x), hle'⟩ nb.symm
        (Ne.symm nne)).comp measurable_id measurable_neg
      apply h.congr
      · filter_upwards with H
        change (p.nativeDiagonalMatrix H (nativeSite p R y) (nativeSite p R x)).re =
          (p.nativeDiagonalMatrix H (nativeSite p R x) (nativeSite p R y)).re
        rw [← (p.nativeDiagonalMatrix_isHermitian H).apply (nativeSite p R x)]
        simp
      · filter_upwards with H
        change -(p.nativeDiagonalMatrix H (nativeSite p R y) (nativeSite p R x)).im =
          (p.nativeDiagonalMatrix H (nativeSite p R x) (nativeSite p R y)).im
        rw [← (p.nativeDiagonalMatrix_isHermitian H).apply (nativeSite p R x)]
        simp
  offdiag_re_law := by
    intro x y hxy hne hb
    have nb : (nativeSite p R x).1 = (nativeSite p R y).1 := (nativeSite_block_iff p R x y).mpr hb
    have nne : nativeSite p R x ≠ nativeSite p R y := fun h => hne (nativeSite_injective p R h)
    by_cases hle : indexLE p.nativeBlockSizes (nativeSite p R x) (nativeSite p R y)
    · refine hasLaw_gaussian_congr (model.nativeOffdiag_re_hasLaw ⟨(nativeSite p R x, nativeSite p R y), hle⟩ nb nne) ?_
      exact congrArg (fun t => t / 2) (entryVariance_eq p R x y).symm
    · have hle' : indexLE p.nativeBlockSizes (nativeSite p R y) (nativeSite p R x) := by
        exact indexLE_of_not _ hle
      have h := hasLaw_gaussian_congr (w := ⟨entryVariance (sizes p R) x y / 2,
          div_nonneg (entryVariance_nonneg (sizes_pos p R) x y) (by norm_num)⟩)
        (model.nativeOffdiag_re_hasLaw ⟨(nativeSite p R y, nativeSite p R x), hle'⟩ nb.symm (Ne.symm nne)) (by
          change entryVariance _ _ _ / 2 = entryVariance _ _ _ / 2
          rw [entryVariance_eq p R x y, entryVariance_symm_native])
      apply h.congr
      filter_upwards with H
      change (p.nativeDiagonalMatrix H (nativeSite p R x) (nativeSite p R y)).re =
        (p.nativeDiagonalMatrix H (nativeSite p R y) (nativeSite p R x)).re
      rw [← (p.nativeDiagonalMatrix_isHermitian H).apply (nativeSite p R x)]
      simp
  offdiag_im_law := by
    intro x y hxy hne hb
    have nb : (nativeSite p R x).1 = (nativeSite p R y).1 := (nativeSite_block_iff p R x y).mpr hb
    have nne : nativeSite p R x ≠ nativeSite p R y := fun h => hne (nativeSite_injective p R h)
    by_cases hle : indexLE p.nativeBlockSizes (nativeSite p R x) (nativeSite p R y)
    · refine hasLaw_gaussian_congr (model.nativeOffdiag_im_hasLaw ⟨(nativeSite p R x, nativeSite p R y), hle⟩ nb nne) ?_
      exact congrArg (fun t => t / 2) (entryVariance_eq p R x y).symm
    · have hle' : indexLE p.nativeBlockSizes (nativeSite p R y) (nativeSite p R x) := by
        exact indexLE_of_not _ hle
      have h0 := gaussianReal_const_mul
        (model.nativeOffdiag_im_hasLaw ⟨(nativeSite p R y, nativeSite p R x), hle'⟩ nb.symm (Ne.symm nne)) (-1)
      have hs : NNReal.mk ((-1 : ℝ) ^ 2) (sq_nonneg _) = 1 := by
        apply NNReal.coe_injective
        norm_num
      rw [mul_zero, hs] at h0
      have h := hasLaw_gaussian_congr (w := ⟨entryVariance (sizes p R) x y / 2,
          div_nonneg (entryVariance_nonneg (sizes_pos p R) x y) (by norm_num)⟩) h0 (by
          change 1 * (entryVariance _ _ _ / 2) = entryVariance _ _ _ / 2
          rw [one_mul, entryVariance_eq p R x y, entryVariance_symm_native])
      apply h.congr
      filter_upwards with H
      change (p.nativeDiagonalMatrix H (nativeSite p R x) (nativeSite p R y)).im =
        -1 * (p.nativeDiagonalMatrix H (nativeSite p R y) (nativeSite p R x)).im
      rw [← (p.nativeDiagonalMatrix_isHermitian H).apply (nativeSite p R x)]
      simp

/-- The normalized fresh blocks have exactly the canonical PSSS block-GUE law. -/
theorem freshNoise_hasLaw (model : p.GaussianRingModel) :
    HasLaw (fun H => freshNoise p R H)
      ((canonicalMatrixMeasure (sizes p R) (sizes_pos p R)).map Subtype.val)
      (model.law : Measure p.SiteMatrix) :=
  (hasLaw_map measurable_subtype_coe.aemeasurable).fun_comp
    (freshLaw model R).hasLaw_matrix_canonical

end PhysicalFresh

end BlockBand.Wegner
