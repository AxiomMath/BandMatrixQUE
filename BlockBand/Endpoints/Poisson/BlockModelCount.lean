module

public import BlockBand.Internal.Contracts.Inputs

/-!
# First factorial moment of the eigenvalue count of block models

Law: `H = D + ⊕_j A_j` on the sites `Fin k × Fin W`, with independent blocks
`A_j ~ gueMatrixLaw W (c/W)` (Johansson coordinate law, total entry variance `c/W`) and
`(D, Y)` independent of the block family (`BlockModel.IsIndependent c`). Conclusion: for
every closed `[a, b]` the number of eigenvalues of `H` in `[a, b]` (with multiplicity) is
integrable and `E #{i | λ_i(H) ∈ [a,b]} ≤ C/√c · kW · (b - a)`, with the absolute constant
`C` of the hypothesis `ConditionalBlockGUECount`, uniformly in `k`, `W ≥ 1`, `c > 0`, the model
and `a ≤ b`.

Normalization (proved here): with `t = c`, `c^{-1/2} ⊕_j A_j`
reindexed along `Fin k × Fin W ≃ Σ _ : Fin k, Fin W` has exactly the canonical PSSS law
`canonicalMatrixMeasure (fun _ => W)`: Johansson's diagonal variance `c/W` and strict-upper
real/imaginary variances `c/(2W)` become `1/W` and `1/(2W)`, which are PSSS's
`entryVariance = 1/d_j` and `1/(2 d_j)` with `d_j = W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints.BlockModelCount

open MeasureTheory ProbabilityTheory
open BlockBand.External BlockBand.External.PSSS BlockBand.External.PSSS.BlockGUE
open BlockBand.Foundations.Spectral
open scoped NNReal

attribute [local instance] BlockBand.External.PSSS.BlockGUE.upperPairFintype

/-!
### Deterministic spectral and Hermitian helpers
-/

section Spectral

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

open Classical in

/-- The count is the number of real parts of characteristic roots in `I`. -/
theorem eigenCount_eq_roots_card (A : PSSS.HermitianMatrix ι) (I : Set ℝ) :
    eigenCount A I = ((A.1.charpoly.roots.map Complex.re).filter (fun x => x ∈ I)).card := by
  have hr : A.1.charpoly.roots.map Complex.re =
      Multiset.map (fun i => increasingEigenvalue A.2 i) Finset.univ.val := by
    rw [A.2.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def]
    change Multiset.map A.2.eigenvalues₀ Finset.univ.val =
      Multiset.map (A.2.eigenvalues₀ ∘ Fin.revPerm) Finset.univ.val
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [hr, Multiset.filter_map, Multiset.card_map]
  rfl

/-- Equal characteristic polynomials give equal counts, across index types. -/
theorem eigenCount_eq_of_charpoly_eq (A : PSSS.HermitianMatrix ι) (B : PSSS.HermitianMatrix κ)
    (h : A.1.charpoly = B.1.charpoly) (I : Set ℝ) : eigenCount A I = eigenCount B I := by
  rw [eigenCount_eq_roots_card, eigenCount_eq_roots_card, h]

/-- The Hermitian part `(A + Aᴴ)/2`, a total measurable map into Hermitian matrices. -/
def toHerm (A : Matrix ι ι ℂ) : PSSS.HermitianMatrix ι :=
  ⟨(2⁻¹ : ℂ) • (A + A.conjTranspose),
    (Matrix.isHermitian_add_transpose_self A).smul (by simp [IsSelfAdjoint])⟩

/-- On Hermitian matrices `toHerm` is the identity. -/
theorem toHerm_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (toHerm A).1 = A := by
  change (2⁻¹ : ℂ) • (A + A.conjTranspose) = A
  rw [hA.eq, ← two_smul ℂ A, smul_smul]
  norm_num

/-- `toHerm` is Borel measurable. -/
theorem measurable_toHerm : Measurable (toHerm (ι := ι)) := by
  apply Measurable.subtype_mk
  exact ((continuous_const (y := (2⁻¹ : ℂ))).smul ((continuous_id (X := Matrix ι ι ℂ)).add
    (continuous_id (X := Matrix ι ι ℂ)).matrix_conjTranspose)).measurable

end Spectral

/-!
### Block-diagonal matrices on the PSSS index
-/

section Blocks

variable {k W : ℕ}

/-- Constant block sizes `d_j = W`. -/
abbrev bsz (k W : ℕ) : Fin k → ℕ := fun _ => W

/-- The PSSS site type `Σ _ : Fin k, Fin W`. -/
abbrev BIdx (k W : ℕ) := Index (bsz k W)

/-- The site reindexing `Fin k × Fin W ≃ Σ _ : Fin k, Fin W`. -/
def siteEquiv (k W : ℕ) : Fin k × Fin W ≃ BIdx k W :=
  (Equiv.sigmaEquivProd (Fin k) (Fin W)).symm

/-- The block-diagonal matrix `⊕_j A_j` on the PSSS index. -/
def blockMatrix (A : Fin k → Matrix (Fin W) (Fin W) ℂ) : Matrix (BIdx k W) (BIdx k W) ℂ :=
  fun x y => if x.1 = y.1 then A x.1 x.2 y.2 else 0

/-- Hermitian blocks give a Hermitian block-diagonal matrix. -/
theorem blockMatrix_isHermitian {A : Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) : (blockMatrix A).IsHermitian := by
  ext x y
  obtain ⟨j, a⟩ := x
  obtain ⟨j', b⟩ := y
  simp only [Matrix.conjTranspose_apply, blockMatrix]
  by_cases hj : j = j'
  · subst hj
    simp only [ite_true]
    exact (hA j).apply a b
  · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj, star_zero]

/-- The block-diagonal assembly is measurable. -/
theorem measurable_blockMatrix : Measurable (blockMatrix (k := k) (W := W)) := by
  rw [Matrix.measurable_iff]
  intro x y
  by_cases hj : x.1 = y.1
  · simp only [blockMatrix, hj, ite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [blockMatrix, hj, ite_false]
    exact measurable_const

/-- Reindexing along `siteEquiv` is measurable. -/
theorem measurable_reindex :
    Measurable (fun A : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      Matrix.reindex (siteEquiv k W) (siteEquiv k W) A) := by
  rw [Matrix.measurable_iff]
  intro x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (measurable_pi_apply _).comp (measurable_pi_apply _)

/-- The Hamiltonian of a block model is Hermitian. -/
theorem isHermitian_H (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) : (M.H w).IsHermitian := by
  refine (M.hermitian_D w).add ?_
  ext x y
  simp only [Matrix.conjTranspose_apply, BlockBand.Internal.Contracts.Inputs.BlockModel.blockSum]
  by_cases hj : x.1 = y.1
  · rw [ite_eq_left hj.symm, ite_eq_left hj]
    obtain ⟨j, a⟩ := x
    obtain ⟨j', b⟩ := y
    simp only at hj
    subst hj
    exact (M.hermitian_A w j).apply a b
  · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj, star_zero]

/-- Reindexing `H = D + ⊕_j A_j` gives `D' + blockMatrix A`. -/
theorem reindex_H (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) :
    Matrix.reindex (siteEquiv k W) (siteEquiv k W) (M.H w) =
      Matrix.reindex (siteEquiv k W) (siteEquiv k W) (M.D w) + blockMatrix (M.A w) := by
  ext x y
  rfl

end Blocks

/-!
### Upper coordinates: Johansson blocks versus the PSSS product
-/

section Coordinates

variable {k W : ℕ}

/-- The PSSS upper order is total. -/
theorem indexLE_total {k : ℕ} (d : Fin k → ℕ) (x y : Index d) :
    indexLE d x y ∨ indexLE d y x :=
  le_total _ _

/-- The PSSS upper order is antisymmetric. -/
theorem indexLE_antisymm {k : ℕ} (d : Fin k → ℕ) {x y : Index d}
    (h₁ : indexLE d x y) (h₂ : indexLE d y x) : x = y :=
  (Fintype.equivFin (Index d)).injective (Fin.ext (le_antisymm h₁ h₂))

/-- The Johansson upper position `(min a b, max a b)` of a PSSS upper pair. -/
def upos (q : UpperPair (bsz k W)) : Johansson.UpperPair W :=
  if h : (q.1.1.2 : Fin W) ≤ q.1.2.2 then ⟨(q.1.1.2, q.1.2.2), h⟩
  else ⟨(q.1.2.2, q.1.1.2), le_of_not_ge h⟩

/-- Scale by `s`, conjugating when the PSSS order flips the Johansson order. -/
def coordMap (s : ℝ) (q : UpperPair (bsz k W)) (w : ℝ × ℝ) : ℝ × ℝ :=
  (s * w.1, (if (q.1.1.2 : Fin W) ≤ q.1.2.2 then s else -s) * w.2)

/-- `coordMap` is measurable. -/
theorem measurable_coordMap (s : ℝ) (q : UpperPair (bsz k W)) :
    Measurable (coordMap s q) := by
  unfold coordMap
  fun_prop

/-- The PSSS upper coordinates of `s • ⊕_j G(z_j)`. -/
def psi (s : ℝ) (z : Fin k → Johansson.UpperPair W → ℝ × ℝ) (q : UpperPair (bsz k W)) :
    ℝ × ℝ :=
  if q.1.1.1 = q.1.2.1 then coordMap s q (z q.1.1.1 (upos q)) else (0, 0)

/-- `psi s` is measurable. -/
theorem measurable_psi (s : ℝ) : Measurable (psi (k := k) (W := W) s) := by
  rw [measurable_pi_iff]
  intro q
  by_cases hq : q.1.1.1 = q.1.2.1
  · simp only [psi, hq, ite_true]
    exact (measurable_coordMap s q).comp
      ((measurable_pi_apply _).comp (measurable_pi_apply _))
  · simp only [psi, hq, ite_false]
    exact measurable_const

/-- Same-block PSSS upper pairs are in bijection with block labels and Johansson upper
positions. -/
def sameEquiv (k W : ℕ) :
    {q : UpperPair (bsz k W) // q.1.1.1 = q.1.2.1} ≃ Fin k × Johansson.UpperPair W where
  toFun q := (q.1.1.1.1, upos q.1)
  invFun r :=
    if h : indexLE (bsz k W) ⟨r.1, r.2.1.1⟩ ⟨r.1, r.2.1.2⟩ then
      ⟨⟨(⟨r.1, r.2.1.1⟩, ⟨r.1, r.2.1.2⟩), h⟩, rfl⟩
    else
      ⟨⟨(⟨r.1, r.2.1.2⟩, ⟨r.1, r.2.1.1⟩),
        (indexLE_total _ _ _).resolve_left h⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨⟨j, a⟩, ⟨j', b⟩⟩, h⟩, hs⟩
    simp only at hs
    subst hs
    by_cases hab : a ≤ b
    · have hu : upos (⟨(⟨j, a⟩, ⟨j, b⟩), h⟩ : UpperPair (bsz k W)) =
          ⟨(a, b), hab⟩ := by
        simp [upos, hab]
      simp only [hu]
      rw [dite_eq_left h]
    · have hu : upos (⟨(⟨j, a⟩, ⟨j, b⟩), h⟩ : UpperPair (bsz k W)) =
          ⟨(b, a), le_of_not_ge hab⟩ := by
        simp [upos, hab]
      have hn : ¬ indexLE (bsz k W) ⟨j, b⟩ ⟨j, a⟩ := by
        intro h'
        have := indexLE_antisymm (bsz k W) h h'
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
        exact hab (le_of_eq this)
      simp only [hu]
      rw [dite_eq_right hn]
  right_inv := by
    rintro ⟨j, ⟨⟨a, b⟩, hab⟩⟩
    by_cases h : indexLE (bsz k W) ⟨j, a⟩ ⟨j, b⟩
    · simp only
      rw [dite_eq_left h]
      simp [upos, hab]
    · simp only
      rw [dite_eq_right h]
      have hne : a ≠ b := by
        rintro rfl
        exact h (le_refl _)
      have hba : ¬ b ≤ a := fun hba => hne (le_antisymm hab hba)
      simp [upos, hba]

/-- The inverse of `sameEquiv` keeps the block label. -/
theorem sameEquiv_symm_block (r : Fin k × Johansson.UpperPair W) :
    ((sameEquiv k W).symm r).1.1.1.1 = r.1 :=
  congrArg Prod.fst ((sameEquiv k W).apply_symm_apply r)

/-- The inverse of `sameEquiv` keeps the Johansson position. -/
theorem sameEquiv_symm_upos (r : Fin k × Johansson.UpperPair W) :
    upos ((sameEquiv k W).symm r).1 = r.2 :=
  congrArg Prod.snd ((sameEquiv k W).apply_symm_apply r)

end Coordinates

/-!
### Exact Gaussian normalization
-/

section Normalization

variable {k W : ℕ}

/-- Scaling a centred real Gaussian of variance `v` by `c` gives variance `c² v`. -/
theorem gaussianReal_map_mul_eq (c : ℝ) (v v' : ℝ≥0) (h : c ^ 2 * (v : ℝ) = v') :
    (gaussianReal 0 v).map (fun x => c * x) = gaussianReal 0 v' := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp [h]

/-- Scaling the diagonal Johansson coordinate law. -/
theorem map_diag_gaussian (s : ℝ) (f : ℝ × ℝ → ℝ × ℝ) (hf : Measurable f)
    (hfx : ∀ x : ℝ, f (x, 0) = (s * x, 0)) (v v' : ℝ≥0) (h : s ^ 2 * (v : ℝ) = v') :
    (Measure.map (fun x : ℝ => (x, (0 : ℝ))) (gaussianReal 0 v)).map f =
      Measure.map (fun x : ℝ => (x, (0 : ℝ))) (gaussianReal 0 v') := by
  rw [Measure.map_map hf (by fun_prop)]
  have hcomp : f ∘ (fun x : ℝ => (x, (0 : ℝ))) =
      (fun x : ℝ => (x, (0 : ℝ))) ∘ (fun x => s * x) := by
    funext x
    simp [hfx]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_mul_eq s v v' h]

/-- Scaling (and possibly conjugating) an off-diagonal Johansson coordinate law. -/
theorem map_offdiag_gaussian (s t : ℝ) (f : ℝ × ℝ → ℝ × ℝ)
    (hf : f = Prod.map (fun x => s * x) (fun x => t * x)) (hts : t ^ 2 = s ^ 2)
    (v v' : ℝ≥0) (h : s ^ 2 * (v : ℝ) = v') :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map f =
      (gaussianReal 0 v').prod (gaussianReal 0 v') := by
  rw [hf, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_mul_eq s v v' h, gaussianReal_map_mul_eq t v v' (by rw [hts, h])]

/-- One Johansson coordinate law, scaled by `s` with `s² S = 1/W`, is the canonical PSSS
upper-pair law of the matching same-block pair. -/
theorem map_coordMap (hW : 0 < W) (s : ℝ) (S : ℝ≥0) (hsS : s ^ 2 * (S : ℝ) = 1 / W)
    (q : UpperPair (bsz k W)) (hq : q.1.1.1 = q.1.2.1) :
    (Johansson.upperEntryMeasure S (upos q)).map (coordMap s q) =
      canonicalUpperPairMeasure (bsz k W) (fun _ => hW) q := by
  have hvar : entryVariance (bsz k W) q.1.1 q.1.2 = 1 / W := by
    simp [entryVariance, hq]
  by_cases hxy : q.1.1 = q.1.2
  · have hle : (q.1.1.2 : Fin W) ≤ q.1.2.2 := by
      rw [Sigma.ext_iff] at hxy
      exact le_of_eq (eq_of_heq hxy.2)
    have hu : (upos q).1.1 = (upos q).1.2 := by
      have h2 := hxy
      rw [Sigma.ext_iff] at h2
      simp only [upos, hle, dite_true]
      exact eq_of_heq h2.2
    have hvar' : entryVariance (bsz k W) q.1.1 q.1.1 = 1 / W := by
      simpa [hxy] using hvar
    simp only [Johansson.upperEntryMeasure, hu, ite_true, canonicalUpperPairMeasure, hxy,
      dite_true]
    refine map_diag_gaussian s _ (measurable_coordMap s q) ?_ _ _ ?_
    · intro x
      simp [coordMap]
    · change s ^ 2 * (S : ℝ) = entryVariance (bsz k W) q.1.2 q.1.2
      rw [← hxy, hvar', hsS]
  · have hab : (q.1.1.2 : Fin W) ≠ q.1.2.2 := by
      intro hab
      apply hxy
      exact Sigma.ext hq (heq_of_eq hab)
    have hu : (upos q).1.1 ≠ (upos q).1.2 := by
      unfold upos
      split_ifs
      · exact hab
      · exact Ne.symm hab
    simp only [Johansson.upperEntryMeasure, hu, ite_false, canonicalUpperPairMeasure, hxy, hq,
      dite_false, dite_true]
    refine map_offdiag_gaussian s (if (q.1.1.2 : Fin W) ≤ q.1.2.2 then s else -s) _ ?_ ?_ _ _ ?_
    · funext w
      rfl
    · split_ifs <;> ring
    · change s ^ 2 * ((S : ℝ) / 2) = entryVariance (bsz k W) q.1.1 q.1.2 / 2
      rw [hvar, ← hsS]
      ring

/-- The PSSS upper coordinates of the scaled Johansson block product have exactly the
canonical PSSS product law. -/
theorem map_psi (hW : 0 < W) (s : ℝ) (S : ℝ≥0) (hsS : s ^ 2 * (S : ℝ) = 1 / W) :
    (Measure.pi fun _ : Fin k => Johansson.coordinateMeasure W S).map (psi s) =
      canonicalUpperCoordinateMeasure (bsz k W) (fun _ => hW) := by
  have hJ : ∀ p : Johansson.UpperPair W, IsProbabilityMeasure (Johansson.upperEntryMeasure S p) :=
    Johansson.upperEntryMeasure_probability S
  have hC : ∀ q : UpperPair (bsz k W),
      IsProbabilityMeasure (canonicalUpperPairMeasure (bsz k W) (fun _ => hW) q) :=
    canonicalUpperPairMeasure_probability _ _
  have hJ' : IsProbabilityMeasure (Johansson.coordinateMeasure W S) :=
    Johansson.coordinateMeasure_probability W S
  unfold canonicalUpperCoordinateMeasure
  symm
  refine Measure.pi_eq ?_
  intro t ht
  rw [Measure.map_apply (measurable_psi s) (MeasurableSet.univ_pi ht)]
  let e := sameEquiv k W
  by_cases hc : ∀ q : UpperPair (bsz k W), ¬ q.1.1.1 = q.1.2.1 → ((0 : ℝ), (0 : ℝ)) ∈ t q
  · have hset : psi s ⁻¹' Set.univ.pi t =
        Set.univ.pi (fun j : Fin k => Set.univ.pi (fun p : Johansson.UpperPair W =>
          coordMap s (e.symm (j, p)).1 ⁻¹' t (e.symm (j, p)).1)) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hz j p
        have h1 := hz (e.symm (j, p)).1
        rw [psi, ite_eq_left (e.symm (j, p)).2, sameEquiv_symm_block, sameEquiv_symm_upos] at h1
        exact h1
      · intro hz q
        by_cases hq : q.1.1.1 = q.1.2.1
        · have h1 := hz (e ⟨q, hq⟩).1 (e ⟨q, hq⟩).2
          rw [Prod.mk.eta, Equiv.symm_apply_apply] at h1
          rw [psi, ite_eq_left hq]
          exact h1
        · rw [psi, ite_eq_right hq]
          exact hc q hq
    rw [hset, Measure.pi_pi]
    simp only [Johansson.coordinateMeasure, Measure.pi_pi]
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun q : UpperPair (bsz k W) => q.1.1.1 = q.1.2.1)]
    have hcross : ∀ q : {q : UpperPair (bsz k W) // ¬ q.1.1.1 = q.1.2.1},
        canonicalUpperPairMeasure (bsz k W) (fun _ => hW) q.1 (t q.1) = 1 := by
      intro q
      have hxy : q.1.1.1 ≠ q.1.1.2 := fun h => q.2 (congrArg Sigma.fst h)
      simp only [canonicalUpperPairMeasure, hxy, q.2, dite_false]
      exact Measure.dirac_apply_of_mem (hc q.1 q.2)
    rw [Finset.prod_eq_one (fun q _ => hcross q), mul_one]
    rw [Fintype.prod_equiv e
      (fun q => canonicalUpperPairMeasure (bsz k W) (fun _ => hW) q.1 (t q.1))
      (fun r => canonicalUpperPairMeasure (bsz k W) (fun _ => hW) (e.symm r).1 (t (e.symm r).1))
      (fun q => by rw [Equiv.symm_apply_apply])]
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl (fun j _ => Finset.prod_congr rfl (fun p _ => ?_))
    rw [← map_coordMap hW s S hsS (e.symm (j, p)).1 (e.symm (j, p)).2,
      Measure.map_apply (measurable_coordMap s _) (ht _), sameEquiv_symm_upos]
  · push Not at hc
    obtain ⟨q, hq, h0⟩ := hc
    have hset : psi s ⁻¹' Set.univ.pi t = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_empty_iff_false, iff_false,
        not_forall]
      refine ⟨q, ?_⟩
      rw [psi, ite_eq_right hq]
      exact h0
    rw [hset, measure_empty]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    have hxy : q.1.1 ≠ q.1.2 := fun h => hq (congrArg Sigma.fst h)
    simp only [canonicalUpperPairMeasure, hxy, hq, dite_false]
    simp [Measure.dirac_apply' _ (ht q), h0]

end Normalization

/-!
### The scaled block matrix is the PSSS reconstruction of `psi`
-/

section Reconstruction

variable {k W : ℕ}

/-- At an upper pair the reconstructed entry depends only on that coordinate. -/
theorem matrixOfUpperCoordinatesRaw_upper {k : ℕ} (d : Fin k → ℕ)
    (z : UpperPair d → UpperRealPair) (q : UpperPair d) :
    matrixOfUpperCoordinatesRaw d z q.1.1 q.1.2 =
      if q.1.1 = q.1.2 then ((z q).1 : ℂ) else complexOfUpperRealPair (z q) := by
  rcases q with ⟨⟨x, y⟩, hxy⟩
  by_cases h : x = y
  · subst h
    simp [matrixOfUpperCoordinatesRaw]
  · simp [matrixOfUpperCoordinatesRaw, h, hxy]

/-- Hermitian matrices agreeing on all PSSS upper pairs are equal. -/
theorem eq_of_upper {k : ℕ} {d : Fin k → ℕ} {A B : Matrix (Index d) (Index d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ x y, indexLE d x y → A x y = B x y) : A = B := by
  ext x y
  by_cases hxy : indexLE d x y
  · exact h x y hxy
  · have hyx : indexLE d y x := (indexLE_total d x y).resolve_left hxy
    rw [← hA.apply x y, ← hB.apply x y, h y x hyx]

/-- Pointwise: `s • ⊕_j G(z_j)` is the PSSS reconstruction of the coordinates `psi s z`. -/
theorem blockMatrix_gaussian_eq (s : ℝ) (z : Fin k → Johansson.UpperPair W → ℝ × ℝ) :
    (s : ℂ) • blockMatrix (fun j => Johansson.gaussianMatrixRaw (z j)) =
      matrixOfUpperCoordinatesRaw (bsz k W) (psi s z) := by
  refine eq_of_upper ((blockMatrix_isHermitian
      (fun j => Johansson.gaussianMatrixRaw_isHermitian (z j))).smul (by simp [IsSelfAdjoint]))
    (matrixOfUpperCoordinatesRaw_isHermitian _ _) ?_
  intro x y hxy
  have hup := matrixOfUpperCoordinatesRaw_upper (bsz k W) (psi s z) ⟨(x, y), hxy⟩
  simp only at hup
  rw [hup]
  obtain ⟨j, a⟩ := x
  obtain ⟨j', b⟩ := y
  by_cases hj : j = j'
  · subst hj
    by_cases hab : a = b
    · subst hab
      simp [blockMatrix, psi, upos, coordMap, Johansson.gaussianMatrixRaw]
    · have hne : (⟨j, a⟩ : BIdx k W) ≠ ⟨j, b⟩ := by
        intro he
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at he
        exact hab he
      rw [ite_eq_right hne]
      by_cases hle : (a : Fin W) ≤ b
      · simp [blockMatrix, psi, upos, coordMap, Johansson.gaussianMatrixRaw, hab, hle,
          complexOfUpperRealPair, Johansson.complexPair]
        ring
      · simp [blockMatrix, psi, upos, coordMap, Johansson.gaussianMatrixRaw, hab, hle,
          complexOfUpperRealPair, Johansson.complexPair]
        apply Complex.ext <;> simp
  · have hne : (⟨j, a⟩ : BIdx k W) ≠ ⟨j', b⟩ := fun he => hj (congrArg Sigma.fst he)
    rw [ite_eq_right hne]
    simp [blockMatrix, psi, hj, complexOfUpperRealPair]

end Reconstruction

/-!
### The block model as PSSS input
-/

section Model

variable {k W : ℕ}

/-- The block noise `⊕_j A_j` on the PSSS index, as a Hermitian matrix. -/
def Gm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) : PSSS.HermitianMatrix (BIdx k W) :=
  toHerm (blockMatrix (M.A w))

/-- The reindexed deformation `D`, as a Hermitian matrix. -/
def Dm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) : PSSS.HermitianMatrix (BIdx k W) :=
  toHerm (Matrix.reindex (siteEquiv k W) (siteEquiv k W) (M.D w))

/-- The underlying matrix of `Gm` is `⊕_j A_j`. -/
theorem Gm_val (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) : (Gm M w).1 = blockMatrix (M.A w) :=
  toHerm_of_isHermitian (blockMatrix_isHermitian (M.hermitian_A w))

/-- The underlying matrix of `Dm` is the reindexed `D`. -/
theorem Dm_val (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω) :
    (Dm M w).1 = Matrix.reindex (siteEquiv k W) (siteEquiv k W) (M.D w) :=
  toHerm_of_isHermitian ((M.hermitian_D w).submatrix _)

/-- `Gm` is measurable. -/
theorem measurable_Gm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) : Measurable (Gm M) :=
  measurable_toHerm.comp (measurable_blockMatrix.comp M.measurable_A)

/-- `Dm` is measurable. -/
theorem measurable_Dm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) : Measurable (Dm M) :=
  measurable_toHerm.comp (measurable_reindex.comp M.measurable_D)

/-- `D` (with `Y`) independent of the block family gives `D'` independent of `⊕_j A_j`. -/
theorem indepFun_Dm_Gm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (c : ℝ) (hM : M.IsIndependent c) :
    IndepFun (Dm M) (Gm M) M.P :=
  hM.2.2.comp
    (φ := fun p : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ ×
        Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ =>
      toHerm (Matrix.reindex (siteEquiv k W) (siteEquiv k W) p.1))
    (ψ := fun a => toHerm (blockMatrix a))
    (measurable_toHerm.comp (measurable_reindex.comp measurable_fst))
    (measurable_toHerm.comp measurable_blockMatrix)

/-- The law of the block family: the product of the Johansson coordinate laws, pushed
through Hermitian reconstruction block by block. -/
theorem map_A (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (c : ℝ) (hM : M.IsIndependent c) :
    M.P.map M.A =
      (Measure.pi fun _ : Fin k => Johansson.coordinateMeasure W (Real.toNNReal (c / W))).map
        (fun z j => Johansson.gaussianMatrixRaw (z j)) := by
  have hmeas : ∀ j, Measurable (fun w => M.A w j) :=
    fun j => (measurable_pi_apply j).comp M.measurable_A
  have hJ : IsProbabilityMeasure (Johansson.coordinateMeasure W (Real.toNNReal (c / W))) :=
    Johansson.coordinateMeasure_probability W _
  have hgR : Measurable (Johansson.gaussianMatrixRaw (N := W)) :=
    measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix
  have hG : ∀ j : Fin k, SigmaFinite ((Johansson.coordinateMeasure W (Real.toNNReal (c / W))).map
      (Johansson.gaussianMatrixRaw (N := W))) := fun _ => by
    infer_instance
  calc M.P.map M.A = M.P.map (fun w j => M.A w j) := rfl
    _ = Measure.pi (fun j => M.P.map (fun w => M.A w j)) :=
        (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hmeas j).aemeasurable)).mp hM.2.1
    _ = Measure.pi (fun _ : Fin k => (Johansson.coordinateMeasure W (Real.toNNReal (c / W))).map
          (Johansson.gaussianMatrixRaw (N := W))) := by
        congr 1
        funext j
        exact (hM.1 j).map_eq
    _ = _ := (Measure.pi_map_pi (fun _ => hgR.aemeasurable)).symm

/-- Normalization: `c^{-1/2} ⊕_j A_j` has exactly the canonical PSSS block-GUE law. -/
theorem hasLaw_Gm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (hW : 0 < W) (c : ℝ) (hc : 0 < c)
    (hM : M.IsIndependent c) :
    HasLaw (fun w => ((Real.sqrt c)⁻¹ : ℂ) • (Gm M w).1)
      ((canonicalMatrixMeasure (bsz k W) (fun _ => hW)).map Subtype.val) M.P := by
  set s : ℝ := (Real.sqrt c)⁻¹ with hs
  set S : ℝ≥0 := Real.toNNReal (c / W) with hS
  have hsS : s ^ 2 * (S : ℝ) = 1 / W := by
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    rw [hS, Real.coe_toNNReal _ (div_nonneg hc.le hW'.le), hs, inv_pow,
      Real.sq_sqrt hc.le]
    field_simp
  have hfun : (fun w => ((Real.sqrt c)⁻¹ : ℂ) • (Gm M w).1) =
      (fun a => (s : ℂ) • blockMatrix a) ∘ M.A := by
    funext w
    simp [Gm_val, hs]
  have hF : Measurable
      (fun a : Fin k → Matrix (Fin W) (Fin W) ℂ => (s : ℂ) • blockMatrix a) :=
    (continuous_const_smul (s : ℂ)).measurable.comp measurable_blockMatrix
  have hgR : Measurable (fun (z : Fin k → Johansson.UpperPair W → ℝ × ℝ) (j : Fin k) =>
      Johansson.gaussianMatrixRaw (z j)) :=
    measurable_pi_iff.mpr fun j =>
      (measurable_subtype_coe.comp Johansson.measurable_gaussianMatrix).comp (measurable_pi_apply j)
  have hR : Measurable (matrixOfUpperCoordinatesRaw (bsz k W)) :=
    measurable_subtype_coe.comp (measurable_matrixOfUpperCoordinates _)
  rw [hfun]
  refine ⟨(hF.comp M.measurable_A).aemeasurable, ?_⟩
  rw [← Measure.map_map hF M.measurable_A, map_A M c hM, Measure.map_map hF hgR]
  have hcomp : (fun a => (s : ℂ) • blockMatrix a) ∘
      (fun (z : Fin k → Johansson.UpperPair W → ℝ × ℝ) (j : Fin k) =>
        Johansson.gaussianMatrixRaw (z j)) =
      matrixOfUpperCoordinatesRaw (bsz k W) ∘ psi s := by
    funext z
    exact blockMatrix_gaussian_eq s z
  rw [hcomp, ← Measure.map_map hR (measurable_psi s), ← hS, map_psi hW s S hsS,
    canonicalMatrixMeasure, Measure.map_map measurable_subtype_coe
      (measurable_matrixOfUpperCoordinates _)]
  rfl

/-- The PSSS count of `D' + G` is the count of `H`. -/
theorem eigenCount_Dm_Gm (M : BlockBand.Internal.Contracts.Inputs.BlockModel k W) (w : M.Ω)
    (h : ((Dm M w).1 + (Gm M w).1).IsHermitian) (I : Set ℝ) :
    eigenCount ⟨(Dm M w).1 + (Gm M w).1, h⟩ I =
      eigenCount ⟨M.H w, isHermitian_H M w⟩ I := by
  apply eigenCount_eq_of_charpoly_eq
  change ((Dm M w).1 + (Gm M w).1).charpoly = (M.H w).charpoly
  rw [Dm_val, Gm_val, ← reindex_H, Matrix.charpoly_reindex]

end Model

/-!
### Main result
-/

/-- **Counting bound for block models** (first step of the finite-log recovery lemma). Assume
`BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount`. There is `C > 0` such that for every `k`, `W ≥ 1`,
`c > 0`, every `BlockBand.Internal.Contracts.Inputs.BlockModel k W` with independent `GUE_W(c/W)` blocks and
`(D, Y)` independent of the blocks (`IsIndependent c`; no norm bound on `D`), and every closed interval `[a, b]`,
the number of eigenvalues of the Hermitian matrix `H = D + ⊕_j A_j` in `[a, b]`, counted with multiplicity in the
increasing convention, is integrable under `M.P` and its expectation is at most `C/√c · kW · (b - a)`. The
constant is uniform in `k, W, c`, the model and the interval. -/
theorem blockModel_count_le (hCount : BlockBand.Internal.Contracts.Inputs.ConditionalBlockGUECount) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c →
      ∀ M : BlockBand.Internal.Contracts.Inputs.BlockModel k W, M.IsIndependent c → ∀ (a b : ℝ), a ≤ b →
        Integrable (fun w => ((Finset.univ.filter fun i =>
            increasingEigenvalue (isHermitian_H M w) i ∈ Set.Icc a b).card : ℝ)) M.P ∧
        (∫ w, ((Finset.univ.filter fun i =>
            increasingEigenvalue (isHermitian_H M w) i ∈ Set.Icc a b).card : ℝ) ∂M.P) ≤
          C / Real.sqrt c * ((k * W : ℕ) : ℝ) * (b - a) := by
  obtain ⟨C, hC, hmain⟩ := hCount
  refine ⟨C, hC, ?_⟩
  intro k W hW c hc M hM a b hab
  obtain ⟨hint, hle⟩ := hmain M.Ω M.P k (bsz k W) (fun _ => hW) c hc (Gm M) (Dm M)
    (measurable_Gm M) (measurable_Dm M) (hasLaw_Gm M hW c hc hM) (indepFun_Dm_Gm M c hM)
    a b hab 1 le_rfl
  have hfc : factorialCount (fun w => eigenCount ⟨(Dm M w).1 + (Gm M w).1,
        (Dm M w).2.add (Gm M w).2⟩ (Set.Icc a b)) 1 =
      fun w => ((Finset.univ.filter fun i =>
        increasingEigenvalue (isHermitian_H M w) i ∈ Set.Icc a b).card : ℝ) := by
    funext w
    rw [factorialCount, Nat.descFactorial_one, eigenCount_Dm_Gm]
    unfold eigenCount
    congr
  rw [hfc] at hint hle
  refine ⟨hint, hle.trans (le_of_eq ?_)⟩
  rw [pow_one]
  congr 3
  simp

end BlockBand.Endpoints.BlockModelCount
