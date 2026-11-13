module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.CompressionSpectrum
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneInterlacing
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.RankOneCompressionLimits

/-!
# Positive rank-one rays and codimension-one compression

This module develops the deterministic finite-branch part of the rank-one
limit of PSSS (Peled–Schenker–Shamis–Sodin).  No probabilistic estimate and no
tail argument of APSSS (Aizenman–Peled–Schenker–Shamis–Sodin) enters.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Filter
open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

universe u

/-- The source-facing name for the canonical ambient compression `P K Pᴴ`. -/
def compressHermitian {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) : HermitianMatrix ι :=
  orthogonalCompression K u

/-- Rank-one shifts form an additive ray. -/
theorem rankOneShift_add {ι : Type u} [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (s t : ℝ) :
    rankOneShift (rankOneShift K u s) u t = rankOneShift K u (s + t) := by
  apply Subtype.ext
  simp only [rankOneShift_coe]
  push_cast
  rw [add_smul]
  abel

/-- Every decreasingly ordered eigenvalue branch of a positive rank-one ray
is monotone in its ray parameter. -/
theorem eigenvalues₀_rankOneShift_monotone {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι)
    (i : Fin (Fintype.card ι)) :
    Monotone (fun τ : ℝ => (rankOneShift K u τ).2.eigenvalues₀ i) := by
  intro s t hst
  have hnonneg : 0 ≤ t - s := sub_nonneg.mpr hst
  have h := eigenvalues₀_rankOneShift_mono
    (rankOneShift K u s) u hnonneg i
  simpa [rankOneShift_add, sub_add_cancel] using h

/-- The Rayleigh quotient of the ambient compression agrees with that of
`K` on `u⊥`. -/
theorem re_inner_compressionRestriction_eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (x : (ℂ ∙ u)ᗮ) :
    RCLike.re (inner ℂ (compressionRestriction K u hu x) x) =
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 (x : EuclideanSpace ℂ ι)) x) := by
  have hx : inner ℂ u (x : EuclideanSpace ℂ ι) = 0 := by
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
  change RCLike.re (inner ℂ
    ((compressionRestriction K u hu x : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ ι)
      (x : EuclideanSpace ℂ ι)) = _
  rw [compressionRestriction_apply]
  change RCLike.re (inner ℂ
    (Matrix.toEuclideanLin
      (orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ)
      (x : EuclideanSpace ℂ ι)) x) = _
  rw [orthogonalProjector_conjTranspose]
  let b := (EuclideanSpace.basisFun ι ℂ).toBasis
  change RCLike.re (inner ℂ
    (Matrix.toLin b b (orthogonalProjector u * K.1 * orthogonalProjector u)
      (x : EuclideanSpace ℂ ι)) x) = _
  rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b]
  change RCLike.re (inner ℂ
    (Matrix.toEuclideanLin (orthogonalProjector u)
      (Matrix.toEuclideanLin K.1
        (Matrix.toEuclideanLin (orthogonalProjector u) x))) x) = _
  rw [orthogonalProjector_apply_of_inner_eq_zero u x hx]
  rw [toEuclideanLin_orthogonalProjector_apply]
  rw [inner_sub_left, inner_smul_left]
  rw [inner_conj_symm (Matrix.toEuclideanLin K.1 x) u, hx]
  simp

/-- The shifted eigenvalue immediately below the escaping branch is bounded
above by the corresponding eigenvalue of the compression.  This is
the min–max comparison that ties the bounded branches to `u⊥`. -/
theorem eigenvalues₀_rankOneShift_succ_le_compression {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (τ : ℝ) (k : Fin (Fintype.card ι - 1)) :
    (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k) ≤
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k := by
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (rankOneShift K u τ).2
  obtain ⟨V, hVdim, hVlow⟩ :=
    hS.exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace (finPredSucc k)
  have hVdim' : Module.finrank ℂ V = ((k : ℕ) + 1) + 1 := by
    simpa [finPredSucc] using hVdim
  obtain ⟨W, hWle, hWdim⟩ :=
    exists_submodule_le_inf_innerKernel_finrank_eq V u hVdim'
  let U : Submodule ℂ (EuclideanSpace ℂ ι) := (ℂ ∙ u)ᗮ
  have hWU : W ≤ U := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact (mem_innerKernel_iff u x).mp (hWle hx).2
  let WU : Submodule ℂ U := W.submoduleOf U
  have hWUdim : Module.finrank ℂ WU = (k : ℕ) + 1 := by
    calc
      Module.finrank ℂ WU = Module.finrank ℂ W :=
        (W.submoduleOfEquivOfLe hWU).finrank_eq
      _ = (k : ℕ) + 1 := hWdim
  let hC := compressionRestriction_isSymmetric K u hu
  obtain ⟨x, hxWU, hxnorm, hxC⟩ :=
    hC.exists_unit_vector_re_inner_le_eigenvalue
      (finrank_spanOrthogonal_eq_card_sub_one u hu) k WU hWUdim
  have hxW : (x : EuclideanSpace ℂ ι) ∈ W := hxWU
  have hxV : (x : EuclideanSpace ℂ ι) ∈ V := (hWle hxW).1
  have hxorth : inner ℂ u (x : EuclideanSpace ℂ ι) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  have hshift :
      RCLike.re (inner ℂ
        (Matrix.toEuclideanLin
          (rankOneShift K u τ : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι)) x) =
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 x) x) := by
    rw [toEuclideanLin_rankOneShift, LinearMap.add_apply,
      LinearMap.smul_apply, inner_add_left, map_add]
    simp [InnerProductSpace.rankOne_apply, hxorth]
  exact (hVlow (x : EuclideanSpace ℂ ι) hxV hxnorm).trans
    (hshift.le.trans ((re_inner_compressionRestriction_eq K u hu x).symm.le.trans hxC))

/-- Every non-top decreasing branch is bounded above, uniformly on the whole
rank-one ray.  This is the shifted half of codimension-one interlacing. -/
theorem eigenvalues₀_rankOneShift_succ_bddAbove {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι)
    (k : Fin (Fintype.card ι - 1)) :
    BddAbove (Set.range (fun τ : ℝ =>
      (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k))) := by
  refine ⟨K.2.eigenvalues₀ (finPredCast k), ?_⟩
  rintro _ ⟨τ, rfl⟩
  exact eigenvalues₀_rankOneShift_succ_le K u τ k

/-- The finite limit of a non-top decreasing eigenvalue branch, defined as
its supremum along the positive rank-one ray. -/
def rankOneFiniteBranchLimit {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι)
    (k : Fin (Fintype.card ι - 1)) : ℝ :=
  ⨆ τ : ℝ, (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)

/-- Without any assumed convergence, monotonicity and interlacing give a
finite limit for every one of the `n-1` non-top branches. -/
theorem eigenvalues₀_rankOneShift_succ_tendsto_limit {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι)
    (k : Fin (Fintype.card ι - 1)) :
    Tendsto (fun τ : ℝ =>
      (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) atTop
      (𝓝 (rankOneFiniteBranchLimit K u k)) := by
  exact tendsto_atTop_ciSup
    (eigenvalues₀_rankOneShift_monotone K u (finPredSucc k))
    (eigenvalues₀_rankOneShift_succ_bddAbove K u k)

/-- The finite monotone branch limit is bounded above by the matching
ordered eigenvalue of the codimension-one compression. -/
theorem rankOneFiniteBranchLimit_le_compression {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (k : Fin (Fintype.card ι - 1)) :
    rankOneFiniteBranchLimit K u k ≤
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k := by
  exact ciSup_le fun τ =>
    eigenvalues₀_rankOneShift_succ_le_compression K u hu τ k

/-- A finite family dominated termwise by another and with the same total sum
is equal termwise.  Applied below, this isolates the sole remaining spectral
input as a trace/sum identity rather than an assumed branch convergence. -/
theorem rankOneFiniteBranchLimit_eq_compression_of_sum_eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (hsum : (∑ k : Fin (Fintype.card ι - 1), rankOneFiniteBranchLimit K u k) =
      ∑ k : Fin (Fintype.card ι - 1),
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k)
    (k : Fin (Fintype.card ι - 1)) :
    rankOneFiniteBranchLimit K u k =
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k := by
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin (Fintype.card ι - 1))),
      rankOneFiniteBranchLimit K u j ≤
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) j := by
    intro j _
    exact rankOneFiniteBranchLimit_le_compression K u hu j
  exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum) k (Finset.mem_univ k)

/-- Endpoint-stable equality with the compression spectrum, reduced
only to the explicit finite trace/sum identity.  Branch convergence itself is
constructed in this module and is not a premise. -/
theorem eigenCount_rankOne_eventually_eq_of_sum_eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (hsum : (∑ k : Fin (Fintype.card ι - 1), rankOneFiniteBranchLimit K u k) =
      ∑ k : Fin (Fintype.card ι - 1),
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k)
    {a b : ℝ}
    (ha : ∀ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k ≠ a)
    (hb : ∀ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k ≠ b) :
    ∀ᶠ τ in atTop,
      finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
        (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) (Set.Icc a b) =
      finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k) (Set.Icc a b) := by
  let μ : Fin (Fintype.card ι - 1) → ℝ := fun k =>
    (compressionRestriction_isSymmetric K u hu).eigenvalues
      (finrank_spanOrthogonal_eq_card_sub_one u hu) k
  have hlim : rankOneFiniteBranchLimit K u = μ := by
    funext k
    exact rankOneFiniteBranchLimit_eq_compression_of_sum_eq K u hu hsum k
  have hconv : ∀ k, Tendsto (fun τ : ℝ =>
      (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) atTop (𝓝 (μ k)) := by
    intro k
    simpa [hlim] using eigenvalues₀_rankOneShift_succ_tendsto_limit K u k
  exact eventually_finiteSpectralCount_Icc_eq_of_tendsto
    (fun (τ : ℝ) k =>
      (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) μ ha hb hconv

/-- Rank-one count interlacing immediately supplies the descending-factorial
predecessor bound used by the PSSS induction. -/
theorem descFactorial_rankOne_le {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) {τ : ℝ} (hτ : 0 ≤ τ)
    (s : Set ℝ) (hs : s.OrdConnected) (m : ℕ) :
    (eigenCount K s - 1).descFactorial m ≤
      (eigenCount (rankOneShift K u τ) s).descFactorial m := by
  apply descFactorial_pred_le_of_count_le_succ
  exact (PSSSNative.BlockBand.eigenCount_rankOne_interlacing
    K (rankOneShift K u τ) (WithLp.ofLp u) hτ rfl s hs).1

/-- The canonical ambient compression count is the restriction count
plus exactly one contribution at zero. -/
theorem eigenCount_compressHermitian_eq_restriction {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (s : Set ℝ) :
    eigenCount (compressHermitian K u) s =
      finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k) s +
      Set.indicator s (fun _ => (1 : ℕ)) 0 := by
  rw [eigenCount_eq_roots_countP]
  let bE := (EuclideanSpace.basisFun ι ℂ).toBasis
  change Multiset.countP (fun z : ℂ => RCLike.re z ∈ s)
      (orthogonalCompression K u : Matrix ι ι ℂ).charpoly.roots = _
  rw [← Matrix.charpoly_toLin (orthogonalCompression K u : Matrix ι ι ℂ) bE]
  change Multiset.countP (fun z : ℂ => RCLike.re z ∈ s)
      (Matrix.toEuclideanLin
        (orthogonalCompression K u : Matrix ι ι ℂ)).charpoly.roots = _
  rw [orthogonalCompression_roots_charpoly_eq_zero_cons_restriction K u hu]
  rw [Multiset.countP_add]
  let hC := compressionRestriction_isSymmetric K u hu
  rw [hC.roots_charpoly_eq_eigenvalues
    (finrank_spanOrthogonal_eq_card_sub_one u hu)]
  simp only [Multiset.countP_map, Function.comp_apply, RCLike.ofReal_re]
  have hzero : Multiset.countP (fun z : ℂ => RCLike.re z ∈ s)
      ({0} : Multiset ℂ) = (if (0 : ℝ) ∈ s then 1 else 0) := by
    change Multiset.countP (fun z : ℂ => RCLike.re z ∈ s) (0 ::ₘ 0) = _
    rw [Multiset.countP_cons, Multiset.countP_zero, zero_add]
    rfl
  rw [hzero]
  change (if (0 : ℝ) ∈ s then 1 else 0) +
      (Finset.univ.filter fun k : Fin (Fintype.card ι - 1) =>
        hC.eigenvalues (finrank_spanOrthogonal_eq_card_sub_one u hu) k ∈ s).card =
    finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
      hC.eigenvalues (finrank_spanOrthogonal_eq_card_sub_one u hu) k) s +
      Set.indicator s (fun _ => (1 : ℕ)) 0
  rw [finiteSpectralCount]
  simp only [Set.indicator_apply]
  split_ifs <;> omega

/-- The real trace lost under unit codimension-one compression is precisely
its Rayleigh quotient in the removed direction. -/
theorem re_trace_orthogonalCompression_eq_sub {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
      (Matrix.toEuclideanLin (orthogonalCompression K u : Matrix ι ι ℂ))) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) -
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) := by
  let T : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := Matrix.toEuclideanLin K.1
  let R : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
    InnerProductSpace.rankOne ℂ u u
  let P : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := LinearMap.id - R
  have hP : P.comp P = P := by
    apply LinearMap.ext
    intro x
    change x - inner ℂ u x • u -
        inner ℂ u (x - inner ℂ u x • u) • u =
      x - inner ℂ u x • u
    rw [inner_sub_right, inner_smul_right,
      inner_self_eq_one_of_norm_eq_one hu]
    simp
  have hC : Matrix.toEuclideanLin
      (orthogonalCompression K u : Matrix ι ι ℂ) = P.comp (T.comp P) := by
    change Matrix.toEuclideanLin
      (orthogonalProjector u * K.1 * (orthogonalProjector u)ᴴ) = _
    rw [orthogonalProjector_conjTranspose]
    let b := (EuclideanSpace.basisFun ι ℂ).toBasis
    apply LinearMap.ext
    intro x
    change Matrix.toLin b b (orthogonalProjector u * K.1 * orthogonalProjector u) x = _
    rw [Matrix.toLin_mul_apply b b b, Matrix.toLin_mul_apply b b b]
    change Matrix.toEuclideanLin (orthogonalProjector u)
      (Matrix.toEuclideanLin K.1
        (Matrix.toEuclideanLin (orthogonalProjector u) x)) = _
    rw [toEuclideanLin_orthogonalProjector]
    rfl
  rw [hC]
  rw [LinearMap.trace_comp_comm']
  change RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
      (T.comp (P.comp P))) = _
  rw [hP]
  change RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
      (T.comp (LinearMap.id - R))) = _
  rw [LinearMap.comp_sub, LinearMap.comp_id, map_sub, map_sub]
  have hTR : T.comp R = InnerProductSpace.rankOne ℂ (T u) u := by
    ext x
    simp [T, R, InnerProductSpace.rankOne_apply]
  rw [hTR, InnerProductSpace.trace_rankOne]
  have hr : RCLike.re (inner ℂ u (T u)) =
      RCLike.re (inner ℂ (T u) u) := by
    calc
      RCLike.re (inner ℂ u (T u)) =
          RCLike.re (starRingEnd ℂ (inner ℂ (T u) u)) := by
            rw [inner_conj_symm u (T u)]
      _ = RCLike.re (inner ℂ (T u) u) :=
        RCLike.conj_re (inner ℂ (T u) u)
  rw [hr]

/-- Removing the escaping top eigenvalue from the affine trace leaves the
sum of the `n-1` finite branches. -/
theorem sum_eigenvalues₀_rankOneShift_succ {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1)
    (τ : ℝ) :
    (∑ k : Fin (Fintype.card ι - 1),
      (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) -
      ((rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι)) - τ) := by
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  have hn : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
  let f : Fin ((Fintype.card ι - 1) + 1) → ℝ := fun i =>
    (rankOneShift K u τ).2.eigenvalues₀ (Fin.cast hn.symm i)
  have hsplit := Fin.sum_univ_succ f
  have hfull : (∑ i : Fin ((Fintype.card ι - 1) + 1), f i) =
      ∑ i : Fin (Fintype.card ι),
        (rankOneShift K u τ).2.eigenvalues₀ i := by
    exact Fin.sum_congr' _ hn.symm
  have hsplit' :
      (∑ i : Fin (Fintype.card ι),
        (rankOneShift K u τ).2.eigenvalues₀ i) =
      (rankOneShift K u τ).2.eigenvalues₀
          (0 : Fin (Fintype.card ι)) +
        ∑ k : Fin (Fintype.card ι - 1),
          (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k) := by
    calc
      _ = ∑ i : Fin ((Fintype.card ι - 1) + 1), f i := hfull.symm
      _ = f 0 + ∑ k : Fin (Fintype.card ι - 1), f k.succ := hsplit
      _ = _ := by rfl
  rw [sum_eigenvalues₀_rankOneShift K u τ, hu, one_pow, mul_one] at hsplit'
  linarith

/-- The total of the intrinsically constructed finite branch limits is the
ambient trace with the escaping Rayleigh contribution removed. -/
theorem sum_rankOneFiniteBranchLimit {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) {u : EuclideanSpace ℂ ι} (hu : ‖u‖ = 1) :
    (∑ k : Fin (Fintype.card ι - 1), rankOneFiniteBranchLimit K u k) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) -
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) := by
  let : Nonempty ι := nonempty_of_euclidean_norm_eq_one u hu
  have hleft : Tendsto (fun τ : ℝ =>
      ∑ k : Fin (Fintype.card ι - 1),
        (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) atTop
      (𝓝 (∑ k : Fin (Fintype.card ι - 1),
        rankOneFiniteBranchLimit K u k)) := by
    simpa only [Finset.sum_apply] using
      (tendsto_finsetSum (Finset.univ : Finset (Fin (Fintype.card ι - 1)))
        (fun k _ => eigenvalues₀_rankOneShift_succ_tendsto_limit K u k))
  have hright : Tendsto (fun τ : ℝ =>
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) -
      ((rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι)) - τ)) atTop
      (𝓝 (RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
          (Matrix.toEuclideanLin K.1)) -
        RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u))) := by
    exact tendsto_const_nhds.sub
      (eigenvalues₀_zero_rankOneShift_sub_tendsto K hu)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  exact Eventually.of_forall fun τ => (sum_eigenvalues₀_rankOneShift_succ K hu τ).symm

/-- Compression eigenvalues have the same trace-minus-Rayleigh total as the
bounded rank-one branches. -/
theorem sum_compression_eigenvalues_eq_sub {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (∑ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k) =
      RCLike.re ((LinearMap.trace ℂ (EuclideanSpace ℂ ι))
        (Matrix.toEuclideanLin K.1)) -
      RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 u) u) := by
  rw [sum_compression_eigenvalues_eq_re_trace K u hu]
  exact re_trace_orthogonalCompression_eq_sub K u hu

/-- The constructed finite branch limits and the compression have
identical total sums. -/
theorem rankOneFiniteBranch_sum_eq_compression {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (∑ k : Fin (Fintype.card ι - 1), rankOneFiniteBranchLimit K u k) =
      ∑ k : Fin (Fintype.card ι - 1),
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k := by
  let : Nonempty ι := nonempty_of_euclidean_norm_eq_one u hu
  rw [sum_rankOneFiniteBranchLimit K hu,
    sum_compression_eigenvalues_eq_sub K u hu]

/-- Endpoint-stable compression-count limit for a positive rank-one
ray.  Both branch convergence and the trace comparison are proved above. -/
theorem eigenCount_rankOne_eventually_eq_restriction {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    {a b : ℝ}
    (ha : ∀ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k ≠ a)
    (hb : ∀ k : Fin (Fintype.card ι - 1),
      (compressionRestriction_isSymmetric K u hu).eigenvalues
        (finrank_spanOrthogonal_eq_card_sub_one u hu) k ≠ b) :
    ∀ᶠ τ in atTop,
      finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
        (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k)) (Set.Icc a b) =
      finiteSpectralCount (fun k : Fin (Fintype.card ι - 1) =>
        (compressionRestriction_isSymmetric K u hu).eigenvalues
          (finrank_spanOrthogonal_eq_card_sub_one u hu) k) (Set.Icc a b) := by
  let : Nonempty ι := nonempty_of_euclidean_norm_eq_one u hu
  exact eigenCount_rankOne_eventually_eq_of_sum_eq K u hu
    (rankOneFiniteBranch_sum_eq_compression K u hu) ha hb

/-- **PSSS rank-one compression limit.**  For a closed interval whose
endpoints carry only the canonical extra-zero multiplicity in `P K Pᴴ`, the
rank-one-ray count, with that zero restored, is eventually the ambient
compression count.  No convergence statement is assumed. -/
theorem eigenCount_rankOne_eventually_eq {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    {a b : ℝ} (_hab : a ≤ b)
    (ha : eigenCount (compressHermitian K u) {a} = (if a = 0 then 1 else 0))
    (hb : eigenCount (compressHermitian K u) {b} = (if b = 0 then 1 else 0)) :
    ∀ᶠ τ : ℝ in atTop,
      eigenCount (rankOneShift K u τ) (Set.Icc a b) +
          (if (0 : ℝ) ∈ Set.Icc a b then 1 else 0) =
        eigenCount (compressHermitian K u) (Set.Icc a b) := by
  let : Nonempty ι := nonempty_of_euclidean_norm_eq_one u hu
  let μ : Fin (Fintype.card ι - 1) → ℝ := fun k =>
    (compressionRestriction_isSymmetric K u hu).eigenvalues
      (finrank_spanOrthogonal_eq_card_sub_one u hu) k
  have hca := eigenCount_compressHermitian_eq_restriction K u hu ({a} : Set ℝ)
  have hcb := eigenCount_compressHermitian_eq_restriction K u hu ({b} : Set ℝ)
  have hza : finiteSpectralCount μ {a} = 0 := by
    rw [ha] at hca
    change (if a = 0 then 1 else 0) =
      finiteSpectralCount μ {a} + Set.indicator {a} (fun _ => (1 : ℕ)) 0 at hca
    have hind : Set.indicator ({a} : Set ℝ) (fun _ => (1 : ℕ)) 0 =
        (if a = 0 then 1 else 0) := by
      by_cases h : a = 0 <;> simp [h, ne_comm]
    rw [hind] at hca
    omega
  have hzb : finiteSpectralCount μ {b} = 0 := by
    rw [hb] at hcb
    change (if b = 0 then 1 else 0) =
      finiteSpectralCount μ {b} + Set.indicator {b} (fun _ => (1 : ℕ)) 0 at hcb
    have hind : Set.indicator ({b} : Set ℝ) (fun _ => (1 : ℕ)) 0 =
        (if b = 0 then 1 else 0) := by
      by_cases h : b = 0 <;> simp [h, ne_comm]
    rw [hind] at hcb
    omega
  have ha' : ∀ k, μ k ≠ a := by
    simpa [finiteSpectralCount] using hza
  have hb' : ∀ k, μ k ≠ b := by
    simpa [finiteSpectralCount] using hzb
  have htail := eigenCount_rankOne_eventually_eq_restriction K u hu ha' hb'
  have htop : ∀ᶠ τ : ℝ in atTop,
      b < (rankOneShift K u τ).2.eigenvalues₀
        (0 : Fin (Fintype.card ι)) :=
    (eigenvalues₀_zero_rankOneShift_tendsto_atTop K hu)
      (eventually_gt_atTop b)
  filter_upwards [htail, htop] with τ hτ hτtop
  have hnot : (rankOneShift K u τ).2.eigenvalues₀
      (0 : Fin (Fintype.card ι)) ∉ Set.Icc a b := by
    intro h
    exact (not_lt_of_ge h.2) hτtop
  rw [eigenCount_eq_finiteBranches_of_top_not_mem
    (rankOneShift K u τ) (Set.Icc a b) hnot]
  rw [hτ]
  rw [eigenCount_compressHermitian_eq_restriction K u hu]
  simp only [Set.indicator_apply]

end PSSSNative.BlockBand.PSSS
