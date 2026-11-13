module

public import BlockBand.Native.PSSS.BlockBand.Spectral.Ordered
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Rank-one interlacing for ordered Hermitian spectra

This PSSS-independent module provides the deterministic interface used by the
external PSSS argument.  The perturbation matrix is supplied only through an
explicit equality, so the theorem applies to arbitrary matrix families.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand

open scoped ComplexConjugate Matrix

universe u v

attribute [local instance] Classical.propDecidable

def rankOneFinPredCast {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k, by have := k.isLt; omega⟩

def rankOneFinPredSucc {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k + 1, by have := k.isLt; omega⟩

/-- Counts in an order-convex set differ by at most one for two increasing
finite spectra satisfying positive rank-one interlacing. -/
theorem finiteOrderedCount_interlacing {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Monotone y)
    (hxy : ∀ i, x i ≤ y i)
    (hyx : ∀ k : Fin (n - 1), y (rankOneFinPredCast k) ≤ x (rankOneFinPredSucc k))
    (s : Set ℝ) (hs : s.OrdConnected) :
    (Finset.univ.filter fun i => x i ∈ s).card ≤
        (Finset.univ.filter fun i => y i ∈ s).card + 1 ∧
      (Finset.univ.filter fun i => y i ∈ s).card ≤
        (Finset.univ.filter fun i => x i ∈ s).card + 1 := by
  classical
  let sx : Finset (Fin n) := Finset.univ.filter fun i => x i ∈ s
  let sy : Finset (Fin n) := Finset.univ.filter fun i => y i ∈ s
  have hfirst : sx.card ≤ sy.card + 1 := by
    by_cases hempty : sx = ∅
    · simp [hempty]
    · have hsx : sx.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let m : Fin n := sx.max' hsx
      have hm : m ∈ sx := Finset.max'_mem sx hsx
      have hsub : sx.erase m ⊆ sy := by
        intro i hi
        have hisx : i ∈ sx := (Finset.mem_erase.mp hi).2
        have him : i ≠ m := (Finset.mem_erase.mp hi).1
        have himle : i ≤ m := Finset.le_max' sx i hisx
        have himlt : i < m := lt_of_le_of_ne himle him
        have hin : i.val < n - 1 := by
          have hm_lt := m.isLt
          omega
        let k : Fin (n - 1) := ⟨i, hin⟩
        have hsucc : rankOneFinPredSucc k ≤ m := by
          apply Fin.le_iff_val_le_val.mpr
          dsimp [rankOneFinPredSucc, k]
          omega
        have hxi : x i ∈ s := by simpa [sx] using hisx
        have hxm : x m ∈ s := by simpa [sx] using hm
        have hlow : x i ≤ y i := hxy i
        have hupp : y i ≤ x m := by
          calc
            y i = y (rankOneFinPredCast k) := rfl
            _ ≤ x (rankOneFinPredSucc k) := hyx k
            _ ≤ x m := hx hsucc
        have hyis : y i ∈ s := hs.out hxi hxm ⟨hlow, hupp⟩
        simpa [sy] using hyis
      calc
        sx.card = (sx.erase m).card + 1 :=
          (Finset.card_erase_add_one hm).symm
        _ ≤ sy.card + 1 := Nat.add_le_add_right (Finset.card_le_card hsub) 1
  have hsecond : sy.card ≤ sx.card + 1 := by
    by_cases hempty : sy = ∅
    · simp [hempty]
    · have hsy : sy.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let m : Fin n := sy.min' hsy
      have hm : m ∈ sy := Finset.min'_mem sy hsy
      have hsub : sy.erase m ⊆ sx := by
        intro i hi
        have hisy : i ∈ sy := (Finset.mem_erase.mp hi).2
        have him : i ≠ m := (Finset.mem_erase.mp hi).1
        have hmle : m ≤ i := Finset.min'_le sy i hisy
        have hmlt : m < i := lt_of_le_of_ne hmle (Ne.symm him)
        have hi0 : 0 < i.val := by omega
        let k : Fin (n - 1) := ⟨i.val - 1, by have := i.isLt; omega⟩
        have hcast : m ≤ rankOneFinPredCast k := by
          apply Fin.le_iff_val_le_val.mpr
          dsimp [rankOneFinPredCast, k]
          omega
        have hsucc : rankOneFinPredSucc k = i := by
          apply Fin.ext
          dsimp [rankOneFinPredSucc, k]
          omega
        have hym : y m ∈ s := by simpa [sy] using hm
        have hyi : y i ∈ s := by simpa [sy] using hisy
        have hlow : y m ≤ x i := by
          calc
            y m ≤ y (rankOneFinPredCast k) := hy hcast
            _ ≤ x (rankOneFinPredSucc k) := hyx k
            _ = x i := by rw [hsucc]
        have hupp : x i ≤ y i := hxy i
        have hxis : x i ∈ s := hs.out hym hyi ⟨hlow, hupp⟩
        simpa [sx] using hxis
      calc
        sy.card = (sy.erase m).card + 1 :=
          (Finset.card_erase_add_one hm).symm
        _ ≤ sx.card + 1 := Nat.add_le_add_right (Finset.card_le_card hsub) 1
  simpa only [sx, sy] using ⟨hfirst, hsecond⟩

private theorem toEuclideanLin_vecMulVec_self {ι : Type u}
    [Fintype ι] [DecidableEq ι] (u : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin
        (Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u))) =
      (InnerProductSpace.rankOne ℂ u u : EuclideanSpace ℂ ι →ₗ[ℂ]
        EuclideanSpace ℂ ι) := by
  have h := congrArg Matrix.toEuclideanLin
    (InnerProductSpace.symm_toEuclideanLin_rankOne u u)
  simpa using h.symm

private def rankOneInnerKernel {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) : Submodule ℂ E :=
  (innerSL ℂ u).toLinearMap.ker

private theorem mem_rankOneInnerKernel_iff {E : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u x : E) :
    x ∈ rankOneInnerKernel u ↔ inner ℂ u x = 0 := by
  simp [rankOneInnerKernel]

private theorem exists_submodule_le_inf_rankOneInnerKernel_finrank_eq
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (V : Submodule ℂ E) (u : E) {d : ℕ}
    (hV : Module.finrank ℂ V = d + 1) :
    ∃ W : Submodule ℂ E,
      W ≤ V ⊓ rankOneInnerKernel u ∧ Module.finrank ℂ W = d := by
  let f : V →ₗ[ℂ] ℂ := (innerSL ℂ u).toLinearMap.comp V.subtype
  have hrange : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    calc
      Module.finrank ℂ (LinearMap.range f) ≤ Module.finrank ℂ ℂ :=
        Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℂ
  have hker : d ≤ Module.finrank ℂ (LinearMap.ker f) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker f
    rw [hV] at hrank
    omega
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank hker
  let g : Fin d → E := fun i => ((q i : V) : E)
  have hg : LinearIndependent ℂ g := by
    exact (hq.map' (LinearMap.ker f).subtype
      (LinearMap.ker f).ker_subtype).map' V.subtype V.ker_subtype
  refine ⟨Submodule.span ℂ (Set.range g), ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    refine ⟨(q i).val.property, ?_⟩
    change inner ℂ u ((q i : V) : E) = 0
    exact (q i).property
  · simpa [g] using finrank_span_eq_card hg

private theorem rankOne_eigenvalues₀_same_le {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K Kτ : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hKτ : (Kτ : Matrix ι ι ℂ) = K.1 + (τ : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)))
    (i : Fin (Fintype.card ι)) :
    K.2.eigenvalues₀ i ≤ Kτ.2.eigenvalues₀ i := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  apply LinearMap.IsSymmetric.eigenvalue_mono
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr K.2)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr Kτ.2)
    finrank_euclideanSpace
  intro x
  rw [show Matrix.toEuclideanLin Kτ.1 = Matrix.toEuclideanLin K.1 +
      (τ : ℂ) • (InnerProductSpace.rankOne ℂ u u :
        EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) by
    rw [hKτ, map_add, map_smul, toEuclideanLin_vecMulVec_self]]
  rw [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, map_add]
  apply le_add_of_nonneg_right
  rw [inner_smul_left]
  change 0 ≤ RCLike.re ((starRingEnd ℂ) (τ : ℂ) *
    inner ℂ (InnerProductSpace.rankOne ℂ u u x) x)
  rw [InnerProductSpace.inner_left_rankOne_apply, ← inner_conj_symm x u]
  simp only [RCLike.mul_re, RCLike.conj_re, RCLike.conj_im, neg_mul]
  have hre : RCLike.re (τ : ℂ) = τ := RCLike.ofReal_re τ
  have him : RCLike.im (τ : ℂ) = 0 := RCLike.ofReal_im τ
  rw [hre, him]
  simp only [zero_mul]
  ring_nf
  exact add_nonneg (mul_nonneg hτ (sq_nonneg _))
    (mul_nonneg hτ (sq_nonneg _))

private theorem rankOne_eigenvalues₀_succ_le {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K Kτ : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ)
    (hKτ : (Kτ : Matrix ι ι ℂ) = K.1 + (τ : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)))
    (k : Fin (Fintype.card ι - 1)) :
    Kτ.2.eigenvalues₀ (rankOneFinPredSucc k) ≤
      K.2.eigenvalues₀ (rankOneFinPredCast k) := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr K.2
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr Kτ.2
  obtain ⟨V, hVdim, hVlow⟩ :=
    hS.exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace (rankOneFinPredSucc k)
  have hVdim' : Module.finrank ℂ V = ((k : ℕ) + 1) + 1 := by
    simpa [rankOneFinPredSucc] using hVdim
  obtain ⟨W, hWle, hWdim⟩ :=
    exists_submodule_le_inf_rankOneInnerKernel_finrank_eq V u hVdim'
  obtain ⟨x, hxW, hxnorm, hxT⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue
      finrank_euclideanSpace (rankOneFinPredCast k) W
        (by simpa [rankOneFinPredCast] using hWdim)
  have hxV : x ∈ V := (hWle hxW).1
  have hxorth : inner ℂ u x = 0 :=
    (mem_rankOneInnerKernel_iff u x).mp (hWle hxW).2
  have hquad :
      RCLike.re (inner ℂ (Matrix.toEuclideanLin Kτ.1 x) x) =
        RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 x) x) := by
    rw [show Matrix.toEuclideanLin Kτ.1 = Matrix.toEuclideanLin K.1 +
        (τ : ℂ) • (InnerProductSpace.rankOne ℂ u u :
          EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) by
      rw [hKτ, map_add, map_smul, toEuclideanLin_vecMulVec_self]]
    rw [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, map_add]
    simp [InnerProductSpace.rankOne_apply, hxorth]
  exact (hVlow x hxV hxnorm).trans (hquad.le.trans hxT)

private theorem orderedEigenvalue_rankOne_same_le {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K Kτ : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ)
    (hτ : 0 ≤ τ)
    (hKτ : (Kτ : Matrix ι ι ℂ) = K.1 + (τ : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)))
    (i : Fin (Fintype.card ι)) :
    orderedEigenvalue K i ≤ orderedEigenvalue Kτ i :=
  rankOne_eigenvalues₀_same_le K Kτ u τ hτ hKτ i.rev

private theorem orderedEigenvalue_rankOne_cast_le_succ {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K Kτ : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ)
    (hKτ : (Kτ : Matrix ι ι ℂ) = K.1 + (τ : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)))
    (k : Fin (Fintype.card ι - 1)) :
    orderedEigenvalue Kτ (rankOneFinPredCast k) ≤
      orderedEigenvalue K (rankOneFinPredSucc k) := by
  let i := rankOneFinPredCast k
  let j := rankOneFinPredSucc k
  have hij : i < j := by
    apply Fin.lt_def.mpr
    simp [i, j, rankOneFinPredCast, rankOneFinPredSucc]
  let q : Fin (Fintype.card ι - 1) :=
    ⟨j.rev, by
      have hj := j.isLt
      have hijv := Fin.lt_def.mp hij
      simp only [Fin.rev, j] at *
      omega⟩
  have hcast : rankOneFinPredCast q = j.rev := by
    apply Fin.ext
    rfl
  have hsucc : rankOneFinPredSucc q = i.rev := by
    apply Fin.ext
    simp only [rankOneFinPredSucc, q, i, j, rankOneFinPredCast, Fin.rev]
    omega
  simpa [orderedEigenvalue, i, j, hcast, hsucc] using
    rankOne_eigenvalues₀_succ_le K Kτ u τ hKτ q

/-- **Rank-one count interlacing.** If `Kτ` is an arbitrary
Hermitian matrix explicitly equal to the noncommuting positive rank-one update
`K + τ uuᴴ`, then for every order-convex Borel-independent set of energies,
each multiplicity count is at most the other plus one.  The quantifiers and
normalization are exactly source-independent: `τ ≥ 0`, no commutativity, no
randomness, and no PSSS assumption. -/
theorem eigenCount_rankOne_interlacing {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K Kτ : HermitianMatrix ι) (u : ι → ℂ) {τ : ℝ}
    (hτ : 0 ≤ τ)
    (hKτ : Kτ.1 = K.1 + (τ : ℂ) • Matrix.vecMulVec u (star u))
    (s : Set ℝ) (hs : s.OrdConnected) :
    eigenCount K s ≤ eigenCount Kτ s + 1 ∧
      eigenCount Kτ s ≤ eigenCount K s + 1 := by
  let ue : EuclideanSpace ℂ ι := WithLp.toLp 2 u
  have hKτ' : (Kτ : Matrix ι ι ℂ) = K.1 + (τ : ℂ) •
      Matrix.vecMulVec (WithLp.ofLp ue) (star (WithLp.ofLp ue)) := by
    simpa [ue] using hKτ
  simpa only [eigenCount_def] using
    finiteOrderedCount_interlacing (orderedEigenvalue K)
      (orderedEigenvalue Kτ) (orderedEigenvalue_mono K)
      (orderedEigenvalue_mono Kτ)
      (orderedEigenvalue_rankOne_same_le K Kτ ue τ hτ hKτ')
      (orderedEigenvalue_rankOne_cast_le_succ K Kτ ue τ hKτ') s hs

end PSSSNative.BlockBand
