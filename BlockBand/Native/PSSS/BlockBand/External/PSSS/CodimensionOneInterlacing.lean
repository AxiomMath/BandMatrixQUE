module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.RankOneInterlacing
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Codimension-one rank-one interlacing

The key input is an explicit dimension argument: a `(k+2)`-plane meets the
kernel of one linear functional in dimension at least `k+1`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace PSSSNative.BlockBand.PSSS

open scoped ComplexConjugate Matrix

universe u v

/-- Kernel of the inner-product functional `x ↦ ⟪u,x⟫`. -/
def innerKernel {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : E) : Submodule ℂ E :=
  (innerSL ℂ u).toLinearMap.ker

@[simp] theorem mem_innerKernel_iff {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u x : E) :
    x ∈ innerKernel u ↔ inner ℂ u x = 0 := by
  simp [innerKernel]

/-- Intersecting a `d+1` dimensional subspace with one homogeneous linear
constraint leaves a subspace of dimension at least `d`. -/
theorem exists_submodule_le_inf_innerKernel_finrank_eq
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (V : Submodule ℂ E) (u : E) {d : ℕ}
    (hV : Module.finrank ℂ V = d + 1) :
    ∃ W : Submodule ℂ E, W ≤ V ⊓ innerKernel u ∧ Module.finrank ℂ W = d := by
  let f : V →ₗ[ℂ] ℂ :=
    (innerSL ℂ u).toLinearMap.comp V.subtype
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
      (LinearMap.ker f).ker_subtype).map'
        V.subtype V.ker_subtype
  refine ⟨Submodule.span ℂ (Set.range g), ?_, ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨i, rfl⟩
    refine ⟨(q i).val.property, ?_⟩
    change inner ℂ u ((q i : V) : E) = 0
    exact (q i).property
  · simpa [g] using finrank_span_eq_card hg

/-- Embed an index below `n-1` into `Fin n`. -/
def finPredCast {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k, by have := k.isLt; omega⟩

/-- The successor in `Fin n` of an index below `n-1`. -/
def finPredSucc {n : ℕ} (k : Fin (n - 1)) : Fin n :=
  ⟨k + 1, by have := k.isLt; omega⟩

/-- **Shifted-index rank-one interlacing, decreasing convention.**  The
`(k+1)`-st eigenvalue of a Hermitian rank-one perturbation is at most the
`k`-th eigenvalue of the unperturbed matrix.  No commutativity is assumed,
and this direction does not require a sign on `τ`. -/
theorem eigenvalues₀_rankOneShift_succ_le {ι : Type u}
    [Fintype ι] [DecidableEq ι]
    (K : HermitianMatrix ι) (u : EuclideanSpace ℂ ι) (τ : ℝ)
    (k : Fin (Fintype.card ι - 1)) :
    (rankOneShift K u τ).2.eigenvalues₀ (finPredSucc k) ≤
      K.2.eigenvalues₀ (finPredCast k) := by
  simp only [Matrix.IsHermitian.eigenvalues₀]
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr K.2
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (rankOneShift K u τ).2
  obtain ⟨V, hVdim, hVlow⟩ :=
    hS.exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace (finPredSucc k)
  have hVdim' : Module.finrank ℂ V = ((k : ℕ) + 1) + 1 := by
    simpa [finPredSucc] using hVdim
  obtain ⟨W, hWle, hWdim⟩ :=
    exists_submodule_le_inf_innerKernel_finrank_eq V u hVdim'
  obtain ⟨x, hxW, hxnorm, hxT⟩ :=
    hT.exists_unit_vector_re_inner_le_eigenvalue
      finrank_euclideanSpace (finPredCast k) W
        (by simpa [finPredCast] using hWdim)
  have hxV : x ∈ V := (hWle hxW).1
  have hxorth : inner ℂ u x = 0 :=
    (mem_innerKernel_iff u x).mp (hWle hxW).2
  have hquad :
      RCLike.re
          (inner ℂ
            (Matrix.toEuclideanLin
              (rankOneShift K u τ : Matrix ι ι ℂ) x) x) =
        RCLike.re (inner ℂ (Matrix.toEuclideanLin K.1 x) x) := by
    rw [toEuclideanLin_rankOneShift, LinearMap.add_apply,
      LinearMap.smul_apply, inner_add_left, map_add]
    simp [InnerProductSpace.rankOne_apply, hxorth]
  exact (hVlow x hxV hxnorm).trans (hquad.le.trans hxT)

end PSSSNative.BlockBand.PSSS
