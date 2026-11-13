module

public import BlockBand.External.CEH.SourceModel
public import BlockBand.Model.Construction.OrderedProjector

/-!
# Measurable spectral projectors onto eigenvalue clusters

The generalized Lagrange product `P_μ(H)` over the increasing eigenvalues of a Hermitian matrix
`H` is the spectral projector onto the `μ`-eigenspace; `H ↦ P_{f(H)}(H)` is Borel measurable for
Borel `f`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH

open Matrix
open BlockBand.External.CEH
open BlockBand.Foundations.Spectral

namespace Eigenpairs

variable {N : ℕ}

/-- Increasing eigenvalues indexed by `Fin N` (`increasingEigenvalue`, multiplicities kept). -/
def eigval (H : SourceHermitian N) (i : Fin N) : ℝ :=
  increasingEigenvalue H.2 (Fin.cast (Fintype.card_fin N).symm i)

/-- The (non-measurable) increasing orthonormal eigenbasis, indexed by `Fin N`.
Used only inside proofs.
-/
def eigbasis (H : SourceHermitian N) (i : Fin N) : Fin N → ℂ :=
  increasingEigenvector H.2 (Fin.cast (Fintype.card_fin N).symm i)

theorem eigval_monotone (H : SourceHermitian N) : Monotone (eigval H) := by
  intro a b hab
  exact increasingEigenvalue_monotone H.2 ((Fin.cast_le_cast _).mpr hab)

theorem measurable_eigval (i : Fin N) : Measurable (fun H : SourceHermitian N => eigval H i) :=
  BlockBand.Model.Construction.measurable_increasingEigenvalue (ι := Fin N) _

theorem mulVec_eigbasis (H : SourceHermitian N) (r : Fin N) :
    H.1 *ᵥ eigbasis H r = (eigval H r : ℂ) • eigbasis H r :=
  mulVec_increasingEigenvector H.2 _

theorem eigbasis_orthonormal (H : SourceHermitian N) (a b : Fin N) :
    star (eigbasis H a) ⬝ᵥ eigbasis H b = if a = b then 1 else 0 := by
  have h := increasingEigenvector_orthonormal H.2 (Fin.cast (Fintype.card_fin N).symm a)
    (Fin.cast (Fintype.card_fin N).symm b)
  simp only [Fin.cast_inj] at h
  rw [← h]
  rfl

theorem matrix_eq_of_eigbasis (H : SourceHermitian N) (P Q : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ r, P *ᵥ eigbasis H r = Q *ᵥ eigbasis H r) : P = Q := by
  apply BlockBand.Model.Construction.matrix_eq_of_mulVec_increasingEigenvector_eq H P Q
  intro r
  have := h (Fin.cast (Fintype.card_fin N) r)
  simpa [eigbasis] using this

/-- One generalized Lagrange factor. -/
def clusterFactor (H : SourceHermitian N) (μ : ℝ) (j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  if eigval H j = μ then 1 else
    (((μ - eigval H j : ℝ) : ℂ)⁻¹) • (H.1 - (eigval H j : ℂ) • 1)

/-- The generalized Lagrange projector onto the `μ`-eigenspace. -/
def clusterProjector (H : SourceHermitian N) (μ : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ((List.finRange N).map (clusterFactor H μ)).prod

/-- Scalar action of one factor on the eigenline `u_r`. -/
def clusterScalar (H : SourceHermitian N) (μ : ℝ) (j r : Fin N) : ℂ :=
  if eigval H j = μ then 1 else
    (((μ - eigval H j : ℝ) : ℂ)⁻¹) * ((eigval H r : ℂ) - (eigval H j : ℂ))

theorem clusterFactor_mulVec (H : SourceHermitian N) (μ : ℝ) (j r : Fin N) :
    clusterFactor H μ j *ᵥ eigbasis H r = clusterScalar H μ j r • eigbasis H r := by
  by_cases hj : eigval H j = μ
  · simp [clusterFactor, clusterScalar, hj, Matrix.one_mulVec]
  · simp only [clusterFactor, clusterScalar, hj, ite_false, Matrix.smul_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, mulVec_eigbasis, ← sub_smul, smul_smul]

theorem list_prod_clusterFactor_mulVec (H : SourceHermitian N) (μ : ℝ) (r : Fin N)
    (l : List (Fin N)) :
    (l.map (clusterFactor H μ)).prod *ᵥ eigbasis H r =
      (l.map (fun j => clusterScalar H μ j r)).prod • eigbasis H r := by
  induction l with
  | nil => simp [Matrix.one_mulVec]
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec]
    rw [ih, Matrix.mulVec_smul, clusterFactor_mulVec, smul_smul, mul_comm]

theorem clusterScalar_prod (H : SourceHermitian N) (μ : ℝ) (r : Fin N) :
    ((List.finRange N).map (fun j => clusterScalar H μ j r)).prod =
      if eigval H r = μ then 1 else 0 := by
  by_cases hr : eigval H r = μ
  · simp only [hr, ite_true]
    apply List.prod_eq_one
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    by_cases hj : eigval H j = μ
    · simp [clusterScalar, hj]
    · have hne : ((μ - eigval H j : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr (Ne.symm hj)
      simp only [clusterScalar, hj, ite_false, hr]
      rw [← Complex.ofReal_sub]
      exact inv_mul_cancel₀ hne
  · simp only [hr, ite_false]
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨r, List.mem_finRange r, ?_⟩
    simp [clusterScalar, hr]

theorem clusterProjector_mulVec (H : SourceHermitian N) (μ : ℝ) (r : Fin N) :
    clusterProjector H μ *ᵥ eigbasis H r =
      (if eigval H r = μ then (1 : ℂ) else 0) • eigbasis H r := by
  rw [clusterProjector, list_prod_clusterFactor_mulVec, clusterScalar_prod]

/-- `H P_μ = μ P_μ`: the range of `P_μ` lies in the `μ`-eigenspace. -/
theorem mul_clusterProjector (H : SourceHermitian N) (μ : ℝ) :
    H.1 * clusterProjector H μ = (μ : ℂ) • clusterProjector H μ := by
  apply matrix_eq_of_eigbasis H
  intro r
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, clusterProjector_mulVec, Matrix.mulVec_smul,
    mulVec_eigbasis]
  by_cases hr : eigval H r = μ
  · simp [hr]
  · simp [hr]

/-- Each factor is Borel measurable in `H` when `μ = f H` is. -/
theorem measurable_clusterFactor (f : SourceHermitian N → ℝ) (hf : Measurable f) (j : Fin N) :
    Measurable (fun H => clusterFactor H (f H) j) := by
  unfold clusterFactor
  refine Measurable.ite (measurableSet_eq_fun (measurable_eigval j) hf) measurable_const ?_
  apply measurable_pi_iff.mpr
  intro x
  apply measurable_pi_iff.mpr
  intro y
  change Measurable (fun H : SourceHermitian N =>
    (((f H - eigval H j : ℝ) : ℂ)⁻¹) *
      (H.1 x y - (eigval H j : ℂ) * (1 : Matrix (Fin N) (Fin N) ℂ) x y))
  have hd : Measurable (fun H : SourceHermitian N => ((f H - eigval H j : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (hf.sub (measurable_eigval j))
  have hj := Complex.measurable_ofReal.comp (measurable_eigval (N := N) j)
  have he : Measurable (fun H : SourceHermitian N => H.1 x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_subtype_coe)
  exact hd.inv.mul (he.sub (hj.mul measurable_const))

theorem measurable_list_prod_clusterFactor (f : SourceHermitian N → ℝ) (hf : Measurable f)
    (l : List (Fin N)) :
    Measurable (fun H => (l.map (clusterFactor H (f H))).prod) := by
  induction l with
  | nil => exact measurable_const
  | cons j l ih =>
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro y
    change Measurable (fun H : SourceHermitian N =>
      ∑ k, clusterFactor H (f H) j x k * (l.map (clusterFactor H (f H))).prod k y)
    apply Finset.measurable_sum
    intro k _
    exact ((measurable_pi_apply k).comp ((measurable_pi_apply x).comp
      (measurable_clusterFactor f hf j))).mul
        ((measurable_pi_apply y).comp ((measurable_pi_apply k).comp ih))

/-- `H ↦ P_{f(H)}(H)` is Borel measurable for Borel `f`. -/
theorem measurable_clusterProjector (f : SourceHermitian N → ℝ) (hf : Measurable f) :
    Measurable (fun H => clusterProjector H (f H)) :=
  measurable_list_prod_clusterFactor f hf _

end Eigenpairs

end BlockBand.Native.CEH
