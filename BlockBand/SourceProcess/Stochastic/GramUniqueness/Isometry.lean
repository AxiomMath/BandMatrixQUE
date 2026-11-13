module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Constructions
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Isometric compression onto a subspace spanned by matrix columns

For a subspace `S ⊆ ℂ^ι` with orthonormal basis `b_1, …, b_m`, the matrix `J` with columns `b_k`
satisfies `JᴴJ = 1` and `J Jᴴ A = A` whenever the columns of `A` lie in `S` (`ColsIn S A`).
`ColsIn S` is closed under right multiplication and addition, and under left multiplication by a
matrix `P` whose action leaves `S` invariant. Used to compress a constrained
frame onto `span(V, PV)`, of dimension `≤ 2|c|`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix

variable {ι : Type*} [Fintype ι]

/-- The `j`-th column of `A` as a vector of `ℂ^ι`. -/
def colVec {κ : Type*} (A : Matrix ι κ ℂ) (j : κ) : EuclideanSpace ℂ ι := WithLp.toLp 2 fun i => A i j

/-- All columns of `A` lie in `S`. -/
def ColsIn (S : Submodule ℂ (EuclideanSpace ℂ ι)) {κ : Type*} (A : Matrix ι κ ℂ) : Prop :=
  ∀ j, colVec A j ∈ S

omit [Fintype ι] in
theorem colVec_mul {κ κ' : Type*} [Fintype κ] (A : Matrix ι κ ℂ) (X : Matrix κ κ' ℂ) (j : κ') :
    colVec (A * X) j = ∑ k, X k j • colVec A k := by
  ext i
  simp only [colVec, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

omit [Fintype ι] in
theorem ColsIn.mul {S : Submodule ℂ (EuclideanSpace ℂ ι)} {κ κ' : Type*} [Fintype κ]
    {A : Matrix ι κ ℂ} (h : ColsIn S A) (X : Matrix κ κ' ℂ) : ColsIn S (A * X) := fun j => by
  rw [colVec_mul]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h k)

omit [Fintype ι] in
theorem ColsIn.add {S : Submodule ℂ (EuclideanSpace ℂ ι)} {κ : Type*} {A B : Matrix ι κ ℂ}
    (hA : ColsIn S A) (hB : ColsIn S B) : ColsIn S (A + B) := fun j => by
  have : colVec (A + B) j = colVec A j + colVec B j := by
    ext i; simp [colVec]
  rw [this]
  exact Submodule.add_mem _ (hA j) (hB j)

/-- `P` maps `S` into itself. -/
def MatInvariant (S : Submodule ℂ (EuclideanSpace ℂ ι)) (P : Matrix ι ι ℂ) : Prop :=
  ∀ x ∈ S, WithLp.toLp 2 (P *ᵥ WithLp.ofLp x) ∈ S

theorem ColsIn.left_mul {S : Submodule ℂ (EuclideanSpace ℂ ι)} {P : Matrix ι ι ℂ}
    (hP : MatInvariant S P) {κ : Type*} {A : Matrix ι κ ℂ} (h : ColsIn S A) :
    ColsIn S (P * A) := fun j => by
  have : colVec (P * A) j = WithLp.toLp 2 (P *ᵥ WithLp.ofLp (colVec A j)) := by
    ext i; simp [colVec, mul_apply, mulVec, dotProduct]
  rw [this]
  exact hP _ (h j)

/-- Invariance can be checked on spanning vectors. -/
theorem matInvariant_span {s : Set (EuclideanSpace ℂ ι)} {P : Matrix ι ι ℂ}
    (h : ∀ x ∈ s, WithLp.toLp 2 (P *ᵥ WithLp.ofLp x) ∈ Submodule.span ℂ s) :
    MatInvariant (Submodule.span ℂ s) P := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simpa [mulVec_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    simpa [mulVec_smul] using Submodule.smul_mem _ a hx

variable (S : Submodule ℂ (EuclideanSpace ℂ ι))

/-- The matrix whose columns are the standard orthonormal basis of `S`. -/
def basisMatrix : Matrix ι (Fin (Module.finrank ℂ S)) ℂ :=
  fun i k => WithLp.ofLp ((stdOrthonormalBasis ℂ S k : S) : EuclideanSpace ℂ ι) i

theorem basisMatrix_conjTranspose_mul : (basisMatrix S)ᴴ * basisMatrix S = 1 := by
  ext k l
  have h := orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ S).orthonormal k l
  rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [mul_apply, one_apply, ← h]
  simp only [basisMatrix, conjTranspose_apply, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem colsIn_basisMatrix : ColsIn S (basisMatrix S) := fun k => by
  have : colVec (basisMatrix S) k = ((stdOrthonormalBasis ℂ S k : S) : EuclideanSpace ℂ ι) := by
    ext i; rfl
  rw [this]
  exact (stdOrthonormalBasis ℂ S k).2

theorem basisMatrix_mul_conjTranspose_mul {κ : Type*} {A : Matrix ι κ ℂ} (hA : ColsIn S A) :
    basisMatrix S * ((basisMatrix S)ᴴ * A) = A := by
  ext i j
  have h := congrArg (fun x : S => WithLp.ofLp (x : EuclideanSpace ℂ ι) i)
    ((stdOrthonormalBasis ℂ S).sum_repr' ⟨colVec A j, hA j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_inner,
    EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [mul_apply]
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, mul_apply]
  simp only [basisMatrix, conjTranspose_apply, dotProduct, colVec, Pi.star_apply]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end BlockBand.SourceProcess.Stochastic.GramUniqueness
