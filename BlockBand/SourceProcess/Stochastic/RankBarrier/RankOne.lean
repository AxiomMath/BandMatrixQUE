module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Rank-one perturbations of minors

The near rows `L = PV` solve a left-linear equation and the far rows
`F = (1−P)V` a right-linear one. For the source noise both coefficients are rank one:
`P σ_a = w ⊗ L_{k·}` and `(1−P) σ_a = (F z) ⊗ L_{k·}` (`near_noise_eq`, `far_noise_eq`). Hence
every minor is
*affine* along the noise line, with slope a combination of minors of the same size:

* `det_add_rankOne` (matrix determinant lemma, no invertibility):
  `det (A + u vᵀ) = det A + ∑_i u_i det (A with row i := v)`;
* `det_rowPerturb_submatrix`: `det (L + t w ⊗ L_{k·})_{f,g} = det L_{f,g} + t ∑_i w_{f i} det L_{f[i↦k],g}`;
* `det_colPerturb_submatrix`:
  `det (F + t (F z) ⊗ y)_{f,g} = det F_{f,g} + t ∑_i y_{g i} ∑_m z_m det F_{f,g[i↦m]}`.
Pure algebra over a commutative ring.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Finset

variable {R : Type*} [CommRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Adding multiples of row `j` to the rows in `s ∌ j` does not change the determinant. -/
theorem det_addRowMultiples (B : Matrix n n R) (j : n) (u : n → R) (s : Finset n)
    (hj : j ∉ s) :
    det (of fun i l => if i ∈ s then B i l + u i * B j l else B i l) = det B := by
  induction s using Finset.induction_on with
  | empty => congr 1
  | insert i s hi ih =>
    have hij : i ≠ j := fun h => hj (h ▸ Finset.mem_insert_self i s)
    have hj' : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
    set Bs : Matrix n n R := of fun i l => if i ∈ s then B i l + u i * B j l else B i l
    have hBi : Bs i = B i := by funext l; simp [Bs, hi]
    have hBj : Bs j = B j := by funext l; simp [Bs, hj']
    have hM : (of fun i' l => if i' ∈ insert i s then B i' l + u i' * B j l else B i' l) =
        Bs.updateRow i (Bs i + u i • Bs j) := by
      ext a l
      by_cases ha : a = i
      · subst ha; simp [Bs, hBi, hBj, updateRow_apply, hi]
      · simp [Bs, updateRow_apply, ha]
    rw [hM, det_updateRow_add_smul_self Bs hij, ih hj']

/-- **Matrix determinant lemma, adjugate-free row form.** -/
theorem det_add_rankOne (A : Matrix n n R) (u v : n → R) :
    det (A + of fun i j => u i * v j) = det A + ∑ i, u i * det (A.updateRow i v) := by
  have key : ∀ s : Finset n, det (of fun i l => if i ∈ s then A i l + u i * v l else A i l) =
      det A + ∑ i ∈ s, u i * det (A.updateRow i v) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp; congr 1
    | insert j s hj ih =>
      set As : Matrix n n R := of fun i l => if i ∈ s then A i l + u i * v l else A i l
      have hAj : As j = A j := by funext l; simp [As, hj]
      have hM : (of fun i l => if i ∈ insert j s then A i l + u i * v l else A i l) =
          As.updateRow j (A j + u j • v) := by
        ext a l
        by_cases ha : a = j
        · subst ha; simp [As, updateRow_apply]
        · simp [As, updateRow_apply, ha]
      have hrow : det (As.updateRow j v) = det (A.updateRow j v) := by
        have h := det_addRowMultiples (A.updateRow j v) j u s hj
        rw [← h]
        congr 1
        ext a l
        by_cases ha : a = j
        · subst ha; simp [As, updateRow_apply, hj]
        · simp [As, updateRow_apply, ha]
      rw [hM, det_updateRow_add, det_updateRow_smul, ← hAj, updateRow_eq_self, hrow, ih,
        Finset.sum_insert hj]
      ring
  have h := key Finset.univ
  simp only [Finset.mem_univ, ite_true] at h
  rw [← h]
  congr 1

/-- **Matrix determinant lemma, column form.** -/
theorem det_add_rankOne_col (A : Matrix n n R) (u v : n → R) :
    det (A + of fun i j => u i * v j) = det A + ∑ j, v j * det (A.updateCol j u) := by
  rw [← det_transpose, transpose_add]
  have : (of fun i j => u i * v j)ᵀ = of fun i j => v i * u j := by
    ext a b; simp [mul_comm]
  rw [this, det_add_rankOne, det_transpose]
  simp_rw [updateRow_transpose, det_transpose]

/-- Linearity of `det` in one column, over a finite sum. -/
theorem det_updateCol_finsetSum {β : Type*} (A : Matrix n n R) (j : n) (s : Finset β)
    (a : β → R) (x : β → n → R) :
    det (A.updateCol j (∑ b ∈ s, a b • x b)) = ∑ b ∈ s, a b * det (A.updateCol j (x b)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using det_updateCol_smul A j 0 0
  | insert b s hb ih => rw [Finset.sum_insert hb, det_updateCol_add, det_updateCol_smul, ih,
      Finset.sum_insert hb]

variable {ι c : Type*} {k : ℕ}

/-- Row perturbation `L + t (w ⊗ L_{k₀·})` of a minor `det L_{f,g}`. -/
theorem det_rowPerturb_submatrix (L : Matrix ι c R) (w : ι → R) (k0 : ι) (t : R)
    (f : Fin k → ι) (g : Fin k → c) :
    det ((L + of fun l m => t * w l * L k0 m).submatrix f g) =
      det (L.submatrix f g) +
        t * ∑ i, w (f i) * det (L.submatrix (Function.update f i k0) g) := by
  have hM : (L + of fun l m => t * w l * L k0 m).submatrix f g =
      L.submatrix f g + of fun i j => (t * w (f i)) * (fun j => L k0 (g j)) j := by
    ext a b; simp
  rw [hM, det_add_rankOne, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hU : (L.submatrix f g).updateRow i (fun j => L k0 (g j)) =
      L.submatrix (Function.update f i k0) g := by
    ext a b
    by_cases ha : a = i
    · subst ha; simp [updateRow_apply]
    · simp [updateRow_apply, ha]
  rw [hU]
  ring

/-- Column perturbation `F + t ((F z) ⊗ y)` of a minor `det F_{f,g}`. -/
theorem det_colPerturb_submatrix [Fintype c] (F : Matrix ι c R) (z y : c → R) (t : R)
    (f : Fin k → ι) (g : Fin k → c) :
    det ((F + of fun l m => t * (F *ᵥ z) l * y m).submatrix f g) =
      det (F.submatrix f g) +
        t * ∑ i, y (g i) * ∑ m, z m * det (F.submatrix f (Function.update g i m)) := by
  have hM : (F + of fun l m => t * (F *ᵥ z) l * y m).submatrix f g =
      F.submatrix f g + of fun a b => (fun a => t * (F *ᵥ z) (f a)) a * y (g b) := by
    ext a b; simp
  rw [hM, det_add_rankOne_col, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : (fun a => t * (F *ᵥ z) (f a)) =
      (∑ m, (t * z m) • (fun a => F (f a) m) : Fin k → R) := by
    funext a
    simp [mulVec, dotProduct, Finset.mul_sum, Finset.sum_apply, mul_comm, mul_left_comm]
  have hU : ∀ m, (F.submatrix f g).updateCol i (fun a => F (f a) m) =
      F.submatrix f (Function.update g i m) := by
    intro m
    ext a b
    by_cases hb : b = i
    · subst hb; simp
    · simp [hb]
  rw [hcol, det_updateCol_finsetSum]
  simp_rw [hU, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
