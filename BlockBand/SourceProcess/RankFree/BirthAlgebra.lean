module

public import BlockBand.SourceProcess.RankFree.NoiseAlgebra
public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# Algebra of shared births

Births are single-column matrices `birthMat j v` (column `j` equal to `v`). This file computes
their inner products and norms, the trace of a frame plus pairwise orthogonal births
(`norm_sq_add_sum_orth`), and the diagonal projection `nonBirthProj` onto the non-birth columns,
which kills the births (`birthMat_mul_nonBirthProj`, `frameBirthJump_mul_nonBirthProj`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [Fintype c] [DecidableEq c]

/-- The matrix with column `j` equal to `v` and all other columns zero. -/
def birthMat (j : c) (v : ι → ℂ) : Matrix ι c ℂ := Matrix.of fun i l => if l = j then v i else 0

omit [Fintype ι] [Fintype c] in
theorem frameBirthJump_eq {Ω : Type*} {nb : ℕ} (τ : Fin nb → Ω → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω) :
    frameBirthJump τ col w t x = ∑ k, if τ k x ≤ t then birthMat (col k) (w k x) else 0 := rfl

theorem reInner_birthMat (j : c) (v : ι → ℂ) (Y : Matrix ι c ℂ) :
    reInner (birthMat j v) Y = (∑ i, star (v i) * Y i j).re := by
  rw [reInner_apply]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, birthMat,
    Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [apply_ite]

theorem norm_sq_birthMat (j : c) (v : ι → ℂ) : ‖birthMat j v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [frob_sq]
  simp [birthMat, apply_ite]

omit [Fintype ι] [Fintype c] in
theorem birthMat_zero (j : c) : birthMat j (0 : ι → ℂ) = 0 := by
  ext i l; simp [birthMat]

theorem reInner_birthMat_of_ne {j l : c} (h : j ≠ l) (u v : ι → ℂ) :
    reInner (birthMat j u) (birthMat l v) = 0 := by
  rw [reInner_birthMat]
  simp [birthMat, h]

omit [DecidableEq c] in
theorem norm_sq_add (x y : Matrix ι c ℂ) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * reInner y x + ‖y‖ ^ 2 := by
  simp only [← reInner_self, map_add, _root_.add_apply, reInner_comm x y]
  ring

omit [DecidableEq c] in
/-- **Trace of a frame plus pairwise orthogonal births.** -/
theorem norm_sq_add_sum_orth {κ : Type*} (s : Finset κ) (Y : Matrix ι c ℂ)
    (a : κ → Matrix ι c ℂ) (h : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → reInner (a k) (a l) = 0) :
    ‖Y + ∑ k ∈ s, a k‖ ^ 2 = ‖Y‖ ^ 2 + ∑ k ∈ s, (2 * reInner (a k) Y + ‖a k‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k₀ s hk₀ ih =>
      have ih' := ih fun k hk l hl hkl => h k (Finset.mem_insert_of_mem hk) l
        (Finset.mem_insert_of_mem hl) hkl
      have horth : reInner (a k₀) (∑ l ∈ s, a l) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun l hl => h k₀ (Finset.mem_insert_self _ _) l
          (Finset.mem_insert_of_mem hl) fun he => hk₀ (he ▸ hl)
      rw [Finset.sum_insert hk₀, Finset.sum_insert hk₀,
        show Y + (a k₀ + ∑ l ∈ s, a l) = (Y + ∑ l ∈ s, a l) + a k₀ by abel, norm_sq_add, ih',
        map_add, horth, add_zero]
      ring

/-- The diagonal projection onto the non-birth columns. -/
def nonBirthProj {nb : ℕ} (col : Fin nb → c) : Matrix c c ℂ :=
  Matrix.diagonal fun j => if ∃ k, col k = j then 0 else 1

variable {nb : ℕ} {col : Fin nb → c}

omit [Fintype ι] in
theorem birthMat_mul_nonBirthProj (k : Fin nb) (v : ι → ℂ) :
    birthMat (col k) v * nonBirthProj col = 0 := by
  ext i l
  simp only [nonBirthProj, mul_diagonal, birthMat, Matrix.of_apply, Matrix.zero_apply]
  by_cases h1 : l = col k
  · subst h1; simp [show ∃ k', col k' = col k from ⟨k, rfl⟩]
  · simp [h1]

omit [Fintype ι] in
theorem frameBirthJump_mul_nonBirthProj {Ω : Type*} (τ : Fin nb → Ω → ℝ≥0)
    (w : Fin nb → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω) :
    frameBirthJump τ col w t x * nonBirthProj col = 0 := by
  rw [frameBirthJump_eq, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs
  · exact birthMat_mul_nonBirthProj k _
  · exact Matrix.zero_mul _

omit [Fintype ι] in
theorem mul_nonBirthProj_of_col {V : Matrix ι c ℂ} (hV : ∀ k i, V i (col k) = 0) :
    V * nonBirthProj col = V := by
  ext i l
  simp only [nonBirthProj, mul_diagonal]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simp [hV k i]
  · simp

omit [Fintype c] in
theorem nonBirthProj_conjTranspose : (nonBirthProj col)ᴴ = nonBirthProj col := by
  rw [nonBirthProj, diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : ∃ k, col k = j <;> simp [h]

theorem nonBirthProj_mul_mul {D : Matrix c c ℂ} (hD : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) :
    nonBirthProj col * D * nonBirthProj col = D := by
  ext i j
  simp only [nonBirthProj, mul_diagonal, diagonal_mul]
  split_ifs with h1 h2 h2
  · obtain ⟨k, rfl⟩ := h2; simp [(hD k _).2]
  · obtain ⟨k, rfl⟩ := h1; simp [(hD k _).1]
  · obtain ⟨k, rfl⟩ := h2; simp [(hD k _).2]
  · simp

omit [Fintype ι] in
theorem gramProjection_mul_nonBirthProj {D : Matrix c c ℂ}
    (hD : ∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) :
    gramProjection P (V * nonBirthProj col) D = gramProjection P V D := by
  rw [gramProjection, gramProjection, conjTranspose_mul, nonBirthProj_conjTranspose]
  congr 1
  conv_rhs => rw [← nonBirthProj_mul_mul hD]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] in
theorem mul_single_diag_apply (Y : Matrix ι c ℂ) (j : c) (i : ι) (l : c) :
    (Y * Matrix.single j j (1 : ℂ)) i l = if l = j then Y i j else 0 := by
  by_cases h : l = j
  · subst h; simp [mul_single_apply_same]
  · simp only [h, ite_false]
    exact mul_single_apply_of_ne _ _ _ _ _ h Y

omit [Fintype ι] in
theorem birthMat_mul_single (j l : c) (v : ι → ℂ) :
    birthMat l v * Matrix.single j j (1 : ℂ) = if l = j then birthMat j v else 0 := by
  ext i m
  rw [mul_single_diag_apply]
  by_cases hl : l = j
  · subst hl
    by_cases hm : m = l <;> simp [hm, birthMat]
  · simp [hl, birthMat, Ne.symm hl]

end BlockBand.SourceProcess.RankFree
