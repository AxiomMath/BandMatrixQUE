module

public import BlockBand.SourceProcess.EigenSel.Interface
public import BlockBand.SourceProcess.EigenSelConstruct.Sel

/-!
# A Borel-measurable sorted orthonormal eigenbasis

Proves `BlockBand.SourceProcess.EigenSel.MeasurableEigenSelection` with the selection `eigSel`.
Invariant `Good A k`: after `k` steps the vectors `0, …, k-1` are unit eigenvectors
for `eigenvalues₀`, pairwise orthogonal, and the remaining slots are `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSelConstruct
open Matrix MeasureTheory BlockBand.SourceProcess.ModelExist

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The invariant after `k` selection steps. -/
def Good {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) (W : Fin (Fintype.card n) → n → ℂ) :
    Prop :=
  (∀ j : Fin (Fintype.card n), k ≤ j.val → W j = 0) ∧
    (∀ j : Fin (Fintype.card n), j.val < k →
      A *ᵥ W j = ((hA.eigenvalues₀ j : ℝ) : ℂ) • W j ∧ star (W j) ⬝ᵥ W j = 1) ∧
    ∀ i j, i ≠ j → star (W i) ⬝ᵥ W j = 0

/-- One selection step from a good state produces a unit eigenvector for `eigenvalues₀ j`,
orthogonal to every earlier vector. -/
theorem step_spec {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : Fin (Fintype.card n))
    {W : Fin (Fintype.card n) → n → ℂ} (hW : Good hA j.val W) :
    A *ᵥ step j A W = ((hA.eigenvalues₀ j : ℝ) : ℂ) • step j A W ∧
      star (step j A W) ⬝ᵥ step j A W = 1 ∧ ∀ l, star (W l) ⬝ᵥ step j A W = 0 := by
  obtain ⟨h0, h1, -⟩ := hW
  obtain ⟨w, hw0, hwA, hwperp⟩ := exists_eigvec_perp hA j W fun l hl => (h1 l hl).1
  set G := condMat j A W
  have hlam : lam j A = hA.eigenvalues₀ j := lam_eq hA j
  have hGw : G *ᵥ w = 0 := by
    refine condMat_mulVec_eq_zero.2 ⟨by rw [hlam]; exact hwA, fun l => ?_⟩
    by_cases hl : l < j
    · exact hwperp l hl
    · rw [h0 l (not_lt.1 hl), star_zero, zero_dotProduct]
  have hPw := specProj_mulVec_of G hGw
  have hex : ∃ i, cols (specProj G) i ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw0
    rw [← hPw]
    funext x
    have : ∀ y, specProj G x y = 0 := fun y => by
      have := congrFun (hall (Fintype.equivFin n y)) x
      simpa [cols] using this
    simp [Matrix.mulVec, dotProduct, this]
  obtain ⟨⟨i, c, hc⟩, hunit⟩ := firstNZ_spec _ _ hex
  have hcol : G *ᵥ cols (specProj G) i = 0 := by
    have h := mul_specProj G
    funext r
    have := congrFun (congrFun h r) ((Fintype.equivFin n).symm i)
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, cols] using this
  have hstep : G *ᵥ step j A W = 0 := by
    change G *ᵥ firstNZ _ (cols (specProj G)) = 0
    rw [hc, Matrix.mulVec_smul, hcol, smul_zero]
  obtain ⟨hA', hperp⟩ := condMat_mulVec_eq_zero.1 hstep
  rw [hlam] at hA'
  exact ⟨hA', hunit, hperp⟩

theorem good_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : Good hA 0 (vecs A 0) :=
  ⟨fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => by simp [vecs]⟩

theorem good_succ {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ)
    (hk : k + 1 ≤ Fintype.card n) (hW : Good hA k (vecs A k)) :
    Good hA (k + 1) (vecs A (k + 1)) := by
  set jk : Fin (Fintype.card n) := ⟨k, hk⟩
  obtain ⟨hu1, hu2, hu3⟩ := step_spec hA jk hW
  have hv : ∀ j : Fin (Fintype.card n),
      vecs A (k + 1) j = if j.val = k then step jk A (vecs A k) else vecs A k j := by
    intro j
    change (if j.val = k then step j A (vecs A k) else vecs A k j) = _
    by_cases hj : j.val = k
    · have : j = jk := Fin.ext hj
      rw [this]
    · rw [ite_eq_right hj, ite_eq_right hj]
  obtain ⟨h0, h1, h2⟩ := hW
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun i j hij => ?_⟩
  · rw [hv, ite_eq_right (by omega)]
    exact h0 j (by omega)
  · rw [hv]
    by_cases hjk : j.val = k
    · have : j = jk := Fin.ext hjk
      rw [ite_eq_left hjk, this]
      exact ⟨hu1, hu2⟩
    · rw [ite_eq_right hjk]
      exact h1 j (by omega)
  · rw [hv, hv]
    by_cases hi : i.val = k
    · have hj : ¬ j.val = k := fun hj => hij (Fin.ext (hi.trans hj.symm))
      rw [ite_eq_left hi, ite_eq_right hj, star_dotProduct, hu3 j, star_zero]
    · by_cases hj : j.val = k
      · rw [ite_eq_right hi, ite_eq_left hj]
        exact hu3 i
      · rw [ite_eq_right hi, ite_eq_right hj]
        exact h2 i j hij

theorem good_vecs {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (k : ℕ) → k ≤ Fintype.card n → Good hA k (vecs A k)
  | 0, _ => good_zero hA
  | k + 1, hk => good_succ hA k hk (good_vecs hA k (by omega))

/-- **A measurable sorted orthonormal eigenbasis exists.** -/
theorem measurableEigenSelection_holds :
    BlockBand.SourceProcess.EigenSel.MeasurableEigenSelection := by
  intro n _ _
  refine ⟨eigSel, measurable_eigSel, fun A hA => ?_⟩
  obtain ⟨-, h1, h2⟩ := good_vecs hA (Fintype.card n) le_rfl
  have hofA : Matrix.of A = A := rfl
  constructor
  · ext i j
    have e : ((Matrix.of (eigSel A))ᴴ * Matrix.of (eigSel A)) i j =
        star (vecs A (Fintype.card n) i) ⬝ᵥ vecs A (Fintype.card n) j := by
      simp [Matrix.mul_apply, dotProduct, eigSel, hofA]
    rw [e, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl]
      exact (h1 i i.2).2
    · rw [ite_eq_right hij]
      exact h2 i j hij
  · ext x k
    have hk := congrFun (h1 k k.2).1 x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hk
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.of_apply, eigSel, hofA]
    rw [hk, mul_comm]

end BlockBand.SourceProcess.EigenSelConstruct
