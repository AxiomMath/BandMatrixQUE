module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Existence of a fresh orthogonal eigenvector

Given eigenvectors of a Hermitian matrix for the first `j` sorted eigenvalues, some nonzero
eigenvector for the `j`-th eigenvalue is orthogonal to all of them (`exists_eigvec_perp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSelConstruct
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Eigenvectors of a Hermitian matrix for distinct (real) eigenvalues are orthogonal. -/
theorem star_dotProduct_eq_zero_of_ne {A : Matrix n n ℂ} (hA : A.IsHermitian) {x y : n → ℂ}
    {a b : ℝ} (hx : A *ᵥ x = (a : ℂ) • x) (hy : A *ᵥ y = (b : ℂ) • y) (hab : a ≠ b) :
    star x ⬝ᵥ y = 0 := by
  have h1 : star x ⬝ᵥ (A *ᵥ y) = (b : ℂ) * (star x ⬝ᵥ y) := by
    rw [hy, dotProduct_smul, smul_eq_mul]
  have h2 : star x ⬝ᵥ (A *ᵥ y) = (a : ℂ) * (star x ⬝ᵥ y) := by
    rw [dotProduct_mulVec]
    have : star x ᵥ* A = star (A *ᵥ x) := by
      rw [star_mulVec, hA.eq]
    rw [this, hx, star_smul, smul_dotProduct, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  have h3 : ((b : ℂ) - a) * (star x ⬝ᵥ y) = 0 := by rw [sub_mul, ← h1, ← h2, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.1 h)).symm hab
  · exact h

/-- The multiplicity of `μ` among `eigenvalues` equals that among `eigenvalues₀`. -/
theorem card_eigenvalues_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) (μ : ℝ) :
    (Finset.univ.filter fun i : n => hA.eigenvalues i = μ).card =
      (Finset.univ.filter fun l : Fin (Fintype.card n) => hA.eigenvalues₀ l = μ).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm.subtypeEquiv fun _ => Iff.rfl)

/-- **Existence of a fresh eigenvector.** Given eigenvectors `v l` (`l < j`) for the eigenvalues
`eigenvalues₀ l`, some nonzero eigenvector for `eigenvalues₀ j` is orthogonal to all of them. -/
theorem exists_eigvec_perp {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : Fin (Fintype.card n))
    (v : Fin (Fintype.card n) → n → ℂ)
    (hv : ∀ l < j, A *ᵥ v l = ((hA.eigenvalues₀ l : ℝ) : ℂ) • v l) :
    ∃ w : n → ℂ, w ≠ 0 ∧ A *ᵥ w = ((hA.eigenvalues₀ j : ℝ) : ℂ) • w ∧
      ∀ l < j, star (v l) ⬝ᵥ w = 0 := by
  set μ := hA.eigenvalues₀ j
  set b := hA.eigenvectorBasis
  set S : Finset n := Finset.univ.filter fun i => hA.eigenvalues i = μ
  set J : Finset (Fin (Fintype.card n)) :=
    Finset.univ.filter fun l => l < j ∧ hA.eigenvalues₀ l = μ
  have hcard : J.card < S.card := by
    rw [card_eigenvalues_eq hA μ]
    refine Finset.card_lt_card ⟨fun l hl => ?_, fun hsub => ?_⟩
    · simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.2
    · have : j ∈ J := hsub (by simp [μ])
      simp [J] at this
  set M : Matrix J S ℂ := fun l i => star (v l.1) ⬝ᵥ ⇑(b i.1)
  have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe]
    exact hcard
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  set wE : EuclideanSpace ℂ n := ∑ i : S, c i • b i.1
  have hwcoe : ⇑wE = ∑ i : S, c i • ⇑(b i.1) := by
    simp [wE]
  have hS : ∀ i : S, hA.eigenvalues i.1 = μ := fun i => (Finset.mem_filter.1 i.2).2
  refine ⟨⇑wE, ?_, ?_, ?_⟩
  · intro hw
    have hwE : wE = 0 := by
      apply WithLp.ofLp_injective
      exact hw
    have hli : LinearIndependent ℂ fun i : S => b i.1 :=
      b.orthonormal.linearIndependent.comp _ Subtype.val_injective
    exact hc0 (funext fun i => Fintype.linearIndependent_iff.1 hli c hwE i)
  · rw [hwcoe, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, hS i, smul_comm, Complex.coe_smul]
  · intro l hl
    by_cases hlμ : hA.eigenvalues₀ l = μ
    · have hlJ : l ∈ J := by simp [J, hl, hlμ]
      have := congrFun hc ⟨l, hlJ⟩
      rw [hwcoe, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      simpa [Matrix.mulVec, dotProduct, M, mul_comm] using this
    · have hw : A *ᵥ ⇑wE = (μ : ℂ) • ⇑wE := by
        rw [hwcoe, Matrix.mulVec_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, hS i, smul_comm, Complex.coe_smul]
      exact star_dotProduct_eq_zero_of_ne hA (hv l hl) hw hlμ

end BlockBand.SourceProcess.EigenSelConstruct
