module

public import BlockBand.Critical.Collar.Density.CondSchurWitnessPoly

/-!
# Conditional Schur identity: Witness

Part of the proof of the conditional Schur identity in the collar density lemma: the top
density, averaged first over `G`, is exactly `TΣ_F(0)T*`.

`det Γ ≠ 0` at the witness `A₁ = λI, A₂ = 0, B₁ = B₂ = I`, `λ ∉ spec(X₁₁ - X₁₂ + X₂₁ - X₂₂)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory Filter ProbabilityTheory
open BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate ComplexOrder ENNReal NNReal

variable {W : ℕ}

theorem csStar_dotProduct_self {ι : Type} [Fintype ι] (a : ι → ℂ) :
    star a ⬝ᵥ a = ((∑ i, ‖a i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast; ring

theorem eq_zero_of_sum_norm_sq_eq_zero {ι : Type} [Fintype ι] {a : ι → ℂ}
    (h : ∑ i, ‖a i‖ ^ 2 = 0) : a = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖a i‖)).1 h i (Finset.mem_univ i)
  simpa using this

/-- Kernel of the Gram matrix for Hermitian `D`: `Γv = 0 ⇒ B*v = 0 ∧ B*Dv = 0`. -/
theorem csGram_kernel {m n : Type} [Fintype m] [Fintype n] {D : Matrix m m ℂ}
    (hD : D.IsHermitian) (B : Matrix m n ℂ) {v : m → ℂ} (hv : csGram D B *ᵥ v = 0) :
    Bᴴ *ᵥ v = 0 ∧ Bᴴ *ᵥ (D *ᵥ v) = 0 := by
  set a := Bᴴ *ᵥ v
  set c := Bᴴ *ᵥ (D *ᵥ v)
  have hG : csGram D B *ᵥ v = B *ᵥ a + D *ᵥ (B *ᵥ c) := by
    unfold csGram
    simp only [add_mulVec, ← mulVec_mulVec, a, c]
  have h1 : star v ⬝ᵥ (B *ᵥ a) = star a ⬝ᵥ a := by
    rw [dotProduct_mulVec]
    congr 1
    rw [star_mulVec, conjTranspose_conjTranspose]
  have h2 : star v ⬝ᵥ (D *ᵥ (B *ᵥ c)) = star c ⬝ᵥ c := by
    rw [dotProduct_mulVec, dotProduct_mulVec]
    congr 1
    rw [star_mulVec, star_mulVec, conjTranspose_conjTranspose, hD.eq]
  have h0 : star v ⬝ᵥ (csGram D B *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  rw [hG, dotProduct_add, h1, h2, csStar_dotProduct_self, csStar_dotProduct_self] at h0
  have h0r : ∑ i, ‖a i‖ ^ 2 + ∑ i, ‖c i‖ ^ 2 = 0 := by exact_mod_cast h0
  have ha0 : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc0 : 0 ≤ ∑ i, ‖c i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact ⟨eq_zero_of_sum_norm_sq_eq_zero (by linarith),
    eq_zero_of_sum_norm_sq_eq_zero (by linarith)⟩

/-- The `W × W` matrix `K = X₁₁ - X₁₂ + X₂₁ - X₂₂` of the witness computation. -/
def witnessK (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun i j => X (0, i) (0, j) - X (0, i) (1, j) + X (1, i) (0, j) - X (1, i) (1, j)

theorem blockDiag_scalar (a : Fin 2 → ℂ) :
    BlockBand.Internal.Contracts.Layers.blockDiag (fun k => a k • (1 : Matrix (Fin W) (Fin W) ℂ)) =
      diagonal fun p : Fin 2 × Fin W => a p.1 := by
  ext p q
  unfold BlockBand.Internal.Contracts.Layers.blockDiag
  by_cases h1 : p.1 = q.1
  · by_cases h2 : p.2 = q.2
    · have : p = q := Prod.ext h1 h2
      subst this; simp
    · have : p ≠ q := fun e => h2 (congrArg Prod.snd e)
      simp [h1, h2, diagonal_apply_ne _ this]
  · have : p ≠ q := fun e => h1 (congrArg Prod.fst e)
    simp [h1, diagonal_apply_ne _ this]

/-- **Genericity at the witness** `A₁ = λ I, A₂ = 0, B₁ = B₂ = I`, when `λ ∉ spec K`. -/
theorem det_csGram_witness_ne_zero (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {l : ℝ} (hl : (witnessK X - (l : ℂ) • 1).det ≠ 0) :
    (csGram (BlockBand.Internal.Contracts.Layers.blockDiag
        (fun k => (if k = 0 then (l : ℂ) else 0) • (1 : Matrix (Fin W) (Fin W) ℂ)) -
        (e : ℂ) • 1 - X) (bondMatrix .common (BlockBand.Layers.bondAssemble (bondWitness W)))).det
      ≠ 0 := by
  set a : Fin 2 → ℂ := fun k => if k = 0 then (l : ℂ) else 0
  set D := BlockBand.Internal.Contracts.Layers.blockDiag
    (fun k => a k • (1 : Matrix (Fin W) (Fin W) ℂ)) - (e : ℂ) • 1 - X
  set Bw := bondMatrix .common (BlockBand.Layers.bondAssemble (bondWitness W))
  have hDdiag : D = diagonal (fun p : Fin 2 × Fin W => a p.1) - (e : ℂ) • 1 - X := by
    simp only [D, blockDiag_scalar]
  have hDH : D.IsHermitian := by
    rw [hDdiag]
    refine ((isHermitian_diagonal_of_self_adjoint _ ?_).sub
      (isHermitian_one.smul (Complex.conj_ofReal e))).sub hX
    funext p
    simp only [a, Pi.star_apply]
    split_ifs <;> simp
  intro h0
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨hB, hBD⟩ := csGram_kernel hDH Bw hv
  have hBw : ∀ (y : Fin 2 × Fin W → ℂ) (j : Fin W), (Bwᴴ *ᵥ y) (0, j) = y (0, j) + y (1, j) := by
    intro y j
    simp only [mulVec, dotProduct, conjTranspose_apply, Bw, bondMatrix_bondWitness_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    simp [Finset.sum_ite_eq', apply_ite]
  have hw : ∀ j, v (1, j) = -v (0, j) := by
    intro j
    have := congrFun hB (0, j)
    rw [hBw] at this
    simp only [Pi.zero_apply] at this
    linear_combination this
  set w : Fin W → ℂ := fun j => v (0, j)
  have hDv : ∀ p, (D *ᵥ v) p = (a p.1 - e) * v p - (X *ᵥ v) p := by
    intro p
    rw [hDdiag, sub_mulVec, sub_mulVec, smul_mulVec, one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_diagonal]
    ring
  have hXv : ∀ j, (X *ᵥ v) (0, j) + (X *ᵥ v) (1, j) = (witnessK X *ᵥ w) j := by
    intro j
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, witnessK,
      Matrix.of_apply, w, hw]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hKw : (witnessK X - (l : ℂ) • 1) *ᵥ w = 0 := by
    funext j
    have := congrFun hBD (0, j)
    rw [hBw, hDv, hDv] at this
    simp only [Pi.zero_apply] at this
    rw [sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      ← hXv j, Pi.zero_apply]
    simp only [a, hw, w] at this ⊢
    simp only [Fin.isValue, ite_true, show ¬ ((1 : Fin 2) = 0) from by decide, ite_false] at this
    linear_combination -this
  have hw0 : w = 0 := by
    by_contra hne
    exact hl (exists_mulVec_eq_zero_iff.1 ⟨w, hne, hKw⟩)
  apply hv0
  funext p
  rcases p with ⟨k, j⟩
  have hj : v (0, j) = 0 := congrFun hw0 j
  fin_cases k
  · simpa using hj
  · simp [hw j, hj]

end BlockBand.Critical.Collar.Density
