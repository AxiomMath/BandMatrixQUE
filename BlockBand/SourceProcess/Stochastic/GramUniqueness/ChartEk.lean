module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ChartFC
public import BlockBand.SourceProcess.Stochastic.RankBarrier.GramMinors
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Nat.Choose.Bounds
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# `e_k` and the eigenvalues; a spectral gap on a fixed-rank stratum

* **`principalMinorSum_eq_esymm`**: for a positive semidefinite `A`,
  `e_k(A) = ∑_{|s| = k} ∏_{i ∈ s} λ_i` (eigenvalues `λ = eL A` of `hermPart A = A`). Proof by
  Cauchy–Binet (`principalMinorSum_gram`, from `RankBarrier/GramMinors`) applied to `X` and `Xᴴ`,
  `X = diag(√λ) Uᴴ`: `XᴴX = A`, `XXᴴ = diag(λ)`.
* **`esymm_gap`**: for `0 ≤ λ_i ≤ T` (`T ≥ 1`), `e_{r+1}(λ) = 0` and `e_r(λ) ≥ η`, every
  positive `λ_j` satisfies `η ≤ 2^n T^r λ_j`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
open Matrix Finset BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.RankBarrierProof
open scoped NNReal ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem minorSq_conjTranspose (k : ℕ) (X : Matrix n n ℂ) : minorSq k Xᴴ = minorSq k X := by
  unfold minorSq
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, norm_star]

theorem principalMinorSum_diagonal (k : ℕ) (d : n → ℝ) :
    principalMinorSum k (diagonal fun i => (d i : ℂ)) = ∑ s ∈ univ.powersetCard k, ∏ i ∈ s, d i := by
  unfold principalMinorSum
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : (diagonal fun i => (d i : ℂ)).submatrix (fun i : s => (i : n)) (fun i : s => (i : n)) =
      diagonal fun i : s => (d i : ℂ) :=
    submatrix_diagonal_embedding (fun i => (d i : ℂ)) (Function.Embedding.subtype (· ∈ s))
  rw [e, det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_coe_sort s d

/-- **`e_k` of a positive semidefinite matrix is the elementary symmetric function of its
eigenvalues.** -/
theorem principalMinorSum_eq_esymm {A : Matrix n n ℂ} (hA : A.PosSemidef) (k : ℕ) :
    principalMinorSum k A = ∑ s ∈ univ.powersetCard k, ∏ i ∈ s, eL A i := by
  have hH : hermPart A = A := hermPart_of_herm hA.1
  have hP : (hermPart A).PosSemidef := by rw [hH]; exact hA
  have h0 : ∀ i, 0 ≤ eL A i := fun i => hP.eigenvalues_nonneg i
  set U := eU A
  set S : Matrix n n ℂ := diagonal fun i => ((Real.sqrt (eL A i) : ℝ) : ℂ)
  set X := S * star U
  have hS : Sᴴ = S := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  have hS' : star S = S := by rw [star_eq_conjTranspose]; exact hS
  have hSS : S * S = diagonal fun i => ((eL A i : ℝ) : ℂ) := by
    rw [diagonal_mul_diagonal]; congr 1; funext i
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (h0 i)]
  have h1 : Xᴴ * X = A := by
    have : Xᴴ * X = U * (S * S) * star U := by
      simp only [X, ← star_eq_conjTranspose, star_mul, star_star, hS', Matrix.mul_assoc]
    rw [this, hSS]
    exact (fcM_id A).trans hH
  have h2 : Xᴴᴴ * Xᴴ = diagonal fun i => ((eL A i : ℝ) : ℂ) := by
    rw [conjTranspose_conjTranspose]
    have : X * Xᴴ = S * (star U * U) * S := by
      simp only [X, ← star_eq_conjTranspose, star_mul, star_star, hS', Matrix.mul_assoc]
    rw [this, eU_star_mul, Matrix.mul_one, hSS]
  have g1 := principalMinorSum_gram k X
  have g2 := principalMinorSum_gram k Xᴴ
  rw [h1] at g1
  rw [h2, minorSq_conjTranspose, ← g1, principalMinorSum_diagonal] at g2
  exact g2.symm

/-- **The spectral gap from `e_r`, `e_{r+1}`.** -/
theorem esymm_gap {lam : n → ℝ} (h0 : ∀ i, 0 ≤ lam i) {T : ℝ} (hT1 : 1 ≤ T)
    (hT : ∀ i, lam i ≤ T) {r : ℕ}
    (hz : ∑ s ∈ univ.powersetCard (r + 1), ∏ i ∈ s, lam i = 0) {η : ℝ}
    (hη : η ≤ ∑ s ∈ univ.powersetCard r, ∏ i ∈ s, lam i) (j : n) (hj : 0 < lam j) :
    η ≤ 2 ^ Fintype.card n * T ^ r * lam j := by
  have hT0 : 0 ≤ T := by linarith
  have hterm : ∀ s ∈ univ.powersetCard r, ∏ i ∈ s, lam i ≤ T ^ r * lam j := by
    intro s hs
    have hcard : s.card = r := (Finset.mem_powersetCard.1 hs).2
    by_cases hjs : j ∈ s
    · rw [← Finset.mul_prod_erase s lam hjs, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ hj.le
      calc ∏ i ∈ s.erase j, lam i ≤ ∏ _i ∈ s.erase j, T :=
            Finset.prod_le_prod₀ (fun i _ => h0 i) fun i _ => hT i
        _ = T ^ (s.erase j).card := Finset.prod_const T
        _ ≤ T ^ r := pow_le_pow_right₀ hT1 (by rw [Finset.card_erase_of_mem hjs, hcard]; omega)
    · have hz' := (Finset.sum_eq_zero_iff_of_nonneg fun s _ =>
        Finset.prod_nonneg fun i _ => h0 i).1 hz (insert j s) (Finset.mem_powersetCard.2
          ⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hjs, hcard]⟩)
      rw [Finset.prod_insert hjs] at hz'
      have hp : ∏ i ∈ s, lam i = 0 := (mul_eq_zero.1 hz').resolve_left hj.ne'
      rw [hp]; positivity
  calc η ≤ ∑ s ∈ univ.powersetCard r, ∏ i ∈ s, lam i := hη
    _ ≤ (univ.powersetCard r).card • (T ^ r * lam j) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ ≤ 2 ^ Fintype.card n * T ^ r * lam j := by
        rw [nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ, mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast Nat.choose_le_two_pow _ _

end BlockBand.SourceProcess.Stochastic.GramUniqueness.GramChart
