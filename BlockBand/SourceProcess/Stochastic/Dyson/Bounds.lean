module

public import BlockBand.SourceProcess.Stochastic.Dyson.ItoIdentities

/-!
# Dyson Brownian motion: a priori bounds on the state, drift and covariance

* `overlap_nonneg`, `overlap_le`: on simple spectrum `0 ≤ X_i ≤ N ‖q‖²` (`‖q‖² = ∑ |q_a|²`);
* `abs_drift_le`, `abs_cov_le`: if all gaps are `≥ δ > 0` and `0 ≤ X ≤ B`, then
  `|dysonStateDrift k| ≤ 1/δ + B/δ²` and `|dysonStateCov k l| ≤ 1/N + 2B²/δ²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Matrix
open scoped Matrix ComplexConjugate
open BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- `q* P q = ‖P q‖²` for a Hermitian idempotent `P`. -/
theorem qf_proj_eq_normSq {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (q : Fin N → ℂ) : qf q P = ∑ a, ((Complex.normSq ((P *ᵥ q) a) : ℝ) : ℂ) := by
  have e : qf q P = star (P *ᵥ q) ⬝ᵥ (P *ᵥ q) := by
    rw [Matrix.star_mulVec, hP.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hPP]; rfl
  rw [e, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

theorem qf_one (q : Fin N → ℂ) : qf q 1 = ∑ a, ((Complex.normSq (q a) : ℝ) : ℂ) := by
  rw [qf, one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]

/-- `‖q‖² = ∑ |q_a|²`. -/
def qNormSq (q : Fin N → ℂ) : ℝ := ∑ a, Complex.normSq (q a)

theorem overlap_eq {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) (hs : HasSimpleSpectrum N H)
    (q : Fin N → ℂ) (i : Fin N) :
    dysonOverlap N q H i = (N : ℝ) * ∑ a, Complex.normSq ((dysonProjection N H i *ᵥ q) a) := by
  have hS := specFamily_dyson hH hs
  change (N : ℝ) * (qf q (dysonProjection N H i)).re = _
  rw [qf_proj_eq_normSq (proj_isHermitian hH hs i) (hS.proj_mul_self i)]
  simp only [← Complex.ofReal_sum, Complex.ofReal_re]

theorem overlap_nonneg {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (q : Fin N → ℂ) (i : Fin N) : 0 ≤ dysonOverlap N q H i := by
  rw [overlap_eq hH hs]
  exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)

theorem sum_overlap {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (q : Fin N → ℂ) :
    ∑ i, dysonOverlap N q H i = (N : ℝ) * qNormSq q := by
  have hS := specFamily_dyson hH hs
  change ∑ i, (N : ℝ) * (qf q (dysonProjection N H i)).re = _
  rw [← Finset.mul_sum, ← Complex.re_sum, ← qf_sum, hS.sum_proj, qf_one, qNormSq]
  simp only [← Complex.ofReal_sum, Complex.ofReal_re]

theorem overlap_le {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hs : HasSimpleSpectrum N H) (q : Fin N → ℂ) (i : Fin N) :
    dysonOverlap N q H i ≤ (N : ℝ) * qNormSq q := by
  rw [← sum_overlap hH hs q]
  exact Finset.single_le_sum (fun j _ => overlap_nonneg hH hs q j) (Finset.mem_univ i)

theorem coupling_nonneg (lam : Fin N → ℝ) (i j : Fin N) : 0 ≤ dysonCoupling N lam i j := by
  unfold dysonCoupling; positivity

theorem coupling_le {lam : Fin N → ℝ} {δ : ℝ} (hδ : 0 < δ) {i j : Fin N}
    (h : δ ≤ |lam i - lam j|) : dysonCoupling N lam i j ≤ 1 / (N * δ ^ 2) := by
  unfold dysonCoupling
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply one_div_le_one_div_of_le (by positivity)
  apply mul_le_mul_of_nonneg_left _ hN'.le
  calc δ ^ 2 ≤ |lam i - lam j| ^ 2 := pow_le_pow_left₀ hδ.le h 2
    _ = (lam i - lam j) ^ 2 := sq_abs _

theorem card_erase_le (i : Fin N) : ((Finset.univ.erase i).card : ℝ) ≤ N := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  exact_mod_cast Nat.sub_le N 1

/-- Drift bound under a gap lower bound and overlap bounds. -/
theorem abs_drift_le {y : Fin (N + N) → ℝ} {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hgap : ∀ i j : Fin N, i ≠ j →
      δ ≤ |y (finSumFinEquiv (Sum.inl i)) - y (finSumFinEquiv (Sum.inl j))|)
    (hX0 : ∀ i, 0 ≤ y (finSumFinEquiv (Sum.inr i))) (hXB : ∀ i, y (finSumFinEquiv (Sum.inr i)) ≤ B)
    (k : Fin (N + N)) : |dysonStateDrift N y k| ≤ 1 / δ + B / δ ^ 2 := by
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  have hN' : (0 : ℝ) < N := by
    rcases k with i | i <;> exact_mod_cast Fin.pos i
  rcases k with i | i
  · rw [dysonStateDrift_inl, dysonDrift, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
    have h1 : |∑ j ∈ Finset.univ.erase i, 1 / (y (finSumFinEquiv (Sum.inl i)) -
        y (finSumFinEquiv (Sum.inl j)))| ≤ N * (1 / δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (1 / δ) fun j hj => ?_).trans ?_
      · rw [abs_div, abs_one]
        exact one_div_le_one_div_of_le hδ (hgap i j (Finset.ne_of_mem_erase hj).symm)
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_erase_le i) (by positivity)
    calc 1 / (N : ℝ) * |∑ j ∈ Finset.univ.erase i, _| ≤ 1 / N * (N * (1 / δ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / δ := by field_simp
      _ ≤ 1 / δ + B / δ ^ 2 := le_add_of_nonneg_right (by positivity)
  · rw [dysonStateDrift_inr]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (1 / (N * δ ^ 2) * B) fun j hj => ?_).trans ?_
    · rw [abs_mul, abs_of_nonneg (coupling_nonneg _ _ _)]
      refine mul_le_mul (coupling_le hδ (hgap i j (Finset.ne_of_mem_erase hj).symm)) ?_
        (abs_nonneg _) (by positivity)
      rw [abs_le]
      constructor <;> linarith [hX0 i, hX0 j, hXB i, hXB j]
    · rw [nsmul_eq_mul]
      calc ((Finset.univ.erase i).card : ℝ) * (1 / (N * δ ^ 2) * B)
          ≤ N * (1 / (N * δ ^ 2) * B) :=
            mul_le_mul_of_nonneg_right (card_erase_le i) (by positivity)
        _ = B / δ ^ 2 := by field_simp
        _ ≤ 1 / δ + B / δ ^ 2 := le_add_of_nonneg_left (by positivity)

/-- Covariance bound under a gap lower bound and overlap bounds. -/
theorem abs_cov_le {y : Fin (N + N) → ℝ} {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hgap : ∀ i j : Fin N, i ≠ j →
      δ ≤ |y (finSumFinEquiv (Sum.inl i)) - y (finSumFinEquiv (Sum.inl j))|)
    (hX0 : ∀ i, 0 ≤ y (finSumFinEquiv (Sum.inr i))) (hXB : ∀ i, y (finSumFinEquiv (Sum.inr i)) ≤ B)
    (k l : Fin (N + N)) : |dysonStateCov N y k l| ≤ 1 / N + 2 * B ^ 2 / δ ^ 2 := by
  have hc0 : (0 : ℝ) ≤ 2 * B ^ 2 / δ ^ 2 := by positivity
  have hN0 : (0 : ℝ) ≤ 1 / N := by positivity
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective k
  obtain ⟨l, rfl⟩ := finSumFinEquiv.surjective l
  have hXX : ∀ a b, |y (finSumFinEquiv (Sum.inr a)) * y (finSumFinEquiv (Sum.inr b))| ≤ B ^ 2 :=
    fun a b => by
      rw [abs_mul, abs_of_nonneg (hX0 a), abs_of_nonneg (hX0 b), sq]
      exact mul_le_mul (hXB a) (hXB b) (hX0 b) hB
  rcases k with i | i <;> rcases l with j | j
  · rw [dysonStateCov_inl_inl]; split_ifs
    · rw [abs_of_nonneg hN0]; linarith
    · simp only [abs_zero]; positivity
  · rw [dysonStateCov_inl_inr]; simp only [abs_zero]; positivity
  · rw [dysonStateCov_inr_inl]; simp only [abs_zero]; positivity
  · have hN' : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
    rw [dysonStateCov_inr_inr]
    split_ifs with hij
    · rw [abs_mul, abs_two]
      have : |∑ m ∈ Finset.univ.erase i, dysonCoupling N (fun a => y (finSumFinEquiv (Sum.inl a)))
          i m * y (finSumFinEquiv (Sum.inr i)) * y (finSumFinEquiv (Sum.inr m))| ≤ B ^ 2 / δ ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (1 / (N * δ ^ 2) * B ^ 2) fun m hm => ?_).trans ?_
        · rw [mul_assoc, abs_mul, abs_of_nonneg (coupling_nonneg _ _ _)]
          exact mul_le_mul (coupling_le hδ (hgap i m (Finset.ne_of_mem_erase hm).symm)) (hXX i m)
            (abs_nonneg _) (by positivity)
        · rw [nsmul_eq_mul]
          calc ((Finset.univ.erase i).card : ℝ) * (1 / (N * δ ^ 2) * B ^ 2)
              ≤ N * (1 / (N * δ ^ 2) * B ^ 2) :=
                mul_le_mul_of_nonneg_right (card_erase_le i) (by positivity)
            _ = B ^ 2 / δ ^ 2 := by field_simp
      have h2 : 2 * B ^ 2 / δ ^ 2 = 2 * (B ^ 2 / δ ^ 2) := by ring
      linarith
    · rw [mul_assoc, mul_assoc, abs_mul, abs_mul, abs_neg, abs_two,
        abs_of_nonneg (coupling_nonneg _ _ _)]
      have hc := coupling_le (lam := fun a => y (finSumFinEquiv (Sum.inl a))) hδ (hgap i j hij)
      have h1 : 1 / (N * δ ^ 2) ≤ 1 / δ ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i
        nlinarith [sq_nonneg δ]
      have := mul_le_mul (hc.trans h1) (hXX i j) (abs_nonneg _) (by positivity)
      have h2 : 2 * B ^ 2 / δ ^ 2 = 2 * (1 / δ ^ 2 * B ^ 2) := by ring
      nlinarith

end BlockBand.SourceProcess.Stochastic.Dyson
