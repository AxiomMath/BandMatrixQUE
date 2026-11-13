module
public import BlockBand.SourceProcess.Stochastic.RankBarrier.Line
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Generator of `‖∧^k (Q V)‖²` under affine minor variations

Abstract step of the proof of the Gram rank barrier. Let
`φ(W) = minorSq k (Q W) / (k!)²` (`= e_k(WᴴQW)` for a Hermitian projection `Q`). Suppose:

* along the drift, `t ↦ φ(V + t b(V))` has derivative `d ≤ 0` at `0`;
* along each noise direction `σ_a(V)`, every minor of `Q(V + t σ_a(V))` is affine in `t`
  with slope `s_a` bounded by `‖s_a(p)‖ ≤ B ∑_q |det (QV)_q|`
  (the "linear equation with bounded coefficients" of).

Then `𝒢φ(V) ≤ |κ| |X|² B² φ(V)` with `X` the minor index set (`generator_minorSq_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

/-- `|a + t b|² = |a|² + t · 2 Re(ā b) + t² |b|²` for real `t`. -/
theorem norm_add_real_mul_sq (a b : ℂ) (t : ℝ) :
    ‖a + (t : ℂ) * b‖ ^ 2 = ‖a‖ ^ 2 + t * (2 * (star a * b).re) + t ^ 2 * ‖b‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Crude quadratic bound: `‖s p‖ ≤ B ∑_q ‖μ q‖` for all `p` gives
`∑_p ‖s p‖² ≤ |X|² B² ∑_q ‖μ q‖²`. -/
theorem sum_norm_sq_le_of_le {X : Type*} [Fintype X] (μ s : X → ℂ) (B : ℝ)
    (h : ∀ p, ‖s p‖ ≤ B * ∑ q, ‖μ q‖) :
    ∑ p, ‖s p‖ ^ 2 ≤ (Fintype.card X : ℝ) ^ 2 * B ^ 2 * ∑ q, ‖μ q‖ ^ 2 := by
  have hS : (∑ q, ‖μ q‖) ^ 2 ≤ (Fintype.card X : ℝ) * ∑ q, ‖μ q‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset X)) (f := fun q => ‖μ q‖)
    simpa [Finset.card_univ] using this
  have hX : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
  calc ∑ p, ‖s p‖ ^ 2 ≤ ∑ _p : X, (B * ∑ q, ‖μ q‖) ^ 2 :=
        Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _) (h p) 2
    _ = (Fintype.card X : ℝ) * (B ^ 2 * (∑ q, ‖μ q‖) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ (Fintype.card X : ℝ) * (B ^ 2 * ((Fintype.card X : ℝ) * ∑ q, ‖μ q‖ ^ 2)) := by
        gcongr
    _ = _ := by ring

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [Fintype c]

/-- Minor vector of `U`, indexed by pairs of index functions. -/
abbrev minorVec (k : ℕ) (U : Matrix ι c ℂ) : (Fin k → ι) × (Fin k → c) → ℂ :=
  fun p => det (U.submatrix p.1 p.2)

/-- `minorSq` along a line on which all minors are affine. -/
theorem minorSq_line (k : ℕ) (Q : Matrix ι ι ℂ) (V H : Matrix ι c ℂ)
    (s : (Fin k → ι) × (Fin k → c) → ℂ)
    (hlin : ∀ t : ℝ, ∀ p, minorVec k (Q * (V + t • H)) p = minorVec k (Q * V) p + t * s p)
    (t : ℝ) :
    minorSq k (Q * (V + t • H)) = minorSq k (Q * V) +
      t * ∑ p, 2 * (star (minorVec k (Q * V) p) * s p).re + t ^ 2 * ∑ p, ‖s p‖ ^ 2 := by
  unfold minorSq
  have : ∀ p : (Fin k → ι) × (Fin k → c), ‖det ((Q * (V + t • H)).submatrix p.1 p.2)‖ ^ 2 =
      ‖minorVec k (Q * V) p‖ ^ 2 + t * (2 * (star (minorVec k (Q * V) p) * s p).re) +
        t ^ 2 * ‖s p‖ ^ 2 := fun p => by
    rw [← norm_add_real_mul_sq]; exact congrArg (‖·‖ ^ 2) (hlin t p)
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

/-- **Abstract generator bound** for `φ(W) = minorSq k (Q W) / (k!)²`. -/
theorem generator_minorSq_le (k : ℕ) (Q : Matrix ι ι ℂ)
    (b : Matrix ι c ℂ → Matrix ι c ℂ) (σ : κ → Matrix ι c ℂ → Matrix ι c ℂ)
    (V : Matrix ι c ℂ) (B : ℝ)
    (hdrift : ∃ d ≤ 0,
      HasDerivAt (fun t : ℝ => minorSq k (Q * (V + t • b V)) / (k.factorial : ℝ) ^ 2) d 0)
    (hnoise : ∀ a, ∃ s : (Fin k → ι) × (Fin k → c) → ℂ,
      (∀ t : ℝ, ∀ p, minorVec k (Q * (V + t • σ a V)) p = minorVec k (Q * V) p + t * s p) ∧
      ∀ p, ‖s p‖ ≤ B * ∑ q, ‖minorVec k (Q * V) q‖) :
    sdeGenerator b σ (fun W => minorSq k (Q * W) / (k.factorial : ℝ) ^ 2) V ≤
      ((Fintype.card κ : ℝ) * (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 * B ^ 2) *
        (minorSq k (Q * V) / (k.factorial : ℝ) ^ 2) := by
  obtain ⟨d, hd, hdd⟩ := hdrift
  choose s hs hsb using hnoise
  set N : ℝ := (k.factorial : ℝ) ^ 2
  have hN : 0 < N := by positivity
  have hφ : ContDiff ℝ 2 fun W : Matrix ι c ℂ => minorSq k (Q * W) / N :=
    (contDiff_minorSq_mul k Q).div_const _
  have h1 := fderiv_apply_eq_of_line (hφ.differentiable (by norm_num) V) hdd
  have h2 : ∀ a, fderiv ℝ (fderiv ℝ fun W : Matrix ι c ℂ => minorSq k (Q * W) / N) V
      (σ a V) (σ a V) = 2 * ((∑ p, ‖s a p‖ ^ 2) / N) := by
    intro a
    refine fderiv_fderiv_eq_of_quadratic (a := minorSq k (Q * V) / N)
      (b := (∑ p, 2 * (star (minorVec k (Q * V) p) * s a p).re) / N) hφ fun t => ?_
    rw [minorSq_line k Q V (σ a V) (s a) (hs a) t]
    ring
  have h3 : ∀ a, (∑ p, ‖s a p‖ ^ 2) / N ≤
      (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 * B ^ 2 * (minorSq k (Q * V) / N) := by
    intro a
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hN]
    exact sum_norm_sq_le_of_le _ _ B (hsb a)
  have key : 1 / 2 * ∑ a, fderiv ℝ (fderiv ℝ fun W : Matrix ι c ℂ => minorSq k (Q * W) / N) V
      (σ a V) (σ a V) ≤ ∑ _a : κ, (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 * B ^ 2 *
        (minorSq k (Q * V) / N) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [h2 a]
    linarith [h3 a]
  have hfin : d + ∑ _a : κ, (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 * B ^ 2 *
        (minorSq k (Q * V) / N) ≤ ((Fintype.card κ : ℝ) *
          (Fintype.card ((Fin k → ι) × (Fin k → c)) : ℝ) ^ 2 * B ^ 2) *
        (minorSq k (Q * V) / N) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  exact le_trans (add_le_add h1.le key) hfin

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
