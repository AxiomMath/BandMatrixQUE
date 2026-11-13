module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.LogCutoff
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GenChain
public import BlockBand.SourceProcess.Stochastic.RankBarrier.Generator
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The log barrier in the ambient form

For `φ(W) = minorSq k (QW)/(k!)²` (`= e_k` of the near or far Gram matrix) with the affine-minor
structure of the rank barrier generator (slopes bounded by `B ∑|minor|`), a drift derivative
`d ≥ −L φ(V)`, and `φ(V) ≥ ε > 0`:
`𝒢(cutH ε ∘ φ)(V) ≤ L + ½ |κ| (2 |X| B)²` (`generator_cut_minorSq_le`), with the bound
**independent of `ε`**. On `φ ≥ ε` the cutoff is `−log`, so this is `𝒢(−log e_k) ≤ C`:
`−𝒢φ/φ ≤ L` (the second-order part of `𝒢φ` is `≥ 0`) and `(Dφ[σ_a])² ≤ (2|X|B)² φ²`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.RankBarrierProof BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [Fintype c] {κ : Type*} [Fintype κ]

theorem abs_sum_two_re_le {X : Type*} [Fintype X] (m s : X → ℂ) (B : ℝ)
    (h : ∀ p, ‖s p‖ ≤ B * ∑ q, ‖m q‖) :
    |∑ p, 2 * (star (m p) * s p).re| ≤ 2 * Fintype.card X * B * ∑ q, ‖m q‖ ^ 2 := by
  have hB : 0 ≤ B ∨ ∑ q, ‖m q‖ = 0 := by
    by_cases hm : ∑ q, ‖m q‖ = 0
    · exact Or.inr hm
    · left
      obtain ⟨p, -⟩ : ∃ p, p ∈ (univ : Finset X) := by
        by_contra hX; push Not at hX
        exact hm (Finset.sum_eq_zero fun q _ => absurd (mem_univ q) (hX q))
      have hpos : 0 < ∑ q, ‖m q‖ := lt_of_le_of_ne (sum_nonneg fun _ _ => norm_nonneg _)
        (Ne.symm hm)
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (h p)) hpos
  have hS : (∑ q, ‖m q‖) ^ 2 ≤ (Fintype.card X : ℝ) * ∑ q, ‖m q‖ ^ 2 := by
    simpa [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := (univ : Finset X))
      (f := fun q => ‖m q‖)
  calc |∑ p, 2 * (star (m p) * s p).re| ≤ ∑ p, |2 * (star (m p) * s p).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, 2 * (‖m p‖ * (B * ∑ q, ‖m q‖)) := by
        refine sum_le_sum fun p _ => ?_
        rw [abs_mul, abs_two]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left (h p) (norm_nonneg _)
    _ = 2 * B * (∑ q, ‖m q‖) ^ 2 := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    _ ≤ 2 * Fintype.card X * B * ∑ q, ‖m q‖ ^ 2 := by
        rcases hB with hB | hB
        · nlinarith
        · rw [hB]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            mul_zero]
          have : ∀ q, ‖m q‖ = 0 := fun q => (Finset.sum_eq_zero_iff_of_nonneg
            (fun _ _ => norm_nonneg _)).1 hB q (mem_univ q)
          simp [this]

theorem key_log_bound {κ : Type*} [Fintype κ] (T1 d a L C' : ℝ) (T2 T3 : κ → ℝ) (h1 : T1 = d)
    (hdL : -(L * a) ≤ d) (h2 : ∀ i, 0 ≤ T2 i) (h3 : ∀ i, T3 i ^ 2 ≤ C' * a ^ 2) (ha : 0 < a) :
    -(T1 + 1 / 2 * ∑ i, T2 i) / a + 1 / 2 * ∑ i, T3 i * T3 i / a ^ 2 ≤
      L + 1 / 2 * ((Fintype.card κ : ℝ) * C') := by
  have hs : 0 ≤ ∑ i, T2 i := sum_nonneg fun i _ => h2 i
  have h3' : ∑ i, T3 i * T3 i / a ^ 2 ≤ ∑ _i : κ, C' := sum_le_sum fun i _ => by
    rw [div_le_iff₀ (by positivity), ← sq]; exact h3 i
  rw [sum_const, card_univ, nsmul_eq_mul] at h3'
  have h4 : -(T1 + 1 / 2 * ∑ i, T2 i) / a ≤ L := by
    rw [div_le_iff₀ ha]; nlinarith
  linarith

/-- **Ambient log barrier.** -/
theorem generator_cut_minorSq_le (k : ℕ) (Q : Matrix ι ι ℂ)
    (b : Matrix ι c ℂ → Matrix ι c ℂ) (σ : κ → Matrix ι c ℂ → Matrix ι c ℂ)
    (V : Matrix ι c ℂ) (B L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hφV : ε ≤ minorSq k (Q * V) / (k.factorial : ℝ) ^ 2) {d : ℝ}
    (hdd : HasDerivAt (fun t : ℝ => minorSq k (Q * (V + t • b V)) / (k.factorial : ℝ) ^ 2) d 0)
    (hdL : -(L * (minorSq k (Q * V) / (k.factorial : ℝ) ^ 2)) ≤ d)
    (hnoise : ∀ a, ∃ s : (Fin k → ι) × (Fin k → c) → ℂ,
      (∀ t : ℝ, ∀ p, minorVec k (Q * (V + t • σ a V)) p = minorVec k (Q * V) p + t * s p) ∧
      ∀ p, ‖s p‖ ≤ B * ∑ q, ‖minorVec k (Q * V) q‖) :
    sdeGenerator b σ (fun W => cutH ε (minorSq k (Q * W) / (k.factorial : ℝ) ^ 2)) V ≤
      L + 1 / 2 * ((Fintype.card κ : ℝ) *
        (2 * Fintype.card ((Fin k → ι) × (Fin k → c)) * B) ^ 2) := by
  choose sl hs hsb using hnoise
  set N : ℝ := (k.factorial : ℝ) ^ 2
  have hN : 0 < N := by positivity
  set φ : Matrix ι c ℂ → ℝ := fun W => minorSq k (Q * W) / N with hφdef
  have hφ : ContDiff ℝ 2 φ := (contDiff_minorSq_mul k Q).div_const _
  set aV := φ V
  have ha : ε / 2 < aV := by linarith
  have ha0 : 0 < aV := by linarith
  -- first and second derivatives along the noise lines
  have hq : ∀ i, ∀ t : ℝ, φ (V + t • σ i V) = aV +
      (∑ p, 2 * (star (minorVec k (Q * V) p) * sl i p).re) / N * t +
        (∑ p, ‖sl i p‖ ^ 2) / N * t ^ 2 := fun i t => by
    simp only [hφdef, aV, minorSq_line k Q V (σ i V) (sl i) (hs i) t]; ring
  have hD1 : ∀ i, fderiv ℝ φ V (σ i V) =
      (∑ p, 2 * (star (minorVec k (Q * V) p) * sl i p).re) / N := fun i => by
    refine fderiv_apply_eq_of_line (hφ.differentiable (by norm_num) V) ?_
    have : HasDerivAt (fun t : ℝ => aV + (∑ p, 2 * (star (minorVec k (Q * V) p) * sl i p).re) / N * t +
        (∑ p, ‖sl i p‖ ^ 2) / N * t ^ 2)
        ((∑ p, 2 * (star (minorVec k (Q * V) p) * sl i p).re) / N) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul
        ((∑ p, 2 * (star (minorVec k (Q * V) p) * sl i p).re) / N)).const_add aV |>.add
        (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul ((∑ p, ‖sl i p‖ ^ 2) / N))
      convert this using 1
      · funext t; simp
      · simp
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hq i t)
  have hD2 : ∀ i, 0 ≤ fderiv ℝ (fderiv ℝ φ) V (σ i V) (σ i V) := fun i => by
    have h := fderiv_fderiv_eq_of_quadratic hφ (hq i)
    have : 0 ≤ ∑ p, ‖sl i p‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    exact le_of_le_of_eq (by positivity) h.symm
  have hDb : fderiv ℝ φ V (b V) = d := fderiv_apply_eq_of_line (hφ.differentiable (by norm_num) V) hdd
  have hDsq : ∀ i, (fderiv ℝ φ V (σ i V)) ^ 2 ≤ (2 * Fintype.card ((Fin k → ι) × (Fin k → c)) * B) ^ 2 * aV ^ 2 := fun i => by
    rw [hD1 i, ← mul_pow]
    refine sq_le_sq' ?_ ?_ <;> [skip; skip]
    all_goals
      have h := abs_sum_two_re_le (minorVec k (Q * V)) (sl i) B (hsb i)
      have hm : ∑ q, ‖minorVec k (Q * V) q‖ ^ 2 = N * aV := by
        simp only [aV, hφdef, minorSq, minorVec]; field_simp
      rw [hm] at h
      rw [abs_le] at h
    · rw [le_div_iff₀ hN]; nlinarith [h.1]
    · rw [div_le_iff₀ hN]; nlinarith [h.2]
  -- assemble
  have e := sdeGenerator_comp b σ (contDiff_cutH hε) hφ V
  rw [e, fderiv_cutH hε ha, ← sdeGenerator_eq_vecGen]
  simp only [fderiv_fderiv_cutH (a := φ V) hε ha]
  unfold sdeGenerator
  exact key_log_bound _ d aV L _ _ _ hDb hdL hD2 hDsq ha0

end BlockBand.SourceProcess.Stochastic.GramUniqueness
