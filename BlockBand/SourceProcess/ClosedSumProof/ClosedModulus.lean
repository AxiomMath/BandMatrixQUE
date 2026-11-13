module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedCond

/-!
# The modulus of one real closed coordinate at fixed `W`

**`closed_modulus_fixed`**: on the alive event at the window end, the probability that the real
coordinate `procX` (`Re(u(G_e - J_e))` on the window `[j₁, j₁ + L]`) moves by more than
`3λ + ℓ W⁻¹C_b + κ + κ'` within `ℓ` steps is at most the block bound of `modulus_tail` (with `c = W⁻¹C_c`) plus
the Markov terms of the drift and birth errors. Inputs: the fourth moments of the steps and the
integrability of the three error integrands (both supplied by `ClosedFourth`, `ClosedSummed`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSumProof

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum

variable {W p K M : ℕ} {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} {R : ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

theorem dInc_pow4_le (u : ℂ) (hu : ‖u‖ = 1) (j₁ L k : ℕ) (y : SampledPath W p M × ℝ) (hk : k < L) :
    dInc b E s T h q R W Vs e u j₁ L k y ^ 4 ≤ ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y‖ ^ 4 := by
  have e1 : dInc b E s T h q R W Vs e u j₁ L k y = reMul u ((am b E s T h q R W Vs (j₁ + k)).indicator
      (fun y => zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y) := by
    simp only [dInc, ite_eq_left hk]
    exact congrFun (indicator_reMul u _ _) y
  rw [e1, ← Even.pow_abs (by decide)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_reMul_le hu _) 4

/-- **The modulus of one real closed coordinate at fixed `W`.** -/
theorem closed_modulus_fixed [IsProbabilityMeasure (lawW b T q M W)]
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) {j₁ L : ℕ} (hj₁ : closeLen s W ≤ j₁)
    {u : ℂ} (hu : ‖u‖ = 1) (N ℓ : ℕ) (hℓ : 0 < ℓ) {lam κ κ' : ℝ} (hlam : 0 < lam) (hκ : 0 < κ)
    (hκ' : 0 < κ')
    (h4 : ∀ k < L, Integrable (fun y => ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y‖ ^ 4)
        (lawW b T q M W))
    (hfI : ∀ k < L, Integrable (fErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W))
    (hgI : ∀ k < L, Integrable (gErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W))
    (hβI : ∀ k < L, Integrable (betaErr b E s T h q R W Vs e j₁ L k) (lawW b T q M W)) :
    (lawW b T q M W) {y | y ∈ aliveM b E s T h q R W (j₁ + L) Vs ∧ ∃ x y', x ≤ y' ∧
        y' ≤ N * ℓ ∧ y' ≤ x + ℓ ∧ 3 * lam + ℓ * ((W : ℝ)⁻¹ * driftC b E K p M R) + κ + κ' <
          |procX b E s T h q W Vs e u j₁ L y' y - procX b E s T h q W Vs e u j₁ L x y|} ≤
      ENNReal.ofReal ((16 * ((W : ℝ)⁻¹ * covC b E K p M R) ^ 2 * ((N : ℝ) * ℓ) * ℓ +
          16 * (∑ i ∈ range (N * ℓ), ∫ y, fErr b E s T h q R W Vs e j₁ L i y ∂lawW b T q M W) ^ 2 +
          8 * lam ^ 2 * ∑ i ∈ range (N * ℓ), ∫ y, fErr b E s T h q R W Vs e j₁ L i y
            ∂lawW b T q M W +
          48 * ∑ i ∈ range (N * ℓ), ∫ y, dInc b E s T h q R W Vs e u j₁ L i y ^ 4
            ∂lawW b T q M W) / lam ^ 4) +
        ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ y, gErr b E s T h q R W Vs e j₁ L i y
          ∂lawW b T q M W) / κ) +
        ENNReal.ofReal ((∑ i ∈ range (N * ℓ), ∫ y, betaErr b E s T h q R W Vs e j₁ L i y
          ∂lawW b T q M W) / κ') := by
  set μ := lawW b T q M W
  have hzeroF : ∀ k, ¬ k < L → fErr b E s T h q R W Vs e j₁ L k = 0 := fun k hk => by
    funext y; simp only [fErr, ite_eq_right hk, Pi.zero_apply]
  have hzeroG : ∀ k, ¬ k < L → gErr b E s T h q R W Vs e j₁ L k = 0 := fun k hk => by
    funext y; simp only [gErr, ite_eq_right hk, Pi.zero_apply]
  have hzeroB : ∀ k, ¬ k < L → betaErr b E s T h q R W Vs e j₁ L k = 0 := fun k hk => by
    funext y; simp only [betaErr, ite_eq_right hk, Pi.zero_apply]
  have hzeroD : ∀ k, ¬ k < L → dInc b E s T h q R W Vs e u j₁ L k = 0 := fun k hk => by
    funext y; simp only [dInc, ite_eq_right hk, Pi.zero_apply]
  have hint : ∀ {φ : ℕ → SampledPath W p M × ℝ → ℝ}, (∀ k < L, Integrable (φ k) μ) →
      (∀ k, ¬ k < L → φ k = 0) → ∀ k, Integrable (φ k) μ := fun h1 h2 k => by
    by_cases hk : k < L
    · exact h1 k hk
    · rw [h2 k hk]; exact integrable_zero _ _ _
  have hΔ : ∀ k < L, Integrable ((am b E s T h q R W Vs (j₁ + k)).indicator fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) μ := fun k hk =>
    integrable_of_pow4 (aestronglyMeasurable_step e hVs (by omega) μ) (h4 k hk)
  have hd4 : ∀ k, Integrable (fun y => dInc b E s T h q R W Vs e u j₁ L k y ^ 4) μ := by
    intro k
    by_cases hk : k < L
    · refine Integrable.mono' (h4 k hk) ?_ (Filter.Eventually.of_forall fun y => ?_)
      · exact (((stronglyMeasurable_dInc e hVs hj₁ u L k).mono
          (closedSigma_le _)).aestronglyMeasurable).pow 4
      · rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
        exact dInc_pow4_le e u hu j₁ L k y hk
    · rw [hzeroD k hk]; simp
  have hdrift : ∀ k < N * ℓ, ∀ᵐ y ∂μ, |μ[dInc b E s T h q R W Vs e u j₁ L k |
      closedSigma W (j₁ + k) p M] y| ≤ (W : ℝ)⁻¹ * driftC b E K p M R +
        gErr b E s T h q R W Vs e j₁ L k y := fun k _ =>
    dInc_drift e hVs hj₁ hu L k (hΔ k)
  have hvar : ∀ k < N * ℓ, μ[fun y => dInc b E s T h q R W Vs e u j₁ L k y ^ 2 |
      closedSigma W (j₁ + k) p M] ≤ᵐ[μ] fun y => (W : ℝ)⁻¹ * covC b E K p M R +
        fErr b E s T h q R W Vs e j₁ L k y := fun k _ =>
    dInc_var e hVs hj₁ hu L k (h4 k)
  have hG : ∀ i, closedSigma W (j₁ + i) p M ≤ (inferInstance : MeasurableSpace _) := fun i =>
    closedSigma_le _
  have hGmono : Monotone fun i => closedSigma W (j₁ + i) p M := fun i i' hii' =>
    closedSigma_mono (by omega)
  have hdm : ∀ k, StronglyMeasurable[closedSigma W (j₁ + (k + 1)) p M]
      (dInc b E s T h q R W Vs e u j₁ L k) := fun k => stronglyMeasurable_dInc e hVs hj₁ u L k
  have hstep : ∀ y ∈ aliveM b E s T h q R W (j₁ + L) Vs, ∀ k < N * ℓ,
      |procX b E s T h q W Vs e u j₁ L (k + 1) y - procX b E s T h q W Vs e u j₁ L k y -
        dInc b E s T h q R W Vs e u j₁ L k y| ≤ betaErr b E s T h q R W Vs e j₁ L k y :=
    fun y hy k _ => procX_step b E s T h q R W Vs e hj₁ hu hy k
  exact modulus_births (fun i => closedSigma W (j₁ + i) p M) hG hGmono N ℓ hℓ
    (procX b E s T h q W Vs e u j₁ L) (aliveM b E s T h q R W (j₁ + L) Vs)
    (dInc b E s T h q R W Vs e u j₁ L) (fErr b E s T h q R W Vs e j₁ L)
    (gErr b E s T h q R W Vs e j₁ L) (betaErr b E s T h q R W Vs e j₁ L)
    ((W : ℝ)⁻¹ * covC b E K p M R) ((W : ℝ)⁻¹ * driftC b E K p M R) lam κ κ'
    (mul_nonneg (by positivity) (covC_nonneg b E K p M R))
    (mul_nonneg (by positivity) (driftC_nonneg b E K p M R)) hlam hκ hκ' hdm
    (fun k _ => hd4 k) (fErr_nonneg b E s T h q R W Vs e j₁ L) (fun k _ => hint hfI hzeroF k)
    hvar (gErr_nonneg b E s T h q R W Vs e j₁ L) (fun k _ => hint hgI hzeroG k) hdrift
    (betaErr_nonneg b E s T h q R W Vs e j₁ L) (fun k _ => hint hβI hzeroB k) hstep

end BlockBand.SourceProcess.ClosedSumProof
