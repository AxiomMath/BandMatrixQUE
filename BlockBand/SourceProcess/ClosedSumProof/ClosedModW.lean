module

public import BlockBand.SourceProcess.ClosedSumProof.ClosedWindow

/-!
# The modulus of one real closed coordinate at fixed `W`, from the summed errors

**`closed_modulus_W`**: if `closedSummedErr … e (swapE e) ≤ ε` and `closedFourthErr … e ≤ ε`
(`ε ≤ 1`) at width `W`, the modulus event of `procX` on the alive event at the window end has
probability at most `16(W⁻¹C_c)²(Nℓ)ℓ/λ⁴ + ε((64 + 8λ²)/λ⁴ + 1/κ + 1/κ')`.
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
open scoped ENNReal

variable {W p K M : ℕ} {b E s T h : ℝ} {q : Fin p → ℝ → ℝ} {R : ℝ}
  {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  (e : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M))

theorem modulus_arith {c NL ℓ F D G B ε lam κ κ' : ℝ} (hlam : 0 < lam) (hκ : 0 < κ)
    (hκ' : 0 < κ') (hF0 : 0 ≤ F) (hF : F ≤ ε) (hD : D ≤ ε) (hG : G ≤ ε) (hB : B ≤ ε)
    (hε1 : ε ≤ 1) :
    (16 * c ^ 2 * NL * ℓ + 16 * F ^ 2 + 8 * lam ^ 2 * F + 48 * D) / lam ^ 4 + G / κ + B / κ' ≤
      16 * c ^ 2 * NL * ℓ / lam ^ 4 + ε * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / κ + 1 / κ') := by
  have h4 : 0 < lam ^ 4 := by positivity
  have hF2 : F ^ 2 ≤ ε := by nlinarith
  have h1 : (16 * c ^ 2 * NL * ℓ + 16 * F ^ 2 + 8 * lam ^ 2 * F + 48 * D) / lam ^ 4 ≤
      (16 * c ^ 2 * NL * ℓ + ε * (64 + 8 * lam ^ 2)) / lam ^ 4 :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg lam]) h4.le
  have h2 : G / κ ≤ ε * (1 / κ) := by rw [mul_one_div]; exact div_le_div_of_nonneg_right hG hκ.le
  have h3 : B / κ' ≤ ε * (1 / κ') := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hB hκ'.le
  have e1 : (16 * c ^ 2 * NL * ℓ + ε * (64 + 8 * lam ^ 2)) / lam ^ 4 =
      16 * c ^ 2 * NL * ℓ / lam ^ 4 + ε * ((64 + 8 * lam ^ 2) / lam ^ 4) := by ring
  linarith

/-- **The modulus of one real closed coordinate at fixed `W`.** -/
theorem closed_modulus_W [IsProbabilityMeasure (lawW b T q M W)] (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hq : ∀ i x, 0 ≤ q i x) (hVs : Measurable[growthSigma W (closeLen s W)] Vs)
    {j₁ L : ℕ} (hj₁ : closeLen s W ≤ j₁) (hL : j₁ + L ≤ ⌊(W : ℝ) * T⌋₊) (N ℓ : ℕ) (hℓ : 0 < ℓ)
    (hNL : L ≤ N * ℓ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hS : closedSummedErr b E s T h q R W Vs e (swapE e) ≤ ENNReal.ofReal ε)
    (hF : closedFourthErr b E s T h q R W Vs e ≤ ENNReal.ofReal ε) {u : ℂ} (hu : ‖u‖ = 1)
    {lam κ κ' : ℝ} (hlam : 0 < lam) (hκ : 0 < κ) (hκ' : 0 < κ') :
    (lawW b T q M W) {y | y ∈ aliveM b E s T h q R W (j₁ + L) Vs ∧ ∃ x y', x ≤ y' ∧
        y' ≤ N * ℓ ∧ y' ≤ x + ℓ ∧ 3 * lam + ℓ * ((W : ℝ)⁻¹ * driftC b E K p M R) + κ + κ' <
          |procX b E s T h q W Vs e u j₁ L y' y - procX b E s T h q W Vs e u j₁ L x y|} ≤
      ENNReal.ofReal (16 * ((W : ℝ)⁻¹ * covC b E K p M R) ^ 2 * ((N : ℝ) * ℓ) * ℓ / lam ^ 4 +
        ε * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / κ + 1 / κ')) := by
  set μ := lawW b T q M W
  obtain ⟨i4, iF, iG, iB, s4, sF, sG, sB⟩ :=
    window_errs e hb hE1 hE2 hq hVs hj₁ hL hNL (N := N) (ℓ := ℓ) hS hF
  rw [max_eq_left hε0] at s4 sF sG sB
  have h4 : ∀ k < L, Integrable (fun y => ‖(am b E s T h q R W Vs (j₁ + k)).indicator (fun y =>
      zc b E s T h q W Vs e (j₁ + k + 1) y - zc b E s T h q W Vs e (j₁ + k) y) y‖ ^ 4) μ :=
    fun k hk => (i4 k hk).congr (Filter.Eventually.of_forall fun y => by
      simp only [phi4, ite_eq_left hk])
  have hi4 : ∀ k, Integrable (phi4 b E s T h q R W Vs e j₁ L k) μ := fun k => by
    by_cases hk : k < L
    · exact i4 k hk
    · have : phi4 b E s T h q R W Vs e j₁ L k = 0 := by
        funext y; simp only [phi4, ite_eq_right hk, Pi.zero_apply]
      rw [this]; exact integrable_zero _ _ _
  have hD : ∑ i ∈ range (N * ℓ), ∫ y, dInc b E s T h q R W Vs e u j₁ L i y ^ 4 ∂μ ≤ ε := by
    refine le_trans (Finset.sum_le_sum fun i _ => integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun y => Even.pow_nonneg (by decide) _) (hi4 i)
      (Filter.Eventually.of_forall fun y => ?_)) s4
    by_cases hk : i < L
    · simp only [phi4, ite_eq_left hk]; exact dInc_pow4_le e u hu j₁ L i y hk
    · simp [dInc, phi4, ite_eq_right hk]
  have hF0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, fErr b E s T h q R W Vs e j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => fErr_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ y
  have hD0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, dInc b E s T h q R W Vs e u j₁ L i y ^ 4 ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => Even.pow_nonneg (by decide) _
  have hG0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, gErr b E s T h q R W Vs e j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y => gErr_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ y
  have hB0 : 0 ≤ ∑ i ∈ range (N * ℓ), ∫ y, betaErr b E s T h q R W Vs e j₁ L i y ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun y =>
      betaErr_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ y
  refine (closed_modulus_fixed e hVs hj₁ hu N ℓ hℓ hlam hκ hκ' h4 (fun k hk => iF k hk)
    (fun k hk => iG k hk) (fun k hk => iB k hk)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (modulus_arith hlam hκ hκ' hF0 sF hD sG sB hε1)

end BlockBand.SourceProcess.ClosedSumProof
