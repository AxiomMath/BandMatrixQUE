module

public import BlockBand.Endpoints.Clock.DetClockProofChain

/-!
# The deterministic-clock lemma (critical determinant evolution)

We prove the deterministic-clock lemma from five hypotheses.

* `detClockEvolutionD_of`: `DetClockEvolutionD`: fixed
  `0 < b < 1/2`, `-2 < E < 2`, `T`, admissible `q`; there is `ε > 0` such that for every
  `K ≥ 1` there are `δ_{W,j}` with `|r^D_{W,j}(a)| ≤ δ_{W,j}` for all Hermitian `‖D‖ ≤ ε`,
  `j₀ ≤ j ≤ TW`, `a ∈ [K⁻¹, K]`, and `Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0`. Here
  `δ_{W,j} = C_K W^{-3/2}` for `W ≥ W₀` (`C_K = C·E Λ⁹`, `stepDefect_le`, `pastWeight_moment`),
  so the sum is `O(W^{-1/2})`; for `W < W₀`, `δ_{W,j}` is the trivial bound
  `2 + D₀W + d K_q K`. `ε` is the minimum of the `ε` of `OpenInputsMoments` and of
  the clock-mixing lemma at moment order `9`; it does not depend on `K`.
* `detClockEvolution_of`: the statement `DetClockEvolution` (`D = 0`), by
  `detClockEvolution_of_D`.

Differences from the paper's proof (none weakens the statement): the event splitting with Markov at
`p > 6` is replaced by the deterministic global Taylor bound
(`taylor_global`, `laplace_diff_le`); the domain `δ₀ ≤ d_*` of the Ward mean is handled by
`1 ≤ (δ₀/d_*)²` and the moments of `δ₀` (so no companion operator-moment estimate is needed); all
past moments are taken at the single order `9`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix Filter Topology Set
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator

namespace DetClockProof

open ClockMixingAlg ClockMixingProb

/-- The trivial bound on the defect for every `W` (`Tr A_a ≤ W`). -/
theorem stepDefect_trivial {W : ℕ} {b E qv a K Kq : ℝ} {X Q : Matrix (Fin W) (Fin W) ℂ}
    (hQ : Q.PosSemidef) (ha0 : 0 ≤ a) (haK : a ≤ K) (hqv0 : 0 ≤ qv) (hqvK : qv ≤ Kq)
    (hD : 0 ≤ transportD0 b E) (hd : 0 ≤ dStar b) :
    |stepDefect W b E qv a X Q| ≤ 2 + transportD0 b E * W + dStar b * Kq * K := by
  refine (stepDefect_crude hQ ha0 hqv0 hD hd).trans ?_
  have hT0 := re_trace_resolventWeight_nonneg hQ ha0
  have hT := trace_weight_le_card hQ ha0
  have hsq : (resolventWeight Q a).trace.re ^ 2 ≤ (W : ℝ) ^ 2 := pow_le_pow_left₀ hT0 hT 2
  have hKq : 0 ≤ Kq := hqv0.trans hqvK
  have h1 : dStar b * qv * a ≤ dStar b * Kq * K :=
    mul_le_mul_nn (mul_nonneg hd hqv0) (mul_le_mul_of_nonneg_left hqvK hd) ha0 haK
  rcases Nat.eq_zero_or_pos W with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, _root_.inv_zero, zero_mul, add_zero, mul_zero]
    have : 0 ≤ dStar b * Kq * K := by
      have hK0 : 0 ≤ K := ha0.trans haK
      positivity
    linarith
  · have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hpos
    have hW0 : (0 : ℝ) < W := by linarith
    have hWi : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
    have e1 : (W : ℝ)⁻¹ * (transportD0 b E * (resolventWeight Q a).trace.re ^ 2) ≤
        transportD0 b E * W := by
      have := mul_le_mul_of_nonneg_left hsq hD
      have e : (W : ℝ)⁻¹ * (transportD0 b E * (W : ℝ) ^ 2) = transportD0 b E * W := by
        field_simp
      rw [← e]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have e2 : (W : ℝ)⁻¹ * (dStar b * qv * a) ≤ dStar b * Kq * K := by
      have h0 : 0 ≤ dStar b * qv * a := by positivity
      calc (W : ℝ)⁻¹ * (dStar b * qv * a) ≤ 1 * (dStar b * qv * a) :=
            mul_le_mul_of_nonneg_right hWi h0
        _ ≤ _ := by rw [one_mul]; exact h1
    rw [mul_add]
    linarith

end DetClockProof

open DetClockProof ClockMixingAlg ClockMixingProb

/-- **The deterministic-clock lemma, uniformly in the initial `‖D‖ ≤ ε`** (`DetClockEvolutionD`),
from `PassiveSourceMixingContract`, `PassiveCovarianceContract`, `GaussianAbsorptionContract`,
`LayersOnePort.OnePortWeightedCovarianceContract` and `OpenInputsMoments`. See the module
docstring. -/
theorem detClockEvolutionD_of (hPSM : PassiveSourceMixingContract)
    (hPC : PassiveCovarianceContract) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    (hOI : OpenInputsMoments) : DetClockEvolutionD := by
  intro b hb0 hb1 E hE0 hE1 T q hq
  obtain ⟨⟨s, hs⟩, -⟩ := hPC b hb0 hb1 E hE0 hE1
  obtain ⟨ε₁, C₁, W₁, hε₁, hOI'⟩ := hOI b hb0 hb1 E hE0 hE1 T q hq 9 (by norm_num)
  obtain ⟨ε₂, C₂, W₂, hε₂, hCM⟩ :=
    clockMixingUniform_of hPSM hGA hOI b hb0 hb1 E hE0 hE1 T q hq 9 (by norm_num)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun K hK => ?_⟩
  obtain ⟨_hqc, hq0, Kq, hqK⟩ := hq
  have hKq : 0 ≤ Kq := (hq0 0).trans (hqK 0)
  have hK0 : 0 < K := by linarith
  obtain ⟨Cs, Ws, hCs0, hstep⟩ := stepDefect_le hPSM hPC hGA hWC hb0 hb1 hE0 hE1 hs hK hKq
  have hD := (transportD0_pos hb0 hE0 hE1).le
  have hd := (dStar_pos (by linarith : b < 1)).le
  set C₁' := max C₁ 0 with hC₁'
  set C₂' := max C₂ 0 with hC₂'
  have hC₁0 : 0 ≤ C₁' := le_max_right _ _
  have hC₂0 : 0 ≤ C₂' := le_max_right _ _
  set B := (1 + C₁' * (|T| + 1) + C₁' + C₂') ^ 9 with hB
  have hB0 : 0 ≤ B := by positivity
  set W₀ := max (max Ws W₁) (max W₂ 1) with hW₀
  let δ : ℕ → ℕ → ℝ := fun W _ => if W₀ ≤ W then Cs * B * ((Real.sqrt W)⁻¹) ^ 3
    else 2 + transportD0 b E * W + dStar b * Kq * K
  refine ⟨δ, ?_, ?_⟩
  · intro W j D hD' hDε hj0 hjT a ha
    have ha0 : 0 < a := lt_of_lt_of_le (inv_pos.mpr hK0) ha.1
    obtain ⟨hint, heq⟩ := remainder_eq_integral b E hq0 D j ha0
    rw [heq]
    have hqv : q (((j + 1 : ℕ) : ℝ) / W) ∈ Icc 0 Kq := ⟨hq0 _, hqK _⟩
    by_cases hW : W₀ ≤ W
    · simp only [δ, hW, ite_true]
      have hWs : Ws ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
      have hW1' : W₁ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
      have hW2' : W₂ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
      have hWpos : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
      have hW0 : (0 : ℝ) < W := by linarith
      obtain ⟨hjet, hgam⟩ := hOI' W hW1' D hD' (hDε.trans (min_le_left _ _))
      have hδ := hjet s hs j hj0 hjT
      have hγ := hgam j hjT
      have hZS := hCM W hW2' D hD' (hDε.trans (min_le_right _ _)) j hj0 hjT
      have hγ' : eLpNorm (oneEndedGamma b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₁' * (|T| + 1)) := by
        refine hγ.trans (ENNReal.ofReal_le_ofReal ?_)
        have ht := time_le hW1 hjT
        calc C₁ * ((j : ℝ) + 1) / W ≤ C₁' * (((j : ℝ) + 1) / W) := by
              rw [mul_div_assoc]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ C₁' * (|T| + 1) := mul_le_mul_of_nonneg_left ht hC₁0
      have hδ' : eLpNorm (fun ω => jetDistance0 b E (oneEndedX E D j ω)) (ENNReal.ofReal 9)
            (oneEndedLaw W b j) +
          eLpNorm (fun ω => jetDistance1 b E s (oneEndedX E D j ω)) (ENNReal.ofReal 9)
            (oneEndedLaw W b j) ≤ ENNReal.ofReal (C₁' / W) :=
        hδ.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _)
          hW0.le))
      have hZS' : eLpNorm (openClockZ b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) +
          eLpNorm (openClockSqrtS b E q D j) (ENNReal.ofReal 9) (oneEndedLaw W b j) ≤
          ENNReal.ofReal (C₂' / Real.sqrt W) :=
        hZS.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _)
          (Real.sqrt_nonneg _)))
      obtain ⟨hΛi, hΛ⟩ := pastWeight_moment (s := s) hq0 hW0 (by positivity) hC₁0 hC₂0 hγ' hδ'
        hZS'
      have hae : ∀ᵐ ω ∂oneEndedLaw W b j,
          |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ≤
          Cs * pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9 *
            ((Real.sqrt W)⁻¹) ^ 3 := by
        filter_upwards [ae_blocks_isHermitian (W := W) b j] with ω hω
        exact hstep W hWs (oneEndedX E D j ω) (X_isHermitian E hD' j ω hω)
          (oneEndedQ b E q D j ω) (Q_posSemidef b E hq0 D j ω) a ha _ hqv
      have hbi : Integrable (fun ω => Cs * pastWeight W b E s (oneEndedX E D j ω)
          (oneEndedQ b E q D j ω) ^ 9 * ((Real.sqrt W)⁻¹) ^ 3) (oneEndedLaw W b j) :=
        (hΛi.const_mul Cs).mul_const _
      calc |∫ ω, stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω) ∂oneEndedLaw W b j|
          ≤ ∫ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ∂oneEndedLaw W b j := abs_integral_le_integral_abs
        _ ≤ ∫ ω, Cs * pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9 *
            ((Real.sqrt W)⁻¹) ^ 3 ∂oneEndedLaw W b j := integral_mono_ae hint.abs hbi hae
        _ = Cs * (∫ ω, pastWeight W b E s (oneEndedX E D j ω) (oneEndedQ b E q D j ω) ^ 9
            ∂oneEndedLaw W b j) * ((Real.sqrt W)⁻¹) ^ 3 := by
          rw [integral_mul_const, integral_const_mul]
        _ ≤ Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := by
          gcongr
    · simp only [δ, hW, ite_false]
      refine (abs_integral_le_integral_abs).trans ?_
      have hcst : ∀ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
          (oneEndedQ b E q D j ω)| ≤ 2 + transportD0 b E * W + dStar b * Kq * K := fun ω =>
        stepDefect_trivial (Q_posSemidef b E hq0 D j ω) ha0.le ha.2 hqv.1 hqv.2 hD hd
      calc ∫ ω, |stepDefect W b E (q (((j + 1 : ℕ) : ℝ) / W)) a (oneEndedX E D j ω)
            (oneEndedQ b E q D j ω)| ∂oneEndedLaw W b j
          ≤ ∫ _ω, (2 + transportD0 b E * W + dStar b * Kq * K) ∂oneEndedLaw W b j :=
            integral_mono hint.abs (integrable_const _) hcst
        _ = 2 + transportD0 b E * W + dStar b * Kq * K := by simp
  · -- the sum tends to zero
    have hsq : Tendsto (fun W : ℕ => (Real.sqrt W)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hlim : Tendsto (fun W : ℕ => (|T| + 1) * (Cs * B) * (Real.sqrt W)⁻¹) atTop (𝓝 0) := by
      have := hsq.const_mul ((|T| + 1) * (Cs * B))
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun W => ?_) ?_ hlim
    · refine Finset.sum_nonneg fun j _ => ?_
      simp only [δ]
      split_ifs
      · positivity
      · have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
        positivity
    · filter_upwards [eventually_ge_atTop W₀] with W hW
      have hWpos : 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hWpos
      have hW0 : (0 : ℝ) < W := by linarith
      have hsW0 : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW0
      have hδW : ∀ j, δ W j = Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := fun j => by
        simp only [δ, hW, ite_true]
      rw [Finset.sum_congr rfl (fun j _ => hδW j), Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc (openEntranceTime W) ⌊T * W⌋₊).card : ℝ) ≤ (|T| + 1) * W := by
        rw [Nat.card_Icc]
        have h1 : ((⌊T * W⌋₊ + 1 - openEntranceTime W : ℕ) : ℝ) ≤ (⌊T * W⌋₊ : ℝ) + 1 := by
          have : ⌊T * W⌋₊ + 1 - openEntranceTime W ≤ ⌊T * W⌋₊ + 1 := Nat.sub_le _ _
          exact_mod_cast this
        have h2 : (⌊T * W⌋₊ : ℝ) ≤ |T| * W := by
          by_cases hx : 0 ≤ T * W
          · exact (Nat.floor_le hx).trans (mul_le_mul_of_nonneg_right (le_abs_self T) hW0.le)
          · rw [Nat.floor_of_nonpos (le_of_not_ge hx), Nat.cast_zero]; positivity
        have h3 : (|T| + 1) * (W : ℝ) = |T| * W + W := by ring
        linarith
      have hw : (W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3 = (Real.sqrt W)⁻¹ := by
        have h : Real.sqrt W ^ 2 = (W : ℝ) := Real.sq_sqrt hW0.le
        have hne : Real.sqrt W ≠ 0 := hsW0.ne'
        calc (W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3 = Real.sqrt W ^ 2 * ((Real.sqrt W)⁻¹) ^ 3 := by
              rw [h]
          _ = (Real.sqrt W)⁻¹ := by field_simp
      have hCB : 0 ≤ Cs * B * ((Real.sqrt W)⁻¹) ^ 3 := by positivity
      calc ((Finset.Icc (openEntranceTime W) ⌊T * W⌋₊).card : ℝ) * (Cs * B * ((Real.sqrt W)⁻¹) ^ 3)
          ≤ (|T| + 1) * W * (Cs * B * ((Real.sqrt W)⁻¹) ^ 3) :=
            mul_le_mul_of_nonneg_right hcard hCB
        _ = (|T| + 1) * (Cs * B) * ((W : ℝ) * ((Real.sqrt W)⁻¹) ^ 3) := by ring
        _ = (|T| + 1) * (Cs * B) * (Real.sqrt W)⁻¹ := by rw [hw]

/-- **The deterministic-clock lemma** (`DetClockEvolution`, with `X₀ = 0`), from the same
five hypotheses as `detClockEvolutionD_of`. -/
theorem detClockEvolution_of (hPSM : PassiveSourceMixingContract)
    (hPC : PassiveCovarianceContract) (hGA : GaussianAbsorptionContract)
    (hWC : BlockBand.Internal.Contracts.LayersOnePort.OnePortWeightedCovarianceContract)
    (hOI : OpenInputsMoments) : DetClockEvolution :=
  detClockEvolution_of_D (detClockEvolutionD_of hPSM hPC hGA hWC hOI)

end BlockBand.Endpoints.Clock
