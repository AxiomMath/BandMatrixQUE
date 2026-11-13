module

public import BlockBand.SourceProcess.PhysApprox.B3StepBridge
public import BlockBand.SourceProcess.RawTag.AbstractStep
public import BlockBand.Transmission.PathScalar.Dissipative

/-!
# One closed fresh step at order 8 with frames controlled by the entry

For the unstopped closed diagonal entry `x = (𝒦_cl)_ll`, the frames of the exact update are
controlled by the entry itself (closed Ward identity: `‖u‖‖v‖ ≤ η⁻¹|x|`), not by a stop. Then
one fresh step is **multiplicative**:

* **`lintegral_fresh_eight_le`** (from `GaussianAbsorptionContract`,
  `GaussianLpGradient`): for passive `X` and `‖u‖‖v‖ ≤ c|x|`,
  `E_F|x + u*Δ(X, F)v|⁸ ≤ |x|⁸ exp(Γ(δ₀(X) + W⁻¹))`. The proof is that of
  `RawTag.lintegral_fresh_step` with the Young parameter `W_r = ε_M/ε`, `ε = δ₀ + W⁻¹`, and the
  deterministic port bound `δ₀ ≤ η⁻¹ + 1`; no `W^{2m-1}` loss survives.
* **`lintegral_closed_eight_le`** (by the fresh-layer Fubini `closedPastFreshLaw_holds`): the same
  under `closedLaw` with any nonnegative weight `g` that is a function of the past.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.KDiag

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ComplexSourceLaw
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W np : ℕ}

/-!
## The real inequality
-/

/-- The real inequality behind one fresh step at order 8: with `W_r = ε_M/ε`,
`(1 + K/W_r)μ⁸ + K W_r³ s⁸ ≤ t⁸ exp(Γε)` when `μ ≤ t(1 + C ε)` and `s² ≤ aεt²`. -/
theorem real_step_eight {t μn s ε εM K Cmc a : ℝ} (hε0 : 0 < ε)
    (hεM : ε ≤ εM) (hK : 0 ≤ K) (hCmc : 0 ≤ Cmc) (hμ0 : 0 ≤ μn)
    (hμ : μn ≤ t * (1 + Cmc * ε)) (hs : s ^ 2 ≤ a * ε * t ^ 2) :
    (1 + K / (εM / ε)) * μn ^ 8 + K * (εM / ε) ^ 3 * s ^ 8 ≤
      t ^ 8 * Real.exp ((K / εM + 8 * Cmc + K * εM ^ 3 * a ^ 4) * ε) := by
  have hεM0 : 0 < εM := hε0.trans_le hεM
  have e1 : K / (εM / ε) = K / εM * ε := by
    rw [div_div_eq_mul_div]
    ring
  have hA : 1 + K / (εM / ε) ≤ Real.exp (K / εM * ε) := by
    rw [e1]
    linarith [Real.add_one_le_exp (K / εM * ε)]
  have hB : μn ^ 8 ≤ t ^ 8 * Real.exp (8 * Cmc * ε) := by
    have h1 : μn ^ 8 ≤ (t * (1 + Cmc * ε)) ^ 8 := pow_le_pow_left₀ hμ0 hμ 8
    have h2 : (1 + Cmc * ε) ^ 8 ≤ Real.exp (Cmc * ε) ^ 8 :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Cmc * ε)]) 8
    rw [← Real.exp_nat_mul] at h2
    calc μn ^ 8 ≤ (t * (1 + Cmc * ε)) ^ 8 := h1
      _ = t ^ 8 * (1 + Cmc * ε) ^ 8 := mul_pow _ _ _
      _ ≤ t ^ 8 * Real.exp (8 * Cmc * ε) := by
          refine mul_le_mul_of_nonneg_left (h2.trans_eq ?_) (by positivity)
          congr 1
          push_cast
          ring
  have hC : s ^ 8 ≤ (a * ε * t ^ 2) ^ 4 := by
    rw [show s ^ 8 = (s ^ 2) ^ 4 by ring]
    exact pow_le_pow_left₀ (by positivity) hs 4
  have hD : K * (εM / ε) ^ 3 * s ^ 8 ≤ t ^ 8 * (K * εM ^ 3 * a ^ 4 * ε) := by
    calc K * (εM / ε) ^ 3 * s ^ 8 ≤ K * (εM / ε) ^ 3 * (a * ε * t ^ 2) ^ 4 :=
          mul_le_mul_of_nonneg_left hC (by positivity)
      _ = K * ((εM / ε) ^ 3 * ε ^ 3) * a ^ 4 * ε * t ^ 8 := by ring
      _ = t ^ 8 * (K * εM ^ 3 * a ^ 4 * ε) := by
          rw [← mul_pow, div_mul_cancel₀ _ hε0.ne']
          ring
  set P := Real.exp (K / εM * ε) * Real.exp (8 * Cmc * ε) with hP
  have hP1 : 1 ≤ P := by
    have h1 := Real.one_le_exp (show 0 ≤ K / εM * ε by positivity)
    have h2 := Real.one_le_exp (show 0 ≤ 8 * Cmc * ε by positivity)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hQ : 0 ≤ K * εM ^ 3 * a ^ 4 * ε := by positivity
  calc (1 + K / (εM / ε)) * μn ^ 8 + K * (εM / ε) ^ 3 * s ^ 8
      ≤ Real.exp (K / εM * ε) * (t ^ 8 * Real.exp (8 * Cmc * ε)) +
          t ^ 8 * (K * εM ^ 3 * a ^ 4 * ε) :=
        add_le_add (mul_le_mul hA hB (by positivity) (Real.exp_pos _).le) hD
    _ = t ^ 8 * (P + K * εM ^ 3 * a ^ 4 * ε) := by
        rw [hP]
        ring
    _ ≤ t ^ 8 * (P * (1 + K * εM ^ 3 * a ^ 4 * ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [mul_nonneg (sub_nonneg.2 hP1) hQ]
    _ ≤ t ^ 8 * (P * Real.exp (K * εM ^ 3 * a ^ 4 * ε)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by linarith))
          (by positivity)
        linarith [Real.add_one_le_exp (K * εM ^ 3 * a ^ 4 * ε)]
    _ = t ^ 8 * Real.exp ((K / εM + 8 * Cmc + K * εM ^ 3 * a ^ 4) * ε) := by
        rw [hP, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-!
## One fresh step at a fixed past
-/

/-- **One fresh step at order 8 with frames controlled by the entry** (from the contract hypotheses):
for passive `X` and `‖u‖‖v‖ ≤ c|x|`, `E_F|x + u*Δ(X, F)v|⁸ ≤ |x|⁸ exp(Γ(δ₀(X) + W⁻¹))`, uniformly
in `W ≥ W₀`, `X`, `x`, `u`, `v`. -/
theorem lintegral_fresh_eight_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {c : ℝ}
    (hc : 0 ≤ c) :
    ∃ (Γ : ℝ) (W₀ : ℕ), 0 ≤ Γ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ (x : ℂ) (u v : Fin W → ℂ),
        vecNorm u * vecNorm v ≤ c * ‖x‖ →
        ∫⁻ F, ENNReal.ofReal ((‖x + bilinear u (freshDelta b E X F) v‖ ^ 2) ^ 4)
            ∂freshLaw W b ≤
          ENNReal.ofReal ((‖x‖ ^ 2) ^ 4 *
            Real.exp (Γ * (jetDistance0 b E X + (W : ℝ)⁻¹))) := by
  obtain ⟨hκ, hEκ⟩ := StepFresh.bulk_of_lt hE1 hE2
  obtain ⟨Cm, Cf, W₁, hCm, hCf, hDl⟩ :=
    RawTag.delta_fresh_bounds hGA hLp b hb0 hb _ hκ 8 (by norm_num)
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) hE1 hE2
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (etaZ b E)⁻¹ + 1 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have := inv_pos.2 hη
    linarith
  obtain ⟨εM, hεMdef⟩ : ∃ εM : ℝ, εM = D + 1 := ⟨_, rfl⟩
  have hεM0 : 0 < εM := by
    rw [hεMdef]
    linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = RawTag.stepK 4 := ⟨_, rfl⟩
  have hK : 0 ≤ K := hKdef ▸ (RawTag.stepK_pos 4).le
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 2 * Cf ^ 2 * c ^ 2 * (1 + D) := ⟨_, rfl⟩
  have ha : 0 ≤ a := by
    rw [hadef]
    have : 0 ≤ 1 + D := by linarith
    positivity
  obtain ⟨Cmc, hCmcdef⟩ : ∃ Cmc : ℝ, Cmc = Cm * c := ⟨_, rfl⟩
  have hCmc : 0 ≤ Cmc := hCmcdef ▸ mul_nonneg hCm hc
  have hΓ : 0 ≤ K / εM + 8 * Cmc + K * εM ^ 3 * a ^ 4 := by
    have h1 : 0 ≤ K / εM := div_nonneg hK hεM0.le
    have h2 : 0 ≤ K * εM ^ 3 * a ^ 4 := by positivity
    linarith
  refine ⟨K / εM + 8 * Cmc + K * εM ^ 3 * a ^ 4, max W₁ 1, hΓ,
    fun W hW X hX x u v huv => ?_⟩
  have hW₁ : W₁ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast le_trans (le_max_right _ _) hW
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hI, hmean, hF⟩ := hDl W hW₁ E hEκ X hX
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδD : jetDistance0 b E X ≤ D := hDdef ▸ jetDistance0_le_bound hb0 hb hE1 hE2 hX
  have hWi0 : 0 < (W : ℝ)⁻¹ := inv_pos.2 hW0
  have hWinv : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  generalize hδdef : jetDistance0 b E X = δ at hmean hF hδ0 hδD ⊢
  have hε0 : 0 < δ + (W : ℝ)⁻¹ := by linarith
  have hεM : δ + (W : ℝ)⁻¹ ≤ εM := by
    rw [hεMdef]
    linarith
  generalize hMdef : matrixExpect (freshLaw W b) (freshDelta b E X) = M at hmean hF
  have hdecomp : ∀ F, x + bilinear u (freshDelta b E X F) v =
      (x + bilinear u M v) + bilinear u (freshDelta b E X F - M) v := by
    intro F
    rw [RawTag.bilinear_sub_mid]
    ring
  have hDM : ∀ i j, Integrable (fun F => (freshDelta b E X F - M) i j) (freshLaw W b) :=
    fun i j => (hI i j).sub (integrable_const _)
  have hdi : Integrable (fun F => bilinear u (freshDelta b E X F - M) v) (freshLaw W b) :=
    FullSource.integrable_bilinear (fun F => freshDelta b E X F - M) hDM u v
  have hd0 : ∫ F, bilinear u (freshDelta b E X F - M) v ∂freshLaw W b = 0 := by
    have e : ∀ F, bilinear u (freshDelta b E X F - M) v =
        bilinear u (freshDelta b E X F) v - bilinear u M v := fun F =>
      RawTag.bilinear_sub_mid _ _ _ _
    simp_rw [e]
    rw [integral_sub (FullSource.integrable_bilinear _ hI u v) (integrable_const _),
      FullSource.integral_bilinear (freshDelta b E X) hI, hMdef, integral_const, probReal_univ,
      one_smul, sub_self]
  have hWr : 1 ≤ εM / (δ + (W : ℝ)⁻¹) := by
    rw [le_div_iff₀ hε0]
    linarith
  have hWr0 : 0 < εM / (δ + (W : ℝ)⁻¹) := by linarith
  have hstep := RawTag.lintegral_fresh_step (x + bilinear u M v) hdi hd0 (m := 2) (by norm_num)
    hWr
  simp only [Nat.reduceMul, Nat.reduceSub] at hstep
  rw [← hKdef] at hstep
  have hu0 := vecNorm_nonneg u
  have hv0 := vecNorm_nonneg v
  have hs0 : 0 ≤ Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v := by positivity
  have hFl : eLpNorm (fun F => bilinear u (freshDelta b E X F - M) v)
      (ENNReal.ofReal (4 * ((2 : ℕ) : ℝ))) (freshLaw W b) ≤
      ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) := by
    have e : (4 * ((2 : ℕ) : ℝ)) = 8 := by norm_num
    rw [e]
    exact hF u v
  have hdm := RawTag.lintegral_pow_le_of_eLpNorm hdi.aestronglyMeasurable (m := 2)
    (by norm_num) hs0 hFl
  simp only [Nat.reduceMul] at hdm
  have hnx : 0 ≤ ‖x‖ := norm_nonneg x
  have huv0 : 0 ≤ vecNorm u * vecNorm v := mul_nonneg hu0 hv0
  have hμ : ‖x + bilinear u M v‖ ≤ ‖x‖ * (1 + Cmc * (δ + (W : ℝ)⁻¹)) := by
    have h1 : ‖bilinear u M v‖ ≤ Cm * (δ + (W : ℝ)⁻¹) * (c * ‖x‖) := by
      refine (norm_bilinear_le u M v).trans ?_
      calc vecNorm u * ‖M‖ * vecNorm v = ‖M‖ * (vecNorm u * vecNorm v) := by ring
        _ ≤ (Cm * (δ + (W : ℝ)⁻¹)) * (c * ‖x‖) :=
            mul_le_mul hmean huv huv0 (mul_nonneg hCm hε0.le)
    calc ‖x + bilinear u M v‖ ≤ ‖x‖ + ‖bilinear u M v‖ := norm_add_le _ _
      _ ≤ ‖x‖ + Cm * (δ + (W : ℝ)⁻¹) * (c * ‖x‖) := by linarith
      _ = ‖x‖ * (1 + Cmc * (δ + (W : ℝ)⁻¹)) := by
          rw [hCmcdef]
          ring
  have hs2 : (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) ^ 2 ≤
      a * (δ + (W : ℝ)⁻¹) * ‖x‖ ^ 2 := by
    have h1 : Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v ≤
        Cf * ((Real.sqrt W)⁻¹ + δ) * (c * ‖x‖) := by
      rw [mul_assoc (Cf * ((Real.sqrt W)⁻¹ + δ))]
      exact mul_le_mul_of_nonneg_left huv (by positivity)
    have e : ((Real.sqrt W)⁻¹) ^ 2 = (W : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hW0.le]
    have h3 : δ ^ 2 ≤ D * δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hδD hδ0
    have h2 : ((Real.sqrt W)⁻¹ + δ) ^ 2 ≤ 2 * ((1 + D) * (δ + (W : ℝ)⁻¹)) := by
      have e1 : 2 * (((Real.sqrt W)⁻¹) ^ 2 + δ ^ 2) - ((Real.sqrt W)⁻¹ + δ) ^ 2 =
          ((Real.sqrt W)⁻¹ - δ) ^ 2 := by ring
      have e2 : (1 + D) * (δ + (W : ℝ)⁻¹) = δ + (W : ℝ)⁻¹ + D * δ + D * (W : ℝ)⁻¹ := by ring
      have h4 := sq_nonneg ((Real.sqrt W)⁻¹ - δ)
      have h5 := mul_nonneg hD0 hWi0.le
      rw [e] at e1
      rw [e2]
      linarith
    calc (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) ^ 2
        ≤ (Cf * ((Real.sqrt W)⁻¹ + δ) * (c * ‖x‖)) ^ 2 := pow_le_pow_left₀ hs0 h1 2
      _ = Cf ^ 2 * c ^ 2 * ‖x‖ ^ 2 * ((Real.sqrt W)⁻¹ + δ) ^ 2 := by ring
      _ ≤ Cf ^ 2 * c ^ 2 * ‖x‖ ^ 2 * (2 * ((1 + D) * (δ + (W : ℝ)⁻¹))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = a * (δ + (W : ℝ)⁻¹) * ‖x‖ ^ 2 := by
          rw [hadef]
          ring
  have hreal := real_step_eight hε0 hεM hK hCmc (norm_nonneg _) hμ hs2
  have hKWr : 0 ≤ 1 + K / (εM / (δ + (W : ℝ)⁻¹)) := by
    have := div_nonneg hK hWr0.le
    linarith
  have hKW3 : 0 ≤ K * (εM / (δ + (W : ℝ)⁻¹)) ^ 3 := mul_nonneg hK (pow_nonneg hWr0.le _)
  have h₁ : 0 ≤ (1 + K / (εM / (δ + (W : ℝ)⁻¹))) * (‖x + bilinear u M v‖ ^ 2) ^ 4 :=
    mul_nonneg hKWr (by positivity)
  have h₂ : 0 ≤ K * (εM / (δ + (W : ℝ)⁻¹)) ^ 3 *
      (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) ^ 8 :=
    mul_nonneg hKW3 (by positivity)
  calc ∫⁻ F, ENNReal.ofReal ((‖x + bilinear u (freshDelta b E X F) v‖ ^ 2) ^ 4) ∂freshLaw W b
      = ∫⁻ F, ENNReal.ofReal ((‖(x + bilinear u M v) +
          bilinear u (freshDelta b E X F - M) v‖ ^ 2) ^ 4) ∂freshLaw W b := by
        refine lintegral_congr fun F => ?_
        rw [hdecomp]
    _ ≤ ENNReal.ofReal ((1 + K / (εM / (δ + (W : ℝ)⁻¹))) * (‖x + bilinear u M v‖ ^ 2) ^ 4) +
          ENNReal.ofReal (K * (εM / (δ + (W : ℝ)⁻¹)) ^ 3) *
            ENNReal.ofReal ((Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) ^ 8) :=
        hstep.trans (add_le_add le_rfl (mul_le_mul_right hdm _))
    _ = ENNReal.ofReal ((1 + K / (εM / (δ + (W : ℝ)⁻¹))) * ‖x + bilinear u M v‖ ^ 8 +
          K * (εM / (δ + (W : ℝ)⁻¹)) ^ 3 *
            (Cf * ((Real.sqrt W)⁻¹ + δ) * vecNorm u * vecNorm v) ^ 8) := by
        rw [← ENNReal.ofReal_mul hKW3, ← ENNReal.ofReal_add h₁ h₂]
        congr 1
        ring
    _ ≤ ENNReal.ofReal ((‖x‖ ^ 2) ^ 4 *
          Real.exp ((K / εM + 8 * Cmc + K * εM ^ 3 * a ^ 4) * (δ + (W : ℝ)⁻¹))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show (‖x‖ ^ 2) ^ 4 = ‖x‖ ^ 8 by ring]
        exact hreal

/-!
## One fresh step under the closed law, with a weight that is a function of the past
-/

theorem measurable_vecNorm_comp {α : Type*} [MeasurableSpace α] {f : α → Fin W → ℂ}
    (hf : Measurable f) : Measurable fun a => vecNorm (f a) :=
  Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hf).norm.pow_const 2)

/-- **One closed fresh step at order 8 with a past weight** (contract hypotheses and fresh-layer
Fubini): for Borel `b3Ext W j`-invariant `g ≥ 0`, `x`, `u`, `v`, `X` with `X` a.e. passive and
`‖u‖‖v‖ ≤ c|x|` a.e., `E[g|x + u*Δ(X, F_j)v|⁸] ≤ E[g|x|⁸ exp(Γ(δ₀(X) + W⁻¹))]`. -/
theorem lintegral_closed_eight_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) {c : ℝ}
    (hc : 0 ≤ c) :
    ∃ (Γ : ℝ) (W₀ : ℕ), 0 ≤ Γ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ (np j : ℕ)
      (g : ProbedPath W np × ℝ → ℝ≥0∞) (x : ProbedPath W np × ℝ → ℂ)
      (u v : ProbedPath W np × ℝ → Fin W → ℂ)
      (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ),
      Measurable g → Measurable x → Measurable u → Measurable v → Measurable X →
      (∀ y, g (b3Ext W j y) = g y) → (∀ y, x (b3Ext W j y) = x y) →
      (∀ y, u (b3Ext W j y) = u y) → (∀ y, v (b3Ext W j y) = v y) →
      (∀ y, X (b3Ext W j y) = X y) →
      (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) →
      (∀ᵐ y ∂closedLaw b W np, vecNorm (u y) * vecNorm (v y) ≤ c * ‖x y‖) →
        ∫⁻ y, g y * ENNReal.ofReal ((‖x y + bilinear (u y)
            (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ ^ 2) ^ 4)
            ∂closedLaw b W np ≤
          ∫⁻ y, g y * ENNReal.ofReal ((‖x y‖ ^ 2) ^ 4 *
            Real.exp (Γ * (jetDistance0 b E (X y) + (W : ℝ)⁻¹))) ∂closedLaw b W np := by
  obtain ⟨Γ, W₀, hΓ, H⟩ := lintegral_fresh_eight_le hGA hLp hb0 hb hE1 hE2 hc
  refine ⟨Γ, W₀, hΓ, fun W hW np j g x u v X hg hx hu hv hX hg' hx' hu' hv' hX' hpas hfr =>
    ?_⟩
  set μ := closedLaw b W np
  set μP := (pastLaw W j b).prod
    ((Measure.pi fun _ : Fin np => circularVectorLaw (Fin W)).prod phaseLaw)
  set π : ProbedPath W np × ℝ → PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) :=
    fun y => (pastCoords W j y.1.1, (y.1.2, y.2))
  set r : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → ProbedPath W np × ℝ :=
    fun p => ((extPast W j p.1, p.2.1), p.2.2)
  have hπ : Measurable π := measurable_b3Sigma_map W j np
  have hr : Measurable r :=
    (((measurable_extPast j).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)
  set φ : ProbedPath W np × ℝ → LayerSample W .oneBlockOnePort := fun y => freshSample W j y.1.1
  have hφ : Measurable φ := (measurable_freshSample W j).comp (measurable_fst.comp measurable_fst)
  have hmap : μ.map (fun y => (π y, φ y)) = μP.prod (freshLaw W b) :=
    closedPastFreshLaw_holds b W np j
  have hmapπ : μ.map π = μP := by
    have h := congrArg (fun m => m.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
      one_smul] at h
    exact h
  have hrπ : ∀ y, r (π y) = b3Ext W j y := fun y => rfl
  have hpasP : ∀ᵐ p ∂μP, (passiveY (X (r p))).PosSemidef := by
    have hset : MeasurableSet {p | (passiveY (X (r p))).PosSemidef} :=
      (hX.comp hr) step_measurableSet_passive
    rw [← hmapπ, ae_map_iff hπ.aemeasurable hset]
    filter_upwards [hpas] with y hy
    rw [hrπ, hX']
    exact hy
  have hfrP : ∀ᵐ p ∂μP, vecNorm (u (r p)) * vecNorm (v (r p)) ≤ c * ‖x (r p)‖ := by
    have hset : MeasurableSet {p | vecNorm (u (r p)) * vecNorm (v (r p)) ≤ c * ‖x (r p)‖} :=
      measurableSet_le ((measurable_vecNorm_comp (hu.comp hr)).mul
        (measurable_vecNorm_comp (hv.comp hr))) (measurable_const.mul (hx.comp hr).norm)
    rw [← hmapπ, ae_map_iff hπ.aemeasurable hset]
    filter_upwards [hfr] with y hy
    show vecNorm (u (r (π y))) * vecNorm (v (r (π y))) ≤ c * ‖x (r (π y))‖
    rw [hrπ, hu', hv', hx']
    exact hy
  have hDm : Measurable fun z : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => freshDelta b E (X (r z.1)) z.2 :=
    FullSource.measurable_freshDelta_comp b E ((hX.comp hr).comp measurable_fst) measurable_snd
  set Φ : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort →
      ℝ≥0∞ := fun z => g (r z.1) * ENNReal.ofReal ((‖x (r z.1) + bilinear (u (r z.1))
        (freshDelta b E (X (r z.1)) z.2) (v (r z.1))‖ ^ 2) ^ 4) with hΦdef
  have hΦ : Measurable Φ :=
    ((hg.comp hr).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp
      (((((hx.comp hr).comp measurable_fst).add (RawTag.measurable_bilinear_jt
        ((hu.comp hr).comp measurable_fst) hDm ((hv.comp hr).comp measurable_fst))).norm.pow_const
          2).pow_const 4))
  set Ψ : PastSample W j × ((Fin np → Fin W → ℂ) × ℝ) → ℝ≥0∞ := fun p =>
    g (r p) * ENNReal.ofReal ((‖x (r p)‖ ^ 2) ^ 4 *
      Real.exp (Γ * (jetDistance0 b E (X (r p)) + (W : ℝ)⁻¹))) with hΨdef
  have hΨ : Measurable Ψ :=
    (hg.comp hr).mul (ENNReal.measurable_ofReal.comp ((((hx.comp hr).norm.pow_const 2).pow_const
      4).mul (Real.measurable_exp.comp (measurable_const.mul
        (((measurable_jetDistance0 (W := W) b E).comp (hX.comp hr)).add measurable_const)))))
  calc ∫⁻ y, g y * ENNReal.ofReal ((‖x y + bilinear (u y)
          (freshDelta b E (X y) (freshSample W j y.1.1)) (v y)‖ ^ 2) ^ 4) ∂μ
      = ∫⁻ y, Φ (π y, φ y) ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Φ, hrπ, hg', hx', hu', hv', hX', φ]
    _ = ∫⁻ z, Φ z ∂(μP.prod (freshLaw W b)) := by
        rw [← hmap, lintegral_map hΦ (hπ.prodMk hφ)]
    _ = ∫⁻ p, ∫⁻ F, Φ (p, F) ∂freshLaw W b ∂μP := lintegral_prod _ hΦ.aemeasurable
    _ ≤ ∫⁻ p, Ψ p ∂μP := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpasP, hfrP] with p hp hq
        have hin : Measurable fun F => ENNReal.ofReal ((‖x (r p) + bilinear (u (r p))
            (freshDelta b E (X (r p)) F) (v (r p))‖ ^ 2) ^ 4) :=
          ENNReal.measurable_ofReal.comp (((measurable_const.add (RawTag.measurable_bilinear_jt
            measurable_const (FullSource.measurable_freshDelta_comp b E measurable_const
              measurable_id) measurable_const)).norm.pow_const 2).pow_const 4)
        simp only [Φ, Ψ]
        rw [lintegral_const_mul _ hin]
        exact mul_le_mul_right (H W hW (X (r p)) hp (x (r p)) (u (r p)) (v (r p)) hq) _
    _ = ∫⁻ y, Ψ (π y) ∂μ := by rw [← hmapπ, lintegral_map hΨ hπ]
    _ = ∫⁻ y, g y * ENNReal.ofReal ((‖x y‖ ^ 2) ^ 4 *
          Real.exp (Γ * (jetDistance0 b E (X y) + (W : ℝ)⁻¹))) ∂μ := by
        refine lintegral_congr fun y => ?_
        simp only [Ψ, hrπ, hg', hx', hX']

end BlockBand.SourceProcess.PhysApprox.B3.KDiag
