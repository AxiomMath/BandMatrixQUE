module

public import BlockBand.Endpoints.Response.RemoteHigherRecursionBounds
public import BlockBand.Endpoints.Response.RemoteHigherNear
public import BlockBand.Endpoints.Response.NearSchattenProkhorov

/-!
# The higher logistic recursion from the higher one-step inequality

Part of the proof of the remote higher-moment theorem: a proof of the isolated input
`RhnHigherWeightedRecursion`, the `r`-analogue of `ce_logisticRecursion_of_oneStep`.

* `rhnHigherWeightedRecursion_of_oneStep (hECM) (hTLU) (hStep : RhcHigherOneStep)` — the
  finite-`W` recursion `y_{j+1} ≤ y_j + W⁻¹(C' y_j - c' y_j^{1+1/r} + C') + o(W⁻²)` of
  `y_j = E[(1 + Kδ₀) H_p(A_j)^r]`, from the weighted higher one-step inequality
  `RhcHigherOneStep` and `EdgeClockMomentsContract` and `TransmissionLengthUniformContract`.
  Proof:
  - the a priori bound `y_j ≤ 3 A C_Ψ W^r` from `H_p^r ≤ W^r γ^{pr}`;
  - the exceptional sets by Markov at failure order `m = 2⌈r⌉ + 6` on `δ₀, δ₁` (jet moments of
    order `m`) and on `g` (conductance moment of order `m`), paid by a second moment with
    `l = W^{2⌈r⌉+3}` (`rhr_moments_at`);
  - Young/Hölder `E(1_D H_p^{r+1}/γ^p) ≥ (E 1_D H_p^r)^{(r+1)/r}/(1 + C_γ')^{1/r}`
    (`rhr_lintegral_indicator_le_young`, `rhr_rpow_le_of_forall`), with `E γ^{pr} ≤ 1 + C_γ'`;
  - the forcing `E|g|^{(r+1)(1-p)}γ^{pr} ≤ 1 + C_g' + C_γ'` (conductance moment of order
    `m ≥ 2(r+1)(1-p)`, edge-clock moment of order `8pr`);
  - the real algebra `rhr_real_step` (Bernoulli for the split).
  Constants `C' = C + C(1 + C_g' + C_γ')`, `c' = c/((1 + Kd)^{1+1/r}(1 + C_γ')^{1/r})`, chosen
  before the source and the preceding middle; error `max e 0 + A/W³`.
* `remoteHigher_of_onePort` — `RemoteHigherStatement` from the listed contracts, the one-port
  contracts, `OnePortJetContraction` and the isolated `RhHigherLimitDecay` only: composes
  `rhcHigherOneStep_of_onePort`, the above, `remoteHigher_of_recursion` and
  `nsCriticalClockLimitsExist_of_contracts`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.TransmissionUniform

/-- **`RhnHigherWeightedRecursion` from the weighted higher one-step inequality.** Hypotheses:
`EdgeClockMomentsContract`, `TransmissionLengthUniformContract` and `RhcHigherOneStep`. The weight
`K` is that of `RhcHigherOneStep`; the recursion constants `C' = C + C(1 + C_g' + C_γ')` and
`c' = c/((1 + Kd)^{1+1/r}(1 + C_γ')^{1/r})` depend on `b, E, p, r, s₀, s₂` only. -/
theorem rhnHigherWeightedRecursion_of_oneStep (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hStep : RhcHigherOneStep) :
    RhnHigherWeightedRecursion := by
  intro b hb hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  obtain ⟨K, C, c, d, s, hK, hC, hc, hd, hs, hsrc⟩ :=
    hStep b hb hb' E hE hE' p r hp hp' hr hpr s₀ s₂ hs₀ hs₀₂
  have hr0 : 0 < r := by linarith
  set n : ℕ := ⌈r⌉₊ with hn
  have hrn : r ≤ n := Nat.le_ceil r
  set m : ℕ := 2 * n + 6 with hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by rw [hm]; push_cast; linarith
  set κI := min (E + 2) (2 - E) with hκI
  have hκI0 : 0 < κI := lt_min (by linarith) (by linarith)
  have hEI : E ∈ BlockBand.Internal.Contracts.Layers.bulkInterval κI :=
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩
  obtain ⟨Cγ, hCγ⟩ := edgeClockMoments hECM b hb hb' E hE hE' (s₂ + 1) (8 * (p * r))
    (by linarith) (by positivity)
  obtain ⟨CJ, hCJ⟩ := hTLU.jet b hb hb' κI (s₀ / 2) 20 hκI0 (by positivity) (by norm_num)
  obtain ⟨CJm, hCJm⟩ := hTLU.jet b hb hb' κI (s₀ / 2) (m : ℝ) hκI0 (by positivity) hm1
  obtain ⟨CG, hCG⟩ := hTLU.conductance b hb hb' κI (s₀ / 2) (m : ℝ) hκI0 (by positivity) hm1
  set M := 1 + max Cγ 0 with hM
  set Fb := 1 + max CG 0 + max Cγ 0 with hFb
  set AE := rhr_AE K d CJ CJm CG Cγ m with hAE
  set Ay := 3 * ce_A K * ce_CPsi CJ Cγ with hAy
  have hM0 : 0 < M := by have := le_max_right Cγ 0; linarith
  have hFb0 : 0 ≤ Fb := by have := le_max_right CG 0; have := le_max_right Cγ 0; linarith
  have hAE0 : 0 ≤ AE := rhr_AE_nonneg K d CJ CJm CG Cγ m hd
  have hAy0 : 0 ≤ Ay := by
    have := ce_CPsi_nonneg CJ Cγ; have : 0 ≤ ce_A K := by unfold ce_A; positivity
    positivity
  have hKd : 0 < 1 + K * d := by nlinarith
  obtain ⟨Mr, hMr⟩ : ∃ a : ℝ, a = M ^ (1 / r) := ⟨_, rfl⟩
  have hMr0 : 0 < Mr := by rw [hMr]; exact Real.rpow_pos_of_pos hM0 _
  obtain ⟨Ay', hAy'⟩ : ∃ a : ℝ, a = Ay ^ (1 / r) := ⟨_, rfl⟩
  have hAy'0 : 0 ≤ Ay' := by rw [hAy']; exact Real.rpow_nonneg hAy0 _
  obtain ⟨cn, hcn⟩ : ∃ a : ℝ, a = c / ((1 + K * d) ^ (1 + 1 / r) * Mr) := ⟨_, rfl⟩
  have hcn0 : 0 < cn := by
    rw [hcn]; have := Real.rpow_pos_of_pos hKd (1 + 1 / r); positivity
  set Cn := C + C * Fb with hCn
  set Atot := AE + cn * (1 + 1 / r) * Ay' * AE with hAtot
  refine ⟨K, Cn, cn, hK, hcn0, fun t₁ R q hq => ?_⟩
  obtain ⟨ht₁, hR, hR1, hsrcT, hq1⟩ := hq
  have hq0 : ∀ x, 0 ≤ q x := hsrcT.1
  have hinj : IsBoundedInjection t₁ R 1 q := ⟨hq0, hq1, hsrcT.2.1⟩
  obtain ⟨e, he, W₀, hW₀⟩ := hsrc t₁ R q ⟨ht₁, hR, hR1, hsrcT, hq1⟩
  obtain ⟨Wγ, hWγ⟩ := hCγ (t₁ + R + (s₂ + 1))
  obtain ⟨WJ, hWJ⟩ := hCJ (t₁ + R + (s₂ + 1))
  obtain ⟨WJm, hWJm⟩ := hCJm (t₁ + R + (s₂ + 1))
  obtain ⟨WG, hWG⟩ := hCG (t₁ + R + (s₂ + 1))
  refine ⟨fun W => max (e W) 0 + Atot / (W : ℝ) ^ 3, ?_,
    max (max W₀ Wγ) (max (max WJ WG) (max WJm (⌈4 / s₀⌉₊ + 1))), fun W hW => ?_⟩
  · -- the error is `o(W⁻²)`
    have h1 : Tendsto (fun W : ℕ => max ((W : ℝ) ^ 2 * e W) 0) atTop (𝓝 0) := by
      simpa using he.max (tendsto_const_nhds (x := (0 : ℝ)))
    have h2 : Tendsto (fun W : ℕ => Atot / (W : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := h1.add h2
    rw [add_zero] at h
    refine h.congr fun W => ?_
    rw [mul_add, mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero]
    congr 1
    rcases (Nat.cast_nonneg W : (0 : ℝ) ≤ W).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · field_simp
  · simp only [max_le_iff] at hW
    obtain ⟨⟨hW0', hWγ'⟩, ⟨hWJ', hWG'⟩, hWJm', hWc⟩ := hW
    have hW1 : (1 : ℝ) ≤ W := by
      have : 1 ≤ W := le_trans (Nat.le_add_left 1 _) hWc
      exact_mod_cast this
    have hW0 : (0 : ℝ) < W := by linarith
    have hWs : 4 ≤ (W : ℝ) * s₀ := by
      have h1 : 4 / s₀ ≤ (⌈4 / s₀⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈4 / s₀⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hWc
      push_cast at h2
      have : 4 / s₀ ≤ W := by linarith
      rwa [div_le_iff₀ hs₀] at this
    have hTR : 0 ≤ t₁ + R := by linarith
    have hmom := fun j (h0 : travelLength W t₁ R s₀ ≤ j) (h2 : j ≤ travelLength W t₁ R s₂) =>
      have hr' := ce_range hTR hs₀ hs₀₂ hWs h0 h2
      have hjet := hWJ W hWJ' E hEI s hs j hr'.1 hr'.2
      have hjetm := hWJm W hWJm' E hEI s hs j hr'.1 hr'.2
      rhr_moments_at (s := s) (n := n) hp hp' hr hrn hK hd hW1 hq0 (le_trans le_self_add hjet)
        (le_trans le_self_add hjetm) (le_trans le_add_self hjetm)
        (hWG W hWG' E hEI j hr'.1 hr'.2)
        ((hWγ W hWγ' t₁ R 1 q ht₁ hR (by linarith) le_rfl hinj j hr'.2).2)
    refine ⟨fun j h0 h2 => ?_, fun j h0 h2 => ?_⟩
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmom j h0 h2).1
    · obtain ⟨hY1, hDc, -, hsplit, hyo, hXY, hFm⟩ := hmom j h0 h2.le
      obtain ⟨hY1', -, hsplit', -⟩ := hmom (j + 1) (by omega) h2
      have hstep := hW₀ W hW0' j h0 h2
      set Y := rhn_weightedHigherMoment K b E p r W j q with hY
      set Y' := rhn_weightedHigherMoment K b E p r W (j + 1) q with hY'
      set Rn := rhc_retainedNext K b E p r s d W j q with hRn
      set X := ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
        (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂growthPathLaw W b with hX
      set N := rhc_concavityMoment b E p r s d W j q with hN
      set Fm := rhc_forcingMoment b E p r W j q with hFm'
      -- the exceptional part of the new length, on the old domain's complement
      have hYRn : Y' ≤ Rn + ENNReal.ofReal (AE / (W : ℝ) ^ 3) := hsplit' _ hDc
      have hYf : Y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY1
      have hY'f : Y' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY1'
      have hRnf : Rn ≠ ⊤ := by
        refine ne_top_of_le_ne_top hY'f (lintegral_mono fun ω => Set.indicator_le_self _ _ ω)
      have hXf : X ≠ ⊤ := ne_top_of_le_ne_top hYf hXY
      have hFmf : Fm ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFm
      have hNf : N ≠ ⊤ := by
        intro hNt
        have hcW : ENNReal.ofReal (c / W) ≠ 0 := by
          rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
        rw [hNt, ENNReal.mul_top hcW, add_top, top_le_iff] at hstep
        exact (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYf,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFmf⟩, ENNReal.ofReal_ne_top⟩) hstep
      have hreal := ce_step_toReal hRnf hNf hYf hFmf (by positivity) (by positivity)
        (by positivity) hstep
      have hY'r : Y'.toReal ≤ Rn.toReal + AE / (W : ℝ) ^ 3 := by
        rw [← ENNReal.ofReal_toReal hRnf, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
          (by positivity)] at hYRn
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hYRn
      have hstepr : Y'.toReal + c / W * N.toReal ≤ (1 + C / W) * Y.toReal + C / W * Fm.toReal +
          AE / (W : ℝ) ^ 3 + max (e W) 0 := by linarith
      -- real forms of the bounds
      have hyW : Y.toReal ^ (1 / r) ≤ W * Ay' := by
        have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hY1
        calc Y.toReal ^ (1 / r) ≤ ((W : ℝ) ^ r * Ay) ^ (1 / r) :=
              Real.rpow_le_rpow ENNReal.toReal_nonneg h (by positivity)
          _ = W * Ay' := by
              rw [Real.mul_rpow (Real.rpow_nonneg hW0.le _) hAy0, hAy', one_div,
                Real.rpow_rpow_inv hW0.le hr0.ne']
      have hFv : Fm.toReal ≤ Fb := ENNReal.toReal_le_of_le_ofReal hFb0 hFm
      have hsplitr : Y.toReal ≤ (1 + K * d) * X.toReal + AE / (W : ℝ) ^ 3 := by
        rw [← ENNReal.ofReal_toReal hXf, ← ENNReal.ofReal_mul hKd.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)] at hsplit
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsplit
      have hholr : X.toReal ^ (1 + 1 / r) ≤ Mr * N.toReal := by
        rw [hMr]
        refine rhr_rpow_le_of_forall ENNReal.toReal_nonneg ENNReal.toReal_nonneg hM0 hr0
          fun l hl => ?_
        have h := hyo l hl
        rw [← ENNReal.ofReal_toReal hNf, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
      have hfinal := rhr_real_step (W := (W : ℝ)) (Fb := Fb) hW0 ENNReal.toReal_nonneg
        ENNReal.toReal_nonneg hC hc hK hd hMr0 hr0 ENNReal.toReal_nonneg hFv le_rfl
        (by positivity) hstepr hsplitr hholr hyW
      rw [← hcn] at hfinal
      have e1 : max (e W) 0 + (AE / (W : ℝ) ^ 3 + cn * (1 + 1 / r) * Ay' * (AE / (W : ℝ) ^ 3)) =
          max (e W) 0 + Atot / (W : ℝ) ^ 3 := by
        rw [hAtot]; ring
      rw [e1] at hfinal
      exact hfinal

open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.LayersOnePort
  BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs in

/-- **The remote higher-moment theorem** (`RemoteHigherStatement`) from
`ConditionalBlockGUECount`, `TransmissionLawContract`, `PassiveCovarianceContract`,
`PassiveSourceMixingContract`, `EdgeClockMomentsContract`, `TransmissionLengthUniformContract`,
`FullSourceGeneratorContract`, the one-port contracts `OnePortPassiveMeanContract`,
`OnePortOperatorMomentsContract`, `OnePortJetContraction`, and the isolated `RhHigherLimitDecay`
(the clock higher decay). Composes `rhcHigherOneStep_of_onePort`,
`rhnHigherWeightedRecursion_of_oneStep`, `remoteHigher_of_recursion` and
`nsCriticalClockLimitsExist_of_contracts`. -/
theorem remoteHigher_of_onePort (hCount : ConditionalBlockGUECount) (hTL : TransmissionLawContract)
    (hPC : PassiveCovarianceContract) (hPSM : PassiveSourceMixingContract)
    (hECM : EdgeClockMomentsContract) (hTLU : TransmissionLengthUniformContract)
    (hPM : OnePortPassiveMeanContract) (hOM : OnePortOperatorMomentsContract)
    (hJet : OnePortJetContraction) (hL : RhHigherLimitDecay)
    (hGen : FullSourceGeneratorContract) : RemoteHigherStatement :=
  remoteHigher_of_recursion
    (rhnHigherWeightedRecursion_of_oneStep hECM hTLU
      (rhcHigherOneStep_of_onePort hCount hTL hPC hPSM hPM hOM hJet))
    hL hGen (nsCriticalClockLimitsExist_of_contracts hGen)

end BlockBand.Endpoints
