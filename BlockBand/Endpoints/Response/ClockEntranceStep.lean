module

public import BlockBand.Endpoints.Response.ClockEntranceStepBounds

/-!
# `later` and `entrance` from the weighted one-step clock inequality

This file derives the finite-`W` logistic recursion, and hence
`ClockFractionalEntranceContract`, from the weighted one-step clock inequality.

## Main results

* The ingredients of the recursion:
  - Cauchy–Schwarz `E(1_D H_p²/γ^p) ≥ (E 1_D H_p)²/E γ^p` (`ce_lintegral_indicator_le_cs`);
  - the exceptional scalar/conductance sets `Dᶜ`, paid with the polynomial failure power
    `W⁻²⁰` (Markov on `δ₀, δ₁` with the jet moments, on `g` with the conductance moments) and
    `H_p ≤ W^{1-p}γ^p` (`ce_lintegral_le_split`);
  - the bounded denominator `E γ^p`, forcing `E g^{2(1-p)}γ^p` and a priori bound
    `y_j ≤ C W`, from the edge-clock moments (`edgeClockMoments`), the conductance moments and
    the jet moments, all with constants chosen before the source and the preceding middle;
  - the real algebra of `ce_real_step`.
* `clockFractionalEntrance_of_oneStep`: `ClockFractionalEntranceContract`, composing with
  `clockFractionalEntrance_holds`.

Constants: `C' = C + C F̄`, `c' = c/((1 + Kd)² M)` with `M = 1 + C_γ` (bound on `E γ^p`) and
`F̄ = 1 + C_g + C_γ` (bound on the forcing); the `o(W⁻²)` error is `max e 0 + A/W³`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.TransmissionUniform

/-!
## Real algebra of one step
-/

/-- One step of the expectation recursion (real algebra). From the integrated one-step
inequality (with the exceptional part `ex ≤ ε` of the new length added), the split
`y ≤ (1 + Kd) x + ε` of the weighted expectation over the jet domain, Cauchy–Schwarz `x² ≤ M n`
and the a priori bound `y ≤ W A_y`:
`y' ≤ y + W⁻¹(C' y - c' y² + C') + e + ε + 2 c' A_y ε` with `C' = C + C F̄`,
`c' = c/((1 + Kd)² M)`. -/
theorem ce_real_step {W y y' x n C c K d M Fb Fv ex ε e Ay : ℝ} (hW : 0 < W) (hy : 0 ≤ y)
    (hC : 0 ≤ C) (hc : 0 < c) (hK : 0 ≤ K) (hd : 0 < d) (hM : 0 < M)
    (hFv0 : 0 ≤ Fv) (hFv : Fv ≤ Fb) (hex : ex ≤ ε) (hε : 0 ≤ ε)
    (hstep : y' + c / W * n ≤ (1 + C / W) * y + C / W * Fv + ex + e)
    (hsplit : y ≤ (1 + K * d) * x + ε) (hcs : x ^ 2 ≤ M * n) (hyW : y ≤ W * Ay) :
    y' ≤ y + W⁻¹ * ((C + C * Fb) * y - c / ((1 + K * d) ^ 2 * M) * y ^ 2 + (C + C * Fb)) +
      (e + (ε + 2 * (c / ((1 + K * d) ^ 2 * M)) * Ay * ε)) := by
  set a := 1 + K * d with ha
  have ha1 : 1 ≤ a := by rw [ha]; nlinarith
  set κ := a ^ 2 * M with hκ
  have hκ0 : 0 < κ := by positivity
  -- `y² - 2yε ≤ a² x²`
  have hsq : y ^ 2 - 2 * y * ε ≤ a ^ 2 * x ^ 2 := by
    by_cases hyε : y ≤ ε
    · nlinarith [sq_nonneg (a * x)]
    · have h1 : y - ε ≤ a * x := by linarith
      have h2 : 0 ≤ y - ε := by linarith
      have : (y - ε) ^ 2 ≤ (a * x) ^ 2 := pow_le_pow_left₀ h2 h1 2
      nlinarith
  have hn' : (y ^ 2 - 2 * y * ε) / κ ≤ n := by
    rw [div_le_iff₀ hκ0]
    have : a ^ 2 * x ^ 2 ≤ a ^ 2 * (M * n) := mul_le_mul_of_nonneg_left hcs (by positivity)
    nlinarith
  set c' := c / κ with hc'
  have hc'0 : 0 < c' := by positivity
  have hcn : c / W * n ≥ c' / W * (y ^ 2 - 2 * y * ε) := by
    have : c / W * ((y ^ 2 - 2 * y * ε) / κ) ≤ c / W * n :=
      mul_le_mul_of_nonneg_left hn' (by positivity)
    have e1 : c / W * ((y ^ 2 - 2 * y * ε) / κ) = c' / W * (y ^ 2 - 2 * y * ε) := by
      rw [hc']; field_simp
    linarith
  have hyε : c' / W * (2 * y * ε) ≤ 2 * c' * Ay * ε := by
    have : y / W ≤ Ay := by rw [div_le_iff₀ hW]; linarith
    have e1 : c' / W * (2 * y * ε) = 2 * c' * (y / W) * ε := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * c')
    nlinarith
  have hFb : 0 ≤ Fb := hFv0.trans hFv
  have hCy : C * y / W ≤ (C + C * Fb) * y / W := by
    apply div_le_div_of_nonneg_right _ hW.le
    nlinarith [mul_nonneg hC hFb, mul_nonneg (mul_nonneg hC hFb) hy]
  have hCF : C * Fv / W ≤ (C + C * Fb) / W := by
    apply div_le_div_of_nonneg_right _ hW.le
    nlinarith [mul_le_mul_of_nonneg_left hFv hC]
  have expand : W⁻¹ * ((C + C * Fb) * y - c' * y ^ 2 + (C + C * Fb)) =
      (C + C * Fb) * y / W - c' / W * y ^ 2 + (C + C * Fb) / W := by ring
  have e2 : (1 + C / W) * y + C / W * Fv = y + C * y / W + C * Fv / W := by ring
  have e3 : c' / W * (y ^ 2 - 2 * y * ε) = c' / W * y ^ 2 - c' / W * (2 * y * ε) := by ring
  rw [expand]
  linarith

/-!
## Pointwise envelopes
-/

theorem ce_sq_le_one_add_pow {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 2 ≤ k) : u ^ 2 ≤ 1 + u ^ k := by
  rcases le_total u 1 with h | h
  · have : u ^ 2 ≤ 1 := pow_le_one₀ hu h
    have : 0 ≤ u ^ k := pow_nonneg hu k
    linarith
  · have : u ^ 2 ≤ u ^ k := pow_le_pow_right₀ h hk
    linarith

/-- `(1 + Kδ) x ≤ A Ψ_s` and `(1 + δ) x ≤ A Ψ_s`, `A = 3 + K²`, `Ψ_s = 1 + δ¹⁰ + x⁴`. -/
theorem ce_envelope_le {K δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    (1 + K * δ) * x ≤ (3 + K ^ 2) * (1 + δ ^ 10 + x ^ 4) ∧
      (1 + δ) * x ≤ (3 + K ^ 2) * (1 + δ ^ 10 + x ^ 4) := by
  have h1 : δ ^ 2 ≤ 1 + δ ^ 10 := ce_sq_le_one_add_pow hδ (by norm_num)
  have h2 : x ^ 2 ≤ 1 + x ^ 4 := ce_sq_le_one_add_pow hx (by norm_num)
  have hd10 : 0 ≤ δ ^ 10 := pow_nonneg hδ _
  have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx _
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hKd : K ^ 2 * δ ^ 2 ≤ K ^ 2 * (1 + δ ^ 10) := mul_le_mul_of_nonneg_left h1 hK2
  have hA : 0 ≤ K ^ 2 * δ ^ 10 := mul_nonneg hK2 hd10
  have hB : 0 ≤ K ^ 2 * x ^ 4 := mul_nonneg hK2 hx4
  constructor
  · nlinarith [sq_nonneg ((1 + K * δ) - x), sq_nonneg (K * δ - 1)]
  · nlinarith [sq_nonneg ((1 + δ) - x), sq_nonneg (δ - 1)]

/-- `Ψ_s² ≤ 3 Ψ_b` and `Ψ_s ≤ 3 Ψ_b`, `Ψ_b = 1 + δ²⁰ + x⁸`. -/
theorem ce_envelope_sq_le {δ x : ℝ} (hδ : 0 ≤ δ) (hx : 0 ≤ x) :
    (1 + δ ^ 10 + x ^ 4) ^ 2 ≤ 3 * (1 + δ ^ 20 + x ^ 8) ∧
      1 + δ ^ 10 + x ^ 4 ≤ 3 * (1 + δ ^ 20 + x ^ 8) := by
  have e1 : δ ^ 20 = (δ ^ 10) ^ 2 := by ring
  have e2 : x ^ 8 = (x ^ 4) ^ 2 := by ring
  rw [e1, e2]
  have hu : 0 ≤ δ ^ 10 := pow_nonneg hδ _
  have hv : 0 ≤ x ^ 4 := pow_nonneg hx _
  constructor
  · nlinarith [sq_nonneg (1 - δ ^ 10), sq_nonneg (1 - x ^ 4), sq_nonneg (δ ^ 10 - x ^ 4)]
  · nlinarith [sq_nonneg (1 - δ ^ 10), sq_nonneg (1 - x ^ 4)]

/-- The forcing envelope: `|g|^{2(1-p)} x ≤ 1 + |g|²⁰ + x⁸` (`0 < p < 1`, `x ≥ 0`). -/
theorem ce_forcing_le {g x p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hx : 0 ≤ x) :
    |g| ^ (2 * (1 - p)) * x ≤ 1 + |g| ^ (20 : ℝ) + x ^ 8 := by
  set G := |g| ^ (2 * (1 - p)) with hG
  have hG0 : 0 ≤ G := Real.rpow_nonneg (abs_nonneg g) _
  have hG2 : G ^ 2 ≤ 1 + |g| ^ (20 : ℝ) := by
    have e : G ^ 2 = |g| ^ (2 * (1 - p) * (2 : ℕ)) := by
      rw [hG, Real.rpow_mul_natCast (abs_nonneg g)]
    rw [e]
    rcases le_total |g| 1 with h | h
    · have : |g| ^ (2 * (1 - p) * (2 : ℕ)) ≤ 1 :=
        Real.rpow_le_one (abs_nonneg g) h (by push_cast; nlinarith)
      have : 0 ≤ |g| ^ (20 : ℝ) := Real.rpow_nonneg (abs_nonneg g) _
      linarith
    · have : |g| ^ (2 * (1 - p) * (2 : ℕ)) ≤ |g| ^ (20 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h (by push_cast; nlinarith)
      linarith
  have hx2 : x ^ 2 ≤ 1 + x ^ 8 := ce_sq_le_one_add_pow hx (by norm_num)
  have : 0 ≤ x ^ 8 := pow_nonneg hx _
  have : 0 ≤ |g| ^ (20 : ℝ) := Real.rpow_nonneg (abs_nonneg g) _
  nlinarith [sq_nonneg (G - x)]

theorem ce_le_one_add_pow_eight {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ 8 := by
  rcases le_total x 1 with h | h
  · have : 0 ≤ x ^ 8 := pow_nonneg hx _
    linarith
  · have : x ≤ x ^ 8 := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ 8 := pow_le_pow_right₀ h (by norm_num)
    linarith

/-!
## The moments at one path length
-/

/-- `C_Ψ = 1 + C_J'^20 + C_γ'`: bound on `E Ψ_b`, `Ψ_b = 1 + δ₀²⁰ + γ^{8p}`. -/
def ce_CPsi (CJ Cγ : ℝ) : ℝ := 1 + max CJ 0 ^ 20 + max Cγ 0

/-- `A = 3 + K²`: the envelope constant of `ce_envelope_le`. -/
def ce_A (K : ℝ) : ℝ := 3 + K ^ 2

/-- `A_E = A_D + 3 A² C_Ψ`, `A_D = 2 C_J'^20/d^20 + C_g'/d^20` (exceptional sets). -/
def ce_AE (K d CJ CG Cγ : ℝ) : ℝ :=
  (2 * (max CJ 0 ^ 20 / d ^ 20) + max CG 0 / d ^ 20) + 3 * ce_A K ^ 2 * ce_CPsi CJ Cγ

theorem ce_CPsi_nonneg (CJ Cγ : ℝ) : 0 ≤ ce_CPsi CJ Cγ := by
  unfold ce_CPsi; positivity

theorem ce_AE_nonneg (K d CJ CG Cγ : ℝ) (hd : 0 < d) : 0 ≤ ce_AE K d CJ CG Cγ := by
  unfold ce_AE ce_A; have := ce_CPsi_nonneg CJ Cγ; positivity

/-- `∫ (1 + u + v) = 1 + ∫ u + ∫ v` on the growth law (`u` a.e. measurable). -/
theorem ce_lintegral_one_add_add {W : ℕ} {b : ℝ} (u v : GrowthPath W → ℝ) (hu0 : ∀ ω, 0 ≤ u ω)
    (hv0 : ∀ ω, 0 ≤ v ω) (hu : AEMeasurable (fun ω => ENNReal.ofReal (u ω)) (growthPathLaw W b)) :
    ∫⁻ ω, ENNReal.ofReal (1 + u ω + v ω) ∂growthPathLaw W b =
      1 + ∫⁻ ω, ENNReal.ofReal (u ω) ∂growthPathLaw W b +
        ∫⁻ ω, ENNReal.ofReal (v ω) ∂growthPathLaw W b := by
  have := isProbabilityMeasure_growthPathLaw W b
  have hpt : ∀ ω, ENNReal.ofReal (1 + u ω + v ω) =
      1 + ENNReal.ofReal (u ω) + ENNReal.ofReal (v ω) := fun ω => by
    rw [ENNReal.ofReal_add (by linarith [hu0 ω]) (hv0 ω),
      ENNReal.ofReal_add zero_le_one (hu0 ω), ENNReal.ofReal_one]
  have h1 : AEMeasurable (fun ω => 1 + ENNReal.ofReal (u ω)) (growthPathLaw W b) :=
    aemeasurable_const.add hu
  rw [lintegral_congr hpt, lintegral_add_left' h1 (fun ω => ENNReal.ofReal (v ω)),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]

/-- The moments at one path length. At width `W ≥ 1` and path length `j`, from the jet bound
`‖δ₀‖₂₀, ‖δ₁‖₂₀ ≤ C_J/W`, the conductance moment `E|g|²⁰ ≤ C_g` and the edge-clock moment
`E γ^{8p} ≤ C_γ`:
1. a priori `y_j ≤ 3 A C_Ψ W` (`H_p ≤ W γ^p`);
2. `E H_p ≤ y_j` (weight `≥ 1`);
3. exceptional sets: `μ(Dᶜ) ≤ A_D W⁻²⁰`, and `y_j ≤ E[1_S (1 + Kδ₀) H_p] + A_E W⁻³` for every
   set `S` with `μ(Sᶜ) ≤ A_D W⁻²⁰`;
4. split: `y_j ≤ (1 + Kd) E[1_D H_p] + A_E W⁻³`;
5. Cauchy–Schwarz: `E[1_D H_p] ≤ (l/2) E[1_D H_p²/γ^p] + (2l)⁻¹ (1 + C_γ')` for `l > 0`;
6. `E[1_D H_p] ≤ E H_p`;
7. forcing: `E[|g|^{2(1-p)} γ^p] ≤ 1 + C_g' + C_γ'`. -/
theorem ce_moments_at {b E p K d CJ CG Cγ : ℝ} {s : ℂ} (hp : 0 < p) (hp1 : p < 1) (hK : 0 ≤ K)
    (hd : 0 < d) {W j : ℕ} (hW : 1 ≤ (W : ℝ)) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (hδ0 : eLpNorm (fun ω => ce_jet0 b E W j ω) (ENNReal.ofReal 20) (growthPathLaw W b) ≤
      ENNReal.ofReal (CJ / W))
    (hδ1 : eLpNorm (fun ω => ce_jet1 b E s W j ω) (ENNReal.ofReal 20) (growthPathLaw W b) ≤
      ENNReal.ofReal (CJ / W))
    (hg : ∫⁻ ω, ‖pathConductance b E W j ω‖ₑ ^ (20 : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal CG)
    (hγ : edgeNearClockMoment b E (8 * p) W j q ≤ ENNReal.ofReal (1 ^ (8 * p) * Cγ)) :
    ce_weightedMoment K b E p W j q ≤ ENNReal.ofReal (W * (3 * ce_A K * ce_CPsi CJ Cγ)) ∧
    ∫⁻ ω, ENNReal.ofReal (ce_fracClock b E p W j q ω) ∂growthPathLaw W b ≤
      ce_weightedMoment K b E p W j q ∧
    (growthPathLaw W b) (ce_jetDomain b E s d W j)ᶜ ≤
      ENNReal.ofReal ((2 * (max CJ 0 ^ 20 / d ^ 20) + max CG 0 / d ^ 20) / (W : ℝ) ^ 20) ∧
    (∀ S : Set (GrowthPath W), (growthPathLaw W b) Sᶜ ≤
        ENNReal.ofReal ((2 * (max CJ 0 ^ 20 / d ^ 20) + max CG 0 / d ^ 20) / (W : ℝ) ^ 20) →
      ce_weightedMoment K b E p W j q ≤ ∫⁻ ω, S.indicator (fun ω => ENNReal.ofReal
          (ce_weight K b E W j ω * ce_fracClock b E p W j q ω)) ω ∂growthPathLaw W b +
        ENNReal.ofReal (ce_AE K d CJ CG Cγ / W ^ 3)) ∧
    ce_weightedMoment K b E p W j q ≤ ENNReal.ofReal (1 + K * d) *
        ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂growthPathLaw W b +
      ENNReal.ofReal (ce_AE K d CJ CG Cγ / W ^ 3) ∧
    (∀ l : ℝ, 0 < l → ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal (l / 2) * ce_concavityMoment b E p s d W j q +
          ENNReal.ofReal (1 / (2 * l)) * ENNReal.ofReal (1 + max Cγ 0)) ∧
    ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂growthPathLaw W b ≤
      ∫⁻ ω, ENNReal.ofReal (ce_fracClock b E p W j q ω) ∂growthPathLaw W b ∧
    ce_forcingMoment b E p W j q ≤ ENNReal.ofReal (1 + max CG 0 + max Cγ 0) := by
  have hP := isProbabilityMeasure_growthPathLaw W b
  have hW0 : 0 < (W : ℝ) := by linarith
  set μ := growthPathLaw W b with hμ
  set D := ce_jetDomain b E s d W j with hD
  set CJ' := max CJ 0 with hCJ'
  set Cγ' := max Cγ 0 with hCγ'
  set CG' := max CG 0 with hCG'
  set A := ce_A K with hA
  set CΨ := ce_CPsi CJ Cγ with hCΨ
  have hA0 : 0 ≤ A := by rw [hA]; unfold ce_A; positivity
  have hCΨ0 : 0 ≤ CΨ := ce_CPsi_nonneg CJ Cγ
  have hCJ'0 : 0 ≤ CJ' := le_max_right _ _
  have hCγ'0 : 0 ≤ Cγ' := le_max_right _ _
  have hCG'0 : 0 ≤ CG' := le_max_right _ _
  -- pointwise facts
  have hδ0n : ∀ ω, 0 ≤ ce_jet0 b E W j ω := fun ω => norm_nonneg _
  have hδ1n : ∀ ω, 0 ≤ ce_jet1 b E s W j ω := fun ω => norm_nonneg _
  have hγn : ∀ ω, 0 ≤ ce_clockTrace b E W j q ω := ce_clockTrace_nonneg b E W j hq
  have hxn : ∀ ω, 0 ≤ ce_clockTrace b E W j q ω ^ p := fun ω => Real.rpow_nonneg (hγn ω) _
  have hHn : ∀ ω, 0 ≤ ce_fracClock b E p W j q ω := ce_fracClock_nonneg b E p W j q
  have hHle : ∀ ω, ce_fracClock b E p W j q ω ≤ W * ce_clockTrace b E W j q ω ^ p :=
    ce_fracClock_le b E p hp hp1 hW j hq
  have hwn : ∀ ω, 1 ≤ ce_weight K b E W j ω := fun ω => by
    unfold ce_weight; nlinarith [hδ0n ω]
  -- measurability and moments of `δ₀, δ₁`
  obtain ⟨hδ0m, hδ0i⟩ := ce_lintegral_pow_of_eLpNorm μ _ hδ0n (by norm_num) hδ0
  obtain ⟨hδ1m, hδ1i⟩ := ce_lintegral_pow_of_eLpNorm μ _ hδ1n (by norm_num) hδ1
  have hmaxJ : max (CJ / W) 0 = CJ' / W := by
    have := max_div_div_right hW0.le CJ 0; rwa [zero_div] at this
  rw [hmaxJ] at hδ0i hδ1i
  have hpow20 : ∀ x : ℝ, x ^ (20 : ℝ) = x ^ (20 : ℕ) := fun x => Real.rpow_ofNat x 20
  have hJW : (CJ' / W) ^ (20 : ℝ) = CJ' ^ 20 / (W : ℝ) ^ 20 := by rw [hpow20, div_pow]
  rw [hJW] at hδ0i hδ1i
  have hγm : Measurable (fun ω => ce_clockTrace b E W j q ω) := ce_measurable_clockTrace b E W j q
  have hgm : Measurable (fun ω => pathConductance b E W j ω) := ce_measurable_conductance b E W j
  -- the edge moment as `E (γ^p)^8 ≤ C_γ'`
  have hγi : ∫⁻ ω, ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ 8) ∂μ ≤
      ENNReal.ofReal Cγ' := by
    have e : ∀ ω, (ce_clockTrace b E W j q ω ^ p) ^ 8 =
        (nearClock b E W j q ω).trace.re ^ (8 * p) := fun ω => by
      rw [mul_comm, ← Real.rpow_mul_natCast (hγn ω)]; rfl
    simp_rw [e]
    refine hγ.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.one_rpow, one_mul]; exact le_max_left _ _
  -- the conductance moment
  have hgi : ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ (20 : ℝ)) ∂μ ≤
      ENNReal.ofReal CG := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hg
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  -- `μ(Dᶜ)`
  have hDc : μ Dᶜ ≤ ENNReal.ofReal ((2 * (CJ' ^ 20 / d ^ 20) + CG' / d ^ 20) / (W : ℝ) ^ 20) := by
    have hsub : Dᶜ ⊆ ({ω | d < ce_jet0 b E W j ω} ∪ {ω | d < ce_jet1 b E s W j ω}) ∪
        {ω | d * W < pathConductance b E W j ω} := by
      intro ω hω
      simp only [hD, ce_jetDomain, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or,
        not_le] at hω
      rcases hω with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have habs : ∀ (f : GrowthPath W → ℝ), (∀ ω, 0 ≤ f ω) →
        ∫⁻ ω, ENNReal.ofReal (|f ω| ^ (20 : ℝ)) ∂μ = ∫⁻ ω, ENNReal.ofReal (f ω ^ (20 : ℝ)) ∂μ :=
      fun f hf => lintegral_congr fun ω => by rw [abs_of_nonneg (hf ω)]
    have m1 := ce_measure_lt_le μ _ hδ0m.aemeasurable hd (m := 20) (by norm_num)
      ((habs _ hδ0n).le.trans hδ0i)
    have m2 := ce_measure_lt_le μ _ hδ1m.aemeasurable hd (m := 20) (by norm_num)
      ((habs _ hδ1n).le.trans hδ1i)
    have m3 := ce_measure_lt_le μ _ hgm.aemeasurable (mul_pos hd hW0) (m := 20) (by norm_num)
      hgi
    rw [hpow20] at m1 m2 m3
    calc μ Dᶜ ≤ μ (({ω | d < ce_jet0 b E W j ω} ∪ {ω | d < ce_jet1 b E s W j ω}) ∪
          {ω | d * W < pathConductance b E W j ω}) := measure_mono hsub
      _ ≤ μ {ω | d < ce_jet0 b E W j ω} + μ {ω | d < ce_jet1 b E s W j ω} +
          μ {ω | d * W < pathConductance b E W j ω} :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ ENNReal.ofReal (CJ' ^ 20 / (W : ℝ) ^ 20 / d ^ 20) +
          ENNReal.ofReal (CJ' ^ 20 / (W : ℝ) ^ 20 / d ^ 20) +
          ENNReal.ofReal (CG / (d * W) ^ 20) := add_le_add (add_le_add m1 m2) m3
      _ ≤ ENNReal.ofReal (CJ' ^ 20 / (W : ℝ) ^ 20 / d ^ 20) +
          ENNReal.ofReal (CJ' ^ 20 / (W : ℝ) ^ 20 / d ^ 20) +
          ENNReal.ofReal (CG' / d ^ 20 / (W : ℝ) ^ 20) := by
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          rw [mul_pow, div_div]
          exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : CJ' ^ 20 / (W : ℝ) ^ 20 / d ^ 20 = CJ' ^ 20 / d ^ 20 / (W : ℝ) ^ 20 := by ring
          have e2 : (2 * (CJ' ^ 20 / d ^ 20) + CG' / d ^ 20) / (W : ℝ) ^ 20 =
              2 * (CJ' ^ 20 / d ^ 20 / (W : ℝ) ^ 20) + CG' / d ^ 20 / (W : ℝ) ^ 20 := by ring
          rw [e2, e1]; linarith
  -- the envelope `Ψ_b`
  set Ψb : GrowthPath W → ℝ := fun ω =>
    1 + ce_jet0 b E W j ω ^ 20 + (ce_clockTrace b E W j q ω ^ p) ^ 8 with hΨb
  have hΨb0 : ∀ ω, 0 ≤ Ψb ω := fun ω => by
    have := pow_nonneg (hδ0n ω) 20; have := pow_nonneg (hxn ω) 8; simp only [hΨb]; linarith
  have hu20 : AEMeasurable (fun ω => ENNReal.ofReal (ce_jet0 b E W j ω ^ 20)) μ :=
    (hδ0m.aemeasurable.pow_const 20).ennreal_ofReal
  have hΨbm : AEMeasurable (fun ω => ENNReal.ofReal (Ψb ω)) μ :=
    (((aemeasurable_const.add (hδ0m.aemeasurable.pow_const 20)).add
      ((hγm.pow_const p).pow_const 8).aemeasurable)).ennreal_ofReal
  have hΨbi : ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ ≤ ENNReal.ofReal CΨ := by
    rw [ce_lintegral_one_add_add _ _ (fun ω => pow_nonneg (hδ0n ω) 20)
      (fun ω => pow_nonneg (hxn ω) 8) hu20]
    have h1 : ∫⁻ ω, ENNReal.ofReal (ce_jet0 b E W j ω ^ 20) ∂μ ≤ ENNReal.ofReal (CJ' ^ 20) := by
      refine le_trans (le_of_eq (lintegral_congr fun ω => by rw [hpow20])) (hδ0i.trans ?_)
      refine ENNReal.ofReal_le_ofReal (div_le_self (by positivity) ?_)
      exact one_le_pow₀ hW
    calc 1 + ∫⁻ ω, ENNReal.ofReal (ce_jet0 b E W j ω ^ 20) ∂μ +
          ∫⁻ ω, ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ 8) ∂μ
        ≤ ENNReal.ofReal 1 + ENNReal.ofReal (CJ' ^ 20) + ENNReal.ofReal Cγ' := by
          rw [ENNReal.ofReal_one]; gcongr
      _ = ENNReal.ofReal CΨ := by
          rw [← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_add (by positivity) hCγ'0, hCΨ, ce_CPsi]
  -- `Φ = 3 (WA)² Ψ_b`
  set Φ : GrowthPath W → ℝ≥0∞ := fun ω => ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2 * Ψb ω) with hΦ
  have hΦm : AEMeasurable Φ μ := by
    have : Φ = fun ω => ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2) * ENNReal.ofReal (Ψb ω) := by
      funext ω; rw [hΦ]; exact ENNReal.ofReal_mul (by positivity)
    rw [this]; exact hΨbm.const_mul _
  have hΦi : ∫⁻ ω, Φ ω ∂μ ≤ ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2 * CΨ) := by
    calc ∫⁻ ω, Φ ω ∂μ = ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2) * ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun ω => ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2) * ENNReal.ofReal CΨ := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  -- the envelope `F = W A Ψ_s`
  set F : GrowthPath W → ℝ := fun ω =>
    (W : ℝ) * A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) with hF
  have hFsq : ∀ ω, ENNReal.ofReal (F ω ^ 2) ≤ Φ ω := fun ω => by
    refine ENNReal.ofReal_le_ofReal ?_
    have h := (ce_envelope_sq_le (hδ0n ω) (hxn ω)).1
    have e : F ω ^ 2 = ((W : ℝ) * A) ^ 2 *
        (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) ^ 2 := by
      simp only [hF]; ring
    rw [e]
    calc ((W : ℝ) * A) ^ 2 * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) ^ 2
        ≤ ((W : ℝ) * A) ^ 2 * (3 * Ψb ω) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * ((W : ℝ) * A) ^ 2 * Ψb ω := by ring
  have hwHF : ∀ ω, ce_weight K b E W j ω * ce_fracClock b E p W j q ω ≤ F ω := fun ω => by
    have h : (1 + K * ce_jet0 b E W j ω) * ce_clockTrace b E W j q ω ^ p ≤
        A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) := by
      rw [hA]; unfold ce_A; exact (ce_envelope_le (hδ0n ω) (hxn ω)).1
    calc ce_weight K b E W j ω * ce_fracClock b E p W j q ω
        ≤ ce_weight K b E W j ω * (W * ce_clockTrace b E W j q ω ^ p) :=
          mul_le_mul_of_nonneg_left (hHle ω) (by linarith [hwn ω])
      _ = W * ((1 + K * ce_jet0 b E W j ω) * ce_clockTrace b E W j q ω ^ p) := by
          simp only [ce_weight]; ring
      _ ≤ W * (A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4)) :=
          mul_le_mul_of_nonneg_left h hW0.le
      _ = F ω := by simp only [hF]; ring
  have hδHF : ∀ ω, (1 + ce_jet0 b E W j ω) * ce_fracClock b E p W j q ω ≤ F ω := fun ω => by
    have h : (1 + ce_jet0 b E W j ω) * ce_clockTrace b E W j q ω ^ p ≤
        A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) := by
      rw [hA]; unfold ce_A; exact (ce_envelope_le (K := K) (hδ0n ω) (hxn ω)).2
    calc (1 + ce_jet0 b E W j ω) * ce_fracClock b E p W j q ω
        ≤ (1 + ce_jet0 b E W j ω) * (W * ce_clockTrace b E W j q ω ^ p) :=
          mul_le_mul_of_nonneg_left (hHle ω) (by linarith [hδ0n ω])
      _ = W * ((1 + ce_jet0 b E W j ω) * ce_clockTrace b E W j q ω ^ p) := by ring
      _ ≤ W * (A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4)) :=
          mul_le_mul_of_nonneg_left h hW0.le
      _ = F ω := by simp only [hF]; ring
  -- the bracket of the exceptional sets, with `l = W⁵`
  set AD := 2 * (CJ' ^ 20 / d ^ 20) + CG' / d ^ 20 with hAD
  have hAD0 : 0 ≤ AD := by positivity
  have hbrS : ∀ S : Set (GrowthPath W), μ Sᶜ ≤ ENNReal.ofReal (AD / (W : ℝ) ^ 20) →
      ENNReal.ofReal ((W : ℝ) ^ 5 / 2) * μ Sᶜ +
      ENNReal.ofReal (1 / (2 * (W : ℝ) ^ 5)) * ∫⁻ ω, Φ ω ∂μ ≤
      ENNReal.ofReal (ce_AE K d CJ CG Cγ / (W : ℝ) ^ 3) := by
    intro S hS
    calc _ ≤ ENNReal.ofReal ((W : ℝ) ^ 5 / 2) * ENNReal.ofReal (AD / (W : ℝ) ^ 20) +
          ENNReal.ofReal (1 / (2 * (W : ℝ) ^ 5)) *
            ENNReal.ofReal (3 * ((W : ℝ) * A) ^ 2 * CΨ) := by gcongr
      _ = ENNReal.ofReal ((W : ℝ) ^ 5 / 2 * (AD / (W : ℝ) ^ 20) +
          1 / (2 * (W : ℝ) ^ 5) * (3 * ((W : ℝ) * A) ^ 2 * CΨ)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : (W : ℝ) ^ 5 / 2 * (AD / (W : ℝ) ^ 20) = AD / (2 * (W : ℝ) ^ 15) := by
            field_simp
          have e2 : 1 / (2 * (W : ℝ) ^ 5) * (3 * ((W : ℝ) * A) ^ 2 * CΨ) =
              3 * A ^ 2 * CΨ / (2 * (W : ℝ) ^ 3) := by
            field_simp
          have e3 : ce_AE K d CJ CG Cγ / (W : ℝ) ^ 3 =
              AD / (W : ℝ) ^ 3 + 3 * A ^ 2 * CΨ / (W : ℝ) ^ 3 := by
            rw [hAD, hA, hCΨ, hCJ', hCG']; unfold ce_AE; ring
          have hW3 : (W : ℝ) ^ 3 ≤ (W : ℝ) ^ 15 := pow_le_pow_right₀ hW (by norm_num)
          have h1 : AD / (2 * (W : ℝ) ^ 15) ≤ AD / (W : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left hAD0 (by positivity) (by nlinarith [pow_pos hW0 15])
          have h2 : 3 * A ^ 2 * CΨ / (2 * (W : ℝ) ^ 3) ≤ 3 * A ^ 2 * CΨ / (W : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (by nlinarith [pow_pos hW0 3])
          rw [e1, e2, e3]; linarith
  have hbr := hbrS D hDc
  have hl5 : (0 : ℝ) < (W : ℝ) ^ 5 := by positivity
  have hl5' : (1 : ℝ) / (2 * (W : ℝ) ^ 5) = 1 / (2 * (W : ℝ) ^ 5) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) a priori bound
    calc ce_weightedMoment K b E p W j q ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hwHF ω)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (3 * (W : ℝ) * A) * ENNReal.ofReal (Ψb ω) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := (ce_envelope_sq_le (hδ0n ω) (hxn ω)).2
          have : F ω = (W : ℝ) * A *
              (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4) := rfl
          rw [this]
          calc (W : ℝ) * A * (1 + ce_jet0 b E W j ω ^ 10 + (ce_clockTrace b E W j q ω ^ p) ^ 4)
              ≤ (W : ℝ) * A * (3 * Ψb ω) := mul_le_mul_of_nonneg_left h (by positivity)
            _ = 3 * (W : ℝ) * A * Ψb ω := by ring
      _ = ENNReal.ofReal (3 * (W : ℝ) * A) * ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * (W : ℝ) * A) * ENNReal.ofReal CΨ := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  · -- (2) `E H_p ≤ y_j`
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_left (hHn ω) (hwn ω)
  · -- (3) `μ(Dᶜ)`
    exact hDc
  · -- (3') split over any large set
    intro S hS
    have h := ce_lintegral_le_split μ S
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω))
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω))
      Φ F hΦm hl5 (fun ω _ => le_rfl)
      (fun ω _ => ENNReal.ofReal_le_ofReal (hwHF ω)) hFsq
    exact h.trans (add_le_add le_rfl (hbrS S hS))
  · -- (4) split over the jet domain
    have h := ce_lintegral_le_split μ D
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω))
      (fun ω => ENNReal.ofReal (1 + K * d) * ENNReal.ofReal (ce_fracClock b E p W j q ω))
      Φ F hΦm hl5
      (fun ω hω => by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hHn ω))
        have : ce_jet0 b E W j ω ≤ d := hω.1
        simp only [ce_weight]; nlinarith)
      (fun ω _ => ENNReal.ofReal_le_ofReal (hwHF ω)) hFsq
    have hind : ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (1 + K * d) *
        ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂μ = ENNReal.ofReal (1 + K * d) *
          ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ D
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [hind] at h
    exact h.trans (add_le_add le_rfl hbr)
  · -- (5) Cauchy–Schwarz
    intro l hl
    have hGm : AEMeasurable (fun ω => ENNReal.ofReal (ce_clockTrace b E W j q ω ^ p)) μ :=
      (hγm.pow_const p).ennreal_ofReal.aemeasurable
    have h := ce_lintegral_indicator_le_cs μ D (fun ω => ce_fracClock b E p W j q ω)
      (fun ω => ce_clockTrace b E W j q ω ^ p) hGm hxn
      (fun ω h0 => ce_fracClock_eq_zero b E p hp hp1 hW j hq ω h0) hl
    refine h.trans (add_le_add le_rfl ?_)
    gcongr
    calc ∫⁻ ω, ENNReal.ofReal (ce_clockTrace b E W j q ω ^ p) ∂μ
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ 8)) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (pow_nonneg (hxn ω) 8)]
          exact ENNReal.ofReal_le_ofReal (ce_le_one_add_pow_eight (hxn ω))
      _ = 1 + ∫⁻ ω, ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ 8) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal Cγ' := by rw [ENNReal.ofReal_one]; gcongr
      _ = ENNReal.ofReal (1 + Cγ') := (ENNReal.ofReal_add zero_le_one hCγ'0).symm
  · -- (6)
    exact lintegral_mono fun ω => Set.indicator_le_self _ _ ω
  · -- (7) forcing
    calc ce_forcingMoment b E p W j q
        ≤ ∫⁻ ω, ENNReal.ofReal (1 + |pathConductance b E W j ω| ^ (20 : ℝ) +
            (ce_clockTrace b E W j q ω ^ p) ^ 8) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (ce_forcing_le hp hp1 (hxn ω))
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ (20 : ℝ)) ∂μ +
            ∫⁻ ω, ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ 8) ∂μ :=
          ce_lintegral_one_add_add _ _ (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
            (fun ω => pow_nonneg (hxn ω) 8)
            ((hgm.abs.pow_const _).ennreal_ofReal.aemeasurable)
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal CG' + ENNReal.ofReal Cγ' := by
          rw [ENNReal.ofReal_one]
          gcongr
          exact hgi.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (1 + CG' + Cγ') := by
          rw [← ENNReal.ofReal_add zero_le_one hCG'0, ← ENNReal.ofReal_add (by positivity) hCγ'0]

/-!
## From `ℝ≥0∞` to real inequalities
-/

/-- The one-step inequality in real numbers (all moments finite). -/
theorem ce_step_toReal {Y' N Y Fm : ℝ≥0∞} (hY' : Y' ≠ ⊤) (hN : N ≠ ⊤) (hY : Y ≠ ⊤)
    (hFm : Fm ≠ ⊤) {c' a1 a2 e : ℝ} (hc' : 0 ≤ c') (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (h : Y' + ENNReal.ofReal c' * N ≤ ENNReal.ofReal a1 * Y + ENNReal.ofReal a2 * Fm +
      ENNReal.ofReal e) :
    Y'.toReal + c' * N.toReal ≤ a1 * Y.toReal + a2 * Fm.toReal + max e 0 := by
  rw [← ENNReal.ofReal_toReal hY', ← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_toReal hY,
    ← ENNReal.ofReal_toReal hFm] at h
  rw [← ENNReal.ofReal_mul hc', ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ← ENNReal.ofReal_mul ha1, ← ENNReal.ofReal_mul ha2,
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  have h' := h.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (le_max_left e 0)))
  rw [← ENNReal.ofReal_add (by positivity) (le_max_right _ _)] at h'
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h'

/-- Cauchy–Schwarz in real form: `x ≤ (l/2) n + M/(2l)` for every `l > 0` gives `x² ≤ M n`. -/
theorem ce_sq_le_of_forall {x n M : ℝ} (hx : 0 ≤ x) (hn : 0 ≤ n) (hM : 0 < M)
    (h : ∀ l : ℝ, 0 < l → x ≤ l / 2 * n + 1 / (2 * l) * M) : x ^ 2 ≤ M * n := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hM.le hn
  · have h1 := h (M / x) (by positivity)
    have e : M / x / 2 * n + 1 / (2 * (M / x)) * M = M * n / (2 * x) + x / 2 := by
      field_simp
    rw [e] at h1
    have h2 : x / 2 ≤ M * n / (2 * x) := by linarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith

/-!
## The expectation recursion and the entrance statement
-/

/-- Travel-length bookkeeping: for `4 ≤ W s₀` and `0 ≤ t₁ + R`, every length
`travelLength W t₁ R s₀ ≤ j ≤ travelLength W t₁ R s₂` satisfies `(s₀/2) W ≤ j ≤ (t₁+R+s₂+1) W`. -/
theorem ce_range {W : ℕ} {t₁ R s₀ s₂ : ℝ} (hTR : 0 ≤ t₁ + R) (hs₀ : 0 < s₀) (hs₀₂ : s₀ ≤ s₂)
    (hWs : 4 ≤ (W : ℝ) * s₀) {j : ℕ} (h0 : travelLength W t₁ R s₀ ≤ j)
    (h2 : j ≤ travelLength W t₁ R s₂) :
    s₀ / 2 * W ≤ j ∧ (j : ℝ) ≤ (t₁ + R + (s₂ + 1)) * W := by
  have hW0 : 0 ≤ (W : ℝ) := Nat.cast_nonneg W
  have hlo : (W : ℝ) * (t₁ + R + s₀) < (travelLength W t₁ R s₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hhi : (travelLength W t₁ R s₂ : ℝ) ≤ (W : ℝ) * (t₁ + R + s₂) :=
    Nat.floor_le (mul_nonneg hW0 (by linarith))
  have h0' : (travelLength W t₁ R s₀ : ℝ) ≤ j := by exact_mod_cast h0
  have h2' : (j : ℝ) ≤ travelLength W t₁ R s₂ := by exact_mod_cast h2
  constructor <;> nlinarith

/-- **`ClockFractionalLogisticRecursion` from the weighted one-step inequality.** Hypotheses:
`EdgeClockMomentsContract`, `TransmissionLengthUniformContract` (jet and conductance moments
uniform in the preceding middle) and `ClockFractionalOneStep`. The recursion constants
`C' = C + C(1 + C_g' + C_γ')` and `c' = c/((1 + Kd)²(1 + C_γ'))` depend on `b, E, p, s₀, s₂`
only (chosen before the source and `t₁`); the error is `max e 0 + A/W³`.
-/
theorem ce_logisticRecursion_of_oneStep (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hStep : ClockFractionalOneStep) :
    ClockFractionalLogisticRecursion := by
  intro b hb hb' E hE hE' p hp hp' s₀ s₂ hs₀ hs₀₂
  obtain ⟨K, C, c, d, s, hK, hC, hc, hd, hs, hsrc⟩ :=
    hStep b hb hb' E hE hE' p hp hp' s₀ s₂ hs₀ hs₀₂
  set κI := min (E + 2) (2 - E) with hκI
  have hκI0 : 0 < κI := lt_min (by linarith) (by linarith)
  have hEI : E ∈ BlockBand.Internal.Contracts.Layers.bulkInterval κI :=
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩
  obtain ⟨Cγ, hCγ⟩ := edgeClockMoments hECM b hb hb' E hE hE' (s₂ + 1) (8 * p) (by linarith)
    (by positivity)
  obtain ⟨CJ, hCJ⟩ := hTLU.jet b hb hb' κI (s₀ / 2) 20 hκI0 (by positivity) (by norm_num)
  obtain ⟨CG, hCG⟩ := hTLU.conductance b hb hb' κI (s₀ / 2) 20 hκI0 (by positivity)
    (by norm_num)
  set M := 1 + max Cγ 0 with hM
  set Fb := 1 + max CG 0 + max Cγ 0 with hFb
  set AE := ce_AE K d CJ CG Cγ with hAE
  set Ay := 3 * ce_A K * ce_CPsi CJ Cγ with hAy
  set cn := c / ((1 + K * d) ^ 2 * M) with hcn
  set Cn := C + C * Fb with hCn
  set Atot := AE + 2 * cn * Ay * AE with hAtot
  have hM0 : 0 < M := by have := le_max_right Cγ 0; linarith
  have hFb0 : 0 ≤ Fb := by have := le_max_right CG 0; have := le_max_right Cγ 0; linarith
  have hAE0 : 0 ≤ AE := ce_AE_nonneg K d CJ CG Cγ hd
  have hAy0 : 0 ≤ Ay := by
    have := ce_CPsi_nonneg CJ Cγ; have : 0 ≤ ce_A K := by unfold ce_A; positivity
    positivity
  have hKd : 0 < 1 + K * d := by nlinarith
  refine ⟨Cn, cn, by positivity, fun t₁ R q hq => ?_⟩
  obtain ⟨ht₁, hR, hR1, hsrcT, hq1⟩ := hq
  have hq0 : ∀ x, 0 ≤ q x := hsrcT.1
  have hinj : IsBoundedInjection t₁ R 1 q := ⟨hq0, hq1, hsrcT.2.1⟩
  obtain ⟨e, he, W₀, hW₀⟩ := hsrc t₁ R q ⟨ht₁, hR, hR1, hsrcT, hq1⟩
  obtain ⟨Wγ, hWγ⟩ := hCγ (t₁ + R + (s₂ + 1))
  obtain ⟨WJ, hWJ⟩ := hCJ (t₁ + R + (s₂ + 1))
  obtain ⟨WG, hWG⟩ := hCG (t₁ + R + (s₂ + 1))
  refine ⟨fun W => max (e W) 0 + Atot / (W : ℝ) ^ 3, ?_,
    max (max W₀ Wγ) (max (max WJ WG) (⌈4 / s₀⌉₊ + 1)), fun W hW => ?_⟩
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
  · have hW0' : W₀ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
    have hWγ' : Wγ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
    have hWJ' : WJ ≤ W :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hW
    have hWG' : WG ≤ W :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hW
    have hWc : ⌈4 / s₀⌉₊ + 1 ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
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
      have hr := ce_range hTR hs₀ hs₀₂ hWs h0 h2
      have hjet := hWJ W hWJ' E hEI s hs j hr.1 hr.2
      ce_moments_at (s := s) hp hp' hK hd hW1 hq0 (le_trans le_self_add hjet)
        (le_trans le_add_self hjet) (hWG W hWG' E hEI j hr.1 hr.2)
        ((hWγ W hWγ' t₁ R 1 q ht₁ hR (by linarith) le_rfl hinj j hr.2).2)
    refine ⟨fun j => (ce_weightedMoment K b E p W j q).toReal, fun j => ENNReal.toReal_nonneg,
      fun j h0 h2 => ?_, fun j h0 h2 => ?_⟩
    · obtain ⟨h1, h2', -⟩ := hmom j h0 h2
      rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)]
      exact h2'
    · obtain ⟨hY1, hHY, hDc, -, hsplit, hcs, hXH, hFm⟩ := hmom j h0 h2.le
      obtain ⟨hY1', -, -, hsplit', -⟩ := hmom (j + 1) (by omega) h2
      have hstep := hW₀ W hW0' j h0 h2
      set Y := ce_weightedMoment K b E p W j q with hY
      set Y' := ce_weightedMoment K b E p W (j + 1) q with hY'
      set Rn := ce_retainedNext K b E p s d W j q with hRn
      set X := ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
        (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω)) ω ∂growthPathLaw W b with hX
      set N := ce_concavityMoment b E p s d W j q with hN
      set Fm := ce_forcingMoment b E p W j q with hFm'
      -- the exceptional part of the new length, on the old domain's complement
      have hYRn : Y' ≤ Rn + ENNReal.ofReal (AE / (W : ℝ) ^ 3) := hsplit' _ hDc
      have hYf : Y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY1
      have hY'f : Y' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY1'
      have hRnf : Rn ≠ ⊤ := by
        refine ne_top_of_le_ne_top hY'f (lintegral_mono fun ω => Set.indicator_le_self _ _ ω)
      have hXf : X ≠ ⊤ := ne_top_of_le_ne_top hYf (hXH.trans hHY)
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
      have hyW : Y.toReal ≤ W * Ay := ENNReal.toReal_le_of_le_ofReal (by positivity) hY1
      have hFv : Fm.toReal ≤ Fb := ENNReal.toReal_le_of_le_ofReal hFb0 hFm
      have hsplitr : Y.toReal ≤ (1 + K * d) * X.toReal + AE / (W : ℝ) ^ 3 := by
        rw [← ENNReal.ofReal_toReal hXf, ← ENNReal.ofReal_mul hKd.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)] at hsplit
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsplit
      have hcsr : X.toReal ^ 2 ≤ M * N.toReal := by
        refine ce_sq_le_of_forall ENNReal.toReal_nonneg ENNReal.toReal_nonneg hM0
          fun l hl => ?_
        have h := hcs l hl
        rw [← ENNReal.ofReal_toReal hNf, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
      have hfinal := ce_real_step (W := (W : ℝ)) (Fb := Fb) hW0 ENNReal.toReal_nonneg hC hc hK hd
        hM0 ENNReal.toReal_nonneg hFv le_rfl (by positivity) hstepr hsplitr hcsr hyW
      have e1 : max (e W) 0 + (AE / (W : ℝ) ^ 3 +
          2 * (c / ((1 + K * d) ^ 2 * M)) * Ay * (AE / (W : ℝ) ^ 3)) =
          max (e W) 0 + Atot / (W : ℝ) ^ 3 := by
        rw [hAtot, hcn]; ring
      rw [e1] at hfinal
      exact hfinal

/-- **`ClockFractionalEntranceContract` from the weighted one-step inequality**: from
`EdgeClockMomentsContract`, `TransmissionLengthUniformContract` and `ClockFractionalOneStep`,
through `ce_logisticRecursion_of_oneStep` and `clockFractionalEntrance_holds`.
-/
theorem clockFractionalEntrance_of_oneStep (hECM : EdgeClockMomentsContract)
    (hTLU : TransmissionLengthUniformContract) (hStep : ClockFractionalOneStep) :
    ClockFractionalEntranceContract :=
  clockFractionalEntrance_holds (ce_logisticRecursion_of_oneStep hECM hTLU hStep)

end BlockBand.Endpoints
