module

public import BlockBand.Endpoints.Response.RemoteHigherRecursionScalar
public import BlockBand.Endpoints.Response.RemoteHigherChainStep

/-!
# The moments of the higher clock at one path length

`rhr_moments_at`: with `n ≥ r` a natural number and the failure order `m = 2n + 6`, from the jet
bounds `‖δ₀‖₂₀ ≤ C_J/W`, `‖δ₀‖_m, ‖δ₁‖_m ≤ C_J^m/W`, the conductance moment `E|g|^m ≤ C_g` and
the edge-clock moment `E γ^{8pr} ≤ C_γ`:
1. a priori `y_j ≤ 3 A C_Ψ W^r` (from `H_p^r ≤ W^r γ^{pr}`);
2. exceptional sets `μ(Dᶜ) ≤ A_D W^{-m}` (Markov), and `y_j ≤ E[1_S(1 + Kδ₀)H_p^r] + A_E W⁻³` for
   every `S` with `μ(Sᶜ) ≤ A_D W^{-m}` (second moment with `l = W^{2n+3}`);
3. split `y_j ≤ (1 + Kd) E[1_D H_p^r] + A_E W⁻³`;
4. Young: `E[1_D H_p^r] ≤ (r/(r+1)) l E[1_D H_p^{r+1}/γ^p] + (1/(r+1)) l^{-r}(1 + C_γ')`;
5. `E[1_D H_p^r] ≤ y_j`;
6. forcing `E[|g|^{(r+1)(1-p)} γ^{pr}] ≤ 1 + C_g' + C_γ'`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

/-- The exceptional-set constant `A_D = 2 C_J'^m/d^m + C_g'/d^m` at failure order `m`. -/
def rhr_AD (d CJm CG : ℝ) (m : ℕ) : ℝ :=
  2 * (max CJm 0 ^ m / d ^ m) + max CG 0 / d ^ m

/-- `A_E = A_D + 3 A² C_Ψ` (exceptional sets of the higher recursion). -/
def rhr_AE (K d CJ CJm CG Cγ : ℝ) (m : ℕ) : ℝ :=
  rhr_AD d CJm CG m + 3 * ce_A K ^ 2 * ce_CPsi CJ Cγ

theorem rhr_AD_nonneg (d CJm CG : ℝ) (m : ℕ) (hd : 0 < d) : 0 ≤ rhr_AD d CJm CG m := by
  unfold rhr_AD
  have := le_max_right CJm 0; have := le_max_right CG 0
  positivity

theorem rhr_AE_nonneg (K d CJ CJm CG Cγ : ℝ) (m : ℕ) (hd : 0 < d) :
    0 ≤ rhr_AE K d CJ CJm CG Cγ m := by
  unfold rhr_AE ce_A
  have := ce_CPsi_nonneg CJ Cγ; have := rhr_AD_nonneg d CJm CG m hd
  positivity

/-- **The moments of the higher clock at one path length**; see the module
docstring. `X = E[1_D H_p^r]`. -/
theorem rhr_moments_at {b E p r K d CJ CJm CG Cγ : ℝ} {s : ℂ} {n : ℕ} (hp : 0 < p)
    (hp1 : p < 1) (hr : 1 ≤ r) (hrn : r ≤ n) (hK : 0 ≤ K) (hd : 0 < d) {W j : ℕ}
    (hW : 1 ≤ (W : ℝ)) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x)
    (hδ0 : eLpNorm (fun ω => ce_jet0 b E W j ω) (ENNReal.ofReal 20) (growthPathLaw W b) ≤
      ENNReal.ofReal (CJ / W))
    (hδ0m : eLpNorm (fun ω => ce_jet0 b E W j ω) (ENNReal.ofReal ((2 * n + 6 : ℕ) : ℝ))
      (growthPathLaw W b) ≤ ENNReal.ofReal (CJm / W))
    (hδ1m : eLpNorm (fun ω => ce_jet1 b E s W j ω) (ENNReal.ofReal ((2 * n + 6 : ℕ) : ℝ))
      (growthPathLaw W b) ≤ ENNReal.ofReal (CJm / W))
    (hg : ∫⁻ ω, ‖pathConductance b E W j ω‖ₑ ^ ((2 * n + 6 : ℕ) : ℝ) ∂growthPathLaw W b ≤
      ENNReal.ofReal CG)
    (hγ : edgeNearClockMoment b E (8 * (p * r)) W j q ≤
      ENNReal.ofReal (1 ^ (8 * (p * r)) * Cγ)) :
    rhn_weightedHigherMoment K b E p r W j q ≤
      ENNReal.ofReal ((W : ℝ) ^ r * (3 * ce_A K * ce_CPsi CJ Cγ)) ∧
    (growthPathLaw W b) (ce_jetDomain b E s d W j)ᶜ ≤
      ENNReal.ofReal (rhr_AD d CJm CG (2 * n + 6) / (W : ℝ) ^ (2 * n + 6)) ∧
    (∀ S : Set (GrowthPath W), (growthPathLaw W b) Sᶜ ≤
        ENNReal.ofReal (rhr_AD d CJm CG (2 * n + 6) / (W : ℝ) ^ (2 * n + 6)) →
      rhn_weightedHigherMoment K b E p r W j q ≤ ∫⁻ ω, S.indicator (fun ω => ENNReal.ofReal
          (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r)) ω ∂growthPathLaw W b +
        ENNReal.ofReal (rhr_AE K d CJ CJm CG Cγ (2 * n + 6) / W ^ 3)) ∧
    rhn_weightedHigherMoment K b E p r W j q ≤ ENNReal.ofReal (1 + K * d) *
        ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂growthPathLaw W b +
      ENNReal.ofReal (rhr_AE K d CJ CJm CG Cγ (2 * n + 6) / W ^ 3) ∧
    (∀ l : ℝ, 0 < l → ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂growthPathLaw W b ≤
        ENNReal.ofReal (r / (r + 1) * l) * rhc_concavityMoment b E p r s d W j q +
          ENNReal.ofReal (1 / (r + 1) * l ^ (-r)) * ENNReal.ofReal (1 + max Cγ 0)) ∧
    ∫⁻ ω, (ce_jetDomain b E s d W j).indicator
          (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂growthPathLaw W b ≤
      rhn_weightedHigherMoment K b E p r W j q ∧
    rhc_forcingMoment b E p r W j q ≤ ENNReal.ofReal (1 + max CG 0 + max Cγ 0) := by
  have hP := isProbabilityMeasure_growthPathLaw W b
  have hW0 : 0 < (W : ℝ) := by linarith
  have hr0 : 0 < r := by linarith
  set m : ℕ := 2 * n + 6 with hm
  set μ := growthPathLaw W b with hμ
  set D := ce_jetDomain b E s d W j with hD
  set CJ' := max CJ 0 with hCJ'
  set CJm' := max CJm 0 with hCJm'
  set Cγ' := max Cγ 0 with hCγ'
  set CG' := max CG 0 with hCG'
  set A := ce_A K with hA
  set CΨ := ce_CPsi CJ Cγ with hCΨ
  have hA0 : 0 ≤ A := by rw [hA]; unfold ce_A; positivity
  have hCΨ0 : 0 ≤ CΨ := ce_CPsi_nonneg CJ Cγ
  have hCJ'0 : 0 ≤ CJ' := le_max_right _ _
  have hCJm'0 : 0 ≤ CJm' := le_max_right _ _
  have hCγ'0 : 0 ≤ Cγ' := le_max_right _ _
  have hCG'0 : 0 ≤ CG' := le_max_right _ _
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by rw [hm]; push_cast; linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  -- pointwise facts
  have hδ0n : ∀ ω, 0 ≤ ce_jet0 b E W j ω := fun ω => norm_nonneg _
  have hδ1n : ∀ ω, 0 ≤ ce_jet1 b E s W j ω := fun ω => norm_nonneg _
  have hγn : ∀ ω, 0 ≤ ce_clockTrace b E W j q ω := ce_clockTrace_nonneg b E W j hq
  set x : GrowthPath W → ℝ := fun ω => ce_clockTrace b E W j q ω ^ (p * r) with hx
  have hxn : ∀ ω, 0 ≤ x ω := fun ω => Real.rpow_nonneg (hγn ω) _
  have hHn : ∀ ω, 0 ≤ ce_fracClock b E p W j q ω := ce_fracClock_nonneg b E p W j q
  have hHrn : ∀ ω, 0 ≤ ce_fracClock b E p W j q ω ^ r := fun ω => Real.rpow_nonneg (hHn ω) _
  have hHle : ∀ ω, ce_fracClock b E p W j q ω ≤ W * ce_clockTrace b E W j q ω ^ p :=
    ce_fracClock_le b E p hp hp1 hW j hq
  have hGr : ∀ ω, (ce_clockTrace b E W j q ω ^ p) ^ r = x ω := fun ω => by
    rw [hx, ← Real.rpow_mul (hγn ω)]
  have hHr : ∀ ω, ce_fracClock b E p W j q ω ^ r ≤ (W : ℝ) ^ r * x ω := fun ω => by
    rw [← hGr, ← Real.mul_rpow hW0.le (Real.rpow_nonneg (hγn ω) _)]
    exact Real.rpow_le_rpow (hHn ω) (hHle ω) hr0.le
  have hwn : ∀ ω, 1 ≤ ce_weight K b E W j ω := fun ω => by
    unfold ce_weight; nlinarith [hδ0n ω]
  have hWr0 : 0 ≤ (W : ℝ) ^ r := Real.rpow_nonneg hW0.le _
  have hWrn : (W : ℝ) ^ r ≤ (W : ℝ) ^ n := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hW hrn
  -- measurability and moments of `δ₀, δ₁`
  obtain ⟨hδ0a, hδ0i⟩ := ce_lintegral_pow_of_eLpNorm μ _ hδ0n (by norm_num) hδ0
  obtain ⟨hδ0ma, hδ0mi⟩ := ce_lintegral_pow_of_eLpNorm μ _ hδ0n hm1 hδ0m
  obtain ⟨hδ1ma, hδ1mi⟩ := ce_lintegral_pow_of_eLpNorm μ _ hδ1n hm1 hδ1m
  have hmaxJ : max (CJ / W) 0 = CJ' / W := by
    have := max_div_div_right hW0.le CJ 0; rwa [zero_div] at this
  have hmaxJm : max (CJm / W) 0 = CJm' / W := by
    have := max_div_div_right hW0.le CJm 0; rwa [zero_div] at this
  rw [hmaxJ] at hδ0i
  rw [hmaxJm] at hδ0mi hδ1mi
  have hpow20 : ∀ y : ℝ, y ^ (20 : ℝ) = y ^ (20 : ℕ) := fun y => Real.rpow_ofNat y 20
  have hpowm : ∀ y : ℝ, y ^ (m : ℝ) = y ^ m := fun y => Real.rpow_natCast y m
  have hJW : (CJ' / W) ^ (20 : ℝ) = CJ' ^ 20 / (W : ℝ) ^ 20 := by rw [hpow20, div_pow]
  have hJWm : (CJm' / W) ^ (m : ℝ) = CJm' ^ m / (W : ℝ) ^ m := by rw [hpowm, div_pow]
  rw [hJW] at hδ0i
  rw [hJWm] at hδ0mi hδ1mi
  have hγm : Measurable (fun ω => ce_clockTrace b E W j q ω) := ce_measurable_clockTrace b E W j q
  have hgm : Measurable (fun ω => pathConductance b E W j ω) := ce_measurable_conductance b E W j
  have hxm : Measurable x := hγm.pow_const _
  -- the edge moment as `E x⁸ ≤ C_γ'`
  have hγi : ∫⁻ ω, ENNReal.ofReal (x ω ^ 8) ∂μ ≤ ENNReal.ofReal Cγ' := by
    have e : ∀ ω, x ω ^ 8 = (nearClock b E W j q ω).trace.re ^ (8 * (p * r)) := fun ω => by
      show (ce_clockTrace b E W j q ω ^ (p * r)) ^ 8 = ce_clockTrace b E W j q ω ^ (8 * (p * r))
      rw [show (8 : ℝ) * (p * r) = (p * r) * ((8 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_mul_natCast (hγn ω)]
    simp_rw [e]
    refine hγ.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.one_rpow, one_mul]; exact le_max_left _ _
  -- the conductance moment
  have hgi : ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ (m : ℝ)) ∂μ ≤
      ENNReal.ofReal CG := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hg
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hm0.le]
  -- `μ(Dᶜ)`
  set AD := rhr_AD d CJm CG m with hAD
  have hAD0 : 0 ≤ AD := rhr_AD_nonneg d CJm CG m hd
  have hDc : μ Dᶜ ≤ ENNReal.ofReal (AD / (W : ℝ) ^ m) := by
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
        ∫⁻ ω, ENNReal.ofReal (|f ω| ^ (m : ℝ)) ∂μ = ∫⁻ ω, ENNReal.ofReal (f ω ^ (m : ℝ)) ∂μ :=
      fun f hf => lintegral_congr fun ω => by rw [abs_of_nonneg (hf ω)]
    have m1 := ce_measure_lt_le μ _ hδ0ma.aemeasurable hd hm0
      ((habs _ hδ0n).le.trans hδ0mi)
    have m2 := ce_measure_lt_le μ _ hδ1ma.aemeasurable hd hm0
      ((habs _ hδ1n).le.trans hδ1mi)
    have m3 := ce_measure_lt_le μ _ hgm.aemeasurable (mul_pos hd hW0) hm0 hgi
    rw [hpowm] at m1 m2 m3
    calc μ Dᶜ ≤ μ (({ω | d < ce_jet0 b E W j ω} ∪ {ω | d < ce_jet1 b E s W j ω}) ∪
          {ω | d * W < pathConductance b E W j ω}) := measure_mono hsub
      _ ≤ μ {ω | d < ce_jet0 b E W j ω} + μ {ω | d < ce_jet1 b E s W j ω} +
          μ {ω | d * W < pathConductance b E W j ω} :=
          (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
      _ ≤ ENNReal.ofReal (CJm' ^ m / (W : ℝ) ^ m / d ^ m) +
          ENNReal.ofReal (CJm' ^ m / (W : ℝ) ^ m / d ^ m) +
          ENNReal.ofReal (CG / (d * W) ^ m) := add_le_add (add_le_add m1 m2) m3
      _ ≤ ENNReal.ofReal (CJm' ^ m / (W : ℝ) ^ m / d ^ m) +
          ENNReal.ofReal (CJm' ^ m / (W : ℝ) ^ m / d ^ m) +
          ENNReal.ofReal (CG' / d ^ m / (W : ℝ) ^ m) := by
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          rw [mul_pow, div_div]
          exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have e1 : CJm' ^ m / (W : ℝ) ^ m / d ^ m = CJm' ^ m / d ^ m / (W : ℝ) ^ m := by ring
          have e2 : AD / (W : ℝ) ^ m =
              2 * (CJm' ^ m / d ^ m / (W : ℝ) ^ m) + CG' / d ^ m / (W : ℝ) ^ m := by
            rw [hAD, rhr_AD]; ring
          rw [e2, e1]; linarith
  -- the envelope `Ψ_b = 1 + δ₀²⁰ + x⁸`
  set Ψb : GrowthPath W → ℝ := fun ω => 1 + ce_jet0 b E W j ω ^ 20 + x ω ^ 8 with hΨb
  have hu20 : AEMeasurable (fun ω => ENNReal.ofReal (ce_jet0 b E W j ω ^ 20)) μ :=
    (hδ0a.aemeasurable.pow_const 20).ennreal_ofReal
  have hΨbm : AEMeasurable (fun ω => ENNReal.ofReal (Ψb ω)) μ :=
    (((aemeasurable_const.add (hδ0a.aemeasurable.pow_const 20)).add
      (hxm.pow_const 8).aemeasurable)).ennreal_ofReal
  have hΨbi : ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ ≤ ENNReal.ofReal CΨ := by
    rw [ce_lintegral_one_add_add _ _ (fun ω => pow_nonneg (hδ0n ω) 20)
      (fun ω => pow_nonneg (hxn ω) 8) hu20]
    have h1 : ∫⁻ ω, ENNReal.ofReal (ce_jet0 b E W j ω ^ 20) ∂μ ≤ ENNReal.ofReal (CJ' ^ 20) := by
      refine le_trans (le_of_eq (lintegral_congr fun ω => by rw [hpow20])) (hδ0i.trans ?_)
      refine ENNReal.ofReal_le_ofReal (div_le_self (by positivity) ?_)
      exact one_le_pow₀ hW
    calc 1 + ∫⁻ ω, ENNReal.ofReal (ce_jet0 b E W j ω ^ 20) ∂μ +
          ∫⁻ ω, ENNReal.ofReal (x ω ^ 8) ∂μ
        ≤ ENNReal.ofReal 1 + ENNReal.ofReal (CJ' ^ 20) + ENNReal.ofReal Cγ' := by
          rw [ENNReal.ofReal_one]; gcongr
      _ = ENNReal.ofReal CΨ := by
          rw [← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_add (by positivity) hCγ'0, hCΨ, ce_CPsi]
  -- `Φ = 3 (W^r A)² Ψ_b`
  set Φ : GrowthPath W → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2 * Ψb ω) with hΦ
  have hΦm : AEMeasurable Φ μ := by
    have : Φ = fun ω => ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2) * ENNReal.ofReal (Ψb ω) := by
      funext ω; rw [hΦ]; exact ENNReal.ofReal_mul (by positivity)
    rw [this]; exact hΨbm.const_mul _
  have hΦi : ∫⁻ ω, Φ ω ∂μ ≤ ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2 * CΨ) := by
    calc ∫⁻ ω, Φ ω ∂μ = ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun ω => ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2) * ENNReal.ofReal CΨ := by gcongr
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  -- the envelope `F = W^r A Ψ_s`, `Ψ_s = 1 + δ₀¹⁰ + x⁴`
  set F : GrowthPath W → ℝ := fun ω =>
    (W : ℝ) ^ r * A * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4) with hF
  have hFsq : ∀ ω, ENNReal.ofReal (F ω ^ 2) ≤ Φ ω := fun ω => by
    refine ENNReal.ofReal_le_ofReal ?_
    have h := (ce_envelope_sq_le (hδ0n ω) (hxn ω)).1
    have e : F ω ^ 2 = ((W : ℝ) ^ r * A) ^ 2 * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4) ^ 2 := by
      simp only [hF]; ring
    rw [e]
    calc ((W : ℝ) ^ r * A) ^ 2 * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4) ^ 2
        ≤ ((W : ℝ) ^ r * A) ^ 2 * (3 * Ψb ω) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = 3 * ((W : ℝ) ^ r * A) ^ 2 * Ψb ω := by ring
  have hwHF : ∀ ω, ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r ≤ F ω := fun ω => by
    have h : (1 + K * ce_jet0 b E W j ω) * x ω ≤ A * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4) := by
      rw [hA]; unfold ce_A; exact (ce_envelope_le (hδ0n ω) (hxn ω)).1
    calc ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r
        ≤ ce_weight K b E W j ω * ((W : ℝ) ^ r * x ω) :=
          mul_le_mul_of_nonneg_left (hHr ω) (by linarith [hwn ω])
      _ = (W : ℝ) ^ r * ((1 + K * ce_jet0 b E W j ω) * x ω) := by
          simp only [ce_weight]; ring
      _ ≤ (W : ℝ) ^ r * (A * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4)) :=
          mul_le_mul_of_nonneg_left h hWr0
      _ = F ω := by simp only [hF]; ring
  -- the bracket of the exceptional sets, with `l = W^{2n+3}`
  set AE := rhr_AE K d CJ CJm CG Cγ m with hAE
  have hbrS : ∀ S : Set (GrowthPath W), μ Sᶜ ≤ ENNReal.ofReal (AD / (W : ℝ) ^ m) →
      ENNReal.ofReal ((W : ℝ) ^ (2 * n + 3) / 2) * μ Sᶜ +
      ENNReal.ofReal (1 / (2 * (W : ℝ) ^ (2 * n + 3))) * ∫⁻ ω, Φ ω ∂μ ≤
      ENNReal.ofReal (AE / (W : ℝ) ^ 3) := by
    intro S hS
    calc _ ≤ ENNReal.ofReal ((W : ℝ) ^ (2 * n + 3) / 2) * ENNReal.ofReal (AD / (W : ℝ) ^ m) +
          ENNReal.ofReal (1 / (2 * (W : ℝ) ^ (2 * n + 3))) *
            ENNReal.ofReal (3 * ((W : ℝ) ^ r * A) ^ 2 * CΨ) := by gcongr
      _ = ENNReal.ofReal ((W : ℝ) ^ (2 * n + 3) / 2 * (AD / (W : ℝ) ^ m) +
          1 / (2 * (W : ℝ) ^ (2 * n + 3)) * (3 * ((W : ℝ) ^ r * A) ^ 2 * CΨ)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hWm : (W : ℝ) ^ m = (W : ℝ) ^ (2 * n + 3) * (W : ℝ) ^ 3 := by
            rw [← pow_add]
          have hW3 : 0 < (W : ℝ) ^ 3 := by positivity
          have hWn3 : 0 < (W : ℝ) ^ (2 * n + 3) := by positivity
          have e1 : (W : ℝ) ^ (2 * n + 3) / 2 * (AD / (W : ℝ) ^ m) = AD / (2 * (W : ℝ) ^ 3) := by
            rw [hWm]; field_simp
          have hsq : ((W : ℝ) ^ r * A) ^ 2 ≤ (W : ℝ) ^ (2 * n) * A ^ 2 := by
            rw [mul_pow, pow_mul']
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hWr0 hWrn 2) (sq_nonneg _)
          have e2 : 1 / (2 * (W : ℝ) ^ (2 * n + 3)) * (3 * ((W : ℝ) ^ (2 * n) * A ^ 2) * CΨ) =
              3 * A ^ 2 * CΨ / (2 * (W : ℝ) ^ 3) := by
            rw [pow_add]; field_simp
          have h2 : 1 / (2 * (W : ℝ) ^ (2 * n + 3)) * (3 * ((W : ℝ) ^ r * A) ^ 2 * CΨ) ≤
              3 * A ^ 2 * CΨ / (2 * (W : ℝ) ^ 3) := by
            rw [← e2]
            gcongr
          have e3 : AE / (W : ℝ) ^ 3 = AD / (W : ℝ) ^ 3 + 3 * A ^ 2 * CΨ / (W : ℝ) ^ 3 := by
            rw [hAE, hAD, hA, hCΨ]; unfold rhr_AE; ring
          have h1 : AD / (2 * (W : ℝ) ^ 3) ≤ AD / (W : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left hAD0 hW3 (by linarith)
          have h3 : 3 * A ^ 2 * CΨ / (2 * (W : ℝ) ^ 3) ≤ 3 * A ^ 2 * CΨ / (W : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left (by positivity) hW3 (by linarith)
          rw [e1, e3]; linarith
  have hbr := hbrS D hDc
  have hl : (0 : ℝ) < (W : ℝ) ^ (2 * n + 3) := by positivity
  refine ⟨?_, hDc, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) a priori bound
    calc rhn_weightedHigherMoment K b E p r W j q ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hwHF ω)
      _ ≤ ∫⁻ ω, ENNReal.ofReal (3 * (W : ℝ) ^ r * A) * ENNReal.ofReal (Ψb ω) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h := (ce_envelope_sq_le (hδ0n ω) (hxn ω)).2
          have : F ω = (W : ℝ) ^ r * A * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4) := rfl
          rw [this]
          calc (W : ℝ) ^ r * A * (1 + ce_jet0 b E W j ω ^ 10 + x ω ^ 4)
              ≤ (W : ℝ) ^ r * A * (3 * Ψb ω) := mul_le_mul_of_nonneg_left h (by positivity)
            _ = 3 * (W : ℝ) ^ r * A * Ψb ω := by ring
      _ = ENNReal.ofReal (3 * (W : ℝ) ^ r * A) * ∫⁻ ω, ENNReal.ofReal (Ψb ω) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3 * (W : ℝ) ^ r * A) * ENNReal.ofReal CΨ := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  · -- (2') split over any large set
    intro S hS
    have h := ce_lintegral_le_split μ S
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r))
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r))
      Φ F hΦm hl (fun ω _ => le_rfl)
      (fun ω _ => ENNReal.ofReal_le_ofReal (hwHF ω)) hFsq
    exact h.trans (add_le_add le_rfl (hbrS S hS))
  · -- (3) split over the jet domain
    have h := ce_lintegral_le_split μ D
      (fun ω => ENNReal.ofReal (ce_weight K b E W j ω * ce_fracClock b E p W j q ω ^ r))
      (fun ω => ENNReal.ofReal (1 + K * d) * ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r))
      Φ F hΦm hl
      (fun ω hω => by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (hHrn ω))
        have : ce_jet0 b E W j ω ≤ d := hω.1
        simp only [ce_weight]; nlinarith)
      (fun ω _ => ENNReal.ofReal_le_ofReal (hwHF ω)) hFsq
    have hind : ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (1 + K * d) *
        ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂μ = ENNReal.ofReal (1 + K * d) *
          ∫⁻ ω, D.indicator (fun ω => ENNReal.ofReal (ce_fracClock b E p W j q ω ^ r)) ω ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ D
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [hind] at h
    exact h.trans (add_le_add le_rfl hbr)
  · -- (4) Young
    intro l hl
    have hGm : AEMeasurable (fun ω => ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ r)) μ :=
      ((hγm.pow_const p).pow_const r).ennreal_ofReal.aemeasurable
    have h := rhr_lintegral_indicator_le_young μ D (fun ω => ce_fracClock b E p W j q ω)
      (fun ω => ce_clockTrace b E W j q ω ^ p) hr0 hGm (fun ω => Real.rpow_nonneg (hγn ω) _)
      hHn (fun ω h0 => ce_fracClock_eq_zero b E p hp hp1 hW j hq ω h0) hl
    refine h.trans (add_le_add le_rfl ?_)
    gcongr
    calc ∫⁻ ω, ENNReal.ofReal ((ce_clockTrace b E W j q ω ^ p) ^ r) ∂μ
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (x ω ^ 8)) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [hGr, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (pow_nonneg (hxn ω) 8)]
          exact ENNReal.ofReal_le_ofReal (ce_le_one_add_pow_eight (hxn ω))
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (x ω ^ 8) ∂μ := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal Cγ' := by rw [ENNReal.ofReal_one]; gcongr
      _ = ENNReal.ofReal (1 + Cγ') := (ENNReal.ofReal_add zero_le_one hCγ'0).symm
  · -- (5) `E[1_D H_p^r] ≤ y_j`
    refine (lintegral_mono fun ω => Set.indicator_le_self _ _ ω).trans ?_
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_left (hHrn ω) (hwn ω)
  · -- (6) forcing
    have ham : 2 * ((r + 1) * (1 - p)) ≤ (m : ℝ) := by
      have hn' : r ≤ (n : ℝ) := hrn
      rw [hm]; push_cast; nlinarith
    calc rhc_forcingMoment b E p r W j q
        ≤ ∫⁻ ω, ENNReal.ofReal (1 + |pathConductance b E W j ω| ^ (m : ℝ) + x ω ^ 8) ∂μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
            (rhr_forcing_le (by nlinarith) ham (hxn ω))
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (|pathConductance b E W j ω| ^ (m : ℝ)) ∂μ +
            ∫⁻ ω, ENNReal.ofReal (x ω ^ 8) ∂μ :=
          ce_lintegral_one_add_add _ _ (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
            (fun ω => pow_nonneg (hxn ω) 8)
            ((hgm.abs.pow_const _).ennreal_ofReal.aemeasurable)
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal CG' + ENNReal.ofReal Cγ' := by
          rw [ENNReal.ofReal_one]
          gcongr
          exact hgi.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (1 + CG' + Cγ') := by
          rw [← ENNReal.ofReal_add zero_le_one hCG'0, ← ENNReal.ofReal_add (by positivity) hCγ'0]

end BlockBand.Endpoints
