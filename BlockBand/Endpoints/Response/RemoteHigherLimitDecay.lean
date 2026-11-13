module

public import BlockBand.Endpoints.Response.RemoteHigherLimitDefs
public import BlockBand.Endpoints.Response.RemoteHigherLimitScalar
public import BlockBand.Endpoints.Response.NearSchattenLimit
public import BlockBand.Endpoints.Response.RemoteHigherNearDefs
public import BlockBand.Endpoints.Response.RemoteHigherNearPassage

/-!
# Higher clock decay at critical limits from the regularized higher generator

`rhl_limitDecay (hLater) (hRG)` proves `RhHigherLimitDecay`. Write `Φ_ε = (H_ε + ε^p)^r` and
`ε = ε_n = 1/(n+1)`. The proof has four steps.

1. Entrance: `RhnHigherLater` at `p₀ = p/2` (`p₀r < 1`) bounds `E (Tr A^{p₀})^r` on the travel
   interval `[s, s+t]` uniformly for `W ≥ W₀`; the lower passage
   `rhn_lintegral_limitFracTrace_rpow_le` gives `E H_{p₀}(μ_u)^r ≤ C₀`.
2. Comparison: `H_ε ≤ Diss_ε + (H_ε - Diss_ε)` with `H_ε - Diss_ε ≤ 2ε^{p-p₀}H_{p₀}`
   (the power regularization bound, `ns_regTrace_le`), hence
   `Φ_ε ≤ (H_ε+ε^p)^{r-1}Diss_ε + (H_ε+ε^p)^{r-1}Err_ε`, `Err_ε = (H_ε - Diss_ε) + ε^p`;
   Hölder (`rhl_lintegral_rpowMul_le`) and the monotonicity of `E Φ_ε` (from the integrated
   inequality) bound the last expectation by
   `c_ε = M^{(r-1)/r}(2^{r-1}((2ε^{p-p₀})^r C₀ + ε^{pr}))^{1/r} → 0`,
   `M = 2^{r-1}(E H_p(s)^r + 1)`.
3. Gronwall (`ns_gronwall`): `E Φ_ε(s+t) ≤ e^{-κ_r t} E Φ_ε(s) + c_ε`.
4. `ε ↓ 0`: Fatou on the left (`H_p ≤ liminf H_{ε_n}`), and on the right
   `E Φ_ε(s) ≤ E(H_p + ε^p)^r(s) ≤ (1-τ)^{1-r} E H_p(s)^r + τ^{1-r}ε^{pr}`
   (`rhl_add_rpow_le`); then `τ ↓ 0` (`rhl_le_of_weighted_one`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open scoped ENNReal
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

theorem rhl_decayRate_nonneg {b E p r : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp : 0 < p) (hr : 1 ≤ r) (hpr : p * r < 1) : 0 ≤ rhlDecayRate b E p r := by
  unfold rhlDecayRate
  have := ns_transportD0_pos hb hE hE'
  have : 0 < 1 - r * p := by linarith
  have : 0 < r := by linarith
  positivity

theorem rhl_tendsto_ofReal_eps_rpow {p r : ℝ} (hp : 0 < p) (hr : 0 < r) :
    Tendsto (fun n => ENNReal.ofReal (nsEps n ^ p) ^ r) atTop (𝓝 0) := by
  have h := rhn_tendsto_regError_rpow (p₀ := 0) hp hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    fun n => ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hr.le
  rw [sub_zero]
  have := Real.rpow_nonneg (ns_eps_pos n).le p
  linarith

/-- `RhHigherLimitDecay` from `RhnHigherLater` (proved from the higher recursion,
`rhn_higherLater_of_recursion`) and `RhlRegularizedLimitGenerator`; see the module docstring. -/
theorem rhl_limitDecay (hLater : RhnHigherLater) (hRG : RhlRegularizedLimitGenerator) :
    RhHigherLimitDecay := by
  intro b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq Ω _ P Z hWL μ hμ s t hs ht
  have hP := hWL.prob
  set t₀ := t₁ + R with ht₀
  set u₀ := t₀ + s with hu₀
  set T' := u₀ + t with hT'
  set p₀ := p / 2 with hp₀
  have hp₀0 : 0 < p₀ := by positivity
  have hp₀p : p₀ < p := by linarith
  have hp₀1 : p₀ < 1 := by linarith
  have hr0 : 0 < r := by linarith
  have hp₀r : p₀ * r < 1 := by rw [hp₀]; nlinarith
  have hqnn := ns_isUnitSource_nonneg hq
  have hmeas : ∀ u, t₀ ≤ u → ∀ k, 1 ≤ k → Measurable (Z (clockWord k) u) := fun u hu k hk =>
    hWL.measurable _ (ns_isOrdinaryWord_clockWord hk) u hu
  obtain ⟨φ, hφ, hfdd⟩ := ns_fdd_of_isWordLimit hWL
  -- the entrance: `E H_{p₀}(μ_u)^r ≤ C₀` on `[u₀, T']`
  obtain ⟨C₀, hC₀⟩ := hLater b hb hb' E hE hE' p₀ r hp₀0 hp₀1 hr hp₀r s (s + t) hs (by linarith)
  obtain ⟨W₀, hW₀⟩ := hC₀ t₁ R q hq
  have hH0 : ∀ u ∈ Icc u₀ T', ∫⁻ ω, limitFracTrace p₀ (μ u ω) ^ r ∂P ≤ ENNReal.ofReal C₀ := by
    intro u hu
    have htu : t₀ ≤ u := by linarith [hu.1]
    refine rhn_lintegral_limitFracTrace_rpow_le hqnn htu (hmeas u htu) hφ hfdd (hμ u htu)
      hp₀0 hp₀1 hr0 (eventually_atTop.2 ⟨W₀, fun W hW => ?_⟩)
    have h := hW₀ W hW (u - t₀) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rwa [ns_travelLength_eq] at h
  set Hs := ∫⁻ ω, limitFracTrace p (μ u₀ ω) ^ r ∂P with hHs
  set e := ENNReal.ofReal (Real.exp (-(transportD0 b E * r * p * (1 - r * p) * t / 2))) with he
  rcases eq_or_ne Hs ⊤ with hHtop | hHfin
  · rw [hHtop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']; exact le_top
  set κ := rhlDecayRate b E p r with hκ
  have hκ0 : 0 ≤ κ := rhl_decayRate_nonneg hb hE hE' hp hr hpr
  have h2top : (2 : ℝ≥0∞) ^ (r - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)
  set M : ℝ≥0∞ := 2 ^ (r - 1) * (Hs + 1) with hM
  have hMtop : M ≠ ⊤ := ENNReal.mul_ne_top h2top (ENNReal.add_ne_top.2 ⟨hHfin, ENNReal.one_ne_top⟩)
  set N : ℕ → ℝ≥0∞ := fun n => 2 ^ (r - 1) * (ENNReal.ofReal (2 * nsEps n ^ (p - p₀)) ^ r *
    ENNReal.ofReal C₀ + ENNReal.ofReal (nsEps n ^ p) ^ r) with hN
  set c : ℕ → ℝ≥0∞ := fun n => M ^ ((r - 1) / r) * N n ^ (1 / r) with hc
  have hr1r : 0 ≤ (r - 1) / r := div_nonneg (by linarith) hr0.le
  have hNtop : ∀ n, N n ≠ ⊤ := fun n => ENNReal.mul_ne_top h2top (ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top, ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top⟩)
  have hctop : ∀ n, c n ≠ ⊤ := fun n => ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hr1r hMtop) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (hNtop n))
  have hδ1 : ∀ n, ENNReal.ofReal (nsEps n ^ p) ^ r ≤ 1 := fun n => by
    refine ENNReal.rpow_le_one ?_ hr0.le
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_one (ns_eps_pos n).le ?_ hp.le)
    have := rhl_eps_half_lt_one n
    unfold nsEps; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  -- the right end: `E Φ_ε(u₀) ≤ E (H_p + ε^p)^r(u₀)`
  have hYp : ∀ n ω, rhlPowTrace p r (nsEps n) (μ u₀ ω) ≤
      (limitFracTrace p (μ u₀ ω) + ENNReal.ofReal (nsEps n ^ p)) ^ r := fun n ω =>
    ENNReal.rpow_le_rpow (add_le_add_left
      (ns_regTrace_le_limitFracTrace hp hp1 (ns_eps_pos n) _) _) hr0.le
  have hY0 : ∀ n, ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ u₀ ω) ∂P ≤ M := by
    intro n
    calc ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ u₀ ω) ∂P
        ≤ ∫⁻ ω, 2 ^ (r - 1) * (limitFracTrace p (μ u₀ ω) ^ r + 1) ∂P := by
          refine lintegral_mono fun ω => (hYp n ω).trans ?_
          refine (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr).trans ?_
          gcongr
          exact hδ1 n
      _ = M := by
          rw [lintegral_const_mul' _ _ h2top, lintegral_add_right _ measurable_const,
            lintegral_const, measure_univ, mul_one]
  -- Gronwall at each `ε_n`
  have hgron : ∀ n, ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ T' ω) ∂P ≤
      ENNReal.ofReal (Real.exp (-(κ * (T' - u₀)))) *
        ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ u₀ ω) ∂P + c n := by
    intro n
    have hε := ns_eps_pos n
    set ε := nsEps n
    have hstep : ∀ u₁ u₂ : ℝ, u₀ ≤ u₁ → u₁ ≤ u₂ → u₂ ≤ T' →
        ∫⁻ ω, rhlPowTrace p r ε (μ u₂ ω) ∂P + ENNReal.ofReal κ *
          ∫⁻ u in Icc u₁ u₂, ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P ≤
        ∫⁻ ω, rhlPowTrace p r ε (μ u₁ ω) ∂P := fun u₁ u₂ h1 h2 _ =>
      hRG b hb hb' E hE hE' p r hp hp1 hr hpr t₁ R q hq Ω _ P Z hWL μ hμ ε hε u₁ u₂
        (by linarith) h2
    refine ns_gronwall (Y := fun u => ∫⁻ ω, rhlPowTrace p r ε (μ u ω) ∂P)
      (X := fun u => ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P) (a := u₀) (b := T') (c := c n)
      (by linarith) hκ0 (hctop n) hstep ?_
    intro u hu
    have htu : t₀ ≤ u := by linarith [hu.1]
    have hYu : ∫⁻ ω, rhlPowTrace p r ε (μ u ω) ∂P ≤ M :=
      (le_trans le_self_add (hstep u₀ u le_rfl hu.1 hu.2)).trans (hY0 n)
    have hHm := ns_aemeasurable_regTrace (hmeas u htu) (hμ u htu) hp.le hε
    have hDm := ns_aemeasurable_dissTrace (p := p) (hmeas u htu) (hμ u htu) hε
    set F : Ω → ℝ≥0∞ := fun ω => nsRegTrace p ε (μ u ω) + ENNReal.ofReal (ε ^ p) with hF
    set Er : Ω → ℝ≥0∞ := fun ω => (nsRegTrace p ε (μ u ω) - nsDissTrace p ε (μ u ω)) +
      ENNReal.ofReal (ε ^ p) with hEr
    have hFm : AEMeasurable F P := hHm.add aemeasurable_const
    have hErm : AEMeasurable Er P := (hHm.sub hDm).add aemeasurable_const
    have hErr : ∫⁻ ω, Er ω ^ r ∂P ≤ N n := by
      calc ∫⁻ ω, Er ω ^ r ∂P
          ≤ ∫⁻ ω, 2 ^ (r - 1) * (ENNReal.ofReal (2 * ε ^ (p - p₀)) ^ r *
              limitFracTrace p₀ (μ u ω) ^ r + ENNReal.ofReal (ε ^ p) ^ r) ∂P := by
            refine lintegral_mono fun ω => (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr).trans ?_
            gcongr
            rw [← ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
            exact ENNReal.rpow_le_rpow (tsub_le_iff_left.2 (ns_regTrace_le hp₀0 hp₀p hp1 hε _))
              hr0.le
        _ = 2 ^ (r - 1) * (ENNReal.ofReal (2 * ε ^ (p - p₀)) ^ r *
              ∫⁻ ω, limitFracTrace p₀ (μ u ω) ^ r ∂P + ENNReal.ofReal (ε ^ p) ^ r) := by
            rw [lintegral_const_mul' _ _ h2top, lintegral_add_right _ measurable_const,
              lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofReal_ne_top),
              lintegral_const, measure_univ, mul_one]
        _ ≤ N n := by
            simp only [hN]
            gcongr
            exact hH0 u hu
    have hHol := rhl_lintegral_rpowMul_le hFm hErm hr hYu hErr
    calc ∫⁻ ω, rhlPowTrace p r ε (μ u ω) ∂P
        ≤ ∫⁻ ω, (rhlDissPowTrace p r ε (μ u ω) + F ω ^ (r - 1) * Er ω) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hsplit : F ω ^ r = F ω ^ (r - 1) * F ω := by
            have h := ENNReal.rpow_add_of_nonneg (x := F ω) (r - 1) 1 (by linarith) zero_le_one
            rwa [ENNReal.rpow_one, sub_add_cancel] at h
          have hle : F ω ≤ nsDissTrace p ε (μ u ω) + Er ω := by
            simp only [hF, hEr, ← add_assoc]
            exact add_le_add_left le_add_tsub _
          unfold rhlPowTrace rhlDissPowTrace
          calc (nsRegTrace p ε (μ u ω) + ENNReal.ofReal (ε ^ p)) ^ r = F ω ^ r := rfl
            _ = F ω ^ (r - 1) * F ω := hsplit
            _ ≤ F ω ^ (r - 1) * (nsDissTrace p ε (μ u ω) + Er ω) := by gcongr
            _ = _ := by rw [mul_add]
      _ = ∫⁻ ω, rhlDissPowTrace p r ε (μ u ω) ∂P + ∫⁻ ω, F ω ^ (r - 1) * Er ω ∂P :=
          lintegral_add_left' ((hFm.pow_const (r - 1)).mul hDm) _
      _ ≤ _ := add_le_add le_rfl hHol
  -- `ε ↓ 0`
  have hTu : T' - u₀ = t := by rw [hT']; ring
  have hexp : Real.exp (-(κ * (T' - u₀))) =
      Real.exp (-(transportD0 b E * r * p * (1 - r * p) * t / 2)) := by
    rw [hTu, hκ, rhlDecayRate]; ring_nf
  rw [hexp] at hgron
  have hT0 : t₀ ≤ T' := by linarith
  have hHm := fun n => ns_aemeasurable_regTrace (hmeas T' hT0) (hμ T' hT0) hp.le (ns_eps_pos n)
  have hlimL : ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s + t) ω) ^ r ∂P ≤
      liminf (fun n => ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ T' ω) ∂P) atTop := by
    have hmono := ENNReal.monotone_rpow_of_nonneg hr0.le
    calc ∫⁻ ω, limitFracTrace p (μ (t₁ + R + s + t) ω) ^ r ∂P
        ≤ ∫⁻ ω, liminf (fun n => nsRegTrace p (nsEps n) (μ T' ω) ^ r) atTop ∂P := by
          refine lintegral_mono fun ω => ?_
          calc limitFracTrace p (μ T' ω) ^ r
              ≤ (liminf (fun n => nsRegTrace p (nsEps n) (μ T' ω)) atTop) ^ r :=
                hmono (ns_limitFracTrace_le_liminf_regTrace hp hp1 _)
            _ = liminf (fun n => nsRegTrace p (nsEps n) (μ T' ω) ^ r) atTop :=
                hmono.map_liminf_of_continuousAt _ ENNReal.continuous_rpow_const.continuousAt
      _ ≤ liminf (fun n => ∫⁻ ω, nsRegTrace p (nsEps n) (μ T' ω) ^ r ∂P) atTop :=
          lintegral_liminf_le' fun n => (hHm n).pow_const r
      _ ≤ _ := liminf_le_liminf (Eventually.of_forall fun n =>
          lintegral_mono fun ω => ENNReal.rpow_le_rpow le_self_add hr0.le)
  have hctend : Tendsto c atTop (𝓝 0) := by
    have hN0 : Tendsto N atTop (𝓝 0) := by
      have h1 := (ENNReal.Tendsto.mul_const (rhn_tendsto_regError_rpow hp₀p hr0)
        (Or.inr ENNReal.ofReal_ne_top) (b := ENNReal.ofReal C₀)).add
        (rhl_tendsto_ofReal_eps_rpow hp hr0)
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr h2top) (a := 2 ^ (r - 1))
      rw [zero_mul, add_zero, mul_zero] at h2
      exact h2
    have h3 := hN0.ennrpow_const (1 / r)
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at h3
    have h4 := ENNReal.Tendsto.const_mul h3
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hr1r hMtop)) (a := M ^ ((r - 1) / r))
    rw [mul_zero] at h4
    exact h4
  refine hlimL.trans (rhl_le_of_weighted_one hr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin)
    fun τ hτ hτ1 => ?_)
  set a := ENNReal.ofReal ((1 - τ) ^ (1 - r))
  set a' := ENNReal.ofReal (τ ^ (1 - r))
  have hup : ∀ n, ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ T' ω) ∂P ≤
      e * (a * Hs + a' * ENNReal.ofReal (nsEps n ^ p) ^ r) + c n := by
    intro n
    refine (hgron n).trans (add_le_add (mul_le_mul_right ?_ _) le_rfl)
    calc ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ u₀ ω) ∂P
        ≤ ∫⁻ ω, (a * limitFracTrace p (μ u₀ ω) ^ r + a' * ENNReal.ofReal (nsEps n ^ p) ^ r) ∂P :=
          lintegral_mono fun ω => (hYp n ω).trans (rhl_add_rpow_le _ _ hr hτ hτ1)
      _ = a * Hs + a' * ENNReal.ofReal (nsEps n ^ p) ^ r := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const, measure_univ, mul_one]
  have hlim : Tendsto (fun n => e * (a * Hs + a' * ENNReal.ofReal (nsEps n ^ p) ^ r) + c n)
      atTop (𝓝 (e * (a * Hs))) := by
    have h1 := ENNReal.Tendsto.const_mul (rhl_tendsto_ofReal_eps_rpow hp hr0)
      (Or.inr ENNReal.ofReal_ne_top) (a := a')
    have h2 := ENNReal.Tendsto.const_mul ((tendsto_const_nhds (x := a * Hs)).add h1)
      (Or.inr ENNReal.ofReal_ne_top) (a := e)
    simpa using h2.add hctend
  calc liminf (fun n => ∫⁻ ω, rhlPowTrace p r (nsEps n) (μ T' ω) ∂P) atTop
      ≤ liminf (fun n => e * (a * Hs + a' * ENNReal.ofReal (nsEps n ^ p) ^ r) + c n) atTop :=
        liminf_le_liminf (Eventually.of_forall hup)
    _ = e * (a * Hs) := hlim.liminf_eq
    _ = a * (e * Hs) := mul_left_comm _ _ _

end BlockBand.Endpoints
