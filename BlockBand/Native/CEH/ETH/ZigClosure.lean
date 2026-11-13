module

public import BlockBand.Native.CEH.ETH.ZigClosureNum
public import BlockBand.Native.CEH.ETH.LawThetaOne

/-!
# CEH ETH: the zig bound for the positive imaginary chain (`ZigImChainBound`)

**Main result.** `zigImChainBound_holds : ZigImChainBound` (no hypotheses).

**Proof.** Fix the parameters of `ZigImChainBound` and `ε_ρ = ε₀/2`, `ξ = min(ε_ρ, ε)/20`,
`ζ = ξ/2`, `K₀ = 2/(sLo c)`, `C₅₆ = zgl_C56 sLo c`, `C_N2 = zgl_CN2 sLo sHi c`,
`κ_ρ = c/(2π)`, `C_g = K₀ sHi`. `N₀` collects: the height cutoff `N^{ε₁-1} ≤
quantitativeIFTHeight sLo c` (`zgl_eventually_rpow_le`), the density bound `N^{ε₀/2} ≤ N η ρ`
(`zgl_eventually_density`), the two-point tube at `(ε₀/2, ζ, D + 1)` (`zgl_flowTube_two`) and the
eventual numeric facts (`zcl_eventually_log_lt`): with `u = N^{ξ/4}` and
`Λ = 1 + 2 log(1 + C_g) + 2 log N`, `16Λ < u`, `2C₅₆Λ < κ_ρ √N`, `π² + 8 sHi C₅₆² π² + 7 < u`,
`C_N2 < u`, `2 log(68(5 + 2C_g)) + 2(1 + D) log N < N^{ξ/2}`, and `N ≥ 2`.

For `N ≥ N₀` and the data of `ZigImChainBound` (Brownian space `(Ω, Q, 𝓖, G)` arbitrary), let
`A° = cehETHRegularizedObservable s Mf z₁ z₂ J`. If `A° = 0` the bad event is empty
(`zgl_measure_bad_eq_zero_of_eq_zero`). Otherwise build `d : zcl_Data` (`s` as
`Real.toNNReal s`, `Mᵢ = Mf zᵢ`) with `d.Valid` (window point `zgl_window_point`, MDE,
`zgl_sTwoAt_pos`), take `p = zpc_parRpow N ξ ζ L_max C₅₆ L_g` with `L_max = 2 log(1 + C_g N)`,
`L_g = 2⌈1 + C_g N⌉`, and split `Ω` into
* the tube failure set (measure `≤ N^{-(D+1)}`, `zgl_flowTube_two`),
* the tail failure set `¬ TailGood` (measure `≤ 17(L_g + 1) · 2 e^{-N^{ξ/2}/2} ≤ N^{-D}/2`,
  `ztl_goodEvent_levels`, `zcl_tail_small`),
* their complement, on which `zcl_Data.endpoint_le` (the path core `zpc_closure_rpow` with all
  fields of `zpc_Hyp`, `zcl_Data.hyp`) gives `‖⟨Im G₁ A° Im G₂ A°*⟩‖ = Z_s ≤ N^{ξ/2} ρ₁ρ₂ s₂(s)²
  ≤ N^{ξ/2} C_N2 < N^ε` (`zgl_norm_cehPositiveChain_eq`, `zgl_N2_window_uniform`), so the bad
  event does not occur.
The numeric hypotheses of `zpc_closure_rpow` are `zcl_numY`, `zcl_numX`, `zcl_numZ`, `zcl_grid`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Filter MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open CEHNative.BlockBand.CEH (quantitativeIFTHeight)
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace sourceDensity)
open scoped NNReal ENNReal ComplexConjugate Matrix.Norms.L2Operator

/-- `x^c = (x^{ξ/4})^k` when `c = k ξ/4`. -/
theorem zcl_rpow_u {x ξ c : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : c = (k : ℝ) * (ξ / 4)) :
    x ^ c = (x ^ (ξ / 4)) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, hk, mul_comm]

/-- **The zig bound for the positive imaginary chain on `θ = 1` pairs, on an arbitrary Hermitian
Brownian space** (CEH Theorem 4.2, (4.4), for `⟨Im G₁ A° Im G₂ A°*⟩`). No hypotheses. -/
theorem zigImChainBound_holds : ZigImChainBound := by
  intro _κ _C _hκ _hC sLo sHi hsLo hsHi r c _K _hr hc _hK ε₀ ε₁ h0 _h01 h1 ε D hε hD
  -- exponents and constants
  set ξ : ℝ := min (ε₀ / 2) ε / 20 with hξdef
  have hξ : 0 < ξ := by
    have : 0 < min (ε₀ / 2) ε := lt_min (by linarith) hε
    positivity
  have hξ₀ : 20 * ξ ≤ ε₀ / 2 := by
    have := min_le_left (ε₀ / 2) ε
    rw [hξdef]; linarith
  have hξε : 20 * ξ ≤ ε := by
    have := min_le_right (ε₀ / 2) ε
    rw [hξdef]; linarith
  set ζ : ℝ := ξ / 2 with hζdef
  have hζ : 0 < ζ := by positivity
  set K₀ : ℝ := zgl_K₀ sLo c with hK₀def
  have hK₀ : 0 ≤ K₀ := by rw [hK₀def]; unfold zgl_K₀; positivity
  set Cm : ℝ := zgl_C56 sLo c with hCmdef
  have hCm : 0 ≤ Cm := by
    rw [hCmdef]; unfold zgl_C56 lemma56Const zgl_K₀
    have : 0 < c / 2 := by positivity
    positivity
  set CN2 : ℝ := zgl_CN2 sLo sHi c with hCN2def
  set κρ : ℝ := c / (2 * Real.pi) with hκρdef
  have hκρ : 0 < κρ := by have := Real.pi_pos; positivity
  have hsHi0 : 0 < sHi := hsLo.trans_le hsHi
  set Cg : ℝ := K₀ * sHi with hCgdef
  have hCg : 0 ≤ Cg := mul_nonneg hK₀ hsHi0.le
  set A₀ : ℝ := 1 + 2 * Real.log (1 + Cg) with hA₀def
  set CZ : ℝ := Real.pi ^ 2 + 8 * sHi * Cm ^ 2 * Real.pi ^ 2 + 7 with hCZdef
  -- the cutoff `N₀`
  obtain ⟨Na, hNa⟩ := zgl_eventually_rpow_le h1 (zgl_quantitativeIFTHeight_pos hsLo hc)
  obtain ⟨Nb, hNb⟩ := zgl_eventually_density h0 hκρ
  obtain ⟨Nc, hNc⟩ := zgl_flowTube_two (ε₀ / 2) ζ (D + 1) (by positivity) hζ (by positivity)
  have ev : ∀ᶠ N : ℕ in atTop, (2 ≤ N ∧ Na ≤ N ∧ Nb ≤ N ∧ Nc ≤ N) ∧
      16 * A₀ + 32 * Real.log N < 1 * (N : ℝ) ^ (ξ / 4) ∧
      2 * Cm * A₀ + 4 * Cm * Real.log N < κρ * (N : ℝ) ^ (1 / 2 : ℝ) ∧
      CZ + 0 * Real.log N < 1 * (N : ℝ) ^ (ξ / 4) ∧
      CN2 + 0 * Real.log N < 1 * (N : ℝ) ^ (ξ / 4) ∧
      2 * Real.log (68 * (5 + 2 * Cg)) + 2 * (1 + D) * Real.log N <
        1 * (N : ℝ) ^ (ξ / 2) := by
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop Na, eventually_ge_atTop Nb,
      eventually_ge_atTop Nc,
      zcl_eventually_log_lt (r := ξ / 4) (by positivity) one_pos (16 * A₀) 32,
      zcl_eventually_log_lt (r := 1 / 2) (by norm_num) hκρ (2 * Cm * A₀) (4 * Cm),
      zcl_eventually_log_lt (r := ξ / 4) (by positivity) one_pos CZ 0,
      zcl_eventually_log_lt (r := ξ / 4) (by positivity) one_pos CN2 0,
      zcl_eventually_log_lt (r := ξ / 2) (by positivity) one_pos
        (2 * Real.log (68 * (5 + 2 * Cg))) (2 * (1 + D))] with N e1 e2 e3 e4 e5 e6 e7 e8 e9
    exact ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ev
  refine ⟨N₀, ?_⟩
  intro N hN s hs1 hs2 F _hFd Mf hMf E₀ hreg z₁ z₂ hz₁r hz₂r hz₁l hz₁u hz₂l hz₂u hθ J _hJh
    hJ Ω _ Q _ 𝓖 G hG
  obtain ⟨⟨hN2, hNa', hNb', hNc'⟩, hA2, hA3, hA4, hA5, hA6⟩ := hN₀ N hN
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set A := cehETHRegularizedObservable s Mf z₁ z₂ J with hAdef
  by_cases hA : A = 0
  · rw [zgl_measure_bad_eq_zero_of_eq_zero Q hN0 ε (fun ω => F.1 + G (Real.toNNReal s) ω) z₁ z₂
      hA]
    exact zero_le
  -- the window data
  have hs0 : 0 < s := hsLo.trans_le hs1
  set st : ℝ≥0 := Real.toNNReal s with hstdef
  have hst : (st : ℝ) = s := Real.coe_toNNReal _ hs0.le
  have hz₁ : 0 < z₁.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr _) hz₁l
  have hz₂ : 0 < z₂.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hNr _) hz₂l
  have hz₁H : z₁.im ≤ quantitativeIFTHeight sLo c := hz₁u.trans (hNa N hNa')
  have hz₂H : z₂.im ≤ quantitativeIFTHeight sLo c := hz₂u.trans (hNa N hNa')
  obtain ⟨p₁, -, -, k₁, ρ₁c, ρ₁s⟩ := zgl_window_point hN0 F.2 hsLo hs1 hMf hc hreg hz₁r hz₁ hz₁H
  obtain ⟨p₂, -, -, k₂, ρ₂c, ρ₂s⟩ := zgl_window_point hN0 F.2 hsLo hs1 hMf hc hreg hz₂r hz₂ hz₂H
  have hm₁ := hMf z₁ hz₁.ne'
  have hm₂ := hMf z₂ hz₂.ne'
  have hM₁ : IsManuscriptMDE (st : ℝ) ⟨F.1, F.2⟩ z₁ (Mf z₁) := by
    rw [hst]; exact ⟨hm₁.inv, hm₁.pos⟩
  have hM₂ : IsManuscriptMDE (st : ℝ) ⟨F.1, F.2⟩ z₂ (Mf z₂) := by
    rw [hst]; exact ⟨hm₂.inv, hm₂.pos⟩
  have ht₁ : 0 < (NTrace (Mf z₁)).im := by linarith
  have ht₂ : 0 < (NTrace (Mf z₂)).im := by linarith
  -- the data of the zig
  set d : zcl_Data Ω N := ⟨F.1, G, st, z₁, z₂, Mf z₁, Mf z₂, A⟩ with hddef
  have hd : d.Valid :=
    { N_pos := hN0
      F_herm := F.2
      G_herm := hG.hermitian
      G_zero := hG.zero
      G_cont := hG.continuous
      mde₁ := hM₁
      mde₂ := hM₂
      z₁_pos := hz₁
      z₂_pos := hz₂
      m₁_pos := ht₁
      m₂_pos := ht₂
      S_pos := by
        show 0 < sTwoAt (st : ℝ) (Mf z₁) (Mf z₂) A
        rw [hst]
        exact zgl_sTwoAt_pos hN0 F.2 hs0.le hz₁ hz₂ hm₁ hm₂ ht₁ ht₂ hA hs0.le
      base_nonneg := (zgl_sTwoBase_pos hN0 F.2 hs0.le hz₁ hz₂ hm₁ hm₂ ht₁ ht₂ hA).le }
  -- the parameters
  set Lmax : ℝ := 2 * Real.log (1 + Cg * N) with hLmaxdef
  set Lg : ℕ := 2 * ⌈1 + Cg * N⌉₊ with hLgdef
  set p : zpc_Par := zpc_parRpow (N : ℝ) ξ ζ Lmax Cm Lg with hpdef
  set u : ℝ := (N : ℝ) ^ (ξ / 4) with hudef
  have hu1 : 1 ≤ u := Real.one_le_rpow hN1 (by positivity)
  have e8 : (N : ℝ) ^ (2 * ξ) = u ^ 8 := zcl_rpow_u hNr.le 8 (by push_cast; ring)
  have e4 : (N : ℝ) ^ ξ = u ^ 4 := zcl_rpow_u hNr.le 4 (by push_cast; ring)
  have e2 : (N : ℝ) ^ (ξ / 2) = u ^ 2 := zcl_rpow_u hNr.le 2 (by push_cast; ring)
  have eζ : (N : ℝ) ^ ζ = u ^ 2 := e2
  have e80 : (N : ℝ) ^ (20 * ξ) = u ^ 80 := zcl_rpow_u hNr.le 80 (by push_cast; ring)
  have hne80 : u ^ 80 ≤ (N : ℝ) ^ (ε₀ / 2) := by
    rw [← e80]; exact Real.rpow_le_rpow_of_exponent_le hN1 hξ₀
  have hε80 : u ^ 80 ≤ (N : ℝ) ^ ε := by
    rw [← e80]; exact Real.rpow_le_rpow_of_exponent_le hN1 hξε
  -- the logarithmic loss
  have hB1 : 1 ≤ 1 + Cg * N := by have := mul_nonneg hCg hNr.le; linarith
  have hL0 : 0 ≤ Lmax := by
    rw [hLmaxdef]; have := Real.log_nonneg hB1; linarith
  set Λ : ℝ := A₀ + 2 * Real.log N with hΛdef
  have hlogB : Real.log (1 + Cg * N) ≤ Real.log (1 + Cg) + Real.log N := by
    rw [← Real.log_mul (by linarith) hNr.ne']
    exact Real.log_le_log (by linarith) (by linarith [mul_le_mul_of_nonneg_left hN1 hCg])
  have hΛ1 : 1 + Lmax ≤ Λ := by rw [hΛdef, hA₀def, hLmaxdef]; linarith
  have hΛ2 : 1 + Lmax / 2 ≤ Λ := by linarith
  have hΛu : 16 * Λ < u := by rw [hΛdef]; linarith
  have hA3' : 2 * Cm * Λ < κρ * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, hΛdef]; linarith
  have hCZ : CZ ≤ u := by linarith
  have hCN : CN2 < u := by linarith
  -- the numeric hypotheses of the path core
  have hgeomN : d.geom.N = (N : ℝ) := rfl
  have hρρ : κρ ^ 2 ≤ cehDensityOf (Mf z₁) * cehDensityOf (Mf z₂) := by
    rw [sq]; exact mul_le_mul ρ₁c ρ₂c hκρ.le (hκρ.le.trans ρ₁c)
  have hY : (1 + Lmax) * (4 * Real.sqrt 3 * (N : ℝ) ^ (ξ / 4) +
      ((N : ℝ) ^ (2 * ξ)) ^ 2 / (3 * (Real.pi * (N : ℝ) ^ (ε₀ / 2))) + 3 * (N : ℝ) ^ ζ) <
        (N : ℝ) ^ (2 * ξ) := by
    rw [e8, eζ]; exact zcl_numY hu1 hne80 hL0 hΛ1 hΛu
  have hX : (1 + Lmax / 2) * (2 * (N : ℝ) ^ (ξ / 4) *
      Real.sqrt (4 * (N : ℝ) ^ ξ / (Real.pi * (N : ℝ) ^ (ε₀ / 2))) +
      Cm * (N : ℝ) ^ (2 * ξ) / Real.sqrt ((N : ℝ) * (cehDensityOf (Mf z₁) *
        cehDensityOf (Mf z₂))) +
      (N : ℝ) ^ (2 * ξ) * (N : ℝ) ^ (2 * ξ) / (2 * (Real.pi * (N : ℝ) ^ (ε₀ / 2))) +
      2 * (N : ℝ) ^ ζ * Real.sqrt (3 / 2 * (N : ℝ) ^ ξ) /
        Real.sqrt (Real.pi * (N : ℝ) ^ (ε₀ / 2))) < (N : ℝ) ^ (2 * ξ) := by
    rw [e8, e4, eζ]
    exact zcl_numX hu1 hne80 hL0 hΛ2 hΛu hNr hκρ hρρ hCm hA3'
  have hsHi' : (st : ℝ) ≤ sHi := by rw [hst]; exact hs2
  have hZ : Real.pi ^ 2 + (N : ℝ) ^ (ξ / 4) * (N : ℝ) ^ ξ *
      Real.sqrt (4 / (Real.pi * (N : ℝ) ^ (ε₀ / 2))) +
      6 * (N : ℝ) ^ ζ * (N : ℝ) ^ ξ / (Real.pi * (N : ℝ) ^ (ε₀ / 2)) +
      8 * (st : ℝ) * Cm ^ 2 * Real.pi ^ 2 +
      8 * ((N : ℝ) ^ (2 * ξ)) ^ 2 / (Real.pi * (N : ℝ) ^ (ε₀ / 2)) ≤ (N : ℝ) ^ (ξ / 2) := by
    rw [e8, e4, eζ]
    exact zcl_numZ hu1 hne80 hsHi' hCZ
  have hβ : (N : ℝ) ^ (ξ / 2) < (N : ℝ) ^ ξ :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hne : 0 < (N : ℝ) ^ (ε₀ / 2) := Real.rpow_pos_of_pos hNr _
  have hη₁ : (N : ℝ) ^ (ε₀ / 2) ≤ (N : ℝ) * cehDensityOf (Mf z₁) * z₁.im := by
    have := hNb N hNb' z₁.im (cehDensityOf (Mf z₁)) hz₁l ρ₁c
    linarith [mul_right_comm (N : ℝ) z₁.im (cehDensityOf (Mf z₁))]
  have hη₂ : (N : ℝ) ^ (ε₀ / 2) ≤ (N : ℝ) * cehDensityOf (Mf z₂) * z₂.im := by
    have := hNb N hNb' z₂.im (cehDensityOf (Mf z₂)) hz₂l ρ₂c
    linarith [mul_right_comm (N : ℝ) z₂.im (cehDensityOf (Mf z₂))]
  have hNη : ∀ η : ℝ, (N : ℝ) ^ (ε₀ - 1) ≤ η → 1 ≤ (N : ℝ) * η := by
    intro η hη
    have e : (N : ℝ) * (N : ℝ) ^ (ε₀ - 1) = (N : ℝ) ^ ε₀ := by
      rw [Real.rpow_sub_one hNr.ne']; field_simp
    have : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1 h0.le
    linarith [mul_le_mul_of_nonneg_left hη hNr.le]
  have hcs₁ : (NTrace (Mf z₁)).im * (st : ℝ) ≤ Cg :=
    mul_le_mul k₁ hsHi' (st.2) hK₀
  have hcs₂ : (NTrace (Mf z₂)).im * (st : ℝ) ≤ Cg :=
    mul_le_mul k₂ hsHi' (st.2) hK₀
  have hPgrid : d.geom.P 0 ≤ (1 + Cg * N) ^ 2 * d.geom.P d.geom.s :=
    zcl_grid hz₁ hz₂ hcs₁ hcs₂ ht₁.le ht₂.le st.2 hCg (hNη _ hz₁l) (hNη _ hz₂l)
  have hPs : 0 < d.geom.P d.geom.s := hd.geom_valid.P_pos le_rfl
  have hgrid : d.geom.P 0 ≤ 2 ^ Lg * d.geom.P d.geom.s :=
    hPgrid.trans (mul_le_mul_of_nonneg_right (zcl_two_pow_ceil (by linarith)) hPs.le)
  have hlog : Real.log (d.geom.P 0 / d.geom.P d.geom.s) ≤ Lmax := by
    have hP0 : 0 < d.geom.P 0 := hd.geom_valid.P_pos d.s.2
    have hq : d.geom.P 0 / d.geom.P d.geom.s ≤ (1 + Cg * N) ^ 2 := by
      rw [div_le_iff₀ hPs]; exact hPgrid
    calc Real.log (d.geom.P 0 / d.geom.P d.geom.s) ≤ Real.log ((1 + Cg * N) ^ 2) :=
          Real.log_le_log (div_pos hP0 hPs) hq
      _ = Lmax := by rw [Real.log_pow]; push_cast; ring
  have hMA : ∀ k : Bool × Bool, ∀ t ∈ Icc 0 (d.s : ℝ), ‖d.μA k t‖ ≤
      Cm * Real.sqrt (NTrace (matrixImaginaryPart d.M₁ * d.A * matrixImaginaryPart d.M₂ *
        d.Aᴴ)).re := by
    intro k t ht
    have ht2 : t ≤ s := by rw [← hst]; exact ht.2
    obtain ⟨a1, a2, a3, a4, -⟩ := zgl_lemma56_window_uniform hN0 F.2 hsLo hs1 hMf hc hreg
      hz₁r hz₂r hz₁ hz₂ hz₁H hz₂H hθ J ht.1 ht2
    have hP0 : 0 ≤ Real.sqrt (NTrace (matrixImaginaryPart (Mf z₁) * A *
        matrixImaginaryPart (Mf z₂) * Aᴴ)).re := Real.sqrt_nonneg _
    rcases k with ⟨_ | _, _ | _⟩
    · exact a2
    · exact a4
    · show ‖NTrace (twoResApprox t (chooseAdjoint (zcl_ch true) (Mf z₁)) A
        (chooseAdjoint (zcl_ch false) (Mf z₂)))‖ ≤ _
      simp only [zcl_ch, ↓reduceIte, Bool.false_eq_true, chooseAdjoint_plain,
        chooseAdjoint_adjoint]
      rw [a3, norm_zero]; positivity
    · exact a1
  -- the tube failure set
  set S₁ : Set Ω := {ω | ∃ σ : ℝ≥0, σ ≤ st ∧
      ¬ (zgl_TubeGood N ζ F.1 G z₁ (normalizedTrace (Mf z₁)) st σ ω ∧
        zgl_TubeGood N ζ F.1 G z₂ (normalizedTrace (Mf z₂)) st σ ω ∧
        zgl_TubeGood N ζ F.1 G (conj z₁) (conj (normalizedTrace (Mf z₁))) st σ ω ∧
        zgl_TubeGood N ζ F.1 G (conj z₂) (conj (normalizedTrace (Mf z₂))) st σ ω)} with hS₁
  have hdS₁ : (N : ℝ) ^ (ε₀ / 2) ≤ N * |z₁.im| * sourceDensity (Mf z₁) := by
    rw [abs_of_pos hz₁]; exact hNb N hNb' z₁.im _ hz₁l ρ₁s
  have hdS₂ : (N : ℝ) ^ (ε₀ / 2) ≤ N * |z₂.im| * sourceDensity (Mf z₂) := by
    rw [abs_of_pos hz₂]; exact hNb N hNb' z₂.im _ hz₂l ρ₂s
  have htube : Q S₁ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
    hNc N hNc' Q 𝓖 G hG st (by rw [hst]; exact hs0) ⟨F.1, F.2⟩ z₁ z₂ (Mf z₁) (Mf z₂) hM₁
      hz₁.ne' hdS₁ hM₂ hz₂.ne' hdS₂
  -- the tail failure set
  set S₂ : Set Ω := {ω | ¬ d.TailGood p ω} with hS₂
  have hθZ : 0 < p.θZ := Real.rpow_pos_of_pos hNr _
  have hlam : 0 < p.lam := Real.rpow_pos_of_pos hNr _
  have hqX : ∀ ℓ ≤ Lg, 0 < zpc_aX d.geom p ℓ ∧ 0 < zpc_bX d.geom p ℓ ∧
      p.lam ^ 2 / 2 ≤ zpc_aX d.geom p ℓ ^ 2 / (2 * zpc_bX d.geom p ℓ) := fun ℓ _ =>
    ⟨mul_pos hlam (Real.sqrt_pos.2 (zpc_bX_pos hd.geom_valid hθZ ℓ)),
      zpc_bX_pos hd.geom_valid hθZ ℓ, (zpc_aX_sq_div hd.geom_valid hθZ ℓ).ge⟩
  have hqY : ∀ ℓ ≤ Lg, 0 < zpc_aY d.geom p ℓ ∧ 0 < zpc_bY d.geom ℓ ∧
      p.lam ^ 2 / 2 ≤ zpc_aY d.geom p ℓ ^ 2 / (2 * zpc_bY d.geom ℓ) := fun ℓ _ =>
    ⟨mul_pos hlam (Real.sqrt_pos.2 (zpc_bY_pos hd.geom_valid ℓ)),
      zpc_bY_pos hd.geom_valid ℓ, (zpc_aY_sq_div hd.geom_valid ℓ).ge⟩
  have hqZ : ∀ ℓ ≤ Lg, 0 < (fun _ : ℕ => zpc_aZ d.geom p) ℓ ∧
      0 < (fun _ : ℕ => zpc_bZ d.geom p) ℓ ∧
      p.lam ^ 2 / 2 ≤ (fun _ : ℕ => zpc_aZ d.geom p) ℓ ^ 2 /
        (2 * (fun _ : ℕ => zpc_bZ d.geom p) ℓ) := fun ℓ _ =>
    ⟨mul_pos hlam (Real.sqrt_pos.2 (zpc_bZ_pos hd.geom_valid hθZ)),
      zpc_bZ_pos hd.geom_valid hθZ, (zpc_aZ_sq_div hd.geom_valid hθZ).ge⟩
  have htail : Q S₂ ≤ ENNReal.ofReal (((17 * (Lg + 1) : ℕ) : ℝ) *
      (2 * Real.exp (-(p.lam ^ 2 / 2)))) :=
    ztl_goodEvent_levels (s := st) (A := A) (L := Lg) hG F.2 hz₁.ne' hd.hm₁ hz₂.ne' hd.hm₂
      (zpc_aX d.geom p) (zpc_bX d.geom p) (zpc_aY d.geom p) (zpc_bY d.geom)
      (fun _ => zpc_aZ d.geom p) (fun _ => zpc_bZ d.geom p) (p.lam ^ 2 / 2) hqX hqY hqZ
  have hq : p.lam ^ 2 / 2 = (N : ℝ) ^ (ξ / 2) / 2 := zpc_lam_rpow_sq _ _ _ _ _ _ hNr.le
  have htb : (((17 * (Lg + 1) : ℕ) : ℝ)) * (2 * Real.exp (-(p.lam ^ 2 / 2))) ≤
      (N : ℝ) ^ (-D) / 2 := by
    rw [hq]
    exact zcl_tail_small (show 1 ≤ N by omega) hCg (by linarith)
  have hNb2 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) / 2 := by
    have := zgl_two_mul_rpow_neg_succ_le (N := N) (D := D) hN2r
    linarith
  -- off `S₁ ∪ S₂` the chain is small
  have hsub : {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + G st ω) z₁ z₂ A‖} ⊆ S₁ ∪ S₂ := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    have hT : d.TubeGood ζ ω := fun σ hσ => by
      by_contra h
      exact hno.1 ⟨σ, hσ, fun h4 => h ⟨h4.1, h4.2.1⟩⟩
    have hM : d.TailGood p ω := by
      by_contra h
      exact hno.2 h
    have hend := zcl_Data.endpoint_le hd hne hη₁ hη₂ hCm hgrid hlog hY hX hZ hβ hMA hT hM
    have hρS : cehDensityOf (Mf z₁) * cehDensityOf (Mf z₂) *
        sTwoAt (st : ℝ) (Mf z₁) (Mf z₂) A ^ 2 ≤ CN2 := by
      rw [hst]
      exact zgl_N2_window_uniform hN0 F.2 hsLo hs1 hs2 hMf hc hreg hz₁r hz₂r hz₁ hz₂ hz₁H
        hz₂H hθ J hJ
    have heq : ‖cehPositiveChain (F.1 + G st ω) z₁ z₂ A‖ = d.Zp ω (d.s : ℝ) := by
      rw [zgl_norm_cehPositiveChain_eq (F.2.add (hG.hermitian st ω)) hz₁ hz₂
        (normalizedTrace (Mf z₁)) (normalizedTrace (Mf z₂)) A]
      show _ = (fz_chain (flowResolvent F.1 G z₁ (normalizedTrace (Mf z₁)) st
        ((st : ℝ).toNNReal) ω) (flowResolvent F.1 G z₂ (normalizedTrace (Mf z₂)) st
        ((st : ℝ).toNNReal) ω) A).re
      rw [Real.toNNReal_coe]
    rw [Set.mem_ofPred_eq, heq] at hω
    have hpos : 0 < (N : ℝ) ^ (ξ / 2) := Real.rpow_pos_of_pos hNr _
    have h1' : d.Zp ω (d.s : ℝ) ≤ (N : ℝ) ^ (ξ / 2) * CN2 :=
      hend.trans (mul_le_mul_of_nonneg_left hρS hpos.le)
    have h2' : (N : ℝ) ^ (ξ / 2) * CN2 < (N : ℝ) ^ ε := by
      rw [e2]
      have hu0 : 0 < u := by linarith
      have : u ^ 2 * CN2 < u ^ 2 * u := mul_lt_mul_of_pos_left hCN (by positivity)
      have h3 : u ^ 2 * u ≤ u ^ 80 := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hu1 (by norm_num)
      linarith
    linarith
  calc Q {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + G st ω) z₁ z₂ A‖}
      ≤ Q (S₁ ∪ S₂) := measure_mono hsub
    _ ≤ Q S₁ + Q S₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal (((17 * (Lg + 1) : ℕ) : ℝ) *
        (2 * Real.exp (-(p.lam ^ 2 / 2)))) := add_le_add htube htail
    _ = ENNReal.ofReal ((N : ℝ) ^ (-(D + 1)) + ((17 * (Lg + 1) : ℕ) : ℝ) *
        (2 * Real.exp (-(p.lam ^ 2 / 2)))) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hNr.le _) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (by linarith)

end BlockBand.Native.CEH.ETH
