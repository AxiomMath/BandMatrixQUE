module

public import BlockBand.Native.ErdosRiabov.ShortRingLocalLaw
public import BlockBand.Native.PSSS.Consequences

/-!
# Critical density and stationarity from the short-ring local law

The critical density theorem and the stationarity proposition, with the Erdős–Riabov input
replaced by the short-ring local law.

The constructors `Density.meanResolventBound_holds`, `Native.PSSS.criticalDensity_native`
and `Native.PSSS.criticalStationarity_native` take `ErdosRiabov.SourceContract` as a hypothesis.
The Erdős–Riabov source enters them only through
`Adapters.ErdosRiabov.shortRingLocalLaw_holds`, i.e. through `Inputs.ShortRingLocalLaw`.
This file restates them with `Inputs.ShortRingLocalLaw` as the hypothesis, then discharges it
with the native `BlockBand.Native.ErdosRiabov.shortRingLocalLaw_holds`.

* `criticalDensity_of_shortRingLocalLaw`, `criticalUnitIntensity_of_shortRingLocalLaw`,
  `criticalMeanSpatialIntensity_of_shortRingLocalLaw` and
  `criticalStationarity_of_shortRingLocalLaw`: the matching variants of the
  `Native.PSSS.*_native` constructors, with the PSSS source discharged by
  `Native.PSSS.sourceContract_holds_zero`.
* `meanResolventBound_native`, `criticalDensity_native_er`, `criticalUnitIntensity_native_er`,
  `criticalMeanSpatialIntensity_native_er` and `criticalStationarity_native_er`: the same
  results with no hypotheses, via the native `shortRingLocalLaw_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory BlockBand.External
open Internal.Contracts.Inputs

/-- **`MeanResolventBound`** from `Inputs.ShortRingLocalLaw`.
This is the proof of
`meanResolventBound_holds` with the input `ErdosRiabov.SourceContract`
replaced by the contract it was used through.
Parameters:
`ζ₀ = 1/128`, `δ₀ = 1/256`, `C₀ = 3`,
`D = 384`, `ε = 1/64`, `D₁ = 4`.
Constants:
`C = 4T·2^{384} + 5`, `W₀ = max(N₀, 2^{32})`.
-/
theorem meanResolventBound_of_shortRingLocalLaw
    (hL : Internal.Contracts.Inputs.ShortRingLocalLaw) : MeanResolventBound := by
  intro b κ T hb hb' hκ hT
  obtain ⟨N₀, hN₀⟩ := hL b (1 / 128) (1 / 256) κ 3 hb hb' (by norm_num) (by norm_num) hκ
    (by norm_num) 384 (by norm_num) (1 / 64) 4 (by norm_num) (by norm_num)
  refine ⟨4 * T * 2 ^ 384 + 5, max (N₀ : ℝ) (2 ^ 32), by positivity, ?_⟩
  intro p hpb hceil hnT hW₀ model e he x
  have hw : (2 : ℝ) ^ 32 ≤ (p.W : ℝ) := (le_max_right _ _).trans hW₀
  have hwN₀ : (N₀ : ℝ) ≤ (p.W : ℝ) := (le_max_left _ _).trans hW₀
  have hw1 := one_le_of_two_pow_le hw
  have hw0 : (0 : ℝ) < p.W := lt_of_lt_of_le zero_lt_one hw1
  have hm16 := sixteen_le_ceil hw
  set m := ⌈(p.W : ℝ) ^ ((15 : ℝ) / 16)⌉₊ with hmdef
  have hm4 : 4 ≤ m := by omega
  have hmn : m < p.n := by omega
  set q := shortParameters p m hm4 with hqdef
  have hqN : ((q.N : ℕ) : ℝ) = (m : ℝ) * (p.W : ℝ) := by
    change ((m * p.W : ℕ) : ℝ) = _
    push_cast; rfl
  have hqW : (q.W : ℝ) = (p.W : ℝ) := rfl
  have hqn : q.n = m := rfl
  have hN1 : (q.W : ℝ) ^ ((31 : ℝ) / 16) ≤ q.N := by rw [hqN, hqW]; exact rpow_le_shortN hw
  have hN2 : (q.N : ℝ) ≤ (q.W : ℝ) ^ ((63 : ℝ) / 32) := by rw [hqN, hqW]; exact shortN_le_rpow hw
  have hNK1 : (p.W : ℝ) ≤ q.N := by
    rw [hqN]
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    nlinarith
  set η := resolventScale p.W with hηdef
  have hη : 0 < η := Real.rpow_pos_of_pos hw0 _
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw1 (by norm_num)
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I with hz
  set model' := q.constructGaussianRingModel
  set K := coupledShortModel hmn model model'
  -- the local law on the coupled short ring
  have hNq : N₀ ≤ q.N := by exact_mod_cast hwN₀.trans hNK1
  have hζ : (q.N : ℝ) ^ ((1 : ℝ) + 1 / 128) ≤ (q.W : ℝ) ^ 2 :=
    shortN_rpow_le_sq hw (Nat.cast_nonneg _) hN2
  have hδ₀ : (q.N : ℝ) ^ ((-1 : ℝ) + 1 / 256) ≤ η := shortN_rpow_le_eta hw hN1
  have hC₀ : ‖(e : ℂ) + (η : ℂ) * Complex.I‖ ≤ 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hη]
    linarith [abs_nonneg e]
  have hLL := hN₀ q hpb hNq hζ K e η he hδ₀ hC₀
  -- the retained site
  set x' : q.Site := (((m / 2 : ℕ) : ZMod q.n), x.2) with hx'def
  have hx'v : x'.1.val = q.n / 2 := by
    change (((m / 2 : ℕ) : ZMod q.n)).val = m / 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show m / 2 < q.n by rw [hqn]; omega)]
  have hιx' : segmentEmbedding p hm4 x' = (((m / 2 : ℕ) : ZMod p.n), x.2) := by
    apply Prod.ext
    · change ((x'.1.val : ℕ) : ZMod p.n) = _
      rw [hx'v]
      rfl
    · rfl
  -- rotation
  have hrot := integral_resolvent_diag_block p model z x ((m / 2 : ℕ) : ZMod p.n)
  change ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ x x ∂(model.law : Measure p.SiteMatrix)) -
    ErdosRiabov.semicircleM z‖ ≤ _
  rw [hrot, ← hιx']
  -- the end-block events
  set δ : ℝ := 2 ^ 384 / (p.W : ℝ) ^ 11
  set β : ℝ := (q.N : ℝ) ^ (-(4 : ℝ))
  have hβ0 : 0 ≤ β := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbad : ∀ u ∈ endBlocks p m hm4,
      (Measure.map coupledShortMatrix (coupledLaw model model'))
        {G | δ < ‖(G - z • (1 : q.SiteMatrix))⁻¹ x' u‖} ≤ ENNReal.ofReal β := by
    intro u hu
    have hu' : u.1.val = 0 ∨ u.1.val = q.n - 1 := (Finset.mem_filter.mp hu).2
    have hne : x' ≠ u := by
      intro h
      have := congrArg (fun s : q.Site => s.1.val) h
      rw [hx'v] at this
      omega
    have hd : (q.N : ℝ) ≤ 4 * siteDistance q x' u := by
      exact_mod_cast four_mul_siteDistance_ge q (by rw [hqn]; exact hm16) x' u hx'v hu'
    have hfar := sqrt_siteControl_far_le q hw hN1 x' u hd
    have hthr : (q.N : ℝ) ^ ((1 : ℝ) / 64) *
        Real.sqrt (siteControl q 384 η x' u) ≤ δ := by
      have heps := shortN_rpow_eps_le hw (Nat.cast_nonneg _) hN2
      have hw32 : (q.W : ℝ) ^ ((1 : ℝ) / 32) ≤ q.W := by
        conv_rhs => rw [← Real.rpow_one (q.W : ℝ)]
        exact rpow_mono_exp hw1 (by norm_num)
      calc (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' u)
          ≤ (q.W : ℝ) * (2 ^ 384 / (q.W : ℝ) ^ 12) :=
            mul_le_mul (heps.trans hw32) hfar (Real.sqrt_nonneg _) (by positivity)
        _ = δ := by
            change (p.W : ℝ) * (2 ^ 384 / (p.W : ℝ) ^ 12) = 2 ^ 384 / (p.W : ℝ) ^ 11
            field_simp
    refine le_trans (measure_mono ?_) (hLL x' u)
    intro G hG
    change δ < ‖(G - z • (1 : q.SiteMatrix))⁻¹ x' u‖ at hG
    change (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' u) <
      ‖(G - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x' u -
        (if x' = u then ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I) else 0)‖
    simp only [hne, ite_false, sub_zero]
    exact lt_of_le_of_lt hthr hG
  have hA := norm_integral_resolvent_sub_le hmn model model' e hη x'
    (by positivity : (0 : ℝ) ≤ δ) hβ0 hbad
  -- the diagonal event
  set t : ℝ := (q.N : ℝ) ^ ((1 : ℝ) / 64) * Real.sqrt (siteControl q 384 η x' x')
  have ht0 : 0 ≤ t := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)
  have hc : ‖ErdosRiabov.semicircleM z‖ ≤ 1 :=
    (ErdosRiabov.norm_semicircleM_lt_one (by simp [hz, hη.ne'])).le
  have hbadD : (K.law : Measure q.SiteMatrix)
      {G | t < ‖(G - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x' x' -
        ErdosRiabov.semicircleM z‖} ≤ ENNReal.ofReal β := by
    have := hLL x' x'
    simp only [ite_true] at this
    exact this
  have hD := norm_integral_resolvent_diag_sub_le q K e hη x' (ErdosRiabov.semicircleM z) hc ht0
    hβ0 hbadD
  have hKlaw : (K.law : Measure q.SiteMatrix) =
      Measure.map coupledShortMatrix (coupledLaw model model') := rfl
  rw [hKlaw] at hD
  -- arithmetic
  have hηi : η⁻¹ ≤ (p.W : ℝ) ^ 2 := by
    rw [hηdef, resolventScale, show -(7 : ℝ) / 4 = -((7 : ℝ) / 4) by ring,
      Real.rpow_neg hw0.le, inv_inv, ← Real.rpow_natCast]
    exact rpow_mono_exp hw1 (by norm_num)
  have hNKw : (q.N : ℝ) ≤ (p.W : ℝ) ^ 2 := by
    refine hN2.trans ?_
    rw [hqW, ← Real.rpow_natCast]
    exact rpow_mono_exp hw1 (by norm_num)
  have hpN : (p.N : ℝ) ≤ T * (p.W : ℝ) ^ 2 := by
    have : (p.N : ℝ) = (p.n : ℝ) * p.W := by
      change ((p.n * p.W : ℕ) : ℝ) = _
      push_cast; ring
    rw [this]
    nlinarith
  have hNK0 : (0 : ℝ) < q.N := lt_of_lt_of_le hw0 hNK1
  have hβe : β = ((q.N : ℝ) ^ 4)⁻¹ := by
    change (q.N : ℝ) ^ (-(4 : ℝ)) = _
    rw [Real.rpow_neg hNK0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hNβ : (q.N : ℝ) * β ≤ ((p.W : ℝ) ^ 3)⁻¹ := by
    rw [hβe]
    have e1 : (q.N : ℝ) * ((q.N : ℝ) ^ 4)⁻¹ = ((q.N : ℝ) ^ 3)⁻¹ := by
      field_simp
    rw [e1]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hw0.le hNK1 3)
  have hβw : β ≤ ((p.W : ℝ) ^ 4)⁻¹ := by
    rw [hβe]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hw0.le hNK1 4)
  have ht : t ≤ (p.W : ℝ) ^ (-(1 : ℝ) / 32) := diag_threshold_le q hw hN1 hN2 384 x'
  have hfin := final_bound hw1 hT.le (by positivity : (0 : ℝ) ≤ 2 ^ 384)
    hηi rfl (Nat.cast_nonneg _) hNKw
    (Nat.cast_nonneg _) hpN hβ0 hNβ hβw ht
  calc ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (segmentEmbedding p hm4 x')
          (segmentEmbedding p hm4 x') ∂(model.law : Measure p.SiteMatrix)) -
        ErdosRiabov.semicircleM z‖
      ≤ ‖(∫ H, (H - z • (1 : p.SiteMatrix))⁻¹ (segmentEmbedding p hm4 x')
          (segmentEmbedding p hm4 x') ∂(model.law : Measure p.SiteMatrix)) -
          ∫ G, (G - z • (1 : q.SiteMatrix))⁻¹ x' x'
            ∂(Measure.map coupledShortMatrix (coupledLaw model model'))‖ +
        ‖(∫ G, (G - z • (1 : q.SiteMatrix))⁻¹ x' x'
            ∂(Measure.map coupledShortMatrix (coupledLaw model model'))) -
          ErdosRiabov.semicircleM z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (4 * T * 2 ^ 384 + 5) * (p.W : ℝ) ^ (-(1 : ℝ) / 32) := by
        refine le_trans (add_le_add hA hD) ?_
        exact hfin

end BlockBand.Density

namespace BlockBand.Native.ErdosRiabov

open BlockBand.External

/-- The critical density theorem (estimate and unit intensity) from `Inputs.ShortRingLocalLaw`. -/
theorem criticalDensity_of_shortRingLocalLaw
    (hL : Internal.Contracts.Inputs.ShortRingLocalLaw) :
    Internal.Contracts.Inputs.CriticalDensity :=
  BlockBand.Density.criticalDensity_of_meanResolventBound
    BlockBand.Native.PSSS.sourceContract_holds_zero
    (BlockBand.Density.meanResolventBound_of_shortRingLocalLaw hL)

/-- The critical density theorem, unit-intensity clause, from `Inputs.ShortRingLocalLaw`. -/
theorem criticalUnitIntensity_of_shortRingLocalLaw
    (hL : Internal.Contracts.Inputs.ShortRingLocalLaw) :
    Internal.Contracts.Inputs.CriticalUnitIntensity :=
  (criticalDensity_of_shortRingLocalLaw hL).2

/-- The stationarity proposition, mean-intensity clause, from `Inputs.ShortRingLocalLaw`. -/
theorem criticalMeanSpatialIntensity_of_shortRingLocalLaw
    (hL : Internal.Contracts.Inputs.ShortRingLocalLaw) :
    Internal.Contracts.Inputs.CriticalMeanSpatialIntensity :=
  BlockBand.Stationarity.criticalMeanSpatialIntensity_of_unitIntensity
    BlockBand.Native.PSSS.sourceContract_holds_zero
    (criticalUnitIntensity_of_shortRingLocalLaw hL)

/-- The stationarity proposition, all three clauses, from `Inputs.ShortRingLocalLaw`. -/
theorem criticalStationarity_of_shortRingLocalLaw
    (hL : Internal.Contracts.Inputs.ShortRingLocalLaw) :
    Internal.Contracts.Inputs.CriticalStationarity :=
  BlockBand.Stationarity.criticalStationarity_of_unitIntensity
    BlockBand.Native.PSSS.sourceContract_holds_zero
    (criticalUnitIntensity_of_shortRingLocalLaw hL)

/-- `MeanResolventBound`, with no hypotheses (short-ring local law). -/
theorem meanResolventBound_native : BlockBand.Density.MeanResolventBound :=
  BlockBand.Density.meanResolventBound_of_shortRingLocalLaw shortRingLocalLaw_holds

/-- The critical density theorem (estimate and unit intensity), with no hypotheses. -/
theorem criticalDensity_native_er : Internal.Contracts.Inputs.CriticalDensity :=
  criticalDensity_of_shortRingLocalLaw shortRingLocalLaw_holds

/-- The critical density theorem, unit-intensity clause, with no hypotheses. -/
theorem criticalUnitIntensity_native_er : Internal.Contracts.Inputs.CriticalUnitIntensity :=
  criticalUnitIntensity_of_shortRingLocalLaw shortRingLocalLaw_holds

/-- The stationarity proposition, mean-intensity clause, with no hypotheses. -/
theorem criticalMeanSpatialIntensity_native_er :
    Internal.Contracts.Inputs.CriticalMeanSpatialIntensity :=
  criticalMeanSpatialIntensity_of_shortRingLocalLaw shortRingLocalLaw_holds

/-- The stationarity proposition, all three clauses, with no hypotheses. -/
theorem criticalStationarity_native_er : Internal.Contracts.Inputs.CriticalStationarity :=
  criticalStationarity_of_shortRingLocalLaw shortRingLocalLaw_holds

end BlockBand.Native.ErdosRiabov
