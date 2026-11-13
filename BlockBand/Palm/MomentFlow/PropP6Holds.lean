module

public import BlockBand.Palm.MomentFlow.P6Canon
public import BlockBand.Palm.MomentFlow.PropLongShortArith
public import BlockBand.Palm.MomentFlow.StepsMultiColSpec

/-!
# `PropagationP6` holds, given the column finite-speed contract

**`propagationP6_holds`** proves `PropagationP6` exactly as stated: the finite-speed
inequality, integrated in time by Tonelli and Markov. Its hypotheses are the column finite-speed
statement `MultiShortColumnSpeed`, the Gaussian inputs `GaussianLpGradient` and
`MultivariateGaussianIBP` (through `bulk_near_target`), and `DysonBrownianMotion`.

Proof. Take `W = K_w w`. The short flow from `1_{rampDist k₀ ≤ W}` is `Σ_{η ∈ window} U δ_η`
(`window_decomp`). For `rampDist k₀ ζ > 2W` and `η` in the window, `occDist(η, ζ) > W ≥ rR`
(`R = N^{1/1000} ℓ`, `eventually_R_le_window`). At each deterministic time `v`, off the column
events of all `(k₀, η)` with `η` in the window of `k₀` (at most `N^{r+1}` of them,
`MultiShortColumnSpeed` with `s = a`), every term is `≤ N^r e^{-c'N^{1/1000}} ≤ N^{r-D₁}`. Here the
window is in the bulk at time `a` by `nearBulk`. The time integral goes through `excess_core`, with
`e(u) = Σ_{(k₀,ζ) far} 1_{nearBulk k₀} fwdC(1_window)(u, ζ)`, continuous in `u`.
`bulk_near_target` places every admissible centre in `nearBulk`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Transmission

/-- `r R ≤ K_w w` for large `N` (`R = N^{1/1000} ℓ`). -/
theorem eventually_R_le_window {Kw : ℝ} (hKw : 0 < Kw) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, r * ((n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n) ≤ Kw * cmW n := by
  filter_upwards [eventually_const_mul_rpow_neg_le (r : ℝ) (by norm_num : (0 : ℝ) < 1 / 1500)
      hKw, eventually_ge_atTop 1] with n h1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  calc (r : ℝ) * ((n : ℝ) ^ (1 / 1000 : ℝ) * cmEll n)
      ≤ r * ((n : ℝ) ^ (1 / 1000 : ℝ) * (n : ℝ) ^ (1 - (1 / 300 : ℝ))) := by
        gcongr; exact cmEll_le_rpow n
    _ = (r * (n : ℝ) ^ (-(1 / 1500 : ℝ))) * cmW n := by
        rw [cmW, mul_assoc, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; norm_num
    _ ≤ Kw * cmW n := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem propagationP6_holds (hCol : MultiShortColumnSpeed) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) (hDBM : ∀ N : ℕ, DysonBrownianMotion N) :
    PropagationP6 := by
  classical
  intro A c₀ r₀ s₀ v₀ hK r hr M Kw hKw D
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨c', hc', hColD⟩ := hCol A c₀ r₀ s₀ v₀ hK r hr (1 / 1000) (by norm_num)
  set Dp : ℝ := max D 1 with hDp
  set Q : ℝ := 2 * r + 1 with hQ
  set D₁ : ℝ := 2 * Dp + Q + r + 5 with hD₁
  obtain ⟨N₁, hN₁⟩ := hColD D₁
  obtain ⟨N₅, hN₅⟩ := bulk_near_target hLp hIBP (A := A) hK (κ' := 1 / 1200) (by norm_num) D₁
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((hnat.eventually_ge_atTop 4).and ((hτ0.eventually (gt_mem_nhds hK.1)).and
      ((eventually_window_le Kw r).and ((eventually_center_le M hr₀).and
      ((eventually_R_le_window hKw r).and
      ((eventually_exp_le_rpow hc' (by norm_num : (0 : ℝ) < 1 / 1000) D₁).and
      ((eventually_ge_atTop N₁).and (eventually_ge_atTop N₅))))))))
  refine ⟨N₀, fun N hN F E hC => ?_⟩
  obtain ⟨hN4, hτc, hwin, hcen, hRW, hexp, hn1, hn5⟩ := hN₀ N hN
  have hF := hC.1
  have hNr : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hτpos : 0 < cmTau N := Real.rpow_pos_of_pos hNr _
  have ha : 0 < c₀ - cmTau N := by unfold cmTau; linarith
  have hac : c₀ - cmTau N ≤ c₀ := by linarith
  obtain ⟨Bbk, hBbkm, hBbkμ, hBbk⟩ := hN₅ N hn5 F E hC
  set W : ℝ := Kw * cmW N with hWdef
  set ρ : ℝ := (N : ℝ) ^ (1 - (1 / 1200 : ℝ)) with hρdef
  set R : ℝ := (N : ℝ) ^ (1 / 1000 : ℝ) * cmEll N with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hWρ : W ≤ ρ := by
    have : 0 ≤ (r : ℝ) * R := by positivity
    have h := hwin; linarith
  have hW0 : 0 ≤ W := (mul_pos hKw (Real.rpow_pos_of_pos hNr _)).le
  set x₁ : ℝ := (N : ℝ) ^ (-D₁) with hx₁def
  have hx₁0 : 0 ≤ x₁ := (Real.rpow_pos_of_pos hNr _).le
  set datW : Fin N → FlowSample N → Occ N → ℝ := fun k₀ _ ζ =>
    if (rampDist (k₀ : ℕ) ζ : ℝ) ≤ W then 1 else 0 with hdatW
  set datD : Occ N → FlowSample N → Occ N → ℝ := fun η _ ζ => if ζ = η then 1 else 0
    with hdatD
  set winS : Fin N → Finset (Occ N) := fun k₀ =>
    (sector N r).filter fun η => (rampDist (k₀ : ℕ) η : ℝ) ≤ W with hwinS
  set far : Finset (Fin N × Occ N) := ((Finset.univ : Finset (Fin N)) ×ˢ sector N r).filter
    fun p => 2 * W < (rampDist (p.1 : ℕ) p.2 : ℝ) with hfar
  set P := windowPairs N r W with hPdef
  set Y : ℕ → ℝ → FlowSample N → ℝ := fun n v ω =>
    ∑ p ∈ far, (nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ p.1).indicator
      (fun ω => fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datW p.1) v ω p.2) ω with hYdef
  have hdatW01 : ∀ k₀ ω, ∀ ζ ∈ sector N r, 0 ≤ datW k₀ ω ζ ∧ datW k₀ ω ζ ≤ 1 := by
    intro k₀ ω ζ _; simp only [hdatW]; split_ifs <;> norm_num
  have hdatD01 : ∀ η ω, ∀ ζ ∈ sector N r, 0 ≤ datD η ω ζ ∧ datD η ω ζ ≤ 1 := by
    intro η ω ζ _; simp only [hdatD]; split_ifs <;> norm_num
  have hH01 : ∀ n, ∀ ω ∈ gapSet F (c₀ - cmTau N) c₀ n, ∀ k₀, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      ∀ ζ ∈ sector N r, 0 ≤ fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datW k₀) v ω ζ ∧
        fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datW k₀) v ω ζ ≤ 1 := fun n ω hω k₀ =>
    fwdC_bounds hF hNpos hac (cmEll N) r n (datW k₀) hω (fun ζ hζ => (hdatW01 k₀ ω ζ hζ).1)
      fun ζ hζ => (hdatW01 k₀ ω ζ hζ).2
  have hcard_sec : ((sector N r).card : ℝ) ≤ (N : ℝ) ^ r := by
    exact_mod_cast card_sector_le (N := N) r
  have hcard_far : (far.card : ℝ) ≤ (N : ℝ) ^ (r + 1) := by
    have h1 : far.card ≤ ((Finset.univ : Finset (Fin N)) ×ˢ sector N r).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : (far.card : ℝ) ≤ (N : ℝ) * (sector N r).card := by exact_mod_cast h1
    calc (far.card : ℝ) ≤ (N : ℝ) * (sector N r).card := h2
      _ ≤ (N : ℝ) * (N : ℝ) ^ r := mul_le_mul_of_nonneg_left hcard_sec (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ (r + 1) := by ring
  -- the column events
  set Scol : ℝ → Occ N → Set (FlowSample N) := fun v η => {ω |
    (∀ k : Fin N, 0 < η k → |flowEigenvalue F (c₀ - cmTau N) ω (c₀ - cmTau N) k - E| ≤ r₀ / 16) ∧
    ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r
        (c₀ - cmTau N) v Φ ∧
      (∀ ζ ∈ sector N r, Φ (c₀ - cmTau N) ζ = if ζ = η then 1 else 0) ∧
      Real.exp (-(c' * (N : ℝ) ^ (1 / 1000 : ℝ))) <
        ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist η ζ : ℝ)), Φ v ζ}
    with hScol
  have hScolμ : ∀ v ∈ Icc (c₀ - cmTau N) c₀, ∀ η ∈ sector N r,
      flowLaw N (c₀ - cmTau N) (Scol v η) ≤ ENNReal.ofReal x₁ := fun v hv η hη =>
    hN₁ N hn1 F E hC (c₀ - cmTau N) v le_rfl hv.1 hv.2 η hη
  set δ : ℝ := (far.card : ℝ) * ((N : ℝ) ^ r * x₁) with hδdef
  set p : ℝ := (P.card : ℝ) * x₁ with hpdef
  set Kb : ℝ := (far.card : ℝ) with hKbdef
  have hδ0 : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg hNr.le r) hx₁0)
  have hp0 : 0 ≤ p := mul_nonneg (Nat.cast_nonneg _) hx₁0
  have hKb0 : 0 ≤ Kb := Nat.cast_nonneg _
  -- per-time bound
  have hbad : ∀ n : ℕ, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      flowLaw N (c₀ - cmTau N) {ω | ω ∈ gapSet F (c₀ - cmTau N) c₀ n ∧ δ < Y n v ω} ≤
        ENNReal.ofReal p := by
    intro n v hv
    have hU : flowLaw N (c₀ - cmTau N) (⋃ pp ∈ P, Scol v pp.2) ≤ ENNReal.ofReal p := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal x₁) fun pp hpp =>
        hScolμ v hv pp.2 (mem_windowPairs.1 (show (pp.1, pp.2) ∈ P from hpp)).1).trans (le_of_eq ?_)
      rw [nsmul_eq_mul, hpdef, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    refine le_trans (measure_mono fun ω hω => ?_) hU
    obtain ⟨hωG, hδY⟩ := hω
    by_contra hωU
    have hωS : ∀ pp ∈ P, ω ∉ Scol v pp.2 := fun pp hpp h =>
      hωU (mem_iUnion₂.2 ⟨pp, hpp, h⟩)
    have hYle : Y n v ω ≤ δ := by
      simp only [hYdef, hδdef]
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun pp hpp => ?_
      have hpp' : pp.2 ∈ sector N r ∧ 2 * W < (rampDist (pp.1 : ℕ) pp.2 : ℝ) := by
        have := Finset.mem_filter.1 hpp
        exact ⟨(Finset.mem_product.1 this.1).2, this.2⟩
      by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
      · simp only [Set.indicator_of_mem hnb]
        obtain ⟨hsH, h0H⟩ := fwdC_isSolution hF hNpos hac (cmEll N) r n (datW pp.1) hωG
        have hdec := window_decomp (fun x _ i j _ => shortFlowRate_nonneg F _ ω (cmEll N) x i j)
          (winS pp.1) hsH (fun ζ hζ => by
            rw [h0H ζ hζ]; simp only [hdatW, hwinS, Finset.mem_filter, hζ, true_and])
          (Φ := fun η v => fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω)
          (fun η _ => (fwdC_isSolution hF hNpos hac (cmEll N) r n (datD η) hωG).1)
          (fun η _ ζ hζ => (fwdC_isSolution hF hNpos hac (cmEll N) r n (datD η) hωG).2 ζ hζ)
        rw [hdec v hv pp.2 hpp'.1]
        calc ∑ η ∈ winS pp.1, fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω pp.2
            ≤ ∑ _η ∈ winS pp.1, x₁ := by
              refine Finset.sum_le_sum fun η hη => ?_
              have hη' : η ∈ sector N r ∧ (rampDist (pp.1 : ℕ) η : ℝ) ≤ W :=
                Finset.mem_filter.1 hη
              have hPη : (pp.1, η) ∈ P := mem_windowPairs.2 hη'
              have hnS := hωS (pp.1, η) hPη
              have hbη := bulk_of_nearBulk hnb (hη'.2.trans hWρ)
              obtain ⟨hsD, h0D⟩ := fwdC_isSolution hF hNpos hac (cmEll N) r n (datD η) hωG
              have hbig : ¬ Real.exp (-(c' * (N : ℝ) ^ (1 / 1000 : ℝ))) <
                  ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist η ζ : ℝ)),
                    fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω ζ := fun hlt =>
                hnS ⟨fun k hk => hbη k hk _ ⟨le_rfl, hac⟩, _, hsD.mono_right hv.2, h0D, hlt⟩
              have hfar : pp.2 ∈ (sector N r).filter
                  (fun ζ => (r : ℝ) * R < (occDist η ζ : ℝ)) := by
                refine Finset.mem_filter.2 ⟨hpp'.1, ?_⟩
                have h1 := rampDist_sub_le_occDist hη'.1 hpp'.1 (pp.1 : ℕ)
                have h2 := neg_abs_le ((rampDist (pp.1 : ℕ) η : ℝ) - rampDist (pp.1 : ℕ) pp.2)
                have h3 := hRW
                linarith [hpp'.2, hη'.2]
              have hnn : ∀ ζ ∈ sector N r,
                  0 ≤ fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω ζ := fun ζ hζ =>
                (fwdC_bounds hF hNpos hac (cmEll N) r n (datD η) hωG
                  (fun ζ hζ => (hdatD01 η ω ζ hζ).1) (fun ζ hζ => (hdatD01 η ω ζ hζ).2)
                  v hv ζ hζ).1
              calc fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω pp.2
                  ≤ ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist η ζ : ℝ)),
                    fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datD η) v ω ζ :=
                    Finset.single_le_sum (fun ζ hζ => hnn ζ (Finset.mem_filter.1 hζ).1) hfar
                _ ≤ Real.exp (-(c' * (N : ℝ) ^ (1 / 1000 : ℝ))) := not_lt.1 hbig
                _ ≤ x₁ := hexp
          _ = (winS pp.1).card * x₁ := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (N : ℝ) ^ r * x₁ := by
              refine mul_le_mul_of_nonneg_right ?_ hx₁0
              exact (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans hcard_sec
      · simp only [Set.indicator_of_notMem hnb]
        exact mul_nonneg (pow_nonneg hNr.le r) hx₁0
    linarith
  -- one bad set for the excess
  have ht : 0 < (N : ℝ) ^ (-Dp) := Real.rpow_pos_of_pos hNr _
  have hmemfar : ∀ pp ∈ far, pp.2 ∈ sector N r := fun pp hpp =>
    (Finset.mem_product.1 (Finset.mem_filter.1 hpp).1).2
  have hY0 : ∀ n, ∀ ω ∈ gapSet F (c₀ - cmTau N) c₀ n, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      0 ≤ Y n v ω := by
    intro n ω hω v hv
    refine Finset.sum_nonneg fun pp hpp => ?_
    by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
    · simp only [Set.indicator_of_mem hnb]
      exact (hH01 n ω hω pp.1 v hv pp.2 (hmemfar pp hpp)).1
    · simp only [Set.indicator_of_notMem hnb]; exact le_rfl
  have hYK : ∀ n, ∀ ω ∈ gapSet F (c₀ - cmTau N) c₀ n, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      Y n v ω ≤ Kb := by
    intro n ω hω v hv
    simp only [hYdef, hKbdef]
    rw [← mul_one (far.card : ℝ), ← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun pp hpp => ?_
    by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
    · simp only [Set.indicator_of_mem hnb]
      exact (hH01 n ω hω pp.1 v hv pp.2 (hmemfar pp hpp)).2
    · simp only [Set.indicator_of_notMem hnb]; exact zero_le_one
  have hYm : ∀ n, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      Measurable[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] (Y n v) := fun n v _ =>
    Finset.measurable_sum _ fun pp _ =>
      (measurable_fwdC hF hNpos hac (cmEll N) r n (Φ₀ := datW pp.1)
        (fun _ => measurable_const) v pp.2).indicator
        (measurableSet_nearBulk hF _ c₀ E (r₀ / 16) ρ pp.1)
  have hYc : ∀ n ω, Continuous fun v => Y n v ω := by
    intro n ω
    refine continuous_finsetSum _ fun pp _ => ?_
    by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
    · simp only [Set.indicator_of_mem hnb]
      exact continuous_fwdC hF hNpos _ c₀ (cmEll N) r n (datW pp.1) ω pp.2
    · simp only [Set.indicator_of_notMem hnb]; exact continuous_const
  have hcons : ∀ n, ∀ ω ∈ gapSet F (c₀ - cmTau N) c₀ n, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      Y (n + 1) v ω = Y n v ω := by
    intro n ω hω v hv
    refine Finset.sum_congr rfl fun pp hpp => ?_
    by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
    · simp only [Set.indicator_of_mem hnb]
      exact fwdC_succ hF hNpos hac (cmEll N) r n (datW pp.1) hω v hv pp.2 (hmemfar pp hpp)
    · simp only [Set.indicator_of_notMem hnb]
  obtain ⟨Bc, hBcm, hBcμ, hBc⟩ := excess_core (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀)
    (pathSigma_le F (c₀ - cmTau N) (c₀ - cmTau N) c₀) (flowLaw N (c₀ - cmTau N)) hac
    (gapSet F (c₀ - cmTau N) c₀) (measurableSet_gapSet hF _ c₀) (gapSet_mono F _ c₀) Y hYm
    (fun n ω => (hYc n ω).continuousOn) hY0 hYK hKb0 hδ0 hp0 ht hcons hbad
  -- arithmetic
  have hpow : ∀ (k : ℕ) (y z : ℝ), (k : ℝ) + y ≤ z → (N : ℝ) ^ k * (N : ℝ) ^ y ≤ (N : ℝ) ^ z := by
    intro k y z h
    rw [← Real.rpow_natCast, ← Real.rpow_add hNr]
    exact Real.rpow_le_rpow_of_exponent_le hN1 h
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hδQ : δ ≤ (N : ℝ) ^ (Q + 1 - D₁) := by
    calc δ ≤ (N : ℝ) ^ (r + 1) * ((N : ℝ) ^ r * x₁) :=
          mul_le_mul_of_nonneg_right hcard_far (mul_nonneg (pow_nonneg hNr.le r) hx₁0)
      _ = (N : ℝ) ^ (r + 1 + r) * x₁ := by rw [pow_add (N : ℝ) (r + 1) r]; ring
      _ ≤ (N : ℝ) ^ (Q + 1 - D₁) := hpow _ _ _ (by rw [hQ]; push_cast; linarith)
  have hKbQ : Kb ≤ (N : ℝ) ^ Q := by
    calc Kb ≤ (N : ℝ) ^ (r + 1) * (N : ℝ) ^ (0 : ℝ) := by
          rw [Real.rpow_zero, mul_one]; exact hcard_far
      _ ≤ (N : ℝ) ^ Q := hpow _ _ _ (by rw [hQ]; push_cast; linarith)
  have hpQ : p ≤ (N : ℝ) ^ ((r : ℝ) + 2 - D₁) := by
    calc p ≤ (N : ℝ) ^ (r + 1) * x₁ :=
          mul_le_mul_of_nonneg_right ((card_windowPairs_le r W)) hx₁0
      _ ≤ (N : ℝ) ^ ((r : ℝ) + 2 - D₁) := hpow _ _ _ (by push_cast; linarith)
  have hDp1 : 1 ≤ Dp := le_max_right _ _
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  obtain ⟨hfin, hδD⟩ := longShort_final_arith (τ' := c₀ - (c₀ - cmTau N)) hN4 hDp1 hQ0 hr0 rfl
    (by have := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1 / 100 : ℝ) ≤ 0)
        unfold cmTau; linarith) hδ0 hδQ hKb0 hKbQ hp0 hpQ
  have hDD : (N : ℝ) ^ (-Dp) ≤ (N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_left _ _))
  refine ⟨Bc ∪ Bbk, hBcm.union hBbkm, ?_, ?_⟩
  · calc flowLaw N (c₀ - cmTau N) (Bc ∪ Bbk)
        ≤ flowLaw N (c₀ - cmTau N) Bc + flowLaw N (c₀ - cmTau N) Bbk := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((c₀ - (c₀ - cmTau N)) * (δ + Kb * p) / (N : ℝ) ^ (-Dp) + p) +
            ENNReal.ofReal x₁ := add_le_add hBcμ hBbkμ
      _ = ENNReal.ofReal ((c₀ - (c₀ - cmTau N)) * (δ + Kb * p) / (N : ℝ) ^ (-Dp) + p + x₁) := by
          rw [ENNReal.ofReal_add (add_nonneg (div_nonneg (mul_nonneg (by linarith)
            (add_nonneg hδ0 (mul_nonneg hKb0 hp0))) ht.le) hp0) hx₁0]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal (hfin.trans hDD)
  · filter_upwards [ae_exists_gapSet (hDBM N) hF ha hac] with ω hgap hωB
    obtain ⟨n, hn⟩ := hgap
    have hωc : ω ∉ Bc := fun h => hωB (Or.inl h)
    have hωb : ω ∉ Bbk := fun h => hωB (Or.inr h)
    obtain ⟨hint, hend⟩ := hBc ω hωc n hn
    refine ⟨fun u => Y n u ω, ⟨fun u hu => hY0 n ω hn u hu,
      (hYc n ω).intervalIntegrable _ _, hint.trans hDD, hend.trans (hδD.trans hDD)⟩, ?_⟩
    intro σ₀ hσ₀ k₀ hk₀ h hh hh0 u hu ζ hζ hfarζ
    have hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ k₀ := fun v hv k hk =>
      hBbk ω hωb k₀ k σ₀ hσ₀ (hk₀.trans hcen) (nearCfg_pos.1 hk) v hv
    have hpk : (k₀, ζ) ∈ far := Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, hζ⟩, hfarζ⟩
    rw [shortSol_eq_fwdC hF hNpos hac (cmEll N) r n (datW k₀) hn hh (fun ζ' hζ' => hh0 ζ' hζ')
      u hu ζ hζ]
    have h1 := Finset.single_le_sum (f := fun pp : Fin N × Occ N =>
      (nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1).indicator
        (fun ω => fwdC F (c₀ - cmTau N) c₀ (cmEll N) r n (datW pp.1) u ω pp.2) ω)
      (fun pp hpp => by
        by_cases hnb' : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
        · simp only [Set.indicator_of_mem hnb']
          exact (hH01 n ω hn pp.1 u hu pp.2 (hmemfar pp hpp)).1
        · simp only [Set.indicator_of_notMem hnb']; exact le_rfl) hpk
    simp only [Set.indicator_of_mem hnb] at h1
    exact h1

end BlockBand.Palm.MomentFlow
