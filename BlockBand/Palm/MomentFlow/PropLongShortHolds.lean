module

public import BlockBand.Palm.MomentFlow.PropLongShortArith

/-!
# `LongShortPropagation` holds

`longShortPropagation_holds` proves `LongShortPropagation` with `C₁ = 4r + 1` and `C₂ = 1`.
Hypotheses: `MultiShortFiniteSpeed` (row finite speed), `ExternalLocalGUE`,
`MDEBranchIdentification`, `GaussianLpGradient`, `MultivariateGaussianIBP` and
`DysonBrownianMotion N` for every `N`.

Proof.
1. If no `RegVersion` exists the statement is vacuous (`B = ∅`). Otherwise fix one, `Φ₀`; it
   supplies the long-jump bound (`d6_uniform`) and `M_loc` (`mloc_uniform`) along a.e. path.
2. Canonical `𝓛`-measurable flows `fullC`, `shortC` from `canonDatum` at gap level `1/(n+1)`;
   every `RegVersion` and every short solution from `Φ(a)` coincide with them on
   `gapSet n`.
3. Per deterministic time `v` and window pair `(k₀, ζ)` (`windowPairs`, at most `N^{r+1}`), `longShort_multi`
   (row tails from `MultiShortFiniteSpeed` at `R = N^{1/1000} ℓ`) with the local error
   `e_loc = r d + (r+1) b r L` (the long-jump bound, `M_loc` and `longCoupling_good`, on the
   `occDist` ball, which lies in the bulk by `nearBulk`) and the global error `K = 2 B^r (r+1) r L`
   gives `|fullC - shortC|(v, ζ) ≤ e_loc τ + K N^{-D₁}` off a union of bad sets.
4. The excess `longShortExcess` is continuous in time; `excess_core` (Tonelli–Markov, monotone
   union over `n`) bounds its integral and its value at `c₀` off one `𝓛`-set; `e(u)` is the excess.
5. `bulk_near_target` (κ' = 1/1200) puts every label within `N^{1-1/1200}` of an admissible centre
   in the bulk on all of `[a, c₀]`, so the centre's term appears in the excess.
6. `e_loc τ ≤ N^{(4r+1)ε} N τ/ℓ` (`eloc_le`: ε-dependent constants absorbed in `N^ε`; the
   `max(1, N‖q‖²)^r N^{-D'}` remainders are `≤ 1` by `nsq_le_of_gamma`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

theorem longShortPropagation_holds (hMS : MultiShortFiniteSpeed) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient) (hIBP : MultivariateGaussianIBP)
    (hDBM : ∀ N : ℕ, DysonBrownianMotion N) : LongShortPropagation := by
  classical
  intro A c₀ r₀ s₀ v₀ hK r hr M Kw hKw
  refine ⟨4 * r + 1, 1, fun ε hε hε1 D => ?_⟩
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨Cst', hCst', hMl⟩ := mloc_uniform hELG hMDE hLp hDBM (A := A) hK hε (by linarith)
  obtain ⟨c₁, c₂, Cst, Cov, hc₁, hc₂, hCst, hCov, hD6⟩ :=
    d6_uniform hELG hMDE hLp hIBP hDBM (A := A) hK hε (by linarith)
  obtain ⟨cL, CL, -, hCL, hLong⟩ := longCoupling_good hLp hIBP (A := A) hK
  set Cq : ℝ := max 1 (1 / (v₀ * lowConst c₀ s₀ v₀)) with hCq
  set Dp : ℝ := max D 1 with hDp
  set Qo : ℝ := r * (1 + 2 * max A 1) + 1 with hQo
  set Q : ℝ := Qo + r + 2 with hQ
  set D₁ : ℝ := 2 * Dp + Q + r + 5 with hD₁
  set D' : ℝ := max D₁ (Qo + 3) with hD'
  set Kc : ℝ := r * max 1 Cov ^ r * (2 * Cst / c₁) + r + (r + 1) * r * CL * (max 1 Cst' ^ r + 1)
    with hKc
  obtain ⟨N₁, hN₁⟩ := hMl r D'
  obtain ⟨N₂, hN₂⟩ := hD6 r D'
  obtain ⟨N₃, hN₃⟩ := hLong D₁
  obtain ⟨N₄, hN₄⟩ := longShort_multi hMS hDBM (A := A) hK hr (ε := 1 / 1000) (by norm_num) D₁
  obtain ⟨N₅, hN₅⟩ := bulk_near_target hLp hIBP (A := A) hK (κ' := 1 / 1200) (by norm_num) D₁
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((hnat.eventually_ge_atTop 4).and ((hτ0.eventually (gt_mem_nhds hK.1)).and
      ((eventually_window_le Kw r).and ((eventually_center_le M hr₀).and
      ((eventually_const_le_rpow Kc hε).and ((hnat.eventually_ge_atTop (Cq ^ r)).and
      ((hnat.eventually_ge_atTop (1 / c₂ ^ 2)).and
      ((hnat.eventually_ge_atTop (2 * (r + 1) * r * CL)).and
      ((eventually_ge_atTop N₁).and ((eventually_ge_atTop N₂).and ((eventually_ge_atTop N₃).and
      ((eventually_ge_atTop N₄).and (eventually_ge_atTop N₅)))))))))))))
  refine ⟨N₀, fun N hN F E hC q hq => ?_⟩
  obtain ⟨hN4, hτc, hwin, hcen, hKcN, hCqN, hc2N, hCLN, hn1, hn2, hn3, hn4, hn5⟩ := hN₀ N hN
  have hF := hC.1
  have hNr : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hτpos : 0 < cmTau N := Real.rpow_pos_of_pos hNr _
  have ha : 0 < c₀ - cmTau N := by unfold cmTau; linarith
  have hac : c₀ - cmTau N ≤ c₀ := by linarith
  have hτ1 : cmTau N ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hℓ1 : (1 : ℝ) ≤ cmEll N := by
    have : 1 ≤ cmEll N := Nat.le_floor (by
      push_cast; exact Real.one_le_rpow hN1 (by norm_num))
    exact_mod_cast this
  have hℓN : (cmEll N : ℝ) ≤ N := (cmEll_le_rpow N).trans
    ((Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 : ℝ) - 1 / 300 ≤ 1)).trans
      (le_of_eq (Real.rpow_one _)))
  -- the bad sets
  obtain ⟨Bml, hBmlm, hBmlμ, hBml⟩ := hN₁ N hn1 F E hC q hq
  obtain ⟨Bd6, hBd6m, hBd6μ, hBd6⟩ := hN₂ N hn2 F E hC q hq
  obtain ⟨BL, hBLm, hBLμ, hBL⟩ := hN₃ N hn3 F E hC
  obtain ⟨Bbk, hBbkm, hBbkμ, hBbk⟩ := hN₅ N hn5 F E hC
  have hl3 := hN₄ N hn4 F E hC
  by_cases hex : ∃ Φ₀ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ₀
  swap
  · exact ⟨∅, @MeasurableSet.empty _ (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀),
      by simp, fun Φ hΦ => absurd ⟨Φ, hΦ⟩ hex⟩
  obtain ⟨Φ₀, hΦ₀⟩ := hex
  -- constants
  set Ob : ℝ := overlapBound N q with hOb
  have hObpoly : Ob ^ r ≤ (N : ℝ) ^ Qo :=
    pow_le_poly hN1 (by linarith [one_le_overlapBound q]) (overlapBound_le_poly hNpos hK hC hq)
      hCqN
  have hOb0 : 0 ≤ Ob ^ r := pow_nonneg (by linarith [one_le_overlapBound q]) r
  set j₁ : ℝ := (N : ℝ) * ((N : ℝ) / c₂ ^ 2) * Ob ^ r * (N : ℝ) ^ (-D') with hj₁def
  set j₂ : ℝ := Ob ^ r * (N : ℝ) ^ (-D') with hj₂def
  obtain ⟨hj₁, hj₂⟩ := junk_le hN1 hc₂ hObpoly (le_max_right _ _) hc2N
  have hDpow : 0 < (N : ℝ) ^ (-D') := Real.rpow_pos_of_pos hNr _
  set d : ℝ := (Cov * (N : ℝ) ^ (4 * ε)) ^ (r - 1) * (2 / (c₁ * cmEll N / N) * Cst) + j₁
    with hddef
  set b : ℝ := (Cst' * (N : ℝ) ^ (4 * ε)) ^ r + j₂ with hbdef
  set L : ℝ := CL * N / cmEll N with hLdef
  set eloc : ℝ := r * d + (r + 1) * b * (r * L) with heldef
  have hd0 : 0 ≤ d := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hL0 : 0 ≤ L := by positivity
  have heloc0 : 0 ≤ eloc := by positivity
  have heloc : eloc ≤ (N : ℝ) ^ ((4 * r + 1) * ε) * (N / cmEll N) :=
    eloc_le hN1 (by linarith) hℓN hε.le hCov hCst hCst' hc₁ hCL.le hj₁ hj₂ hKcN
  set main : ℝ := eloc * cmTau N with hmaindef
  have hmain0 : 0 ≤ main := mul_nonneg heloc0 hτpos.le
  set Kg : ℝ := 2 * Ob ^ r * (r + 1) * r * L with hKgdef
  have hKg0 : 0 ≤ Kg := by positivity
  set W : ℝ := Kw * cmW N with hWdef
  set ρ : ℝ := (N : ℝ) ^ (1 - (1 / 1200 : ℝ)) with hρdef
  set R : ℝ := (N : ℝ) ^ (1 / 1000 : ℝ) * cmEll N with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hWR : W + r * R ≤ ρ := hwin
  have hWρ : W ≤ ρ := by have : 0 ≤ (r : ℝ) * R := by positivity
                         linarith
  set P := windowPairs N r W with hPdef
  set x₁ : ℝ := (N : ℝ) ^ (-D₁) with hx₁def
  have hx₁0 : 0 ≤ x₁ := (Real.rpow_pos_of_pos hNr _).le
  set δ : ℝ := P.card * (Kg * x₁) with hδdef
  set p : ℝ := (3 + P.card) * x₁ with hpdef
  set Kb : ℝ := P.card * (2 * Ob ^ r) with hKbdef
  have hcard0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hδ0 : 0 ≤ δ := mul_nonneg hcard0 (mul_nonneg hKg0 hx₁0)
  have hp0 : 0 ≤ p := mul_nonneg (add_nonneg (by norm_num) hcard0) hx₁0
  have hKb0 : 0 ≤ Kb := mul_nonneg hcard0 (mul_nonneg zero_le_two hOb0)
  set Y : ℕ → ℝ → FlowSample N → ℝ := fun n v ω =>
    longShortExcess F (c₀ - cmTau N) c₀ q (cmEll N) r n E (r₀ / 16) ρ W main v ω with hYdef
  
  have hl3' : ∀ v : ℝ, ∀ ζ : Occ N, ∃ B : Set (FlowSample N),
      MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
      flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal x₁ ∧
      (v ∈ Icc (c₀ - cmTau N) c₀ → ζ ∈ sector N r →
        ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
          (∀ v' ∈ Icc (c₀ - cmTau N) v, ∀ k : Fin N, 0 < ζ k →
            |flowEigenvalue F (c₀ - cmTau N) ω v' k - E| ≤ r₀ / 16) →
          ∀ (Φ G : ℝ → Occ N → ℝ) (e K : ℝ), 0 ≤ e → 0 ≤ K →
            IsMomentFlowSolution (flowRate F (c₀ - cmTau N) ω) r (c₀ - cmTau N) v Φ →
            IsMomentFlowSolution (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r
              (c₀ - cmTau N) v G →
            (∀ ζ' ∈ sector N r, Φ (c₀ - cmTau N) ζ' = G (c₀ - cmTau N) ζ') →
            (∀ v' ∈ Icc (c₀ - cmTau N) v, ∀ η ∈ sector N r, η ∈ occBall r R ζ →
              |momentGenerator (flowRate F (c₀ - cmTau N) ω v') (Φ v') η -
                momentGenerator (shortFlowRate F (c₀ - cmTau N) ω (cmEll N) v') (Φ v') η| ≤
                e) →
            (∀ v' ∈ Icc (c₀ - cmTau N) v, ∀ η ∈ sector N r,
              |momentGenerator (flowRate F (c₀ - cmTau N) ω v') (Φ v') η -
                momentGenerator (shortFlowRate F (c₀ - cmTau N) ω (cmEll N) v') (Φ v') η| ≤
                K) →
            |Φ v ζ - G v ζ| ≤ e * (v - (c₀ - cmTau N)) + K * x₁) := by
    intro v ζ
    by_cases hv : v ∈ Icc (c₀ - cmTau N) c₀ ∧ ζ ∈ sector N r
    · obtain ⟨B, hB1, hB2, hB3⟩ := hl3 (c₀ - cmTau N) v le_rfl hv.1.1 hv.1.2 ζ hv.2
      exact ⟨B, hB1, hB2, fun _ _ => hB3⟩
    · exact ⟨∅, @MeasurableSet.empty _ (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀),
        by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
  choose Bl hBlm hBlμ hBl using hl3'
  -- the per-time bound
  have hD'1 : ENNReal.ofReal ((N : ℝ) ^ (-D')) ≤ ENNReal.ofReal x₁ :=
    ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_left _ _)))
  have hbad : ∀ n : ℕ, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      flowLaw N (c₀ - cmTau N) {ω | ω ∈ gapSet F (c₀ - cmTau N) c₀ n ∧ δ < Y n v ω} ≤
        ENNReal.ofReal p := by
    intro n v hv
    set U : Set (FlowSample N) := Bml ∪ Bd6 ∪ BL ∪ ⋃ pp ∈ P, Bl v pp.2 with hUdef
    have hU : flowLaw N (c₀ - cmTau N) U ≤ ENNReal.ofReal p := by
      calc flowLaw N (c₀ - cmTau N) U
          ≤ flowLaw N (c₀ - cmTau N) Bml + flowLaw N (c₀ - cmTau N) Bd6 +
              flowLaw N (c₀ - cmTau N) BL + ∑ pp ∈ P, flowLaw N (c₀ - cmTau N) (Bl v pp.2) := by
            refine (measure_union_le _ _).trans (add_le_add ?_ (measure_biUnion_finset_le _ _))
            exact (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ ≤ ENNReal.ofReal x₁ + ENNReal.ofReal x₁ + ENNReal.ofReal x₁ +
              ∑ _pp ∈ P, ENNReal.ofReal x₁ := by
            gcongr with pp hpp
            · exact hBmlμ.trans hD'1
            · exact hBd6μ.trans hD'1
            · exact hBLμ
            · exact hBlμ v pp.2
        _ = ENNReal.ofReal p := by
            rw [Finset.sum_const, nsmul_eq_mul,
              show p = x₁ + x₁ + x₁ + (P.card : ℝ) * x₁ by rw [hpdef]; ring,
              ENNReal.ofReal_add (by linarith) (mul_nonneg hcard0 hx₁0),
              ENNReal.ofReal_add (by linarith) hx₁0,
              ENNReal.ofReal_add hx₁0 hx₁0, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
    refine le_trans (measure_mono_ae ?_) hU
    filter_upwards [hBml Φ₀ hΦ₀, hBd6 Φ₀ hΦ₀, regVersion_eq_fullC (hDBM N) hF hNpos ha hac hΦ₀,
      (eventually_all_finset P).2 fun pp hpp =>
        hBl v pp.2 hv (mem_windowPairs.1 (show (pp.1, pp.2) ∈ P from hpp)).1]
      with ω hml hd6 hreg hl3s
    intro hω
    obtain ⟨hωG, hδY⟩ := hω
    by_contra hωU
    have hωml : ω ∉ Bml := fun h => hωU (Or.inl (Or.inl (Or.inl h)))
    have hωd6 : ω ∉ Bd6 := fun h => hωU (Or.inl (Or.inl (Or.inr h)))
    have hωL : ω ∉ BL := fun h => hωU (Or.inl (Or.inr h))
    have hωl3 : ∀ pp ∈ P, ω ∉ Bl v pp.2 := fun pp hpp h =>
      hωU (Or.inr (mem_iUnion₂.2 ⟨pp, hpp, h⟩))
    have hmlω := hml hωml
    have hd6ω := hd6 hωd6
    have heq := hreg.2.2 n hωG
    have hLω : ∀ σ ∈ Icc (c₀ - cmTau N) c₀, ∀ i : Fin N,
        longCoupling F (c₀ - cmTau N) ω (cmEll N) σ i ≤ L := fun σ hσ i =>
      (hBL ω hωL σ hσ).2 i
    obtain ⟨hsF, h0F⟩ := fullC_isSolution hF hNpos hac q r n hωG
    obtain ⟨hsS, h0S⟩ := shortC_isSolution hF hNpos hac q (cmEll N) r n hωG
    have hloc := fullC_localGen (Φ := Φ₀) (κ := r₀ / 2) (d := d) (b := b) heq
      (fun ξ hξ σ hσ => (hmlω ξ hξ σ hσ).1) (fun ξ hξ σ hσ hbk => (hmlω ξ hξ σ hσ).2 hbk)
      (fun ξ hξ i hi hbk σ hσ => hd6ω ξ hξ i hi hbk σ hσ) hLω
    have hglob := fullC_globalGen hF hNpos hac q (cmEll N) r n hωG hLω
    have hYle : Y n v ω ≤ δ := by
      simp only [hYdef, longShortExcess, hδdef]
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun pp hpp => ?_
      have hpp' := mem_windowPairs.1 (show (pp.1, pp.2) ∈ P from hpp)
      by_cases hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ pp.1
      · simp only [Set.indicator_of_mem hnb]
        refine max_le ?_ (mul_nonneg hKg0 hx₁0)
        have hbζ := bulk_of_nearBulk hnb (hpp'.2.trans hWρ)
        have hb3 := hl3s pp hpp (hωl3 pp hpp)
          (fun v' hv' k hk => hbζ k hk v' ⟨hv'.1, hv'.2.trans hv.2⟩)
          (fun σ => fullC F (c₀ - cmTau N) c₀ q r n σ ω)
          (fun σ => shortC F (c₀ - cmTau N) c₀ q (cmEll N) r n σ ω) eloc Kg heloc0 hKg0
          (hsF.mono_right hv.2) (hsS.mono_right hv.2)
          (fun ζ' hζ' => by rw [h0F ζ' hζ', h0S ζ' hζ'])
          (fun v' hv' η hη hηB => by
            have hv'c : v' ∈ Icc (c₀ - cmTau N) c₀ := ⟨hv'.1, hv'.2.trans hv.2⟩
            have hrη : (rampDist (pp.1 : ℕ) η : ℝ) ≤ ρ :=
              (rampDist_le_of_mem_occBall hpp'.1 hηB _).trans (by linarith [hpp'.2])
            have hbη := bulk_of_nearBulk hnb hrη
            exact hloc v' hv'c η hη fun k hk σ' hσ' =>
              (hbη k hk σ' hσ').trans (by linarith))
          (fun v' hv' η hη => hglob v' ⟨hv'.1, hv'.2.trans hv.2⟩ η hη)
        have hva : eloc * (v - (c₀ - cmTau N)) ≤ main :=
          mul_le_mul_of_nonneg_left (by linarith [hv.2]) heloc0
        linarith
      · simp only [Set.indicator_of_notMem hnb]
        exact mul_nonneg hKg0 hx₁0
    linarith
  -- one bad set for the excess
  have ht : 0 < (N : ℝ) ^ (-Dp) := Real.rpow_pos_of_pos hNr _
  obtain ⟨Bc, hBcm, hBcμ, hBc⟩ := excess_core (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀)
    (pathSigma_le F (c₀ - cmTau N) (c₀ - cmTau N) c₀) (flowLaw N (c₀ - cmTau N)) hac
    (gapSet F (c₀ - cmTau N) c₀) (measurableSet_gapSet hF _ c₀) (gapSet_mono F _ c₀) Y
    (fun n v _ => measurable_longShortExcess hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W main v)
    (fun n ω => (continuous_longShortExcess hF hNpos _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main
      ω).continuousOn)
    (fun n ω _ v _ => longShortExcess_nonneg F _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main v ω)
    (fun n ω hω v hv => longShortExcess_le hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W hmain0 hω hv)
    (K := Kb) hKb0 hδ0 hp0 ht
    (fun n ω hω v hv => longShortExcess_succ hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W main hω hv)
    hbad
  -- arithmetic
  have hcard : (P.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) + 1) := by
    rw [show ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact card_windowPairs_le r W
  obtain ⟨hc1, hc2, hc3⟩ := longShort_counts_le (D₁ := D₁) hN4 (Nat.cast_nonneg _) hcard hOb0 hObpoly
    hCL hCLN hℓ1
  have hDp1 : 1 ≤ Dp := le_max_right _ _
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right _ _)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    rw [hQ, hQo]; positivity
  obtain ⟨hfin, hδD⟩ := longShort_final_arith (τ' := c₀ - (c₀ - cmTau N)) hN4 hDp1 hQ0
    (Nat.cast_nonneg r) rfl (by linarith) hδ0
    (hc1.trans (le_of_eq (by rw [show Qo + r + 3 - D₁ = Q + 1 - D₁ by rw [hQ]; ring]))) hKb0 (hc2.trans (le_of_eq (by rw [hQ])))
    hp0 hc3
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
  · intro Φ hΦ
    filter_upwards [regVersion_eq_fullC (hDBM N) hF hNpos ha hac hΦ,
      ae_exists_gapSet (hDBM N) hF ha hac] with ω hreg hgap hωB
    obtain ⟨n, hn⟩ := hgap
    obtain ⟨h0, -, heq⟩ := hreg
    have hωc : ω ∉ Bc := fun h => hωB (Or.inl h)
    have hωb : ω ∉ Bbk := fun h => hωB (Or.inr h)
    obtain ⟨hint, hend⟩ := hBc ω hωc n hn
    refine ⟨fun u => Y n u ω, ⟨fun u _ => longShortExcess_nonneg F _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W
      main u ω, (continuous_longShortExcess hF hNpos _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main
      ω).intervalIntegrable _ _, hint.trans hDD, hend.trans (hδD.trans hDD)⟩, ?_⟩
    intro σ₀ hσ₀ k₀ hk₀ h hh hh0 u hu ζ hζ hrd
    have hnb : ω ∈ nearBulk F (c₀ - cmTau N) c₀ E (r₀ / 16) ρ k₀ := fun v hv k hk =>
      hBbk ω hωb k₀ k σ₀ hσ₀ (hk₀.trans hcen) (nearCfg_pos.1 hk) v hv
    have hpk : (k₀, ζ) ∈ P := mem_windowPairs.2 ⟨hζ, hrd⟩
    have hterm := term_le_longShortExcess (F := F) (a := c₀ - cmTau N) (c := c₀) (q := q)
      (ℓ := cmEll N) (n := n) (main := main) (v := u) hpk hnb
    rw [heq n hn u hu ζ hζ, shortSol_eq_shortC hF hNpos hac q (cmEll N) r n hn hh
      (fun ζ' hζ' => (hh0 ζ' hζ').trans (h0 ζ' hζ')) u hu ζ hζ]
    have hmain : main ≤ 1 * (N : ℝ) ^ ((4 * r + 1) * ε) * ((N : ℝ) * cmTau N / cmEll N) := by
      calc main ≤ (N : ℝ) ^ ((4 * r + 1) * ε) * (N / cmEll N) * cmTau N :=
            mul_le_mul_of_nonneg_right heloc hτpos.le
        _ = 1 * (N : ℝ) ^ ((4 * r + 1) * ε) * ((N : ℝ) * cmTau N / cmEll N) := by ring
    have hmax := le_max_left (|fullC F (c₀ - cmTau N) c₀ q r n u ω ζ -
      shortC F (c₀ - cmTau N) c₀ q (cmEll N) r n u ω ζ| - main) 0
    show _ ≤ _ + Y n u ω
    linarith

end BlockBand.Palm.MomentFlow
