module

public import BlockBand.Palm.MomentFlow.EventHeightDet

/-!
# The isotropic upper bound along the flow at all heights, energies and times

**`isotropic_upper_uniform`** (hypotheses `ExternalLocalGUE`, `MDEBranchIdentification`,
`GaussianLpGradient`): fixed `A`, `FreshConstants c₀ r₀ s₀ v₀`, `0 < ε < 1/4`; a constant `Cst`
(regularity constants and chaining constant only); for every `D` an `N₀`; for `N ≥ N₀`, every `F`
in the fresh class, `a ≥ 0`, `0 < T ≤ 1`, `[a, a+T] ⊆ [c₀-s₀, c₀]`, every `q`: outside a
measurable set of `flowLaw N a`-probability `≤ N^{-D}`, for all `σ ∈ [a, a+T]`, `|x - E| ≤ r₀/2`,
`N^{-1+4ε} ≤ h ≤ 1`: `Im q*(H_σ - x - ih)⁻¹q ≤ Cst · q*Γq`. (Hermitian `ω.1` only; no simple
spectrum needed.)

Proof: mesh `ρ = N^{-p₂}` in energy and height, dyadic time mesh, the external isotropic local law
at every mesh point with loss `N^ε` (`im_resolvent_le_on_good`, `Γ(z) ≍ Γ`), Lipschitz in `z`
(`resolvent_quad_im_lipschitz`), time modulus (`resolvent_quad_im_compare`, `chainGood_modulus`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Palm.CoarseRelative
open BlockBand.Palm BlockBand.Palm.GoodEvent
open scoped ENNReal Matrix.Norms.L2Operator

variable {N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Isotropic upper bound at all heights, energies and times.** -/
theorem isotropic_upper_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ a T : ℝ, 0 ≤ a → 0 < T → T ≤ 1 → c₀ - s₀ ≤ a → a + T ≤ c₀ →
      ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N), MeasurableSet Bad ∧
        flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ σ ∈ Icc a (a + T), ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
          ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
            (star q ⬝ᵥ ((flowMatrix F a ω σ - (⟨x, h⟩ : ℂ) •
              (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im ≤
              Cst * quadForm (freshGamma F c₀ E) q := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  obtain ⟨K₁, hK₁, hchain⟩ := chain_event hLp
  have hcs : 0 < c₀ - s₀ := by linarith
  have hl : 0 < lowConst c₀ s₀ v₀ := by unfold lowConst; positivity
  have hq0 := chainRatio_pos
  have hq1 := chainRatio_lt_one
  set C₂ : ℝ := K₁ / ((1 - chainRatio) * (v₀ * lowConst c₀ s₀ v₀))
  have hC₂ : 0 ≤ C₂ := div_nonneg hK₁.le (mul_nonneg (by linarith) (by positivity))
  have hKc : 0 ≤ gammaCompConst c₀ r₀ s₀ v₀ := by
    unfold gammaCompConst; simp only
    have : 0 < (c₀ - s₀) * v₀ := mul_pos hcs hv0
    positivity
  set C₃ : ℝ := 2 / (v₀ * lowConst c₀ s₀ v₀)
  have hC₃ : 0 ≤ C₃ := by positivity
  refine ⟨(1 + 1 / Real.sqrt (Real.pi * v₀)) * gammaCompConst c₀ r₀ s₀ v₀ + C₂ + C₃, ?_,
    fun D => ?_⟩
  · positivity
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  set κ := max A 0 + 1
  set p : ℕ := ⌈2 * max A 1⌉₊ + 2
  have hp : 2 + 2 * max A 1 ≤ (p : ℝ) := by
    simp only [p]; push_cast; linarith [Nat.le_ceil (2 * max A 1)]
  set p₂ : ℕ := ⌈2 * max A 1⌉₊ + 3
  have hp₂ : 2 + 2 * max A 1 ≤ (p₂ : ℝ) := by
    simp only [p₂]; push_cast; linarith [Nat.le_ceil (2 * max A 1)]
  set D' := max D 0 + 4 * p + 2 * p₂ + 4
  have hD' : 0 < D' := by positivity
  obtain ⟨N₁, hN₁, hloc⟩ := flowLaw_isotropicBad_freshM_le hELG hMDE κ ρ0⁻¹ ε ε D' hε hε hD'
  have h14 : 0 < 1 - 4 * ε := by linarith
  set k₀ : ℕ := ⌈max D 0⌉₊
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k₀ (by norm_num)
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ 8 ≤ n) ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 - 4 * ε)) ≤ min 1 (r₀ / 2) ∧ Real.pi / v₀ ≤ (n : ℝ) ^ (3 * ε) ∧
      (2 + 2 / v₀ + r₀) / ρ0 ≤ (n : ℝ) ∧ r₀ + 2 ≤ (n : ℝ) ∧
      (n : ℝ) ^ (-(p₂ : ℝ)) ≤ r₀ / 2 ∧
      (2 : ℝ) ^ (4 * p + 1) ≤ (n : ℝ) ^ (2 : ℝ) ∧ (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop 8)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 1).and
      ((eventually_rpow_le h14 (lt_min one_pos (by linarith))).and
      ((eventually_rpow_ge (by linarith) _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((eventually_rpow_le (by positivity) (by linarith)).and
      ((eventually_rpow_ge (by norm_num) _).and
      ((hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
        fun _ h => h.le))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC a T ha hT hT1 haT hTc q => ?_⟩
  obtain ⟨⟨hNN₁, hN8⟩, hN1, hηsmall, hdens, hnormN, hcardN, hρr, h2p, hexpN⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hNpos : 0 < N := by exact_mod_cast hNp
  have hrpow_mono : ∀ {p r : ℝ}, p ≤ r → (N : ℝ) ^ p ≤ (N : ℝ) ^ r := fun h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  set η : ℝ := (N : ℝ) ^ (-(1 - 4 * ε))
  have hη : 0 < η := Real.rpow_pos_of_pos hNp _
  have hη1 : η ≤ 1 := hηsmall.trans (min_le_left _ _)
  have hηr : η ≤ r₀ / 2 := hηsmall.trans (min_le_right _ _)
  have hNη : (N : ℝ) * η = (N : ℝ) ^ (4 * ε) := by
    simp only [η]
    rw [← Real.rpow_one_add' hNp.le (by linarith)]
    congr 1; ring
  set ρ : ℝ := (N : ℝ) ^ (-(p₂ : ℝ))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hNp _
  -- the time grid
  set kb : ℕ := Nat.clog 2 N
  set m : ℕ := 4 * p * kb
  set tk : ℕ → ℝ := fun k => a + (k : ℝ) * T / 2 ^ m
  have htk : ∀ k : ℕ, k < 2 ^ m → tk k ∈ Icc (c₀ - s₀) c₀ ∧ a ≤ tk k := by
    intro k hk
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have hk' : (k : ℝ) ≤ 2 ^ m := by exact_mod_cast hk.le
    have h0 : 0 ≤ (k : ℝ) * T / 2 ^ m := by positivity
    have h1 : (k : ℝ) * T / 2 ^ m ≤ T := by
      rw [div_le_iff₀ h2]; nlinarith
    exact ⟨⟨by simp only [tk]; linarith, by simp only [tk]; linarith⟩, by simp only [tk]; linarith⟩
  have hbranch : ∀ k : ℕ, k < 2 ^ m →
      Nonempty (CEH.MDEBranch (Real.sqrt (tk k)) ⟨F, hC.1⟩) := fun k hk =>
    exists_mdeBranch_eq_freshM hMDE hNpos hC.1 (by linarith [(htk k hk).1.1])
  -- the grid-point estimates
  have hpt : ∀ k : ℕ, k < 2 ^ m → ∀ x ∈ energyGrid E r₀ ρ, ∀ y ∈ heightGrid η ρ,
      flowLaw N a {ω | (N : ℝ) ^ ε * CEH.isotropicControl (freshM F (tk k) ⟨x, y⟩) ⟨x, y⟩ q q <
        ‖star q ⬝ᵥ (((flowMatrix F a ω (tk k) - (⟨x, y⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F (tk k) ⟨x, y⟩) *ᵥ q)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro k hk x hx y hy
    obtain ⟨hσ, haσ⟩ := htk k hk
    have hσ0 : 0 < tk k := by linarith [hσ.1]
    obtain ⟨M⟩ := hbranch k hk
    have hxw := energyGrid_window hρ hρr hr0 hx
    obtain ⟨hyη, hy1⟩ := heightGrid_mem hρ hη1 hy
    have hy0 : 0 < y := lt_of_lt_of_le hη hyη
    have hFn : (Real.sqrt (tk k))⁻¹ * ‖F‖ ≤ ρ0⁻¹ * (N : ℝ) ^ κ :=
      (cehNormBound_uniform hC.2.1 hcs hσ.1).trans
        (mul_le_mul_of_nonneg_left (hrpow_mono (by simp only [κ]; linarith [le_max_left A 0]))
          (by positivity))
    have hdom : CEH.InLocalLawDomain M κ ε ⟨x, y⟩ := by
      refine inLocalLawDomain_of_bulk hMDE hNpos hK' hC hσ hxw hy0 hy1 M ?_ ?_
      · show (N : ℝ) ^ ε ≤ (N : ℝ) * y * (v₀ / Real.pi)
        have hNy : (N : ℝ) ^ (4 * ε) ≤ (N : ℝ) * y := by
          rw [← hNη]; exact mul_le_mul_of_nonneg_left hyη hNp.le
        have e : (N : ℝ) ^ (4 * ε) = (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) := by
          rw [← Real.rpow_add hNp]; ring_nf
        have hNe : 0 ≤ (N : ℝ) ^ ε := by positivity
        have : (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) = (N : ℝ) ^ ε := by field_simp
        calc (N : ℝ) ^ ε = (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) := this.symm
          _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) * (v₀ / Real.pi) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdens hNe) (by positivity)
          _ ≤ (N : ℝ) * y * (v₀ / Real.pi) := by
            rw [← e]; exact mul_le_mul_of_nonneg_right hNy (by positivity)
      · have hz := norm_z_le hNpos hK' hC (z := ⟨x, y⟩) hxw hy0.le hy1
        have hsq : ρ0 ≤ Real.sqrt (tk k) := Real.sqrt_le_sqrt hσ.1
        have hm1 : (1 : ℝ) ≤ (N : ℝ) ^ max A 0 := Real.one_le_rpow hN1 (le_max_right _ _)
        have hpow : (N : ℝ) ^ max A 0 * N ≤ (N : ℝ) ^ (κ + 1 / ε) := by
          have : (N : ℝ) ^ max A 0 * N = (N : ℝ) ^ (max A 0 + 1) := by
            rw [Real.rpow_add hNp, Real.rpow_one]
          rw [this]; exact hrpow_mono (by simp only [κ]; have := one_div_pos.2 hε; linarith)
        have hmA : (N : ℝ) ^ A ≤ (N : ℝ) ^ max A 0 := hrpow_mono (le_max_left _ _)
        have hρN : 2 + 2 / v₀ + r₀ ≤ ρ0 * N := by
          rw [div_le_iff₀ hρ0] at hnormN; linarith
        calc ‖(⟨x, y⟩ : ℂ)‖ ≤ (N : ℝ) ^ A + 2 / v₀ + r₀ + 1 := hz
          _ ≤ (N : ℝ) ^ max A 0 * (2 + 2 / v₀ + r₀) := by
              have : 0 ≤ 2 / v₀ + r₀ + 1 := by positivity
              nlinarith
          _ ≤ (N : ℝ) ^ max A 0 * (ρ0 * N) := mul_le_mul_of_nonneg_left hρN (by positivity)
          _ = ρ0 * ((N : ℝ) ^ max A 0 * N) := by ring
          _ ≤ Real.sqrt (tk k) * (N : ℝ) ^ (κ + 1 / ε) :=
              mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _)
    have him : 0 < (freshDyson F (tk k) ⟨x, y⟩).im :=
      lt_of_lt_of_le hv0 (fresh_regular_bounds hC.2.2 hσ hxw hy0.le hy1).1
    exact hloc N hNN₁ a (tk k) ha haσ hσ0 F hC.1 hFn M ⟨x, y⟩ hdom hy0 him q q
  set badk : ℕ → ℝ → ℝ → Set (FlowSample N) := fun k x y => {ω | (N : ℝ) ^ ε *
      CEH.isotropicControl (freshM F (tk k) ⟨x, y⟩) ⟨x, y⟩ q q <
      ‖star q ⬝ᵥ (((flowMatrix F a ω (tk k) - (⟨x, y⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        freshM F (tk k) ⟨x, y⟩) *ᵥ q)‖}
  set Bad₁ : Set (FlowSample N) :=
    ⋃ k ∈ Finset.range (2 ^ m), ⋃ x ∈ energyGrid E r₀ ρ, ⋃ y ∈ heightGrid η ρ, badk k x y
  set Bad₂ : Set (FlowSample N) := {ω | ¬ ChainGood K₁ T ω.2}
  have hρN : (1 : ℝ) / ρ = (N : ℝ) ^ (p₂ : ℝ) := by
    simp only [ρ]; rw [Real.rpow_neg hNp.le, one_div, inv_inv]
  refine ⟨Bad₁ ∪ Bad₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.union ?_ (measurableSet_not_chainGood K₁ T)
    refine Finset.measurableSet_biUnion _ fun k _ => Finset.measurableSet_biUnion _ fun x _ =>
      Finset.measurableSet_biUnion _ fun y _ => ?_
    exact measurableSet_isoBad_flow F a (tk k) _ q _ _
  · have h2k : (2 : ℝ) ^ kb ≤ 2 * N := by
      have hN2 : 1 < N := by omega
      have h3 : 2 ^ kb.pred < N := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN2
      have hkb : 0 < kb := Nat.clog_pos (by norm_num) hN2
      have h' : 2 ^ kb ≤ 2 * N := by
        have e : kb = kb.pred + 1 := (Nat.succ_pred_eq_of_pos hkb).symm
        rw [e, pow_succ]; omega
      exact_mod_cast h'
    have hNp2 : (N : ℝ) ^ (p₂ : ℝ) * N = (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) := by
      rw [show ((p₂ + 1 : ℕ) : ℝ) = (p₂ : ℝ) + 1 by push_cast; ring, Real.rpow_add hNp,
        Real.rpow_one]
    have hone : (1 : ℝ) ≤ (N : ℝ) ^ (p₂ : ℝ) := Real.one_le_rpow hN1 (Nat.cast_nonneg _)
    have hcardE : ((energyGrid E r₀ ρ).card : ℝ) ≤ (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) := by
      have h1 := energyGrid_card_le (E := E) hρ hr0
      rw [div_eq_mul_one_div, hρN] at h1
      rw [← hNp2]
      calc ((energyGrid E r₀ ρ).card : ℝ) ≤ r₀ * (N : ℝ) ^ (p₂ : ℝ) + 2 := h1
        _ ≤ r₀ * (N : ℝ) ^ (p₂ : ℝ) + 2 * (N : ℝ) ^ (p₂ : ℝ) := by linarith
        _ = (r₀ + 2) * (N : ℝ) ^ (p₂ : ℝ) := by ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (p₂ : ℝ) :=
            mul_le_mul_of_nonneg_right hcardN (by positivity)
        _ = _ := by ring
    have hcardH : ((heightGrid η ρ).card : ℝ) ≤ (N : ℝ) ^ ((p₂ + 1 : ℕ) : ℝ) := by
      have h1 := heightGrid_card_le hρ hη.le hη1
      rw [hρN] at h1
      rw [← hNp2]
      have : (N : ℝ) ^ (p₂ : ℝ) + 1 ≤ (N : ℝ) ^ (p₂ : ℝ) * N := by nlinarith
      linarith
    have htimes : ((2 ^ m : ℕ) : ℝ) ≤ 2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ) := by
      have : ((2 ^ m : ℕ) : ℝ) = ((2 : ℝ) ^ kb) ^ (4 * p) := by
        rw [Nat.cast_pow, Nat.cast_two, ← pow_mul]
        congr 1
        simp only [m]; ring
      rw [this, Real.rpow_natCast, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h2k _
    have hsum : ((2 ^ m : ℕ) : ℝ) * ((energyGrid E r₀ ρ).card : ℝ) * ((heightGrid η ρ).card : ℝ) *
        (N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (-D) / 2 :=
      count_le3 hNp hN1 p p₂ D htimes (by positivity) hcardE (by positivity) hcardH h2p
    have hchainN : 2 * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) / 2 :=
      chain_small hNp hN1 ((le_max_left D 0).trans (Nat.le_ceil _)) hexpN
    calc flowLaw N a (Bad₁ ∪ Bad₂) ≤ flowLaw N a Bad₁ + flowLaw N a Bad₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
          gcongr
          · calc flowLaw N a Bad₁ ≤ ∑ k ∈ Finset.range (2 ^ m), ∑ x ∈ energyGrid E r₀ ρ,
                  ∑ y ∈ heightGrid η ρ, flowLaw N a (badk k x y) := by
                  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
                  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
                  exact measure_biUnion_finset_le _ _
              _ ≤ ∑ _k ∈ Finset.range (2 ^ m), ∑ _x ∈ energyGrid E r₀ ρ,
                  ∑ _y ∈ heightGrid η ρ, ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
                  Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun x hx =>
                    Finset.sum_le_sum fun y hy => hpt k (Finset.mem_range.1 hk) x hx y hy
              _ = ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) * ((energyGrid E r₀ ρ).card : ℝ) *
                  ((heightGrid η ρ).card : ℝ) * (N : ℝ) ^ (-D')) := by
                  rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range,
                    nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
                    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
                    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
                  ring
              _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
          · exact (hchain N hN8 a T hT).trans (ENNReal.ofReal_le_ofReal hchainN)
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro ω hω hH σ hσ x hx h hhη hh1
    have hω₁ : ω ∉ Bad₁ := fun h' => hω (Or.inl h')
    have hω₂ : ChainGood K₁ T ω.2 := not_not.1 fun h' => hω (Or.inr h')
    obtain ⟨xj, hxj, hxxj⟩ := energyGrid_cover hρ hx
    have hxw := energyGrid_window hρ hρr hr0 hxj
    obtain ⟨y, hy, hyh, hhy⟩ := heightGrid_cover hρ hhη hh1
    obtain ⟨hyη, hy1⟩ := heightGrid_mem hρ hη1 hy
    have hy0 : 0 < y := lt_of_lt_of_le hη hyη
    have hh0 : 0 < h := lt_of_lt_of_le hη hhη
    obtain ⟨k, hk, hu1, hu2⟩ := dyadic_cell hT m (u := σ - a) (by linarith [hσ.1])
      (by linarith [hσ.2])
    obtain ⟨hσk, haσk⟩ := htk k hk
    have hnot : ω ∉ badk k xj y := fun h' =>
      hω₁ (mem_biUnion (Finset.mem_range.2 hk) (mem_biUnion hxj (mem_biUnion hy h')))
    simp only [badk, Set.mem_ofPred_eq, not_lt] at hnot
    have hHσ := flowMatrix_isHermitian hC.1 a hH σ
    have hHk := flowMatrix_isHermitian hC.1 a hH (tk k)
    have h1 := resolvent_quad_im_lipschitz hHσ (z := ⟨x, h⟩) (z' := ⟨xj, y⟩) hh0 hy0 q
    have h2 := resolvent_quad_im_compare hHσ hHk (z := ⟨xj, y⟩) hy0 q
    have h3 := im_resolvent_le_on_good hK' hC hσk hxw hy0 hy1 hNpos q hnot
    have hmod : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤
        K₁ * Real.sqrt T * chainRatio ^ m / (1 - chainRatio) := by
      have e : flowMatrix F a ω σ - flowMatrix F a ω (tk k) =
          hermitianBrownian ω.2 (σ - a) - hermitianBrownian ω.2 ((k : ℝ) * T / 2 ^ m) := by
        have : tk k - a = (k : ℝ) * T / 2 ^ m := by simp only [tk]; ring
        simp only [flowMatrix]; rw [this]; abel
      rw [e]
      exact chainGood_modulus hK₁.le hT hω₂ m k hk hu1 hu2
    have hqm : chainRatio ^ m ≤ (N : ℝ) ^ (-(p : ℝ)) := by
      have e : chainRatio ^ m = ((1 / 2 : ℝ) ^ kb) ^ p := by
        simp only [m]; rw [show 4 * p * kb = 4 * (kb * p) by ring, pow_mul, chainRatio_pow_four,
          pow_mul]
      rw [e, Real.rpow_neg hNp.le, Real.rpow_natCast, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have hle : (N : ℝ) ≤ 2 ^ kb := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
      rw [one_div, inv_pow]
      exact inv_anti₀ hNp hle
    have hnsq := nsq_le_of_gamma hNpos hK' hC q
    set γ := quadForm (freshGamma F c₀ E) q
    have hγ : 0 ≤ γ := by
      simp only [γ]; rw [freshGamma_quad_eq hC.1]
      exact mul_nonneg hc0.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
    have hη2 : η ^ 2 = (N : ℝ) ^ (-(2 - 8 * ε)) := by
      simp only [η]; rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
    have hl' : 0 < v₀ * lowConst c₀ s₀ v₀ := by positivity
    have hy2 : η ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hη.le hyη 2
    -- time error
    have hextra : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / y ^ 2 ≤ C₂ * γ := by
      have hsT : Real.sqrt T ≤ 1 := Real.sqrt_le_one.2 hT1
      have hopB : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤
          K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio) := by
        refine hmod.trans (div_le_div_of_nonneg_right ?_ (by linarith))
        calc K₁ * Real.sqrt T * chainRatio ^ m ≤ K₁ * 1 * chainRatio ^ m := by gcongr
          _ ≤ K₁ * (N : ℝ) ^ (-(p : ℝ)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hqm hK₁.le
      have hpow : (N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2 ≤ 1 := by
        rw [hη2, div_le_one (by positivity), ← Real.rpow_add hNp]
        exact hrpow_mono (by linarith)
      have hop0 := opB_nonneg (flowMatrix F a ω σ - flowMatrix F a ω (tk k))
      calc opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / y ^ 2
          ≤ opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / η ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hop0 hnn) (by positivity) hy2
        _ ≤ (K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio)) *
              ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) / η ^ 2 := by
            gcongr
        _ = C₂ * γ * ((N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2) := by
            simp only [C₂]; field_simp
        _ ≤ C₂ * γ * 1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₂ hγ)
        _ = C₂ * γ := mul_one _
    -- energy/height error
    have hzdist : ‖(⟨x, h⟩ : ℂ) - ⟨xj, y⟩‖ ≤ 2 * ρ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.sub_im]
      rw [abs_of_nonneg (by linarith : 0 ≤ h - y)]
      linarith [hxxj]
    have hlip : ‖(⟨x, h⟩ : ℂ) - ⟨xj, y⟩‖ * nsq q / (h * y) ≤ C₃ * γ := by
      have hhy2 : η ^ 2 ≤ h * y := by nlinarith
      have hpow : (N : ℝ) ^ (-(p₂ : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2 ≤ 1 := by
        rw [hη2, div_le_one (by positivity), ← Real.rpow_add hNp]
        exact hrpow_mono (by linarith)
      calc ‖(⟨x, h⟩ : ℂ) - ⟨xj, y⟩‖ * nsq q / (h * y)
          ≤ (2 * ρ) * nsq q / η ^ 2 := by
            refine div_le_div₀ (mul_nonneg (by positivity) hnn)
              (mul_le_mul_of_nonneg_right hzdist hnn) (by positivity) hhy2
        _ ≤ (2 * ρ) * ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) / η ^ 2 := by
            gcongr
        _ = C₃ * γ * ((N : ℝ) ^ (-(p₂ : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2) := by
            simp only [C₃, ρ]; field_simp
        _ ≤ C₃ * γ * 1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₃ hγ)
        _ = C₃ * γ := mul_one _
    -- the loss factor at height `y ≥ η`
    have hfac : 1 + (N : ℝ) ^ ε / Real.sqrt (Real.pi * v₀ * N * y) ≤
        1 + 1 / Real.sqrt (Real.pi * v₀) := by
      have hspv : 0 < Real.sqrt (Real.pi * v₀) := Real.sqrt_pos.2 (by positivity)
      have hNy : (N : ℝ) ^ (4 * ε) ≤ (N : ℝ) * y := by
        rw [← hNη]; exact mul_le_mul_of_nonneg_left hyη hNp.le
      have hsq2 : Real.sqrt (Real.pi * v₀) * (N : ℝ) ^ (2 * ε) ≤
          Real.sqrt (Real.pi * v₀ * N * y) := by
        have e : Real.sqrt (Real.pi * v₀ * N * y) =
            Real.sqrt (Real.pi * v₀) * Real.sqrt ((N : ℝ) * y) := by
          rw [mul_assoc (Real.pi * v₀) (N : ℝ) y,
            Real.sqrt_mul (x := Real.pi * v₀) (by positivity) ((N : ℝ) * y)]
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ hspv.le
        rw [show (N : ℝ) ^ (2 * ε) = Real.sqrt ((N : ℝ) ^ (4 * ε)) by
          rw [show (N : ℝ) ^ (4 * ε) = ((N : ℝ) ^ (2 * ε)) ^ 2 by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num; ring_nf,
            Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt hNy
      have : (N : ℝ) ^ ε / Real.sqrt (Real.pi * v₀ * N * y) ≤ 1 / Real.sqrt (Real.pi * v₀) := by
        rw [div_le_div_iff₀ (lt_of_lt_of_le (by positivity) hsq2) hspv]
        have hε2 : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (2 * ε) := hrpow_mono (by linarith)
        nlinarith
      linarith
    have hKc' : 0 ≤ gammaCompConst c₀ r₀ s₀ v₀ * γ := mul_nonneg hKc hγ
    have h3' := h3.trans (mul_le_mul_of_nonneg_right hfac hKc')
    calc (star q ⬝ᵥ ((flowMatrix F a ω σ - (⟨x, h⟩ : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im
        ≤ (1 + 1 / Real.sqrt (Real.pi * v₀)) * (gammaCompConst c₀ r₀ s₀ v₀ * γ) + C₂ * γ +
            C₃ * γ := by
          have hy2' : (⟨xj, y⟩ : ℂ).im ^ 2 = y ^ 2 := rfl
          have hhy' : (⟨x, h⟩ : ℂ).im * (⟨xj, y⟩ : ℂ).im = h * y := rfl
          rw [hy2'] at h2; rw [hhy'] at h1
          linarith
      _ = ((1 + 1 / Real.sqrt (Real.pi * v₀)) * gammaCompConst c₀ r₀ s₀ v₀ + C₂ + C₃) * γ := by
          ring

end BlockBand.Palm.MomentFlow
