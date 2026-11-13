module

public import BlockBand.Palm.MomentFlow.AvgLineDet
public import BlockBand.Palm.MomentFlow.EventHeight

/-!
# The averaged (scalar) local law along the flow at all heights, energies and times

**`averaged_uniform`** (hypotheses `ExternalLocalGUE`, `MDEBranchIdentification`,
`GaussianLpGradient`): fixed `A`, `FreshConstants c₀ r₀ s₀ v₀`, `0 < ε < 1/4`; a constant `Cst`
(regularity constants and the chaining constant only); for every `D` an `N₀`; for `N ≥ N₀`, every
`F` in the fresh class, `a ≥ 0`, `0 < T ≤ 1`, `[a, a+T] ⊆ [c₀ - s₀, c₀]`: outside a measurable set
of `flowLaw N a`-probability `≤ N^{-D}`, for all `σ ∈ [a, a+T]`, `|x - E| ≤ r₀/2`,
`N^{-1+4ε} ≤ h ≤ 1`:
`|⟨(H_σ - x - ih)⁻¹⟩ - m_σ(x + ih)| ≤ Cst N^ε/(Nh)`, `m_σ = freshDyson F σ`.
(Hermitian `ω.1` only.)

Proof: the external averaged local law (`B = 1`, `averagedControl_one_le`) on an energy/height mesh
of spacing `N^{-4}` and a dyadic time mesh (as `isotropic_upper_uniform`); between mesh points the
trace is Lipschitz in `z` (`normalizedTrace_resolvent_lipschitz`) and in the matrix
(`normalizedTrace_resolvent_compare` with the chaining modulus), and `m_σ(z)` is Lipschitz in
`(σ, z)` uniformly in the height (`freshDyson_window_lipschitz`).
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

theorem measurableSet_avgBad_flow (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ)
    (M B : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) (thr : ℝ) :
    MeasurableSet {ω : FlowSample N | thr <
      ‖CEH.normalizedTrace (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *
        B)‖} := by
  have hm : Measurable (fun ω : FlowSample N => flowMatrix F a ω σ - F) := by
    have := measurable_matrix_sub.comp ((measurable_flowMatrix F a σ).prodMk
      (measurable_const (a := F)))
    simpa only [Function.comp_def] using this
  have e : {ω : FlowSample N | thr <
      ‖CEH.normalizedTrace (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *
        B)‖} = (fun ω => flowMatrix F a ω σ - F) ⁻¹' avgBadSet F M B z thr := by
    ext ω; simp only [avgBadSet, Set.mem_preimage, Set.mem_ofPred_eq, add_sub_cancel]
  rw [e]
  exact hm (measurableSet_avgBadSet F M B z thr)

/-- `⟨(G - M)·1⟩ = ⟨G⟩ - m` for `M = freshM` with a positive Dyson root. -/
theorem normalizedTrace_sub_freshM (G : Matrix (Fin N) (Fin N) ℂ) {F : Matrix (Fin N) (Fin N) ℂ}
    {σ : ℝ} {z : ℂ} (hm : 0 < (freshDyson F σ z).im) :
    CEH.normalizedTrace ((G - freshM F σ z) * 1) =
      CEH.normalizedTrace G - freshDyson F σ z := by
  rw [Matrix.mul_one, ← freshM_normalizedTrace hm]
  unfold CEH.normalizedTrace
  rw [Matrix.trace_sub, mul_sub]

set_option maxHeartbeats 1600000 in
/-- **Averaged local law at all heights, energies and times.** -/
theorem averaged_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ a T : ℝ, 0 ≤ a → 0 < T → T ≤ 1 → c₀ - s₀ ≤ a → a + T ≤ c₀ →
      ∃ Bad : Set (FlowSample N), MeasurableSet Bad ∧
        flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ σ ∈ Icc a (a + T), ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
          ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
            ‖CEH.normalizedTrace ((flowMatrix F a ω σ - (⟨x, h⟩ : ℂ) •
              (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) - freshDyson F σ ⟨x, h⟩‖ ≤
              Cst * (N : ℝ) ^ ε / ((N : ℝ) * h) := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  obtain ⟨K₁, hK₁, hchain⟩ := chain_event hLp
  have hcs : 0 < c₀ - s₀ := by linarith
  have hq0 := chainRatio_pos
  have hq1 := chainRatio_lt_one
  set C₂ : ℝ := K₁ / (1 - chainRatio)
  have hC₂ : 0 ≤ C₂ := div_nonneg hK₁.le (by linarith)
  set L : ℝ := dysonLipConst c₀ s₀ v₀
  have hL : 0 ≤ L := dysonLipConst_nonneg c₀ s₀ v₀
  set C₄ : ℝ := L * (2 + 1 / Real.sqrt (c₀ - s₀))
  have hC₄ : 0 ≤ C₄ := by positivity
  refine ⟨3 + C₂ + C₄, by positivity, fun D => ?_⟩
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  set κ := max A 0 + 1
  obtain ⟨p, hp4⟩ : ∃ p : ℕ, p = 4 := ⟨_, rfl⟩
  set D' := max D 0 + 4 * p + 2 * p + 4
  have hD' : 0 < D' := by positivity
  obtain ⟨N₁, hN₁, hloc⟩ := flowLaw_averagedBad_le hELG κ ρ0⁻¹ ε ε D' hε hε hD'
  have h14 : 0 < 1 - 4 * ε := by linarith
  set k₀ : ℕ := ⌈max D 0⌉₊
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k₀ (by norm_num)
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ 8 ≤ n) ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 - 4 * ε)) ≤ min 1 (r₀ / 2) ∧ Real.pi / v₀ ≤ (n : ℝ) ^ (3 * ε) ∧
      (2 + 2 / v₀ + r₀) / ρ0 ≤ (n : ℝ) ∧ r₀ + 2 ≤ (n : ℝ) ∧ 2 / r₀ ≤ (n : ℝ) ∧
      (2 : ℝ) ^ (4 * p + 1) ≤ (n : ℝ) ^ (2 : ℝ) ∧ (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop 8)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 1).and
      ((eventually_rpow_le h14 (lt_min one_pos (by linarith))).and
      ((eventually_rpow_ge (by linarith) _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((eventually_rpow_ge (by norm_num) _).and
      ((hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
        fun _ h => h.le))))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC a T ha hT hT1 haT hTc => ?_⟩
  obtain ⟨⟨hNN₁, hN8⟩, hN1, hηsmall, hdens, hnormN, hcardN, hρr0, h2p, hexpN⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hNpos : 0 < N := by exact_mod_cast hNp
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hrpow_mono : ∀ {p r : ℝ}, p ≤ r → (N : ℝ) ^ p ≤ (N : ℝ) ^ r := fun h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  set η : ℝ := (N : ℝ) ^ (-(1 - 4 * ε))
  have hη : 0 < η := Real.rpow_pos_of_pos hNp _
  have hη1 : η ≤ 1 := hηsmall.trans (min_le_left _ _)
  have hNη : (N : ℝ) * η = (N : ℝ) ^ (4 * ε) := by
    simp only [η]
    rw [← Real.rpow_one_add' hNp.le (by linarith)]
    congr 1; ring
  have hηN : 1 / (N : ℝ) ≤ η := by
    have : (N : ℝ) ^ (-(1 : ℝ)) ≤ η := hrpow_mono (by linarith)
    rwa [Real.rpow_neg_one, ← one_div] at this
  set ρ : ℝ := (N : ℝ) ^ (-(p : ℝ))
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hNp _
  have hρeq : ρ = 1 / (N : ℝ) ^ 4 := by
    simp only [ρ]; rw [hp4, Real.rpow_neg hNp.le, one_div]; norm_cast
  have hN4 : (N : ℝ) ^ 1 * 2 ≤ (N : ℝ) ^ 4 := by
    have : (2 : ℝ) ≤ (N : ℝ) ^ 3 := le_trans hN2 (by nlinarith)
    nlinarith
  have hρN2 : ρ * (N : ℝ) ^ 2 ≤ 1 / (2 * N) := by
    rw [hρeq, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hρN : ρ ≤ 1 / (2 * N) := by
    rw [hρeq, one_div_le_one_div (by positivity) (by positivity)]; nlinarith
  have hρ1N : ρ ≤ 1 / N := hρN.trans (one_div_le_one_div_of_le hNp (by linarith))
  have hρη : ρ ≤ η / 2 := by
    calc ρ ≤ 1 / (2 * N) := hρN
      _ = (1 / N) / 2 := by ring
      _ ≤ η / 2 := by linarith
  have hρr : ρ ≤ r₀ / 2 := by
    refine hρ1N.trans ?_
    rw [div_le_iff₀ hNp]
    have := (div_le_iff₀ hr0).1 hρr0
    linarith
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
      flowLaw N a {ω | (N : ℝ) ^ ε * CEH.averagedControl (freshM F (tk k) ⟨x, y⟩) 1 ⟨x, y⟩ <
        ‖CEH.normalizedTrace (((flowMatrix F a ω (tk k) - (⟨x, y⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F (tk k) ⟨x, y⟩) * 1)‖} ≤
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
        have hρN' : 2 + 2 / v₀ + r₀ ≤ ρ0 * N := by
          rw [div_le_iff₀ hρ0] at hnormN; linarith
        calc ‖(⟨x, y⟩ : ℂ)‖ ≤ (N : ℝ) ^ A + 2 / v₀ + r₀ + 1 := hz
          _ ≤ (N : ℝ) ^ max A 0 * (2 + 2 / v₀ + r₀) := by
              have : 0 ≤ 2 / v₀ + r₀ + 1 := by positivity
              nlinarith
          _ ≤ (N : ℝ) ^ max A 0 * (ρ0 * N) := mul_le_mul_of_nonneg_left hρN' (by positivity)
          _ = ρ0 * ((N : ℝ) ^ max A 0 * N) := by ring
          _ ≤ Real.sqrt (tk k) * (N : ℝ) ^ (κ + 1 / ε) :=
              mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _)
    have him : 0 < (freshDyson F (tk k) ⟨x, y⟩).im :=
      lt_of_lt_of_le hv0 (fresh_regular_bounds hC.2.2 hσ hxw hy0.le hy1).1
    have hMeq := mdeBranch_matrix_eq_freshM hMDE hNpos hC.1 hσ0 (z := ⟨x, y⟩) hy0 him M
    have := hloc N hNN₁ a (tk k) ha haσ hσ0 F hC.1 hFn M ⟨x, y⟩ hdom 1
    rwa [hMeq] at this
  set badk : ℕ → ℝ → ℝ → Set (FlowSample N) := fun k x y => {ω | (N : ℝ) ^ ε *
      CEH.averagedControl (freshM F (tk k) ⟨x, y⟩) 1 ⟨x, y⟩ <
      ‖CEH.normalizedTrace (((flowMatrix F a ω (tk k) - (⟨x, y⟩ : ℂ) •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F (tk k) ⟨x, y⟩) * 1)‖}
  set Bad₁ : Set (FlowSample N) :=
    ⋃ k ∈ Finset.range (2 ^ m), ⋃ x ∈ energyGrid E r₀ ρ, ⋃ y ∈ heightGrid η ρ, badk k x y
  set Bad₂ : Set (FlowSample N) := {ω | ¬ ChainGood K₁ T ω.2}
  have hρN1 : (1 : ℝ) / ρ = (N : ℝ) ^ (p : ℝ) := by
    simp only [ρ]; rw [Real.rpow_neg hNp.le, one_div, inv_inv]
  refine ⟨Bad₁ ∪ Bad₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.union ?_ (measurableSet_not_chainGood K₁ T)
    refine Finset.measurableSet_biUnion _ fun k _ => Finset.measurableSet_biUnion _ fun x _ =>
      Finset.measurableSet_biUnion _ fun y _ => ?_
    exact measurableSet_avgBad_flow F a (tk k) _ 1 _ _
  · have h2k : (2 : ℝ) ^ kb ≤ 2 * N := by
      have hN2' : 1 < N := by omega
      have h3 : 2 ^ kb.pred < N := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN2'
      have hkb : 0 < kb := Nat.clog_pos (by norm_num) hN2'
      have h' : 2 ^ kb ≤ 2 * N := by
        have e : kb = kb.pred + 1 := (Nat.succ_pred_eq_of_pos hkb).symm
        rw [e, pow_succ]; omega
      exact_mod_cast h'
    have hNp2 : (N : ℝ) ^ (p : ℝ) * N = (N : ℝ) ^ ((p + 1 : ℕ) : ℝ) := by
      rw [show ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 by push_cast; ring, Real.rpow_add hNp,
        Real.rpow_one]
    have hone : (1 : ℝ) ≤ (N : ℝ) ^ (p : ℝ) := Real.one_le_rpow hN1 (Nat.cast_nonneg _)
    have hcardE : ((energyGrid E r₀ ρ).card : ℝ) ≤ (N : ℝ) ^ ((p + 1 : ℕ) : ℝ) := by
      have h1 := energyGrid_card_le (E := E) hρ hr0
      rw [div_eq_mul_one_div, hρN1] at h1
      rw [← hNp2]
      calc ((energyGrid E r₀ ρ).card : ℝ) ≤ r₀ * (N : ℝ) ^ (p : ℝ) + 2 := h1
        _ ≤ r₀ * (N : ℝ) ^ (p : ℝ) + 2 * (N : ℝ) ^ (p : ℝ) := by linarith
        _ = (r₀ + 2) * (N : ℝ) ^ (p : ℝ) := by ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (p : ℝ) :=
            mul_le_mul_of_nonneg_right hcardN (by positivity)
        _ = _ := by ring
    have hcardH : ((heightGrid η ρ).card : ℝ) ≤ (N : ℝ) ^ ((p + 1 : ℕ) : ℝ) := by
      have h1 := heightGrid_card_le hρ hη.le hη1
      rw [hρN1] at h1
      rw [← hNp2]
      have : (N : ℝ) ^ (p : ℝ) + 1 ≤ (N : ℝ) ^ (p : ℝ) * N := by nlinarith
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
      count_le3 hNp hN1 p p D htimes (by positivity) hcardE (by positivity) hcardH h2p
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
    have hyh2 : h / 2 ≤ y := by linarith
    obtain ⟨k, hk, hu1, hu2⟩ := dyadic_cell hT m (u := σ - a) (by linarith [hσ.1])
      (by linarith [hσ.2])
    obtain ⟨hσk, haσk⟩ := htk k hk
    have hσw : σ ∈ Icc (c₀ - s₀) c₀ := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hnot : ω ∉ badk k xj y := fun h' =>
      hω₁ (mem_biUnion (Finset.mem_range.2 hk) (mem_biUnion hxj (mem_biUnion hy h')))
    simp only [badk, Set.mem_ofPred_eq, not_lt] at hnot
    have hHσ := flowMatrix_isHermitian hC.1 a hH σ
    have hHk := flowMatrix_isHermitian hC.1 a hH (tk k)
    set z : ℂ := ⟨x, h⟩
    set zj : ℂ := ⟨xj, y⟩
    have hzdist : ‖z - zj‖ ≤ 2 * ρ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [z, zj, Complex.sub_re, Complex.sub_im]
      rw [abs_of_nonneg (by linarith : 0 ≤ h - y)]
      linarith [hxxj]
    have hyN : 1 / y ^ 2 ≤ (N : ℝ) ^ 2 := by
      have h1 : 1 / (N : ℝ) ≤ y := hηN.trans hyη
      rw [div_le_iff₀ (by positivity)]
      have h2 : (1 / (N : ℝ)) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      have : (N : ℝ) ^ 2 * (1 / (N : ℝ)) ^ 2 = 1 := by field_simp
      nlinarith
    have hNe1 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
    -- Lipschitz in `z`
    have hTA : ‖CEH.normalizedTrace ((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
        CEH.normalizedTrace ((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)‖ ≤
        1 / N := by
      refine (normalizedTrace_resolvent_lipschitz hNpos hHσ hy0 (z := z) (z' := zj) hyh
        le_rfl).trans ?_
      calc ‖z - zj‖ / y ^ 2 = ‖z - zj‖ * (1 / y ^ 2) := by ring
        _ ≤ (2 * ρ) * (N : ℝ) ^ 2 := mul_le_mul hzdist hyN (by positivity) (by positivity)
        _ = 2 * (ρ * (N : ℝ) ^ 2) := by ring
        _ ≤ 2 * (1 / (2 * N)) := by linarith
        _ = 1 / N := by field_simp
    -- time modulus
    have hmod : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤
        K₁ * Real.sqrt T * chainRatio ^ m / (1 - chainRatio) := by
      have e : flowMatrix F a ω σ - flowMatrix F a ω (tk k) =
          hermitianBrownian ω.2 (σ - a) - hermitianBrownian ω.2 ((k : ℝ) * T / 2 ^ m) := by
        have : tk k - a = (k : ℝ) * T / 2 ^ m := by simp only [tk]; ring
        simp only [flowMatrix]; rw [this]; abel
      rw [e]
      exact chainGood_modulus hK₁.le hT hω₂ m k hk hu1 hu2
    have hqm : chainRatio ^ m ≤ ρ := by
      have e : chainRatio ^ m = ((1 / 2 : ℝ) ^ kb) ^ p := by
        simp only [m]; rw [show 4 * p * kb = 4 * (kb * p) by ring, pow_mul, chainRatio_pow_four,
          pow_mul]
      rw [e]
      simp only [ρ]
      rw [Real.rpow_neg hNp.le, Real.rpow_natCast, ← inv_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have hle : (N : ℝ) ≤ 2 ^ kb := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
      rw [one_div, inv_pow]
      exact inv_anti₀ hNp hle
    have hopB : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤ C₂ * ρ := by
      refine hmod.trans ?_
      have hsT : Real.sqrt T ≤ 1 := Real.sqrt_le_one.2 hT1
      simp only [C₂]
      rw [div_mul_eq_mul_div]
      refine div_le_div_of_nonneg_right ?_ (by linarith)
      calc K₁ * Real.sqrt T * chainRatio ^ m ≤ K₁ * 1 * ρ := by gcongr
        _ = K₁ * ρ := by ring
    have hTB : ‖CEH.normalizedTrace ((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
        CEH.normalizedTrace ((flowMatrix F a ω (tk k) - zj •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)‖ ≤ C₂ / N := by
      refine (normalizedTrace_resolvent_compare hNpos hHσ hHk (z := zj) hy0).trans ?_
      have hop0 := opB_nonneg (flowMatrix F a ω σ - flowMatrix F a ω (tk k))
      calc opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) / zj.im ^ 2
          = opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * (1 / y ^ 2) := by
            simp only [zj]; ring
        _ ≤ (C₂ * ρ) * (N : ℝ) ^ 2 := mul_le_mul hopB hyN (by positivity) (by positivity)
        _ = C₂ * (ρ * (N : ℝ) ^ 2) := by ring
        _ ≤ C₂ * (1 / (2 * N)) := mul_le_mul_of_nonneg_left hρN2 hC₂
        _ ≤ C₂ * (1 / N) := mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le hNp (by linarith)) hC₂
        _ = C₂ / N := by ring
    -- the external averaged law at the mesh point
    have hmk : 0 < (freshDyson F (tk k) zj).im :=
      lt_of_lt_of_le hv0 (fresh_regular_bounds hC.2.2 hσk hxw hy0.le hy1).1
    have hTC : ‖CEH.normalizedTrace ((flowMatrix F a ω (tk k) - zj •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) - freshDyson F (tk k) zj‖ ≤
        2 * (N : ℝ) ^ ε / ((N : ℝ) * h) := by
      have e := normalizedTrace_sub_freshM ((flowMatrix F a ω (tk k) - zj •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) hmk
      rw [← e]
      refine hnot.trans ?_
      have hc := averagedControl_one_le hNpos (freshM F (tk k) zj) zj
      have hzi : |zj.im| = y := abs_of_pos hy0
      rw [hzi] at hc
      have hNe0 : 0 ≤ (N : ℝ) ^ ε := by positivity
      calc (N : ℝ) ^ ε * CEH.averagedControl (freshM F (tk k) zj) 1 zj
          ≤ (N : ℝ) ^ ε * (1 / ((N : ℝ) * y)) := mul_le_mul_of_nonneg_left hc hNe0
        _ ≤ (N : ℝ) ^ ε * (2 / ((N : ℝ) * h)) := by
            refine mul_le_mul_of_nonneg_left ?_ hNe0
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * (N : ℝ) ^ ε / ((N : ℝ) * h) := by ring
    -- Lipschitz bound for `m`
    have hσtk : |tk k - σ| ≤ 1 / N := by
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      have hlo : tk k ≤ σ := by simp only [tk]; linarith
      have hhi : σ - tk k ≤ T / 2 ^ m := by
        simp only [tk]
        have : ((k : ℝ) + 1) * T / 2 ^ m = (k : ℝ) * T / 2 ^ m + T / 2 ^ m := by ring
        linarith
      have h2m : (N : ℝ) ≤ 2 ^ m := by
        have hle : (N : ℝ) ≤ 2 ^ kb := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
        refine hle.trans (pow_le_pow_right₀ (by norm_num) ?_)
        simp only [m]; rw [hp4]; omega
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      refine hhi.trans ?_
      calc T / 2 ^ m ≤ 1 / 2 ^ m := div_le_div_of_nonneg_right hT1 h2.le
        _ ≤ 1 / N := one_div_le_one_div_of_le hNp h2m
    have hTD : ‖freshDyson F (tk k) zj - freshDyson F σ z‖ ≤ C₄ / N := by
      have hlip := freshDyson_window_lipschitz hNpos hK' hC hσk hσw (z := zj) (z' := z) hxw
        (by simp only [z]; linarith) hy0.le hy1 hh0.le hh1
      refine hlip.trans ?_
      have hsq : 0 < Real.sqrt (c₀ - s₀) := Real.sqrt_pos.2 hcs
      have h1 : ‖zj - z‖ ≤ 2 / N := by
        rw [norm_sub_rev]; refine hzdist.trans ?_
        have := hρ1N; rw [div_eq_mul_one_div 2]; linarith
      have h2 : |tk k - σ| / Real.sqrt (c₀ - s₀) ≤ (1 / N) / Real.sqrt (c₀ - s₀) :=
        div_le_div_of_nonneg_right hσtk hsq.le
      calc L * (‖zj - z‖ + |tk k - σ| / Real.sqrt (c₀ - s₀))
          ≤ L * (2 / N + (1 / N) / Real.sqrt (c₀ - s₀)) := by gcongr
        _ = C₄ / N := by simp only [C₄]; ring
    -- combination
    have hsplit : CEH.normalizedTrace ((flowMatrix F a ω σ - z •
        (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) - freshDyson F σ z =
        (CEH.normalizedTrace ((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
          CEH.normalizedTrace ((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)) +
        (CEH.normalizedTrace ((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) -
          CEH.normalizedTrace ((flowMatrix F a ω (tk k) - zj •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)) +
        (CEH.normalizedTrace ((flowMatrix F a ω (tk k) - zj •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) - freshDyson F (tk k) zj) +
        (freshDyson F (tk k) zj - freshDyson F σ z) := by ring
    have h1N : 1 / (N : ℝ) ≤ (N : ℝ) ^ ε / ((N : ℝ) * h) := by
      rw [div_le_div_iff₀ hNp (by positivity)]
      nlinarith
    have hC4N : C₄ / N = C₄ * (1 / N) := by ring
    have hC2N : C₂ / N = C₂ * (1 / N) := by ring
    rw [hsplit]
    refine norm_add₄_le.trans ?_
    have hA := mul_le_mul_of_nonneg_left h1N hC₂
    have hB := mul_le_mul_of_nonneg_left h1N hC₄
    have e : (3 + C₂ + C₄) * (N : ℝ) ^ ε / ((N : ℝ) * h) =
        (N : ℝ) ^ ε / ((N : ℝ) * h) + C₂ * ((N : ℝ) ^ ε / ((N : ℝ) * h)) +
          2 * (N : ℝ) ^ ε / ((N : ℝ) * h) + C₄ * ((N : ℝ) ^ ε / ((N : ℝ) * h)) := by ring
    rw [e]
    linarith [hTA, hTB, hTC, hTD]

end BlockBand.Palm.MomentFlow
