module

public import BlockBand.Palm.MomentFlow.AvgQuadLip
public import BlockBand.Palm.CoarseRelativeDyson

/-!
# The isotropic local law along the flow at all heights, energies and times

**`isotropic_accuracy_uniform`** (hypotheses `ExternalLocalGUE`, `MDEBranchIdentification`,
`GaussianLpGradient`): fixed `A`, `FreshConstants c₀ r₀ s₀ v₀`, `0 < ε < 1/4`; a constant `Cst`
(regularity constants and the chaining constant only); for every `D` an `N₀`; for `N ≥ N₀`, every
`F` in the fresh class, `a ≥ 0`, `0 < T ≤ 1`, `[a, a+T] ⊆ [c₀ - s₀, c₀]`, every `q`: outside a
measurable set of `flowLaw N a`-probability `≤ N^{-D}`, for all `σ ∈ [a, a+T]`, `|x - E| ≤ r₀/2`,
`N^{-1+4ε} ≤ h ≤ 1`:
`|q*((H_σ - x - ih)⁻¹ - M_σ(x + ih))q| ≤ Cst N^ε/√(Nh) · q*Γq`, `M_σ = freshM F σ`.
(Hermitian `ω.1` only.)

Proof: the external isotropic local law at every point of an energy/height mesh of spacing `N^{-p}`
and a dyadic time mesh, `p = ⌈2max(A,1)⌉ + 3`; control `isotropicControl_freshM_le` and
`quad_im_le_gamma`; between mesh points: `resolvent_quad_lipschitz` (in `z`),
`resolvent_quad_norm_compare` with the chaining modulus (in time) and `freshM_quad_lipschitz` (for
`q*Mq`); the factor `‖q‖²` is converted with `nsq_le_of_gamma` (`‖q‖² ≤ N^{2max(A,1)} q*Γq/(v₀
lowConst)`).
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

/-- `1/N ≤ N^ε/√(N h)` for `N ≥ 1`, `0 < h ≤ 1`, `ε ≥ 0`. -/
theorem one_div_le_rpow_div_sqrt {N : ℕ} (hN1 : (1 : ℝ) ≤ N) {ε h : ℝ} (hε : 0 ≤ ε)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    1 / (N : ℝ) ≤ (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) := by
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hs : 0 < Real.sqrt ((N : ℝ) * h) := Real.sqrt_pos.2 (by positivity)
  have hsN : Real.sqrt ((N : ℝ) * h) ≤ N := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε
  rw [div_le_div_iff₀ hNp hs]
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Isotropic accuracy line at all heights, energies and times.** -/
theorem isotropic_accuracy_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ a T : ℝ, 0 ≤ a → 0 < T → T ≤ 1 → c₀ - s₀ ≤ a → a + T ≤ c₀ →
      ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N), MeasurableSet Bad ∧
        flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ σ ∈ Icc a (a + T), ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
          ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
            ‖star q ⬝ᵥ (((flowMatrix F a ω σ - (⟨x, h⟩ : ℂ) •
              (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F σ ⟨x, h⟩) *ᵥ q)‖ ≤
              Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * quadForm (freshGamma F c₀ E) q := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  obtain ⟨K₁, hK₁, hchain⟩ := chain_event hLp
  have hcs : 0 < c₀ - s₀ := by linarith
  have hl : 0 < lowConst c₀ s₀ v₀ := by unfold lowConst; positivity
  have hq0 := chainRatio_pos
  have hq1 := chainRatio_lt_one
  have hl' : 0 < v₀ * lowConst c₀ s₀ v₀ := by positivity
  have hKc : 0 ≤ gammaCompConst c₀ r₀ s₀ v₀ := by
    unfold gammaCompConst; simp only
    have : 0 < (c₀ - s₀) * v₀ := mul_pos hcs hv0
    positivity
  have hQL : 0 ≤ quadLipConst c₀ s₀ v₀ := by
    unfold quadLipConst; exact div_nonneg (slowWConst_nonneg hK') (by positivity)
  have hpv : 0 < Real.sqrt (Real.pi * v₀ / 2) := Real.sqrt_pos.2 (by positivity)
  set C₁ : ℝ := gammaCompConst c₀ r₀ s₀ v₀ / Real.sqrt (Real.pi * v₀ / 2)
  have hC₁ : 0 ≤ C₁ := div_nonneg hKc hpv.le
  set C₂ : ℝ := K₁ / ((1 - chainRatio) * (v₀ * lowConst c₀ s₀ v₀))
  have hC₂ : 0 ≤ C₂ := div_nonneg hK₁.le (mul_nonneg (by linarith) (by positivity))
  set C₃ : ℝ := 2 / (v₀ * lowConst c₀ s₀ v₀)
  have hC₃ : 0 ≤ C₃ := by positivity
  set C₅ : ℝ := 3 * quadLipConst c₀ s₀ v₀ / (v₀ * lowConst c₀ s₀ v₀)
  have hC₅ : 0 ≤ C₅ := by positivity
  refine ⟨C₁ + C₂ + C₃ + C₅, by positivity, fun D => ?_⟩
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  set κ := max A 0 + 1
  set p : ℕ := ⌈2 * max A 1⌉₊ + 3
  have hp : 3 + 2 * max A 1 ≤ (p : ℝ) := by
    simp only [p]; push_cast; linarith [Nat.le_ceil (2 * max A 1)]
  have hp3 : (3 : ℝ) ≤ p := by
    have : (0 : ℝ) ≤ 2 * max A 1 := by have := le_max_right A 1; linarith
    linarith
  set D' := max D 0 + 4 * p + 2 * p + 4
  have hD' : 0 < D' := by positivity
  obtain ⟨N₁, hN₁, hloc⟩ := flowLaw_isotropicBad_freshM_le hELG hMDE κ ρ0⁻¹ ε ε D' hε hε hD'
  have h14 : 0 < 1 - 4 * ε := by linarith
  set k₀ : ℕ := ⌈max D 0⌉₊
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k₀ (by norm_num)
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ 8 ≤ n) ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 - 4 * ε)) ≤ min 1 (r₀ / 2) ∧ Real.pi / v₀ ≤ (n : ℝ) ^ (3 * ε) ∧
      (2 + 2 / v₀ + r₀) / ρ0 ≤ (n : ℝ) ∧ r₀ + 2 ≤ (n : ℝ) ∧
      (n : ℝ) ^ (-(p : ℝ)) ≤ r₀ / 2 ∧
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
  have hρ3 : ρ ≤ 1 / (N : ℝ) ^ 3 := by
    have : ρ ≤ (N : ℝ) ^ (-(3 : ℝ)) := hrpow_mono (by linarith)
    rwa [Real.rpow_neg hNp.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← one_div] at this
  have hρη : ρ ≤ η / 2 := by
    refine hρ3.trans ?_
    have h1 : 1 / (N : ℝ) ^ 3 ≤ 1 / (2 * N) := by
      rw [one_div_le_one_div (by positivity) (by positivity)]
      have h4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN2]
      nlinarith only [h4, hNp]
    have : 1 / (2 * (N : ℝ)) = (1 / N) / 2 := by ring
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
  have hρN : (1 : ℝ) / ρ = (N : ℝ) ^ (p : ℝ) := by
    simp only [ρ]; rw [Real.rpow_neg hNp.le, one_div, inv_inv]
  refine ⟨Bad₁ ∪ Bad₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.union ?_ (measurableSet_not_chainGood K₁ T)
    refine Finset.measurableSet_biUnion _ fun k _ => Finset.measurableSet_biUnion _ fun x _ =>
      Finset.measurableSet_biUnion _ fun y _ => ?_
    exact measurableSet_isoBad_flow F a (tk k) _ q _ _
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
      rw [div_eq_mul_one_div, hρN] at h1
      rw [← hNp2]
      calc ((energyGrid E r₀ ρ).card : ℝ) ≤ r₀ * (N : ℝ) ^ (p : ℝ) + 2 := h1
        _ ≤ r₀ * (N : ℝ) ^ (p : ℝ) + 2 * (N : ℝ) ^ (p : ℝ) := by linarith
        _ = (r₀ + 2) * (N : ℝ) ^ (p : ℝ) := by ring
        _ ≤ (N : ℝ) * (N : ℝ) ^ (p : ℝ) :=
            mul_le_mul_of_nonneg_right hcardN (by positivity)
        _ = _ := by ring
    have hcardH : ((heightGrid η ρ).card : ℝ) ≤ (N : ℝ) ^ ((p + 1 : ℕ) : ℝ) := by
      have h1 := heightGrid_card_le hρ hη.le hη1
      rw [hρN] at h1
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
    set γ := quadForm (freshGamma F c₀ E) q
    have hγ : 0 ≤ γ := by
      simp only [γ]; rw [freshGamma_quad_eq hC.1]
      exact mul_nonneg hc0.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
    have hnsq := nsq_le_of_gamma hNpos hK' hC q
    have hη2 : η ^ 2 = (N : ℝ) ^ (-(2 - 8 * ε)) := by
      simp only [η]; rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
    have hy2 : η ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hη.le hyη 2
    -- `N^{-p} N^{2max(A,1)}/η² ≤ 1/N`
    have hpow : (N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2 ≤ 1 / N := by
      rw [hη2, div_le_iff₀ (by positivity), ← Real.rpow_add hNp, one_div, ← Real.rpow_neg_one,
        ← Real.rpow_add hNp]
      exact hrpow_mono (by linarith)
    have hpow' : (N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) ≤ 1 / N := by
      have h1 : η ^ 2 ≤ 1 := pow_le_one₀ hη.le hη1
      have h0 : 0 ≤ (N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) := by positivity
      refine le_trans ?_ hpow
      rw [le_div_iff₀ (by positivity)]
      exact mul_le_of_le_one_right h0 h1
    have hnsqγ : ∀ c : ℝ, 0 ≤ c → c * nsq q ≤
        c * ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) := fun c hc =>
      mul_le_mul_of_nonneg_left hnsq hc
    -- Lipschitz in `z`
    have hzdist : ‖z - zj‖ ≤ 2 * ρ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [z, zj, Complex.sub_re, Complex.sub_im]
      rw [abs_of_nonneg (by linarith only [hyh] : 0 ≤ h - y)]
      linarith only [hxxj, hhy]
    have hTA : ‖star q ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q)‖ ≤ C₃ * γ / N := by
      refine (resolvent_quad_lipschitz hHσ hy0 (w := z) (w' := zj) hyh le_rfl q).trans ?_
      have hyi : y⁻¹ ^ 2 ≤ 1 / η ^ 2 := by
        rw [inv_pow, one_div]; exact inv_anti₀ (by positivity) hy2
      calc ‖z - zj‖ * y⁻¹ ^ 2 * nsq q ≤ (2 * ρ) * (1 / η ^ 2) * nsq q := by gcongr
        _ ≤ (2 * ρ) * (1 / η ^ 2) * ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) :=
            hnsqγ _ (by positivity)
        _ = C₃ * γ * ((N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2) := by
            simp only [C₃, ρ]; field_simp
        _ ≤ C₃ * γ * (1 / N) := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₃ hγ)
        _ = C₃ * γ / N := by ring
    -- time modulus
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
    have hTB : ‖star q ⬝ᵥ (((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        (flowMatrix F a ω (tk k) - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q)‖ ≤
        C₂ * γ / N := by
      refine (resolvent_quad_norm_compare hHσ hHk (z := zj) hy0 q).trans ?_
      have hsT : Real.sqrt T ≤ 1 := Real.sqrt_le_one.2 hT1
      have hopB : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤
          K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio) := by
        refine hmod.trans (div_le_div_of_nonneg_right ?_ (by linarith))
        calc K₁ * Real.sqrt T * chainRatio ^ m ≤ K₁ * 1 * chainRatio ^ m := by gcongr
          _ ≤ K₁ * (N : ℝ) ^ (-(p : ℝ)) := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hqm hK₁.le
      have hop0 := opB_nonneg (flowMatrix F a ω σ - flowMatrix F a ω (tk k))
      have hzi : zj.im = y := rfl
      rw [hzi]
      calc opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / y ^ 2
          ≤ opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / η ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hop0 hnn) (by positivity) hy2
        _ ≤ (K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio)) *
              ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) / η ^ 2 := by
            gcongr
        _ = C₂ * γ * ((N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2) := by
            simp only [C₂]; field_simp
        _ ≤ C₂ * γ * (1 / N) := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₂ hγ)
        _ = C₂ * γ / N := by ring
    -- the external isotropic law at the mesh point
    have hzjr : |zj.re - E| ≤ r₀ := hxw
    have hctrl := isotropicControl_freshM_le hK' hC hσk hzjr hy0 hy1 hNpos q
    have hgam := quad_im_le_gamma hNpos hK' hC hσk hzjr hy0.le hy1 q
    have hTC : ‖star q ⬝ᵥ (((flowMatrix F a ω (tk k) - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        freshM F (tk k) zj) *ᵥ q)‖ ≤ C₁ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by
      refine hnot.trans ?_
      have hNe0 : 0 ≤ (N : ℝ) ^ ε := by positivity
      have hsh : 0 < Real.sqrt ((N : ℝ) * h) := Real.sqrt_pos.2 (by positivity)
      have hsq : Real.sqrt (Real.pi * v₀ / 2) * Real.sqrt ((N : ℝ) * h) ≤
          Real.sqrt (Real.pi * v₀ * N * zj.im) := by
        rw [← Real.sqrt_mul (by positivity)]
        refine Real.sqrt_le_sqrt ?_
        have hzi : zj.im = y := rfl
        rw [hzi]
        have h0 : 0 ≤ Real.pi * v₀ * N := by positivity
        calc Real.pi * v₀ / 2 * ((N : ℝ) * h) = Real.pi * v₀ * N * (h / 2) := by ring
          _ ≤ Real.pi * v₀ * N * y := mul_le_mul_of_nonneg_left hyh2 h0
      have hai : 0 ≤ (star q ⬝ᵥ (freshM F (tk k) zj *ᵥ q)).im := by
        have hw : (freshW F (tk k) zj).im ≠ 0 := by
          rw [freshW_im]
          have hm1 := (fresh_regular_bounds hC.2.2 hσk hzjr hy0.le hy1).1
          have : 0 < tk k := by linarith [hσk.1]
          have : 0 < (freshDyson F (tk k) zj).im := lt_of_lt_of_le hv0 hm1
          have : 0 < zj.im := hy0
          positivity
        rw [freshM_quad_im hC.1 hw q]
        have hm1 := (fresh_regular_bounds hC.2.2 hσk hzjr hy0.le hy1).1
        have : 0 < tk k := by linarith [hσk.1]
        have : 0 ≤ (freshDyson F (tk k) zj).im := le_trans hv0.le hm1
        have : 0 ≤ zj.im := hy0.le
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
      calc (N : ℝ) ^ ε * CEH.isotropicControl (freshM F (tk k) zj) zj q q
          ≤ (N : ℝ) ^ ε * ((star q ⬝ᵥ (freshM F (tk k) zj *ᵥ q)).im /
              Real.sqrt (Real.pi * v₀ * N * zj.im)) := mul_le_mul_of_nonneg_left hctrl hNe0
        _ ≤ (N : ℝ) ^ ε * ((gammaCompConst c₀ r₀ s₀ v₀ * γ) /
              (Real.sqrt (Real.pi * v₀ / 2) * Real.sqrt ((N : ℝ) * h))) := by
            refine mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) hgam
              (by positivity) hsq) hNe0
        _ = C₁ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by
            simp only [C₁]; field_simp
    -- Lipschitz bound for `q*Mq`
    have hσtk : |tk k - σ| ≤ ρ := by
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      have hlo : tk k ≤ σ := by simp only [tk]; linarith only [hu1]
      have hhi : σ - tk k ≤ T / 2 ^ m := by
        simp only [tk]
        have : ((k : ℝ) + 1) * T / 2 ^ m = (k : ℝ) * T / 2 ^ m + T / 2 ^ m := by ring
        linarith only [this, hu2]
      have h2m : (N : ℝ) ^ (p : ℝ) ≤ 2 ^ m := by
        have hle : (N : ℝ) ≤ 2 ^ kb := by exact_mod_cast Nat.le_pow_clog (by norm_num) N
        rw [Real.rpow_natCast]
        refine (pow_le_pow_left₀ hNp.le hle p).trans ?_
        rw [← pow_mul]
        refine pow_le_pow_right₀ (by norm_num) ?_
        simp only [m]
        rw [show 4 * p * kb = 4 * (kb * p) by ring]
        exact Nat.le_mul_of_pos_left (kb * p) (by norm_num)
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hlo])]
      refine hhi.trans ?_
      calc T / 2 ^ m ≤ 1 / 2 ^ m := div_le_div_of_nonneg_right hT1 h2.le
        _ ≤ 1 / (N : ℝ) ^ (p : ℝ) := one_div_le_one_div_of_le (by positivity) h2m
        _ = ρ := by simp only [ρ]; rw [Real.rpow_neg hNp.le, one_div]
    have hTD : ‖star q ⬝ᵥ (freshM F (tk k) zj *ᵥ q) - star q ⬝ᵥ (freshM F σ z *ᵥ q)‖ ≤
        C₅ * γ / N := by
      have hzr : |z.re - E| ≤ r₀ := by simp only [z]; linarith only [hx, hr0]
      refine (freshM_quad_lipschitz hNpos hK' hC hσk hσw hzjr hzr hy0.le hy1 hh0.le hh1 q).trans ?_
      have hd : ‖zj - z‖ + |tk k - σ| ≤ 3 * ρ := by
        rw [norm_sub_rev]; linarith only [hzdist, hσtk]
      calc quadLipConst c₀ s₀ v₀ * (‖zj - z‖ + |tk k - σ|) * nsq q
          ≤ quadLipConst c₀ s₀ v₀ * (3 * ρ) *
              ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hd hQL) hnsq hnn (by positivity)
        _ = C₅ * γ * ((N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1)) := by
            simp only [C₅, ρ]; field_simp
        _ ≤ C₅ * γ * (1 / N) := mul_le_mul_of_nonneg_left hpow' (mul_nonneg hC₅ hγ)
        _ = C₅ * γ / N := by ring
    -- combination
    have hsplit : star q ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        freshM F σ z) *ᵥ q) =
        star q ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          (flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q) +
        star q ⬝ᵥ (((flowMatrix F a ω σ - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          (flowMatrix F a ω (tk k) - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹) *ᵥ q) +
        star q ⬝ᵥ (((flowMatrix F a ω (tk k) - zj • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
          freshM F (tk k) zj) *ᵥ q) +
        (star q ⬝ᵥ (freshM F (tk k) zj *ᵥ q) - star q ⬝ᵥ (freshM F σ z *ᵥ q)) := by
      simp only [Matrix.sub_mulVec, dotProduct_sub]; ring
    have h1N := one_div_le_rpow_div_sqrt hN1 hε.le hh0 hh1
    rw [hsplit]
    refine norm_add₄_le.trans ?_
    have hA : C₃ * γ / N ≤ C₃ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by
      have := mul_le_mul_of_nonneg_left h1N (mul_nonneg hC₃ hγ)
      calc C₃ * γ / N = C₃ * γ * (1 / N) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have hB : C₂ * γ / N ≤ C₂ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by
      have := mul_le_mul_of_nonneg_left h1N (mul_nonneg hC₂ hγ)
      calc C₂ * γ / N = C₂ * γ * (1 / N) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have hD5 : C₅ * γ / N ≤ C₅ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by
      have := mul_le_mul_of_nonneg_left h1N (mul_nonneg hC₅ hγ)
      calc C₅ * γ / N = C₅ * γ * (1 / N) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have e : (C₁ + C₂ + C₃ + C₅) * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ =
        C₃ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ +
        C₂ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ +
        C₁ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ +
        C₅ * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * h) * γ := by ring
    rw [e]
    linarith only [hTA, hTB, hTC, hTD, hA, hB, hD5]

end BlockBand.Palm.MomentFlow
