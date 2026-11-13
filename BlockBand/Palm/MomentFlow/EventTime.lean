module

public import BlockBand.Palm.MomentFlow.EventTimeDet
public import BlockBand.Palm.MomentFlow.EventOverlap
public import BlockBand.Palm.MomentFlow.EventDisintegrate

/-!
# The overlap bound, uniformly in time, and its conditional form

Proof: energy grid of spacing `η = N^{-1+4ε}`, dyadic time grid of level `m = 4p⌈log₂ N⌉`
(`p ≥ 2 + 2max(A,1)`), the external isotropic local law at every grid point (union bound), and
between grid times
the resolvent comparison `resolvent_quad_im_compare` with the chaining modulus
`chainGood_modulus` (`‖B(u) - B(u_k)‖ ≤ K₁ 2^{-m/4}/(1-2^{-1/4})`), the `‖q‖² ≲ N^{2max(A,1)} q*Γq`
conversion `nsq_le_of_gamma`.

**`overlap_event_conditional`**: the conditional form, by disintegration over `𝓛`: an
`𝓛 = pathSigma`-measurable set of probability `≤ N^{-D}` off which `P(Bad | 𝓛) < N^{-D}`.
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

theorem measurableSet_isoBad_flow (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ)
    (M : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (z : ℂ) (thr : ℝ) :
    MeasurableSet {ω : FlowSample N | thr <
      ‖star q ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *ᵥ q)‖} := by
  have hm : Measurable (fun ω : FlowSample N => flowMatrix F a ω σ - F) := by
    have := measurable_matrix_sub.comp ((measurable_flowMatrix F a σ).prodMk
      (measurable_const (a := F)))
    simpa only [Function.comp_def] using this
  have e : {ω : FlowSample N | thr <
      ‖star q ⬝ᵥ (((flowMatrix F a ω σ - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - M) *ᵥ q)‖} =
      (fun ω => flowMatrix F a ω σ - F) ⁻¹' isoBadSet F M q q z thr := by
    ext ω; simp only [isoBadSet, Set.mem_preimage, Set.mem_ofPred_eq, add_sub_cancel]
  rw [e]
  exact hm (measurableSet_isoBadSet F M q q z thr)

theorem measurableSet_not_chainGood (K₁ T : ℝ) :
    MeasurableSet {ω : FlowSample N | ¬ ChainGood K₁ T ω.2} := by
  have e : {ω : FlowSample N | ChainGood K₁ T ω.2} = ⋂ n : ℕ, ⋂ k : ℕ, ⋂ (_ : k < 2 ^ n),
      {ω : FlowSample N | opB (hermitianBrownian ω.2 (((k : ℝ) + 1) * T / 2 ^ n) -
        hermitianBrownian ω.2 ((k : ℝ) * T / 2 ^ n)) ≤ K₁ * Real.sqrt T * chainRatio ^ n} := by
    ext ω; simp [ChainGood]
  have hm : MeasurableSet {ω : FlowSample N | ChainGood K₁ T ω.2} := by
    rw [e]
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le (continuous_opB.measurable.comp (measurable_matrix_sub.comp
      (((measurable_hermitianBrownian _).comp measurable_snd).prodMk
        ((measurable_hermitianBrownian _).comp measurable_snd)))) measurable_const
  exact hm.compl

theorem count_le {N : ℕ} (hNp : (0 : ℝ) < N) (hN1 : (1 : ℝ) ≤ N) (p : ℕ) (D : ℝ) {T₂ G : ℝ}
    (hT₂ : T₂ ≤ 2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ)) (hG0 : 0 ≤ G)
    (hG : G ≤ (N : ℝ) ^ (2 : ℝ)) (h2p : (2 : ℝ) ^ (4 * p + 1) ≤ (N : ℝ) ^ (2 : ℝ)) :
    T₂ * G * (N : ℝ) ^ (-(max D 0 + 4 * p + 4)) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hpos : 0 < (N : ℝ) ^ (-(max D 0 + 4 * p + 4)) := Real.rpow_pos_of_pos hNp _
  have hN2 : (N : ℝ) ^ ((4 * p : ℕ) : ℝ) * (N : ℝ) ^ (2 : ℝ) *
      (N : ℝ) ^ (-(max D 0 + 4 * p + 4)) = (N : ℝ) ^ (-(max D 0)) / (N : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_sub hNp]; congr 1; push_cast; ring
  have hmD : (N : ℝ) ^ (-(max D 0)) ≤ (N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_max_left D 0])
  have hN2pos : 0 < (N : ℝ) ^ (2 : ℝ) := by positivity
  have h1 : T₂ * G * (N : ℝ) ^ (-(max D 0 + 4 * p + 4)) ≤
      2 ^ (4 * p) * ((N : ℝ) ^ ((4 * p : ℕ) : ℝ) * (N : ℝ) ^ (2 : ℝ) *
        (N : ℝ) ^ (-(max D 0 + 4 * p + 4))) := by
    calc T₂ * G * (N : ℝ) ^ (-(max D 0 + 4 * p + 4))
        ≤ (2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ)) * (N : ℝ) ^ (2 : ℝ) *
            (N : ℝ) ^ (-(max D 0 + 4 * p + 4)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hT₂ hG hG0 (by positivity)) hpos.le
      _ = _ := by ring
  rw [hN2] at h1
  have h2 : (2 : ℝ) ^ (4 * p) * ((N : ℝ) ^ (-(max D 0)) / (N : ℝ) ^ (2 : ℝ)) ≤
      (N : ℝ) ^ (-(max D 0)) / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ hN2pos (by norm_num)]
    have h2p' : (2 : ℝ) ^ (4 * p) * 2 ≤ (N : ℝ) ^ (2 : ℝ) := by rw [← pow_succ]; exact h2p
    have h0 : 0 ≤ (N : ℝ) ^ (-(max D 0)) := by positivity
    calc (2 : ℝ) ^ (4 * p) * (N : ℝ) ^ (-(max D 0)) * 2
        = (N : ℝ) ^ (-(max D 0)) * ((2 : ℝ) ^ (4 * p) * 2) := by ring
      _ ≤ (N : ℝ) ^ (-(max D 0)) * (N : ℝ) ^ (2 : ℝ) := mul_le_mul_of_nonneg_left h2p' h0
  linarith

theorem chain_small {N : ℕ} (hNp : (0 : ℝ) < N) (hN1 : (1 : ℝ) ≤ N) {D : ℝ} {k₀ : ℕ}
    (hk : D ≤ k₀) (hexpN : (N : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ N ≤ 1 / 4) :
    2 * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) / 2 := by
  have hkD : (N : ℝ) ^ D ≤ (N : ℝ) ^ k₀ := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hN1 hk
  have hpos : 0 < (N : ℝ) ^ D := by positivity
  have h12 : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
  have h : (N : ℝ) ^ D * (1 / 2 : ℝ) ^ N ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hkD h12).trans hexpN
  have hinv : (N : ℝ) ^ (-D) = ((N : ℝ) ^ D)⁻¹ := by rw [Real.rpow_neg hNp.le]
  rw [hinv, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have h4 : 2 * (1 / 2 : ℝ) ^ N * 2 * (N : ℝ) ^ D ≤ 1 := by nlinarith
  calc 2 * (1 / 2 : ℝ) ^ N * 2 = (2 * (1 / 2 : ℝ) ^ N * 2 * (N : ℝ) ^ D) * ((N : ℝ) ^ D)⁻¹ := by
        field_simp
    _ ≤ 1 * ((N : ℝ) ^ D)⁻¹ := mul_le_mul_of_nonneg_right h4 (inv_nonneg.2 hpos.le)
    _ = ((N : ℝ) ^ D)⁻¹ := one_mul _

set_option maxHeartbeats 1000000 in
/-- **Overlap bound, uniformly in time.** -/
theorem overlap_event_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ a T : ℝ, 0 ≤ a → 0 < T → T ≤ 1 → c₀ - s₀ ≤ a → a + T ≤ c₀ →
      ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N), MeasurableSet Bad ∧
        flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ Bad, ω.1.IsHermitian → ∀ σ ∈ Icc a (a + T),
          HasSimpleSpectrum N (flowMatrix F a ω σ) →
          ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 2 →
            flowOverlap F a q σ i ω ≤ Cst * (N : ℝ) ^ (4 * ε) * quadForm (freshGamma F c₀ E) q := by
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
  refine ⟨overlapConst c₀ r₀ s₀ v₀ + 2 * C₂, ?_, fun D => ?_⟩
  · unfold overlapConst; positivity
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  set κ := max A 0 + 1
  set p : ℕ := ⌈2 * max A 1⌉₊ + 2
  have hp : 2 + 2 * max A 1 ≤ (p : ℝ) := by
    simp only [p]; push_cast; linarith [Nat.le_ceil (2 * max A 1)]
  set D' := max D 0 + 4 * p + 4
  have hD' : 0 < D' := by positivity
  obtain ⟨N₁, hN₁, hloc⟩ := flowLaw_isotropicBad_freshM_le hELG hMDE κ ρ0⁻¹ ε ε D' hε hε hD'
  have h14 : 0 < 1 - 4 * ε := by linarith
  set k₀ : ℕ := ⌈max D 0⌉₊
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one k₀ (by norm_num)
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ 8 ≤ n) ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 - 4 * ε)) ≤ min 1 (r₀ / 2) ∧ Real.pi / v₀ ≤ (n : ℝ) ^ (3 * ε) ∧
      (2 + 2 / v₀ + r₀) / ρ0 ≤ (n : ℝ) ∧ r₀ + 2 ≤ (n : ℝ) ∧
      (2 : ℝ) ^ (4 * p + 1) ≤ (n : ℝ) ^ (2 : ℝ) ∧ (n : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ n ≤ 1 / 4 := by
    refine ((eventually_ge_atTop N₁).and (eventually_ge_atTop 8)).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 1).and
      ((eventually_rpow_le h14 (lt_min one_pos (by linarith))).and
      ((eventually_rpow_ge (by linarith) _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      ((eventually_rpow_ge (by norm_num) _).and
      ((hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
        fun _ h => h.le)))))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC a T ha hT hT1 haT hTc q => ?_⟩
  obtain ⟨⟨hNN₁, hN8⟩, hN1, hηsmall, hdens, hnormN, hcardN, h2p, hexpN⟩ := hN₀ N hN
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
  -- one CEH branch per grid time
  have hbranch : ∀ k : ℕ, k < 2 ^ m →
      Nonempty (CEH.MDEBranch (Real.sqrt (tk k)) ⟨F, hC.1⟩) := fun k hk =>
    exists_mdeBranch_eq_freshM hMDE hNpos hC.1 (by linarith [(htk k hk).1.1])
  -- the grid-point estimates
  have hpt : ∀ k : ℕ, k < 2 ^ m → ∀ x ∈ energyGrid E r₀ η,
      flowLaw N a {ω | (N : ℝ) ^ ε * CEH.isotropicControl (freshM F (tk k) ⟨x, η⟩) ⟨x, η⟩ q q <
        ‖star q ⬝ᵥ (((flowMatrix F a ω (tk k) - (⟨x, η⟩ : ℂ) •
          (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ - freshM F (tk k) ⟨x, η⟩) *ᵥ q)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D')) := by
    intro k hk x hx
    obtain ⟨hσ, haσ⟩ := htk k hk
    have hσ0 : 0 < tk k := by linarith [hσ.1]
    obtain ⟨M⟩ := hbranch k hk
    have hxw := energyGrid_window hη hηr hr0 hx
    have hFn : (Real.sqrt (tk k))⁻¹ * ‖F‖ ≤ ρ0⁻¹ * (N : ℝ) ^ κ :=
      (cehNormBound_uniform hC.2.1 hcs hσ.1).trans
        (mul_le_mul_of_nonneg_left (hrpow_mono (by simp only [κ]; linarith [le_max_left A 0]))
          (by positivity))
    have hdom : CEH.InLocalLawDomain M κ ε ⟨x, η⟩ := by
      refine inLocalLawDomain_of_bulk hMDE hNpos hK' hC hσ hxw hη hη1 M ?_ ?_
      · show (N : ℝ) ^ ε ≤ (N : ℝ) * η * (v₀ / Real.pi)
        rw [hNη]
        have e : (N : ℝ) ^ (4 * ε) = (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) := by
          rw [← Real.rpow_add hNp]; ring_nf
        rw [e]
        have hNe : 0 ≤ (N : ℝ) ^ ε := by positivity
        have : (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) = (N : ℝ) ^ ε := by field_simp
        calc (N : ℝ) ^ ε = (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) := this.symm
          _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) * (v₀ / Real.pi) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdens hNe) (by positivity)
      · have hz := norm_z_le hNpos hK' hC (z := ⟨x, η⟩) hxw hη.le hη1
        have hsq : ρ0 ≤ Real.sqrt (tk k) := Real.sqrt_le_sqrt hσ.1
        have hm1 : (1 : ℝ) ≤ (N : ℝ) ^ max A 0 := Real.one_le_rpow hN1 (le_max_right _ _)
        have hpow : (N : ℝ) ^ max A 0 * N ≤ (N : ℝ) ^ (κ + 1 / ε) := by
          have : (N : ℝ) ^ max A 0 * N = (N : ℝ) ^ (max A 0 + 1) := by
            rw [Real.rpow_add hNp, Real.rpow_one]
          rw [this]; exact hrpow_mono (by simp only [κ]; have := one_div_pos.2 hε; linarith)
        have hmA : (N : ℝ) ^ A ≤ (N : ℝ) ^ max A 0 := hrpow_mono (le_max_left _ _)
        have hρN : 2 + 2 / v₀ + r₀ ≤ ρ0 * N := by
          rw [div_le_iff₀ hρ0] at hnormN; linarith
        calc ‖(⟨x, η⟩ : ℂ)‖ ≤ (N : ℝ) ^ A + 2 / v₀ + r₀ + 1 := hz
          _ ≤ (N : ℝ) ^ max A 0 * (2 + 2 / v₀ + r₀) := by
              have : 0 ≤ 2 / v₀ + r₀ + 1 := by positivity
              nlinarith
          _ ≤ (N : ℝ) ^ max A 0 * (ρ0 * N) := mul_le_mul_of_nonneg_left hρN (by positivity)
          _ = ρ0 * ((N : ℝ) ^ max A 0 * N) := by ring
          _ ≤ Real.sqrt (tk k) * (N : ℝ) ^ (κ + 1 / ε) :=
              mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _)
    have him : 0 < (freshDyson F (tk k) ⟨x, η⟩).im :=
      lt_of_lt_of_le hv0 (fresh_regular_bounds hC.2.2 hσ hxw hη.le hη1).1
    exact hloc N hNN₁ a (tk k) ha haσ hσ0 F hC.1 hFn M ⟨x, η⟩ hdom hη him q q
  set badkx : ℕ → ℝ → Set (FlowSample N) := fun k x => {ω | (N : ℝ) ^ ε *
      CEH.isotropicControl (freshM F (tk k) ⟨x, η⟩) ⟨x, η⟩ q q <
      ‖star q ⬝ᵥ (((flowMatrix F a ω (tk k) - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        freshM F (tk k) ⟨x, η⟩) *ᵥ q)‖}
  set Bad₁ : Set (FlowSample N) :=
    ⋃ k ∈ Finset.range (2 ^ m), ⋃ x ∈ energyGrid E r₀ η, badkx k x
  set Bad₂ : Set (FlowSample N) := {ω | ¬ ChainGood K₁ T ω.2}
  refine ⟨Bad₁ ∪ Bad₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.union ?_ (measurableSet_not_chainGood K₁ T)
    refine Finset.measurableSet_biUnion _ fun k _ => Finset.measurableSet_biUnion _ fun x _ => ?_
    exact measurableSet_isoBad_flow F a (tk k) _ q _ _
  · -- the probability bound
    have h2k : (2 : ℝ) ^ kb ≤ 2 * N := by
      have hN2 : 1 < N := by omega
      have h3 : 2 ^ kb.pred < N := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN2
      have hkb : 0 < kb := Nat.clog_pos (by norm_num) hN2
      have h' : 2 ^ kb ≤ 2 * N := by
        have e : kb = kb.pred + 1 := (Nat.succ_pred_eq_of_pos hkb).symm
        rw [e, pow_succ]; omega
      exact_mod_cast h'
    have hgrid := energyGrid_card_le (E := E) hη hr0
    have hcardg : ((energyGrid E r₀ η).card : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
      have h2 : r₀ / η ≤ r₀ * N := by
        rw [div_le_iff₀ hη, mul_assoc, hNη]
        have : (1 : ℝ) ≤ (N : ℝ) ^ (4 * ε) := Real.one_le_rpow hN1 (by linarith)
        have := mul_le_mul_of_nonneg_left this hr0.le
        linarith
      rw [Real.rpow_two]
      calc ((energyGrid E r₀ η).card : ℝ) ≤ r₀ / η + 2 := hgrid
        _ ≤ r₀ * N + 2 * N := by linarith
        _ = (r₀ + 2) * N := by ring
        _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right hcardN hNp.le
        _ = (N : ℝ) ^ 2 := by ring
    have htimes : ((2 ^ m : ℕ) : ℝ) ≤ 2 ^ (4 * p) * (N : ℝ) ^ ((4 * p : ℕ) : ℝ) := by
      have : ((2 ^ m : ℕ) : ℝ) = ((2 : ℝ) ^ kb) ^ (4 * p) := by
        rw [Nat.cast_pow, Nat.cast_two, ← pow_mul]
        congr 1
        simp only [m]; ring
      rw [this, Real.rpow_natCast, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h2k _
    have hsum : ((2 ^ m : ℕ) : ℝ) * ((energyGrid E r₀ η).card : ℝ) * (N : ℝ) ^ (-D') ≤
        (N : ℝ) ^ (-D) / 2 :=
      count_le hNp hN1 p D htimes (by positivity) hcardg h2p
    have hchainN : 2 * (1 / 2 : ℝ) ^ N ≤ (N : ℝ) ^ (-D) / 2 :=
      chain_small hNp hN1 ((le_max_left D 0).trans (Nat.le_ceil _)) hexpN
    calc flowLaw N a (Bad₁ ∪ Bad₂) ≤ flowLaw N a Bad₁ + flowLaw N a Bad₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) + ENNReal.ofReal ((N : ℝ) ^ (-D) / 2) := by
          gcongr
          · calc flowLaw N a Bad₁ ≤ ∑ k ∈ Finset.range (2 ^ m), ∑ x ∈ energyGrid E r₀ η,
                  flowLaw N a (badkx k x) := by
                  refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
                  exact measure_biUnion_finset_le _ _
              _ ≤ ∑ _k ∈ Finset.range (2 ^ m), ∑ _x ∈ energyGrid E r₀ η,
                  ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
                  Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun x hx =>
                    hpt k (Finset.mem_range.1 hk) x hx
              _ = ENNReal.ofReal (((2 ^ m : ℕ) : ℝ) * ((energyGrid E r₀ η).card : ℝ) *
                  (N : ℝ) ^ (-D')) := by
                  rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                    nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
                    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
                    ENNReal.ofReal_natCast]
                  ring
              _ ≤ _ := ENNReal.ofReal_le_ofReal hsum
          · exact (hchain N hN8 a T hT).trans (ENNReal.ofReal_le_ofReal hchainN)
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · -- the deterministic bound on the good event
    intro ω hω hH σ hσ hs i hi
    have hω₁ : ω ∉ Bad₁ := fun h => hω (Or.inl h)
    have hω₂ : ChainGood K₁ T ω.2 := not_not.1 fun h => hω (Or.inr h)
    obtain ⟨x, hxX, hix⟩ := energyGrid_cover hη hi
    have hxw := energyGrid_window hη hηr hr0 hxX
    obtain ⟨k, hk, hu1, hu2⟩ := dyadic_cell hT m (u := σ - a) (by linarith [hσ.1])
      (by linarith [hσ.2])
    obtain ⟨hσk, haσk⟩ := htk k hk
    have hnot : ω ∉ badkx k x := fun h' =>
      hω₁ (mem_biUnion (Finset.mem_range.2 hk) (mem_biUnion hxX h'))
    simp only [badkx, Set.mem_ofPred_eq, not_lt] at hnot
    have hHσ := flowMatrix_isHermitian hC.1 a hH σ
    have hHk := flowMatrix_isHermitian hC.1 a hH (tk k)
    have h1 := overlap_le_of_near hHσ hs hNpos hη q i hix
    have h2 := resolvent_quad_im_compare hHσ hHk (z := ⟨x, η⟩) hη q
    have h3 := im_resolvent_le_on_good hK' hC hσk hxw hη hη1 hNpos q hnot
    -- the modulus
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
    have hextra : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / η ^ 2 ≤ C₂ * γ := by
      have hη2 : η ^ 2 = (N : ℝ) ^ (-(2 - 8 * ε)) := by
        simp only [η]; rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
      have hsT : Real.sqrt T ≤ 1 := Real.sqrt_le_one.2 hT1
      have hnn : 0 ≤ nsq q := Finset.sum_nonneg fun _ _ => by positivity
      have hopB : opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) ≤
          K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio) := by
        refine hmod.trans (div_le_div_of_nonneg_right ?_ (by linarith))
        calc K₁ * Real.sqrt T * chainRatio ^ m ≤ K₁ * 1 * chainRatio ^ m := by gcongr
          _ ≤ K₁ * (N : ℝ) ^ (-(p : ℝ)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hqm hK₁.le
      have hpow : (N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2 ≤ 1 := by
        rw [hη2, div_le_one (by positivity), ← Real.rpow_add hNp]
        exact hrpow_mono (by linarith)
      have hl' : 0 < v₀ * lowConst c₀ s₀ v₀ := by positivity
      calc opB (flowMatrix F a ω σ - flowMatrix F a ω (tk k)) * nsq q / η ^ 2
          ≤ (K₁ * (N : ℝ) ^ (-(p : ℝ)) / (1 - chainRatio)) *
              ((N : ℝ) ^ (2 * max A 1) * γ / (v₀ * lowConst c₀ s₀ v₀)) / η ^ 2 := by
            gcongr
        _ = C₂ * γ * ((N : ℝ) ^ (-(p : ℝ)) * (N : ℝ) ^ (2 * max A 1) / η ^ 2) := by
            simp only [C₂]; field_simp
        _ ≤ C₂ * γ * 1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₂ hγ)
        _ = C₂ * γ := mul_one _
    have hsqrt : Real.sqrt (Real.pi * v₀ * N * η) = Real.sqrt (Real.pi * v₀) * (N : ℝ) ^ (2 * ε) := by
      rw [mul_assoc, hNη, Real.sqrt_mul (by positivity)]
      congr 1
      rw [show (N : ℝ) ^ (4 * ε) = ((N : ℝ) ^ (2 * ε)) ^ 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num; ring_nf]
      exact Real.sqrt_sq (by positivity)
    have hfac : 1 + (N : ℝ) ^ ε / Real.sqrt (Real.pi * v₀ * N * η) ≤
        1 + 1 / Real.sqrt (Real.pi * v₀) := by
      rw [hsqrt]
      have hspv : 0 < Real.sqrt (Real.pi * v₀) := Real.sqrt_pos.2 (by positivity)
      have : (N : ℝ) ^ ε / (Real.sqrt (Real.pi * v₀) * (N : ℝ) ^ (2 * ε)) ≤
          1 / Real.sqrt (Real.pi * v₀) := by
        rw [div_le_div_iff₀ (by positivity) hspv]
        have : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (2 * ε) := hrpow_mono (by linarith)
        nlinarith
      linarith
    have hcoef : (0 : ℝ) ≤ 2 * N * η := by positivity
    calc flowOverlap F a q σ i ω
        ≤ 2 * N * η * (star q ⬝ᵥ ((flowMatrix F a ω σ - (⟨x, η⟩ : ℂ) •
            (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ q)).im := h1
      _ ≤ 2 * N * η * ((1 + 1 / Real.sqrt (Real.pi * v₀)) *
            (gammaCompConst c₀ r₀ s₀ v₀ * γ) + C₂ * γ) := by
          refine mul_le_mul_of_nonneg_left ?_ hcoef
          have := mul_le_mul_of_nonneg_right hfac (mul_nonneg hKc hγ)
          linarith
      _ = (overlapConst c₀ r₀ s₀ v₀ + 2 * C₂) * ((N : ℝ) * η) * γ := by
          unfold overlapConst; ring
      _ = (overlapConst c₀ r₀ s₀ v₀ + 2 * C₂) * (N : ℝ) ^ (4 * ε) * γ := by rw [hNη]

/-- **The conditional form of the overlap bound**: an `𝓛`-measurable set of probability
`≤ N^{-D}` off which `P(Bad | 𝓛) < N^{-D}`, where `Bad` is the exceptional set of
`overlap_event_uniform` at failure exponent `2D`. -/
theorem overlap_event_conditional (F : Matrix (Fin N) (Fin N) ℂ) (a s c : ℝ) (hN : 0 < N)
    (D : ℝ) {Bad : Set (FlowSample N)} (hBad : MeasurableSet Bad)
    (hP : flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-(2 * D)))) :
    ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a s c] B ∧
      (flowLaw N a).real B ≤ (N : ℝ) ^ (-D) ∧
      ∀ ω ∉ B, ((flowLaw N a)[Bad.indicator (fun _ => (1 : ℝ)) | pathSigma F a s c]) ω <
        (N : ℝ) ^ (-D) := by
  have hA : MeasurableSet Badᶜ := hBad.compl
  have hAc : (flowLaw N a).real Badᶜᶜ ≤ (N : ℝ) ^ (-(2 * D)) := by
    rw [compl_compl, measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hP
  obtain ⟨B, hB, hμB, hoff⟩ := pathSigma_disintegrate F a s c hN D hA hAc
  refine ⟨B, hB, hμB, fun ω hω => ?_⟩
  have := hoff ω hω
  rwa [compl_compl] at this

end BlockBand.Palm.MomentFlow
