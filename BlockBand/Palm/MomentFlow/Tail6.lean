module

public import BlockBand.Palm.MomentFlow.PropMeas
public import BlockBand.Palm.MomentFlow.Steps2Gap
public import BlockBand.Palm.MomentFlow.Steps2LongUnif
public import BlockBand.Palm.MomentFlow.StepsMultiSpec
public import BlockBand.Palm.MomentFlow.StepsShortOne

/-!
# Time-integrated finite-speed tails on one `𝓛`-good set

* `tail6_core`: from per-time finite-speed bounds (deterministic `v`, outside probability `p`,
  every forward short solution started at `v` from `1_{Wᶜ}` has `Φ(u,ξ) ≤ δ` under bulk at `v`)
  to **one** `pathSigma F a a c`-measurable set `B`, `P(B) ≤ (u-s)(δ+p)/t + p`, off which (a.e.,
  under bulk on all of `[s,u]`) the backward short row `w` ending at `δ_ξ` satisfies
  `∫_s^u Σ_{ζ∉W} w(v,ζ) dv ≤ t` and `Σ_{ζ∉W} w(s,ζ) ≤ δ`. The row is `truncBackward` at a
  sample-dependent truncation level `1/(n+1)` (chosen below the minimal gap, which is positive a.s.
  by `ae_noCollision`); the tail is identified with the forward solution by `tail_eq_forward`,
  which also makes the bad sets monotone in `n`, so their union has the same bound.
* `tail6_multi` (every `r ≥ 1`, from `MultiShortFiniteSpeed`): `W = occBall r R ξ`.
* `tail6_one` (`r = 1`, from `RelativeLocalizationContract.short_row` through
  `shortRow_of_momentFlow`): `W = labelBall k R`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory intervalIntegral Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization

variable {N : ℕ}

/-- Clamp to `[0,1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem continuous_clamp01 : Continuous clamp01 := by unfold clamp01; fun_prop

/-- Truncated rates along the clamped path are the exact short rates on `[s,u]` when all gaps
at time `x` are `≥ g`. -/
theorem cfgRate_clampEig_eq_short (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) {g s u x : ℝ} (hg : 0 < g) (hx : x ∈ Icc s u)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|) :
    cfgRate N (clampEig F a s u ω x) ℓ g = shortFlowRate F a ω ℓ x := by
  have e : clampEig F a s u ω x = fun k => flowEigenvalue F a ω x k := by
    funext k; simp [clampEig, clampT_of_mem hx]
  rw [e, cfgRate_eq_zero_gap hg.le hgap, cfgRate_zero_eq_short]

/-- A collision-free path has a uniform positive gap on a compact time interval. -/
theorem exists_gap_of_noCollision {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {s u : ℝ} (hsu : s ≤ u) (ω : FlowSample N)
    (hω : ∀ x ∈ Icc s u, ∀ i j : Fin N, i ≠ j →
      flowEigenvalue F a ω x i ≠ flowEigenvalue F a ω x j) :
    ∃ n : ℕ, ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
      1 / ((n : ℝ) + 1) ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m| := by
  have hpair : ∀ p : Fin N × Fin N, ∃ g : ℝ, 0 < g ∧ (p.1 ≠ p.2 → ∀ x ∈ Icc s u,
      g ≤ |flowEigenvalue F a ω x p.1 - flowEigenvalue F a ω x p.2|) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · have hcont : ContinuousOn
          (fun x => |flowEigenvalue F a ω x p.1 - flowEigenvalue F a ω x p.2|) (Icc s u) :=
        (((continuous_flowEigenvalue hF a ω _).sub
          (continuous_flowEigenvalue hF a ω _)).abs).continuousOn
      obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hsu) hcont
      exact ⟨_, abs_pos.2 (sub_ne_zero.2 (hω x₀ hx₀ _ _ hp)), fun _ x hx => hmin hx⟩
  choose g hg0 hg using hpair
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ p : Fin N × Fin N, 1 / ((n : ℝ) + 1) ≤ g p :=
    Filter.eventually_all.2 fun p =>
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (ge_mem_nhds (hg0 p))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, fun x hx k m hkm => (hn (k, m)).trans (hg (k, m) hkm x hx)⟩

theorem measurableSet_gap (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {a c s u : ℝ}
    (has : a ≤ s) (huc : u ≤ c) (g : ℝ) :
    MeasurableSet[pathSigma F a a c] {ω : FlowSample N | ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
      g ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|} := by
  have e : {ω : FlowSample N | ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
      g ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|} =
      ⋂ k : Fin N, ⋂ m : Fin N, {ω | k ≠ m → ∀ x ∈ Icc s u,
        g - |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m| ≤ 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, sub_nonpos]
    exact ⟨fun h k m hkm x hx => h x hx k m hkm, fun h x hx k m hkm => h k m hkm x hx⟩
  rw [e]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun m => ?_
  by_cases hkm : k ≠ m
  · convert measurableSet_forall_Icc_le (m := pathSigma F a a c)
      (f := fun x ω => g - |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|)
      (fun x hx => ?_) (fun ω => ?_) 0 using 1
    · ext ω; exact ⟨fun h => h hkm, fun h _ => h⟩
    · have hx' : x ∈ Icc a c := ⟨has.trans hx.1, hx.2.trans huc⟩
      exact (continuous_abs.measurable.comp ((measurable_flowEigenvalue_pathSigma F a a c hx' k).sub
        (measurable_flowEigenvalue_pathSigma F a a c hx' m))).const_sub g
    · exact (continuous_const.sub ((continuous_flowEigenvalue hF a ω k).sub
        (continuous_flowEigenvalue hF a ω m)).abs).continuousOn
  · simp only [hkm, false_implies, ofPred_true, MeasurableSet.univ]

theorem measurableSet_bulk (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {a c s u : ℝ}
    (has : a ≤ s) (huc : u ≤ c) (ξ : Occ N) (E κ : ℝ) :
    MeasurableSet[pathSigma F a a c] {ω : FlowSample N | ∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k →
      |flowEigenvalue F a ω v k - E| ≤ κ} := by
  have e : {ω : FlowSample N | ∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k →
      |flowEigenvalue F a ω v k - E| ≤ κ} =
      ⋂ k : Fin N, {ω | 0 < ξ k → ∀ v ∈ Icc s u, |flowEigenvalue F a ω v k - E| ≤ κ} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    exact ⟨fun h k hk v hv => h v hv k hk, fun h v hv k hk => h k hk v hv⟩
  rw [e]
  refine MeasurableSet.iInter fun k => ?_
  by_cases hk : 0 < ξ k
  · convert measurableSet_forall_Icc_le (m := pathSigma F a a c)
      (f := fun x ω => |flowEigenvalue F a ω x k - E|) (fun x hx => ?_) (fun ω => ?_) κ using 1
    · ext ω; exact ⟨fun h => h hk, fun h _ => h⟩
    · exact continuous_abs.measurable.comp ((measurable_flowEigenvalue_pathSigma F a a c
        ⟨has.trans hx.1, hx.2.trans huc⟩ k).sub_const E)
    · exact ((continuous_flowEigenvalue hF a ω k).sub continuous_const).abs.continuousOn
  · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- **Time-integrated tails, core** (Tonelli + Markov over the backward time `v`). For deterministic
`a ≤ s ≤ u ≤ c`, a terminal configuration `ξ` and a set `W` of configurations: if for every
deterministic `v ∈ [s,u]`, outside `flowLaw`-probability `p`, bulk at time `v` forces every
short forward solution on `[v,u]` started from `1_{Wᶜ}` to have `Φ(u,ξ) ≤ δ`, then there is
**one** `pathSigma F a a c`-measurable set `B` of probability `≤ (u-s)(δ+p)/t + p` such that for
a.e. sample outside `B` with bulk positions on all of `[s,u]` the backward short-flow row `w`
ending at `δ_ξ` has `∫_s^u Σ_{ζ ∉ W} w(v,ζ) dv ≤ t` and terminal tail `Σ_{ζ ∉ W} w(s,ζ) ≤ δ`. -/
theorem tail6_core (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ} (ha : 0 < a) (ℓ : ℕ) {s u : ℝ} (has : a ≤ s)
    (hsu : s ≤ u) (huc : u ≤ c) {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r)
    (W : Finset (Occ N)) (E κ : ℝ) {δ p t : ℝ} (hδ : 0 ≤ δ) (hp : 0 ≤ p) (ht : 0 < t)
    (hspeed : ∀ v ∈ Icc s u, flowLaw N a {ω | (∀ k : Fin N, 0 < ξ k →
        |flowEigenvalue F a ω v k - E| ≤ κ) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r v u Φ ∧
          (∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ W then 0 else 1) ∧ δ < Φ u ξ} ≤
        ENNReal.ofReal p) :
    ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
      flowLaw N a B ≤ ENNReal.ofReal ((u - s) * (δ + p) / t + p) ∧
      ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
        (∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k → |flowEigenvalue F a ω v k - E| ≤ κ) →
        ∃ w : ℝ → Occ N → ℝ, IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r s u w ∧
          (∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) ∧
          (∫ v in s..u, ∑ ζ ∈ sector N r \ W, w v ζ) ≤ t ∧
          ∑ ζ ∈ sector N r \ W, w s ζ ≤ δ := by
  classical
  set gg : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hggdef
  have hgg : ∀ n, 0 < gg n := fun n => by simp only [hggdef]; positivity
  have hggmono : ∀ n, gg (n + 1) ≤ gg n := fun n => by
    simp only [hggdef]
    exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
  set Gap : ℕ → Set (FlowSample N) := fun n => {ω | ∀ x ∈ Icc s u, ∀ k m : Fin N, k ≠ m →
    gg n ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|} with hGapdef
  set Bulk : Set (FlowSample N) := {ω | ∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k →
    |flowEigenvalue F a ω v k - E| ≤ κ} with hBulkdef
  have hGapm : ∀ n, MeasurableSet[pathSigma F a a c] (Gap n) := fun n =>
    measurableSet_gap F hF has huc (gg n)
  have hBulkm : MeasurableSet[pathSigma F a a c] Bulk := measurableSet_bulk F hF has huc ξ E κ
  have hGapmono : ∀ n, Gap n ⊆ Gap (n + 1) := fun n ω hω x hx k m hkm =>
    (hggmono n).trans (hω x hx k m hkm)
  set G : ℕ → Set (FlowSample N) := fun n => Gap n ∩ Bulk with hGdef
  set wB : ℕ → ℝ → FlowSample N → Occ N → ℝ := fun n v ω =>
    truncBackward F a ℓ (gg n) s u r ξ v ω with hwBdef
  set tail : ℕ → ℝ → FlowSample N → ℝ := fun n v ω => ∑ ζ ∈ sector N r \ W, wB n v ω ζ
    with htaildef
  set X : ℕ → ℝ → FlowSample N → ℝ := fun n v ω =>
    (G n).indicator (fun ω => clamp01 (tail n v ω)) ω with hXdef
  have hback : ∀ n ω, ω ∈ Gap n →
      IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r s u (fun v => wB n v ω) ∧
        ∀ ζ ∈ sector N r, wB n u ω ζ = deltaCfg ξ ζ := fun n ω hω =>
    truncBackward_isBackward hF hN a ℓ (hgg n) hsu r ξ ω hω
  have hfwd : ∀ n ω, ω ∈ Gap n → ∀ v ∈ Icc s u, ∃ Φ : ℝ → Occ N → ℝ,
      IsMomentFlowSolution (shortFlowRate F a ω ℓ) r v u Φ ∧
        ∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ W then 0 else 1 := by
    intro n ω hω v hv
    have hcont : Continuous fun x => cfgRate N (clampEig F a s u ω x) ℓ (gg n) :=
      (continuous_cfgRate hN ℓ (hgg n)).comp
        (continuous_pi fun k => (continuous_flowEigenvalue hF a ω k).comp (continuous_clampT s u))
    refine exists_forward hv.2 (hcont.continuousOn.congr fun x hx => ?_) r _
    have hx' : x ∈ Icc s u := ⟨hv.1.trans hx.1, hx.2⟩
    exact (cfgRate_clampEig_eq_short F a ω ℓ (hgg n) hx' (hω x hx')).symm
  have htail_eq : ∀ n ω, ω ∈ Gap n → ∀ v ∈ Icc s u, ∀ Φ : ℝ → Occ N → ℝ,
      IsMomentFlowSolution (shortFlowRate F a ω ℓ) r v u Φ →
      (∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ W then 0 else 1) → tail n v ω = Φ u ξ :=
    fun n ω hω v hv Φ hΦ hΦ0 => tail_eq_forward (fun x _ i j => shortFlowRate_symm F a ω ℓ x i j)
      (hback n ω hω).1 hξ (hback n ω hω).2 hv W hΦ hΦ0
  have htail01 : ∀ n ω, ω ∈ Gap n → ∀ v ∈ Icc s u, 0 ≤ tail n v ω ∧ tail n v ω ≤ 1 := by
    intro n ω hω v hv
    obtain ⟨hw, hwu⟩ := hback n ω hω
    have hnn := hw.nonneg (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j)
      (fun ζ hζ => by rw [hwu ζ hζ]; unfold deltaCfg; split_ifs <;> norm_num)
    have hmass : ∑ ζ ∈ sector N r, wB n v ω ζ = 1 := by
      rw [hw.mass_eq (fun x _ i j => shortFlowRate_symm F a ω ℓ x i j) v hv,
        Finset.sum_congr rfl fun ζ hζ => hwu ζ hζ]
      simpa using sum_deltaCfg_mul hξ (fun _ => (1 : ℝ))
    refine ⟨Finset.sum_nonneg fun ζ hζ => hnn v hv ζ (Finset.mem_sdiff.1 hζ).1, ?_⟩
    rw [← hmass]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      fun ζ hζ _ => hnn v hv ζ hζ
  have hXeq : ∀ n ω, ω ∈ G n → ∀ v ∈ Icc s u, X n v ω = tail n v ω := by
    intro n ω hω v hv
    simp only [hXdef, indicator_of_mem hω]
    obtain ⟨h0, h1⟩ := htail01 n ω hω.1 v hv
    unfold clamp01; rw [min_eq_left h1, max_eq_right h0]
  have hXm : ∀ n v, Measurable[pathSigma F a a c] (X n v) := by
    intro n v
    have htm : Measurable[pathSigma F a a c] fun ω => tail n v ω :=
      Finset.measurable_sum _ fun ζ _ =>
        measurable_truncBackward hF hN ℓ (hgg n) has hsu huc r ξ v ζ
    exact (continuous_clamp01.measurable.comp htm).indicator ((hGapm n).inter hBulkm)
  have hXc : ∀ n ω, Continuous fun v => X n v ω := by
    intro n ω
    by_cases hω : ω ∈ G n
    · have e : (fun v => X n v ω) = fun v => clamp01 (tail n v ω) :=
        funext fun v => by simp only [hXdef, indicator_of_mem hω]
      rw [e]
      exact continuous_clamp01.comp (continuous_finsetSum _ fun ζ _ =>
        continuous_truncBackward hF hN a ℓ (hgg n) s u r ξ ω ζ)
    · have e : (fun v => X n v ω) = fun _ => 0 :=
        funext fun v => by simp only [hXdef, indicator_of_notMem hω]
      rw [e]; exact continuous_const
  have hX01 : ∀ n v ω, 0 ≤ X n v ω ∧ X n v ω ≤ 1 := by
    intro n v ω
    by_cases hω : ω ∈ G n
    · simp only [hXdef, indicator_of_mem hω]
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    · simp only [hXdef, indicator_of_notMem hω]; exact ⟨le_rfl, zero_le_one⟩
  set S : ℝ → Set (FlowSample N) := fun v => {ω | (∀ k : Fin N, 0 < ξ k →
      |flowEigenvalue F a ω v k - E| ≤ κ) ∧
      ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r v u Φ ∧
        (∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ W then 0 else 1) ∧ δ < Φ u ξ} with hSdef
  have hXbad : ∀ n, ∀ v ∈ Icc s u, {ω | δ < X n v ω} ⊆ S v := by
    intro n v hv ω hωX
    have hωX' : δ < X n v ω := hωX
    by_cases hω : ω ∈ G n
    · rw [hXeq n ω hω v hv] at hωX'
      obtain ⟨Φ, hΦ, hΦ0⟩ := hfwd n ω hω.1 v hv
      refine ⟨fun k hk => hω.2 v hv k hk, Φ, hΦ, hΦ0, ?_⟩
      rwa [← htail_eq n ω hω.1 v hv Φ hΦ hΦ0]
    · simp only [hXdef, indicator_of_notMem hω] at hωX'
      exact absurd hωX' (not_lt.2 hδ)
  have hXmono : ∀ n, ∀ v ∈ Icc s u, ∀ ω, X n v ω ≤ X (n + 1) v ω := by
    intro n v hv ω
    by_cases hω : ω ∈ G n
    · have hω' : ω ∈ G (n + 1) := ⟨hGapmono n hω.1, hω.2⟩
      rw [hXeq n ω hω v hv, hXeq (n + 1) ω hω' v hv]
      obtain ⟨Φ, hΦ, hΦ0⟩ := hfwd n ω hω.1 v hv
      rw [htail_eq n ω hω.1 v hv Φ hΦ hΦ0, htail_eq (n + 1) ω hω'.1 v hv Φ hΦ hΦ0]
    · simp only [hXdef, indicator_of_notMem hω]; exact (hX01 (n + 1) v ω).1
  -- the two families of bad sets
  set B1 : ℕ → Set (FlowSample N) := fun n => {ω | t < ∫ v in s..u, X n v ω} with hB1def
  set B2 : ℕ → Set (FlowSample N) := fun n => {ω | δ < X n s ω} with hB2def
  have hTM : ∀ n, MeasurableSet[pathSigma F a a c] (B1 n) ∧
      flowLaw N a (B1 n) ≤ ENNReal.ofReal ((u - s) * (δ + 1 * p) / t) := fun n =>
    tonelli_markov (pathSigma F a a c) (pathSigma_le F a a c) (flowLaw N a) hsu
      (fun v _ => hXm n v) (fun ω => (hXc n ω).continuousOn) (fun v _ ω => (hX01 n v ω).1)
      (fun v _ ω => (hX01 n v ω).2) zero_le_one hδ hp ht
      (fun v hv => (measure_mono (hXbad n v hv)).trans (hspeed v hv))
  have hB1mono : Monotone B1 := by
    refine monotone_nat_of_le_succ fun n ω hω => ?_
    have hω' : t < ∫ v in s..u, X n v ω := hω
    show t < ∫ v in s..u, X (n + 1) v ω
    refine hω'.trans_le (intervalIntegral.integral_mono_on hsu
      ((hXc n ω).intervalIntegrable s u) ((hXc (n + 1) ω).intervalIntegrable s u)
      fun v hv => hXmono n v hv ω)
  have hB2mono : Monotone B2 := by
    refine monotone_nat_of_le_succ fun n ω hω => ?_
    have hω' : δ < X n s ω := hω
    show δ < X (n + 1) s ω
    exact hω'.trans_le (hXmono n s ⟨le_rfl, hsu⟩ ω)
  refine ⟨(⋃ n, B1 n) ∪ ⋃ n, B2 n, ?_, ?_, ?_⟩
  · exact (MeasurableSet.iUnion fun n => (hTM n).1).union
      (MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (hXm n s))
  · refine (measure_union_le _ _).trans ?_
    rw [hB1mono.measure_iUnion, hB2mono.measure_iUnion]
    have h1 : (⨆ n, flowLaw N a (B1 n)) ≤ ENNReal.ofReal ((u - s) * (δ + p) / t) :=
      iSup_le fun n => by simpa using (hTM n).2
    have h2 : (⨆ n, flowLaw N a (B2 n)) ≤ ENNReal.ofReal p :=
      iSup_le fun n => (measure_mono (hXbad n s ⟨le_rfl, hsu⟩)).trans (hspeed s ⟨le_rfl, hsu⟩)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    have hus : 0 ≤ u - s := by linarith
    rw [ENNReal.ofReal_add (by positivity) hp]
  · filter_upwards [ae_noCollision hDBM hF ha] with ω hω hωB hbulk
    obtain ⟨n, hn⟩ := exists_gap_of_noCollision hF a hsu ω
      fun x hx i j hij => hω.2 x (has.trans hx.1) i j hij
    have hgap : ω ∈ Gap n := hn
    have hG : ω ∈ G n := ⟨hgap, hbulk⟩
    have hnB1 : ω ∉ B1 n := fun h => hωB (Or.inl (mem_iUnion.2 ⟨n, h⟩))
    have hnB2 : ω ∉ B2 n := fun h => hωB (Or.inr (mem_iUnion.2 ⟨n, h⟩))
    refine ⟨fun v => wB n v ω, (hback n ω hgap).1, (hback n ω hgap).2, ?_, ?_⟩
    · have hle : (∫ v in s..u, X n v ω) ≤ t := not_lt.1 hnB1
      have e : (∫ v in s..u, ∑ ζ ∈ sector N r \ W, wB n v ω ζ) = ∫ v in s..u, X n v ω := by
        refine intervalIntegral.integral_congr fun v hv => ?_
        rw [uIcc_of_le hsu] at hv
        exact (hXeq n ω hG v hv).symm
      rw [e]; exact hle
    · have hle : X n s ω ≤ δ := not_lt.1 hnB2
      rwa [hXeq n ω hG s ⟨le_rfl, hsu⟩] at hle

theorem eventually_exp_le_rpow {c' ε : ℝ} (hc' : 0 < c') (hε : 0 < ε) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, Real.exp (-(c' * (n : ℝ) ^ ε)) ≤ (n : ℝ) ^ (-x) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have h2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (x / ε) c' hc').comp h1
  filter_upwards [h2.eventually (gt_mem_nhds one_pos), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [Function.comp] at hn
  rw [← Real.rpow_mul hnpos.le, mul_div_cancel₀ _ hε.ne', neg_mul] at hn
  have hpos : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos hnpos x
  calc Real.exp (-(c' * (n : ℝ) ^ ε))
      = ((n : ℝ) ^ x * Real.exp (-(c' * (n : ℝ) ^ ε))) / (n : ℝ) ^ x := by field_simp
    _ ≤ 1 / (n : ℝ) ^ x := div_le_div_of_nonneg_right hn.le hpos.le
    _ = (n : ℝ) ^ (-x) := by rw [Real.rpow_neg hnpos.le, one_div]

theorem tail6_arith {n D₁ x δ p : ℝ} (hn : 3 ≤ n) (hD : 1 ≤ D₁) (hx : x ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ n ^ (-(2 * D₁ + 1))) (hp : p = n ^ (-(2 * D₁ + 1))) :
    x * (δ + p) / n ^ (-D₁) + p ≤ n ^ (-D₁) := by
  have hn0 : 0 < n := by linarith
  set t := n ^ (-D₁) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hn0 _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hq : n ^ (-(2 * D₁ + 1)) = t * t / n := by
    rw [ht, ← Real.rpow_add hn0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hn0]
    ring_nf
  rw [hq] at hδ hp
  subst hp
  have h1 : x * (δ + t * t / n) / t ≤ 2 * t / n := by
    rw [div_le_iff₀ htpos]
    have : x * (δ + t * t / n) ≤ 1 * (t * t / n + t * t / n) :=
      mul_le_mul hx (by linarith) (by positivity) zero_le_one
    calc x * (δ + t * t / n) ≤ 1 * (t * t / n + t * t / n) := this
      _ = 2 * t / n * t := by ring
  have h2 : t * t / n ≤ t / n := div_le_div_of_nonneg_right (by nlinarith) hn0.le
  have h3 : 3 * t / n ≤ t := by rw [div_le_iff₀ hn0]; nlinarith
  linarith [show 2 * t / n + t / n = 3 * t / n by ring]

/-- The occDist ball `{ζ ∈ sector : occDist ξ ζ ≤ rR}`. -/
def occBall (r : ℕ) (R : ℝ) (ξ : Occ N) : Finset (Occ N) := by
  classical
  exact (sector N r).filter fun ζ => ¬ ((r : ℝ) * R < (occDist ξ ζ : ℝ))

/-- **Time-integrated tails for every `r ≥ 1`** (from `MultiShortFiniteSpeed` and
`DysonBrownianMotion`). At the moment-flow scales of `short_row`; for every `D`, for `N ≥ N₀`,
every fresh `F`, deterministic `a ≤ s ≤ u ≤ c` and `ξ` in the `r`-sector: one
`pathSigma`-measurable `B` with `P(B) ≤ N^{-D}` such that a.e. off `B`, if all particles of `ξ`
are in the bulk (`r₀/16`) at every time of `[s,u]`, the backward short row `w` ending at `δ_ξ` has
`∫_s^u Σ_{occDist(ξ,ζ) > rR} w(v,ζ) dv ≤ N^{-D}` and the same tail at `v = s` is `≤ N^{-D}`. -/
theorem tail6_multi (hMS : MultiShortFiniteSpeed) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) {r : ℕ} (hr : 1 ≤ r) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        let R : ℝ := (N : ℝ) ^ ε * ℓ
        ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ ξ ∈ sector N r,
          ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
            flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
              (∀ v ∈ Icc s u, ∀ k : Fin N, 0 < ξ k →
                |flowEigenvalue F a ω v k - E| ≤ r₀ / 16) →
              ∃ w : ℝ → Occ N → ℝ, IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r s u w ∧
                (∀ ζ ∈ sector N r, w u ζ = deltaCfg ξ ζ) ∧
                (∫ v in s..u, ∑ ζ ∈ sector N r \ occBall r R ξ, w v ζ) ≤ (N : ℝ) ^ (-D) ∧
                ∑ ζ ∈ sector N r \ occBall r R ξ, w s ζ ≤ (N : ℝ) ^ (-D) := by
  classical
  intro D
  obtain ⟨c', hc', hMSD⟩ := hMS A c r₀ s₀ v₀ hK r hr ε hε
  set D₁ : ℝ := max D 1 with hD₁
  obtain ⟨N₁, hN₁⟩ := hMSD (2 * D₁ + 1)
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ (3 : ℝ) ≤ n) ∧ (n : ℝ) ^ (-(1 / 100 : ℝ)) < c ∧
      Real.exp (-(c' * (n : ℝ) ^ ε)) ≤ (n : ℝ) ^ (-(2 * D₁ + 1)) :=
    ((eventually_ge_atTop N₁).and (eventually_ge_atTop 3 |>.mono fun n hn => by
      exact_mod_cast hn)).and ((hτ0.eventually (gt_mem_nhds hK.1)).and
      (eventually_exp_le_rpow hc' hε _))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC => ?_⟩
  obtain ⟨⟨hN1, hN3⟩, hτ, hexp⟩ := hN₀ N hN
  intro a ℓ R s u has hsu huc ξ hξ
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have ha : 0 < a := by simp only [a]; linarith
  have hspeed : ∀ v ∈ Icc s u, flowLaw N a {ω | (∀ k : Fin N, 0 < ξ k →
      |flowEigenvalue F a ω v k - E| ≤ r₀ / 16) ∧
      ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r v u Φ ∧
        (∀ ζ ∈ sector N r, Φ v ζ = if ζ ∈ occBall r R ξ then 0 else 1) ∧
        Real.exp (-(c' * (N : ℝ) ^ ε)) < Φ u ξ} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(2 * D₁ + 1))) := by
    intro v hv
    refine (measure_mono fun ω hω => ?_).trans
      (hN₁ N hN1 F E hC v u (has.trans hv.1) hv.2 huc ξ hξ)
    obtain ⟨hb, Φ, hΦ, hΦ0, hbig⟩ := hω
    refine ⟨hb, Φ, hΦ, fun ζ hζ => ?_, hbig⟩
    rw [hΦ0 ζ hζ]
    by_cases hd : (r : ℝ) * R < (occDist ξ ζ : ℝ)
    · have : ζ ∉ occBall r R ξ := fun h => (Finset.mem_filter.1 h).2 hd
      rw [ite_eq_right_iff.2 fun h => absurd h this, ite_eq_left_iff.2 fun h => absurd hd h]
    · have : ζ ∈ occBall r R ξ := Finset.mem_filter.2 ⟨hζ, hd⟩
      rw [ite_eq_left_iff.2 fun h => absurd this h, ite_eq_right_iff.2 fun h => absurd h hd]
  have hNr : (0 : ℝ) < N := by linarith
  obtain ⟨B, hBm, hBμ, hBae⟩ := tail6_core (hDBM N) hC.1 hNpos ha ℓ has hsu huc hξ
    (occBall r R ξ) E (r₀ / 16) (Real.exp_pos _).le (Real.rpow_nonneg hNr.le _)
    (Real.rpow_pos_of_pos hNr (-D₁)) hspeed
  have hD1 : 1 ≤ D₁ := le_max_right _ _
  have hDD : D ≤ D₁ := le_max_left _ _
  have hus0 : 0 ≤ u - s := by linarith
  have hus1 : u - s ≤ 1 := by
    have h1 : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have : u - s ≤ c - a := by linarith
    simp only [a] at this; linarith
  have hmono : ∀ y : ℝ, D ≤ y → (N : ℝ) ^ (-y) ≤ (N : ℝ) ^ (-D) := fun y hy =>
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine ⟨B, hBm, hBμ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact (tail6_arith hN3 hD1 hus1 (Real.exp_pos _).le hexp rfl).trans (hmono D₁ hDD)
  · filter_upwards [hBae] with ω hω hωB hbulk
    obtain ⟨w, hw, hwu, hint, hterm⟩ := hω hωB hbulk
    exact ⟨w, hw, hwu, hint.trans (hmono D₁ hDD),
      hterm.trans (hexp.trans (hmono _ (by linarith)))⟩

theorem single_one_inj {j j' : Fin N} (h : (Pi.single j' 1 : Occ N) = Pi.single j 1) : j' = j := by
  by_contra hne
  have := congrFun h j
  simp [Ne.symm hne] at this

/-- The label ball `{δ_j : labelDist k j ≤ R}` in the one-particle sector. -/
def labelBall (k : Fin N) (R : ℝ) : Finset (Occ N) := by
  classical
  exact (Finset.univ.filter fun j : Fin N => ¬ R < (labelDist k j : ℝ)).image
    fun j => Pi.single j 1

/-- **Time-integrated tails for `r = 1`** (from `RelativeLocalizationContract.short_row` through
`shortRow_of_momentFlow`): same conclusion as `tail6_multi` with the label ball. -/
theorem tail6_one (hRL : RelativeLocalizationContract) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    {A c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
        let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
        let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
        let R : ℝ := (N : ℝ) ^ ε * ℓ
        ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
          ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
            flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
            ∀ᵐ ω ∂flowLaw N a, ω ∉ B →
              (∀ v ∈ Icc s u, |flowEigenvalue F a ω v k - E| ≤ r₀ / 16) →
              ∃ w : ℝ → Occ N → ℝ, IsBackwardMomentFlow (shortFlowRate F a ω ℓ) 1 s u w ∧
                (∀ ζ ∈ sector N 1, w u ζ = deltaCfg (Pi.single k 1) ζ) ∧
                (∫ v in s..u, ∑ ζ ∈ sector N 1 \ labelBall k R, w v ζ) ≤ (N : ℝ) ^ (-D) ∧
                ∑ ζ ∈ sector N 1 \ labelBall k R, w s ζ ≤ (N : ℝ) ^ (-D) := by
  classical
  intro D
  obtain ⟨c', hc', hMSD⟩ := shortRow_of_momentFlow hRL A c r₀ s₀ v₀ hK ε hε
  set D₁ : ℝ := max D 1 with hD₁
  obtain ⟨N₁, hN₁⟩ := hMSD (2 * D₁ + 1)
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have ev : ∀ᶠ n : ℕ in atTop, (N₁ ≤ n ∧ (3 : ℝ) ≤ n) ∧ (n : ℝ) ^ (-(1 / 100 : ℝ)) < c ∧
      Real.exp (-(c' * (n : ℝ) ^ ε)) ≤ (n : ℝ) ^ (-(2 * D₁ + 1)) :=
    ((eventually_ge_atTop N₁).and (eventually_ge_atTop 3 |>.mono fun n hn => by
      exact_mod_cast hn)).and ((hτ0.eventually (gt_mem_nhds hK.1)).and
      (eventually_exp_le_rpow hc' hε _))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC => ?_⟩
  obtain ⟨⟨hN1, hN3⟩, hτ, hexp⟩ := hN₀ N hN
  intro a ℓ R s u has hsu huc k
  have hξ : (Pi.single k 1 : Occ N) ∈ sector N 1 := single_mem_sector_one k
  have hNpos : 0 < N := by exact_mod_cast (show (0 : ℝ) < N by linarith)
  have ha : 0 < a := by simp only [a]; linarith
  have hspeed : ∀ v ∈ Icc s u, flowLaw N a {ω | (∀ k' : Fin N, 0 < (Pi.single k 1 : Occ N) k' →
      |flowEigenvalue F a ω v k' - E| ≤ r₀ / 16) ∧
      ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) 1 v u Φ ∧
        (∀ ζ ∈ sector N 1, Φ v ζ = if ζ ∈ labelBall k R then 0 else 1) ∧
        Real.exp (-(c' * (N : ℝ) ^ ε)) < Φ u (Pi.single k 1)} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(2 * D₁ + 1))) := by
    intro v hv
    refine (measure_mono fun ω hω => ?_).trans
      (hN₁ N hN1 F E hC v u (has.trans hv.1) hv.2 huc k)
    obtain ⟨hb, Φ, hΦ, hΦ0, hbig⟩ := hω
    refine ⟨hb k (by simp), Φ, hΦ, fun j => ?_, hbig⟩
    rw [hΦ0 _ (single_mem_sector_one j)]
    by_cases hd : R < (labelDist k j : ℝ)
    · have : (Pi.single j 1 : Occ N) ∉ labelBall k R := by
        intro h
        obtain ⟨j', hj', hjj⟩ := Finset.mem_image.1 h
        rw [single_one_inj hjj] at hj'
        exact (Finset.mem_filter.1 hj').2 hd
      rw [ite_eq_right_iff.2 fun h => absurd h this, ite_eq_left_iff.2 fun h => absurd hd h]
    · have : (Pi.single j 1 : Occ N) ∈ labelBall k R :=
        Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, rfl⟩
      rw [ite_eq_left_iff.2 fun h => absurd this h, ite_eq_right_iff.2 fun h => absurd h hd]
  have hNr : (0 : ℝ) < N := by linarith
  obtain ⟨B, hBm, hBμ, hBae⟩ := tail6_core (hDBM N) hC.1 hNpos ha ℓ has hsu huc hξ
    (labelBall k R) E (r₀ / 16) (Real.exp_pos _).le (Real.rpow_nonneg hNr.le _)
    (Real.rpow_pos_of_pos hNr (-D₁)) hspeed
  have hD1 : 1 ≤ D₁ := le_max_right _ _
  have hDD : D ≤ D₁ := le_max_left _ _
  have hus0 : 0 ≤ u - s := by linarith
  have hus1 : u - s ≤ 1 := by
    have h1 : (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have : u - s ≤ c - a := by linarith
    simp only [a] at this; linarith
  have hmono : ∀ y : ℝ, D ≤ y → (N : ℝ) ^ (-y) ≤ (N : ℝ) ^ (-D) := fun y hy =>
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  refine ⟨B, hBm, hBμ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · exact (tail6_arith hN3 hD1 hus1 (Real.exp_pos _).le hexp rfl).trans (hmono D₁ hDD)
  · filter_upwards [hBae] with ω hω hωB hbulk
    obtain ⟨w, hw, hwu, hint, hterm⟩ := hω hωB fun v hv k' hk' => by
      have hkk : k' = k := by
        by_contra hne
        simp [hne] at hk'
      rw [hkk]; exact hbulk v hv
    exact ⟨w, hw, hwu, hint.trans (hmono D₁ hDD),
      hterm.trans (hexp.trans (hmono _ (by linarith)))⟩

end BlockBand.Palm.MomentFlow
