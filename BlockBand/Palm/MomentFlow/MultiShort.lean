module

public import BlockBand.Palm.MomentFlow.MultiFlow
public import BlockBand.Palm.MomentFlow.FlowRates
public import BlockBand.Palm.RelativeLocalizationHit

/-!
# `r`-particle finite speed of propagation for the short moment flow (quantitative form)

The `r`-particle analogue of the short-row bound `RelativeLocalizationContract.short_row`, proved
by the weight argument of the relative localization lemma applied directly to the `r`-particle
short moment flow `𝓢` (no auxiliary rotation `M_{s,u}`).

Main result `multi_short_row_quant` (fixed `N`; hypotheses
`SemimartingaleItoFormula (N + M)`, `StoppedSemimartingale 1`, `DysonBrownianMotion N`):
for flow times `a < s ≤ u`, a label `k`, a configuration `ξ₀` of the `r`-particle sector, a
radius `R`, and a set of samples `G` on which (when the moving centre `λ_k(s)` is in the bulk)
the initial matrix is Hermitian, the long/short gap clauses and all gaps `> g` hold on
`[s,u]`, the product weight `W = ∏ φ(λ_m - λ_k(s))^{ζ_m}` of every far configuration at time `s`
is `≤ δ₀`, and `W(ξ₀)` at time `u` is `≥ w`:

`P(λ_k(s) bulk ∧ ∃ Φ solving 𝓢 on [s,u], Φ(s) = 1_far, e < Φ(u, ξ₀)) ≤ P(Gᶜ) + M δ₀ e^{K(u-s)}/(w e)`

where `far ζ ⟺ ∃ j, ζ_j > 0 ∧ R < |j - k|`, `M = #sector`, `φ = rlPhi ν 0 d R₀` (the weight of
`RelativeLocalizationWeight`, centred at `λ_k(s)`), and `K` dominates the explicit rate `κ_r`.

Proof: clamped centre `c₀ = clamp(λ_k(s))` (`𝓖'_0`-measurable), data `v₀ = 1_A 1_far` with
`A = {far weights at time s are ≤ δ₀} ∈ 𝓖'_0`, the raw-filtration hitting time `flowStop` of the
relaxed clauses and small gaps, `mf_expectation_le` (stopped Itô + Gronwall in mean), Markov's
inequality, and uniqueness of the moment flow (`IsMomentFlowSolution.eq_of_initial_eq`) to
identify every solution `Φ` with the adapted mass on `G`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- Far configurations: some particle at rank distance `> R` from `k`. -/
def farCfg (k : Fin N) (R : ℝ) (ζ : Occ N) : Prop := ∃ j, 0 < ζ j ∧ R < (labelDist k j : ℝ)

/-- Indicator of the far configurations. -/
def farInd (k : Fin N) (R : ℝ) (ζ : Occ N) : ℝ := by
  classical
  exact if farCfg k R ζ then 1 else 0

theorem farInd_mem (k : Fin N) (R : ℝ) (ζ : Occ N) : 0 ≤ farInd k R ζ ∧ farInd k R ζ ≤ 1 := by
  unfold farInd; split_ifs <;> norm_num

/-! ### Small deterministic lemmas -/

theorem flowLam_eq_eig (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {ω : FlowSample N}
    (hω : ω.1.IsHermitian) {σ : ℝ} (hσ : a ≤ σ) :
    flowLam F (Real.toNNReal (σ - a)) ω = flowEigenvalue F a ω σ := by
  funext k
  simp only [flowLam, flowH, flowEigenvalue]
  rw [flowMatrix_eq F a hω hσ]

theorem flowLam_add_eq_eig (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {ω : FlowSample N}
    (hω : ω.1.IsHermitian) (t : ℝ≥0) :
    flowLam F t ω = flowEigenvalue F a ω (a + t) := by
  have := flowLam_eq_eig F a hω (σ := a + t) (by have := t.2; linarith)
  rwa [add_sub_cancel_left, Real.toNNReal_coe] at this

theorem momentGenerator_congr_offdiag {c c' : Fin N → Fin N → ℝ}
    (h : ∀ i j, i ≠ j → c i j = c' i j) (f : Occ N → ℝ) (ξ : Occ N) :
    momentGenerator c f ξ = momentGenerator c' f ξ := by
  unfold momentGenerator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  rw [h i j (Ne.symm (mem_erase.1 hj).1)]

theorem IsMomentFlowSolution.congr_rate {c c' : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    {Φ : ℝ → Occ N → ℝ} (hΦ : IsMomentFlowSolution c r s u Φ)
    (h : ∀ x ∈ Ioo s u, ∀ i j, i ≠ j → c x i j = c' x i j) :
    IsMomentFlowSolution c' r s u Φ := fun ξ hξ =>
  ⟨(hΦ ξ hξ).1, fun x hx => by
    rw [← momentGenerator_congr_offdiag (h x hx)]; exact (hΦ ξ hξ).2 x hx⟩

theorem shortFlowRate_eq_cfgRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N)
    (ℓ : ℕ) (σ : ℝ) {i j : Fin N} (hij : i ≠ j) :
    shortFlowRate F a ω ℓ σ i j = cfgRate N (flowEigenvalue F a ω σ) ℓ 0 i j := by
  unfold shortFlowRate maskRate
  by_cases hd : labelDist i j < ℓ
  · rw [ite_eq_left hd, cfgRate_zero_apply _ ℓ hij hd]; rfl
  · rw [ite_eq_right hd]
    unfold cfgRate
    rw [ite_eq_right fun h => hd h.2]

theorem forwardMass_shift_to {M : ℕ} {L : ℝ → Fin M → Fin M → ℝ} {T : ℝ} {v₀ : Fin M → ℝ}
    {v : ℝ → Fin M → ℝ} (hv : ForwardMassSolution L 0 T v₀ v) (s : ℝ) :
    ForwardMassSolution (fun σ => L (σ - s)) s (s + T) v₀ (fun σ => v (σ - s)) := by
  obtain ⟨h0, hc, hd⟩ := hv
  refine ⟨by simp [h0], ?_, fun x hx => ?_⟩
  · exact hc.comp (continuous_sub_right s).continuousOn fun x hx =>
      ⟨show 0 ≤ x - s by linarith [hx.1], show x - s ≤ T by linarith [hx.2]⟩
  · have := hd (x - s) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact HasDerivAt.comp_sub_const x s this

/-- Clamp to `[E - r₀/16, E + r₀/16]`. -/
def clampC (E r₀ x : ℝ) : ℝ := max (E - r₀ / 16) (min (E + r₀ / 16) x)

theorem continuous_clampC (E r₀ : ℝ) : Continuous (clampC E r₀) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clampC_sub_le {E r₀ : ℝ} (hr₀ : 0 ≤ r₀) (x : ℝ) : |clampC E r₀ x - E| ≤ r₀ / 16 := by
  unfold clampC
  rw [abs_le]
  constructor
  · linarith [le_max_left (E - r₀ / 16) (min (E + r₀ / 16) x)]
  · have : min (E + r₀ / 16) x ≤ E + r₀ / 16 := min_le_left _ _
    have : max (E - r₀ / 16) (min (E + r₀ / 16) x) ≤ E + r₀ / 16 :=
      max_le (by linarith) this
    linarith

theorem clampC_eq {E r₀ x : ℝ} (hx : |x - E| ≤ r₀ / 16) : clampC E r₀ x = x := by
  unfold clampC
  rw [abs_le] at hx
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

/-- `cfgWeight` of a continuous weight is continuous in `λ`. -/
theorem continuous_cfgWeight {φ : ℝ → ℝ} (hφ : Continuous φ) (ξ : Occ N) :
    Continuous fun lam : Fin N → ℝ => cfgWeight φ lam ξ := by
  unfold cfgWeight
  exact continuous_finsetProd _ fun m _ => (hφ.comp (continuous_apply m)).pow _

theorem cfgTilted_sumVec {M : ℕ} (K : ℝ) (φ : ℝ → ℝ) (σ : Fin M → Occ N) (t : ℝ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    cfgTilted K φ σ (t, sumVec x y) = Real.exp (-(K * t)) * ∑ q, cfgWeight φ x (σ q) * y q := by
  simp [cfgTilted, sumVec, mlIdx, mvIdx]

/-! ### The quantitative `r`-particle short-row bound -/

/-- **`r`-particle finite speed of propagation, quantitative form.** -/
theorem multi_short_row_quant (r : ℕ) (hIto : SemimartingaleItoFormula (N + sectorCard N r))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s u : ℝ} (has : a < s) (hsu : s ≤ u)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (k : Fin N) {ξ₀ : Occ N} (hξ₀ : ξ₀ ∈ sector N r) (R : ℝ)
    {E r₀ ν d R₀ c₁ C₁ g K δ₀ w e : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR₀ : 0 < R₀)
    (hρ : d + 2 * R₀ ≤ r₀ / 16) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hg : 0 < g) (hK0 : 0 ≤ K)
    (hK : r * (2 * ℓ * (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) +
          (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)) +
        r ^ 2 * ((ν * weightConst) ^ 2 *
          (Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 2 + 1)) / (2 * N) ≤ K)
    (hδ₀ : 0 ≤ δ₀) (hw : 0 < w) (he : 0 < e) (G : Set (FlowSample N))
    (hG : ∀ ω ∈ G, |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 →
      ω.1.IsHermitian ∧
      (∀ σ ∈ Icc s u,
        (∀ i j : Fin N, ℓ ≤ labelDist i j →
          c₁ * labelDist i j / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) ∧
        (∀ i j : Fin N, labelDist i j < ℓ →
          min |flowEigenvalue F a ω σ i - E| |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
          |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| ≤ C₁ * ℓ / N) ∧
        (∀ i j : Fin N, i ≠ j → g < |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)) ∧
      (∀ ζ ∈ sector N r, farCfg k R ζ →
        cfgWeight (rlPhi ν 0 d R₀)
          (fun m => flowEigenvalue F a ω s m - flowEigenvalue F a ω s k) ζ ≤ δ₀) ∧
      w ≤ cfgWeight (rlPhi ν 0 d R₀)
        (fun m => flowEigenvalue F a ω u m - flowEigenvalue F a ω s k) ξ₀) :
    flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = farInd k R ζ) ∧ e < Φ u ξ₀} ≤
      flowLaw N a Gᶜ +
        ENNReal.ofReal (sectorCard N r * δ₀ / (Real.exp (-(K * (u - s))) * w * e)) := by
  classical
  set μ := flowLaw N a with hμ
  have hr₀ : 0 ≤ r₀ := by linarith
  set sL : ℝ≥0 := Real.toNNReal (s - a) with hsLdef
  set T : ℝ≥0 := Real.toNNReal (u - s) with hTdef
  have hsL : (sL : ℝ) = s - a := Real.coe_toNNReal _ (by linarith)
  have hsLpos : 0 < sL := Real.toNNReal_pos.mpr (by linarith)
  have hT : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  set φ := rlPhi ν 0 d R₀ with hφdef
  set c₀ : FlowSample N → ℝ := fun ω => clampC E r₀ (flowLam F sL ω k) with hc₀def
  set σe := sectorEnum N r with hσe
  set A : Set (FlowSample N) := {ω | ∀ q, farCfg k R (σe q) →
    cfgWeight φ (mfLam F sL c₀ 0 ω) (σe q) ≤ δ₀} with hAdef
  set v₀ : FlowSample N → Fin (sectorCard N r) → ℝ :=
    fun ω q => A.indicator (fun _ => farInd k R (σe q)) ω with hv₀def
  set ρ := flowStop F sL ℓ E r₀ c₁ C₁ g with hρdef
  set Kc := Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) with hKc
  have hφc : Continuous φ := (rlPhi_contDiff hd hR₀).continuous
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  have hφle : ∀ z, φ z ≤ 1 := rlPhi_le_one hν hR₀
  -- measurability at the start
  have hlam0 : Measurable[shiftFiltration (flowFiltration N) sL 0] (flowLam F (sL + 0)) :=
    flowLam_adapted F (sL + 0)
  have hle0 : flowFiltration N sL ≤ shiftFiltration (flowFiltration N) sL 0 :=
    (flowFiltration N).mono (le_of_eq (add_zero sL).symm)
  have hc₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] c₀ :=
    ((continuous_clampC E r₀).measurable.comp
      ((measurable_pi_apply k).comp (flowLam_adapted F sL))).mono hle0 le_rfl
  have hmfLam0 : Measurable[shiftFiltration (flowFiltration N) sL 0] (mfLam F sL c₀ 0) := by
    refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) sL 0) _ _ |>.mpr fun m => ?_
    exact ((measurable_pi_apply m).comp hlam0).sub hc₀m
  have hAm : MeasurableSet[shiftFiltration (flowFiltration N) sL 0] A := by
    have : A = ⋂ q, {ω | farCfg k R (σe q) → cfgWeight φ (mfLam F sL c₀ 0 ω) (σe q) ≤ δ₀} := by
      ext ω; simp [hAdef]
    rw [this]
    refine MeasurableSet.iInter fun q => ?_
    by_cases hq : farCfg k R (σe q)
    · simp only [hq, true_imp_iff]
      exact measurableSet_le ((continuous_cfgWeight hφc _).measurable.comp hmfLam0)
        measurable_const
    · simp only [hq, false_imp_iff, Set.ofPred_true]; exact MeasurableSet.univ
  have hv₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] v₀ := by
    refine @measurable_pi_iff (FlowSample N) (Fin (sectorCard N r)) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) sL 0) _ _ |>.mpr fun q => ?_
    exact Measurable.indicator measurable_const hAm
  have hv₀ : ∀ ω q, 0 ≤ v₀ ω q ∧ v₀ ω q ≤ 1 := by
    intro ω q
    simp only [hv₀def, Set.indicator]
    split_ifs
    · exact farInd_mem k R _
    · norm_num
  -- the expectation bound
  have hcomp : ∀ x z, |z - x| ≤ 2 * C₁ * ℓ / N → φ z ≤ Kc * φ x := by
    intro x z hxz
    refine (rlPhi_le_exp_mul hν hd hR₀ x z).trans
      (mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x).le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxz
      (mul_nonneg hν weightConst_pos.le))
  have hgood : ∀ ω (x : ℝ≥0), (x : WithTop ℝ≥0) < ρ ω →
      (∀ i j : Fin N, i ≠ j → g ≤ |flowLam F (sL + x) ω i - flowLam F (sL + x) ω j|) ∧
      (∀ i j : Fin N, j ≠ i → labelDist i j < ℓ →
        |mfLam F sL c₀ x ω j - mfLam F sL c₀ x ω i| ≤ 2 * C₁ * ℓ / N ∨
          (rlPhi1 ν 0 d R₀ (mfLam F sL c₀ x ω i) = 0 ∧
            φ (mfLam F sL c₀ x ω j) = φ (mfLam F sL c₀ x ω i))) ∧
      (∀ i j : Fin N, j ≠ i → ℓ ≤ labelDist i j →
        c₁ / 2 * labelDist i j / N ≤ |flowLam F (sL + x) ω i - flowLam F (sL + x) ω j|) := by
    intro ω x hx
    obtain ⟨h1, h2, h3⟩ := good_before_flowStop hx
    refine ⟨h3, ?_, fun i j _ hij => h1 i j hij⟩
    have hcl := abs_clampC_sub_le (E := E) hr₀ (flowLam F sL ω k)
    refine rlPhi_short_close_or_flat (ν := ν) (E := 0) (d := d) (R := R₀) (r₀ := r₀ / 2)
      (G := 2 * C₁ * ℓ / N) hR₀ (by linarith) (mfLam F sL c₀ x ω) ℓ ?_
    intro i j hij hm
    have hdiff : mfLam F sL c₀ x ω i - mfLam F sL c₀ x ω j =
        flowLam F (sL + x) ω i - flowLam F (sL + x) ω j := by
      simp only [mfLam]; ring
    rw [hdiff]
    refine h2 i j hij ?_
    simp only [mfLam, sub_zero] at hm
    rcases min_le_iff.1 hm with hm | hm
    · refine (min_le_left _ _).trans ?_
      calc |flowLam F (sL + x) ω i - E|
          ≤ |flowLam F (sL + x) ω i - c₀ ω| + |c₀ ω - E| := abs_sub_le _ _ _
        _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
        _ = r₀ / 8 := by ring
    · refine (min_le_right _ _).trans ?_
      calc |flowLam F (sL + x) ω j - E|
          ≤ |flowLam F (sL + x) ω j - c₀ ω| + |c₀ ω - E| := abs_sub_le _ _ _
        _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
        _ = r₀ / 8 := by ring
  have hexp := mf_expectation_le r hIto hStop hDBM hN hF a sL hsLpos ℓ hg hv₀m hv₀ hc₀m
    (rlPhi_hasDerivAt hd hR₀) (rlPhi1_hasDerivAt hd hR₀) (rlPhi_contDiff hd hR₀)
    (fun z => (rlPhi_pos z).le) (rlPhi_le_one hν hR₀) (abs_rlPhi1_le hν hd hR₀)
    (mul_nonneg hν weightConst_pos.le) (abs_rlPhi2_le hν hd hR₀)
    (by have := weightConst_pos; positivity) (Real.exp_pos _).le hcomp (half_pos hc₁) hK0 hK
    ρ (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) hgood T
  -- the initial weighted mass is at most `M δ₀`
  set X : FlowSample N → ℝ := stoppedProcess (fun (x : ℝ≥0) ω => cfgTilted K φ σe
      ((x : ℝ), sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω))) ρ T with hXdef
  have hmass0 : ∀ ω, mfMass F sL ℓ g r v₀ 0 ω = v₀ ω := fun ω =>
    (adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω le_rfl).1
  have hlamY : ∀ (x : ℝ≥0) ω, (fun m => sumVec (mfLam F sL c₀ x ω)
      (mfMass F sL ℓ g r v₀ x ω) (mlIdx m)) = mfLam F sL c₀ x ω := by
    intro x ω; funext m; simp [sumVec, mlIdx]
  have hmassY : ∀ (x : ℝ≥0) ω q, sumVec (mfLam F sL c₀ x ω)
      (mfMass F sL ℓ g r v₀ x ω) (mvIdx q) = mfMass F sL ℓ g r v₀ x ω q := by
    intro x ω q; simp [sumVec, mvIdx]
  have hinit_pt : ∀ ω, cfgTilted K φ σe (0, sumVec (mfLam F sL c₀ 0 ω)
      (mfMass F sL ℓ g r v₀ 0 ω)) ≤ sectorCard N r * δ₀ := by
    intro ω
    rw [cfgTilted_sumVec, hmass0]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    calc ∑ q, cfgWeight φ (mfLam F sL c₀ 0 ω) (σe q) * v₀ ω q ≤ ∑ _q : Fin (sectorCard N r), δ₀ :=
          Finset.sum_le_sum fun q _ => by
            simp only [hv₀def, Set.indicator]
            split_ifs with hωA
            · unfold farInd
              split_ifs with hq
              · rw [mul_one]; exact hωA q hq
              · rw [mul_zero]; exact hδ₀
            · rw [mul_zero]; exact hδ₀
      _ = sectorCard N r * δ₀ := by simp
  have hinit : ∫ ω, cfgTilted K φ σe (0, sumVec (mfLam F sL c₀ 0 ω)
      (mfMass F sL ℓ g r v₀ 0 ω)) ∂μ ≤ sectorCard N r * δ₀ := by
    by_cases hi : Integrable (fun ω => cfgTilted K φ σe (0, sumVec (mfLam F sL c₀ 0 ω)
        (mfMass F sL ℓ g r v₀ 0 ω))) μ
    · calc _ ≤ ∫ _ω, (sectorCard N r * δ₀ : ℝ) ∂μ :=
            integral_mono hi (integrable_const _) hinit_pt
        _ = sectorCard N r * δ₀ := by simp
    · rw [integral_undef hi]; positivity
  have hXint_le : ∫ ω, X ω ∂μ ≤ sectorCard N r * δ₀ := hexp.trans hinit
  -- integrability and nonnegativity of the stopped value
  have hYc : ∀ ω, Continuous fun x : ℝ≥0 =>
      sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω) := fun ω =>
    continuous_sumVec.comp ((continuous_pi fun m => ((continuous_apply m).comp
      ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))).sub
      continuous_const).prodMk (adaptedMass_continuous (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω))
  have hYa : ∀ x, Measurable[shiftFiltration (flowFiltration N) sL x]
      (fun ω => sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω)) := by
    intro x
    have h1 : Measurable[shiftFiltration (flowFiltration N) sL x] (mfLam F sL c₀ x) := by
      refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
        (shiftFiltration (flowFiltration N) sL x) _ _ |>.mpr fun m => ?_
      exact ((measurable_pi_apply m).comp (flowLam_adapted F (sL + x))).sub
        (hc₀m.mono ((shiftFiltration (flowFiltration N) sL).mono (zero_le (a := x))) le_rfl)
    have h2 := adaptedMass_measurable (shiftFiltration (flowFiltration N) sL)
      (mfCoeff_adapted hN F sL ℓ hg r) (mfCoeff_continuous hN hF sL ℓ hg r) hv₀m x
    exact continuous_sumVec.measurable.comp (h1.prodMk h2)
  have hΦcont : Continuous (cfgTilted (N := N) (M := sectorCard N r) K φ σe) :=
    (cfgTilted_contDiff (rlPhi_contDiff hd hR₀)).continuous
  have hpt0 : ∀ (x : ℝ≥0) ω, 0 ≤ cfgTilted K φ σe
      ((x : ℝ), sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω)) := by
    intro x ω
    rw [cfgTilted_sumVec]
    refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun q _ => mul_nonneg
      (cfgWeight_nonneg hφ0 _ _)
      (mfMass_mem_unit hN hF sL ℓ hg r hv₀ x ω q).1)
  have hptbd : ∀ (x : ℝ≥0) ω, cfgTilted K φ σe
      ((x : ℝ), sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω)) ≤ sectorCard N r := by
    intro x ω
    rw [cfgTilted_sumVec]
    have hexp1 : Real.exp (-(K * x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg x; nlinarith)
    have hs0 : 0 ≤ ∑ q, cfgWeight φ (mfLam F sL c₀ x ω) (σe q) * mfMass F sL ℓ g r v₀ x ω q :=
      Finset.sum_nonneg fun q _ => mul_nonneg
        (cfgWeight_nonneg hφ0 _ _)
        (mfMass_mem_unit hN hF sL ℓ hg r hv₀ x ω q).1
    have hs1 : ∑ q, cfgWeight φ (mfLam F sL c₀ x ω) (σe q) * mfMass F sL ℓ g r v₀ x ω q ≤
        sectorCard N r := by
      calc _ ≤ ∑ _q : Fin (sectorCard N r), (1 : ℝ) := Finset.sum_le_sum fun q _ => by
            have hW := cfgWeight_le_pow hφ0 hφle
              (mfLam F sL c₀ x ω) (sectorEnum_mem r q)
            rw [one_pow] at hW
            have hm := mfMass_mem_unit hN hF sL ℓ hg r hv₀ x ω q
            calc _ ≤ 1 * 1 := mul_le_mul hW hm.2 hm.1 zero_le_one
              _ = 1 := one_mul 1
        _ = sectorCard N r := by simp
    calc _ ≤ 1 * (sectorCard N r : ℝ) := mul_le_mul hexp1 hs1 hs0 zero_le_one
      _ = sectorCard N r := one_mul _
  have hXa : ∀ x, StronglyMeasurable[shiftFiltration (flowFiltration N) sL x]
      (fun ω => cfgTilted K φ σe
        ((x : ℝ), sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω))) := fun x =>
    (hΦcont.measurable.comp (measurable_const.prodMk (hYa x))).stronglyMeasurable
  have hXc : ∀ ω, Continuous fun x : ℝ≥0 => cfgTilted K φ σe
      ((x : ℝ), sumVec (mfLam F sL c₀ x ω) (mfMass F sL ℓ g r v₀ x ω)) := fun ω =>
    hΦcont.comp (NNReal.continuous_coe.prodMk (hYc ω))
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  have hm := hprog.stronglyMeasurable_stoppedProcess
    (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) T
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by simp only [hXdef, stoppedProcess]; exact hpt0 _ ω
  have hXint : Integrable X μ :=
    Integrable.of_bound hm.aestronglyMeasurable (sectorCard N r)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
        simp only [hXdef, stoppedProcess]; exact hptbd _ ω)
  -- Markov
  set θ := Real.exp (-(K * (u - s))) * w * e with hθ
  have hθpos : 0 < θ := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hX0) hXint θ
  have hmeas : μ {ω | θ ≤ X ω} ≤
      ENNReal.ofReal (sectorCard N r * δ₀ / θ) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hθpos]
    have : θ * μ.real {ω | θ ≤ X ω} ≤ sectorCard N r * δ₀ := hmk.trans hXint_le
    rw [measureReal_def] at this
    linarith
  -- containment
  have hsub : {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = farInd k R ζ) ∧ e < Φ u ξ₀} ⊆
      Gᶜ ∪ {ω | θ ≤ X ω} := by
    rintro ω ⟨hbulk, Φ, hΦ, hΦ0, hΦu⟩
    by_cases hωG : ω ∈ G
    swap
    · exact Or.inl hωG
    right
    obtain ⟨hH, hcl, hfarW, hwW⟩ := hG ω hωG hbulk
    have hlamS : flowLam F sL ω = flowEigenvalue F a ω s := flowLam_eq_eig F a hH has.le
    have hc0 : c₀ ω = flowEigenvalue F a ω s k := by
      simp only [hc₀def, hlamS]; exact clampC_eq hbulk
    have hlam_t : ∀ x : ℝ≥0, flowLam F (sL + x) ω = flowEigenvalue F a ω (s + x) := by
      intro x
      rw [flowLam_add_eq_eig F a hH, NNReal.coe_add, hsL]
      congr 1; ring
    have hmfLam : ∀ x : ℝ≥0, mfLam F sL c₀ x ω =
        fun m => flowEigenvalue F a ω (s + x) m - flowEigenvalue F a ω s k := by
      intro x; funext m; simp only [mfLam, hlam_t x, hc0]
    have hωA : ω ∈ A := by
      intro q hq
      rw [hmfLam 0]
      simp only [NNReal.coe_zero, add_zero]
      exact hfarW (σe q) (sectorEnum_mem r q) hq
    -- the stopping time is not reached before `T`
    have hρT : ¬ ρ ω ≤ T := by
      have hiff := hitTime_le_iff (X := fun x ω => flowLam F (sL + x) ω)
        (K := stopSet N ℓ E r₀ c₁ C₁ g) (ω := ω)
        ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))
        ((isClosed_failSet N ℓ E r₀ c₁ C₁).union (isClosed_gapSet N g)) T
      rw [hρdef, flowStop, hiff]
      rintro ⟨x, hxT, hx⟩
      simp only [stopSet, Set.mem_union] at hx
      have hxT' : (x : ℝ) ≤ u - s := by rw [← hT]; exact_mod_cast hxT
      have hσ : s + (x : ℝ) ∈ Icc s u := ⟨by linarith [x.2], by linarith⟩
      obtain ⟨h1, h2, h3⟩ := hcl _ hσ
      simp only [hlam_t x] at hx
      rcases hx with hx | hx
      · exact not_mem_failSet_of_clauses hℓ hc₁ hC₁ hN h1 h2 hx
      · obtain ⟨i, j, hij, hle⟩ := hx
        exact absurd hle (not_le.mpr (h3 i j hij))
    have hTρ : (T : WithTop ℝ≥0) ≤ ρ ω := (lt_of_not_ge hρT).le
    have hXω : X ω = cfgTilted K φ σe
        ((T : ℝ), sumVec (mfLam F sL c₀ T ω) (mfMass F sL ℓ g r v₀ T ω)) := by
      simp only [hXdef, stoppedProcess, min_eq_left hTρ]
      rfl
    -- uniqueness: `Φ u ξ₀` is the adapted mass
    set Lc := mfCoeff F sL ℓ g r with hLc
    have hsol := adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω
      (T := u - s) (by linarith)
    have hsh := forwardMass_shift_to hsol s
    have hsu' : s + (u - s) = u := by ring
    rw [hsu'] at hsh
    have hmf := isMomentFlowSolution_of_forwardMass
      (c := fun σ => cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g) hsh
    have hmf' : IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u
        (fun σ => cfgExt r (adaptedMass Lc v₀ (σ - s) ω)) := by
      refine hmf.congr_rate fun σ hσ i j hij => ?_
      have hσs : ((Real.toNNReal (σ - s) : ℝ≥0) : ℝ) = σ - s :=
        Real.coe_toNNReal _ (by linarith [hσ.1])
      have hl : flowLam F (sL + Real.toNNReal (σ - s)) ω = flowEigenvalue F a ω σ := by
        rw [hlam_t, hσs]; congr 1; ring
      show cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g i j = _
      rw [hl, shortFlowRate_eq_cfgRate F a ω ℓ σ hij]
      have hgap := (hcl σ ⟨hσ.1.le, hσ.2.le⟩).2.2
      rw [cfgRate_eq_zero_gap hg.le fun i j h => (hgap i j h).le]
    have h0 : ∀ ζ ∈ sector N r, Φ s ζ = cfgExt r (adaptedMass Lc v₀ (s - s) ω) ζ := by
      intro ζ hζ
      rw [sub_self, hΦ0 ζ hζ, cfgExt_of_mem _ hζ]
      have : adaptedMass Lc v₀ 0 ω = v₀ ω := hsol.1
      rw [this]
      simp only [hv₀def, Set.indicator_of_mem hωA, sectorEnum_index hζ, hσe]
    have heq := hΦ.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hmf'
      h0 u ⟨hsu, le_rfl⟩ ξ₀ hξ₀
    have hΦval : Φ u ξ₀ = mfMass F sL ℓ g r v₀ T ω (sectorIndex hξ₀) := by
      rw [heq, cfgExt_of_mem _ hξ₀]
      simp only [mfMass, hT, hLc]
    -- the lower bound at the terminal time
    have hWξ : w ≤ cfgWeight φ (mfLam F sL c₀ T ω) (σe (sectorIndex hξ₀)) := by
      rw [hσe, sectorEnum_index hξ₀, hmfLam T, hT]
      have : s + (u - s) = u := by ring
      rw [this]; exact hwW
    show θ ≤ X ω
    rw [hXω, cfgTilted_sumVec]
    have hterm : cfgWeight φ (mfLam F sL c₀ T ω) (σe (sectorIndex hξ₀)) *
        mfMass F sL ℓ g r v₀ T ω (sectorIndex hξ₀) ≤
        ∑ q, cfgWeight φ (mfLam F sL c₀ T ω) (σe q) * mfMass F sL ℓ g r v₀ T ω q :=
      Finset.single_le_sum (f := fun q => cfgWeight φ (mfLam F sL c₀ T ω) (σe q) *
          mfMass F sL ℓ g r v₀ T ω q)
        (fun q _ => mul_nonneg (cfgWeight_nonneg hφ0 _ _)
          (mfMass_mem_unit hN hF sL ℓ hg r hv₀ T ω q).1) (Finset.mem_univ _)
    rw [← hΦval] at hterm
    rw [hT]
    have hΦpos : 0 ≤ Φ u ξ₀ := le_of_lt (lt_trans he hΦu)
    calc θ = Real.exp (-(K * (u - s))) * (w * e) := by rw [hθ]; ring
      _ ≤ Real.exp (-(K * (u - s))) *
          (cfgWeight φ (mfLam F sL c₀ T ω) (σe (sectorIndex hξ₀)) * Φ u ξ₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul hWξ hΦu.le he.le (hw.le.trans hWξ)
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
  calc μ _ ≤ μ (Gᶜ ∪ {ω | θ ≤ X ω}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ {ω | θ ≤ X ω} := measure_union_le _ _
    _ ≤ μ Gᶜ + ENNReal.ofReal (sectorCard N r * δ₀ / θ) := add_le_add le_rfl hmeas

end BlockBand.Palm.MomentFlow
