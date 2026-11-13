module

public import BlockBand.Palm.MomentFlow.MultiIto
public import BlockBand.Palm.RelativeLocalizationStopped

/-!
# `r`-particle finite speed: stopped Itô and the tilted Gronwall inequality in mean

The `r`-particle analogue of `flow_tilted_expectation_le`, applied to the short moment flow.

Setting: start `s > 0` (flow time `a + s`), filtration
`𝓖' = shiftFiltration (flowFiltration N) s`, gap level `g > 0`, `M = sectorCard N r`.

* `mfCoeff`: the matrix of the truncated short moment generator `𝓢` on the `r`-particle sector
  along the eigenvalue path `flowLam F (s+u)`; continuous in `u` for every sample, `𝓖'`-adapted.
* `mfMass = adaptedMass mfCoeff v₀` (adapted solution of the `r`-particle short flow);
  `mfMass_mem_unit` (`v₀ ∈ [0,1] ⇒ v ∈ [0,1]`).
* `mf_state_semimartingale` (`DysonBrownianMotion` (b2) via `flowLam_semimartingale`):
  `(λ(s+u) - c₀, v(u))` is a continuous semimartingale in `ℝ^{N+M}` with covariance `cfgCov N M`.
* `mf_expectation_le` (**stopped Itô + Gronwall in mean**, hypotheses
  `SemimartingaleItoFormula (N+M)`, `StoppedSemimartingale 1`, `DysonBrownianMotion N`): for every
  `𝓖'`-stopping time `ρ` before which all gaps are `≥ g`, short pairs are close or flat for the
  weight, and the long-gap clause holds, and `K ≥ κ_r`,
  `E[e^{-K(T∧ρ)} Σ_ξ W_φ(λ(s+T∧ρ) - c₀, ξ) v_ξ(T∧ρ)] ≤ E[Σ_ξ W_φ(λ(s) - c₀, ξ) v₀_ξ]`.
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

/-! ### Shift invariance -/

theorem mf_sub_const {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (hY : IsContinuousSemimartingale Q 𝓖 Y β α)
    {c : Ω → Fin d → ℝ} (hc : StronglyMeasurable[𝓖 0] c) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => Y t ω - c ω) β α := by
  obtain ⟨τ, hτ, hτlim, hloc⟩ := hY.localizing
  have hcs : ∀ t, StronglyMeasurable[Subtype.instMeasurableSpace.prod (𝓖 t)]
      fun p : Set.Iic t × Ω => c p.2 :=
    fun t => (hc.mono (𝓖.mono (zero_le (a := t)))).comp_measurable measurable_snd
  refine ⟨fun t => (hY.adapted t).sub (hc.mono (𝓖.mono (zero_le (a := t)))),
    fun t => (hY.progressive t).sub (hcs t), ?_, hY.drift_progressive, hY.cov_progressive,
    hY.integrable, ⟨τ, hτ, hτlim, fun n => ⟨fun i => ?_, fun i j => ?_⟩⟩⟩
  · filter_upwards [hY.continuous] with ω hω using hω.sub continuous_const
  · refine hasMartingaleModification_congr ?_ ((hloc n).1 i)
    funext t ω; simp only [stoppedProcess, smCompensated, Pi.sub_apply]; ring
  · refine hasMartingaleModification_congr ?_ ((hloc n).2 i j)
    funext t ω; simp only [stoppedProcess, smCompensated, Pi.sub_apply]; ring

theorem mf_dysonDrift_sub_const (lam : Fin N → ℝ) (c : ℝ) (k : Fin N) :
    dysonDrift N (fun l => lam l - c) k = dysonDrift N lam k := by
  unfold dysonDrift; congr 1
  exact Finset.sum_congr rfl fun j _ => by ring_nf

theorem cfgRate_sub_const (lam : Fin N → ℝ) (ℓ : ℕ) (g c : ℝ) :
    cfgRate N (fun l => lam l - c) ℓ g = cfgRate N lam ℓ g := by
  funext i j
  simp only [cfgRate, sub_sub_sub_cancel_right]

/-! ### Coefficients and mass -/

/-- The truncated short `r`-particle generator on the sector along the path from `s`. -/
def mfCoeff (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ) (u : ℝ≥0)
    (ω : FlowSample N) : Fin (sectorCard N r) → Fin (sectorCard N r) → ℝ :=
  cfgMat (cfgRate N (flowLam F (s + u) ω) ℓ g) r

theorem mfCoeff_continuous (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (s : ℝ≥0) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ) (ω : FlowSample N) :
    Continuous fun u => mfCoeff F s ℓ g r u ω :=
  continuous_cfgMat_comp ((continuous_cfgRate hN ℓ hg).comp
    ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))) r

theorem mfCoeff_adapted (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) {g : ℝ}
    (hg : 0 < g) (r : ℕ) (u : ℝ≥0) :
    Measurable[shiftFiltration (flowFiltration N) s u] (mfCoeff F s ℓ g r u) :=
  (continuous_cfgMat_comp (continuous_cfgRate hN ℓ hg) r).measurable.comp
    (flowLam_adapted F (s + u))

/-- The adapted `r`-particle mass. -/
def mfMass (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (u : ℝ≥0) (ω : FlowSample N) :
    Fin (sectorCard N r) → ℝ :=
  adaptedMass (mfCoeff F s ℓ g r) v₀ (u : ℝ) ω

theorem mfMass_isSubGenerator (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (g : ℝ)
    (r : ℕ) (ω : FlowSample N) (a b : ℝ) :
    IsSubGenerator (realCoeff (mfCoeff F s ℓ g r) ω) a b :=
  cfgMat_isSubGenerator (c := fun x => cfgRate N (flowLam F (s + x.toNNReal) ω) ℓ g)
    (fun _ i j _ => cfgRate_nonneg _ ℓ g i j) r a b

theorem mfMass_mem_unit (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (s : ℝ≥0) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ)
    {v₀ : FlowSample N → Fin (sectorCard N r) → ℝ} (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    (u : ℝ≥0) (ω : FlowSample N) (k : Fin (sectorCard N r)) :
    0 ≤ mfMass F s ℓ g r v₀ u ω k ∧ mfMass F s ℓ g r v₀ u ω k ≤ 1 := by
  have hc := mfCoeff_continuous hN hF s ℓ hg r
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg u)
  have hsub := mfMass_isSubGenerator F s ℓ g r ω 0 u
  have hmem : (u : ℝ) ∈ Icc 0 (u : ℝ) := ⟨NNReal.coe_nonneg u, le_rfl⟩
  exact ⟨forwardMass_nonneg hsub hsol (fun k => (hv₀ ω k).1) u hmem k,
    forwardMass_le_const hsub hsol zero_le_one (fun k => (hv₀ ω k).2) u hmem k⟩

theorem mfMass_compensated_zero (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (s : ℝ≥0) (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ)
    (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (ω : FlowSample N) (t : ℝ≥0)
    (i : Fin (sectorCard N r)) :
    smCompensated (mfMass F s ℓ g r v₀)
      (fun u ω => matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω)) i t ω = 0 := by
  have hc := mfCoeff_continuous hN hF s ℓ hg r
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg t)
  have hrepr := forwardMass_integral (realCoeff_continuous hc ω).continuousOn hsol
    ⟨NNReal.coe_nonneg t, le_rfl⟩
  have h0 : mfMass F s ℓ g r v₀ 0 ω = v₀ ω := hsol.1
  have hint : IntervalIntegrable
      (fun x => matAct (realCoeff (mfCoeff F s ℓ g r) ω x)
        (adaptedMass (mfCoeff F s ℓ g r) v₀ x ω)) volume 0 t :=
    (continuousOn_matAct (realCoeff_continuous hc ω).continuousOn hsol.2.1).intervalIntegrable_of_Icc
      (NNReal.coe_nonneg t)
  have hcomp := congrArg (fun x : Fin (sectorCard N r) → ℝ => x i) hrepr
  simp only [Pi.add_apply] at hcomp
  have hproj : (∫ x in (0 : ℝ)..t, matAct (realCoeff (mfCoeff F s ℓ g r) ω x)
      (adaptedMass (mfCoeff F s ℓ g r) v₀ x ω)) i =
      ∫ x in (0 : ℝ)..t, matAct (realCoeff (mfCoeff F s ℓ g r) ω x)
        (adaptedMass (mfCoeff F s ℓ g r) v₀ x ω) i := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (sectorCard N r) => ℝ)
      i).intervalIntegral_comp_comm hint
    simpa using this.symm
  rw [hproj, intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at hcomp
  unfold smCompensated
  rw [h0]
  have hcongr : ∫ x in Set.Ioc (0 : ℝ) t, matAct (mfCoeff F s ℓ g r x.toNNReal ω)
      (mfMass F s ℓ g r v₀ x.toNNReal ω) i =
      ∫ x in Set.Ioc (0 : ℝ) t, matAct (realCoeff (mfCoeff F s ℓ g r) ω x)
          (adaptedMass (mfCoeff F s ℓ g r) v₀ x ω) i := by
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [mfMass, realCoeff, Real.coe_toNNReal _ hx.1.le]
  rw [hcongr]
  change mfMass F s ℓ g r v₀ t ω i - v₀ ω i - _ = 0
  simp only [mfMass] at hcomp ⊢
  linarith

/-- The centred eigenvalue path `λ(s+u) - c₀`. -/
def mfLam (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (c₀ : FlowSample N → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : Fin N → ℝ :=
  fun k => flowLam F (s + u) ω k - c₀ ω

/-- **State semimartingale** `(λ(s+u) - c₀, v(u))` in `ℝ^{N+M}`. -/
theorem mf_state_semimartingale (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ) {v₀ : FlowSample N → Fin (sectorCard N r) → ℝ}
    (hv₀ : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) s 0] c₀) :
    IsContinuousSemimartingale (flowLaw N a) (shiftFiltration (flowFiltration N) s)
      (fun u ω => sumVec (mfLam F s c₀ u ω) (mfMass F s ℓ g r v₀ u ω))
      (fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
        (matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω)))
      (fun _ _ => cfgCov N (sectorCard N r)) := by
  have hc := mfCoeff_continuous hN hF s ℓ hg r
  have hadC := mfCoeff_adapted hN F s ℓ hg r
  have hZa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (mfMass F s ℓ g r v₀ u) :=
    fun u => adaptedMass_measurable (shiftFiltration (flowFiltration N) s) hadC hc hv₀ u
  have hZc : ∀ ω, Continuous fun u => mfMass F s ℓ g r v₀ u ω := fun ω =>
    adaptedMass_continuous hc v₀ ω
  have hγc : ∀ ω, Continuous fun u =>
      matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω) := by
    intro ω
    refine continuous_pi fun k => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_apply l).comp ((continuous_apply k).comp (hc ω))).mul
      ((continuous_apply l).comp (hZc ω))
  have hγa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (fun ω => matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω)) := by
    intro u
    refine @measurable_pi_iff (FlowSample N) (Fin (sectorCard N r)) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) s u) _ _ |>.mpr fun k => ?_
    refine Finset.measurable_sum _ fun l _ => ?_
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hadC u))).mul
      ((measurable_pi_apply l).comp (hZa u))
  have hcv : StronglyMeasurable[shiftFiltration (flowFiltration N) s 0]
      (fun ω (_ : Fin N) => c₀ ω) :=
    (@measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) s 0) _ _ |>.mpr fun _ => hc₀).stronglyMeasurable
  have hY := mf_sub_const (flowLam_semimartingale hDBM hF a s hs) hcv
  have h := IsContinuousSemimartingale.appendFV hY (Z := mfMass F s ℓ g r v₀)
    (γ := fun u ω => matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω))
    (fun u => (hZa u).stronglyMeasurable)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hZa u).stronglyMeasurable) hZc)
    (Eventually.of_forall hZc)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hγa u).stronglyMeasurable) hγc)
    (Eventually.of_forall fun ω t i =>
      (((continuous_apply i).comp ((hγc ω).comp continuous_real_toNNReal))).integrableOn_Ioc)
    (Eventually.of_forall fun ω t i => mfMass_compensated_zero hN hF s ℓ hg r v₀ ω t i)
  exact h

/-! ### The drift inequality at a state -/

/-- The summed drift inequality in the enumeration coordinates of `itoDrift_cfgTilted_nonpos`. -/
theorem mf_Q_le (lam : Fin N → ℝ) (ℓ : ℕ) (r : ℕ) (vv : Fin (sectorCard N r) → ℝ)
    (hvv : ∀ q, 0 ≤ vv q)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B Kc G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hKc0 : 0 ≤ Kc)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ Kc * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k) = 0 ∧ φ (lam l) = φ (lam k)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    ∑ q, cfgWeight φ lam (sectorEnum N r q) *
          ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam (sectorEnum N r q) i +
          cfgD2 φ φ1 φ2 lam (sectorEnum N r q) i / (2 * N)) ≤
      (r * (2 * ℓ * B * Kc / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (Kc ^ 2 + 1)) / (2 * N)) *
        ∑ q, cfgWeight φ lam (sectorEnum N r q) * vv q := by
  have hext : ∀ q, vv q = cfgExt r vv (sectorEnum N r q) := fun q => (cfgExt_enum r vv q).symm
  have hact : ∀ q, ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) (sectorEnum N r q) := by
    intro q
    rw [← cfgMat_act]
    exact Finset.sum_congr rfl fun q' _ => by rw [cfgExt_enum]
  have hv : ∀ ξ ∈ sector N r, 0 ≤ cfgExt r vv ξ := fun ξ hξ => by
    rw [cfgExt_of_mem vv hξ]; exact hvv _
  have h := cfg_drift_le lam ℓ hφ hφ1 hφ0 hA hA0 hB hB0 hKc0 hcomp hc₁ hshort hlong r
    (cfgExt r vv) hv
  have e1 : ∑ q, cfgWeight φ lam (sectorEnum N r q) *
        ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      ∑ ξ ∈ sector N r, cfgWeight φ lam ξ * momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [hact]).trans (sum_sectorEnum r (fun ξ =>
      cfgWeight φ lam ξ * momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ))
  have e2 : ∑ q, vv q * ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam (sectorEnum N r q) i +
          cfgD2 φ φ1 φ2 lam (sectorEnum N r q) i / (2 * N)) =
      ∑ ξ ∈ sector N r, cfgExt r vv ξ * ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i +
          cfgD2 φ φ1 φ2 lam ξ i / (2 * N)) :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans (sum_sectorEnum r (fun ξ =>
      cfgExt r vv ξ * ∑ i, (dysonDrift N lam i * cfgD1 φ φ1 lam ξ i +
          cfgD2 φ φ1 φ2 lam ξ i / (2 * N))))
  have e3 : ∑ q, cfgWeight φ lam (sectorEnum N r q) * vv q =
      ∑ ξ ∈ sector N r, cfgWeight φ lam ξ * cfgExt r vv ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans (sum_sectorEnum r (fun ξ =>
      cfgWeight φ lam ξ * cfgExt r vv ξ))
  rw [e1, e2, e3]
  exact h

/-! ### Stopped Itô and Gronwall in mean -/

/-- **`r`-particle stopped Itô + tilted Gronwall in mean.** -/
theorem mf_expectation_le (r : ℕ) (hIto : SemimartingaleItoFormula (N + sectorCard N r))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin (sectorCard N r) → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) s 0] c₀)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    (hφc : ContDiff ℝ 2 φ) {A B Kc G c₁ M₀ K : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M₀)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B)
    (hKc0 : 0 ≤ Kc) (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ Kc * φ x) (hc₁ : 0 < c₁)
    (hK0 : 0 ≤ K)
    (hK : r * (2 * ℓ * B * Kc / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (Kc ^ 2 + 1)) / (2 * N) ≤ K)
    (ρ : FlowSample N → WithTop ℝ≥0)
    (hρst : IsStoppingTime (shiftFiltration (flowFiltration N) s) ρ)
    (hgood : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      (∀ k l : Fin N, k ≠ l → g ≤ |flowLam F (s + u) ω k - flowLam F (s + u) ω l|) ∧
      (∀ k l : Fin N, l ≠ k → labelDist k l < ℓ →
        |mfLam F s c₀ u ω l - mfLam F s c₀ u ω k| ≤ G ∨
          (φ1 (mfLam F s c₀ u ω k) = 0 ∧ φ (mfLam F s c₀ u ω l) = φ (mfLam F s c₀ u ω k))) ∧
      (∀ k l : Fin N, l ≠ k → ℓ ≤ labelDist k l →
        c₁ * labelDist k l / N ≤ |flowLam F (s + u) ω k - flowLam F (s + u) ω l|))
    (T : ℝ≥0) :
    ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => cfgTilted K φ (sectorEnum N r)
        ((u : ℝ), sumVec (mfLam F s c₀ u ω) (mfMass F s ℓ g r v₀ u ω))) ρ T ω
        ∂flowLaw N a ≤
      ∫ ω, cfgTilted K φ (sectorEnum N r)
        (0, sumVec (mfLam F s c₀ 0 ω) (mfMass F s ℓ g r v₀ 0 ω)) ∂flowLaw N a := by
  set Y : ℝ≥0 → FlowSample N → Fin (N + sectorCard N r) → ℝ :=
    fun u ω => sumVec (mfLam F s c₀ u ω) (mfMass F s ℓ g r v₀ u ω) with hYdef
  set Bd : ℝ≥0 → FlowSample N → Fin (N + sectorCard N r) → ℝ :=
    fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
      (matAct (mfCoeff F s ℓ g r u ω) (mfMass F s ℓ g r v₀ u ω)) with hBdef
  set Φ := cfgTilted (N := N) (M := sectorCard N r) K φ (sectorEnum N r) with hΦ
  have hY := mf_state_semimartingale hDBM hN hF a s hs ℓ hg r hv₀m hc₀
  have hΦc : ContDiff ℝ 2 Φ := cfgTilted_contDiff hφc
  have hI := hIto (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) Y Bd
    (fun _ _ => cfgCov N (sectorCard N r)) hY Set.univ isOpen_univ (Eventually.of_forall fun _ _ => trivial) Φ
    (hΦc.continuous.measurable) hΦc.contDiffOn
  have hS := hStop (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) _ _ _ hI
    ρ hρst
  have hM0 : 0 ≤ M₀ := (hφ0 0).trans (hφM 0)
  have hlamY : ∀ u ω, (fun m => Y u ω (mlIdx m)) = mfLam F s c₀ u ω := by
    intro u ω; funext m; simp [hYdef, sumVec, mlIdx]
  have hmassY : ∀ u ω q, Y u ω (mvIdx q) = mfMass F s ℓ g r v₀ u ω q := by
    intro u ω q; simp [hYdef, sumVec, mvIdx]
  have hbd : ∀ (u : ℝ≥0) ω, |Φ ((u : ℝ), Y u ω)| ≤ (sectorCard N r) * M₀ ^ r := by
    intro u ω
    have hv := mfMass_mem_unit hN hF s ℓ hg r hv₀ u ω
    have hexp : Real.exp (-(K * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg u; nlinarith)
    have hsum0 : 0 ≤ ∑ q, cfgWeight φ (fun m => Y u ω (mlIdx m)) (sectorEnum N r q) *
        Y u ω (mvIdx q) :=
      Finset.sum_nonneg fun q _ => mul_nonneg (cfgWeight_nonneg hφ0 _ _) (by
        rw [hmassY]; exact (hv q).1)
    have hsum1 : ∑ q, cfgWeight φ (fun m => Y u ω (mlIdx m)) (sectorEnum N r q) *
        Y u ω (mvIdx q) ≤ (sectorCard N r) * M₀ ^ r := by
      calc _ ≤ ∑ _q : Fin (sectorCard N r), M₀ ^ r := Finset.sum_le_sum fun q _ => by
            rw [hmassY]
            calc _ ≤ M₀ ^ r * 1 := mul_le_mul
                  (cfgWeight_le_pow hφ0 hφM _ (sectorEnum_mem r q)) (hv q).2 (hv q).1
                  (pow_nonneg hM0 r)
              _ = M₀ ^ r := mul_one _
        _ = (sectorCard N r) * M₀ ^ r := by simp
    simp only [hΦ, cfgTilted]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum0)]
    calc _ ≤ 1 * ((sectorCard N r) * M₀ ^ r) := mul_le_mul hexp hsum1 hsum0 zero_le_one
      _ = (sectorCard N r) * M₀ ^ r := one_mul _
  have hdrift : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      itoDrift Φ (Y u ω) u (Bd u ω) (cfgCov N (sectorCard N r)) ≤ 0 := by
    intro ω u hu
    obtain ⟨hgap, hsh, hlg⟩ := hgood ω u hu
    have hv := mfMass_mem_unit hN hF s ℓ hg r hv₀ u ω
    have hrate : cfgRate N (flowLam F (s + u) ω) ℓ g = cfgRate N (mfLam F s c₀ u ω) ℓ 0 := by
      rw [cfgRate_eq_zero_gap hg.le hgap]
      exact (cfgRate_sub_const _ ℓ 0 _).symm
    have hQ := mf_Q_le (mfLam F s c₀ u ω) ℓ r (mfMass F s ℓ g r v₀ u ω) (fun q => (hv q).1)
      hφ hφ1 hφ0 hA hA0 hB hB0 hKc0 hcomp hc₁ hsh
      (fun k l hlk hd => by
        have := hlg k l hlk hd
        simpa only [mfLam, sub_sub_sub_cancel_right] using this)
    refine itoDrift_cfgTilted_nonpos hφ hφ1 hφc (Y u ω) u (mfCoeff F s ℓ g r u ω) hK ?_ ?_
      (Bd u ω) (fun i => ?_) (fun q => ?_)
    · exact Finset.sum_nonneg fun q _ => mul_nonneg (cfgWeight_nonneg hφ0 _ _) (by
        rw [hmassY]; exact (hv q).1)
    · simp only [hlamY, hmassY, mfCoeff, hrate]
      exact hQ
    · rw [hlamY]
      simp only [hBdef, sumVec, mlIdx, Equiv.symm_apply_apply, Sum.elim_inl]
      exact (mf_dysonDrift_sub_const _ _ i).symm
    · simp only [hBdef, hmassY]
      simp [sumVec, mvIdx, matAct]
  have hβ : ∀ᵐ ω ∂flowLaw N a, ∀ r' : ℝ≥0, ∫ x in Set.Ioc (0 : ℝ) r',
      switchAfter ρ (fun t ω (_ : Fin 1) => itoDrift Φ (Y t ω) t (Bd t ω) (cfgCov N (sectorCard N r)))
        x.toNNReal ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω r' => setIntegral_nonpos_of_ae_restrict ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Measure.ae_ne volume (((ρ ω).untopA : ℝ≥0) : ℝ)] with x hx hxI
    have hx0 : 0 < x := hxI.1
    simp only [switchAfter, Pi.zero_apply]
    split_ifs with hle
    · refine hdrift ω x.toNNReal (lt_of_le_of_ne hle fun heq => hx ?_)
      cases hρω : ρ ω with
      | top => rw [hρω] at heq; exact absurd heq WithTop.coe_ne_top
      | coe p =>
        rw [hρω] at heq
        have := WithTop.coe_injective heq
        change x = ((p : ℝ≥0) : ℝ)
        rw [← this, Real.coe_toNNReal _ hx0.le]
    · exact le_rfl
  have hfin := integral_le_of_drift_nonpos (flowLaw N a) (shiftFiltration (flowFiltration N) s)
    _ _ _ hS (C := (sectorCard N r) * M₀ ^ r) (fun t ω => hbd _ ω) hβ T
  have e0 : ∀ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0 =
      Φ (0, sumVec (mfLam F s c₀ 0 ω) (mfMass F s ℓ g r v₀ 0 ω)) := by
    intro ω
    have hm : min ((0 : ℝ≥0) : WithTop ℝ≥0) (ρ ω) = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      min_eq_left (by rw [WithTop.coe_zero]; exact zero_le (a := ρ ω))
    simp only [stoppedProcess]
    rw [hm]
    have hu : ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopA : ℝ≥0) = 0 := rfl
    rw [hu]
    simp only [hYdef, NNReal.coe_zero]
  calc ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => Φ ((u : ℝ), Y u ω)) ρ T ω ∂flowLaw N a
      = ∫ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ T ω 0
          ∂flowLaw N a := rfl
    _ ≤ ∫ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0
          ∂flowLaw N a := hfin
    _ = _ := integral_congr_ae (Eventually.of_forall e0)

end BlockBand.Palm.MomentFlow
