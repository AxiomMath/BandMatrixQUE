module

public import BlockBand.Palm.MomentFlow.MultiItoGen

/-!
# Stopped Itô formula and Gronwall in mean for a generic weight with fixed centres

* `gen_state_semimartingale` (from `DysonBrownianMotion`): `(λ(s+u), c₀, v(u))` is a
  continuous semimartingale in `ℝ^{N+(r+M)}` with covariance `gCov N r M`;
* `gen_mf_expectation_le` (from `SemimartingaleItoFormula`, `StoppedSemimartingale 1`): for every
  `𝓖'`-stopping time `ρ` before which the drift inequality `Q ≤ K S` holds for all `v ≥ 0`,
  `E[e^{-K(T∧ρ)} Σ_q w_q(λ(s+T∧ρ), c₀) v_q(T∧ρ)] ≤ E[Σ_q w_q(λ(s), c₀) v₀_q]`.
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

/-- The state `(λ(s+u), c₀, v(u))`. -/
def gState (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (c₀ : FlowSample N → Fin r → ℝ) (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : Fin (N + (r + sectorCard N r)) → ℝ :=
  sumVec (flowLam F (sL + u) ω) (sumVec (c₀ ω) (mfMass F sL ℓ g r v₀ u ω))

theorem gTilted_sumVec {r M : ℕ} (K : ℝ) (w : Fin M → (Fin N → ℝ) → (Fin r → ℝ) → ℝ) (t : ℝ)
    (x : Fin N → ℝ) (c : Fin r → ℝ) (v : Fin M → ℝ) :
    gTilted K w (t, sumVec x (sumVec c v)) = Real.exp (-(K * t)) * ∑ q, w q x c * v q := by
  simp [gTilted, sumVec, glIdx, gcIdx, gvIdx]

theorem gState_lam (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (c₀ : FlowSample N → Fin r → ℝ) (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) :
    (fun m => gState F sL ℓ g r c₀ v₀ u ω (glIdx m)) = flowLam F (sL + u) ω := by
  funext m; simp [gState, sumVec, glIdx]

theorem gState_c (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (c₀ : FlowSample N → Fin r → ℝ) (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) :
    (fun m => gState F sL ℓ g r c₀ v₀ u ω (gcIdx m)) = c₀ ω := by
  funext m; simp [gState, sumVec, gcIdx]

theorem gState_v (F : Matrix (Fin N) (Fin N) ℂ) (sL : ℝ≥0) (ℓ : ℕ) (g : ℝ) (r : ℕ)
    (c₀ : FlowSample N → Fin r → ℝ) (v₀ : FlowSample N → Fin (sectorCard N r) → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) (q : Fin (sectorCard N r)) :
    gState F sL ℓ g r c₀ v₀ u ω (gvIdx q) = mfMass F sL ℓ g r v₀ u ω q := by
  simp [gState, sumVec, gvIdx]

/-- **State semimartingale** `(λ(s+u), c₀, v(u))`. -/
theorem gen_state_semimartingale (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (sL : ℝ≥0) (hs : 0 < sL)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) (r : ℕ) {v₀ : FlowSample N → Fin (sectorCard N r) → ℝ}
    (hv₀ : Measurable[shiftFiltration (flowFiltration N) sL 0] v₀)
    {c₀ : FlowSample N → Fin r → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) sL 0] c₀) :
    IsContinuousSemimartingale (flowLaw N a) (shiftFiltration (flowFiltration N) sL)
      (fun u ω => gState F sL ℓ g r c₀ v₀ u ω)
      (fun u ω => sumVec (fun k => dysonDrift N (flowLam F (sL + u) ω) k)
        (sumVec (0 : Fin r → ℝ) (matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω))))
      (fun _ _ => gCov N r (sectorCard N r)) := by
  set 𝓖 := shiftFiltration (flowFiltration N) sL
  have hc := mfCoeff_continuous hN hF sL ℓ hg r
  have hadC := mfCoeff_adapted hN F sL ℓ hg r
  have hZa : ∀ u, Measurable[𝓖 u] (mfMass F sL ℓ g r v₀ u) :=
    fun u => adaptedMass_measurable 𝓖 hadC hc hv₀ u
  have hZc : ∀ ω, Continuous fun u => mfMass F sL ℓ g r v₀ u ω := fun ω =>
    adaptedMass_continuous hc v₀ ω
  have hγc : ∀ ω, Continuous fun u =>
      matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω) := by
    intro ω
    refine continuous_pi fun k => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_apply l).comp ((continuous_apply k).comp (hc ω))).mul
      ((continuous_apply l).comp (hZc ω))
  have hγa : ∀ u, Measurable[𝓖 u]
      (fun ω => matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω)) := by
    intro u
    refine @measurable_pi_iff (FlowSample N) (Fin (sectorCard N r)) (fun _ => ℝ)
      (𝓖 u) _ _ |>.mpr fun k => ?_
    refine Finset.measurable_sum _ fun l _ => ?_
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hadC u))).mul
      ((measurable_pi_apply l).comp (hZa u))
  have hc₀u : ∀ u, Measurable[𝓖 u] c₀ := fun u => hc₀.mono (𝓖.mono (zero_le (a := u))) le_rfl
  have hsv := continuous_sumVec (d := r) (e := sectorCard N r)
  have hZ'a : ∀ u, Measurable[𝓖 u] (fun ω => sumVec (c₀ ω) (mfMass F sL ℓ g r v₀ u ω)) :=
    fun u => hsv.measurable.comp ((hc₀u u).prodMk (hZa u))
  have hZ'c : ∀ ω, Continuous fun u => sumVec (c₀ ω) (mfMass F sL ℓ g r v₀ u ω) :=
    fun ω => hsv.comp (continuous_const.prodMk (hZc ω))
  have hγ'a : ∀ u, Measurable[𝓖 u] (fun ω => sumVec (0 : Fin r → ℝ)
      (matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω))) :=
    fun u => hsv.measurable.comp (measurable_const.prodMk (hγa u))
  have hγ'c : ∀ ω, Continuous fun u => sumVec (0 : Fin r → ℝ)
      (matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω)) :=
    fun ω => hsv.comp (continuous_const.prodMk (hγc ω))
  have hY := flowLam_semimartingale hDBM hF a sL hs
  have h := IsContinuousSemimartingale.appendFV hY
    (Z := fun u ω => sumVec (c₀ ω) (mfMass F sL ℓ g r v₀ u ω))
    (γ := fun u ω => sumVec (0 : Fin r → ℝ)
      (matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω)))
    (fun u => (hZ'a u).stronglyMeasurable)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hZ'a u).stronglyMeasurable)
      hZ'c)
    (Eventually.of_forall hZ'c)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hγ'a u).stronglyMeasurable)
      hγ'c)
    (Eventually.of_forall fun ω t i =>
      (((continuous_apply i).comp ((hγ'c ω).comp continuous_real_toNNReal))).integrableOn_Ioc)
    (Eventually.of_forall fun ω t i => by
      obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
      rcases x with m | q
      · simp [smCompensated, sumVec]
      · have := mfMass_compensated_zero hN hF sL ℓ hg r v₀ ω t q
        simpa [smCompensated, sumVec] using this)
  exact h

/-- **Generic stopped Itô + tilted Gronwall in mean.** -/
theorem gen_mf_expectation_le (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (sL : ℝ≥0) (hs : 0 < sL)
    (ℓ : ℕ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin (sectorCard N r) → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {c₀ : FlowSample N → Fin r → ℝ}
    (hc₀ : Measurable[shiftFiltration (flowFiltration N) sL 0] c₀)
    {w : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ}
    {d1 d2 : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → Fin N → ℝ}
    (hw : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => w q z.1 z.2))
    (hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => w q (fun m => lam m + if m = i then s else 0) c) (d1 q lam c i) 0)
    (hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => d1 q (fun m => lam m + if m = i then s else 0) c i) (d2 q lam c i) 0)
    {Wm K : ℝ} (hWm0 : 0 ≤ Wm) (hw0 : ∀ q lam c, 0 ≤ w q lam c) (hwM : ∀ q lam c, w q lam c ≤ Wm) (hK0 : 0 ≤ K)
    (ρ : FlowSample N → WithTop ℝ≥0)
    (hρst : IsStoppingTime (shiftFiltration (flowFiltration N) sL) ρ)
    (hgood : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω → ∀ v : Fin (sectorCard N r) → ℝ,
      (∀ q, 0 ≤ v q) →
      ∑ q, w q (flowLam F (sL + u) ω) (c₀ ω) * ∑ q', mfCoeff F sL ℓ g r u ω q q' * v q' +
        ∑ q, v q * ∑ i, (dysonDrift N (flowLam F (sL + u) ω) i *
          d1 q (flowLam F (sL + u) ω) (c₀ ω) i +
          d2 q (flowLam F (sL + u) ω) (c₀ ω) i / (2 * N)) ≤
      K * ∑ q, w q (flowLam F (sL + u) ω) (c₀ ω) * v q)
    (T : ℝ≥0) :
    ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => gTilted K w
        ((u : ℝ), gState F sL ℓ g r c₀ v₀ u ω)) ρ T ω ∂flowLaw N a ≤
      ∫ ω, gTilted K w (0, gState F sL ℓ g r c₀ v₀ 0 ω) ∂flowLaw N a := by
  set Y : ℝ≥0 → FlowSample N → Fin (N + (r + sectorCard N r)) → ℝ :=
    fun u ω => gState F sL ℓ g r c₀ v₀ u ω with hYdef
  set Bd : ℝ≥0 → FlowSample N → Fin (N + (r + sectorCard N r)) → ℝ :=
    fun u ω => sumVec (fun k => dysonDrift N (flowLam F (sL + u) ω) k)
      (sumVec (0 : Fin r → ℝ) (matAct (mfCoeff F sL ℓ g r u ω) (mfMass F sL ℓ g r v₀ u ω)))
    with hBdef
  set Φ := gTilted (N := N) (r := r) (M := sectorCard N r) K w with hΦ
  have hY := gen_state_semimartingale hDBM hN hF a sL hs ℓ hg r hv₀m hc₀
  have hΦc : ContDiff ℝ 2 Φ := gTilted_contDiff hw
  have hI := hIto (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) sL) Y Bd
    (fun _ _ => gCov N r (sectorCard N r)) hY Set.univ isOpen_univ
    (Eventually.of_forall fun _ _ => trivial) Φ (hΦc.continuous.measurable) hΦc.contDiffOn
  have hS := hStop (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) sL) _ _ _ hI
    ρ hρst
  have hbd : ∀ (u : ℝ≥0) ω, |Φ ((u : ℝ), Y u ω)| ≤ (sectorCard N r) * Wm := by
    intro u ω
    have hv := mfMass_mem_unit hN hF sL ℓ hg r hv₀ u ω
    have hexp : Real.exp (-(K * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg u; nlinarith)
    simp only [hΦ, hYdef, gState, gTilted_sumVec]
    have hsum0 : 0 ≤ ∑ q, w q (flowLam F (sL + u) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ u ω q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _) (hv q).1
    have hsum1 : ∑ q, w q (flowLam F (sL + u) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ u ω q ≤
        (sectorCard N r) * Wm := by
      calc _ ≤ ∑ _q : Fin (sectorCard N r), Wm := Finset.sum_le_sum fun q _ => by
            calc _ ≤ Wm * 1 := mul_le_mul (hwM _ _ _) (hv q).2 (hv q).1 hWm0
              _ = Wm := mul_one _
        _ = _ := by simp
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum0)]
    calc _ ≤ 1 * ((sectorCard N r) * Wm) := mul_le_mul hexp hsum1 hsum0 zero_le_one
      _ = _ := one_mul _
  have hdrift : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      itoDrift Φ (Y u ω) u (Bd u ω) (gCov N r (sectorCard N r)) ≤ 0 := by
    intro ω u hu
    have hv := mfMass_mem_unit hN hF sL ℓ hg r hv₀ u ω
    have hQ := hgood ω u hu (mfMass F sL ℓ g r v₀ u ω) (fun q => (hv q).1)
    refine itoDrift_gTilted_nonpos hw hd1 hd2 (Y u ω) u (mfCoeff F sL ℓ g r u ω) le_rfl ?_ ?_
      (Bd u ω) (fun i => ?_) (fun m => ?_) (fun q => ?_)
    · simp only [hYdef, gState_lam, gState_c, gState_v]
      exact Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _) (hv q).1
    · simp only [hYdef, gState_lam, gState_c, gState_v]
      exact hQ
    · simp only [hYdef, gState_lam]
      simp [hBdef, sumVec, glIdx]
    · simp [hBdef, sumVec, gcIdx]
    · simp only [hYdef, gState_v]
      simp [hBdef, sumVec, gvIdx, matAct]
  have hβ : ∀ᵐ ω ∂flowLaw N a, ∀ r' : ℝ≥0, ∫ x in Set.Ioc (0 : ℝ) r',
      switchAfter ρ (fun t ω (_ : Fin 1) =>
        itoDrift Φ (Y t ω) t (Bd t ω) (gCov N r (sectorCard N r))) x.toNNReal ω 0 ≤ 0 := by
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
  have hfin := integral_le_of_drift_nonpos (flowLaw N a) (shiftFiltration (flowFiltration N) sL)
    _ _ _ hS (C := (sectorCard N r) * Wm) (fun t ω => hbd _ ω) hβ T
  have e0 : ∀ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0 =
      Φ (0, gState F sL ℓ g r c₀ v₀ 0 ω) := by
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
