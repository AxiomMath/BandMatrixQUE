module

public import BlockBand.Palm.RelativeLocalizationStopped

/-!
# Relative localization: the per-start expectation bound for a generic generator and weight

Generalizes `flow_tilted_expectation_le` (continuation C01) to

* an arbitrary continuous sub-generator field `Gen : ℝ^N → Mat` (`truncRefGen`, `truncShortGen`),
* an arbitrary `C²` weight `φ ≥ 0`, `φ ≤ M`, with the hypotheses of `weighted_drift_le`,
* a random centre `c₀` measurable at the start (moving centre `λ_k(s)` of the short fields):
  the weight is evaluated at `λ - c₀` (`IsContinuousSemimartingale.sub_const`; the Dyson drift
  and the short generator only see differences).

Main result `gen_expectation_le` : `E Φ_{T∧ρ} ≤ E Φ_0`, `Φ_u = e^{-Ku} Σ φ(λ_k(s+u) - c₀) v_k(u)`,
for every stopping time `ρ` of `shiftFiltration (flowFiltration N) s` (`s > 0`) before which
the domination, short-pair and long-gap conditions hold.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-!
### Subtracting an initially measurable constant
-/

theorem IsContinuousSemimartingale.sub_const {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
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

theorem dysonDrift_sub_const (lam : Fin N → ℝ) (c : ℝ) (k : Fin N) :
    dysonDrift N (fun l => lam l - c) k = dysonDrift N lam k := by
  unfold dysonDrift; congr 1
  exact Finset.sum_congr rfl fun j _ => by ring_nf

theorem shortGen_sub_const (lam : Fin N → ℝ) (ℓ : ℕ) (c : ℝ) :
    shortGen N (fun l => lam l - c) ℓ = shortGen N lam ℓ := by
  funext k l
  have : ∀ m, pairRate N (fun l => lam l - c) k m = pairRate N lam k m := fun m => by
    unfold pairRate; ring_nf
  simp only [shortGen, this]

/-!
### Generic coefficients and mass
-/

/-- Coefficients `Gen(λ(s+u))`. -/
def genCoeff (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (u : ℝ≥0) (ω : FlowSample N) : Fin N → Fin N → ℝ :=
  Gen (flowLam F (s + u) ω)

/-- The adapted mass for the generic coefficients. -/
def genMass (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (v₀ : FlowSample N → Fin N → ℝ) (u : ℝ≥0) (ω : FlowSample N) : Fin N → ℝ :=
  adaptedMass (genCoeff Gen F s) v₀ (u : ℝ) ω

/-- Sub-generator field. -/
def IsSubGenField (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) : Prop :=
  ∀ lam, (∀ k l, k ≠ l → 0 ≤ Gen lam k l) ∧ ∀ k, ∑ l, Gen lam k l ≤ 0

theorem genCoeff_continuous {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0) (ω : FlowSample N) :
    Continuous fun u => genCoeff Gen F s u ω :=
  hG.comp ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))

theorem genCoeff_adapted {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    (F : Matrix (Fin N) (Fin N) ℂ) (s u : ℝ≥0) :
    Measurable[shiftFiltration (flowFiltration N) s u] (genCoeff Gen F s u) :=
  hG.measurable.comp (flowLam_adapted F (s + u))

theorem genMass_mem_unit {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    (hGs : IsSubGenField Gen) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    {v₀ : FlowSample N → Fin N → ℝ} (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1) (u : ℝ≥0)
    (ω : FlowSample N) (k : Fin N) :
    0 ≤ genMass Gen F s v₀ u ω k ∧ genMass Gen F s v₀ u ω k ≤ 1 := by
  have hc := genCoeff_continuous hG hF s
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg u)
  have hsub : IsSubGenerator (realCoeff (genCoeff Gen F s) ω) 0 u :=
    fun x _ => hGs _
  have hmem : (u : ℝ) ∈ Icc 0 (u : ℝ) := ⟨NNReal.coe_nonneg u, le_rfl⟩
  exact ⟨forwardMass_nonneg hsub hsol (fun k => (hv₀ ω k).1) u hmem k,
    forwardMass_le_const hsub hsol zero_le_one (fun k => (hv₀ ω k).2) u hmem k⟩

theorem genMass_compensated_zero {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    (v₀ : FlowSample N → Fin N → ℝ) (ω : FlowSample N) (t : ℝ≥0) (i : Fin N) :
    smCompensated (genMass Gen F s v₀)
      (fun u ω => matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω)) i t ω = 0 := by
  have hc := genCoeff_continuous hG hF s
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg t)
  have hrepr := forwardMass_integral (realCoeff_continuous hc ω).continuousOn hsol
    ⟨NNReal.coe_nonneg t, le_rfl⟩
  have h0 : genMass Gen F s v₀ 0 ω = v₀ ω := hsol.1
  have hint : IntervalIntegrable
      (fun r => matAct (realCoeff (genCoeff Gen F s) ω r) (adaptedMass (genCoeff Gen F s) v₀ r ω))
      volume 0 t :=
    (continuousOn_matAct (realCoeff_continuous hc ω).continuousOn hsol.2.1).intervalIntegrable_of_Icc
      (NNReal.coe_nonneg t)
  have hcomp := congrArg (fun x : Fin N → ℝ => x i) hrepr
  simp only [Pi.add_apply] at hcomp
  have hproj : (∫ r in (0 : ℝ)..t, matAct (realCoeff (genCoeff Gen F s) ω r)
      (adaptedMass (genCoeff Gen F s) v₀ r ω)) i =
      ∫ r in (0 : ℝ)..t, matAct (realCoeff (genCoeff Gen F s) ω r)
        (adaptedMass (genCoeff Gen F s) v₀ r ω) i := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).intervalIntegral_comp_comm
      hint
    simpa using this.symm
  rw [hproj, intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at hcomp
  unfold smCompensated
  rw [h0]
  have hcongr : ∫ r in Set.Ioc (0 : ℝ) t, matAct (genCoeff Gen F s r.toNNReal ω)
      (genMass Gen F s v₀ r.toNNReal ω) i =
      ∫ r in Set.Ioc (0 : ℝ) t, matAct (realCoeff (genCoeff Gen F s) ω r)
          (adaptedMass (genCoeff Gen F s) v₀ r ω) i := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [genMass, realCoeff, Real.coe_toNNReal _ hr.1.le]
  rw [hcongr]
  change genMass Gen F s v₀ t ω i - v₀ ω i - _ = 0
  simp only [genMass] at hcomp ⊢
  linarith

/-- The shifted eigenvalue path `λ(s+u) - c₀`. -/
def lamShift (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (c₀ : FlowSample N → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : Fin N → ℝ :=
  fun k => flowLam F (s + u) ω k - c₀ ω

/-- **State semimartingale** `(λ - c₀, v)` for generic coefficients. -/
theorem gen_state_semimartingale (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {v₀ : FlowSample N → Fin N → ℝ} (hv₀ : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) s 0] c₀) :
    IsContinuousSemimartingale (flowLaw N a) (shiftFiltration (flowFiltration N) s)
      (fun u ω => sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω))
      (fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
        (matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω)))
      (fun _ _ => lamCov N) := by
  have hc := genCoeff_continuous hG hF s
  have hadC := genCoeff_adapted hG F s
  have hZa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u] (genMass Gen F s v₀ u) :=
    fun u => adaptedMass_measurable (shiftFiltration (flowFiltration N) s) hadC hc hv₀ u
  have hZc : ∀ ω, Continuous fun u => genMass Gen F s v₀ u ω := fun ω =>
    adaptedMass_continuous hc v₀ ω
  have hγc : ∀ ω, Continuous fun u =>
      matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω) := by
    intro ω
    refine continuous_pi fun k => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_apply l).comp ((continuous_apply k).comp (hc ω))).mul
      ((continuous_apply l).comp (hZc ω))
  have hγa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (fun ω => matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω)) := by
    intro u
    refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) s u) _ _ |>.mpr fun k => ?_
    refine Finset.measurable_sum _ fun l _ => ?_
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hadC u))).mul
      ((measurable_pi_apply l).comp (hZa u))
  have hcv : StronglyMeasurable[shiftFiltration (flowFiltration N) s 0]
      (fun ω (_ : Fin N) => c₀ ω) :=
    (@measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) s 0) _ _ |>.mpr fun _ => hc₀).stronglyMeasurable
  have hY := IsContinuousSemimartingale.sub_const (flowLam_semimartingale hDBM hF a s hs) hcv
  have h := IsContinuousSemimartingale.appendFV hY (Z := genMass Gen F s v₀)
    (γ := fun u ω => matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω))
    (fun u => (hZa u).stronglyMeasurable)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hZa u).stronglyMeasurable) hZc)
    (Eventually.of_forall hZc)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hγa u).stronglyMeasurable) hγc)
    (Eventually.of_forall fun ω t i =>
      (((continuous_apply i).comp ((hγc ω).comp continuous_real_toNNReal))).integrableOn_Ioc)
    (Eventually.of_forall fun ω t i => genMass_compensated_zero hG hF s v₀ ω t i)
  simp only [blockCov_eq_lamCov] at h
  exact h

/-- **Generic per-start expectation bound** (`s > 0`). -/
theorem gen_expectation_le (hIto : SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen) (hGs : IsSubGenField Gen)
    {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) s 0] c₀)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    (hφc : ContDiff ℝ 2 φ) {A B Kc G c₁ M K : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B)
    (hKc0 : 0 ≤ Kc) (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ Kc * φ x) (hc₁ : 0 < c₁)
    (hK0 : 0 ≤ K) {ℓ : ℕ}
    (hK : 2 * ℓ * B * Kc / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N) ≤ K)
    (ρ : FlowSample N → WithTop ℝ≥0)
    (hρst : IsStoppingTime (shiftFiltration (flowFiltration N) s) ρ)
    (hgood : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      (∀ v : Fin N → ℝ, (∀ k, 0 ≤ v k) → ∀ k,
        ∑ l, Gen (flowLam F (s + u) ω) k l * v l ≤
          ∑ l, shortGen N (flowLam F (s + u) ω) ℓ k l * v l) ∧
      (∀ k l : Fin N, l ≠ k → labelDist k l < ℓ →
        |lamShift F s c₀ u ω l - lamShift F s c₀ u ω k| ≤ G ∨
          (φ1 (lamShift F s c₀ u ω k) = 0 ∧
            φ (lamShift F s c₀ u ω l) = φ (lamShift F s c₀ u ω k))) ∧
      (∀ k l : Fin N, l ≠ k → ℓ ≤ labelDist k l →
        c₁ * labelDist k l / N ≤ |flowLam F (s + u) ω k - flowLam F (s + u) ω l|))
    (T : ℝ≥0) :
    ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => tiltedMass K φ
        ((u : ℝ), sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω))) ρ T ω
        ∂flowLaw N a ≤
      ∫ ω, tiltedMass K φ (0, sumVec (lamShift F s c₀ 0 ω) (genMass Gen F s v₀ 0 ω))
        ∂flowLaw N a := by
  set Y : ℝ≥0 → FlowSample N → Fin (N + N) → ℝ :=
    fun u ω => sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω) with hYdef
  set Bd : ℝ≥0 → FlowSample N → Fin (N + N) → ℝ :=
    fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
      (matAct (genCoeff Gen F s u ω) (genMass Gen F s v₀ u ω)) with hBdef
  set Φ := tiltedMass (N := N) K φ with hΦ
  have hY := gen_state_semimartingale hDBM hF a s hs hG hv₀m hc₀
  have hΦc : ContDiff ℝ 2 Φ := tiltedMass_contDiff hφc
  have hI := hIto (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) Y Bd
    (fun _ _ => lamCov N) hY Set.univ isOpen_univ (Eventually.of_forall fun _ _ => trivial) Φ
    (hΦc.continuous.measurable) hΦc.contDiffOn
  have hS := hStop (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) _ _ _ hI
    ρ hρst
  have hM0 : 0 ≤ M := (hφ0 0).trans (hφM 0)
  have hbd : ∀ (u : ℝ≥0) ω, |Φ ((u : ℝ), Y u ω)| ≤ M * N := by
    intro u ω
    have hv := genMass_mem_unit hG hGs hF s hv₀ u ω
    have hexp : Real.exp (-(K * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg u; nlinarith)
    have hsum0 : 0 ≤ ∑ k, φ (Y u ω (lamIdx k)) * Y u ω (massIdx k) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hφ0 _) (by
        rw [hYdef]; simp only [sumVec_massIdx]; exact (hv k).1)
    have hsum1 : ∑ k, φ (Y u ω (lamIdx k)) * Y u ω (massIdx k) ≤ M * N := by
      calc _ ≤ ∑ _k : Fin N, M := Finset.sum_le_sum fun k _ => by
            rw [hYdef]; simp only [sumVec_massIdx]
            calc _ ≤ M * 1 := mul_le_mul (hφM _) (hv k).2 (hv k).1 hM0
              _ = M := mul_one M
        _ = M * N := by simp [mul_comm]
    simp only [hΦ, tiltedMass]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum0)]
    calc _ ≤ 1 * (M * N) := mul_le_mul hexp hsum1 hsum0 zero_le_one
      _ = M * N := one_mul _
  have hdrift : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      itoDrift Φ (Y u ω) u (Bd u ω) (lamCov N) ≤ 0 := by
    intro ω u hu
    obtain ⟨hdom, hsh, hlg⟩ := hgood ω u hu
    have hv := genMass_mem_unit hG hGs hF s hv₀ u ω
    have hlam : (fun m => Y u ω (lamIdx m)) = lamShift F s c₀ u ω := by
      funext m; rw [hYdef]; simp only [sumVec_lamIdx]
    have hmass : (fun m => Y u ω (massIdx m)) = genMass Gen F s v₀ u ω := by
      funext m; rw [hYdef]; simp only [sumVec_massIdx]
    have hsg : shortGen N (lamShift F s c₀ u ω) ℓ = shortGen N (flowLam F (s + u) ω) ℓ :=
      shortGen_sub_const _ ℓ _
    have hQ := weighted_drift_le (lamShift F s c₀ u ω) ℓ (genCoeff Gen F s u ω)
      (genMass Gen F s v₀ u ω) (fun k => (hv k).1) hφ hφ1 hφ0 hA hA0 hB hB0 hKc0 hcomp hc₁
      (fun k => by rw [hsg]; exact hdom _ (fun k => (hv k).1) k) hsh
      (fun k l hlk hd => by
        have := hlg k l hlk hd
        simpa only [lamShift, sub_sub_sub_cancel_right] using this)
    refine itoDrift_tiltedMass_nonpos hφ hφ1 hφc hφ0 (Y u ω) u (genCoeff Gen F s u ω)
      (fun k => by rw [hYdef]; simp only [sumVec_massIdx]; exact (hv k).1) hK ?_ (Bd u ω)
      (fun k => ?_) (fun k => ?_)
    · simp only [hYdef, sumVec_lamIdx, sumVec_massIdx]; exact hQ
    · simp only [hBdef, hYdef, sumVec_lamIdx]
      exact (dysonDrift_sub_const _ _ k).symm
    · simp only [hBdef, hYdef, sumVec_massIdx, matAct]
  have hβ : ∀ᵐ ω ∂flowLaw N a, ∀ r : ℝ≥0, ∫ x in Set.Ioc (0 : ℝ) r,
      switchAfter ρ (fun t ω (_ : Fin 1) => itoDrift Φ (Y t ω) t (Bd t ω) (lamCov N))
        x.toNNReal ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω r => setIntegral_nonpos_of_ae_restrict ?_
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
    _ _ _ hS (C := M * N) (fun t ω => hbd _ ω) hβ T
  have e0 : ∀ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0 =
      Φ (0, sumVec (lamShift F s c₀ 0 ω) (genMass Gen F s v₀ 0 ω)) := by
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

end BlockBand.Palm.RelativeLocalization
