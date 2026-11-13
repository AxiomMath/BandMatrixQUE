module

public import BlockBand.Palm.RelativeLocalizationFlowLam
public import BlockBand.Palm.RelativeLocalizationAdapted
public import BlockBand.Palm.RelativeLocalizationTrunc
public import BlockBand.Palm.RelativeLocalizationIto

/-!
# Relative localization: the state `(λ, v)` is a continuous semimartingale

Start time `s > 0` (flow time `a + s`), filtration `𝓖' = shiftFiltration (flowFiltration N) s`,
gap level `g > 0`, coefficients `flowCoeff F s ℓ b₀ g u ω = truncRefGen N (flowLam F (s+u) ω) ℓ b₀ g`
(continuous in `u` for every sample, `𝓖'`-adapted), `𝓖'_0`-measurable datum `v₀`, mass process
`flowMass = adaptedMass flowCoeff v₀` (`RelativeLocalizationAdapted`). Proved:

* `flowCoeff_adapted`, `flowCoeff_continuous`;
* `flowMass_compensated_zero` : every sample has `v_u = v_0 + ∫_{(0,u]} L v` (finite variation);
* `flow_state_semimartingale` : `u ↦ (flowLam F (s+u), flowMass u)` is an
  `IsContinuousSemimartingale` in `ℝ^{N+N}` (layout `lamIdx`/`massIdx`) with drift
  `(dysonDrift, flowCoeff · v)` and covariance `lamCov N`, the shape required by
  `itoDrift_tiltedMass`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-- Truncated reference coefficients along the eigenvalue path started at `s`. -/
def flowCoeff (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (b₀ g : ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : Fin N → Fin N → ℝ :=
  truncRefGen N (flowLam F (s + u) ω) ℓ b₀ g

theorem flowCoeff_continuous {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    (ℓ : ℕ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) (ω : FlowSample N) :
    Continuous fun u => flowCoeff F s ℓ b₀ g u ω :=
  (continuous_truncRefGen ℓ b₀ hg).comp
    ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))

theorem flowCoeff_adapted (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (b₀ : ℝ) {g : ℝ}
    (hg : 0 < g) (u : ℝ≥0) :
    Measurable[shiftFiltration (flowFiltration N) s u] (flowCoeff F s ℓ b₀ g u) :=
  (continuous_truncRefGen ℓ b₀ hg).measurable.comp (flowLam_adapted F (s + u))

/-- The adapted mass along the flow. -/
def flowMass (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ℓ : ℕ) (b₀ g : ℝ)
    (v₀ : FlowSample N → Fin N → ℝ) (u : ℝ≥0) (ω : FlowSample N) : Fin N → ℝ :=
  adaptedMass (flowCoeff F s ℓ b₀ g) v₀ (u : ℝ) ω

theorem flowMass_compensated_zero {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (s : ℝ≥0) (ℓ : ℕ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) (v₀ : FlowSample N → Fin N → ℝ)
    (ω : FlowSample N) (t : ℝ≥0) (i : Fin N) :
    smCompensated (flowMass F s ℓ b₀ g v₀)
      (fun u ω => matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω)) i t ω = 0 := by
  have hc := flowCoeff_continuous hF s ℓ b₀ hg
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg t)
  have hrepr := forwardMass_integral (realCoeff_continuous hc ω).continuousOn hsol
    ⟨NNReal.coe_nonneg t, le_rfl⟩
  have h0 : flowMass F s ℓ b₀ g v₀ 0 ω = v₀ ω := hsol.1
  have hint : IntervalIntegrable
      (fun r => matAct (realCoeff (flowCoeff F s ℓ b₀ g) ω r) (adaptedMass (flowCoeff F s ℓ b₀ g) v₀ r ω))
      volume 0 t :=
    (continuousOn_matAct (realCoeff_continuous hc ω).continuousOn hsol.2.1).intervalIntegrable_of_Icc
      (NNReal.coe_nonneg t)
  have hcomp := congrArg (fun x : Fin N → ℝ => x i) hrepr
  simp only [Pi.add_apply] at hcomp
  have hproj : (∫ r in (0 : ℝ)..t, matAct (realCoeff (flowCoeff F s ℓ b₀ g) ω r)
      (adaptedMass (flowCoeff F s ℓ b₀ g) v₀ r ω)) i =
      ∫ r in (0 : ℝ)..t, matAct (realCoeff (flowCoeff F s ℓ b₀ g) ω r)
        (adaptedMass (flowCoeff F s ℓ b₀ g) v₀ r ω) i := by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i).intervalIntegral_comp_comm
      hint
    simpa using this.symm
  rw [hproj] at hcomp
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] at hcomp
  unfold smCompensated
  rw [h0]
  have hcongr : ∫ r in Set.Ioc (0 : ℝ) t, matAct (flowCoeff F s ℓ b₀ g r.toNNReal ω)
      (flowMass F s ℓ b₀ g v₀ r.toNNReal ω) i =
      ∫ r in Set.Ioc (0 : ℝ) t, matAct (realCoeff (flowCoeff F s ℓ b₀ g) ω r)
          (adaptedMass (flowCoeff F s ℓ b₀ g) v₀ r ω) i := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [flowMass, realCoeff, Real.coe_toNNReal _ hr.1.le]
  rw [hcongr]
  change flowMass F s ℓ b₀ g v₀ t ω i - v₀ ω i - _ = 0
  simp only [flowMass] at hcomp ⊢
  linarith

theorem blockCov_eq_lamCov :
    blockCov (e := N) (Matrix.of fun k l : Fin N => if k = l then 1 / (N : ℝ) else 0) = lamCov N := by
  ext i j
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with a | b <;> rcases y with c | f <;>
    simp only [blockCov, lamCov, Matrix.of_apply, Equiv.symm_apply_apply]

/-- The state `(λ, v)` is a continuous semimartingale with drift `(dysonDrift, flowCoeff · v)` and
covariance `lamCov N`. -/
theorem flow_state_semimartingale (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    (ℓ : ℕ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀ : Measurable[shiftFiltration (flowFiltration N) s 0] v₀) :
    IsContinuousSemimartingale (flowLaw N a) (shiftFiltration (flowFiltration N) s)
      (fun u ω => sumVec (flowLam F (s + u) ω) (flowMass F s ℓ b₀ g v₀ u ω))
      (fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
        (matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω)))
      (fun _ _ => lamCov N) := by
  have hc := flowCoeff_continuous hF s ℓ b₀ hg
  have hadC := flowCoeff_adapted F s ℓ b₀ hg
  have hZa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (flowMass F s ℓ b₀ g v₀ u) := fun u =>
    adaptedMass_measurable (shiftFiltration (flowFiltration N) s) hadC hc hv₀ u
  have hZc : ∀ ω, Continuous fun u => flowMass F s ℓ b₀ g v₀ u ω := fun ω =>
    adaptedMass_continuous hc v₀ ω
  have hγc : ∀ ω, Continuous fun u =>
      matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω) := by
    intro ω
    refine continuous_pi fun k => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_apply l).comp ((continuous_apply k).comp (hc ω))).mul
      ((continuous_apply l).comp (hZc ω))
  have hγa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (fun ω => matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω)) := by
    intro u
    refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) s u) _ _ |>.mpr fun k => ?_
    refine Finset.measurable_sum _ fun l _ => ?_
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp (hadC u))).mul
      ((measurable_pi_apply l).comp (hZa u))
  have hY := flowLam_semimartingale hDBM hF a s hs
  have h := IsContinuousSemimartingale.appendFV hY (Z := flowMass F s ℓ b₀ g v₀)
    (γ := fun u ω => matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω))
    (fun u => (hZa u).stronglyMeasurable)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hZa u).stronglyMeasurable) hZc)
    (Eventually.of_forall hZc)
    (StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hγa u).stronglyMeasurable) hγc)
    (Eventually.of_forall fun ω t i =>
      (((continuous_apply i).comp ((hγc ω).comp continuous_real_toNNReal))).integrableOn_Ioc)
    (Eventually.of_forall fun ω t i => flowMass_compensated_zero hF s ℓ b₀ hg v₀ ω t i)
  simpa only [blockCov_eq_lamCov] using h

end BlockBand.Palm.RelativeLocalization
