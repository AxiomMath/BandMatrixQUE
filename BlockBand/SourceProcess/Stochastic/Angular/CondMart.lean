module

public import BlockBand.SourceProcess.Stochastic.Angular.CondSemi
public import BlockBand.SourceProcess.Stochastic.Angular.CondOrth

/-!
# Complex angular martingale problem: the martingales of the conditioning state

`CondHyp Q 𝓖 G F s n φ A` bundles the hypotheses of `GenericConditioning N` (with `0 < N`).
Let `Y = Yst N 0 G F s` (`lamOf ∘ Y` is the eigenvalue path of `F + G_{s+·}`),
`Mc u = φ(y_u) - ∫_0^u A(y_r) dr` and `σ = σ_n` the gap stop. Then:
* `CondHyp.phic_mart`: `e^{c_θ u} h(phase_θ Y u)` is a martingale (modification form);
* `CondHyp.pcond_mart`: `(e^{c_θ u} h(phase_θ Y u) Mc_u)^{σ}` is a martingale;
* `CondHyp.mc_stop_bound`, `CondHyp.ms_props`: `Mc^{σ}` is bounded by `C_φ + C_A T` on `[0, T]`
  along a simple path, hence adapted and a.s. bounded on bounded intervals.

From these, the test-function identity of `e^{c_θ u} h(⋯) Mc^{σ}_u` (as in `testMart_ZreMs`: the
stopped product before `σ`, optional sampling after it) is proved in the sibling module,
`CondHyp.zrems`.

All come from `zeroDrift_stoppedU` and the zero Itô drift of `Phic`, `Pcond`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson BlockBand.SourceProcess.Stochastic.Dyson.Angular
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_le
  stoppedProcess_eq_stopTime)

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- The compensated process `φ(y_u) - ∫_0^u A(y_r) dr`. -/
def Mc (φ A : (Fin (N * N) → ℝ) → ℝ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s u : ℝ≥0) (ω : Ω) : ℝ :=
  φ (ycd N G F s u ω) - ∫ r in Ioc (0 : ℝ) u, A (ycd N G F s r.toNNReal ω)

/-- **The hypotheses of `GenericConditioning N`**, with `0 < N`. -/
structure CondHyp (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (n : ℕ) (φ A : (Fin (N * N) → ℝ) → ℝ) : Prop where
  hN : 0 < N
  hG : IsHermitianBrownian Q 𝓖 N G
  hF : Measurable[𝓖 0] F
  hFh : ∀ ω, (F ω).IsHermitian
  hs : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)
  hn : 0 < n
  hφm : Measurable φ
  hφ : ∀ y ∈ simpleSet N, ContDiffAt ℝ 2 φ y
  hAm : Measurable A
  hA : ContinuousOn A (simpleSet N)
  hΔ : ∀ y ∈ simpleSet N,
    ∑ a, fderiv ℝ (fderiv ℝ φ) y (Pi.single a 1) (Pi.single a 1) = 2 * N * A y
  hx : ∀ y ∈ simpleSet N, ∀ i : Fin N,
    ∑ a, fderiv ℝ φ y (Pi.single a 1) * fderiv ℝ (lam N i) y (Pi.single a 1) = 0
  hφb : ∃ C, ∀ y, |φ y| ≤ C
  hAb : ∃ C, ∀ y ∈ simpleSet N,
    (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) → |A y| ≤ C

/-!
### Values of the test functions along the state
-/

section Values
variable {Q' : Measure Ω} (hG : IsHermitianBrownian Q' 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
include hG hFh

theorem lam_ycd (s u : ℝ≥0) (ω : Ω) (i : Fin N) :
    lam N i (ycd N G F s u ω) = dysonEigenvalue N (F ω + G (s + u) ω) i := by
  simp only [lam, ycd, vecHerm_hermVec (herm_add hG hFh _ ω)]

theorem lam_ycd_eq (s u : ℝ≥0) (ω : Ω) :
    (fun j => lam N j (ycd N G F s u ω)) = lamOf (Yst N 0 G F s u ω) := by
  funext j; rw [lam_ycd hG hFh, Yst, lamOf_dysonState]

theorem lam_ycd' (s u : ℝ≥0) (ω : Ω) (i : Fin N) :
    lam N i (ycd N G F s u ω) = lamOf (Yst N 0 G F s u ω) i :=
  congrFun (lam_ycd_eq hG hFh s u ω) i

theorem phase_Zc (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (s u : ℝ≥0) (ω : Ω) :
    yfun (thLam θ) 0 (Zc θ A G F s u ω) = phase θ (Yst N 0 G F s) u ω := by
  simp only [yfun, stY_Zc, stW_Zc, Vc, condVd, Matrix.cons_val_zero, phase, thLam,
    lam_ycd' hG hFh]

theorem Phic_Zc {h : ℝ → ℝ} (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (s u : ℝ≥0) (ω : Ω) :
    Phic h θ (Zc θ A G F s u ω) = Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) := by
  rw [Phic, phase_Zc hG hFh, Ec, stW_Zc]
  simp [Vc, condVd]

theorem Pcond_Zc {h : ℝ → ℝ} (θ : Fin N → ℝ) (φ A : (Fin (N * N) → ℝ) → ℝ) (s u : ℝ≥0)
    (ω : Ω) : Pcond h θ φ (Zc θ A G F s u ω) =
      Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) * Mc φ A G F s u ω := by
  rw [Pcond, Phic_Zc hG hFh]
  congr 1
  rw [yfun, stY_Zc, stW_Zc, Mc]
  simp [Vc, condVd]

end Values

theorem measurable_thLam (θ : Fin N → ℝ) : Measurable (thLam θ) :=
  Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_lam i)

theorem measurable_yfun {ψ : (Fin (N * N) → ℝ) → ℝ} (hψ : Measurable ψ) (k : Fin 3) :
    Measurable (yfun ψ k) :=
  (hψ.comp (stY N).continuous.measurable).sub (stW N k).continuous.measurable

theorem measurable_Phic {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ) :
    Measurable (Phic h θ) :=
  (contDiff_Ec _).continuous.measurable.mul
    (hh.cont.measurable.comp (measurable_yfun (measurable_thLam θ) 0))

theorem contDiffAt_Phic {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ)
    {z : Fin (N * N + 3) → ℝ} (hz : stY N z ∈ simpleSet N) : ContDiffAt ℝ 2 (Phic h θ) z :=
  (contDiff_Ec _).contDiffAt.mul
    ((contDiff_trig hh).contDiffAt.comp z (contDiffAt_yfun (contDiffAt_thLam hz) 0))

theorem exp_mul_bound {h : ℝ → ℝ} (hb : ∀ x, |h x| ≤ 1) (θ : Fin N → ℝ) {u T : ℝ≥0}
    (hu : u ≤ T) (x : ℝ) : |Real.exp (cθ θ * u) * h x| ≤ Real.exp (cθ θ * T) := by
  have hc : 0 ≤ cθ θ := by unfold cθ; positivity
  rw [abs_mul, Real.abs_exp]
  calc Real.exp (cθ θ * u) * |h x| ≤ Real.exp (cθ θ * u) * 1 :=
        mul_le_mul_of_nonneg_left (hb _) (Real.exp_pos _).le
    _ ≤ Real.exp (cθ θ * T) := by
        rw [mul_one]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) hc)

variable {s : ℝ≥0} {n : ℕ} {φ A : (Fin (N * N) → ℝ) → ℝ}

theorem CondHyp.mem_Uc (H : CondHyp Q 𝓖 G F s n φ A) (θ : Fin N → ℝ)
    (A' : (Fin (N * N) → ℝ) → ℝ) : ∀ᵐ ω ∂Q, ∀ t, Zc θ A' G F s t ω ∈ Uc N := by
  filter_upwards [H.hs] with ω hω t
  show stY N (Zc θ A' G F s t ω) ∈ simpleSet N
  rw [stY_Zc]; exact ycd_mem H.hG H.hFh hω t

/-- **The exponential martingale** `e^{c_θ u} h(θ·λ_u - ∫_0^u θ·b(λ))`. -/
theorem CondHyp.phic_mart [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A)
    (θ : Fin N → ℝ) {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    HasMartingaleModification Q (shiftFiltration 𝓖 s)
        (fun (u : ℝ≥0) ω => Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω)) ∧
      (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t]
        fun ω => Real.exp (cθ θ * t) * h (phase θ (Yst N 0 G F s) t ω)) ∧
      ∀ᵐ ω ∂Q, Continuous fun t : ℝ≥0 => Real.exp (cθ θ * t) * h (phase θ (Yst N 0 G F s) t ω) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast H.hN.ne'
  have K := zeroDrift_stoppedU (isContinuousSemimartingale_Zc H.hG H.hF H.hFh H.hs θ
    (A := fun _ => 0) measurable_const continuousOn_const) isOpen_Uc (H.mem_Uc θ _)
    (measurable_Phic hh θ) (fun z hz => contDiffAt_Phic hh θ hz)
    (fun t ω hz => itoDrift_Phic θ _ hN hh hz t) isStoppingTime_top_const
    (fun T => ⟨Real.exp (cθ θ * T), ae_of_all _ fun ω r hr => by
      rw [stoppedProcess_top, Phic_Zc H.hG H.hFh]; exact exp_mul_bound hb θ hr _⟩)
  simp only [stoppedProcess_top, Phic_Zc H.hG H.hFh] at K
  exact K

/-- `|Mc^{σ}| ≤ C_φ + C_A T` on `[0, T]` along a simple path. -/
theorem CondHyp.mc_stop_bound (H : CondHyp Q 𝓖 G F s n φ A) {ω : Ω}
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) {Cφ CA : ℝ}
    (hCφ : ∀ y, |φ y| ≤ Cφ) (hCA0 : 0 ≤ CA) (hCA : ∀ y ∈ simpleSet N,
      (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) → |A y| ≤ CA)
    {T r : ℝ≥0} (hr : r ≤ T) :
    |Mc φ A G F s (stopTime (sig N G F s n ω) r) ω| ≤ Cφ + CA * T := by
  set r' := stopTime (sig N G F s n ω) r
  have hr' : (r' : WithTop ℝ≥0) ≤ sig N G F s n ω :=
    BlockBand.SourceProcess.Stochastic.Semimartingale.stopTime_le_self _ r
  have hr'T : r' ≤ T := (stopTime_le _ r).trans hr
  have hb : ∀ x ∈ Ioo (0 : ℝ) r', ‖A (ycd N G F s x.toNNReal ω)‖ ≤ CA := by
    intro x hx
    have hxr : (x.toNNReal : WithTop ℝ≥0) < gapStop N (fun t ω => F ω + G t ω) s n ω := by
      refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hr'
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx.1.le]; exact hx.2
    rw [Real.norm_eq_abs]
    refine hCA _ (ycd_mem H.hG H.hFh hω _) fun i j hij => ?_
    rw [lam_ycd H.hG H.hFh, lam_ycd H.hG H.hFh]
    exact (gap_of_lt_gapStop hxr i j hij).le
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (by simp) hb
  rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by simp), sub_zero,
    ← integral_Ioc_eq_integral_Ioo, Real.norm_eq_abs] at hI
  have h3 : CA * (r' : ℝ) ≤ CA * T := mul_le_mul_of_nonneg_left (by exact_mod_cast hr'T) hCA0
  unfold Mc
  calc _ ≤ |φ (ycd N G F s r' ω)| + |∫ x in Ioc (0 : ℝ) r', A (ycd N G F s x.toNNReal ω)| :=
        abs_sub _ _
    _ ≤ Cφ + CA * T := by linarith [hCφ (ycd N G F s r' ω)]

theorem CondHyp.exists_bounds (H : CondHyp Q 𝓖 G F s n φ A) :
    ∃ Cφ CA : ℝ, (∀ y, |φ y| ≤ Cφ) ∧ 0 ≤ CA ∧ ∀ y ∈ simpleSet N,
      (∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) ≤ |lam N i y - lam N j y|) → |A y| ≤ CA := by
  obtain ⟨Cφ, hCφ⟩ := H.hφb
  obtain ⟨CA, hCA⟩ := H.hAb
  exact ⟨Cφ, max CA 0, hCφ, le_max_right _ _, fun y hy hg => (hCA y hy hg).trans (le_max_left _ _)⟩

/-- **The stopped product martingale** `(e^{c_θ u} h(phase) Mc_u)^{σ_n}`. -/
theorem CondHyp.pcond_mart [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A)
    (θ : Fin N → ℝ) {h h' : ℝ → ℝ} (hh : Trig h h') (hb : ∀ x, |h x| ≤ 1) :
    HasMartingaleModification Q (shiftFiltration 𝓖 s) (stoppedProcess (fun (u : ℝ≥0) ω =>
        Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) * Mc φ A G F s u ω)
        (sig N G F s n)) ∧
      (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t] (stoppedProcess (fun (u : ℝ≥0) ω =>
        Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) * Mc φ A G F s u ω)
        (sig N G F s n) t)) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast H.hN.ne'
  obtain ⟨Cφ, CA, hCφ, hCA0, hCA⟩ := H.exists_bounds
  have K := zeroDrift_stoppedU (isContinuousSemimartingale_Zc H.hG H.hF H.hFh H.hs θ H.hAm H.hA)
    isOpen_Uc (H.mem_Uc θ A) (g := Pcond h θ φ) ((measurable_Phic hh θ).mul (measurable_yfun H.hφm 1))
    (fun z hz => (contDiffAt_Phic hh θ hz).mul (contDiffAt_yfun (H.hφ _ hz) 1))
    (fun t ω hz => itoDrift_Pcond θ A hN hh hz (H.hφ _ hz) (H.hΔ _ hz) (H.hx _ hz) t)
    (isStoppingTime_sigma H.hG H.hF s n)
    (fun T => ⟨Real.exp (cθ θ * T) * (Cφ + CA * T), ?_⟩)
  · have e : (fun t ω => Pcond h θ φ (Zc θ A G F s t ω)) = fun (u : ℝ≥0) ω =>
        Real.exp (cθ θ * u) * h (phase θ (Yst N 0 G F s) u ω) * Mc φ A G F s u ω :=
      funext fun u => funext fun ω => Pcond_Zc H.hG H.hFh θ φ A s u ω
    rw [e] at K
    exact ⟨K.1, K.2.1⟩
  · filter_upwards [H.hs] with ω hω r hr
    rw [stoppedProcess_eq_stopTime]
    show |Pcond h θ φ _| ≤ _
    rw [Pcond_Zc H.hG H.hFh, abs_mul]
    exact mul_le_mul (exp_mul_bound hb θ ((stopTime_le _ r).trans hr) _)
      (H.mc_stop_bound hω hCφ hCA0 hCA hr) (abs_nonneg _) (Real.exp_pos _).le

/-- **Properties of `Ms = Mc^{σ_n}`**: adapted and a.s. bounded on bounded intervals. -/
theorem CondHyp.ms_props [IsProbabilityMeasure Q] (H : CondHyp Q 𝓖 G F s n φ A) :
    (∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t]
        (stoppedProcess (Mc φ A G F s) (sig N G F s n) t)) ∧
      ∀ T : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ r ≤ T,
        |stoppedProcess (Mc φ A G F s) (sig N G F s n) r ω| ≤ C := by
  have e : (fun (u : ℝ≥0) ω => Real.exp (cθ (0 : Fin N → ℝ) * u) *
      Real.cos (phase 0 (Yst N 0 G F s) u ω) * Mc φ A G F s u ω) = Mc φ A G F s := by
    funext u ω; simp [phase_zero, cθ_zero]
  have K := (H.pcond_mart 0 trig_cos fun x => Real.abs_cos_le_one x).2
  rw [e] at K
  refine ⟨K, fun T => ?_⟩
  obtain ⟨Cφ, CA, hCφ, hCA0, hCA⟩ := H.exists_bounds
  refine ⟨Cφ + CA * T, ?_⟩
  filter_upwards [H.hs] with ω hω r hr
  rw [stoppedProcess_eq_stopTime]
  exact H.mc_stop_bound hω hCφ hCA0 hCA hr

end BlockBand.SourceProcess.Stochastic.ComplexAngular
