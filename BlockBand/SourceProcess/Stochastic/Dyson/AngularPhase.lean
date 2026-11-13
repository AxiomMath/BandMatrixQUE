module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularMart
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularTest

/-!
# The driving path `W = λ - ∫ b(λ)` and the angular phase

`Hyp Q 𝓖 N G F s f n` bundles the hypotheses of clause (b3) together with non-collision (b1).
With `Y = (λ, X)(F + G_{s+·})`:
* `Wp` is the driving path `W_u = λ_u - ∫_0^u b(λ_r) dr` (`N^{-1/2}` times the eigenvalue
  Brownian motion plus `λ_0`), and `phase θ = θ·W` a.s. (`phase_eq_Wd`);
* `Mt = f(X) - ∫ 𝒜 f` and `Ms = Mt^{σ_n}` (`σ_n` the gap stop).

The martingale identities of `e^{c_θ u} h(θ·W_u)` and `e^{c_θ u} h(θ·W_u) Ms_u` (`h = cos, sin`),
`Hyp.testMart_Zre` and `Hyp.testMart_ZreMs`, are proved in the sibling module.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime)

/-- Hypotheses of clause (b3), with non-collision (b1). -/
structure Hyp {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (N : ℕ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (f : (Fin N → ℝ) → ℝ) (n : ℕ) : Prop where
  hG : IsHermitianBrownian Q 𝓖 N G
  hF : Measurable[𝓖 0] F
  hFh : ∀ ω, (F ω).IsHermitian
  hb1 : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, 0 < t → HasSimpleSpectrum N (F ω + G t ω)
  hs : 0 < s
  hf : ContDiff ℝ 2 f
  hn : 0 < n

variable {N : ℕ} {Ω : Type}

/-- `θ·λ_u - ∫_0^u θ·b(λ_r) dr`. -/
def phase (θ : Fin N → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, θ i * lamOf (Y u ω) i -
    ∫ r in Ioc (0 : ℝ) u, ∑ i, θ i * dysonDrift N (lamOf (Y r.toNNReal ω)) i

/-- The driving path `W_u = λ_u - ∫_0^u b(λ_r) dr`. -/
def Wp (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) (i : Fin N) : ℝ :=
  phase (Pi.single i 1) Y u ω

/-- `θ·W_u`. -/
def Wd (θ : Fin N → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, θ i * Wp Y u ω i

/-- `f(X_u) - ∫_0^u 𝒜 f`. -/
def Mt (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  f (xOf (Y u ω)) - ∫ r in Ioc (0 : ℝ) u,
    angularGenerator N (lamOf (Y r.toNNReal ω)) f (xOf (Y r.toNNReal ω))

theorem ell_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : ell θ (Yplus θ f Y u ω) = phase θ Y u ω := by
  simp [ell_apply, Yplus, cL, cV, Vint, vdOf, phase, lamOf_eq]

theorem g2_Yplus (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ)
    (u : ℝ≥0) (ω : Ω) : g2 f (Yplus θ f Y u ω) = Mt f Y u ω := by
  rw [g2, prX_Yplus, prV1_Yplus, Mt]

theorem Phi_Yplus (h : ℝ → ℝ) (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ)
    (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) :
    Phi h θ (Yplus θ f Y u ω) = Real.exp (cθ θ * u) * h (phase θ Y u ω) := by
  rw [Phi, Efun, prV2_Yplus, ell_Yplus]

theorem phase_zero (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0) (ω : Ω) : phase 0 Y u ω = 0 := by
  simp [phase]

theorem cθ_zero : cθ (0 : Fin N → ℝ) = 0 := by simp [cθ]

theorem Pfun_zero_Yplus (f : (Fin N → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) (u : ℝ≥0)
    (ω : Ω) : Pfun Real.cos 0 f (Yplus 0 f Y u ω) = Mt f Y u ω := by
  rw [Pfun, Phi_Yplus, g2_Yplus, phase_zero, cθ_zero]; simp

/-- Linearity of the phase on samples with locally integrable eigenvalue drift. -/
theorem phase_eq_Wd_of {Y : ℝ≥0 → Ω → Fin (N + N) → ℝ} {ω : Ω}
    (hint : ∀ u : ℝ≥0, ∀ i, IntegrableOn
      (fun r : ℝ => dysonDrift N (lamOf (Y r.toNNReal ω)) i) (Ioc 0 u))
    (θ : Fin N → ℝ) (u : ℝ≥0) : phase θ Y u ω = Wd θ Y u ω := by
  simp only [Wd, Wp, phase, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_sub, Finset.sum_sub_distrib]
  rw [integral_finsetSum _ fun i _ => (hint u i).const_mul (θ i)]
  simp_rw [integral_const_mul]

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

omit [IsProbabilityMeasure Q] in
theorem Hyp.phase_eq_Wd (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ) :
    ∀ᵐ ω ∂Q, ∀ u, phase θ (Yst N q G F s) u ω = Wd θ (Yst N q G F s) u ω := by
  filter_upwards [H.hb1] with ω hω u
  refine phase_eq_Wd_of (fun u i => ?_) θ u
  have hc := continuous_vd_path H.hG H.hs hω q (Pi.single i 1) H.hf
  have : Continuous fun r : ℝ => dysonDrift N (lamOf (Yst N q G F s r.toNNReal ω)) i := by
    have h0 := (continuous_apply 0).comp hc
    refine h0.congr fun r => ?_
    simp [vdOf, Pi.single_apply]
  exact this.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem Hyp.adapted_phase (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (θ : Fin N → ℝ)
    (u : ℝ≥0) :
    StronglyMeasurable[shiftFiltration 𝓖 s u] fun ω => phase θ (Yst N q G F s) u ω := by
  have hY := (isContinuousSemimartingale_Yplus H.hG H.hF H.hFh H.hb1 H.hs q θ H.hf).adapted u
  have e : (fun ω => phase θ (Yst N q G F s) u ω) =
      fun ω => ell θ (Yplus θ f (Yst N q G F s) u ω) := funext fun ω => (ell_Yplus θ f _ u ω).symm
  rw [e]
  exact (ell θ).continuous.comp_stronglyMeasurable hY

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
