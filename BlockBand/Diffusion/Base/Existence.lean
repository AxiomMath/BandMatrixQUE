module

public import BlockBand.Diffusion.Base.Model
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionHolds
public import BlockBand.SourceProcess.Stochastic.Bridges.NativeIto
public import BlockBand.SourceProcess.Stochastic.Bridges.MartingaleProblemConverse
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Main
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Adapted

/-!
# Existence of the base diffusion

`hasExBaseDiffusion`: for every `D₀ > 0` and every starting point of the closed strip, the base
diffusion exists. It is realized as `Φ(U)` for the global strong solution `U` of the linear
five-dimensional equation of `exDrift`, `exDiff` started on the sphere `|v| = 1`: the solution
solves the martingale problem on `ℝ⁵`, Itô's formula holds without localization for bounded tests,
the sphere is conserved almost surely, and the generator identity `exGen_comp_exPhi` transfers the
martingale problem to `Φ(U)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

/-!
### Generic facts
-/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- With a filtration for which `Y` is adapted, a process a.s. equal at every time to a
martingale is a martingale. -/
theorem martingale_of_ae_eq {M Y : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P)
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) (h : ∀ t, Y t =ᵐ[P] M t) : Martingale Y 𝓖 P :=
  ⟨hY, fun i j hij => (condExp_congr_ae (h j)).trans ((hM.2 i j hij).trans (h i).symm)⟩

/-- A property of a continuous process that is closed in time and holds a.s. at each fixed time
holds a.s. at all times. -/
theorem ae_forall_of_continuous {E : Type*} [TopologicalSpace E] {X : ℝ≥0 → Ω → E}
    {S : Set E} (hS : IsClosed S) (hX : ∀ᵐ ω ∂P, Continuous fun t => X t ω)
    (h : ∀ t, ∀ᵐ ω ∂P, X t ω ∈ S) : ∀ᵐ ω ∂P, ∀ t, X t ω ∈ S := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD := (ae_ball_iff hDc).2 fun t _ => h t
  filter_upwards [hD, hX] with ω hω hc t
  have hcl : IsClosed {t | X t ω ∈ S} := hS.preimage hc
  have hsub : closure D ⊆ {t | X t ω ∈ S} := hcl.closure_subset_iff.2 fun t ht => hω t ht
  exact hsub (hDd.closure_eq.symm ▸ mem_univ t)

end Generic

/-!
### The probability space
-/

/-- The driver space with six Brownian drivers. -/
abbrev ExΩ : Type := DriverSample Unit (Fin 6)

/-- The law of the drivers. -/
def exP : Measure ExΩ := driverLaw (κ := Fin 6) (Measure.dirac ())

instance : IsProbabilityMeasure exP := by
  unfold exP
  infer_instance

/-- The augmented driver filtration `F_t ∨ N`. -/
def ex𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace ExΩ) :=
  driverAugmented (κ := Fin 6) (Measure.dirac ())

/-!
### Regularity of the coefficients
-/

theorem contDiff_exDrift (D0 : ℝ) : ContDiff ℝ 1 (exDrift D0) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [exDrift] <;> fun_prop

theorem contDiff_exDiff (D0 : ℝ) (c : Fin 6) : ContDiff ℝ 1 (exDiff D0 c) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases c <;> fin_cases i <;> simp [exDiff] <;> fun_prop

theorem continuous_exCov (D0 : ℝ) : Continuous (exCov D0) := by
  have h := fun c => (contDiff_exDiff D0 c).continuous
  unfold exCov
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.of_apply]
  exact continuous_finsetSum _ fun c _ =>
    ((continuous_apply i).comp (h c)).mul ((continuous_apply j).comp (h c))

theorem norm_sq_le_wsq_wOne (y : Fin 5 → ℝ) : ‖y‖ ^ 2 ≤ wsq wOne y := by
  have h0 : 0 ≤ wsq wOne y := wsq_nonneg (fun _ => zero_le_one) y
  have hle : ‖y‖ ≤ √(wsq wOne y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have := Finset.single_le_sum (f := fun j => wOne j * (y j * y j))
      (fun j _ => mul_nonneg zero_le_one (mul_self_nonneg (y j))) (Finset.mem_univ i)
    simp only [wOne, one_mul] at this
    unfold wsq wOne
    simpa [sq] using this
  calc ‖y‖ ^ 2 ≤ √(wsq wOne y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = wsq wOne y := Real.sq_sqrt h0

/-- **A global strong solution** of the linear equation from any start. -/
theorem exists_exSol {D0 : ℝ} (hD0 : 0 ≤ D0) (y₀ : Fin 5 → ℝ) :
    ∃ U : ℝ≥0 → ExΩ → Fin 5 → ℝ,
      IsSDESolution (κ := Fin 6) (Measure.dirac ()) (exDrift D0) (exDiff D0) (fun _ => y₀) U := by
  refine NativeSDE.nonexplosionFor_holds (κ := Fin 6) (Measure.dirac ()) (Fin 5 → ℝ)
    (exDrift D0) (exDiff D0) (contDiff_exDrift D0).locallyLipschitz
    (fun c => (contDiff_exDiff D0 c).locallyLipschitz) (fun _ => y₀) stronglyMeasurable_const
    univ isClosed_univ (ae_of_all _ fun _ => mem_univ _)
    (fun _ _ _ => ae_of_all _ fun _ _ => mem_univ _) (wsq wOne) (3 * D0)
    ((contDiff_wsq wOne).of_le le_top) (fun y _ => wsq_nonneg (fun _ => zero_le_one) y)
    (fun M => ⟨|M| + 1, fun y _ hy => ?_⟩) (fun y _ => exGen_lyap_le hD0 y)
  have h1 : 1 ≤ |M| + 1 := by linarith [abs_nonneg M]
  have h2 : (|M| + 1) ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  nlinarith [le_abs_self M, norm_sq_le_wsq_wOne y]

/-- The solution as an Itô process with its coefficients. -/
theorem exSol_native {D0 : ℝ} {y₀ : Fin 5 → ℝ} {U : ℝ≥0 → ExΩ → Fin 5 → ℝ}
    (hU : IsSDESolution (κ := Fin 6) (Measure.dirac ()) (exDrift D0) (exDiff D0) (fun _ => y₀) U) :
    IsNativeItoProcess (κ := Fin 6) (Measure.dirac ()) U (fun t x => exDrift D0 (U t x))
      (fun c t x => exDiff D0 c (U t x)) := by
  have h := hU.1
  have e1 : switchOff (fun _ => (⊤ : WithTop ℝ≥0)) (fun t x => exDrift D0 (U t x)) =
      fun t x => exDrift D0 (U t x) := by
    funext t x
    exact ite_eq_left le_top
  have e2 : (fun c => switchOff (fun _ => (⊤ : WithTop ℝ≥0)) fun t x => exDiff D0 c (U t x)) =
      fun c t x => exDiff D0 c (U t x) := by
    funext c t x
    exact ite_eq_left le_top
  rwa [e1, e2] at h

/-- The solution solves the `(exDrift, exCov)` martingale problem on `ℝ⁵`. -/
theorem exSol_isMPSolutionOn {D0 : ℝ} {y₀ : Fin 5 → ℝ} {U : ℝ≥0 → ExΩ → Fin 5 → ℝ}
    (hU : IsSDESolution (κ := Fin 6) (Measure.dirac ()) (exDrift D0) (exDiff D0) (fun _ => y₀) U) :
    IsMPSolutionOn exP ex𝓖 (exDrift D0) (exCov D0) univ U :=
  (exSol_native hU).isContinuousSemimartingale.isMPSolutionOn
    (contDiff_exDrift D0).continuous.continuousOn (continuous_exCov D0).continuousOn

/-- **Itô's formula without localization** for a solution of the martingale problem on `ℝ⁵`
with continuous coefficients: if `φ ∈ C²` is bounded by `A` and `𝓛φ(U_s)` is a.s. bounded by
`B` for all `s`, then `φ(U_t) − φ(U_0) − ∫₀ᵗ 𝓛φ(U_s) ds` has a martingale modification. -/
theorem hasMartingaleModification_ito {b : (Fin 5 → ℝ) → Fin 5 → ℝ}
    {a : (Fin 5 → ℝ) → Matrix (Fin 5) (Fin 5) ℝ} (hb : Continuous b) (ha : Continuous a)
    {U : ℝ≥0 → ExΩ → Fin 5 → ℝ} (hU : IsMPSolutionOn exP ex𝓖 b a univ U)
    {φ : (Fin 5 → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) {A B : ℝ} (hA : ∀ y, |φ y| ≤ A)
    (hB : ∀ᵐ ω ∂exP, ∀ s, |mpGenerator b a φ (U s ω)| ≤ B) :
    HasMartingaleModification exP ex𝓖 (fun t ω => φ (U t ω) - φ (U 0 ω) -
      ∫ s in Ioc (0 : ℝ) t, mpGenerator b a φ (U s.toNNReal ω)) := by
  refine Bridges.hasMartingaleModification_of_localized
    (τ := fun n => exitTimeFrom (ball (0 : Fin 5 → ℝ) n) U) ?_ (fun n => ?_) (fun t => ?_)
  · filter_upwards [hU.continuous] with ω hω using Bridges.tendsto_exitTimeFrom_ball hω
  · obtain ⟨M, hM, hMe⟩ := martingaleProblemIto_holds 5 ExΩ exP ex𝓖 b a univ isOpen_univ
      hb.continuousOn ha.continuousOn U hU φ hφ.contDiffOn _ (Bridges.isInteriorDomain_ball_univ n)
    exact ⟨M, hM, hMe⟩
  · have hB0 : 0 ≤ B := by
      obtain ⟨ω, hω⟩ := hB.exists
      exact (abs_nonneg _).trans (hω 0)
    refine ⟨2 * A + B * t, ?_⟩
    filter_upwards [hB] with ω hω s hs
    have hI : |∫ u in Ioc (0 : ℝ) s, mpGenerator b a φ (U u.toNNReal ω)| ≤ B * s := by
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) s)
        (C := B) (f := fun u => mpGenerator b a φ (U u.toNNReal ω)) measure_Ioc_lt_top
        (fun u _ => by rw [Real.norm_eq_abs]; exact hω _)
      rwa [Real.norm_eq_abs, Real.volume_real_Ioc_of_le (NNReal.coe_nonneg s), sub_zero] at h
    have hst : B * (s : ℝ) ≤ B * t := mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hs) hB0
    calc |φ (U s ω) - φ (U 0 ω) - ∫ u in Ioc (0 : ℝ) s, mpGenerator b a φ (U u.toNNReal ω)|
        ≤ |φ (U s ω)| + |φ (U 0 ω)| + |∫ u in Ioc (0 : ℝ) s, mpGenerator b a φ (U u.toNNReal ω)| :=
          (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ ≤ 2 * A + B * t := by linarith [hA (U s ω), hA (U 0 ω)]

/-!
### Conservation of the sphere
-/

theorem sphereDefect_eq_zero_iff (y : Fin 5 → ℝ) : sphereDefect y = 0 ↔ wsq wV y = 1 := by
  unfold sphereDefect
  rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem sphereDefect_nonneg (y : Fin 5 → ℝ) : 0 ≤ sphereDefect y := sq_nonneg _

/-- **The sphere `|v| = 1` is conserved** for all times, almost surely. -/
theorem ae_forall_sphere {D0 : ℝ} (hD0 : 0 ≤ D0) {y₀ : Fin 5 → ℝ} (hy₀ : wsq wV y₀ = 1)
    {U : ℝ≥0 → ExΩ → Fin 5 → ℝ}
    (hU : IsSDESolution (κ := Fin 6) (Measure.dirac ()) (exDrift D0) (exDiff D0) (fun _ => y₀) U) :
    ∀ᵐ ω ∂exP, ∀ t, wsq wV (U t ω) = 1 := by
  have hMP := exSol_isMPSolutionOn hU
  have h0 : ∀ᵐ ω ∂exP, U 0 ω = y₀ := hU.2
  have hψ0 : sphereDefect y₀ = 0 := (sphereDefect_eq_zero_iff y₀).2 hy₀
  have hstop : ∀ (n : ℕ) (t : ℝ≥0), ∀ᵐ ω ∂exP,
      sphereDefect (U (stopTime (exitTimeFrom (ball (0 : Fin 5 → ℝ) n) U ω) t) ω) = 0 := by
    intro n t
    obtain ⟨M, hM, hMe⟩ := martingaleProblemIto_holds 5 ExΩ exP ex𝓖 (exDrift D0) (exCov D0)
      univ isOpen_univ (contDiff_exDrift D0).continuous.continuousOn
      (continuous_exCov D0).continuousOn U hMP sphereDefect
      ((contDiff_sphereDefect.of_le le_top : ContDiff ℝ 2 sphereDefect).contDiffOn) _
      (Bridges.isInteriorDomain_ball_univ n)
    have hval : ∀ s, ∀ᵐ ω ∂exP,
        M s ω = sphereDefect (U (stopTime (exitTimeFrom (ball (0 : Fin 5 → ℝ) n) U ω) s) ω) := by
      intro s
      filter_upwards [hMe s, h0] with ω h1 h2
      rw [h1, stoppedProcess_eq_stopTime]
      simp only [exGen_sphereDefect hD0, integral_zero, sub_zero, h2, hψ0]
    have hM0 : M 0 =ᵐ[exP] 0 := by
      filter_upwards [hval 0, h0] with ω h1 h2
      rw [h1, le_antisymm (stopTime_le _ 0) zero_le, h2, hψ0, Pi.zero_apply]
    have hint : ∫ ω, M t ω ∂exP = 0 := by
      have h := hM.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
      rw [setIntegral_univ, setIntegral_univ, integral_congr_ae hM0] at h
      rw [← h]
      simp
    have hnn : 0 ≤ᵐ[exP] M t := by
      filter_upwards [hval t] with ω h
      rw [h]
      exact sphereDefect_nonneg _
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn (hM.integrable t)).1 hint, hval t]
      with ω h1 h2
    rw [← h2]
    exact h1
  have hfix : ∀ t, ∀ᵐ ω ∂exP, U t ω ∈ {y | sphereDefect y = 0} := by
    intro t
    filter_upwards [ae_all_iff.2 fun n => hstop n t, hMP.continuous] with ω h hc
    obtain ⟨n, hn⟩ :=
      ((WithTop.tendsto_nhds_top_iff _).1 (Bridges.tendsto_exitTimeFrom_ball hc) t).exists
    have h' := h n
    rwa [stopTime_of_lt hn] at h'
  filter_upwards [ae_forall_of_continuous
    (isClosed_eq contDiff_sphereDefect.continuous continuous_const) hMP.continuous hfix]
    with ω h t
  exact (sphereDefect_eq_zero_iff _).1 (h t)

/-!
### The base generator of a smooth compactly supported test
-/

theorem continuous_exBaseGenerator {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (D0 : ℝ) :
    Continuous (exBaseGenerator D0 f) := by
  have hd1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hg : ∀ v, ContDiff ℝ 1 (fun w => fderiv ℝ f w v) := fun v =>
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h1 : ∀ v, Continuous fun z => fderiv ℝ f z v := fun v => hd1.clm_apply continuous_const
  have h2 : ∀ v, Continuous fun z => fderiv ℝ (fun w => fderiv ℝ f w v) z v := fun v =>
    ((hg v).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have a1 := h1 (1, 0)
  have a2 := h1 (0, 1)
  have b1 := h2 (1, 0)
  have b2 := h2 (0, 1)
  unfold exBaseGenerator
  fun_prop

theorem hasCompactSupport_exBaseGenerator {f : ℝ × ℝ → ℝ} (hcs : HasCompactSupport f)
    (D0 : ℝ) : HasCompactSupport (exBaseGenerator D0 f) := by
  refine HasCompactSupport.intro (K := tsupport f) hcs fun z hz => ?_
  have h1 : fderiv ℝ f z = 0 :=
    Function.notMem_support.1 fun h => hz (support_fderiv_subset ℝ h)
  have h2 : ∀ v, fderiv ℝ (fun w => fderiv ℝ f w v) z = 0 := by
    intro v
    have hsub : tsupport (fun w => fderiv ℝ f w v) ⊆ tsupport f := by
      refine closure_minimal (fun w hw => ?_) (isClosed_tsupport f)
      refine support_fderiv_subset ℝ (Function.mem_support.2 fun h0 => hw ?_)
      simp [h0]
    exact Function.notMem_support.1 fun h => hz (hsub (support_fderiv_subset ℝ h))
  simp [exBaseGenerator, h1, h2]

theorem exY_mem_Icc {y : Fin 5 → ℝ} (hy : wsq wV y = 1) : exY y ∈ Icc (0 : ℝ) 1 := by
  simp only [wsq, Fin.sum_univ_five, wV] at hy
  simp at hy
  have h4 : y 4 ^ 2 ≤ 1 := by nlinarith [mul_self_nonneg (y 2), mul_self_nonneg (y 3)]
  unfold exY
  constructor <;> nlinarith

/-!
### Assembly
-/

/-- **`Z = Φ(U)` is the base diffusion from `z`.** -/
theorem isExBaseDiffusion_exPhi {D0 : ℝ} (hD0 : 0 ≤ D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip)
    {U : ℝ≥0 → ExΩ → Fin 5 → ℝ}
    (hU : IsSDESolution (κ := Fin 6) (Measure.dirac ()) (exDrift D0) (exDiff D0)
      (fun _ => exStart z) U) :
    IsExBaseDiffusion exP ex𝓖 D0 z (fun t ω => exPhi (U t ω)) := by
  have hN := exSol_native hU
  have hsph := ae_forall_sphere hD0 (wsq_wV_exStart hz) hU
  refine ⟨inferInstance, fun t => ?_, ?_, ?_, fun f hf hcs => ?_⟩
  · exact contDiff_exPhi.continuous.measurable.comp (hN.adapted t).measurable
  · filter_upwards [hU.2] with ω hω
    rw [hω]
    exact exPhi_exStart hz
  · filter_upwards [hN.continuous, hsph] with ω hc hs
    exact ⟨contDiff_exPhi.continuous.comp hc, fun t => ⟨mem_Ici.2 (exX_nonneg _),
      exY_mem_Icc (hs t)⟩⟩
  · have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
    have hφ : ContDiff ℝ 2 (f ∘ exPhi) := hf2.comp (contDiff_exPhi.of_le le_top)
    obtain ⟨A, hA⟩ := hf2.continuous.bounded_above_of_compact_support hcs
    obtain ⟨B, hB⟩ := (continuous_exBaseGenerator hf2 D0).bounded_above_of_compact_support
      (hasCompactSupport_exBaseGenerator hcs D0)
    have hgen : ∀ᵐ ω ∂exP, ∀ s, mpGenerator (exDrift D0) (exCov D0) (f ∘ exPhi) (U s ω) =
        exBaseGenerator D0 f (exPhi (U s ω)) := by
      filter_upwards [hsph] with ω h s using exGen_comp_exPhi hD0 hf2 (h s)
    obtain ⟨M, hM, hMe⟩ := hasMartingaleModification_ito (contDiff_exDrift D0).continuous
      (continuous_exCov D0) (exSol_isMPSolutionOn hU) hφ (A := A) (B := B)
      (fun y => by simpa [Real.norm_eq_abs] using hA (exPhi y))
      (by
        filter_upwards [hgen] with ω h s
        rw [h s]
        simpa [Real.norm_eq_abs] using hB _)
    have hprog : IsStronglyProgressive ex𝓖
        (fun s ω => exBaseGenerator D0 f (exPhi (U s ω))) := fun i =>
      ((continuous_exBaseGenerator hf2 D0).comp contDiff_exPhi.continuous).comp_stronglyMeasurable
        (hN.progressive i)
    refine martingale_of_ae_eq (hM.add (martingale_const ex𝓖 exP (f z))) (fun t => ?_)
      (fun t => ?_)
    · exact ((hf2.continuous.comp contDiff_exPhi.continuous).comp_stronglyMeasurable
        (hN.adapted t)).sub (SemimartingaleIto.stronglyMeasurable_integral_of_progressive hprog t)
    · filter_upwards [hMe t, hgen, hU.2] with ω h1 h2 h3
      simp only [Pi.add_apply]
      rw [h1]
      have hI : ∫ s in Ioc (0 : ℝ) t, mpGenerator (exDrift D0) (exCov D0) (f ∘ exPhi)
          (U s.toNNReal ω) = ∫ s in Ioc (0 : ℝ) t, exBaseGenerator D0 f (exPhi (U s.toNNReal ω)) :=
        integral_congr_ae (Eventually.of_forall fun s => h2 _)
      rw [hI, Function.comp_apply, Function.comp_apply, h3, exPhi_exStart hz]
      ring

/-- **Existence of the base diffusion** from every point of the closed strip, for every
`D₀ ≥ 0`. -/
theorem hasExBaseDiffusion_of_nonneg {D0 : ℝ} (hD0 : 0 ≤ D0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) :
    HasExBaseDiffusion D0 z := by
  obtain ⟨U, hU⟩ := exists_exSol hD0 (exStart z)
  exact ⟨ExΩ, inferInstance, ex𝓖, exP, _, isExBaseDiffusion_exPhi hD0 hz hU⟩

/-- **Existence of the base diffusion** `∀ D₀ > 0, ∀ z ∈ [0,∞) × [0,1]`. -/
theorem hasExBaseDiffusion : ∀ D0 : ℝ, 0 < D0 → ∀ z ∈ exBaseStrip, HasExBaseDiffusion D0 z :=
  fun _ hD0 _ hz => hasExBaseDiffusion_of_nonneg hD0.le hz

end BlockBand.Diffusion
