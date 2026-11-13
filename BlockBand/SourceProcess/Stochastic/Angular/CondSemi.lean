module

public import BlockBand.SourceProcess.Stochastic.Angular.CondIto
public import BlockBand.SourceProcess.Stochastic.Dyson.AngularPhase

/-!
# Complex angular martingale problem: the conditioning state is a semimartingale

* `zeroDrift_stoppedU`: the analogue of `zeroDrift_stopped` for a function
  that is `C²` and has zero Itô drift only on an open set `U`, which the path stays in a.s.
  It uses the Itô formula `SemimartingaleItoFormula` with this `U`, `StoppedSemimartingale`, and
  removal of the localization by domination.
* The state `Zc θ A G F s u = (y_u, ∫θ·b(λ(y)), ∫A(y), u)` with `y_u = hermVec(F + G_{s+u})`,
  and `isContinuousSemimartingale_Zc`: it is a continuous semimartingale for `u ↦ 𝓖_{s+u}`
  with characteristics `condDrift θ A`, `condCov N`, when a.s. the spectrum of `F + G_{s+v}`
  is simple for every `v ≥ 0` and `A` is measurable and continuous on `simpleSet N`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_le stopTime_zero
  stoppedProcess_eq_stopTime)

/-- **Zero-drift functions on an open set, stopped, are martingales (modification form).** -/
theorem zeroDrift_stoppedU {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓕 Y β α) {U : Set (Fin d → ℝ)} (hUo : IsOpen U)
    (hU : ∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U) {g : (Fin d → ℝ) → ℝ} (hgm : Measurable g)
    (hg : ∀ y ∈ U, ContDiffAt ℝ 2 g y)
    (hzero : ∀ t ω, Y t ω ∈ U →
      itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) (Y t ω) t (β t ω) (α t ω) = 0)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    (hbd : ∀ T, ∃ C, ∀ᵐ ω ∂Q, ∀ r ≤ T, |stoppedProcess (fun t ω => g (Y t ω)) ρ r ω| ≤ C) :
    HasMartingaleModification Q 𝓕 (stoppedProcess (fun t ω => g (Y t ω)) ρ) ∧
      (∀ t, StronglyMeasurable[𝓕 t] (stoppedProcess (fun t ω => g (Y t ω)) ρ t)) ∧
      ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess (fun t ω => g (Y t ω)) ρ t ω := by
  have hgU : ContDiffOn ℝ 2 (fun p : ℝ × (Fin d → ℝ) => g p.2) (Set.univ ×ˢ U) :=
    fun p hp => ((hg p.2 hp.2).comp p contDiff_snd.contDiffAt).contDiffWithinAt
  have hI := SemimartingaleIto.semimartingaleItoFormula_holds d Ω Q 𝓕 Y β α H U hUo hU
    (fun p => g p.2) (hgm.comp measurable_snd) hgU
  have hS := Semimartingale.stoppedSemimartingale_holds 1 Ω Q 𝓕 _ _ _ hI ρ hρ
  set Z := stoppedProcess (fun t ω => g (Y t ω)) ρ with hZdef
  have hZ0 : ∀ ω, Z 0 ω = g (Y 0 ω) := fun ω => by
    simp only [Z, stoppedProcess_eq_stopTime, stopTime_zero]
  refine ⟨?_, fun t => ?_, ?_⟩
  · obtain ⟨τ, -, hτlim, hloc⟩ := hS.localizing
    set X : ℝ≥0 → Ω → ℝ := fun t ω => Z t ω - g (Y 0 ω)
    have hcomp : ∀ᵐ ω ∂Q, ∀ t, smCompensated (stoppedProcess (fun t ω (_ : Fin 1) =>
        (fun p : ℝ × (Fin d → ℝ) => g p.2) ((t : ℝ), Y t ω)) ρ)
        (switchAfter ρ fun t ω (_ : Fin 1) => itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2)
          (Y t ω) t (β t ω) (α t ω)) 0 t ω = X t ω := by
      filter_upwards [hU] with ω hω t
      have hz : ∀ s : ℝ≥0, itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) (Y s ω) s (β s ω)
          (α s ω) = 0 := fun s => hzero s ω (hω s)
      simp only [smCompensated, switchAfter, hz, X, Z, stoppedProcess_eq_stopTime,
        stopTime_zero]
      have : ∀ s : ℝ, ((if ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ ω then fun _ : Fin 1 => (0 : ℝ)
          else 0) 0) = 0 := fun s => by split_ifs <;> rfl
      simp only [this, integral_zero, sub_zero]
    have hX : HasMartingaleModification Q 𝓕 X := by
      refine hasMartingaleModification_of_localized hτlim (fun n => ?_) (fun T => ?_)
      · refine Dyson.hasMM_congr ((hloc n).1 0) fun t => ?_
        filter_upwards [hcomp] with ω hω
        simp only [stoppedProcess_eq_stopTime, hω]
      · obtain ⟨C, hC⟩ := hbd T
        refine ⟨C + C, ?_⟩
        filter_upwards [hC] with ω hω r hr
        have h0 := hω 0 zero_le
        rw [hZ0] at h0
        calc |X r ω| ≤ |Z r ω| + |g (Y 0 ω)| := abs_sub _ _
          _ ≤ C + C := add_le_add (hω r hr) h0
    have hm0 : StronglyMeasurable[𝓕 0] fun ω => g (Y 0 ω) :=
      (hgm.comp (H.adapted 0).measurable).stronglyMeasurable
    obtain ⟨C, hC⟩ := hbd 0
    have hint : Integrable (fun ω => g (Y 0 ω)) Q := by
      refine Integrable.of_bound (hm0.mono (𝓕.le 0)).aestronglyMeasurable C ?_
      filter_upwards [hC] with ω hω
      have := hω 0 le_rfl; rwa [hZ0, ← Real.norm_eq_abs] at this
    have hconst : HasMartingaleModification Q 𝓕 (fun _ ω => g (Y 0 ω)) := by
      refine ⟨fun _ ω => g (Y 0 ω), ⟨fun t => hm0.mono (𝓕.mono zero_le), fun i j _ => ?_⟩,
        fun _ => ae_of_all _ fun _ => rfl⟩
      show Q[fun ω => g (Y 0 ω) | 𝓕 i] =ᵐ[Q] fun ω => g (Y 0 ω)
      rw [condExp_of_stronglyMeasurable (𝓕.le i) (hm0.mono (𝓕.mono zero_le)) hint]
    refine Dyson.hasMM_congr (Dyson.hasMM_add hX hconst) fun t => ae_of_all _ fun ω => ?_
    simp [X]
  · exact (continuous_apply 0).comp_stronglyMeasurable (hS.adapted t)
  · filter_upwards [hS.continuous] with ω hω
    exact (continuous_apply 0).comp hω

/-!
### Regularity of the drift
-/

variable {N : ℕ}

theorem measurable_lam (i : Fin N) : Measurable (lam N i) :=
  (measurable_dysonEigenvalue i).comp continuous_vecHerm.measurable

theorem measurable_thDrift (θ : Fin N → ℝ) :
    Measurable fun y : Fin (N * N) → ℝ => ∑ i, θ i * dysonDrift N (fun j => lam N j y) i := by
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  unfold dysonDrift
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    measurable_const.div ((measurable_lam i).sub (measurable_lam j)))

theorem measurable_condVd (θ : Fin N → ℝ) {A : (Fin (N * N) → ℝ) → ℝ} (hA : Measurable A) :
    Measurable (condVd θ A) := by
  refine measurable_pi_iff.2 fun k => ?_
  fin_cases k
  · simpa [condVd] using measurable_thDrift θ
  · simpa [condVd] using hA
  · simp [condVd]

theorem continuousAt_thDrift (θ : Fin N → ℝ) {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ContinuousAt (fun y : Fin (N * N) → ℝ => ∑ i, θ i * dysonDrift N (fun j => lam N j y) i)
      y := by
  refine tendsto_finsetSum _ fun i _ => continuousAt_const.mul ?_
  unfold dysonDrift
  refine continuousAt_const.mul (tendsto_finsetSum _ fun j hj => ?_)
  have hc : ∀ k, ContinuousAt (lam N k) y := fun k =>
    (contDiffAt_eigenvalue (n := 0) hy k).continuousAt
  refine continuousAt_const.div ((hc i).sub (hc j)) (sub_ne_zero.2 ?_)
  exact HasSimpleSpectrum.ne hy (Ne.symm (Finset.ne_of_mem_erase hj))

theorem continuousOn_condVd (θ : Fin N → ℝ) {A : (Fin (N * N) → ℝ) → ℝ}
    (hA : ContinuousOn A (simpleSet N)) : ContinuousOn (condVd θ A) (simpleSet N) := by
  intro y hy
  refine (continuousAt_pi.2 fun k => ?_).continuousWithinAt
  fin_cases k
  · simpa [condVd] using continuousAt_thDrift θ hy
  · simpa [condVd] using hA.continuousAt (isOpen_simpleSet.mem_nhds hy)
  · simp only [condVd]; exact continuousAt_const

/-!
### The state
-/

variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

/-- The coordinates `y_u = hermVec(F + G_{s+u})`. -/
def ycd (N : ℕ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (u : ℝ≥0) (ω : Ω) : Fin (N * N) → ℝ :=
  hermVec N (F ω + G (s + u) ω)

/-- The auxiliary integrals `∫_0^u condVd θ A (y_r) dr`. -/
def Vc (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (u : ℝ≥0) (ω : Ω) : Fin 3 → ℝ :=
  fun k => ∫ r in Ioc (0 : ℝ) u, condVd θ A (ycd N G F s r.toNNReal ω) k

/-- The state `(y_u, V_u)`. -/
def Zc (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (F : Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (u : ℝ≥0) (ω : Ω) : Fin (N * N + 3) → ℝ :=
  concatCoord (ycd N G F s u ω) (Vc θ A G F s u ω)

theorem stY_concatCoord (y : Fin (N * N) → ℝ) (v : Fin 3 → ℝ) : stY N (concatCoord y v) = y := by
  funext a; simp [cstY]

theorem concatCoord_cstW (y : Fin (N * N) → ℝ) (v : Fin 3 → ℝ) (k : Fin 3) :
    concatCoord y v (cstW N k) = v k := by
  simp [cstW]

omit [MeasurableSpace Ω] in
theorem stY_Zc (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (s u : ℝ≥0) (ω : Ω) :
    stY N (Zc θ A G F s u ω) = ycd N G F s u ω := stY_concatCoord _ _

omit [MeasurableSpace Ω] in
theorem stW_Zc (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) (s u : ℝ≥0) (ω : Ω) (k : Fin 3) :
    stW N k (Zc θ A G F s u ω) = Vc θ A G F s u ω k := by
  rw [stW_apply, Zc, concatCoord_cstW]

/-- The set `simpleSet × ℝ³`. -/
def Uc (N : ℕ) : Set (Fin (N * N + 3) → ℝ) := stY N ⁻¹' simpleSet N

theorem isOpen_Uc : IsOpen (Uc N) := isOpen_simpleSet.preimage (stY N).continuous

/-- The a.s. simple-spectrum hypothesis of `GenericConditioning` gives a path in `simpleSet`. -/
theorem ycd_mem {s : ℝ≥0} (hG : IsHermitianBrownian Q 𝓖 N G) (hFh : ∀ ω, (F ω).IsHermitian)
    {ω : Ω} (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (v : ℝ≥0) :
    ycd N G F s v ω ∈ simpleSet N := by
  show HasSimpleSpectrum N (vecHerm N (hermVec N _))
  rw [vecHerm_hermVec (herm_add hG hFh _ ω)]; exact hω v

theorem continuous_ycd (hG : IsHermitianBrownian Q 𝓖 N G) (s : ℝ≥0) (ω : Ω) :
    Continuous fun r : ℝ => ycd N G F s r.toNNReal ω :=
  continuous_hermVec.comp ((continuous_hermBM_add hG F ω).comp
    (continuous_const.add continuous_real_toNNReal))

theorem continuous_condVd_path {s : ℝ≥0} (hG : IsHermitianBrownian Q 𝓖 N G)
    (hFh : ∀ ω, (F ω).IsHermitian) {ω : Ω}
    (hω : ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω)) (θ : Fin N → ℝ)
    {A : (Fin (N * N) → ℝ) → ℝ} (hA : ContinuousOn A (simpleSet N)) :
    Continuous fun r : ℝ => condVd θ A (ycd N G F s r.toNNReal ω) :=
  (continuousOn_condVd θ hA).comp_continuous (continuous_ycd hG s ω)
    fun _ => ycd_mem hG hFh hω _

/-- **The conditioning state is a continuous semimartingale.** -/
theorem isContinuousSemimartingale_Zc [IsProbabilityMeasure Q]
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (hFh : ∀ ω, (F ω).IsHermitian)
    {s : ℝ≥0} (hs : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F ω + G (s + v) ω))
    (θ : Fin N → ℝ) {A : (Fin (N * N) → ℝ) → ℝ} (hAm : Measurable A)
    (hA : ContinuousOn A (simpleSet N)) :
    IsContinuousSemimartingale Q (shiftFiltration 𝓖 s) (Zc θ A G F s)
      (fun u ω => condDrift θ A (Zc θ A G F s u ω)) (fun _ _ => condCov N) := by
  have hY := isContinuousSemimartingale_hermVec hG hF s
  have hvd : IsStronglyProgressive (shiftFiltration 𝓖 s)
      (fun u ω => condVd θ A (ycd N G F s u ω)) :=
    IsStronglyProgressive.comp_measurable' hY.progressive (measurable_condVd θ hAm)
  have hV : IsStronglyProgressive (shiftFiltration 𝓖 s) (Vc θ A G F s) :=
    Angular.isStronglyProgressive_pi fun k => Angular.isStronglyProgressive_integral
      (g := fun u ω => condVd θ A (ycd N G F s u ω) k)
      (IsStronglyProgressive.comp_measurable' hvd (measurable_pi_apply k))
  have hac : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, ∀ k, IntegrableOn
      (fun r : ℝ => condVd θ A (ycd N G F s r.toNNReal ω) k) (Ioc 0 t) ∧
      Vc θ A G F s t ω k = Vc θ A G F s 0 ω k +
        ∫ r in Ioc (0 : ℝ) t, condVd θ A (ycd N G F s r.toNNReal ω) k := by
    filter_upwards [hs] with ω hω t k
    refine ⟨?_, by simp [Vc]⟩
    exact ((continuous_apply k).comp (continuous_condVd_path hG hFh hω θ hA)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have H := hY.concat_ac hV hvd hac
  have e1 : (fun u ω => condDrift θ A (Zc θ A G F s u ω)) =
      fun u ω => concatCoord (0 : Fin (N * N) → ℝ) (condVd θ A (ycd N G F s u ω)) := by
    funext u ω; simp only [condDrift, stY_Zc]
  rw [e1]
  exact H

end BlockBand.SourceProcess.Stochastic.ComplexAngular
