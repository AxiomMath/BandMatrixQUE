module
public import BlockBand.Diffusion.PathSpace.Adapter
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.ItoUniverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Space-time coefficients and the space-time martingale problem

Coordinates: `ℝ^{d+1} = Fin (d+1) → ℝ` with coordinate `0` the time and `Fin.tail` the space;
`stEquiv d : ℝ^{d+1} ≃L ℝ × ℝ^d`, `y ↦ (y 0, Fin.tail y)`.

* `stDrift b y = (1, b(tail y))`, `stCov a y = diag-block (0, a(tail y))`: the coefficients of
  the space-time generator `∂_s + 𝓛`.
* `stGen b a u p = ∂_s u + ∑ b_i ∂_i u + ½ ∑ a_ij ∂_ij u` at `p = (s, x)`, with
  `partialTime`, `partialSpace`, `partialSpace2` (no regularity in the definition).
* `mpGenerator_stDrift_comp`: `mpGenerator (stDrift b) (stCov a) (u ∘ stEquiv d) y =
  stGen b a u (stEquiv d y)` for **every** `u` and `y` (chain rule for a linear equivalence,
  through `iteratedFDeriv`).
* `IsMPSolutionOn.spaceTime`: if `Z` solves the localized martingale problem
  `IsMPSolutionOn Q 𝓖 b a U Z` (`U` open, `b, a` continuous on `U`), then the space-time
  process `stProc Z s = (s, Z_s)` solves `IsMPSolutionOn Q 𝓖 (stDrift b) (stCov a) V` for every
  open `V ⊆ ℝ^{d+1}` whose points have spatial part in `U`. Localization: an interior domain
  `W` of `V` has compact spatial shadow, which lies in some exhaustion set `W'` of `U`; the
  exit time from `W` is at most the exit time of `Z` from `W'`, and the `W'`-stopped
  martingales are stopped once more at the raw stopping time `rawHit Wᶜ (stProc Z)`.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Bridges BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {d : ℕ}

/-!
### Coordinates and coefficients
-/

/-- `y ↦ (y 0, tail y)` as a linear equivalence. -/
def stLinearEquiv (d : ℕ) : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin d → ℝ) where
  toFun y := (y 0, Fin.tail y)
  invFun p := Fin.cons p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := Fin.cons_self_tail y
  right_inv p := by simp

/-- Space-time coordinates `ℝ^{d+1} ≃L ℝ × ℝ^d`. -/
def stEquiv (d : ℕ) : (Fin (d + 1) → ℝ) ≃L[ℝ] ℝ × (Fin d → ℝ) :=
  (stLinearEquiv d).toContinuousLinearEquiv

@[simp] theorem stEquiv_apply (y : Fin (d + 1) → ℝ) : stEquiv d y = (y 0, Fin.tail y) := rfl

@[simp] theorem stEquiv_symm_apply (p : ℝ × (Fin d → ℝ)) :
    (stEquiv d).symm p = Fin.cons p.1 p.2 := rfl

/-- Space-time drift `(1, b(tail y))`. -/
def stDrift (b : (Fin d → ℝ) → Fin d → ℝ) (y : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons 1 (b (Fin.tail y))

/-- Space-time covariance: `0` in the time row and column, `a(tail y)` in the space block. -/
def stCov (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (y : Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun k l => Fin.cases 0 (fun i => Fin.cases 0 (fun j => a (Fin.tail y) i j) l) k

@[simp] theorem stDrift_zero (b : (Fin d → ℝ) → Fin d → ℝ) (y : Fin (d + 1) → ℝ) :
    stDrift b y 0 = 1 := rfl

@[simp] theorem stDrift_succ (b : (Fin d → ℝ) → Fin d → ℝ) (y : Fin (d + 1) → ℝ) (i : Fin d) :
    stDrift b y i.succ = b (Fin.tail y) i := rfl

@[simp] theorem stCov_zero_left (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (y : Fin (d + 1) → ℝ) (l : Fin (d + 1)) : stCov a y 0 l = 0 := rfl

@[simp] theorem stCov_succ_zero (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (y : Fin (d + 1) → ℝ) (i : Fin d) : stCov a y i.succ 0 = 0 := rfl

@[simp] theorem stCov_succ_succ (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (y : Fin (d + 1) → ℝ) (i j : Fin d) : stCov a y i.succ j.succ = a (Fin.tail y) i j := rfl

theorem continuous_tail : Continuous fun y : Fin (d + 1) → ℝ => Fin.tail y :=
  continuous_pi fun i => continuous_apply i.succ

theorem continuousOn_stDrift {U : Set (Fin d → ℝ)} {b : (Fin d → ℝ) → Fin d → ℝ}
    (hb : ContinuousOn b U) {V : Set (Fin (d + 1) → ℝ)} (hVU : ∀ y ∈ V, Fin.tail y ∈ U) :
    ContinuousOn (stDrift b) V := by
  have hb' : ContinuousOn (fun y : Fin (d + 1) → ℝ => b (Fin.tail y)) V :=
    hb.comp continuous_tail.continuousOn hVU
  refine continuousOn_pi.2 fun k => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · exact continuousOn_const
  · exact (continuous_apply i).comp_continuousOn hb'

theorem continuousOn_stCov {U : Set (Fin d → ℝ)} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (ha : ContinuousOn a U) {V : Set (Fin (d + 1) → ℝ)} (hVU : ∀ y ∈ V, Fin.tail y ∈ U) :
    ContinuousOn (stCov a) V := by
  have ha' : ContinuousOn (fun y : Fin (d + 1) → ℝ => a (Fin.tail y)) V :=
    ha.comp continuous_tail.continuousOn hVU
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  refine Fin.cases ?_ (fun i => ?_) k
  · exact continuousOn_const
  · refine Fin.cases ?_ (fun j => ?_) l
    · exact continuousOn_const
    · exact (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn ha')

/-!
### The space-time generator
-/

/-- The space-time generator `∂_s u + ∑ b_i ∂_i u + ½ ∑ a_ij ∂_ij u` at `p = (s, x)`. -/
def stGen (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (u : ℝ × (Fin d → ℝ) → ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  partialTime u p + ∑ i, b p.2 i * partialSpace u p i +
    (1 / 2 : ℝ) * ∑ i, ∑ j, a p.2 i j * partialSpace2 u p i j

theorem fderiv_comp_stEquiv (u : ℝ × (Fin d → ℝ) → ℝ) (y v : Fin (d + 1) → ℝ) :
    fderiv ℝ (u ∘ stEquiv d) y v = fderiv ℝ u (stEquiv d y) (stEquiv d v) := by
  rw [(stEquiv d).comp_right_fderiv]; rfl

theorem fderiv_fderiv_comp_stEquiv (u : ℝ × (Fin d → ℝ) → ℝ) (y v w : Fin (d + 1) → ℝ) :
    fderiv ℝ (fderiv ℝ (u ∘ stEquiv d)) y v w =
      fderiv ℝ (fderiv ℝ u) (stEquiv d y) (stEquiv d v) (stEquiv d w) := by
  have h := (stEquiv d).iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (mem_univ (stEquiv d y)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have h2 := congrArg (fun L => L ![v, w]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply] at h2
  simpa using h2

theorem stEquiv_single_zero : stEquiv d (Pi.single 0 1) = ((1 : ℝ), (0 : Fin d → ℝ)) := by
  ext i
  · simp
  · simp [Fin.tail, Fin.succ_ne_zero]

theorem stEquiv_single_succ (i : Fin d) :
    stEquiv d (Pi.single i.succ 1) = ((0 : ℝ), (Pi.single i 1 : Fin d → ℝ)) := by
  ext j
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Fin.tail, Pi.single_apply, Fin.succ_inj]

/-- **Generator transport.** For every `u` and `y`, the `ℝ^{d+1}` generator of
`(stDrift b, stCov a)` applied to `u ∘ stEquiv d` is the space-time generator. -/
theorem mpGenerator_stDrift_comp (b : (Fin d → ℝ) → Fin d → ℝ)
    (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (u : ℝ × (Fin d → ℝ) → ℝ)
    (y : Fin (d + 1) → ℝ) :
    mpGenerator (stDrift b) (stCov a) (u ∘ stEquiv d) y = stGen b a u (stEquiv d y) := by
  simp only [mpGenerator, fderiv_comp_stEquiv, fderiv_fderiv_comp_stEquiv, Fin.sum_univ_succ,
    stDrift_zero, stDrift_succ, stCov_zero_left, stCov_succ_zero, stCov_succ_succ,
    stEquiv_single_zero, stEquiv_single_succ, zero_mul, Finset.sum_const_zero, zero_add, one_mul,
    stGen, partialTime, partialSpace, partialSpace2]
  rfl

/-!
### The space-time process
-/

variable {Ω : Type*}

/-- The space-time process `s ↦ (s, Z_s)` in `ℝ^{d+1}`. -/
def stProc (Z : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) (ω : Ω) : Fin (d + 1) → ℝ :=
  Fin.cons (s : ℝ) (Z s ω)

@[simp] theorem stEquiv_stProc (Z : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) (ω : Ω) :
    stEquiv d (stProc Z s ω) = ((s : ℝ), Z s ω) := by
  simp [stProc]

@[simp] theorem stProc_zero (Z : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) (ω : Ω) :
    stProc Z s ω 0 = s := rfl

@[simp] theorem tail_stProc (Z : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ≥0) (ω : Ω) :
    Fin.tail (stProc Z s ω) = Z s ω := by
  simp [stProc]

theorem continuous_stProc {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hZ : Continuous fun t => Z t ω) :
    Continuous fun t => stProc Z t ω := by
  have : (fun t => stProc Z t ω) = fun t : ℝ≥0 => (stEquiv d).symm ((t : ℝ), Z t ω) := by
    funext t; rfl
  rw [this]
  exact (stEquiv d).symm.continuous.comp (NNReal.continuous_coe.prodMk hZ)

/-!
### Continuity of stopped compensated processes
-/

/-- Up to the exit time from `W` (with `closure W ⊆ U`), an integral of a function continuous on
`U` along a continuous path is continuous in the (stopped) time. -/
theorem continuous_integral_stop {U W : Set (Fin d → ℝ)} (hW : IsOpen W) (hWU : closure W ⊆ U)
    {g : (Fin d → ℝ) → ℝ} (hg : ContinuousOn g U) {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}
    (hZ : Continuous fun t => Z t ω) :
    Continuous fun t => ∫ r in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Z ω) t),
      g (Z r.toNNReal ω) := by
  set τ := exitTimeFrom W Z ω with hτ
  by_cases h0 : Z 0 ω ∈ W
  · have hmem : ∀ r : ℝ≥0, Z (stopTime τ r) ω ∈ closure W := fun r => stop_mem_closure hW hZ h0 r
    have hc : Continuous fun r : ℝ≥0 => g (Z (stopTime τ r) ω) :=
      hg.comp_continuous (hZ.comp (continuous_stopTime τ)) fun r => hWU (hmem r)
    have hF : Continuous fun x : ℝ≥0 => ∫ r in Ioc (0 : ℝ) x, g (Z (stopTime τ r.toNNReal) ω) :=
      continuous_setIntegral_Ioc (g := fun r => g (Z (stopTime τ r) ω))
        fun t => (hc.comp continuous_real_toNNReal).integrableOn_Ioc
    refine (hF.comp (continuous_stopTime τ)).congr fun t => ?_
    simp only [Function.comp]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hle : r.toNNReal ≤ stopTime τ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [stopTime_eq_of_le_stopTime hle]
  · have he : τ = 0 := exitTimeFrom_eq_zero h0
    have : ∀ t, stopTime τ t = 0 := fun t => by rw [he]; exact stopTime_of_eq_zero t
    simp only [this]
    exact continuous_const

theorem continuous_mpCompensated_stop {U W : Set (Fin d → ℝ)} (hW : IsOpen W)
    (hWU : closure W ⊆ U) {b : (Fin d → ℝ) → Fin d → ℝ} (hb : ContinuousOn b U)
    {Z : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} (hZ : Continuous fun t => Z t ω) (i : Fin d) :
    Continuous fun t => stoppedProcess (mpCompensated b Z i) (exitTimeFrom W Z) t ω := by
  simp only [stoppedProcess_eq_stopTime, mpCompensated]
  exact (((continuous_apply i).comp (hZ.comp (continuous_stopTime _))).sub continuous_const).sub
    (continuous_integral_stop hW hWU ((continuous_apply i).comp_continuousOn hb) hZ)

/-!
### Re-stopping
-/

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- Re-stopping a stopped martingale modification at an earlier raw stopping time. -/
theorem exists_martingale_restop {X : ℝ≥0 → Ω → ℝ} {τ' ρ σ : Ω → WithTop ℝ≥0}
    {N : ℝ≥0 → Ω → ℝ} (hN : Martingale N 𝓖 Q) (hNX : ∀ t, N t =ᵐ[Q] stoppedProcess X τ' t)
    (hc : ∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X τ' t ω) (hρ : IsStoppingTime 𝓖 ρ)
    (hρσ : ∀ᵐ ω ∂Q, ρ ω = σ ω) (hστ : ∀ ω, σ ω ≤ τ' ω) :
    ∃ N' : ℝ≥0 → Ω → ℝ, Martingale N' 𝓖 Q ∧ ∀ t, N' t =ᵐ[Q] stoppedProcess X σ t := by
  obtain ⟨M, hM, hMX⟩ := exists_martingale_stoppedProcess hN hNX hc hρ
  refine ⟨M, hM, fun t => (hMX t).trans ?_⟩
  rw [stoppedProcess_stoppedProcess']
  filter_upwards [hρσ] with ω hω
  simp only [stoppedProcess_eq_stopTime, hω, min_eq_left (hστ ω)]

variable {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}

omit [MeasurableSpace Ω] [IsProbabilityMeasure Q] in
/-- The exit time of the space-time process from `W` is at most the exit time of `Z` from any
`W'` containing the spatial shadow of `W`. -/
theorem exitTimeFrom_stProc_le {W : Set (Fin (d + 1) → ℝ)} {W' : Set (Fin d → ℝ)}
    (hWW' : ∀ y ∈ W, Fin.tail y ∈ W') (ω : Ω) :
    exitTimeFrom W (stProc Z) ω ≤ exitTimeFrom W' Z ω :=
  le_iInf₂ fun t ht => iInf₂_le t fun h => ht (by simpa using hWW' _ h)

omit [IsProbabilityMeasure Q] in
theorem exists_exhaust_shadow (hU : IsOpen U) {V W : Set (Fin (d + 1) → ℝ)}
    (hVU : ∀ y ∈ V, Fin.tail y ∈ U) (hW : IsInteriorDomain W V) :
    ∃ W' : Set (Fin d → ℝ), IsInteriorDomain W' U ∧ ∀ y ∈ closure W, Fin.tail y ∈ W' := by
  have hK : IsCompact ((fun y : Fin (d + 1) → ℝ => Fin.tail y) '' closure W) :=
    hW.2.1.image continuous_tail
  obtain ⟨m, hm⟩ := exists_exhaust_of_compact hU hK (by
    rintro _ ⟨y, hy, rfl⟩; exact hVU y (hW.2.2 hy))
  exact ⟨exhaust U m, ⟨isOpen_exhaust m, isCompact_closure_exhaust m,
    closure_exhaust_subset_U m⟩, fun y hy => hm ⟨y, hy, rfl⟩⟩

omit [MeasurableSpace Ω] in
theorem mpCompensated_stDrift_succ (i : Fin d) :
    mpCompensated (stDrift b) (stProc Z) i.succ = mpCompensated b Z i := by
  funext t ω
  simp [mpCompensated, stProc]

omit [MeasurableSpace Ω] in
theorem mpCompensated_stDrift_zero : mpCompensated (stDrift b) (stProc Z) 0 = fun _ _ => 0 := by
  funext t ω
  simp [mpCompensated, stProc]

/-- **The space-time martingale problem.** -/
theorem IsMPSolutionOn.spaceTime (h : IsMPSolutionOn Q 𝓖 b a U Z) (hU : IsOpen U)
    (hb : ContinuousOn b U) (ha : ContinuousOn a U) {V : Set (Fin (d + 1) → ℝ)}
    (hVU : ∀ y ∈ V, Fin.tail y ∈ U) :
    IsMPSolutionOn Q 𝓖 (stDrift b) (stCov a) V (stProc Z) := by
  have hadapt : ∀ t, StronglyMeasurable[𝓖 t] (stProc Z t) := fun t => by
    have : stProc Z t = fun ω => (stEquiv d).symm ((t : ℝ), Z t ω) := by funext ω; rfl
    rw [this]
    exact ((stEquiv d).symm.continuous.comp (continuous_const.prodMk continuous_id))
      |>.comp_stronglyMeasurable (h.adapted t)
  have hcont : ∀ᵐ ω ∂Q, Continuous fun t => stProc Z t ω := by
    filter_upwards [h.continuous] with ω hω
    exact continuous_stProc hω
  have hmeas : ∀ t, Measurable[𝓖 t] (stProc Z t) := fun t => (hadapt t).measurable
  -- re-stopping data for an interior domain of `V`
  have restop : ∀ W, IsInteriorDomain W V → ∃ W' : Set (Fin d → ℝ), IsInteriorDomain W' U ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (N : ℝ≥0 → Ω → ℝ), Martingale N 𝓖 Q →
      (∀ t, N t =ᵐ[Q] stoppedProcess X (exitTimeFrom W' Z) t) →
      (∀ᵐ ω ∂Q, Continuous fun t => stoppedProcess X (exitTimeFrom W' Z) t ω) →
      ∃ N' : ℝ≥0 → Ω → ℝ, Martingale N' 𝓖 Q ∧
        ∀ t, N' t =ᵐ[Q] stoppedProcess X (exitTimeFrom W (stProc Z)) t := by
    intro W hW
    obtain ⟨W', hW', hsh⟩ := exists_exhaust_shadow hU hVU hW
    refine ⟨W', hW', fun X N hN hNX hc => ?_⟩
    refine exists_martingale_restop hN hNX hc (isStoppingTime_rawHit (F := Wᶜ) hmeas) ?_
      (exitTimeFrom_stProc_le fun y hy => hsh y (subset_closure hy))
    filter_upwards [hcont] with ω hω
    exact rawHit_compl_eq_exitTimeFrom hW.1 hω
  refine ⟨hadapt, hcont, fun W hW k => ?_, fun W hW k l => ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) k
    · refine ⟨fun _ _ => 0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => ?_⟩
      simp [mpCompensated_stDrift_zero, stoppedProcess_eq_stopTime]
    · obtain ⟨W', hW', hre⟩ := restop W hW
      obtain ⟨N, hN, hNe⟩ := h.drift W' hW' i
      rw [mpCompensated_stDrift_succ]
      refine hre _ N hN hNe ?_
      filter_upwards [h.continuous] with ω hω
      exact continuous_mpCompensated_stop hW'.1 hW'.2.2 hb hω i
  · have hzero : ∀ k l : Fin (d + 1), (k = 0 ∨ l = 0) →
        (fun t ω => mpCompensated (stDrift b) (stProc Z) k t ω *
          mpCompensated (stDrift b) (stProc Z) l t ω -
            ∫ s in Ioc (0 : ℝ) t, stCov a (stProc Z s.toNNReal ω) k l) = fun _ _ => 0 := by
      intro k l hkl
      funext t ω
      rcases hkl with rfl | rfl
      · simp [mpCompensated_stDrift_zero]
      · refine Fin.cases ?_ (fun i => ?_) k
        · simp [mpCompensated_stDrift_zero]
        · simp [mpCompensated_stDrift_zero]
    by_cases hkl : k = 0 ∨ l = 0
    · rw [hzero k l hkl]
      refine ⟨fun _ _ => 0, martingale_zero ℝ 𝓖 Q, fun t => ae_of_all _ fun ω => ?_⟩
      simp [stoppedProcess_eq_stopTime]
    · push Not at hkl
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hkl.1
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hkl.2
      obtain ⟨W', hW', hre⟩ := restop W hW
      obtain ⟨N, hN, hNe⟩ := h.bracket W' hW' i j
      have e : (fun t ω => mpCompensated (stDrift b) (stProc Z) i.succ t ω *
          mpCompensated (stDrift b) (stProc Z) j.succ t ω -
            ∫ s in Ioc (0 : ℝ) t, stCov a (stProc Z s.toNNReal ω) i.succ j.succ) =
          fun t ω => mpCompensated b Z i t ω * mpCompensated b Z j t ω -
            ∫ s in Ioc (0 : ℝ) t, a (Z s.toNNReal ω) i j := by
        rw [mpCompensated_stDrift_succ, mpCompensated_stDrift_succ]
        simp
      rw [e]
      refine hre _ N hN hNe ?_
      filter_upwards [h.continuous] with ω hω
      have h1 := continuous_mpCompensated_stop hW'.1 hW'.2.2 hb hω i
      have h2 := continuous_mpCompensated_stop hW'.1 hW'.2.2 hb hω j
      have h3 := continuous_integral_stop hW'.1 hW'.2.2
        ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn ha)) hω
      simp only [stoppedProcess_eq_stopTime] at h1 h2 ⊢
      exact (h1.mul h2).sub h3

end BlockBand.Diffusion
