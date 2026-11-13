module

public import BlockBand.Transmission.DualEntrance.FaceEntrance
public import BlockBand.Transmission.DualEntrance.LiftFaceCalc

/-!
# The faces of the lifted flat path are entrance faces

Setting: the driver space `(LΩ S, L𝓖 μ, LP μ)` (any `S : Type`, any probability `μ`,
augmented filtration), `D₀ > 0`, an admissible random start `ξ` (`IsLiftStart`), a
`LiftFamily μ D₀ ξ` and its flat paths `Yf n` (`isCSM_Yf`).

For `n ∈ ℕ`, `ε > 0`, `m ≥ 0`:
* `stopV = min(x + y − ε, m − x)` along `Yf n`, and the stopping time
  `stopT = e_n ∧ inf{t : x + y ≤ ε or x ≥ m}` (`isStoppingTime_stopT`);
* `faceZ i = faceA i · (Yf n)^{stopT} + faceB i` (`i = 0, 1, 2`: `x`, `y`, `1 − y`), a real
  continuous semimartingale (stopping, then `IsContinuousSemimartingale.affine`);
* **`isEntranceFace`**: `faceZ i` satisfies `IsEntranceFace` with `τ = stopT`, `c = D₀/2`,
  `K = M = faceK D₀ ε m`, `B = faceBd D₀ m`. On `(0, stopT]` the path is in
  `{x + y ≥ ε, x ≤ m}` (`le_of_le_hitLe`), where `face_ineq` applies; after `stopT` the
  characteristics are switched off.
* `faceZ_eq`: on `[0, stopT]`, `faceZ i` is the face coordinate of `Yf n`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic
  BlockBand.Transmission.Dual BlockBand.Transmission.DualLift
open scoped NNReal Matrix

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {D0 : ℝ}
  {ξ : LΩ S → Fin 6 → ℝ}

/-- The stopping potential `min(x + y − ε, m − x)` along the flat path. -/
def stopV (F : LiftFamily μ D0 ξ) (n : ℕ) (ε m : ℝ) (t : ℝ≥0) (ω : LΩ S) : ℝ :=
  min (F.Yf n t ω 0 + F.Yf n t ω 1 - ε) (m - F.Yf n t ω 0)

/-- `stopT = e_n ∧ inf{t : x + y ≤ ε or x ≥ m}`. -/
def stopT (F : LiftFamily μ D0 ξ) (n : ℕ) (ε m : ℝ) (ω : LΩ S) : WithTop ℝ≥0 :=
  min (F.e n ω) (hitLe (stopV F n ε m) 0 ω)

/-- The face process `faceA i · (Yf n)^{stopT} + faceB i`. -/
def faceZ (F : LiftFamily μ D0 ξ) (n : ℕ) (ε m : ℝ) (i : Fin 3) :
    ℝ≥0 → LΩ S → Fin 1 → ℝ :=
  fun t ω => faceA i *ᵥ stoppedProcess (F.Yf n) (stopT F n ε m) t ω + faceB i

/-- Its drift. -/
def faceβ (F : LiftFamily μ D0 ξ) (n : ℕ) (ε m : ℝ) (i : Fin 3) :
    ℝ≥0 → LΩ S → Fin 1 → ℝ :=
  fun t ω => faceA i *ᵥ switchAfter (stopT F n ε m)
    (fun t ω => switchOff (F.e n) (fun t ω => flatDrift D0 1 (F.Yf n t ω)) t ω) t ω

/-- Its covariance. -/
def faceα (F : LiftFamily μ D0 ξ) (n : ℕ) (ε m : ℝ) (i : Fin 3) :
    ℝ≥0 → LΩ S → Matrix (Fin 1) (Fin 1) ℝ :=
  fun t ω => faceA i * switchAfter (stopT F n ε m)
    (fun t ω => switchOff (F.e n) (fun t ω => flatDiff D0 1 (F.Yf n t ω)) t ω) t ω * (faceA i)ᵀ

theorem switchAfter_of_le {Ω' G : Type*} [Zero G] {ρ : Ω' → WithTop ℝ≥0}
    {f : ℝ≥0 → Ω' → G} {u : ℝ≥0} {ω : Ω'} (h : (u : WithTop ℝ≥0) ≤ ρ ω) :
    switchAfter ρ f u ω = f u ω := ite_eq_left h

theorem switchAfter_of_not_le {Ω' G : Type*} [Zero G] {ρ : Ω' → WithTop ℝ≥0}
    {f : ℝ≥0 → Ω' → G} {u : ℝ≥0} {ω : Ω'} (h : ¬(u : WithTop ℝ≥0) ≤ ρ ω) :
    switchAfter ρ f u ω = 0 := ite_eq_right h

theorem switchOff_of_le {G : Type*} [Zero G] {ρ : LΩ S → WithTop ℝ≥0}
    {f : ℝ≥0 → LΩ S → G} {u : ℝ≥0} {ω : LΩ S} (h : (u : WithTop ℝ≥0) ≤ ρ ω) :
    switchOff ρ f u ω = f u ω := ite_eq_left h

variable (F : LiftFamily μ D0 ξ)

theorem continuous_stopV (n : ℕ) (ε m : ℝ) (ω : LΩ S) :
    Continuous fun u => stopV F n ε m u ω := by
  have h0 : Continuous fun u => F.Yf n u ω 0 := (continuous_apply 0).comp (F.continuous_Yf n ω)
  have h1 : Continuous fun u => F.Yf n u ω 1 := (continuous_apply 1).comp (F.continuous_Yf n ω)
  exact ((h0.add h1).sub continuous_const).min (continuous_const.sub h0)

theorem isStoppingTime_stopT (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) (ε m : ℝ) :
    IsStoppingTime (L𝓖 μ) (stopT F n ε m) := by
  refine (F.isStoppingTime_e n).min (isStoppingTime_hitLe (fun t => ?_)
    (fun ω t => ((continuous_stopV F n ε m ω).tendsto t).mono_left nhdsWithin_le_nhds)
    (fun ω => (continuous_stopV F n ε m ω).lowerSemicontinuous) 0)
  have hY := F.measurable_Yf hD0 hξ n t
  have h0 : Measurable[L𝓖 μ t] fun ω => F.Yf n t ω 0 := (measurable_pi_apply 0).comp hY
  have h1 : Measurable[L𝓖 μ t] fun ω => F.Yf n t ω 1 := (measurable_pi_apply 1).comp hY
  exact ((h0.add h1).sub measurable_const).min (measurable_const.sub h0)

/-- On `(0, stopT]` the flat path is in `{x + y ≥ ε, x ≤ m}`. -/
theorem inside_of_le {n : ℕ} {ε m : ℝ} {u : ℝ≥0} {ω : LΩ S} (hu : 0 < u)
    (huτ : (u : WithTop ℝ≥0) ≤ stopT F n ε m ω) :
    ε ≤ F.Yf n u ω 0 + F.Yf n u ω 1 ∧ F.Yf n u ω 0 ≤ m := by
  have h := le_of_le_hitLe (continuous_stopV F n ε m ω) hu (huτ.trans (min_le_right _ _))
  unfold stopV at h
  exact ⟨by linarith [le_min_iff.1 h |>.1], by linarith [le_min_iff.1 h |>.2]⟩

theorem faceZ_eq {n : ℕ} {ε m : ℝ} (i : Fin 3) {t : ℝ≥0} {ω : LΩ S}
    (ht : (t : WithTop ℝ≥0) ≤ stopT F n ε m ω) :
    faceZ F n ε m i t ω 0 = faceR i 0 * F.Yf n t ω 0 + faceR i 1 * F.Yf n t ω 1 + faceC i := by
  unfold faceZ
  rw [stoppedProcess_eq_of_le ht, face_apply]

/-- **The faces `x`, `y`, `1 − y` of the stopped flat path are entrance faces.** -/
theorem isEntranceFace (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {ε m : ℝ}
    (hε : 0 < ε) (hm : 0 ≤ m) (i : Fin 3) :
    IsEntranceFace (LP μ) (L𝓖 μ) (faceZ F n ε m i) (faceβ F n ε m i) (faceα F n ε m i)
      (stopT F n ε m) (D0 / 2) (faceK D0 ε m) (faceK D0 ε m) (faceBd D0 m) := by
  have hτ := isStoppingTime_stopT F hD0 hξ n ε m
  have hK : ∀ t ω, F.Yf n t ω ∈ flatK (max (max (n : ℝ) ‖ξ ω‖) 1) := F.Yf_mem_flatK hξ n
  refine
    { csm := ((Semimartingale.stoppedSemimartingale_holds 2 (LΩ S) (LP μ) (L𝓖 μ) _ _ _
        (F.isCSM_Yf hD0 hξ n) _ hτ).affine (faceA i) (faceB i))
      cont := fun ω => (continuous_apply 0).comp
        (((continuous_const.matrix_mulVec continuous_id).add continuous_const).comp
          (NativeSDE.continuous_stoppedProcess (F.continuous_Yf n ω) _))
      nonneg := fun u ω => ?_
      meas := hτ.measurable'
      c_pos := by positivity
      K_nonneg := faceK_nonneg hD0 hε hm
      M_nonneg := faceK_nonneg hD0 hε hm
      inside := fun u ω hu huτ => ?_
      outside := fun u ω hu => ?_ }
  · show 0 ≤ (faceA i *ᵥ stoppedProcess (F.Yf n) (stopT F n ε m) u ω + faceB i) 0
    rw [face_apply]
    have h := hK (min (u : WithTop ℝ≥0) (stopT F n ε m ω)).untopA ω
    exact face_nonneg i h.2.1 h.2.2.2.1 h.2.2.2.2
  · have hue : (u : WithTop ℝ≥0) ≤ F.e n ω := huτ.trans (min_le_left _ _)
    obtain ⟨hS, hm'⟩ := inside_of_le F hu huτ
    have h := hK u ω
    have hz := faceZ_eq F i huτ
    have hb : faceβ F n ε m i u ω 0 =
        faceR i 0 * flatDrift D0 1 (F.Yf n u ω) 0 + faceR i 1 * flatDrift D0 1 (F.Yf n u ω) 1 := by
      simp only [faceβ, switchAfter_of_le huτ, switchOff_of_le hue, faceA_mulVec]
    have ha : faceα F n ε m i u ω 0 0 =
        faceR i 0 ^ 2 * (D0 * (F.Yf n u ω 0 * (1 + F.Yf n u ω 0))) +
          faceR i 1 ^ 2 * (D0 * (F.Yf n u ω 1 * (1 - F.Yf n u ω 1))) := by
      simp only [faceα, switchAfter_of_le huτ, switchOff_of_le hue, flatDiff_one_eq]
      exact faceA_cov _ _
    rw [hz, hb, ha]
    exact face_ineq i hD0 hε hm h.2.1 hm' h.2.2.2.1 h.2.2.2.2 hS
  · simp only [faceβ, faceα, switchAfter_of_not_le hu]
    simp

end BlockBand.Transmission.DualEntrance
