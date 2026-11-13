module

public import BlockBand.Transmission.Dual.GStageMart
public import BlockBand.Transmission.Dual.GGluePath
public import BlockBand.Transmission.Dual.GDelFrom

/-!
# The glued process and its deletion paths

Stage 1 is a random-start family `F : B1R D₀ (k+1) μ ξ` on `Ω₁ = ΩR S (k+1)`; the restart is any
realization `(N', X', Y')` on `(Ω, 𝓖, P)` with a map `π' : Ω → Ω₁`, started at the survivors
`F.surv ∘ π'` (the output of `DelFrom k` for `(Ω₁, PR μ (k+1), F.surv)`).
* `toSeq`, `sX`, `sY`: the stage-1 coordinates as sequences (`dualCoordOf_sX`);
* `continuousAt_Zs`: the stage-1 flat path is continuous before `ρ₁ = rho1`;
* `gN`, `gX`, `gY`: stage 1 for `t < ρ = ρ₁ ∘ π'`, the truncated restart at time `t − θ`
  (`θ = ρ.untopA`) from `ρ` on;
* **`isDeletionPath_g`**: the glued path is a deletion path at **every** `ω`
  (`isDeletionPath_glue` on `{ρ < ⊤}`, `isDeletionPath_const_level` on `{ρ = ⊤}`);
* `gN_zero`, `dualCoordOf_g_zero`: the start.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- A finite vector as a sequence (zero beyond its length). -/
def toSeq {p : ℕ} (v : Fin p → ℝ) : ℕ → ℝ := fun i => if h : i < p then v ⟨i, h⟩ else 0

theorem toSeq_of_lt {p : ℕ} (v : Fin p → ℝ) {i : ℕ} (h : i < p) : toSeq v i = v ⟨i, h⟩ := by
  simp [toSeq, h]

theorem dualCoordOf_toSeq {p : ℕ} (v w : Fin p → ℝ) : dualCoordOf p (toSeq v) (toSeq w) = (v, w) :=
  Prod.ext (funext fun i => toSeq_of_lt v i.2) (funext fun i => toSeq_of_lt w i.2)

theorem measurable_toSeq {p : ℕ} : Measurable (toSeq (p := p)) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold toSeq
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

variable {k : ℕ} {D0 : ℝ}
variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin ((k + 1) + (k + 1)) → ℝ}

namespace B1R

variable (F : B1R D0 (k + 1) μ ξ)

/-- The stage-1 `x`-coordinates. -/
def sX (t : ℝ≥0) (x : ΩR S (k + 1)) : ℕ → ℝ := toSeq (ofFlat (k + 1) (F.Zs t x)).1

/-- The stage-1 `y`-coordinates. -/
def sY (t : ℝ≥0) (x : ΩR S (k + 1)) : ℕ → ℝ := toSeq (ofFlat (k + 1) (F.Zs t x)).2

theorem dualCoordOf_sX (t : ℝ≥0) (x : ΩR S (k + 1)) :
    dualCoordOf (k + 1) (F.sX t x) (F.sY t x) = ofFlat (k + 1) (F.Zs t x) :=
  dualCoordOf_toSeq _ _

theorem continuousAt_Zs (x : ΩR S (k + 1)) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < F.rho1 x) :
    ContinuousAt (fun u => F.Zs u x) t := by
  by_cases hx : x ∈ F.good
  · have hc := (F.good_spec hx).1
    have hζ : (t : WithTop ℝ≥0) < F.zeta x := by simpa only [rho1, hx, ↓reduceIte] using ht
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 hζ
    have hlt : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : WithTop ℝ≥0) < F.e n x := by
      induction he : F.e n x using WithTop.recTopCoe with
      | top => exact Eventually.of_forall fun u => WithTop.coe_lt_top u
      | coe r =>
        rw [he] at hn
        filter_upwards [Iio_mem_nhds (WithTop.coe_lt_coe.1 hn)] with u hu
        exact WithTop.coe_lt_coe.2 hu
    have hev : (fun u => F.Yf n u x) =ᶠ[𝓝 t] fun u => F.Zs u x := by
      filter_upwards [hlt] with u hu
      simp only [Zs, hx, ↓reduceIte]; exact (F.Z_eq hc hu.le).symm
    exact (F.continuous_Yf n x).continuousAt.congr hev
  · simp only [Zs, hx, ↓reduceIte]; exact continuousAt_const

theorem continuousAt_sX (x : ΩR S (k + 1)) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < F.rho1 x)
    {i : ℕ} (hi : i < k + 1) :
    ContinuousAt (fun u => F.sX u x i) t ∧ ContinuousAt (fun u => F.sY u x i) t := by
  simp only [sX, sY, toSeq_of_lt _ hi]
  have h := F.continuousAt_Zs x ht
  have h1 : Continuous fun w : Fin ((k + 1) + (k + 1)) → ℝ => (ofFlat (k + 1) w).1 ⟨i, hi⟩ :=
    (continuous_apply _).comp (continuous_fst.comp (ofFlat (k + 1)).continuous)
  have h2 : Continuous fun w : Fin ((k + 1) + (k + 1)) → ℝ => (ofFlat (k + 1) w).2 ⟨i, hi⟩ :=
    (continuous_apply _).comp (continuous_snd.comp (ofFlat (k + 1)).continuous)
  exact ⟨h1.continuousAt.comp h, h2.continuousAt.comp h⟩

theorem rho1_eq_coe {x : ΩR S (k + 1)} {r : ℝ≥0} (h : F.rho1 x = r) :
    x ∈ F.finE ∧ (F.zeta x).untopA = r := by
  by_cases hx : x ∈ F.good
  · have hz : F.zeta x = r := by simpa only [rho1, hx, ↓reduceIte] using h
    refine ⟨⟨hx, show F.zeta x < ⊤ by rw [hz]; exact WithTop.coe_lt_top r⟩, ?_⟩
    rw [hz]; rfl
  · simp only [rho1, hx, ↓reduceIte] at h; exact absurd h WithTop.top_ne_coe

/-- The corner limits of the stage-1 coordinates at a finite `ρ₁`. -/
theorem tendsto_corner {x : ΩR S (k + 1)} {r : ℝ≥0} (h : F.rho1 x = r) :
    (∀ j : Fin (k + 1), Tendsto (fun u => (ofFlat (k + 1) (F.Zs u x)).1 j) (𝓝[<] r)
        (𝓝 ((ofFlat (k + 1) (F.corner x)).1 j)) ∧
      Tendsto (fun u => (ofFlat (k + 1) (F.Zs u x)).2 j) (𝓝[<] r)
        (𝓝 ((ofFlat (k + 1) (F.corner x)).2 j))) ∧
    IsCorner k (F.corner x) ∧
      ofFlat k (F.surv x) = restOf 0 (ofFlat (k + 1) (F.corner x)) := by
  obtain ⟨hfin, hr⟩ := F.rho1_eq_coe h
  obtain ⟨hcor, hT⟩ := F.corner_spec hfin
  rw [hr] at hT
  have hT' : Tendsto (fun u => F.Zs u x) (𝓝[<] r) (𝓝 (F.corner x)) := by
    refine hT.congr fun u => ?_
    simp only [Zs, hfin.1, ↓reduceIte]
  refine ⟨fun j => ⟨(((continuous_apply j).comp (continuous_fst.comp
    (ofFlat (k + 1)).continuous)).tendsto _).comp hT', (((continuous_apply j).comp
    (continuous_snd.comp (ofFlat (k + 1)).continuous)).tendsto _).comp hT'⟩, hcor, ?_⟩
  simp only [surv, hfin, ↓reduceIte]
  exact ofFlat_right_slot 0 _

/-! ## The glued process -/

variable {Ω : Type} (π' : Ω → ΩR S (k + 1)) (N' : ℝ≥0 → Ω → ℕ) (X' Y' : ℝ≥0 → Ω → ℕ → ℝ)

/-- The restart time `θ = ρ.untopA`. -/
def theta (ω : Ω) : ℝ≥0 := (F.rho1 (π' ω)).untopA

/-- The glued level. -/
def gN (t : ℝ≥0) (ω : Ω) : ℕ :=
  if (t : WithTop ℝ≥0) < F.rho1 (π' ω) then k + 1 else N' (t - F.theta π' ω) ω

/-- The glued coordinates (`Z = sX` or `sY`, `X' = X'` or `Y'`). -/
def gC (Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ) (X' : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℕ → ℝ :=
  if (t : WithTop ℝ≥0) < F.rho1 (π' ω) then Z t (π' ω)
  else truncCoord (N' (t - F.theta π' ω) ω) (X' (t - F.theta π' ω) ω)

theorem gN_zero (ω : Ω) : F.gN π' N' 0 ω = k + 1 := by
  simp only [gN, WithTop.coe_zero, F.rho1_pos (π' ω), ↓reduceIte]

theorem gC_zero (Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ) (ω : Ω) :
    F.gC π' N' Z X' 0 ω = Z 0 (π' ω) := by
  simp only [gC, WithTop.coe_zero, F.rho1_pos (π' ω), ↓reduceIte]

theorem dualCoordOf_g_zero (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) (ω : Ω) :
    dualCoordOf (k + 1) (F.gC π' N' F.sX X' 0 ω) (F.gC π' N' F.sY Y' 0 ω) =
      ofFlat (k + 1) (ξ (π' ω).1) := by
  rw [gC_zero, gC_zero, dualCoordOf_sX, F.Zs_zero hξc]

theorem gN_of_lt {t : ℝ≥0} {ω : Ω} (h : (t : WithTop ℝ≥0) < F.rho1 (π' ω)) :
    F.gN π' N' t ω = k + 1 := by simp only [gN, h, ↓reduceIte]

theorem gN_of_le {t : ℝ≥0} {ω : Ω} (h : F.rho1 (π' ω) ≤ t) :
    F.gN π' N' t ω = N' (t - F.theta π' ω) ω := by simp only [gN, not_lt.2 h, ↓reduceIte]

theorem gC_of_lt (Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ) {t : ℝ≥0} {ω : Ω}
    (h : (t : WithTop ℝ≥0) < F.rho1 (π' ω)) : F.gC π' N' Z X' t ω = Z t (π' ω) := by
  simp only [gC, h, ↓reduceIte]

theorem gC_of_le (Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ) {t : ℝ≥0} {ω : Ω}
    (h : F.rho1 (π' ω) ≤ t) : F.gC π' N' Z X' t ω =
      truncCoord (N' (t - F.theta π' ω) ω) (X' (t - F.theta π' ω) ω) := by
  simp only [gC, not_lt.2 h, ↓reduceIte]

variable {π' N' X' Y'}

/-- **The glued path is a deletion path** at every `ω`. -/
theorem isDeletionPath_g (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) {ω : Ω}
    (hP : IsDeletionPath (fun t => N' t ω) (fun t => X' t ω) (fun t => Y' t ω))
    (h0 : N' 0 ω = k ∧ dualCoordOf k (X' 0 ω) (Y' 0 ω) = ofFlat k (F.surv (π' ω))) :
    IsDeletionPath (fun t => F.gN π' N' t ω) (fun t => F.gC π' N' F.sX X' t ω)
      (fun t => F.gC π' N' F.sY Y' t ω) := by
  set x := π' ω
  have hch : ∀ t, dualCoordOf (k + 1) (F.sX t x) (F.sY t x) ∈ dualChamber (k + 1) := fun t => by
    rw [dualCoordOf_sX]; exact F.Zs_mem hξc t x
  induction hρ : F.rho1 x using WithTop.recTopCoe with
  | top =>
    have hlt : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < F.rho1 (π' ω) := fun t => by
      rw [hρ]; exact WithTop.coe_lt_top t
    have e1 : (fun t => F.gN π' N' t ω) = fun _ => k + 1 := funext fun t => F.gN_of_lt π' N' (hlt t)
    have e2 : ∀ Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ, ∀ X'' : ℝ≥0 → Ω → ℕ → ℝ,
        (fun t => F.gC π' N' Z X'' t ω) = fun t => Z t x :=
      fun Z X'' => funext fun t => F.gC_of_lt π' N' X'' Z (hlt t)
    rw [e1, e2, e2]
    refine isDeletionPath_const_level hch fun i hi => ?_
    exact ⟨continuous_iff_continuousAt.2 fun t => (F.continuousAt_sX x (hlt t) hi).1,
      continuous_iff_continuousAt.2 fun t => (F.continuousAt_sX x (hlt t) hi).2⟩
  | coe r =>
    have hθ : F.theta π' ω = r := by simp only [theta]; rw [show F.rho1 (π' ω) = r from hρ]; rfl
    have hiff : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < F.rho1 (π' ω) ↔ t < r := fun t => by
      rw [show F.rho1 (π' ω) = r from hρ, WithTop.coe_lt_coe]
    have e1 : (fun t => F.gN π' N' t ω) = fun t => if t < r then k + 1 else N' (t - r) ω :=
      funext fun t => by simp only [gN, hiff, hθ]
    have e2 : ∀ Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ, ∀ X'' : ℝ≥0 → Ω → ℕ → ℝ,
        (fun t => F.gC π' N' Z X'' t ω) =
          fun t => if t < r then Z t x else truncCoord (N' (t - r) ω) (X'' (t - r) ω) :=
      fun Z X'' => funext fun t => by simp only [gC, hiff, hθ]; rfl
    rw [e1, e2, e2]
    obtain ⟨hT, hcor, hsurv⟩ := F.tendsto_corner (show F.rho1 x = r from hρ)
    have hP' : IsDeletionPath (fun s => N' s ω) (fun s => truncCoord (N' s ω) (X' s ω))
        (fun s => truncCoord (N' s ω) (Y' s ω)) := by
      simpa only [zero_add] using isDeletionPath_shift hP 0
    refine isDeletionPath_glue (fun t _ => hch t) (fun i hi => ⟨?_, ?_⟩) ?_ ?_
      (fun i hi => ⟨?_, ?_⟩) hP' h0.1
    · intro u hu
      have hu' : (u : WithTop ℝ≥0) < F.rho1 x := by rw [hρ]; exact WithTop.coe_lt_coe.2 hu
      exact (F.continuousAt_sX x hu' hi).1.continuousWithinAt
    · intro u hu
      have hu' : (u : WithTop ℝ≥0) < F.rho1 x := by rw [hρ]; exact WithTop.coe_lt_coe.2 hu
      exact (F.continuousAt_sX x hu' hi).2.continuousWithinAt
    · simp only [sX, toSeq_of_lt _ (Nat.succ_pos k)]
      have := (hT 0).1; rw [hcor.1] at this; exact this
    · simp only [sY, toSeq_of_lt _ (Nat.succ_pos k)]
      have := (hT 0).2; rw [hcor.2.1] at this; exact this
    · have hv : truncCoord (N' 0 ω) (X' 0 ω) i =
          (ofFlat (k + 1) (F.corner x)).1 ⟨i + 1, by omega⟩ := by
        rw [h0.1, truncCoord_of_lt _ hi]
        have := congrArg (fun z => z.1 ⟨i, hi⟩) (h0.2.trans hsurv)
        simpa [dualCoordOf, restOf] using this
      simp only [sX, toSeq_of_lt _ (show i + 1 < k + 1 by omega), hv]
      exact (hT _).1
    · have hv : truncCoord (N' 0 ω) (Y' 0 ω) i =
          (ofFlat (k + 1) (F.corner x)).2 ⟨i + 1, by omega⟩ := by
        rw [h0.1, truncCoord_of_lt _ hi]
        have := congrArg (fun z => z.2 ⟨i, hi⟩) (h0.2.trans hsurv)
        simpa [dualCoordOf, restOf] using this
      simp only [sY, toSeq_of_lt _ (show i + 1 < k + 1 by omega), hv]
      exact (hT _).2

end B1R

end BlockBand.Transmission.Dual.G
