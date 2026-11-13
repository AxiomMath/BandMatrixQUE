module

public import BlockBand.SourceProcess.Stochastic.Dyson.MMTools
public import BlockBand.SourceProcess.Stochastic.Dyson.Partials

/-!
# Stopped Itô formula with bounded stopped characteristics,)

Let `Y` be a continuous semimartingale in `ℝ^d` with zero drift and constant covariance `α`, a.s.
in an open set `U`, `g` measurable and `C²` on `U` with `itoDrift (g ∘ snd) = Dr` and
`itoBracket (g ∘ snd) = Br` on `U`, and `ρ` a stopping time. If the stopped processes
`M = g(Y) - g(Y_0) - ∫ Dr(Y)` and `M² - ∫ Br(Y)` are a.s. bounded on `[0, t] ∩ [0, ρ]` for every
`t`, then both stopped at `ρ` have martingale modifications (`localized_hasMM`). The localizing
sequence produced by (a1) is removed with `hasMM_of_tendsto`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.Internal.Contracts.Transmission

theorem untopA_coe' (t : ℝ≥0) : (t : WithTop ℝ≥0).untopA = t := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

theorem min_ne_top' (t : ℝ≥0) (ρ : WithTop ℝ≥0) : min (t : WithTop ℝ≥0) ρ ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)

theorem coe_untopA_min (t : ℝ≥0) (ρ : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) ρ).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) ρ := by
  rw [WithTop.untopA_eq_untop (min_ne_top' t ρ), WithTop.coe_untop]

theorem untopA_min_le (t : ℝ≥0) (ρ : WithTop ℝ≥0) : (min (t : WithTop ℝ≥0) ρ).untopA ≤ t := by
  have := coe_untopA_min t ρ ▸ (min_le_left (t : WithTop ℝ≥0) ρ)
  exact_mod_cast this

theorem untopA_min_le_rho (t : ℝ≥0) (ρ : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) ρ).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ ρ :=
  (coe_untopA_min t ρ).symm ▸ min_le_right _ _

/-- `∫_{(0,t]} 1_{r ≤ ρ} f = ∫_{(0, t ∧ ρ]} f`. -/
theorem integral_Ioc_switch (f : ℝ → ℝ) (t : ℝ≥0) (ρ : WithTop ℝ≥0) :
    ∫ r in Ioc (0 : ℝ) t, (if ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ then f r else 0) =
      ∫ r in Ioc (0 : ℝ) ((min (t : WithTop ℝ≥0) ρ).untopA : ℝ≥0), f r := by
  set S : Set ℝ := {r | ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ}
  have hS : MeasurableSet S :=
    (isClosed_le (WithTop.continuous_coe.comp continuous_real_toNNReal) continuous_const).measurableSet
  have e1 : (fun r => if ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ then f r else 0) = S.indicator f := by
    funext r
    by_cases h : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ
    · rw [ite_eq_left_iff.mpr (fun h' => absurd h h'), Set.indicator_of_mem (show r ∈ S from h)]
    · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), Set.indicator_of_notMem (show r ∉ S from h)]
  rw [e1, setIntegral_indicator hS]
  rw [show Ioc (0 : ℝ) t ∩ S = Ioc (0 : ℝ) ((min (t : WithTop ℝ≥0) ρ).untopA : ℝ≥0) from ?_]
  ext r
  simp only [S, mem_inter_iff, mem_Ioc, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h0, ht⟩, hρ⟩
    refine ⟨h0, ?_⟩
    have hr : ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) ρ :=
      le_min (WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr ht)) hρ
    rw [← coe_untopA_min, WithTop.coe_le_coe] at hr
    have := (Real.toNNReal_le_iff_le_coe).mp hr
    exact this
  · rintro ⟨h0, hr⟩
    have hr' : r.toNNReal ≤ (min (t : WithTop ℝ≥0) ρ).untopA := Real.toNNReal_le_iff_le_coe.mpr hr
    refine ⟨⟨h0, hr.trans (by exact_mod_cast untopA_min_le t ρ)⟩, ?_⟩
    exact (WithTop.coe_le_coe.mpr hr').trans (untopA_min_le_rho t ρ)

/-- The compensated process `g(Y_t) - g(Y_0) - ∫_0^t Dr(Y_r) dr`. -/
def locComp {Ω : Type*} {d : ℕ} (Y : ℝ≥0 → Ω → Fin d → ℝ) (g Dr : (Fin d → ℝ) → ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  g (Y t ω) - g (Y 0 ω) - ∫ r in Ioc (0 : ℝ) t, Dr (Y r.toNNReal ω)

/-- Its bracket-compensated square `M_t² - ∫_0^t Br(Y_r) dr`. -/
def locSq {Ω : Type*} {d : ℕ} (Y : ℝ≥0 → Ω → Fin d → ℝ) (g Dr Br : (Fin d → ℝ) → ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  locComp Y g Dr t ω * locComp Y g Dr t ω - ∫ r in Ioc (0 : ℝ) t, Br (Y r.toNNReal ω)

theorem itoDrift_zero_cov {d : ℕ} {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : DifferentiableAt ℝ g y) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) y t 0 0 = 0 := by
  unfold itoDrift
  rw [partialTime_comp_snd hg]
  simp

theorem itoBracket_zero_cov {d : ℕ} (φ : ℝ × (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) (t : ℝ≥0) :
    itoBracket φ y t 0 = 0 := by
  simp [itoBracket]

theorem stoppedProcess_zero' {Ω β : Type*} (u : ℝ≥0 → Ω → β) (ρ : Ω → WithTop ℝ≥0) (ω : Ω) :
    stoppedProcess u ρ 0 ω = u 0 ω :=
  stoppedProcess_eq_of_le (by simp)

/-- **Stopped Itô formula with bounded stopped characteristics** (conditional on (a1), (a2)). -/
theorem localized_hasMM (hIto : ∀ d, SemimartingaleItoFormula d)
    (hStop : ∀ d, StoppedSemimartingale d) {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {d : ℕ}
    {Y : ℝ≥0 → Ω → Fin d → ℝ} {α : Matrix (Fin d) (Fin d) ℝ}
    (hY : IsContinuousSemimartingale Q 𝓕 Y (fun _ _ => 0) (fun _ _ => α))
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hYU : ∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U)
    {g : (Fin d → ℝ) → ℝ} (hgm : Measurable g) (hgc : ∀ y ∈ U, ContDiffAt ℝ 2 g y)
    {Dr Br : (Fin d → ℝ) → ℝ}
    (hDr : ∀ y ∈ U, ∀ t : ℝ≥0, itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) y t 0 α = Dr y)
    (hBr : ∀ y ∈ U, ∀ t : ℝ≥0, itoBracket (fun p : ℝ × (Fin d → ℝ) => g p.2) y t α = Br y)
    {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    (hdom : ∀ t : ℝ≥0, ∃ C, ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ ρ ω →
      |locComp Y g Dr v ω| ≤ C ∧ |locSq Y g Dr Br v ω| ≤ C) :
    HasMartingaleModification Q 𝓕 (stoppedProcess (locComp Y g Dr) ρ) ∧
      HasMartingaleModification Q 𝓕 (stoppedProcess (locSq Y g Dr Br) ρ) := by
  set Yρ := stoppedProcess Y ρ with hYρdef
  have hYρ := hStop d Ω Q 𝓕 Y _ _ hY ρ hρ
  have hYρU : ∀ᵐ ω ∂Q, ∀ t, Yρ t ω ∈ U := hYU.mono fun ω h t => h _
  have hφm : Measurable (fun p : ℝ × (Fin d → ℝ) => g p.2) := hgm.comp measurable_snd
  have hφc : ContDiffOn ℝ 2 (fun p : ℝ × (Fin d → ℝ) => g p.2) (univ ×ˢ U) := fun p hp =>
    ((hgc p.2 hp.2).comp p contDiffAt_snd).contDiffWithinAt
  have hZ := hIto d Ω Q 𝓕 Yρ _ _ hYρ U hU hYρU _ hφm hφc
  obtain ⟨σ, -, hσlim, hMM⟩ := hZ.localizing
  -- the drift and bracket of the stopped Itô output
  have hdr : ∀ ω, (∀ t, Y t ω ∈ U) → ∀ r : ℝ≥0,
      itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) (Yρ r ω) r
        (switchAfter ρ (fun _ _ => (0 : Fin d → ℝ)) r ω) (switchAfter ρ (fun _ _ => α) r ω) =
      if (r : WithTop ℝ≥0) ≤ ρ ω then Dr (Y r ω) else 0 := by
    intro ω hω r
    unfold switchAfter
    by_cases h : (r : WithTop ℝ≥0) ≤ ρ ω
    · simp only [h, ite_true]
      rw [hYρdef, stoppedProcess_eq_of_le h]
      exact hDr _ (hω r) r
    · simp only [h, ite_false]
      exact itoDrift_zero_cov ((hgc _ (hω _)).differentiableAt (by norm_num)) r
  have hbr : ∀ ω, (∀ t, Y t ω ∈ U) → ∀ r : ℝ≥0,
      itoBracket (fun p : ℝ × (Fin d → ℝ) => g p.2) (Yρ r ω) r
        (switchAfter ρ (fun _ _ => α) r ω) =
      if (r : WithTop ℝ≥0) ≤ ρ ω then Br (Y r ω) else 0 := by
    intro ω hω r
    unfold switchAfter
    by_cases h : (r : WithTop ℝ≥0) ≤ ρ ω
    · simp only [h, ite_true]
      rw [hYρdef, stoppedProcess_eq_of_le h]
      exact hBr _ (hω r) r
    · simp only [h, ite_false]
      exact itoBracket_zero_cov _ _ r
  set φ : ℝ × (Fin d → ℝ) → ℝ := fun p => g p.2 with hφdef
  set Zp : ℝ≥0 → Ω → Fin 1 → ℝ := fun t ω _ => φ ((t : ℝ), Yρ t ω)
  set βZ : ℝ≥0 → Ω → Fin 1 → ℝ := fun t ω _ => itoDrift φ (Yρ t ω) t
    (switchAfter ρ (fun _ _ => (0 : Fin d → ℝ)) t ω) (switchAfter ρ (fun _ _ => α) t ω)
  set αZ : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ := fun t ω => Matrix.of fun _ _ =>
    itoBracket φ (Yρ t ω) t (switchAfter ρ (fun _ _ => α) t ω)
  have hcomp : ∀ ω, (∀ t, Y t ω ∈ U) → ∀ t,
      smCompensated Zp βZ 0 t ω = stoppedProcess (locComp Y g Dr) ρ t ω := by
    intro ω hω t
    simp only [smCompensated, Zp, βZ]
    simp_rw [hdr ω hω]
    rw [integral_Ioc_switch (fun r => Dr (Y r.toNNReal ω)) t (ρ ω)]
    simp only [hYρdef, stoppedProcess_zero']
    rfl
  have hsq : ∀ ω, (∀ t, Y t ω ∈ U) → ∀ t,
      smCompensated Zp βZ 0 t ω * smCompensated Zp βZ 0 t ω -
          ∫ r in Ioc (0 : ℝ) t, αZ r.toNNReal ω 0 0 =
        stoppedProcess (locSq Y g Dr Br) ρ t ω := by
    intro ω hω t
    rw [hcomp ω hω t]
    simp only [αZ, Matrix.of_apply]
    simp_rw [hbr ω hω]
    rw [integral_Ioc_switch (fun r => Br (Y r.toNNReal ω)) t (ρ ω)]
    rfl
  have hev : ∀ ω, Tendsto (fun m => σ m ω) atTop (𝓝 ⊤) → ∀ t : ℝ≥0,
      ∀ᶠ m in atTop, (t : WithTop ℝ≥0) ≤ σ m ω := fun ω hω t =>
    (hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))).mono fun m hm => le_of_lt hm
  refine ⟨hasMM_of_tendsto (Z := fun m => stoppedProcess (smCompensated Zp βZ 0) (σ m))
    (fun m => (hMM m).1 0) (fun t => ?_) (fun t => ?_),
    hasMM_of_tendsto (Z := fun m => stoppedProcess (fun t ω => smCompensated Zp βZ 0 t ω *
      smCompensated Zp βZ 0 t ω - ∫ r in Ioc (0 : ℝ) t, αZ r.toNNReal ω 0 0) (σ m))
    (fun m => (hMM m).2 0 0) (fun t => ?_) (fun t => ?_)⟩
  · filter_upwards [hYU, hσlim] with ω hω hσω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev ω hσω t] with m hm
    rw [stoppedProcess_eq_of_le hm, hcomp ω hω t]
  · obtain ⟨C, hC⟩ := hdom t
    refine ⟨C, fun m => ?_⟩
    filter_upwards [hYU, hC] with ω hω hCω
    change |smCompensated Zp βZ 0 ((min (t : WithTop ℝ≥0) (σ m ω)).untopA) ω| ≤ C
    rw [hcomp ω hω]
    exact (hCω _ ((untopA_min_le _ _).trans (untopA_min_le _ _)) (untopA_min_le_rho _ _)).1
  · filter_upwards [hYU, hσlim] with ω hω hσω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev ω hσω t] with m hm
    rw [stoppedProcess_eq_of_le hm, hsq ω hω t]
  · obtain ⟨C, hC⟩ := hdom t
    refine ⟨C, fun m => ?_⟩
    filter_upwards [hYU, hC] with ω hω hCω
    change |smCompensated Zp βZ 0 ((min (t : WithTop ℝ≥0) (σ m ω)).untopA) ω *
      smCompensated Zp βZ 0 ((min (t : WithTop ℝ≥0) (σ m ω)).untopA) ω -
        ∫ r in Ioc (0 : ℝ) ((min (t : WithTop ℝ≥0) (σ m ω)).untopA : ℝ≥0), αZ r.toNNReal ω 0 0| ≤ C
    rw [hsq ω hω]
    exact (hCω _ ((untopA_min_le _ _).trans (untopA_min_le _ _)) (untopA_min_le_rho _ _)).2

end BlockBand.SourceProcess.Stochastic.Dyson
