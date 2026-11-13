module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.OptionalMain
public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Contract: pathwise identities and measurability for stopping

For a `𝓖`-stopping time `ρ` (raw filtration) and the contract objects of
`BlockBand.Internal.Contracts.Transmission`:

* `setIntegral_switch`: `∫_{(0,u]} 1{v ≤ ρ} f(v) dv = ∫_{(0, u∧ρ]} f(v) dv` (every path);
* `smCompensated_stopped`: the compensated coordinates of `Y^ρ` with switched-off drift are the
  compensated coordinates of `Y` evaluated at `u ∧ ρ`;
* `isStronglyProgressive_switchAfter`: switching off after a stopping time keeps progressive
  measurability.

The a.s. path continuity of the compensated coordinates is proved elsewhere, as
`continuous_smCompensated`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

theorem stopTime_comm (a b : WithTop ℝ≥0) (t : ℝ≥0) :
    stopTime a (stopTime b t) = stopTime b (stopTime a t) := by
  induction a with
  | top => rw [stopTime_top, stopTime_top]
  | coe a =>
    induction b with
    | top => rw [stopTime_top, stopTime_top]
    | coe b =>
      simp only [stopTime_coe]
      rw [min_right_comm]

theorem measurableSet_toNNReal_le (r : WithTop ℝ≥0) :
    MeasurableSet {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} :=
  measurableSet_le (WithTop.measurable_coe.comp measurable_real_toNNReal) measurable_const

/-- Integrating a function switched off after `r` over `(0, u]`. -/
theorem setIntegral_switch {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (r : WithTop ℝ≥0) (u : ℝ≥0) :
    ∫ v in Ioc (0 : ℝ) u, (if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0) =
      ∫ v in Ioc (0 : ℝ) (stopTime r u), f v := by
  classical
  have e : (fun v : ℝ => if (v.toNNReal : WithTop ℝ≥0) ≤ r then f v else 0) =
      {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r}.indicator f := by
    funext v
    by_cases h : (v.toNNReal : WithTop ℝ≥0) ≤ r
    · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} from h)]
      split_ifs; rfl
    · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} from h)]
      split_ifs; rfl
  rw [e, setIntegral_indicator (measurableSet_toNNReal_le r)]
  have hset : Ioc (0 : ℝ) u ∩ {v : ℝ | (v.toNNReal : WithTop ℝ≥0) ≤ r} =
      Ioc (0 : ℝ) (stopTime r u) := by
    ext v
    show (v ∈ Ioc (0 : ℝ) u ∧ (v.toNNReal : WithTop ℝ≥0) ≤ r) ↔ v ∈ Ioc (0 : ℝ) (stopTime r u)
    simp only [mem_Ioc]
    constructor
    · rintro ⟨⟨h0, hu⟩, hr⟩
      refine ⟨h0, ?_⟩
      have hv : v.toNNReal ≤ u := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0.le]; exact hu
      have := le_stopTime hr hv
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0.le] at this
      exact this
    · rintro ⟨h0, hs⟩
      have hsu : (stopTime r u : ℝ) ≤ u := by exact_mod_cast stopTime_le r u
      refine ⟨⟨h0, hs.trans hsu⟩, ?_⟩
      have hv : v.toNNReal ≤ stopTime r u := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0.le]; exact hs
      refine (WithTop.coe_le_coe.2 hv).trans ?_
      induction r with
      | top => exact le_top
      | coe a => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
  rw [hset]

variable {Ω : Type*} {d : ℕ}

/-- The compensated coordinates of the stopped process with switched-off drift. -/
theorem smCompensated_stopped (Y β : ℝ≥0 → Ω → Fin d → ℝ) (ρ : Ω → WithTop ℝ≥0) (i : Fin d)
    (u : ℝ≥0) (ω : Ω) :
    smCompensated (stoppedProcess Y ρ) (switchAfter ρ β) i u ω =
      smCompensated Y β i (stopTime (ρ ω) u) ω := by
  simp only [smCompensated, stoppedProcess_eq_stopTime, switchAfter]
  have h0 : stopTime (ρ ω) 0 = 0 := le_antisymm (stopTime_le _ 0) zero_le
  rw [h0]
  congr 1
  have := setIntegral_switch (fun v : ℝ => β v.toNNReal ω i) (ρ ω) u
  rw [← this]
  congr 1; funext v
  split_ifs <;> rfl

/-- Same for the covariance integral. -/
theorem integral_switchAfter_α (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ) (ρ : Ω → WithTop ℝ≥0)
    (i j : Fin d) (u : ℝ≥0) (ω : Ω) :
    ∫ v in Ioc (0 : ℝ) u, switchAfter ρ α v.toNNReal ω i j =
      ∫ v in Ioc (0 : ℝ) (stopTime (ρ ω) u), α v.toNNReal ω i j := by
  rw [← setIntegral_switch (fun v : ℝ => α v.toNNReal ω i j) (ρ ω) u]
  congr 1; funext v
  simp only [switchAfter]
  split_ifs <;> rfl

/-- Switching off after a stopping time keeps strong progressive measurability. -/
theorem isStronglyProgressive_switchAfter {m₀ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 m₀}
    {G : Type*} [TopologicalSpace G] [Zero G] {f : ℝ≥0 → Ω → G}
    (hf : IsStronglyProgressive 𝓖 f) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ) :
    IsStronglyProgressive 𝓖 (switchAfter ρ f) := by
  classical
  intro i
  have hmin := isStronglyProgressive_min_stopping_time hρ i
  set S : Set (Set.Iic i × Ω) := {p | ((p.1 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ p.2}
  have hS : MeasurableSet[Subtype.instMeasurableSpace.prod (𝓖 i)] S := by
    have e : S = {p : Set.Iic i × Ω | (min ((p.1 : ℝ≥0) : WithTop ℝ≥0) (ρ p.2)).untopA =
        (p.1 : ℝ≥0)} := by
      ext p
      simp only [S, mem_ofPred]
      constructor
      · intro h; rw [min_eq_left h]; rfl
      · intro h
        by_contra hlt
        push Not at hlt
        induction hρp : ρ p.2 with
        | top => rw [hρp] at hlt; exact absurd hlt (not_lt.2 le_top)
        | coe a =>
          rw [hρp] at h hlt
          rw [← WithTop.coe_min, show (WithTop.untopA (((min (p.1 : ℝ≥0) a) : ℝ≥0) :
            WithTop ℝ≥0)) = min (p.1 : ℝ≥0) a from WithTop.untopD_coe _ _] at h
          have : a < (p.1 : ℝ≥0) := WithTop.coe_lt_coe.1 hlt
          rw [min_eq_right this.le] at h
          exact absurd h this.ne
    rw [e]
    exact measurableSet_eq_fun hmin.measurable
      ((measurable_subtype_coe (p := fun x => x ∈ Set.Iic i)).comp measurable_fst)
  have e : (fun p : Set.Iic i × Ω => switchAfter ρ f p.1 p.2) =
      S.piecewise (fun p => f p.1 p.2) (fun _ => 0) := by
    funext p
    simp only [switchAfter, Set.piecewise, S, mem_ofPred]
  rw [e]
  exact (hf i).piecewise hS stronglyMeasurable_const

end BlockBand.SourceProcess.Stochastic.Semimartingale
