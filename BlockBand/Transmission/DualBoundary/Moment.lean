module

public import BlockBand.Transmission.DualBoundary.Transfer
public import BlockBand.Transmission.DualEntrance.LiftEntrance

/-!
# `firstMoment` of `DualBoundaryStartContract`

* `lintegral_lintegral_total_le` (Tonelli, any one-pair boundary realization): a bound
  `E R_s ≤ c` at every fixed `s` gives `E∫⁻_{[0,t]} R ≤ c t`. Joint measurability of
  `(ω, s) ↦ R_s(ω)` is not assumed: `R` agrees, for a.e. `ω` and every `s`, with the measurable
  liminf of the dyadic samples.
* `LiftFamily.lintegral_total₂_le` (the lifted realization `N₂, X₂, Y₂` from any start with
  `S(π ξ) ≤ B`): `E R_t ≤ B` for every `t`. Proof: on `good₂`, `R_t = S(Z̄_t)` equals
  `S_{t ∧ e_n}` for all large `n` before `ζ` and is `0` after, so `R_t ≤ liminf_n S_{t∧e_n}`;
  Fatou and optional stopping `E S_{t∧e_n} = E S₀` (`integral_Sp_stop`). Fatou suffices
  because only an upper bound is needed.
* **`firstMoment_lift`**: every boundary start has a realization on `LΩ Unit` (the one of
  `DualEntrance.liftBoundaryDual_holds`) with `E∫⁻_{[0,t]} R ≤ t(x + y)`.
* **`firstMoment_of_unique`**: the field `firstMoment`, from the field `unique` (transfer
  through the law of `truncDualState`, `lintegral_total_eq_of_map_eq`).

Measure: driver law `LP μ` (`μ = δ_()` for `firstMoment_lift`) or any probability
space carrying a boundary realization; `D₀ > 0`; `t ≥ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.Dual.Exists BlockBand.Transmission.DualLift
open scoped NNReal ENNReal

section Generic

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ}
  {x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- **Tonelli for `R` along a one-pair boundary realization.** -/
theorem lintegral_lintegral_total_le (h : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    {c : ℝ≥0∞} (hc : ∀ s : ℝ≥0, ∫⁻ ω, ENNReal.ofReal (dualTotal (N s ω) (X s ω) (Y s ω)) ∂P ≤ c)
    (t : ℝ) :
    ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
        ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P ≤
      c * ENNReal.ofReal t := by
  have hΦ := measurable_truncDualState h
  have := h.prob
  set G : Ω × ℝ → ℝ≥0∞ := fun q =>
    liminf (fun k => ENNReal.ofReal (dyTotal k (truncDualState N X Y q.1, q.2))) atTop with hGdef
  have hG : Measurable G := Measurable.liminf fun k => ENNReal.measurable_ofReal.comp
    ((measurable_dyTotal k).comp ((hΦ.comp measurable_fst).prodMk measurable_snd))
  have hGe : ∀ᵐ ω ∂P, ∀ s : ℝ,
      G (ω, s) = ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)) := by
    filter_upwards [ae_continuous_pathTotal h] with ω hω s
    rw [← pathTotal_truncDualState]
    exact ((ENNReal.continuous_ofReal.tendsto _).comp (tendsto_dyTotal hω s)).liminf_eq
  calc ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
        ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P
      = ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t, G (ω, s)) ∂P :=
        lintegral_congr_ae (hGe.mono fun ω hω => by simp_rw [hω])
    _ = ∫⁻ s in Icc (0 : ℝ) t, (∫⁻ ω, G (ω, s) ∂P) :=
        lintegral_lintegral_swap (f := fun ω s => G (ω, s)) hG.aemeasurable
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) t, c := by
        refine lintegral_mono fun s => ?_
        rw [lintegral_congr_ae (hGe.mono fun ω hω => hω s)]
        exact hc _
    _ = c * ENNReal.ofReal t := by simp [lintegral_const, Real.volume_Icc]

end Generic

namespace LiftFamily

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ} (F : DualLift.LiftFamily μ D0 ξ)

/-- On `good₂`, `R_t ≤ liminf_n S_{t ∧ e_n}` (equality eventually before `ζ`, `R_t = 0` after). -/
theorem total₂_le_liminf {ω : LΩ S} (hω : ω ∈ F.good₂) (t : ℝ≥0) :
    ENNReal.ofReal (dualTotal (F.N₂ t ω) (F.X₂ t ω) (F.Y₂ t ω)) ≤
      liminf (fun n => ENNReal.ofReal (F.Sp n t ω)) atTop := by
  have hg := (F.good₂_spec hω).1
  have hN : F.N₂ t ω = if F.zeta ω ≤ t then 0 else 1 := by
    simp only [DualLift.LiftFamily.N₂, hω, ite_true, F.Nd_of_good hg]
  by_cases hz : F.zeta ω ≤ t
  · rw [hN, ite_eq_left hz]; simp [dualTotal]
  · obtain ⟨n, hn⟩ := lt_iSup_iff.1 (not_le.1 hz)
    have hev : ∀ᶠ k in atTop, ENNReal.ofReal (F.Sp k t ω) =
        ENNReal.ofReal (dualTotal (F.N₂ t ω) (F.X₂ t ω) (F.Y₂ t ω)) := by
      filter_upwards [eventually_ge_atTop n] with k hk
      have hle : (t : WithTop ℝ≥0) ≤ F.e k ω := hn.le.trans ((F.good_spec hg).2 n k hk).1
      rw [hN, ite_eq_right hz]
      simp [dualTotal, DualLift.LiftFamily.X₂, DualLift.LiftFamily.Y₂,
        DualLift.LiftFamily.Z₂, hω, DualLift.LiftFamily.Zd, hg, F.Z_eq hg hle,
        DualLift.LiftFamily.Sp, tot]
    rw [liminf_congr hev, liminf_const]

/-- **`E R_t ≤ B` for the lifted realization** from a start with `S(π ξ) ≤ B`. -/
theorem lintegral_total₂_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) {B : ℝ}
    (hB : ∀ ω, tot (liftProj (ξ ω)) ≤ B) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (dualTotal (F.N₂ t ω) (F.X₂ t ω) (F.Y₂ t ω)) ∂LP μ ≤
      ENNReal.ofReal B := by
  have hS : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (F.Sp n t ω) ∂LP μ ≤ ENNReal.ofReal B := by
    intro n
    obtain ⟨hint, heq⟩ := F.integral_Sp_stop hD0 hξ n (σ := fun _ => (t : WithTop ℝ≥0))
      (isStoppingTime_const _ t) t (A := univ) MeasurableSet.univ (fun ω _ => hB ω)
    have et : (t : WithTop ℝ≥0).untopA = t := rfl
    simp only [min_self, et, Measure.restrict_univ, integrableOn_univ] at hint heq
    have htm : Measurable fun ω => tot (liftProj (ξ ω)) :=
      DualLift.LiftFamily.measurable_tot_start hξ
    have hpos : ∀ ω, 0 < tot (liftProj (ξ ω)) := fun ω => lS_pos (hξ.mem ω)
    have htint : Integrable (fun ω => tot (liftProj (ξ ω))) (LP μ) := by
      refine Integrable.of_bound (C := max B 0) htm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (hpos ω)]
      exact (hB ω).trans (le_max_left _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun ω => (F.Sp_pos hξ n t ω).le), heq,
      ofReal_integral_eq_lintegral_ofReal htint (ae_of_all _ fun ω => (hpos ω).le)]
    calc ∫⁻ ω, ENNReal.ofReal (tot (liftProj (ξ ω))) ∂LP μ ≤ ∫⁻ _, ENNReal.ofReal B ∂LP μ :=
          lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hB ω)
      _ = ENNReal.ofReal B := by simp
  calc ∫⁻ ω, ENNReal.ofReal (dualTotal (F.N₂ t ω) (F.X₂ t ω) (F.Y₂ t ω)) ∂LP μ
      ≤ ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F.Sp n t ω)) atTop ∂LP μ :=
        lintegral_mono_ae ((F.ae_good₂ hD0 hξ).mono fun ω hω => total₂_le_liminf F hω t)
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F.Sp n t ω) ∂LP μ) atTop :=
        lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp
          ((F.measurable_Sp hD0 hξ n t).mono ((L𝓖 μ).le t) le_rfl)
    _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' (Frequently.of_forall hS)

end LiftFamily

/-- **`firstMoment` for one realization of every boundary start** (on `LΩ Unit`). -/
theorem firstMoment_lift {D0 : ℝ} (hD0 : 0 < D0) {x y : ℝ} (hxy : IsDualStart ![x] ![y]) :
    ∃ (N : ℝ≥0 → LΩ Unit → ℕ) (X Y : ℝ≥0 → LΩ Unit → ℕ → ℝ),
      IsBoundaryDualProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y] N X Y ∧
      ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) t,
            ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)))
            ∂LP (Measure.dirac ()) ≤ ENNReal.ofReal (t * (x + y)) := by
  have hx : 0 ≤ x := hxy.2.2.1 0
  have hy := hxy.2.2.2.1 0
  have hs : 0 < x + y := hxy.2.2.2.2 0 0
  have hξ := isLiftStart_section hx hy.1 hy.2 hs
  obtain ⟨F⟩ := nonempty_liftFamily hD0 hξ
  have hP : IsBoundaryDualProcess (LP (Measure.dirac ())) (L𝓖 (Measure.dirac ())) D0 ![x] ![y]
      F.N₂ F.X₂ F.Y₂ :=
    { prob := inferInstance
      adapted := F.adapted₂ hD0 hξ
      start := Eventually.of_forall fun ω => ⟨F.N₂_zero ω, fun i => start_values F hx ω i⟩
      paths := by
        filter_upwards [F.ae_good₂ hD0 hξ,
          DualEntrance.liftEntrance_holds hD0 Unit (Measure.dirac ()) _ hξ F] with ω h1 h2
        exact F.isBoundaryDeletionPath_N₂ hξ h1 h2
      martingale := fun q hq hq1 f hf hfc hfs => by
        obtain rfl : q = 1 := le_antisymm hq1 hq
        exact F.martingale_dualMartingale₂ hD0 hξ hf hfc hfs }
  refine ⟨F.N₂, F.X₂, F.Y₂, hP, fun t ht => ?_⟩
  have hB : ∀ ω, tot (liftProj (sectionStart x y ω)) ≤ x + y := fun ω => by
    rw [sectionStart, liftProj_liftSection hx]; simp [tot]
  refine (lintegral_lintegral_total_le hP (fun s => LiftFamily.lintegral_total₂_le F hD0 hξ hB s)
    t).trans_eq ?_
  rw [ENNReal.ofReal_mul ht, mul_comm]

/-- **The field `firstMoment` from the field `unique`.** -/
theorem firstMoment_of_unique
    (hU : ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
      ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (P₁ : Measure Ω₁)
        (N₁ : ℝ≥0 → Ω₁ → ℕ) (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
        (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (P₂ : Measure Ω₂)
        (N₂ : ℝ≥0 → Ω₂ → ℕ) (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
        IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁ →
        IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂ →
        P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂)) :
    ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P ≤
          ENNReal.ofReal (t * (x + y)) := by
  intro D0 hD0 x y hxy Ω m 𝓖 P N X Y h t ht
  obtain ⟨N', X', Y', h', hb⟩ := firstMoment_lift hD0 hxy
  rw [lintegral_total_eq_of_map_eq h h'
    (hU D0 hD0 x y hxy Ω m 𝓖 P N X Y _ _ _ _ N' X' Y' h h') t]
  exact hb t ht

end BlockBand.Transmission.DualBoundary
