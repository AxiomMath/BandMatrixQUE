module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.LocData
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The augmented instance satisfies the integral-bound scheme hypotheses)

Under `LocData Q 𝓖 Y β α U W φ σ T c ys`, with `M` bounding the partial derivatives of `φ`
on `[0, T] × closure W`, `M₀ ≥ |φ(0, ·)|` on `closure W`, and martingales `MN`, `MB` that are
modifications of the `σ`-stopped compensated coordinates and products of `Y`:

`LocData.ihyp : IHyp Q 𝓖 (augK T L W ys) augZ augβ augα (augN MN) (augB MB) ((1 + M)(T + c))`
with `L = M₀ + M (T + c)`, and `augK ⊆ augSet U` (`augK_subset`).
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}

/-- The compact of the instance. -/
def augK (T : ℝ≥0) (L : ℝ) (W : Set (Fin d → ℝ)) (ys : Fin d → ℝ) : Set (Fin (d + 2) → ℝ) :=
  (fun q : (ℝ × ℝ) × (Fin d → ℝ) => consAug q.1.1 q.1.2 q.2) ''
    ((Icc 0 (T : ℝ) ×ˢ Icc (-L) L) ×ˢ insert ys (closure W))

theorem isCompact_augK {T : ℝ≥0} {L : ℝ} {W : Set (Fin d → ℝ)} {ys : Fin d → ℝ}
    (hW : IsCompact (closure W)) : IsCompact (augK T L W ys) :=
  ((isCompact_Icc.prod isCompact_Icc).prod (hW.insert ys)).image continuous_consAug

theorem projL_consAug (a b : ℝ) (y : Fin d → ℝ) : projL d (consAug a b y) = (a, y) := rfl

theorem augK_subset {T : ℝ≥0} {L : ℝ} {U W : Set (Fin d → ℝ)} {ys : Fin d → ℝ}
    (hWU : closure W ⊆ U) (hys : ys ∈ U) : augK T L W ys ⊆ augSet U := by
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨mem_univ _, ?_⟩
  rcases hq.2 with h | h
  · rw [show (projL d (consAug q.1.1 q.1.2 q.2)).2 = q.2 from rfl, h]; exact hys
  · exact hWU h

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m₀}
  {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
  {U W : Set (Fin d → ℝ)} {φ : ℝ × (Fin d → ℝ) → ℝ} {σ : Ω → WithTop ℝ≥0} {T : ℝ≥0} {c : ℝ}
  {ys : Fin d → ℝ}

theorem augA_sub (t : ℝ≥0) (ω : Ω) :
    augA φ Y β α σ W t ω - augA φ Y β α σ W 0 ω =
      ∫ v in Ioc (0 : ℝ) t, switchAfter σ (driftPath φ Y β α) v.toNNReal ω := by
  simp [augA]

theorem LocData.ihyp (D : LocData Q 𝓖 Y β α U W φ σ T c ys) {M M₀ : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ Icc (0 : ℝ) T ×ˢ closure W, |partialTime φ p| ≤ M ∧
      (∀ i, |partialSpace φ p i| ≤ M) ∧ ∀ i j, |partialSpace2 φ p i j| ≤ M)
    (hM₀0 : 0 ≤ M₀) (hM₀ : ∀ y ∈ closure W, |φ (0, y)| ≤ M₀)
    {MN : Fin d → ℝ≥0 → Ω → ℝ} {MB : Fin d → Fin d → ℝ≥0 → Ω → ℝ}
    (hMN : ∀ i, Martingale (MN i) 𝓖 Q)
    (hMNeq : ∀ i t, MN i t =ᵐ[Q] stoppedProcess (smCompensated Y β i) σ t)
    (hMB : ∀ i j, Martingale (MB i j) 𝓖 Q)
    (hMBeq : ∀ i j t, MB i j t =ᵐ[Q] stoppedProcess (fun t ω =>
      smCompensated Y β i t ω * smCompensated Y β j t ω -
        ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j) σ t) :
    IHyp Q 𝓖 (augK T (M₀ + M * (T + c)) W ys) (augZ φ Y β α σ W ys) (augβ φ Y β α σ)
      (augα α σ) (augN MN) (augB MB) ((1 + M) * (T + c)) := by
  classical
  have hdr := isStronglyProgressive_driftPath φ D.sm.progressive D.sm.drift_progressive
    D.sm.cov_progressive
  have hG0 : MeasurableSet[𝓖 0] {ω | Y 0 ω ∈ W} :=
    (D.sm.adapted 0).measurable D.hW.measurableSet
  refine ⟨isCompact_augK D.hWc, ?_, ?_, fun t => ?_, ?_, ?_, fun t => ?_, ?_, ?_, ?_, ?_⟩
  · -- mem
    filter_upwards [D.ae_good] with ω hω t
    refine ⟨(((stopTime (σ ω) t : ℝ), augA φ Y β α σ W t ω),
      if Y 0 ω ∈ W then Y (stopTime (σ ω) t) ω else ys), ⟨⟨⟨NNReal.coe_nonneg _, ?_⟩, ?_⟩, ?_⟩,
      rfl⟩
    · exact_mod_cast stopTime_le_of_le (D.le_T ω) t
    · refine abs_le.1 ?_
      have h1 := hω.abs_int_dr_le D hM0 hM t
      have h2 : |(if Y 0 ω ∈ W then φ (0, Y 0 ω) else 0)| ≤ M₀ := by
        split_ifs with hG
        · exact hM₀ _ (subset_closure hG)
        · rw [abs_zero]; exact hM₀0
      unfold augA
      rw [integral_switch_path]
      exact (abs_add_le _ _).trans (add_le_add h2 h1)
    · split_ifs with hG
      · exact Or.inr (hω.2.2.2.1 hG t)
      · exact Or.inl rfl
  · -- continuity
    filter_upwards [D.ae_good] with ω hω
    refine continuous_consAug_comp (NNReal.continuous_coe.comp (continuous_stopTime _))
      (continuous_const.add (continuous_setIntegral_Ioc
        (g := fun u => switchAfter σ (driftPath φ Y β α) u ω) fun t =>
          integrableOn_switchAfter_path σ (driftPath φ Y β α) (fun x : ℝ => x) rfl ω t
            (hω.integrableOn_dr D t))) ?_
    split_ifs
    · exact hω.1.comp (continuous_stopTime _)
    · exact continuous_const
  · -- adaptedness
    have h1 : StronglyMeasurable[𝓖 t] fun ω => ((stopTime (σ ω) t : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp_stronglyMeasurable
        ((isStronglyProgressive_min_stopping_time D.stop).stronglyAdapted t)
    have hGt : MeasurableSet[𝓖 t] {ω | Y 0 ω ∈ W} := 𝓖.mono zero_le _ hG0
    have hφ0 : StronglyMeasurable[𝓖 t] fun ω => φ (0, Y 0 ω) :=
      ((D.hφm.comp (measurable_const.prodMk (D.sm.adapted 0).measurable)).stronglyMeasurable).mono
        (𝓖.mono zero_le)
    have h2 : StronglyMeasurable[𝓖 t] fun ω => augA φ Y β α σ W t ω :=
      (hφ0.ite hGt stronglyMeasurable_const).add
        (stronglyMeasurable_integral_of_progressive (isStronglyProgressive_switchAfter hdr D.stop) t)
    have h3 : StronglyMeasurable[𝓖 t] fun ω =>
        if Y 0 ω ∈ W then Y (stopTime (σ ω) t) ω else ys :=
      (D.sm.progressive.stronglyAdapted_stoppedProcess D.stop t).ite hGt stronglyMeasurable_const
    exact (stronglyMeasurable_consAug h1 h2 h3).aestronglyMeasurable
  · -- integrability
    filter_upwards [D.ae_good] with ω hω t
    refine ⟨fun k => ?_, fun k l => ?_⟩
    · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
      · exact integrableOn_switchAfter_path σ (fun _ _ => (1 : ℝ)) (fun x : ℝ => x) rfl ω t
          (integrable_const (1 : ℝ))
      · exact integrableOn_switchAfter_path σ (driftPath φ Y β α) (fun x : ℝ => x) rfl ω t
          (hω.integrableOn_dr D t)
      · exact integrableOn_switchAfter_path σ β (fun b => b i) rfl ω t ((hω.2.2.1 t).1 i)
    · refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
      · exact integrableOn_zero
      · exact integrableOn_zero
      · refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun j => ?_) l) l
        · exact integrableOn_zero
        · exact integrableOn_zero
        · exact integrableOn_switchAfter_path σ α (fun a => a i j) rfl ω t ((hω.2.2.1 t).2 i j)
  · -- integral bound
    filter_upwards [D.ae_good] with ω hω t
    unfold ctrlI
    simp_rw [ctrl_aug]
    rw [integral_switch_path (σ := σ)
      (fun u ω => 1 + |driftPath φ Y β α u ω| + ctrl β (matF α) u ω) t ω]
    exact hω.int_aug_le D hM0 hM t
  · -- measurability of the control
    have hp : IsStronglyProgressive 𝓖
        (fun u ω => 1 + |driftPath φ Y β α u ω| + ctrl β (matF α) u ω) := fun i =>
      (stronglyMeasurable_const.add (continuous_abs.comp_stronglyMeasurable (hdr i))).add
        (isStronglyProgressive_ctrl D.sm.drift_progressive D.sm.cov_progressive i)
    have e : ctrlI (augβ φ Y β α σ) (augα α σ) t = fun ω => ∫ v in Ioc (0 : ℝ) t,
        switchAfter σ (fun u ω => 1 + |driftPath φ Y β α u ω| + ctrl β (matF α) u ω)
          v.toNNReal ω := by
      funext ω; unfold ctrlI; simp_rw [ctrl_aug]
    rw [e]
    exact ((stronglyMeasurable_integral_of_progressive
      (isStronglyProgressive_switchAfter hp D.stop) t).mono (𝓖.le t)).aestronglyMeasurable
  · -- martingales
    intro k
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · exact martingale_const 𝓖 Q (0 : ℝ)
    · exact martingale_const 𝓖 Q (0 : ℝ)
    · exact hMN i
  · -- compensated coordinates
    intro k t
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · refine ae_of_all _ fun ω => ?_
      show (0 : ℝ) = _
      beta_reduce
      rw [augZ_zero_coord, augZ_zero_coord, drI_augβ_zero, stopTime_zero']
      simp
    · refine ae_of_all _ fun ω => ?_
      show (0 : ℝ) = _
      beta_reduce
      rw [augZ_one_coord, augZ_one_coord, drI_augβ_one, ← augA_sub]
      ring
    · filter_upwards [hMNeq i t] with ω h
      show MN i t ω = _
      rw [h, augZ_ss_coord, augZ_ss_coord, drI_augβ_ss, stoppedProcess_eq_stopTime]
      by_cases hG : Y 0 ω ∈ W
      · simp only [hG, ↓reduceIte, smCompensated, stopTime_zero']
      · simp only [hG, ↓reduceIte, smCompensated, D.off ω hG, stopTime_of_eq_zero']
        simp
  · -- bracket martingales
    intro k l
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · exact martingale_const 𝓖 Q (0 : ℝ)
    · exact martingale_const 𝓖 Q (0 : ℝ)
    · refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun j => ?_) l) l
      · exact martingale_const 𝓖 Q (0 : ℝ)
      · exact martingale_const 𝓖 Q (0 : ℝ)
      · exact hMB i j
  · -- compensated products
    intro k l t
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun i => ?_) k) k
    · refine ae_of_all _ fun ω => ?_
      show (0 : ℝ) = 0 * _ - _
      rw [difJ_eq_zero_of (fun u ω => augα_zero_row (α := α) (σ := σ) u ω l)]; ring
    · refine ae_of_all _ fun ω => ?_
      show (0 : ℝ) = 0 * _ - _
      rw [difJ_eq_zero_of (fun u ω => augα_one_row (α := α) (σ := σ) u ω l)]; ring
    · refine Fin.cases ?_ (fun l => Fin.cases ?_ (fun j => ?_) l) l
      · refine ae_of_all _ fun ω => ?_
        show (0 : ℝ) = _ * 0 - _
        rw [difJ_eq_zero_of (fun u ω => augα_ss_zero (α := α) (σ := σ) u ω i)]; ring
      · refine ae_of_all _ fun ω => ?_
        show (0 : ℝ) = _ * 0 - _
        rw [difJ_eq_zero_of (fun u ω => augα_ss_one (α := α) (σ := σ) u ω i)]; ring
      · filter_upwards [hMBeq i j t, hMNeq i t, hMNeq j t] with ω h1 h2 h3
        show MB i j t ω = MN i t ω * MN j t ω - _
        rw [h1, h2, h3, difJ_augα_ss]
        simp only [stoppedProcess_eq_stopTime]

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
