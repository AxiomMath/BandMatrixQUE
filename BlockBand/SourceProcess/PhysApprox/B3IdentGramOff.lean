module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramGood

/-!
# Tested identities off the birth times suffice

The conditioned fdd limit `IsCapFddLimitAll` only tests model times `u` that are not birth
times (`s + u ≠ τ_j`). This file shows that tested identities whose test times and increment
times avoid the finite set of birth times give the full tested identities, when the stopped
process is bounded and the observables are right-continuous. Measure: an arbitrary finite
(resp. probability) measure `Q`.

* `IsTestedMartOff B`: `IsTestedMart` with all times (`s`, `t`, the test times `u_l`) outside `B`.
* **`isTestedMart_of_off`** (abstract): for finite `B`, observables right-continuous for every
  `ω`, `X` continuous for every `ω` and a.s. bounded on every `[0, t]`, `IsTestedMartOff B`
  gives `IsTestedMart` (shift all times by `ε_n ↓ 0` avoiding `B`; dominated convergence).
* `birthTimes s τ` (finite); `tendsto_complexObs_right`: the observables of the candidate are
  right-continuous for every `ω` (every-`ω` continuity of `G − gramJ`, `Kc − kJ`; the jumps are
  locally constant from the right).
* Bounds before the stops: Gram coordinates before `σ_L` (`exists_norm_cComp_inl_le`,
  from `TransBound`, on the a.s. feasible set), `𝒦` coordinates before `ρ_M` (by
  `max M 0`, given `Kc 0 = 0` a.s. and no birth at time `0`), time integrals before `σ_L`.
* `IsGramCoordTestedOff`, `IsKCoordTestedOff`; **`IsGramCoordTestedOff.toAt`**,
  **`IsKCoordTestedOff.toAt`**.
* **Hypothesis `CapIdentGramOff`**, **Hypothesis `CapIdentKDoubleOff`**: the identities at good levels, with
  all times off the birth times. **`capIdentGramGood_of_off`**, **`capIdentKDoubleGood_of_off`**,
  `targetCapIdentAll_of_off`, `targetCapCond'_of_off`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal ComplexConjugate

/-!
## Tested identities off a finite set of times (abstract)
-/

section Abstract

variable {Ω : Type*} [MeasurableSpace Ω] {I : Type*}

/-- **Tested increments with all times outside `B`.** -/
def IsTestedMartOff (B : Set ℝ≥0) (Q : Measure Ω) (obs : I → ℝ≥0 → Ω → ℂ)
    (X : ℝ≥0 → Ω → ℂ) : Prop :=
  (∀ t, Integrable (X t) Q) ∧ ∀ s t : ℝ≥0, s ≤ t → s ∉ B → t ∉ B →
    ∀ (m : ℕ) (i : Fin m → I) (u : Fin m → ℝ≥0), (∀ l, u l ≤ s) → (∀ l, u l ∉ B) →
      ∀ φ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
        ∫ ω, φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω) ∂Q = 0

/-- **Tested identities off a finite set of times give all tested identities.** -/
theorem isTestedMart_of_off {Q : Measure Ω} [IsFiniteMeasure Q] {obs : I → ℝ≥0 → Ω → ℂ}
    {X : ℝ≥0 → Ω → ℂ} {B : Set ℝ≥0} (hB : B.Finite) (hobs : ∀ i u, Measurable (obs i u))
    (hrc : ∀ i ω u, Tendsto (fun v => obs i v ω) (𝓝[≥] u) (𝓝 (obs i u ω)))
    (hXc : ∀ ω, Continuous fun t => X t ω)
    (hbd : ∀ t, ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t, ‖X v ω‖ ≤ C)
    (hX : IsTestedMartOff B Q obs X) : IsTestedMart Q obs X := by
  refine ⟨hX.1, fun s t hst m i u hu φ => ?_⟩
  set D : Set ℝ≥0 := ((fun e => s + e) ⁻¹' B ∪ (fun e => t + e) ⁻¹' B) ∪
    ⋃ l, (fun e => u l + e) ⁻¹' B with hD_def
  have hD : D.Finite :=
    ((hB.preimage (add_right_injective s).injOn).union
      (hB.preimage (add_right_injective t).injOn)).union
      (Set.finite_iUnion fun l => hB.preimage (add_right_injective (u l)).injOn)
  set r : ℕ → ℝ≥0 := fun n => (1 / ((n : ℝ) + 1)).toNNReal with hr_def
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h := (continuous_real_toNNReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [Real.toNNReal_zero] at h
  have hrpos : ∀ n, 0 < r n := fun n => Real.toNNReal_pos.2 Nat.one_div_pos_of_nat
  have hr1 : ∀ n, r n ≤ 1 := fun n => by
    refine Real.toNNReal_le_one.2 ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hex : ∀ n : ℕ, ∃ ε : ℝ≥0, ε ∈ Set.Ioo 0 (r n) ∧ ε ∉ D := fun n => by
    obtain ⟨ε, hε⟩ := ((Set.Ioo_infinite (hrpos n)).sdiff hD).nonempty
    exact ⟨ε, hε.1, hε.2⟩
  choose ε hεI hεD using hex
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr0 (fun n => zero_le)
      (fun n => (hεI n).2.le)
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεI n).2.le.trans (hr1 n)
  have hεn : ∀ x : ℝ≥0, Tendsto (fun n => x + ε n) atTop (𝓝 x) := fun x => by
    simpa using (tendsto_const_nhds (x := x)).add hεlim
  have hεw : ∀ x : ℝ≥0, Tendsto (fun n => x + ε n) atTop (𝓝[≥] x) := fun x =>
    tendsto_nhdsWithin_iff.2 ⟨hεn x, Eventually.of_forall fun n =>
      show x ≤ x + ε n from le_self_add⟩
  obtain ⟨C, hC⟩ := hbd (t + 1)
  have hzero : ∀ n, ∫ ω, φ (fun l => obs (i l) (u l + ε n) ω) •
      (X (t + ε n) ω - X (s + ε n) ω) ∂Q = 0 := fun n =>
    hX.2 (s + ε n) (t + ε n) (add_le_add hst le_rfl)
      (fun h => hεD n (Or.inl (Or.inl h))) (fun h => hεD n (Or.inl (Or.inr h))) m i
      (fun l => u l + ε n) (fun l => add_le_add (hu l) le_rfl)
      (fun l h => hεD n (Or.inr (Set.mem_iUnion.2 ⟨l, h⟩))) φ
  have hY : ∀ n, Measurable fun ω (l : Fin m) => obs (i l) (u l + ε n) ω := fun n =>
    Measurable.of_eval fun l => hobs _ _
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q) (fun _ => ‖φ‖ * (C + C))
    (F := fun n ω => φ (fun l => obs (i l) (u l + ε n) ω) • (X (t + ε n) ω - X (s + ε n) ω))
    (f := fun ω => φ (fun l => obs (i l) (u l) ω) • (X t ω - X s ω))
    (fun n => ((φ.continuous.measurable.comp (hY n)).aestronglyMeasurable).smul
      (((hX.1 _).sub (hX.1 _)).aestronglyMeasurable))
    (integrable_const _)
    (fun n => by
      filter_upwards [hC] with ω hω
      rw [norm_smul]
      refine mul_le_mul (φ.norm_coe_le_norm _) ((norm_sub_le _ _).trans
        (add_le_add (hω _ ?_) (hω _ ?_))) (norm_nonneg _) (norm_nonneg _)
      · exact add_le_add le_rfl (hε1 n)
      · exact (add_le_add hst le_rfl).trans (add_le_add le_rfl (hε1 n)))
    (Eventually.of_forall fun ω => by
      have h1 : Tendsto (fun n => fun l => obs (i l) (u l + ε n) ω) atTop
          (𝓝 fun l => obs (i l) (u l) ω) :=
        tendsto_pi_nhds.2 fun l => (hrc (i l) ω (u l)).comp (hεw (u l))
      have h2 := (φ.continuous.tendsto _).comp h1
      have h3 : Tendsto (fun n => X (t + ε n) ω - X (s + ε n) ω) atTop (𝓝 (X t ω - X s ω)) :=
        (((hXc ω).tendsto t).comp (hεn t)).sub (((hXc ω).tendsto s).comp (hεn s))
      exact h2.smul h3)
  exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)

omit [MeasurableSpace Ω] in
/-- A stopped process is bounded on `[0, t]` where the process is bounded before the stop. -/
theorem norm_stoppedProcess_le {X : ℝ≥0 → Ω → ℂ} {σ : Ω → WithTop ℝ≥0} {t : ℝ≥0} {C : ℝ}
    {ω : Ω} (h : ∀ v ≤ t, (v : WithTop ℝ≥0) ≤ σ ω → ‖X v ω‖ ≤ C) :
    ∀ v ≤ t, ‖stoppedProcess X σ v ω‖ ≤ C := fun v hv => by
  obtain ⟨w, hwv, hwσ, he⟩ := exists_stoppedProcess_eq X σ v ω
  rw [he]
  exact h w (hwv.trans hv) hwσ

omit [MeasurableSpace Ω] in
theorem norm_br_le {A B D : ℂ} {C1 C2 C3 : ℝ} (h1 : ‖A‖ ≤ C1) (h2 : ‖B‖ ≤ C2) (h3 : ‖D‖ ≤ C3) :
    ‖A * B - D‖ ≤ C1 * C2 + C3 :=
  (norm_sub_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
    (mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1))) h3)

end Abstract

/-!
## The candidate: birth times, right-continuity, bounds
-/

variable {Ω : Type*} {K np : ℕ} {b E s : ℝ} {τ m : Fin np → ℝ}
  {tseq : Ω → ℕ → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
  {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

/-- The model birth times `{u | s + u = τ_j for some j}`. -/
def birthTimes (s : ℝ) (τ : Fin np → ℝ) : Set ℝ≥0 := {u | ∃ j, s + (u : ℝ) = τ j}

theorem birthTimes_finite (s : ℝ) (τ : Fin np → ℝ) : (birthTimes s τ).Finite :=
  (Set.finite_range fun j => (τ j - s).toNNReal).subset fun u ⟨j, hj⟩ =>
    ⟨j, show (τ j - s).toNNReal = u by rw [← hj, add_sub_cancel_left, Real.toNNReal_coe]⟩

theorem eventually_gramJ_eq (t : ℝ≥0) :
    ∀ᶠ v in 𝓝[≥] t, gramJ (K := K) b s τ m v = gramJ b s τ m t := by
  have hiff : ∀ᶠ v : ℝ≥0 in 𝓝[≥] t, ∀ j, (τ j - s ≤ (v : ℝ) ↔ τ j - s ≤ (t : ℝ)) := by
    rw [eventually_all]
    intro j
    by_cases hj : τ j - s ≤ t
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact ⟨fun _ => hj, fun _ => hj.trans (NNReal.coe_le_coe.2 hv)⟩
    · rw [not_le] at hj
      have h : ∀ᶠ v : ℝ≥0 in 𝓝 t, (v : ℝ) < τ j - s :=
        (NNReal.continuous_coe.tendsto t).eventually (gt_mem_nhds hj)
      filter_upwards [nhdsWithin_le_nhds h] with v hv
      exact ⟨fun h' => absurd h' (not_le.2 hv), fun h' => absurd h' (not_le.2 hj)⟩
  exact hiff.mono fun v hv => by simp only [gramJ, birthJump, hv]

theorem eventually_kJ_eq (t : ℝ≥0) : ∀ᶠ v in 𝓝[≥] t, kJ E s τ m v = kJ E s τ m t := by
  have hiff : ∀ᶠ v : ℝ≥0 in 𝓝[≥] t, ∀ j, (τ j - s ≤ (v : ℝ) ↔ τ j - s ≤ (t : ℝ)) := by
    rw [eventually_all]
    intro j
    by_cases hj : τ j - s ≤ t
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact ⟨fun _ => hj, fun _ => hj.trans (NNReal.coe_le_coe.2 hv)⟩
    · rw [not_le] at hj
      have h : ∀ᶠ v : ℝ≥0 in 𝓝 t, (v : ℝ) < τ j - s :=
        (NNReal.continuous_coe.tendsto t).eventually (gt_mem_nhds hj)
      filter_upwards [nhdsWithin_le_nhds h] with v hv
      exact ⟨fun h' => absurd h' (not_le.2 hv), fun h' => absurd h' (not_le.2 hj)⟩
  exact hiff.mono fun v hv => by simp only [kJ, kBirthJump, hv]

theorem kJ_zero (hτ : ∀ j, s < τ j) : kJ E s τ m 0 = 0 := by
  unfold kJ kBirthJump
  refine Finset.sum_eq_zero fun j _ => ?_
  exact ite_eq_right_iff.2 fun h' => absurd h' (not_le.2 (by
    simp only [NNReal.coe_zero]; linarith [hτ j]))

/-- **The observables of the candidate are right-continuous for every `ω`.** -/
theorem tendsto_complexObs_right (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u) (i : LIdx K np) (ω : Ω)
    (u : ℝ≥0) : Tendsto (fun v => complexObs tseq G Kc i v ω) (𝓝[≥] u)
      (𝓝 (complexObs tseq G Kc i u ω)) := by
  rcases i with e | k | ij
  · have h1 : Tendsto (fun v => G v ω - gramJ b s τ m v) (𝓝[≥] u)
        (𝓝 (G u ω - gramJ b s τ m u)) := ((hc ω).tendsto u).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun v => gramJ (K := K) b s τ m v) (𝓝[≥] u) (𝓝 (gramJ b s τ m u)) :=
      tendsto_const_nhds.congr' ((eventually_gramJ_eq u).mono fun v hv => hv.symm)
    have e1 : (fun v => complexObs tseq G Kc (Sum.inl e) v ω) =
        gramEntry e ∘ fun v => (G v ω - gramJ b s τ m v) + gramJ b s τ m v :=
      funext fun v => by simp only [complexObs, Function.comp, sub_add_cancel]
    have e2 : complexObs tseq G Kc (Sum.inl e) u ω =
        gramEntry e ((G u ω - gramJ b s τ m u) + gramJ b s τ m u) := by
      simp only [complexObs, sub_add_cancel]
    rw [e1, e2]
    exact ((ClosedLimit.continuous_gramEntry e).tendsto _).comp (h1.add h2)
  · exact tendsto_const_nhds
  · have h1 : Tendsto (fun v => Kc v ω - kJ E s τ m v) (𝓝[≥] u)
        (𝓝 (Kc u ω - kJ E s τ m u)) := ((hkc ω).tendsto u).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun v => kJ E s τ m v) (𝓝[≥] u) (𝓝 (kJ E s τ m u)) :=
      tendsto_const_nhds.congr' ((eventually_kJ_eq u).mono fun v hv => hv.symm)
    have e1 : (fun v => complexObs tseq G Kc (Sum.inr (Sum.inr ij)) v ω) =
        (fun A : Matrix (Fin np) (Fin np) ℂ => A ij.1 ij.2) ∘
          fun v => (Kc v ω - kJ E s τ m v) + kJ E s τ m v :=
      funext fun v => by simp only [complexObs, Function.comp, sub_add_cancel]
    have e2 : complexObs tseq G Kc (Sum.inr (Sum.inr ij)) u ω =
        ((Kc u ω - kJ E s τ m u) + kJ E s τ m u) ij.1 ij.2 := by
      simp only [complexObs, sub_add_cancel]
    rw [e1, e2]
    exact ((continuous_id.matrix_elem ij.1 ij.2).tendsto _).comp (h1.add h2)

/-- **The `𝒦` level stop bounds `Σ_ij |(𝒦 − J_𝒦)_ij|` by `max M 0`** on a continuous path
starting at `0`. -/
theorem kLevel_sum_le {ω : Ω} {M : ℝ} (hkc : Continuous fun u => Kc u ω - kJ E s τ m u)
    (h0 : Kc 0 ω - kJ E s τ m 0 = 0) {v : ℝ≥0}
    (hv : (v : WithTop ℝ≥0) ≤ kLevelStop E s τ m Kc M ω) :
    ∑ i, ∑ j, ‖(Kc v ω - kJ E s τ m v) i j‖ ≤ max M 0 := by
  set f : ℝ≥0 → ℝ := fun u => ∑ i, ∑ j, ‖(Kc u ω - kJ E s τ m u) i j‖ with hf_def
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => continuous_norm.comp (hkc.matrix_elem i j)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ v) with h | h
  · subst h
    rw [h0]
    simp
  · refine le_max_of_le_left (not_lt.1 fun hlt => ?_)
    obtain ⟨a, hav, hsub⟩ := exists_Ioc_subset_of_mem_nhds
      (hf.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt)) ⟨0, h⟩
    obtain ⟨w, haw, hwv⟩ := exists_between hav
    have hw : M < f w := hsub ⟨haw, hwv.le⟩
    have hle : kLevelStop E s τ m Kc M ω ≤ w := iInf₂_le w hw.le
    exact absurd (hv.trans hle) (not_le.2 (WithTop.coe_lt_coe.2 hwv))

theorem norm_entry_le_sum (A : Matrix (Fin np) (Fin np) ℂ) (i j : Fin np) :
    ‖A i j‖ ≤ ∑ i, ∑ j, ‖A i j‖ :=
  (Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

section Bounds

variable [MeasurableSpace Ω] {Q : Measure Ω}
  (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
  (hfe : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω))
include hc hfe

theorem ae_bound_cComp_inl (L : ℝ) (t : ℝ≥0)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t,
      (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω → ‖cComp b E s τ m G Kc (Sum.inl e) v ω‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_cComp_inl_le (b := b) (E := E) (s := s) (τ := τ) (m := m)
    (G := G) (Kc := Kc) L t e
  exact ⟨C, hfe.mono fun ω hω => hC ω hω (hc ω)⟩

omit hc in
theorem ae_bound_integral {f : GramState (SrcCol K (Fin np)) → ℂ} (hf : Continuous f) (L : ℝ)
    (t : ℝ≥0) : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t, (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
      ‖∫ u in Set.Ioc (0 : ℝ) v, f (G u.toNNReal ω)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_integral_le (G := G) hf L t
  exact ⟨C, hfe.mono fun ω hω => hC ω hω⟩

/-- **The coordinates are bounded before `σ_L ∧ ρ_M`.** -/
theorem ae_bound_cComp_double (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (hK0 : ∀ᵐ ω ∂Q, Kc 0 ω - kJ E s τ m 0 = 0) (L M : ℝ) (t : ℝ≥0) (c : CIdx K np) :
    ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t,
      (v : WithTop ℝ≥0) ≤ min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω) →
        ‖cComp b E s τ m G Kc c v ω‖ ≤ C := by
  rcases c with e | ij
  · obtain ⟨C, hC⟩ := ae_bound_cComp_inl (E := E) (Kc := Kc) hc hfe L t e
    exact ⟨C, hC.mono fun ω hω v hv hvσ => hω v hv (hvσ.trans (min_le_left _ _))⟩
  · refine ⟨max M 0, hK0.mono fun ω h0 v _ hvσ => ?_⟩
    have hle := kLevel_sum_le (hkc ω) h0 (hvσ.trans (min_le_right _ _))
    rw [cComp_inr]
    simp only [kCompensated, h0, Matrix.zero_apply, sub_zero]
    exact (norm_entry_le_sum _ ij.1 ij.2).trans hle

end Bounds

/-!
## The coordinate identities off the birth times
-/

/-- **The Gram coordinate identities at one stop, all times off `B`.** -/
structure IsGramCoordTestedOff [MeasurableSpace Ω] (B : Set ℝ≥0) (b E s : ℝ) (τ m : Fin np → ℝ)
    (Q : Measure Ω) (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
    IsTestedMartOff B Q (complexObs tseq G Kc)
      (stoppedProcess (cComp b E s τ m G Kc (Sum.inl e)) σ)
  bracket : ∀ e e' : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
    IsTestedMartOff B Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inl e) (Sum.inl e')) σ)

/-- **The `𝒦` coordinate identities at one stop, all times off `B`.** -/
structure IsKCoordTestedOff [MeasurableSpace Ω] (B : Set ℝ≥0) (b E s : ℝ) (τ m : Fin np → ℝ)
    (Q : Measure Ω) (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) (σ : Ω → WithTop ℝ≥0) : Prop where
  drift : ∀ ij : Fin np × Fin np, IsTestedMartOff B Q (complexObs tseq G Kc)
    (stoppedProcess (cComp b E s τ m G Kc (Sum.inr ij)) σ)
  bracketK : ∀ ij kl : Fin np × Fin np, IsTestedMartOff B Q (complexObs tseq G Kc)
    (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inr kl)) σ)
  bracketG : ∀ (ij : Fin np × Fin np) (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)),
    IsTestedMartOff B Q (complexObs tseq G Kc)
      (stoppedProcess (cBr b E s τ m G Kc (Sum.inr ij) (Sum.inl e)) σ)
  conjBr : ∀ ij kl : Fin np × Fin np, IsTestedMartOff B Q (complexObs tseq G Kc)
    (stoppedProcess (kBr b E s τ m G Kc ij kl) σ)

section ToAt

variable [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
  (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
  (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
  (hfe : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω))
include hobs hc hkc hfe

/-- **The Gram identities at `σ_L` from those off the birth times.** -/
theorem IsGramCoordTestedOff.toAt {L : ℝ}
    (h : IsGramCoordTestedOff (birthTimes s τ) b E s τ m Q tseq G Kc (gramTraceStop G L)) :
    IsGramCoordTestedAt b E s τ m Q tseq G Kc (gramTraceStop G L) := by
  have hrc := tendsto_complexObs_right (tseq := tseq) hc hkc
  refine ⟨fun e => isTestedMart_of_off (birthTimes_finite s τ) hobs hrc
    (fun ω => NativeSDE.continuous_stoppedProcess (continuous_cComp hc hkc _ ω) _)
    (fun t => ?_) (h.drift e), fun e e' => isTestedMart_of_off (birthTimes_finite s τ) hobs hrc
    (fun ω => NativeSDE.continuous_stoppedProcess (continuous_cBr hc hkc _ _ ω) _)
    (fun t => ?_) (h.bracket e e')⟩
  · obtain ⟨C, hC⟩ := ae_bound_cComp_inl (E := E) (Kc := Kc) hc hfe L t e
    exact ⟨C, hC.mono fun ω hω => norm_stoppedProcess_le hω⟩
  · obtain ⟨C1, h1⟩ := ae_bound_cComp_inl (E := E) (Kc := Kc) hc hfe L t e
    obtain ⟨C2, h2⟩ := ae_bound_cComp_inl (E := E) (Kc := Kc) hc hfe L t e'
    obtain ⟨C3, h3⟩ := ae_bound_integral (Q := Q) hfe (continuous_cCov (b := b) (E := E)
      (Sum.inl e : CIdx K np) (Sum.inl e')) L t
    refine ⟨C1 * C2 + C3, ?_⟩
    filter_upwards [h1, h2, h3] with ω g1 g2 g3
    exact norm_stoppedProcess_le fun v hv hvσ =>
      norm_br_le (g1 v hv hvσ) (g2 v hv hvσ) (g3 v hv hvσ)

/-- **The `𝒦` identities at `σ_L ∧ ρ_M` from those off the birth times.** -/
theorem IsKCoordTestedOff.toAt (hK0 : ∀ᵐ ω ∂Q, Kc 0 ω - kJ E s τ m 0 = 0) {L M : ℝ}
    (h : IsKCoordTestedOff (birthTimes s τ) b E s τ m Q tseq G Kc
      (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω))) :
    IsKCoordTestedAt b E s τ m Q tseq G Kc
      (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω)) := by
  have hrc := tendsto_complexObs_right (tseq := tseq) hc hkc
  have hB := birthTimes_finite s τ
  have hint : ∀ (f : GramState (SrcCol K (Fin np)) → ℂ), Continuous f → ∀ t : ℝ≥0,
      ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t,
        (v : WithTop ℝ≥0) ≤ min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω) →
          ‖∫ u in Set.Ioc (0 : ℝ) v, f (G u.toNNReal ω)‖ ≤ C := fun f hf t => by
    obtain ⟨C, hC⟩ := ae_bound_integral (Q := Q) hfe hf L t
    exact ⟨C, hC.mono fun ω hω v hv hvσ => hω v hv (hvσ.trans (min_le_left _ _))⟩
  have hbr : ∀ c c' : CIdx K np, ∀ t : ℝ≥0, ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ v ≤ t,
      ‖stoppedProcess (cBr b E s τ m G Kc c c')
        (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω)) v ω‖ ≤ C :=
    fun c c' t => by
      obtain ⟨C1, h1⟩ := ae_bound_cComp_double hc hfe hkc hK0 L M t c
      obtain ⟨C2, h2⟩ := ae_bound_cComp_double hc hfe hkc hK0 L M t c'
      obtain ⟨C3, h3⟩ := hint _ (continuous_cCov (b := b) (E := E) c c') t
      refine ⟨C1 * C2 + C3, ?_⟩
      filter_upwards [h1, h2, h3] with ω g1 g2 g3
      exact norm_stoppedProcess_le fun v hv hvσ =>
        norm_br_le (g1 v hv hvσ) (g2 v hv hvσ) (g3 v hv hvσ)
  refine ⟨fun ij => isTestedMart_of_off hB hobs hrc
      (fun ω => NativeSDE.continuous_stoppedProcess (continuous_cComp hc hkc _ ω) _)
      (fun t => ?_) (h.drift ij),
    fun ij kl => isTestedMart_of_off hB hobs hrc
      (fun ω => NativeSDE.continuous_stoppedProcess (continuous_cBr hc hkc _ _ ω) _)
      (hbr _ _) (h.bracketK ij kl),
    fun ij e => isTestedMart_of_off hB hobs hrc
      (fun ω => NativeSDE.continuous_stoppedProcess (continuous_cBr hc hkc _ _ ω) _)
      (hbr _ _) (h.bracketG ij e),
    fun ij kl => isTestedMart_of_off hB hobs hrc
      (fun ω => NativeSDE.continuous_stoppedProcess (continuous_kBr hc hkc _ _ ω) _)
      (fun t => ?_) (h.conjBr ij kl)⟩
  · obtain ⟨C, hC⟩ := ae_bound_cComp_double hc hfe hkc hK0 L M t (Sum.inr ij)
    exact ⟨C, hC.mono fun ω hω => norm_stoppedProcess_le hω⟩
  · obtain ⟨C1, h1⟩ := ae_bound_cComp_double hc hfe hkc hK0 L M t (Sum.inr ij)
    obtain ⟨C2, h2⟩ := ae_bound_cComp_double hc hfe hkc hK0 L M t (Sum.inr kl)
    obtain ⟨C3, h3⟩ := hint _ (continuous_kConjCov (K := K) (b := b) (E := E) ij kl) t
    refine ⟨C1 * C2 + C3, ?_⟩
    filter_upwards [h1, h2, h3] with ω g1 g2 g3
    exact norm_stoppedProcess_le fun v hv hvσ =>
      norm_br_le (g1 v hv hvσ) (by rw [Complex.norm_conj]; exact g2 v hv hvσ) (g3 v hv hvσ)

end ToAt

/-!
## The hypotheses off the birth times and the reductions
-/

/-- **Hypothesis `CapIdentGramOff`** ( at good levels, off the birth times): under
the premises of `CapIdentGram`, for every good trace level `L`, the Gram coordinate identities at
`σ_L` with all test and increment times off the birth times. -/
def CapIdentGramOff : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    ∀ L : ℝ, IsGoodLevel Q (gramTraceStop G) L →
      IsGramCoordTestedOff (birthTimes s τ) b E s τ m Q tseq G Kc (gramTraceStop G L)

/-- **Hypothesis `CapIdentKDoubleOff`** ( at good levels, off the birth times): under
the premises of `CapIdentKDouble` and the Gram identities, for every good trace level `L` and
good `𝒦` level `M`, the `𝒦` coordinate identities at `σ_L ∧ ρ_M` with all test and increment
times off the birth times. -/
def CapIdentKDoubleOff : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval)
    (φ : ℕ → ℕ) (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
    (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
    CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc →
    IsGramCoordTested b E s τ m Q tseq G Kc (gramTraceStop G) →
    ∀ L M : ℝ, IsGoodLevel Q (gramTraceStop G) L → IsGoodLevel Q (kLevelStop E s τ m Kc) M →
      IsKCoordTestedOff (birthTimes s τ) b E s τ m Q tseq G Kc
        (fun ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω))

/-- **The Gram good-level hypothesis from the hypothesis off the birth times.** -/
theorem capIdentGramGood_of_off (hpin : CapIdentGramOff) : CapIdentGramGood := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP L hgood
  have hoff := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP L
    hgood
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, hfdd⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, -, hh0, -, -⟩ := id hD
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  exact hoff.toAt hobs hc hkc hfe

/-- **The `𝒦` good-level hypothesis from the hypothesis off the birth times.** -/
theorem capIdentKDoubleGood_of_off (hpin : CapIdentKDoubleOff) : CapIdentKDoubleGood := by
  intro hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr L M hgL hgM
  have hoff := hpin hTL hS hT hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP hGr
    L M hgL hgM
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, hc, hkc⟩, hfdd⟩ := hP
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, hs, hτ, hh0, -, -⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  have hcap := hφ.eventually (eventually_capProb_ne_zero hTL hb0 hb hE1 hE2 hlim hs hh0 hA hne)
  have hfe := ae_feasible_all hD hφ hfdd hobs hcap hc
  have hK0 : ∀ᵐ ω ∂Q, Kc 0 ω - kJ E s τ m 0 = 0 :=
    (ae_kc_zero hb1 hE1 hE2 hτ hfdd hobs hcap).mono fun ω hω => by rw [hω, kJ_zero hτ, sub_zero]
  exact hoff.toAt hobs hc hkc hfe hK0

/-- **`TargetCapIdentAll` from the entrance, the two hypotheses off the birth times and the `𝒦`
stop.** -/
theorem targetCapIdentAll_of_off (hEnt : CapIdentEntrance) (hGr : CapIdentGramOff)
    (hKD : CapIdentKDoubleOff) (hKS : CapIdentKStop) : TargetCapIdentAll :=
  targetCapIdentAll_of_good hEnt (capIdentGramGood_of_off hGr) (capIdentKDoubleGood_of_off hKD)
    hKS

/-- **`TargetCapCond'` from the entrance, the two hypotheses off the birth times and the `𝒦` stop.** -/
theorem targetCapCond'_of_off (hEnt : CapIdentEntrance) (hGr : CapIdentGramOff)
    (hKD : CapIdentKDoubleOff) (hKS : CapIdentKStop) : TargetCapCond' :=
  targetCapCond'_of_good hEnt (capIdentGramGood_of_off hGr) (capIdentKDoubleGood_of_off hKD) hKS

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram
