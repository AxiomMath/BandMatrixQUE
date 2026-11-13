module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2Coord
public import BlockBand.SourceProcess.ModelExist.TransBound
public import BlockBand.SourceProcess.ComplexUnique.Coeffs
public import BlockBand.SourceProcess.ClosedLimit.PathInt

/-!
# The `𝒦` stop

`𝒦` is not bounded by the Gram trace, so the products in the `𝒦` clauses (`𝒦·𝒦`, `𝒦·\bar𝒦`,
`𝒦·G`) are not bounded before the Gram trace stop `σ_L`. At finite `W` the summed conditional
errors of `ComplexClosedSummed` are only `L¹`-small, so a product `𝒦_j · (drift error)_j` is
controlled only where `𝒦` is bounded: the `𝒦` clauses are naturally obtained **doubly
stopped**, at `σ_L ∧ ρ_M` with the `𝒦` level stop `ρ_M`. This file removes `ρ_M` in the limit
model, with a domination of `|𝒦|²` before `σ_L` (the limit form of the `𝒦` stop
`ComplexKStoppedMomentMax`).

Measure: an arbitrary `Q` on `Ω`; no filtration.

* `kLevelStop E s τ m Kc M`: the first time `Σ_ij |(𝒦 − J_𝒦)_ij| ≥ M`;
  `eventually_lt_kLevelStop`: for continuous `𝒦 − J_𝒦`, every `t` is eventually before it.
* `exists_stoppedProcess_eq`: a stopped value is a value at some `v ≤ t`, `v ≤ τ`.
* **`isTestedMart_of_removal`** (abstract): tested identities stopped at `σ ∧ ρ_M` for every `M`,
  with `ρ_M → ∞` pointwise and an integrable domination of `X` on `[0, t] ∩ [0, σ]`, give the
  tested identities stopped at `σ`.
* `IsKStopDominated`: for every level `L`, horizon `t` and entry `ij`, `|𝒦_ij(v) − 𝒦_ij(0)|²`
  (births removed) is dominated on `v ≤ t ∧ σ_L` by an integrable function.
* Path bounds before the trace stop (`ModelExist.TransBound`): `exists_norm_gramJ_le`,
  `exists_norm_cComp_inl_le`, `exists_norm_integral_le`.
* **`isKCoordTested_of_double`**: with every-`ω` continuity, a.s. feasibility and
  `IsKStopDominated`, the doubly stopped `𝒦` coordinate identities (every `M`) give the `𝒦`
  coordinate identities at `σ_L`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open scoped NNReal ComplexConjugate

variable {Ω : Type*} {K np : ℕ}

/-!
## The `𝒦` level stop
-/

/-- **The `𝒦` level stop**: the first time `Σ_ij |(𝒦 − J_𝒦)_ij| ≥ M`. -/
def kLevelStop (E s : ℝ) (τ m : Fin np → ℝ) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ)
    (M : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : M ≤ ∑ i, ∑ j, ‖(Kc t ω - kJ E s τ m t) i j‖), (t : WithTop ℝ≥0)

theorem eventually_lt_kLevelStop {E s : ℝ} {τ m : Fin np → ℝ}
    {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ} {ω : Ω}
    (hkc : Continuous fun u => Kc u ω - kJ E s τ m u) (t : ℝ≥0) :
    ∀ᶠ M : ℕ in atTop, (t : WithTop ℝ≥0) < kLevelStop E s τ m Kc M ω := by
  set f : ℝ≥0 → ℝ := fun u => ∑ i, ∑ j, ‖(Kc u ω - kJ E s τ m u) i j‖
  have hf : Continuous f := continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => continuous_norm.comp (hkc.matrix_elem i j)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t + 1)).exists_bound_of_continuousOn
    hf.continuousOn
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop B] with M hM
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one t)) (le_iInf₂ fun u hu => ?_)
  refine WithTop.coe_le_coe.2 (le_of_not_gt fun hlt => ?_)
  have h1 := hB u ⟨bot_le, hlt.le⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : (M : ℝ) ≤ f u := hu
  linarith [le_abs_self (f u)]

/-!
## Removing a stop in the limit
-/

theorem exists_stoppedProcess_eq {β : Type*} (X : ℝ≥0 → Ω → β) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0)
    (ω : Ω) : ∃ v : ℝ≥0, v ≤ t ∧ (v : WithTop ℝ≥0) ≤ τ ω ∧ stoppedProcess X τ t ω = X v ω := by
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left (t : WithTop ℝ≥0) (τ ω)))
  refine ⟨v, WithTop.coe_le_coe.1 ?_, ?_, ?_⟩
  · rw [hv]; exact min_le_left _ _
  · rw [hv]; exact min_le_right _ _
  · simp only [stoppedProcess, ← hv]
    rfl

theorem stoppedProcess_min_eq {β : Type*} (X : ℝ≥0 → Ω → β) (σ ρ : Ω → WithTop ℝ≥0)
    {t : ℝ≥0} {ω : Ω} (h : (t : WithTop ℝ≥0) < ρ ω) :
    stoppedProcess X (fun ω => min (σ ω) (ρ ω)) t ω = stoppedProcess X σ t ω := by
  have e : min (t : WithTop ℝ≥0) (min (σ ω) (ρ ω)) = min (t : WithTop ℝ≥0) (σ ω) := by
    rw [← min_assoc]
    exact min_eq_left ((min_le_left _ _).trans h.le)
  simp only [stoppedProcess, e]

/-- **Removal of a stop in tested identities** (abstract). -/
theorem isTestedMart_of_removal [MeasurableSpace Ω] {I : Type*} {Q : Measure Ω}
    {obs : I → ℝ≥0 → Ω → ℂ} (hobs : ∀ i u, Measurable (obs i u)) {X : ℝ≥0 → Ω → ℂ}
    {σ : Ω → WithTop ℝ≥0} {ρ : ℕ → Ω → WithTop ℝ≥0}
    (hρ : ∀ ω (t : ℝ≥0), ∀ᶠ M in atTop, (t : WithTop ℝ≥0) < ρ M ω)
    (hX : ∀ M, IsTestedMart Q obs (stoppedProcess X fun ω => min (σ ω) (ρ M ω)))
    (hdom : ∀ t, ∃ g : Ω → ℝ, Integrable g Q ∧ ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ t →
      (v : WithTop ℝ≥0) ≤ σ ω → ‖X v ω‖ ≤ g ω) :
    IsTestedMart Q obs (stoppedProcess X σ) := by
  set XM : ℕ → ℝ≥0 → Ω → ℂ := fun M => stoppedProcess X fun ω => min (σ ω) (ρ M ω)
  have hconv : ∀ t ω, ∀ᶠ M in atTop, XM M t ω = stoppedProcess X σ t ω := fun t ω =>
    (hρ ω t).mono fun M hM => stoppedProcess_min_eq X σ (ρ M) hM
  have hbd : ∀ t, ∃ g : Ω → ℝ, Integrable g Q ∧ ∀ᵐ ω ∂Q,
      (∀ M, ‖XM M t ω‖ ≤ g ω) ∧ ‖stoppedProcess X σ t ω‖ ≤ g ω := fun t => by
    obtain ⟨g, hg, hgb⟩ := hdom t
    refine ⟨g, hg, hgb.mono fun ω hω => ⟨fun M => ?_, ?_⟩⟩
    · obtain ⟨v, hvt, hvσ, he⟩ := exists_stoppedProcess_eq X (fun ω => min (σ ω) (ρ M ω)) t ω
      rw [show XM M t ω = _ from he]
      exact hω v hvt (hvσ.trans (min_le_left _ _))
    · obtain ⟨v, hvt, hvσ, he⟩ := exists_stoppedProcess_eq X σ t ω
      rw [he]
      exact hω v hvt hvσ
  have hmeas : ∀ t, AEStronglyMeasurable (stoppedProcess X σ t) Q := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun M => ((hX M).1 t).aestronglyMeasurable)
      (ae_of_all _ fun ω => tendsto_nhds_of_eventually_eq (hconv t ω))
  have hint : ∀ t, Integrable (stoppedProcess X σ t) Q := fun t => by
    obtain ⟨g, hg, hgb⟩ := hbd t
    exact hg.mono' (hmeas t) (hgb.mono fun ω hω => hω.2)
  refine ⟨hint, fun s t hst k i u hu φ => ?_⟩
  obtain ⟨gs, hgs, hgsb⟩ := hbd s
  obtain ⟨gt, hgt, hgtb⟩ := hbd t
  have hY : Measurable fun ω (l : Fin k) => obs (i l) (u l) ω :=
    Measurable.of_eval fun l => hobs (i l) (u l)
  have hφm : AEStronglyMeasurable (fun ω => φ (fun l => obs (i l) (u l) ω)) Q :=
    (φ.continuous.measurable.comp hY).aestronglyMeasurable
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (fun ω => ‖φ‖ * (gt ω + gs ω))
    (F := fun M ω => φ (fun l => obs (i l) (u l) ω) • (XM M t ω - XM M s ω))
    (f := fun ω => φ (fun l => obs (i l) (u l) ω) •
      (stoppedProcess X σ t ω - stoppedProcess X σ s ω))
    (fun M => hφm.smul ((((hX M).1 t).sub ((hX M).1 s)).aestronglyMeasurable))
    ((hgt.add hgs).const_mul _)
    (fun M => (hgtb.and hgsb).mono fun ω hω => by
      rw [norm_smul]
      refine mul_le_mul (φ.norm_coe_le_norm _) ((norm_sub_le _ _).trans
        (add_le_add (hω.1.1 M) (hω.2.1 M))) (norm_nonneg _) (norm_nonneg _))
    (ae_of_all _ fun ω => tendsto_nhds_of_eventually_eq
      (((hconv t ω).and (hconv s ω)).mono fun M hM => by simp only [hM.1, hM.2]))
  have h0 : (fun M => ∫ ω, φ (fun l => obs (i l) (u l) ω) • (XM M t ω - XM M s ω) ∂Q) =
      fun _ => 0 := funext fun M => (hX M).2 s t hst k i u hu φ
  rw [h0] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

/-!
## The `𝒦` stop in the limit model
-/

/-- **The limit form of the `𝒦` stop**: for every trace level `L`, horizon `t` and entry `ij`,
the square of the births-removed `𝒦_ij(v) − 𝒦_ij(0)` is dominated, for `v ≤ t` and `v ≤ σ_L`,
by an integrable function. -/
def IsKStopDominated [MeasurableSpace Ω] (E s : ℝ) (τ m : Fin np → ℝ) (Q : Measure Ω)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))) (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) :
    Prop :=
  ∀ (L : ℝ) (t : ℝ≥0) (ij : Fin np × Fin np), ∃ g : Ω → ℝ, Integrable g Q ∧ ∀ᵐ ω ∂Q,
    ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
      ‖kCompensated Kc (fun t _ => kJ E s τ m t) ij.1 ij.2 v ω‖ ^ 2 ≤ g ω

/-!
## Gram path bounds before the trace stop
-/

theorem gramJ_eq_sel (b s : ℝ) (τ m : Fin np → ℝ) (t : ℝ≥0) :
    gramJ (K := K) b s τ m t = ∑ j, if decide (τ j - s ≤ (t : ℝ)) then
      ((((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1,
        ((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1) :
          GramState (SrcCol K (Fin np))) else 0 := by
  simp only [gramJ, birthJump, decide_eq_true_eq]

/-- The Gram birth jumps are bounded. -/
theorem exists_norm_gramJ_le (b s : ℝ) (τ m : Fin np → ℝ) :
    ∃ CJ : ℝ, ∀ t e, ‖gramEntry e (gramJ (K := K) b s τ m t)‖ ≤ CJ := by
  set F : (Fin np → Bool) → GramState (SrcCol K (Fin np)) := fun x => ∑ j, if x j then
    ((((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1,
      ((dStar b * m j : ℝ) : ℂ) • Matrix.single (Sum.inr j) (Sum.inr j) 1) :
        GramState (SrcCol K (Fin np))) else 0
  refine ⟨∑ x : Fin np → Bool, ∑ e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np),
    ‖gramEntry e (F x)‖, fun t e => ?_⟩
  have e1 : gramJ (K := K) b s τ m t = F fun j => decide (τ j - s ≤ (t : ℝ)) :=
    gramJ_eq_sel b s τ m t
  rw [e1]
  refine le_trans ?_ (Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _) (Finset.mem_univ (fun j => decide (τ j - s ≤ (t : ℝ)))))
  exact Finset.single_le_sum (f := fun e => ‖gramEntry e (F fun j => decide (τ j - s ≤ (t : ℝ)))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ e)

variable {b E s : ℝ} {τ m : Fin np → ℝ} {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))}
  {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

theorem gramTraceStop_eq_pathStop (L : ℝ) (ω : Ω) :
    gramTraceStop G L ω = ModelExist.pathStop (fun t => G t ω) L := rfl

/-- A bound on the time integral of a continuous function of the Gram state before the stop. -/
theorem exists_norm_integral_le {φ : GramState (SrcCol K (Fin np)) → ℂ} (hφ : Continuous φ)
    (L : ℝ) (t : ℝ≥0) : ∃ C : ℝ, ∀ ω, (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) →
      ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
        ‖∫ u in Set.Ioc (0 : ℝ) v, φ (G u.toNNReal ω)‖ ≤ C := by
  obtain ⟨C, hC⟩ := ModelExist.exists_bound_box hφ (2 * |L|)
  refine ⟨|C| * t, fun ω hf v hvt hvσ => ?_⟩
  have h := ModelExist.norm_integral_le_stop (G := fun u => G u ω) (K := L) hf hC hvσ
  refine h.trans ?_
  have hv : (v : ℝ) ≤ t := NNReal.coe_le_coe.2 hvt
  calc C * v ≤ |C| * v := mul_le_mul_of_nonneg_right (le_abs_self C) v.2
    _ ≤ |C| * t := mul_le_mul_of_nonneg_left hv (abs_nonneg C)

/-- A bound on a compensated Gram coordinate before the stop. -/
theorem exists_norm_cComp_inl_le (L : ℝ) (t : ℝ≥0)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) : ∃ C : ℝ, ∀ ω,
      (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) →
      Continuous (fun u => G u ω - gramJ b s τ m u) →
      ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
        ‖cComp b E s τ m G Kc (Sum.inl e) v ω‖ ≤ C := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  obtain ⟨Ci, hCi⟩ := exists_norm_integral_le (G := G) (K := K)
    (ClosedLimit.continuous_gramDriftEntry (transportD0 b E) (srcSignature K (Fin np)) e) L t
  refine ⟨2 * (2 * |L| + CJ) + Ci, fun ω hf hc v hvt hvσ => ?_⟩
  have hCJ0 : 0 ≤ CJ := (norm_nonneg _).trans (hCJ 0 e)
  have hCi0 : 0 ≤ Ci := (norm_nonneg _).trans (hCi ω hf 0 bot_le (by
    rw [WithTop.coe_zero]; exact bot_le))
  rcases eq_zero_or_pos v with h0 | h0
  · subst h0
    simp only [cComp, cEntry, sub_self, NNReal.coe_zero, Set.Ioc_self, Measure.restrict_empty,
      integral_zero_measure, norm_zero]
    positivity
  have hσ : (0 : WithTop ℝ≥0) < gramTraceStop G L ω :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.2 h0) hvσ
  have h1 := ModelExist.norm_sub_le_stop (G := fun u => G u ω) (J := gramJ b s τ m) hf hc hCJ
    hσ hvσ e
  have h2 := ModelExist.norm_sub_le_stop (G := fun u => G u ω) (J := gramJ b s τ m) hf hc hCJ
    hσ (u := 0) (by rw [WithTop.coe_zero]; exact hσ.le) e
  have h3 := hCi ω hf v hvt hvσ
  simp only [cComp, cEntry]
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2) |>.trans ?_) h3
  linarith

/-!
## The doubly stopped `𝒦` identities give the `𝒦` identities at the trace stop
-/

theorem norm_mul_le_sq_add_sq (x y : ℂ) : ‖x * y‖ ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_mul]
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

theorem norm_le_sq_add_one (x : ℂ) : ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- **The `𝒦` coordinate identities at the trace stops from the doubly stopped ones.** -/
theorem isKCoordTested_of_double [MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
    {tseq : Ω → ℕ → ℝ}
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (hfe : ∀ᵐ ω ∂Q, ∀ t, GramFeasible (srcSignature K (Fin np)) (G t ω))
    (hD : ∀ M : ℕ, IsKCoordTested b E s τ m Q tseq G Kc
      (fun L ω => min (gramTraceStop G L ω) (kLevelStop E s τ m Kc M ω)))
    (hK : IsKStopDominated E s τ m Q G Kc) :
    IsKCoordTested b E s τ m Q tseq G Kc (gramTraceStop G) := by
  have hρ : ∀ ω (t : ℝ≥0), ∀ᶠ M : ℕ in atTop, (t : WithTop ℝ≥0) < kLevelStop E s τ m Kc M ω :=
    fun ω t => eventually_lt_kLevelStop (hkc ω) t
  have hK' : ∀ (L : ℝ) (t : ℝ≥0) (ij : Fin np × Fin np), ∃ g : Ω → ℝ, Integrable g Q ∧
      ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, v ≤ t → (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω →
        ‖cComp b E s τ m G Kc (Sum.inr ij) v ω‖ ^ 2 ≤ g ω := fun L t ij => by
    obtain ⟨g, hg, hgb⟩ := hK L t ij
    exact ⟨g, hg, hgb.mono fun ω hω v hvt hvσ => by rw [cComp_inr]; exact hω v hvt hvσ⟩
  refine ⟨fun L ij => ?_, fun L ij kl => ?_, fun L ij e => ?_, fun L ij kl => ?_⟩
  · refine isTestedMart_of_removal hobs hρ (fun M => (hD M).drift L ij) fun t => ?_
    obtain ⟨g, hg, hgb⟩ := hK' L t ij
    refine ⟨fun ω => g ω + 1, hg.add (integrable_const _), hgb.mono fun ω hω v hvt hvσ => ?_⟩
    exact (norm_le_sq_add_one _).trans (by linarith [hω v hvt hvσ])
  · refine isTestedMart_of_removal hobs hρ (fun M => (hD M).bracketK L ij kl) fun t => ?_
    obtain ⟨g, hg, hgb⟩ := hK' L t ij
    obtain ⟨g', hg', hgb'⟩ := hK' L t kl
    refine ⟨fun ω => g ω + g' ω, hg.add hg', (hgb.and hgb').mono fun ω hω v hvt hvσ => ?_⟩
    simp only [cBr, cCov, MeasureTheory.integral_zero, sub_zero]
    exact (norm_mul_le_sq_add_sq _ _).trans (add_le_add (hω.1 v hvt hvσ) (hω.2 v hvt hvσ))
  · refine isTestedMart_of_removal hobs hρ (fun M => (hD M).bracketG L ij e) fun t => ?_
    obtain ⟨g, hg, hgb⟩ := hK' L t ij
    obtain ⟨C1, hC1⟩ := exists_norm_cComp_inl_le (G := G) (Kc := Kc) (E := E) L t e
    have hcov : Continuous fun H : GramState (SrcCol K (Fin np)) =>
        cCov b E (Sum.inr ij : CIdx K np) (Sum.inl e) H := by
      change Continuous fun H : GramState (SrcCol K (Fin np)) => kGramCov b E ij e H
      unfold kGramCov
      split_ifs
      · exact continuous_const.mul ((continuous_snd.matrix_elem _ _)) |>.mul
          (ComplexUnique.continuous_gramC0_entry _ _ _)
      · exact continuous_const.mul ((continuous_snd.matrix_elem _ _)) |>.mul
          (ComplexUnique.continuous_gramC1H_entry _ _ _)
    obtain ⟨C2, hC2⟩ := exists_norm_integral_le (G := G) hcov L t
    refine ⟨fun ω => (g ω + 1) * |C1| + |C2|, (hg.add (integrable_const _)).mul_const _ |>.add
      (integrable_const _), (hgb.and hfe).mono fun ω hω v hvt hvσ => ?_⟩
    simp only [cBr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ((hC2 ω hω.2 v hvt hvσ).trans (le_abs_self _)))
    rw [norm_mul]
    refine mul_le_mul ((norm_le_sq_add_one _).trans (by linarith [hω.1 v hvt hvσ]))
      ((hC1 ω hω.2 (hc ω) v hvt hvσ).trans (le_abs_self _)) (norm_nonneg _) ?_
    linarith [hω.1 v hvt hvσ, sq_nonneg ‖cComp b E s τ m G Kc (Sum.inr ij) v ω‖,
      (sq_nonneg ‖cComp b E s τ m G Kc (Sum.inr ij) v ω‖).trans (hω.1 v hvt hvσ)]
  · refine isTestedMart_of_removal hobs hρ (fun M => (hD M).conjBr L ij kl) fun t => ?_
    obtain ⟨g, hg, hgb⟩ := hK' L t ij
    obtain ⟨g', hg', hgb'⟩ := hK' L t kl
    have hcov : Continuous fun H : GramState (SrcCol K (Fin np)) => kConjCov b E ij kl H := by
      unfold kConjCov
      exact continuous_const.mul ((continuous_snd.matrix_elem _ _)) |>.mul
        (ComplexUnique.continuous_gramC0_entry _ _ _)
    obtain ⟨C2, hC2⟩ := exists_norm_integral_le (G := G) hcov L t
    refine ⟨fun ω => g ω + g' ω + |C2|, (hg.add hg').add (integrable_const _),
      ((hgb.and hgb').and hfe).mono fun ω hω v hvt hvσ => ?_⟩
    simp only [kBr]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ((hC2 ω hω.2 v hvt hvσ).trans (le_abs_self _)))
    refine (norm_mul_le_sq_add_sq _ _).trans ?_
    rw [Complex.norm_conj]
    exact add_le_add (hω.1.1 v hvt hvσ) (hω.1.2 v hvt hvσ)

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
