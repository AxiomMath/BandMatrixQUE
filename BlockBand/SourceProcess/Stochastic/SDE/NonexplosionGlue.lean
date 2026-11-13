module
public import BlockBand.SourceProcess.Stochastic.SDE.NonexplosionLocalize
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gluing exit-time solutions into a global solution

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

`exists_isSDESolution_of_family`: let `X^n` be strong exit-time solutions of radius `n`
(`IsStrongExitSolution`, from `exists_solutionUntil_exitTime_strong`) and suppose that almost
surely every time precedes some exit time `e_n = exit_n(X^n)`. Then a global solution exists.

Construction. By radius consistency (`IsStrongExitSolution.ae_consistent`) there is a
measurable full set `G` on which `e_n` is nondecreasing, `X^n = X^m` on `[0, e_n]` (`n ≤ m`),
and every `t` is before some `e_n`. On `G` set `X_t = X^N_t` with `N` the first index with
`t < e_N`, and `X_t = ξ` off `G`. Then `X = X^n` on `[0, e_n]` on `G`; `X` is the pointwise limit
of `F_t ∨ N`-measurable maps, has everywhere continuous paths and `X_0 = ξ`. Its localizing
sequence is `e_n`; the identity at `τ ∧ e_n` is that of `X^n` (`StoppedIdentity.congr_stopped`)
and passes to `τ` by `identity_of_localizing`.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Gluing**: a consistent escaping family of exit-time solutions gives a global solution. -/
theorem exists_isSDESolution_of_family {b : E → E} {σ : κ → E → E} (hb : LocallyLipschitz b)
    (hσ : ∀ a, LocallyLipschitz (σ a)) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ)
    {X : ℕ → ℝ≥0 → DriverSample S κ → E} (hX : ∀ n : ℕ, IsStrongExitSolution μ b σ ξ n (X n))
    (hesc : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℕ, ∃ n : ℕ,
      ((T : ℝ≥0) : WithTop ℝ≥0) < exitTime (X n) n x) :
    ∃ Y : ℝ≥0 → DriverSample S κ → E, IsSDESolution μ b σ ξ Y := by
  classical
  set e : ℕ → DriverSample S κ → WithTop ℝ≥0 := fun n => exitTime (X n) n with hedef
  have hcons : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ n m : ℕ, n ≤ m → e n x ≤ e m x ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ e n x → X n t x = X m t x := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [(hX n).ae_consistent hb hσ (Nat.cast_le.2 hnm) (hX m)] with x hx _
      exact ⟨hx.2.1, hx.2.2⟩
    · exact Eventually.of_forall fun x h => absurd h hnm
  obtain ⟨G, hGm, hG0, hG⟩ := exists_good_set μ (hcons.and hesc)
  have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  have hex : ∀ x ∈ G, ∀ t : ℝ≥0, ∃ n, (t : WithTop ℝ≥0) < e n x := fun x hx t => by
    obtain ⟨n, hn⟩ := (hG x hx).2 ⌈t⌉₊
    exact ⟨n, lt_of_le_of_lt (WithTop.coe_le_coe.2 (Nat.le_ceil t)) hn⟩
  have hev : ∀ x ∈ G, ∀ t : ℝ≥0, ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < e n x := fun x hx t => by
    obtain ⟨n₀, hn₀⟩ := hex x hx t
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact hn₀.trans_le ((hG x hx).1 n₀ n hn).1
  set N : ℝ≥0 → DriverSample S κ → ℕ := fun t x =>
    if h : x ∈ G then Nat.find (hex x h t) else 0 with hNdef
  set Y : ℝ≥0 → DriverSample S κ → E := fun t x => if x ∈ G then X (N t x) t x else ξ x
    with hYdef
  have hkey : ∀ x ∈ G, ∀ (n : ℕ) (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ e n x → Y t x = X n t x := by
    intro x hx n t ht
    have hN : N t x = Nat.find (hex x hx t) := by simp only [N, hx, dite_true]
    have hNs : (t : WithTop ℝ≥0) < e (N t x) x := hN ▸ Nat.find_spec (hex x hx t)
    simp only [Y, hx, ite_true]
    rcases le_total n (N t x) with h | h
    · exact (((hG x hx).1 n _ h).2 t ht).symm
    · exact ((hG x hx).1 _ n h).2 t hNs.le
  have hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t) := fun t => by
    refine stronglyMeasurable_of_tendsto (f := fun n => G.piecewise (X n t) ξ) atTop
      (fun n => StronglyMeasurable.piecewise (measurableSet_aug_of_full μ hGm hG0 t)
        ((hX n).sol.1.adapted t) (hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le)))
      (tendsto_pi_nhds.2 fun x => ?_)
    by_cases hx : x ∈ G
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x hx t] with n hn
      rw [Set.piecewise_eq_of_mem _ _ _ hx, hkey x hx n t hn.le]
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hx, Y, hx, ite_false]
      exact tendsto_const_nhds
  have hYc : ∀ x, Continuous fun t => Y t x := fun x => by
    by_cases hx : x ∈ G
    · refine continuous_iff_continuousAt.2 fun t₀ => ?_
      obtain ⟨n, hn⟩ := hex x hx t₀
      refine ((hX n).continuous x).continuousAt.congr ?_
      filter_upwards [(isOpen_lt WithTop.continuous_coe continuous_const).mem_nhds hn] with t ht
      exact (hkey x hx n t (le_of_lt ht)).symm
    · have : (fun t => Y t x) = fun _ => ξ x := funext fun t => by simp only [Y, hx, ite_false]
      rw [this]
      exact continuous_const
  have hY0 : ∀ x, Y 0 x = ξ x := fun x => by
    by_cases hx : x ∈ G
    · rw [hkey x hx 0 0 (by rw [WithTop.coe_zero]; exact zero_le), (hX 0).init x]
    · simp only [Y, hx, ite_false]
  have hYprog : IsStronglyProgressive (driverAugmented (κ := κ) μ) Y :=
    StronglyAdapted.isStronglyProgressive_of_continuous hYa hYc
  have hetop : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => e n x) atTop (𝓝 ⊤) := by
    filter_upwards [hGae] with x hx
    exact (WithTop.tendsto_nhds_top_iff _).2 fun i => hev x hx i
  have hsw : ∀ (n : ℕ) {τ : DriverSample S κ → WithTop ℝ≥0},
      IsStoppingTime (driverAugmented (κ := κ) μ) τ → ∀ (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ fun a =>
        switchOff (e n) fun t x => σ a (X n t x))) := fun n τ hτ ℓ T =>
    nativeIntegrand_switched hb hσ (hX n).sol.1.adapted
      (Eventually.of_forall (hX n).continuous) (hX n).continuous
      (Eventually.of_forall fun _ _ => rfl) (hX n).stopping hτ ℓ T
  refine ⟨Y, ⟨hYa, hYprog, Eventually.of_forall hYc,
    isStronglyProgressive_switchOff isStoppingTime_top fun i =>
      hb.continuous.comp_stronglyMeasurable (hYprog i),
    fun a => isStronglyProgressive_switchOff isStoppingTime_top fun i =>
      (hσ a).continuous.comp_stronglyMeasurable (hYprog i), ?_,
    ⟨e, fun n => (hX n).stopping, hetop, fun n ℓ T => ?_⟩, ?_⟩, Eventually.of_forall hY0⟩
  · -- drift integrability: continuous paths
    refine Eventually.of_forall fun x t => ?_
    have he : (fun s : ℝ => switchOff (fun _ => (⊤ : WithTop ℝ≥0)) (fun t x => b (Y t x))
        s.toNNReal x) = fun s : ℝ => b (Y s.toNNReal x) :=
      funext fun s => ite_eq_left le_top
    rw [he]
    exact (hb.continuous.comp ((hYc x).comp continuous_real_toNNReal)).integrableOn_Ioc
  · -- localizing integrands
    refine NativeIntegrand.congr (hsw n (hX n).stopping ℓ T) fun a => ?_
    filter_upwards [ae_timeProb_of_ae (T := T) hGae] with p hp
    simp only [stopIntegrand, functionalIntegrand, switchOff, le_top, ite_true]
    by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ e n p.2
    · have h1' : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime (X n) n p.2 := h1
      simp only [h1, h1', ite_true, hkey p.2 hp n _ h1]
    · have h1' : ¬ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime (X n) n p.2 := h1
      simp only [h1, h1', ite_false, map_zero]
  · -- the identity, by localization at `τ ∧ e_n`
    intro ℓ τ hτ T hint t ht
    refine identity_of_localizing hetop (fun n => ?_) ℓ hint t ht
    have hτn := hτ.min (hX n).stopping
    refine StoppedIdentity.congr_stopped ?_ ?_ (IsNativeItoProcess.stoppedIdentity (hX n).sol.1
      hτn T fun ℓ => hsw n hτn ℓ T)
    · filter_upwards [hGae] with x hx s hs
      exact hkey x hx n s (hs.trans (min_le_right _ _))
    · filter_upwards [hGae] with x hx s _ hs
      have hs' : (s : WithTop ℝ≥0) ≤ exitTime (X n) n x := hs.trans (min_le_right _ _)
      simp only [switchOff, le_top, ite_true, hs', hkey x hx n s hs', implies_true, and_self]

end BlockBand.SourceProcess.Stochastic.NativeSDE
