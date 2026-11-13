module
public import BlockBand.SourceProcess.Stochastic.SDE.ExportStop
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Localization and congruence of identities

`Ω = DriverSample S κ`, `P = driverLaw μ`, `dt ⊗ P = timeProbMeasure T P`.

* `StoppedIdentity.congr_stopped`: the identity at a stopping time `ρ` only depends on
  the process on `[0, ρ]` and on the coefficients on `(0, ρ]` (almost surely).
* `identity_of_localizing`: if the identity holds at `τ ∧ ρ_n` for all `n`, where
  `ρ_n → ⊤` a.s., and the `τ`-stopped integrand `ℓ∘γ · 1{s ≤ τ}` is an integrand, then it
  holds at `τ` (for this `ℓ`). Proof: the left sides at `τ ∧ ρ_n` are eventually equal to the
  left side at `τ`; by the Itô isometry and dominated convergence the integrals of
  `g · 1{s ≤ ρ_n}` converge in `L²(P)` to that of `g`; Fatou gives `E|LHS - I(g)|² = 0`.
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

omit [MeasurableSpace S] [Fintype κ] in
theorem coe_stopTime_le (t : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0) (x : DriverSample S κ) :
    ((stopTime t ρ x : ℝ≥0) : WithTop ℝ≥0) ≤ ρ x := by
  rw [coe_stopTime]
  exact min_le_right _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The identity at `ρ` only sees the process on `[0, ρ]` and the coefficients on
`(0, ρ]`. -/
theorem StoppedIdentity.congr_stopped {T : ℝ≥0} {ρ : DriverSample S κ → WithTop ℝ≥0}
    {X X' β β' : ℝ≥0 → DriverSample S κ → E} {γ γ' : κ → ℝ≥0 → DriverSample S κ → E}
    (hX : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ ρ x → X' s x = X s x)
    (hβ : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      β' s x = β s x ∧ ∀ a, γ' a s x = γ a s x)
    (h : StoppedIdentity μ T ρ X β γ) : StoppedIdentity μ T ρ X' β' γ' := by
  intro ℓ t ht
  obtain ⟨hs, hid⟩ := h ℓ t ht
  have hint : ∀ a, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ γ) a =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x)) (functionalIntegrand ℓ γ') a :=
    fun a => by
      filter_upwards [ae_timeProb_of_ae (T := T) hβ, timeProbMeasure_horizon (κ := κ) μ T]
        with p hp hpT
      simp only [stopIntegrand, functionalIntegrand]
      split_ifs with h1
      · rw [((hp _ (Real.toNNReal_pos.2 hpT.1) (h1.trans (min_le_right _ _))).2 a)]
      · rfl
  refine ⟨NativeIntegrand.congr hs hint, ?_⟩
  rw [← nativeIntegralOf_congr hs _ hint]
  filter_upwards [hid, hX, hβ] with x hx hxX hxβ
  have h1 : stoppedProcess X' ρ t x = stoppedProcess X ρ t x := hxX _ (coe_stopTime_le t ρ x)
  have h2 : stoppedDrift ρ β' t x = stoppedDrift ρ β t x := by
    unfold stoppedDrift
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    split_ifs with h3
    · rw [(hxβ _ (Real.toNNReal_pos.2 hs.1) h3).1]
    · rfl
  rw [h1, h2, hxX 0 zero_le]
  exact hx

omit [MeasurableSpace S] [Fintype κ] in
theorem min_min_of_le {t : ℝ≥0} {a c : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ c) :
    min (t : WithTop ℝ≥0) (min a c) = min (t : WithTop ℝ≥0) a := by
  rw [min_comm a c, ← min_assoc, min_eq_left h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Localization of the identity** (for one functional `ℓ`). -/
theorem identity_of_localizing {T : ℝ≥0} {τ : DriverSample S κ → WithTop ℝ≥0}
    {ρ : ℕ → DriverSample S κ → WithTop ℝ≥0}
    {X β : ℝ≥0 → DriverSample S κ → E} {γ : κ → ℝ≥0 → DriverSample S κ → E}
    (hρ : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => ρ n x) atTop (𝓝 ⊤))
    (hloc : ∀ n, StoppedIdentity μ T (fun x => min (τ x) (ρ n x)) X β γ) (ℓ : E →L[ℝ] ℝ)
    (hint : NativeIntegrand μ T (stopIntegrand τ (functionalIntegrand ℓ γ))) (t : ℝ≥0)
    (ht : t ≤ T) :
    ∃ hs : NativeIntegrand μ T
        (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) (functionalIntegrand ℓ γ)),
      (fun x => ℓ (stoppedProcess X τ t x) - ℓ (X 0 x) - ℓ (stoppedDrift τ β t x))
        =ᵐ[driverLaw (κ := κ) μ] (nativeIntegralOf hs : DriverSample S κ → ℝ) := by
  set g := stopIntegrand (fun x => min (t : WithTop ℝ≥0) (τ x)) (functionalIntegrand ℓ γ)
  have hs : NativeIntegrand μ T g := by
    have h := stopIntegrand_nativeIntegrand hint
      (isStoppingTime_const (driverAugmented (κ := κ) μ) t)
    rwa [stopIntegrand_min_stopIntegrand] at h
  refine ⟨hs, ?_⟩
  choose hsn hidn using fun n => hloc n ℓ t ht
  set L : DriverSample S κ → ℝ :=
    fun x => ℓ (stoppedProcess X τ t x) - ℓ (X 0 x) - ℓ (stoppedDrift τ β t x)
  set Ln : ℕ → DriverSample S κ → ℝ := fun n x =>
    ℓ (stoppedProcess X (fun x => min (τ x) (ρ n x)) t x) - ℓ (X 0 x) -
      ℓ (stoppedDrift (fun x => min (τ x) (ρ n x)) β t x)
  set I : DriverSample S κ → ℝ := (nativeIntegralOf hs : DriverSample S κ → ℝ)
  -- the left sides are eventually equal
  have hev : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ᶠ n in atTop, Ln n x = L x := by
    filter_upwards [hρ] with x hx
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hx t] with n hn
    have hle : (t : WithTop ℝ≥0) ≤ ρ n x := hn.le
    have h1 : stoppedProcess X (fun x => min (τ x) (ρ n x)) t x = stoppedProcess X τ t x := by
      simp only [stoppedProcess, min_min_of_le hle]
    have h2 : stoppedDrift (fun x => min (τ x) (ρ n x)) β t x = stoppedDrift τ β t x := by
      unfold stoppedDrift
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hst : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ n x := by
        refine le_trans ?_ hle
        rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
        exact hs.2
      simp only [le_min_iff, hst, and_true]
    simp only [Ln, L, h1, h2]
  -- integrand convergence in `L²(dt ⊗ P)`
  have hgn : ∀ n a, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (min (τ x) (ρ n x)))
      (functionalIntegrand ℓ γ) a = fun p => if ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ n p.2
        then g a p else 0 := fun n a => by
    funext p
    simp only [g, stopIntegrand, le_min_iff]
    split_ifs <;> simp_all
  have hconv : Tendsto (fun n => ∑ a, ∫⁻ p, ‖stopIntegrand (fun x => min (t : WithTop ℝ≥0)
      (min (τ x) (ρ n x))) (functionalIntegrand ℓ γ) a p - g a p‖ₑ ^ 2
        ∂timeProbMeasure T (driverLaw (κ := κ) μ)) atTop (𝓝 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _a : κ, 0 by simp]
    refine tendsto_finsetSum _ fun a _ => ?_
    have hfin : ∫⁻ p, ‖g a p‖ₑ ^ 2 ∂timeProbMeasure T (driverLaw (κ := κ) μ) ≠ ⊤ := by
      rw [lintegral_enorm_sq_eq_ofReal (hs a).2]
      exact ENNReal.ofReal_ne_top
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _p, 0 ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by simp
    rw [h0]
    refine tendsto_lintegral_of_dominated_convergence' _ (fun n => ?_) (fun n => ?_) hfin ?_
    · exact (((hsn n a).2.aestronglyMeasurable.sub (hs a).2.aestronglyMeasurable).enorm).pow_const _
    · refine Eventually.of_forall fun p => ?_
      simp only [hgn n a]
      split_ifs
      · simp
      · simp
    · filter_upwards [ae_timeProb_of_ae (T := T) hρ] with p hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hp p.1.toNNReal] with n hn
      simp only [hgn n a, hn.le, ite_true, sub_self, enorm_zero]
      norm_num
  -- `E |L_n - I|² = ∑_a ‖g_n - g‖²`
  have hLn : ∀ n, ∫⁻ x, ‖Ln n x - I x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ = ∑ a, ∫⁻ p,
      ‖stopIntegrand (fun x => min (t : WithTop ℝ≥0) (min (τ x) (ρ n x)))
        (functionalIntegrand ℓ γ) a p - g a p‖ₑ ^ 2
        ∂timeProbMeasure T (driverLaw (κ := κ) μ) := fun n => by
    rw [← lintegral_sq_nativeIntegralOf (nativeIntegrand_sub (hsn n) hs),
      nativeIntegralOf_sub (hsn n) hs]
    refine lintegral_congr_ae ?_
    filter_upwards [hidn n, Lp.coeFn_sub (nativeIntegralOf (hsn n)) (nativeIntegralOf hs)]
      with x h1 h2
    rw [h2, Pi.sub_apply]
    simp only [Ln, I]
    rw [h1]
  have hmeas : ∀ n, AEMeasurable (fun x => ‖Ln n x - I x‖ₑ ^ 2) (driverLaw (κ := κ) μ) :=
    fun n => ((((Lp.aestronglyMeasurable (nativeIntegralOf (hsn n))).congr (hidn n).symm).sub
      (Lp.aestronglyMeasurable (nativeIntegralOf hs))).enorm).pow_const _
  have hlim : ∀ᵐ x ∂driverLaw (κ := κ) μ, Tendsto (fun n => ‖Ln n x - I x‖ₑ ^ 2) atTop
      (𝓝 (‖L x - I x‖ₑ ^ 2)) := by
    filter_upwards [hev] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn]
  have hLm : AEMeasurable (fun x => ‖L x - I x‖ₑ ^ 2) (driverLaw (κ := κ) μ) :=
    aemeasurable_of_tendsto_metrizable_ae' hmeas hlim
  have hzero : ∫⁻ x, ‖L x - I x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ x, ‖L x - I x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ
        = ∫⁻ x, liminf (fun n => ‖Ln n x - I x‖ₑ ^ 2) atTop ∂driverLaw (κ := κ) μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with x hx
          exact hx.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖Ln n x - I x‖ₑ ^ 2 ∂driverLaw (κ := κ) μ) atTop :=
          lintegral_liminf_le' hmeas
      _ = 0 := by
          simp only [hLn]
          exact hconv.liminf_eq
  filter_upwards [(lintegral_eq_zero_iff' hLm).1 hzero] with x hx
  have : ‖L x - I x‖ₑ = 0 := by simpa using hx
  exact sub_eq_zero.1 (enorm_eq_zero.1 this)

end BlockBand.SourceProcess.Stochastic.NativeSDE
