module
public import BlockBand.SourceProcess.Stochastic.SDE.NativePicardFixed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# From strong solutions to identities; global Lipschitz solutions

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`.

* `stoppedIdentity_of_strongSolOn`: a horizon-`N` strong solution satisfies the native
  identity (`StoppedIdentity`) for every augmented stopping time `ρ`, with drift `b(X)` and
  diffusion `σ(X)` (the stopped identities of `ContinuousStoppedIntegral` and linearity of the
integral).
* `StoppedIdentity.mono`: identities pass to smaller horizons (`nativeIntegralOf_horizon`);
  `StoppedIdentity.congr`: and to processes that agree a.s. on `[0,T]`.
* `strongSolOn_agree`: horizon-`N` and horizon-`N'` solutions (`N ≤ N'`) agree a.s. on `[0,N]`
  (Gronwall uniqueness `stoppedProcess_ae_eq_of_lipschitz` with `ρ = ⊤`).
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

theorem coeFn_sum_smul {α ι : Type*} [MeasurableSpace α] {m : Measure α} (s : Finset ι)
    (r : ι → ℝ) (F : ι → Lp ℝ 2 m) :
    ((∑ i ∈ s, r i • F i : Lp ℝ 2 m) : α → ℝ) =ᵐ[m] fun x => ∑ i ∈ s, r i * (F i : α → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (r a • F a) (∑ i ∈ s, r i • F i), Lp.coeFn_smul (r a) (F a), ih]
      with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

/-- The stopped time `t ∧ ρ(x)` as an element of `ℝ≥0`. -/
abbrev stopTime (t : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0) (x : DriverSample S κ) : ℝ≥0 :=
  (min (t : WithTop ℝ≥0) (ρ x)).untopA

omit [MeasurableSpace S] [Fintype κ] in
theorem coe_stopTime (t : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0) (x : DriverSample S κ) :
    ((stopTime t ρ x : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (ρ x) := by
  have hne : min (t : WithTop ℝ≥0) (ρ x) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [stopTime, WithTop.untopA_eq_untop hne, WithTop.coe_untop]

omit [MeasurableSpace S] [Fintype κ] in
theorem stopTime_le (t : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0) (x : DriverSample S κ) :
    stopTime t ρ x ≤ t := by
  have h := min_le_left (t : WithTop ℝ≥0) (ρ x)
  rw [← coe_stopTime t ρ x] at h
  exact_mod_cast h

omit [MeasurableSpace S] [Fintype κ] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The stopped drift is the drift integral up to `t ∧ ρ`. -/
theorem stoppedDrift_eq_integral (ρ : DriverSample S κ → WithTop ℝ≥0)
    (β : ℝ≥0 → DriverSample S κ → E) (t : ℝ≥0) (x : DriverSample S κ) :
    stoppedDrift ρ β t x = ∫ s in Ioc (0 : ℝ) (stopTime t ρ x), β s.toNNReal x := by
  unfold stoppedDrift
  have hsub : Ioc (0 : ℝ) (stopTime t ρ x) ⊆ Ioc (0 : ℝ) t :=
    Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 (stopTime_le t ρ x))
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext s
  have key : s ∈ Ioc (0 : ℝ) (stopTime t ρ x) ↔
      s ∈ Ioc (0 : ℝ) t ∧ ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ x := by
    constructor
    · intro hs
      refine ⟨hsub hs, ?_⟩
      have h1 : s.toNNReal ≤ stopTime t ρ x := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact hs.2
      have h2 := WithTop.coe_le_coe.2 h1
      rw [coe_stopTime] at h2
      exact h2.trans (min_le_right _ _)
    · rintro ⟨hs, hρ⟩
      refine ⟨hs.1, ?_⟩
      have h1 : ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (ρ x) := by
        refine le_min ?_ hρ
        rw [WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
        exact hs.2
      rw [← coe_stopTime, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe] at h1
      exact h1
  by_cases h1 : s ∈ Ioc (0 : ℝ) (stopTime t ρ x)
  · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (key.1 h1).1, ite_eq_left (key.1 h1).2]
  · rw [Set.indicator_of_notMem h1]
    by_cases h2 : s ∈ Ioc (0 : ℝ) t
    · rw [Set.indicator_of_mem h2, ite_eq_right fun h => h1 (key.2 ⟨h2, h⟩)]
    · rw [Set.indicator_of_notMem h2]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Strong solutions satisfy the identity at every stopping time.** -/
theorem stoppedIdentity_of_strongSolOn {N : ℝ≥0} {b : E → E} {σ : κ → E → E}
    {ξ : DriverSample S κ → E} {X : ℝ≥0 → DriverSample S κ → E} (hX : StrongSolOn μ N b σ ξ X)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ) :
    StoppedIdentity μ N ρ X (fun t x => b (X t x)) (fun a t x => σ a (X t x)) := by
  classical
  intro ℓ t ht
  obtain ⟨-, -, hX0, hg, hXeq⟩ := hX
  let B := Module.finBasis ℝ E
  choose hs hid using fun j => nativeAdaptedLimit_stopped (hg j) hρ t
  obtain ⟨hsum, hsumeq⟩ := exists_nativeIntegralOf_sum Finset.univ hs (fun j => ℓ (B j))
  have hpt : ∀ c p, (fun c p => ∑ j, ℓ (B j) *
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (fun a p => coordCLM E j (σ a (X p.1.toNNReal p.2))) c p) c p =
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (functionalIntegrand ℓ fun a t x => σ a (X t x)) c p := by
    intro c p
    simp only [stopIntegrand, functionalIntegrand]
    split_ifs
    · conv_rhs => rw [← B.sum_repr (σ c (X p.1.toNNReal p.2))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    · simp
  have htarget : NativeIntegrand μ N (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a (X t x))) :=
    NativeIntegrand.congr hsum fun c => Eventually.of_forall fun p => hpt c p
  refine ⟨htarget, ?_⟩
  rw [← nativeIntegralOf_congr hsum htarget (fun c => Eventually.of_forall fun p => hpt c p),
    hsumeq]
  filter_upwards [hXeq, ae_all_iff.2 hid, coeFn_sum_smul Finset.univ (fun j => ℓ (B j))
    (fun j => nativeIntegralOf (hs j))] with x hx hj hsumx
  rw [hsumx]
  have hu := stopTime_le t ρ x
  have hXu := hx (stopTime t ρ x) (hu.trans ht)
  have hsp : stoppedProcess X ρ t x = X (stopTime t ρ x) x := rfl
  rw [hsp, hXu, hX0 x, stoppedDrift_eq_integral]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  have hj' : ∀ j, nativeAdaptedLimit μ N (hg j).family (stopTime t ρ x) x =
      (nativeIntegralOf (hs j) : DriverSample S κ → ℝ) x := fun j => hj j
  simp only [hj']
  rw [show ∀ a b c : ℝ, a + b + c - a - b = c from fun a b c => by ring]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Identities pass to smaller horizons. -/
theorem StoppedIdentity.mono {N N' : ℝ≥0} (hNN' : N ≤ N') {ρ : DriverSample S κ → WithTop ℝ≥0}
    {X β : ℝ≥0 → DriverSample S κ → E} {γ : κ → ℝ≥0 → DriverSample S κ → E}
    (h : StoppedIdentity μ N' ρ X β γ) : StoppedIdentity μ N ρ X β γ := by
  intro ℓ t ht
  obtain ⟨hs', hid⟩ := h ℓ t (ht.trans hNN')
  obtain ⟨hs, he⟩ := nativeIntegralOf_horizon hNN' hs' fun c p hp => by
    have hlt : t < p.1.toNNReal := by
      rw [Real.lt_toNNReal_iff_coe_lt]
      exact lt_of_le_of_lt (NNReal.coe_le_coe.2 ht) hp
    have hn : ¬ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (ρ p.2) := fun h' =>
      absurd ((WithTop.coe_le_coe.1 (h'.trans (min_le_left _ _)))) (not_le.2 hlt)
    simp only [stopIntegrand, hn, ite_false]
  exact ⟨hs, he ▸ hid⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Identities for coefficient functions of the path transfer to processes that agree
a.s. on `[0,T]`. -/
theorem StoppedIdentity.congr {T : ℝ≥0} {ρ : DriverSample S κ → WithTop ℝ≥0} {b : E → E}
    {σ : κ → E → E} {X X' : ℝ≥0 → DriverSample S κ → E}
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ T, X t x = X' t x)
    (h : StoppedIdentity μ T ρ X' (fun t x => b (X' t x)) (fun a t x => σ a (X' t x))) :
    StoppedIdentity μ T ρ X (fun t x => b (X t x)) (fun a t x => σ a (X t x)) := by
  intro ℓ t ht
  obtain ⟨hs', hid⟩ := h ℓ t ht
  have hint : ∀ c, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a (X' t x)) c =ᵐ[timeProbMeasure T
        (driverLaw (κ := κ) μ)] stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a (X t x)) c := fun c => by
    filter_upwards [ae_timeProb_of_ae (T := T) hXX', timeProbMeasure_horizon (κ := κ) μ T] with
      p hp hpT
    have hle : p.1.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hpT.2
    simp only [stopIntegrand, functionalIntegrand, hp _ hle]
  refine ⟨NativeIntegrand.congr hs' hint, ?_⟩
  rw [← nativeIntegralOf_congr hs' _ hint]
  filter_upwards [hid, hXX'] with x hx hxx
  have h1 : stoppedProcess X ρ t x = stoppedProcess X' ρ t x :=
    hxx _ ((stopTime_le t ρ x).trans ht)
  have h2 : stoppedDrift ρ (fun t x => b (X t x)) t x = stoppedDrift ρ (fun t x => b (X' t x)) t x := by
    rw [stoppedDrift_eq_integral, stoppedDrift_eq_integral]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hle : s.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.2.trans (by exact_mod_cast (stopTime_le t ρ x).trans ht)
    simp only [hxx _ hle]
  rw [h1, h2, hxx 0 zero_le]
  exact hx

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_sub_le_of_lip {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (a b : E) :
    ‖f a - f b‖ ≤ K * ‖a - b‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact hf.dist_le_mul a b

/-- **Horizon consistency of strong solutions**: solutions on `N ≤ N'` agree on `[0,N]`. -/
theorem strongSolOn_agree (c : LipCoeff κ E) {ξ : DriverSample S κ → E} {N N' : ℝ≥0}
    (hNN' : N ≤ N') {X Y : ℝ≥0 → DriverSample S κ → E} (hX : StrongSolOn μ N c.b c.σ ξ X)
    (hY : StrongSolOn μ N' c.b c.σ ξ Y) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N, X t x = Y t x := by
  have hXid := stoppedIdentity_of_strongSolOn hX (isStoppingTime_top (μ := μ))
  have hYid := (stoppedIdentity_of_strongSolOn hY (isStoppingTime_top (μ := μ))).mono hNN'
  obtain ⟨hXa, hXc, hX0, -⟩ := hX
  obtain ⟨hYa, hYc, hY0, -⟩ := hY
  have heq := stoppedProcess_ae_eq_of_lipschitz (isStoppingTime_top (μ := μ)) hXa hYa
    (Eventually.of_forall hXc) (Eventually.of_forall hYc)
    (Eventually.of_forall fun x => by rw [hX0, hY0]) hXid hYid (K := c.K) (C := c.C)
    (Eventually.of_forall fun x s _ _ => ⟨norm_sub_le_of_lip c.lip_b _ _,
      fun a => norm_sub_le_of_lip (c.lip_σ a) _ _⟩)
    (Eventually.of_forall fun x s _ _ => ⟨c.bd_b _, c.bd_b _, fun a => ⟨c.bd_σ a _, c.bd_σ a _⟩⟩)
    (Eventually.of_forall fun x => (c.lip_b.continuous.comp ((hXc x).comp
      continuous_real_toNNReal)).aestronglyMeasurable)
    (Eventually.of_forall fun x => (c.lip_b.continuous.comp ((hYc x).comp
      continuous_real_toNNReal)).aestronglyMeasurable)
  have hst (Z : ℝ≥0 → DriverSample S κ → E) (t : ℝ≥0) :
      stoppedProcess Z (fun _ => ⊤) t = Z t := funext fun _ => stoppedProcess_eq_of_le le_top
  have hall := indistinguishable_of_continuous (P := driverLaw (κ := κ) μ)
    (X := fun t x => X (min t N) x) (Y := fun t x => Y (min t N) x)
    (Eventually.of_forall fun x => (hXc x).comp (continuous_id.min continuous_const))
    (Eventually.of_forall fun x => (hYc x).comp (continuous_id.min continuous_const))
    fun t => by
      have := heq (min t N) (min_le_right _ _)
      rwa [hst, hst] at this
  filter_upwards [hall] with x hx t ht
  have := hx t
  simp only [min_eq_left ht] at this
  exact this

end BlockBand.SourceProcess.Stochastic.NativeSDE
