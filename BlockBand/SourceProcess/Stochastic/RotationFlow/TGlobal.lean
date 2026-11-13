module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TPicardFixed
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Global solutions for time-dependent Lipschitz bounded coefficients

Time-inhomogeneous versions of the global Picard solution and its properties.
`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`, `c : TLipCoeff κ E`.

* `stoppedIdentity_of_tStrongSolOn`: horizon-`N` strong solutions satisfy the identity
  at every augmented stopping time, with drift `b(t, X_t)` and diffusion `σ(t, X_t)`.
* `StoppedIdentity.tcongr`: the identity transfers to processes agreeing a.s. on `[0,T]`.
* `tStrongSolOn_agree`: horizon-`N` and horizon-`N'` solutions agree a.s. on `[0,N]`
  (`stoppedProcess_ae_eq_of_lipschitz`, which is stated for arbitrary process coefficients).
* `exists_tGlobalSol`: a global solution (`TGlobalSol`), glued from the horizon solutions.
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.NativeSDE

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Strong solutions satisfy the identity at every stopping time.** -/
theorem stoppedIdentity_of_tStrongSolOn {N : ℝ≥0} {b : ℝ≥0 → E → E} {σ : κ → ℝ≥0 → E → E}
    {ξ : DriverSample S κ → E} {X : ℝ≥0 → DriverSample S κ → E}
    (hX : TStrongSolOn μ N b σ ξ X)
    {ρ : DriverSample S κ → WithTop ℝ≥0} (hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ) :
    StoppedIdentity μ N ρ X (fun t x => b t (X t x)) (fun a t x => σ a t (X t x)) := by
  classical
  intro ℓ t ht
  obtain ⟨-, -, hX0, hg, hXeq⟩ := hX
  let B := Module.finBasis ℝ E
  choose hs hid using fun j => nativeAdaptedLimit_stopped (hg j) hρ t
  obtain ⟨hsum, hsumeq⟩ := exists_nativeIntegralOf_sum Finset.univ hs (fun j => ℓ (B j))
  have hpt : ∀ c p, (fun c p => ∑ j, ℓ (B j) *
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (fun a p => coordCLM E j (σ a p.1.toNNReal (X p.1.toNNReal p.2))) c p) c p =
      stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
        (functionalIntegrand ℓ fun a t x => σ a t (X t x)) c p := by
    intro c p
    simp only [stopIntegrand, functionalIntegrand]
    split_ifs
    · conv_rhs => rw [← B.sum_repr (σ c p.1.toNNReal (X p.1.toNNReal p.2))]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl
    · simp
  have htarget : NativeIntegrand μ N (stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a t (X t x))) :=
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
/-- Identities for time-dependent coefficient functions of the path transfer to
processes that agree a.s. on `[0,T]`. -/
theorem StoppedIdentity.tcongr {T : ℝ≥0} {ρ : DriverSample S κ → WithTop ℝ≥0}
    {b : ℝ≥0 → E → E} {σ : κ → ℝ≥0 → E → E} {X X' : ℝ≥0 → DriverSample S κ → E}
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ T, X t x = X' t x)
    (h : StoppedIdentity μ T ρ X' (fun t x => b t (X' t x)) (fun a t x => σ a t (X' t x))) :
    StoppedIdentity μ T ρ X (fun t x => b t (X t x)) (fun a t x => σ a t (X t x)) := by
  intro ℓ t ht
  obtain ⟨hs', hid⟩ := h ℓ t ht
  have hint : ∀ c, stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a t (X' t x)) c =ᵐ[timeProbMeasure T
        (driverLaw (κ := κ) μ)] stopIntegrand (fun x => min (t : WithTop ℝ≥0) (ρ x))
      (functionalIntegrand ℓ fun a t x => σ a t (X t x)) c := fun c => by
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
  have h2 : stoppedDrift ρ (fun t x => b t (X t x)) t x =
      stoppedDrift ρ (fun t x => b t (X' t x)) t x := by
    rw [stoppedDrift_eq_integral, stoppedDrift_eq_integral]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hle : s.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.2.trans (by exact_mod_cast (stopTime_le t ρ x).trans ht)
    simp only [hxx _ hle]
  rw [h1, h2, hxx 0 zero_le]
  exact hx

omit [MeasurableSpace S] [Fintype κ] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
theorem aesm_coeff_path {f : ℝ≥0 → E → E} (hf : Continuous fun q : ℝ≥0 × E => f q.1 q.2)
    {X : ℝ≥0 → DriverSample S κ → E} {x : DriverSample S κ} (hx : Continuous fun t => X t x)
    (m : Measure ℝ) :
    AEStronglyMeasurable (fun s : ℝ => f s.toNNReal (X s.toNNReal x)) m :=
  (hf.comp (continuous_real_toNNReal.prodMk (hx.comp continuous_real_toNNReal))).aestronglyMeasurable

/-- **Horizon consistency of strong solutions**: solutions on `N ≤ N'` agree on `[0,N]`. -/
theorem tStrongSolOn_agree (c : TLipCoeff κ E) {ξ : DriverSample S κ → E} {N N' : ℝ≥0}
    (hNN' : N ≤ N') {X Y : ℝ≥0 → DriverSample S κ → E} (hX : TStrongSolOn μ N c.b c.σ ξ X)
    (hY : TStrongSolOn μ N' c.b c.σ ξ Y) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t ≤ N, X t x = Y t x := by
  have hXid := stoppedIdentity_of_tStrongSolOn hX (isStoppingTime_top (μ := μ))
  have hYid := (stoppedIdentity_of_tStrongSolOn hY (isStoppingTime_top (μ := μ))).mono hNN'
  obtain ⟨hXa, hXc, hX0, -⟩ := hX
  obtain ⟨hYa, hYc, hY0, -⟩ := hY
  have heq := stoppedProcess_ae_eq_of_lipschitz (isStoppingTime_top (μ := μ)) hXa hYa
    (Eventually.of_forall hXc) (Eventually.of_forall hYc)
    (Eventually.of_forall fun x => by rw [hX0, hY0]) hXid hYid (K := c.K) (C := c.C)
    (Eventually.of_forall fun x s _ _ => ⟨norm_sub_le_of_lip (c.lip_b s) _ _,
      fun a => norm_sub_le_of_lip (c.lip_σ a s) _ _⟩)
    (Eventually.of_forall fun x s _ _ => ⟨c.bd_b _ _, c.bd_b _ _,
      fun a => ⟨c.bd_σ a _ _, c.bd_σ a _ _⟩⟩)
    (Eventually.of_forall fun x => aesm_coeff_path c.cont_b (hXc x) _)
    (Eventually.of_forall fun x => aesm_coeff_path c.cont_b (hYc x) _)
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

variable (μ) in
/-- Global strong solution for time-dependent Lipschitz bounded coefficients. -/
def TGlobalSol (c : TLipCoeff κ E) (ξ : DriverSample S κ → E)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  (∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t)) ∧
    (∀ x, Continuous fun t => X t x) ∧ (∀ x, X 0 x = ξ x) ∧
    ∀ (T : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0),
      IsStoppingTime (driverAugmented (κ := κ) μ) ρ →
        StoppedIdentity μ T ρ X (fun t x => c.b t (X t x)) (fun a t x => c.σ a t (X t x))

/-- **Global existence** for time-dependent Lipschitz bounded coefficients. -/
theorem exists_tGlobalSol (c : TLipCoeff κ E) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) : ∃ X, TGlobalSol μ c ξ X := by
  classical
  choose Xn hXn using fun n : ℕ => exists_tStrongSolOn c hξ (N := (n : ℝ≥0))
  have hagree : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ∀ n m : ℕ, n ≤ m → ∀ t ≤ (n : ℝ≥0), Xn n t x = Xn m t x := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [tStrongSolOn_agree c (Nat.cast_le.2 hnm) (hXn n) (hXn m)] with x hx _ t ht
      exact hx t ht
    · exact Eventually.of_forall fun x h => absurd h hnm
  obtain ⟨G, hGm, hG0, hGa⟩ := exists_good_set μ hagree
  have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  let X : ℝ≥0 → DriverSample S κ → E := fun t => G.piecewise (Xn ⌈t⌉₊ t) ξ
  have hkey : ∀ x ∈ G, ∀ m : ℕ, ∀ t ≤ (m : ℝ≥0), X t x = Xn m t x := by
    intro x hx m t ht
    simp only [X, Set.piecewise_eq_of_mem _ _ _ hx]
    exact hGa x hx ⌈t⌉₊ m (Nat.ceil_le.2 ht) t (Nat.le_ceil t)
  refine ⟨X, fun t => ?_, fun x => ?_, fun x => ?_, fun T ρ hρ => ?_⟩
  · exact StronglyMeasurable.piecewise (measurableSet_aug_of_full μ hGm hG0 t) ((hXn _).1 t)
      (hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le))
  · by_cases hx : x ∈ G
    · refine continuous_iff_continuousAt.2 fun t₀ => ?_
      set m : ℕ := ⌈t₀⌉₊ + 1
      have hlt : t₀ < (m : ℝ≥0) := (Nat.le_ceil t₀).trans_lt (by simp [m])
      refine ((hXn m).2.1 x).continuousAt.congr ?_
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact (hkey x hx m t (le_of_lt ht)).symm
    · have : (fun t => X t x) = fun _ => ξ x := by
        funext t
        simp only [X, Set.piecewise_eq_of_notMem _ _ _ hx]
      rw [this]
      exact continuous_const
  · by_cases hx : x ∈ G
    · rw [hkey x hx 0 0 (by simp)]
      exact (hXn 0).2.2.1 x
    · simp only [X, Set.piecewise_eq_of_notMem _ _ _ hx]
  · have h := (stoppedIdentity_of_tStrongSolOn (hXn ⌈T⌉₊) hρ).mono (Nat.le_ceil T)
    refine StoppedIdentity.tcongr ?_ h
    filter_upwards [hGae] with x hx t ht
    exact hkey x hx _ t (ht.trans (Nat.le_ceil T))

end BlockBand.SourceProcess.Stochastic.RotationFlow
