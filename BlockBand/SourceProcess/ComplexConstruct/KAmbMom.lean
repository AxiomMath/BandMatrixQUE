module

public import BlockBand.SourceProcess.ComplexConstruct.KAmbSol
public import BlockBand.SourceProcess.CoupledFrames.NativeSum
public import BlockBand.SourceProcess.Stochastic.SDE.NativeUnique

/-!
# The joint SDE `(X, 𝒴)`: second moments of the noise part before the frame exit

`lintegral_sq_snd_le`: let `Z` be a strong exit-time solution of radius `n > 0` of the joint
equation from `(ξ, 0)`, `X` the global solution of the frame equation, `X'` a
continuous adapted modification, `M ≤ n` and `‖σ₂ a y‖ ≤ C` on the `M`-ball. With
`τ = exit_n(Z) ∧ exit_M(X')` and every functional `ℓ` of `E₂`,
`E|ℓ(Z^τ_T.2)|² ≤ 2‖ℓ‖²(T + |κ|) C² T` (one-step comparison with the zero process,
`lintegral_sq_functional_sub_le`). The bound does not depend on `n`.

`exists_functionals_ge`: in a finite-dimensional space finitely many functionals `ℓ_k` satisfy
`‖v‖ ≤ max_k |ℓ_k v|` for `v ≠ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral BlockBand.SourceProcess.CoupledFrames

variable {κ : Type*} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₁] [NormedSpace ℝ E₂]

/-- Finitely many functionals dominate the norm. -/
theorem exists_functionals_ge [FiniteDimensional ℝ E₂] :
    ∃ (d : ℕ) (ℓ : Fin d → E₂ →L[ℝ] ℝ), ∀ v : E₂, 0 < ‖v‖ → ∃ k, ‖v‖ ≤ |ℓ k v| := by
  set b := Module.finBasis ℝ E₂
  set d := Module.finrank ℝ E₂
  refine ⟨d, fun k => ((d : ℝ) * ‖b k‖) • LinearMap.toContinuousLinearMap (b.coord k),
    fun v hv => ?_⟩
  have hsum : ‖v‖ ≤ ∑ k, |b.repr v k| * ‖b k‖ := by
    conv_lhs => rw [← b.sum_repr v]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [norm_smul, Real.norm_eq_abs]
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsum
    linarith
  have hd : (0 : ℝ) < d := by
    obtain ⟨k, -⟩ := hne
    exact Nat.cast_pos.2 (Fin.pos k)
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le hne (f := fun _ => ‖v‖ / d)
    (g := fun k => |b.repr v k| * ‖b k‖) (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rwa [mul_div_cancel₀ _ hd.ne'])
  refine ⟨k, ?_⟩
  simp only [FunLike.coe_smul, Pi.smul_apply, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply,
    smul_eq_mul, abs_mul, abs_of_nonneg (mul_nonneg hd.le (norm_nonneg (b k)))]
  have := (div_le_iff₀ hd).1 hk
  nlinarith [norm_nonneg (b k), abs_nonneg (b.repr v k)]

variable [Fintype κ] {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂]

/-- **Second moment of the noise part of a joint exit-time solution, stopped at the frame
exit.** -/
theorem lintegral_sq_snd_le {b₁ : E₁ → E₁} {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    (hb : LocallyLipschitz b₁) (hσ : ∀ a, LocallyLipschitz (σ₁ a))
    (hσ₂ : ∀ a, Continuous (σ₂ a)) {ξ : DriverSample S κ → E₁}
    {X X' : ℝ≥0 → DriverSample S κ → E₁} (hX : IsSDESolution μ b₁ σ₁ ξ X)
    (hX'a : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t))
    (hX'c : ∀ x, Continuous fun t => X' t x)
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x)
    {Z : ℝ≥0 → DriverSample S κ → E₁ × E₂} {R : ℝ} (hR : 0 < R)
    (hZ : IsStrongExitSolution μ (jb b₁) (jσ σ₁ σ₂) (fun x => (ξ x, 0)) R Z) {M C : ℝ}
    (hC : ∀ y : E₁, ‖y‖ ≤ M → ∀ a, ‖σ₂ a y‖ ≤ C) (ℓ : E₂ →L[ℝ] ℝ) (T : ℝ≥0) :
    ∫⁻ x, ‖ℓ (stoppedProcess (fun t x => (Z t x).2)
        (fun x => min (exitTime Z R x) (exitTimeOf X' M x)) T x)‖ₑ ^ 2 ∂driverLaw (κ := κ) μ ≤
      2 * ‖ℓ‖ₑ ^ 2 * (ENNReal.ofReal T + Fintype.card κ) *
        (ENNReal.ofReal C ^ 2 * ENNReal.ofReal T) := by
  classical
  have hU := ae_fst_eq_of_joint hb hσ hR hX hZ hX'a hX'c hXX'
  set e := exitTime Z R with hedef
  set τ : DriverSample S κ → WithTop ℝ≥0 := fun x => min (e x) (exitTimeOf X' M x) with hτdef
  have hτ : IsStoppingTime (driverAugmented (κ := κ) μ) τ :=
    hZ.stopping.min (isStoppingTime_exitTimeOf hX'a hX'c M)
  have hZ₁ := fst_nativeIto hZ.sol.1
  have hZ₂ := snd_nativeIto hZ.sol.1
  have hZ₁c : ∀ x, Continuous fun t => (Z t x).1 := fun x => continuous_fst.comp (hZ.continuous x)
  have hball : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ τ x →
      ‖(Z s x).1‖ ≤ M := by
    filter_upwards [hU, hXX'] with x hu hx s hs0 hs
    rw [hu.2 s (hs.trans (min_le_left _ _)), ← hx s]
    exact norm_le_of_le_exitTimeOf (hX'c x) hs0 (hs.trans (min_le_right _ _))
  have hid₂ : StoppedIdentity μ T τ (fun t x => (Z t x).2) (fun _ _ => 0)
      (fun a => switchOff e fun t x => σ₂ a (Z t x).1) :=
    IsNativeItoProcess.stoppedIdentity hZ₂ hτ T fun ℓ' => by
      refine NativeIntegrand.congr (nativeIntegrand_stopped_bounded (μ := μ) hZ₁.adapted
        (Eventually.of_forall hZ₁c) hτ (φ := fun a y => ℓ' (σ₂ a y))
        (fun a => ℓ'.continuous.comp (hσ₂ a)) (M := ‖ℓ'‖ * C) ?_ T) fun a =>
          Eventually.of_forall fun p => ?_
      · filter_upwards [hball] with x hx s hs0 hs a
        rw [← Real.norm_eq_abs]
        exact (ℓ'.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC _ (hx s hs0 hs) a)
          (norm_nonneg _))
      · simp only [stopIntegrand, functionalIntegrand, switchOff]
        by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2
        · have h2 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime Z R p.2 :=
            h1.trans (min_le_left _ _)
          simp only [h1, h2, ite_true]
        · simp only [h1, ite_false]
  have hid0 : StoppedIdentity μ T τ (fun (_ : ℝ≥0) (_ : DriverSample S κ) => (0 : E₂))
      (fun _ _ => 0) (fun _ _ _ => 0) :=
    IsNativeItoProcess.stoppedIdentity isNativeItoProcess_zero hτ T fun ℓ' => by
      refine NativeIntegrand.congr (nativeIntegrand_zero (μ := μ) (T := T)) fun a =>
        Eventually.of_forall fun p => ?_
      simp only [stopIntegrand, functionalIntegrand, map_zero, ite_self]
  have h := lintegral_sq_functional_sub_le (H := fun _ => ENNReal.ofReal C)
    (by filter_upwards [] with x; simp only [hZ.init]) hid₂ hid0 (C := 0)
    (ae_of_all _ fun x s _ _ => by simp)
    (ae_of_all _ fun x => aestronglyMeasurable_const)
    (ae_of_all _ fun x => aestronglyMeasurable_const) aemeasurable_const
    (ae_of_all _ fun x => aemeasurable_const) ?_ ℓ le_rfl
  · simp only [stoppedProcess, map_zero, sub_zero, lintegral_const,
      timeProbMeasure_univ] at h
    exact h
  · filter_upwards [hball] with x hx s hs0 hs
    refine ⟨by simp, fun a => ?_⟩
    have hse : (s : WithTop ℝ≥0) ≤ e x := hs.trans (min_le_left _ _)
    simp only [switchOff, hse, ite_true, sub_zero]
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC _ (hx s hs0 hs) a)

end BlockBand.SourceProcess.ComplexConstruct
