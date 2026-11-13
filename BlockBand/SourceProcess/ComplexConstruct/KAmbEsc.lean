module

public import BlockBand.SourceProcess.ComplexConstruct.KAmbMom

/-!
# The joint SDE `(X, 𝒴)`: the exit times escape

`ae_escape`: for strong exit-time solutions `Z_n` of radius `n` of the joint equation from
`(ξ, 0)` and a global solution `X` of the frame equation, a.s. for every `T`
some `exit_n(Z_n)` exceeds `T`; this is the hypothesis of `exists_isSDESolution_of_family`.

Proof. Fix `T` and `M`. On `A_M = {exit_n(Z_n) ≤ T for all n} ∩ {T < exit_M(X')}`, for `n > M`
the frame part of `Z_n` is `X` up to `e_n = exit_n(Z_n)` (`ae_fst_eq_of_joint`), of norm `< M`,
so the noise part has norm `≥ n` at `e_n = τ_n ∧ T` (`τ_n = e_n ∧ exit_M(X')`). Chebyshev with
`lintegral_sq_snd_le` gives `P(A_M) ≤ C_M/n²` for all `n > M`, so `P(A_M) = 0`; the sets `A_M`
cover the bad event since `exit_M(X') → ⊤`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic.Semimartingale

variable {κ : Type*} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℝ E₁] [NormedSpace ℝ E₂]
  [Fintype κ] {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂]

omit [MeasurableSpace S] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂]
  [BorelSpace E₂] [Fintype κ] [MeasurableSpace E₁] [BorelSpace E₁] in
theorem exists_bound_ball {σ₂ : κ → E₁ → E₂} [Finite κ] (hσ₂ : ∀ a, Continuous (σ₂ a)) (M : ℝ) :
    ∃ C : ℝ, ∀ y : E₁, ‖y‖ ≤ M → ∀ a, ‖σ₂ a y‖ ≤ C := by
  have := Fintype.ofFinite κ
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E₁) M).exists_bound_of_continuousOn
    (f := fun y => ∑ a, ‖σ₂ a y‖) (continuous_finsetSum _ fun a _ =>
      (hσ₂ a).norm).continuousOn
  refine ⟨C, fun y hy a => ?_⟩
  have h := hC y (mem_closedBall_zero_iff.2 hy)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)] at h
  exact (Finset.single_le_sum (f := fun a => ‖σ₂ a y‖) (fun a _ => norm_nonneg _)
    (Finset.mem_univ a)).trans h

theorem tendsto_div_natSq (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun n : ℕ => K / ((n ^ 2 : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n ^ 2 : ℕ) : ℝ≥0∞)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_nat_nhds_top.comp (tendsto_pow_atTop two_ne_zero)
  have h2 := ENNReal.Tendsto.const_mul (tendsto_inv_iff.2 h1) (a := K) (Or.inr hK)
  simp only [ENNReal.inv_top, mul_zero] at h2
  simpa only [div_eq_mul_inv] using h2

/-- **Escape of the joint exit times.** -/
theorem ae_escape {b₁ : E₁ → E₁} {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    (hb : LocallyLipschitz b₁) (hσ : ∀ a, LocallyLipschitz (σ₁ a))
    (hσ₂ : ∀ a, Continuous (σ₂ a)) {ξ : DriverSample S κ → E₁}
    {X X' : ℝ≥0 → DriverSample S κ → E₁} (hX : IsSDESolution μ b₁ σ₁ ξ X)
    (hX'a : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t))
    (hX'c : ∀ x, Continuous fun t => X' t x)
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x)
    {Z : ℕ → ℝ≥0 → DriverSample S κ → E₁ × E₂}
    (hZ : ∀ n : ℕ, IsStrongExitSolution μ (jb b₁) (jσ σ₁ σ₂) (fun x => (ξ x, 0)) n (Z n)) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ T : ℕ, ∃ n : ℕ,
      ((T : ℝ≥0) : WithTop ℝ≥0) < exitTime (Z n) n x := by
  classical
  obtain ⟨d, ℓ, hℓ⟩ := exists_functionals_ge (E₂ := E₂)
  rw [ae_all_iff]
  intro T
  set A : Set (DriverSample S κ) := {x | ∀ n : ℕ, exitTime (Z n) n x ≤ ((T : ℝ≥0) : WithTop ℝ≥0)}
  set AM : ℕ → Set (DriverSample S κ) := fun M =>
    A ∩ {x | ((T : ℝ≥0) : WithTop ℝ≥0) < exitTimeOf X' M x}
  have hcov : A ⊆ ⋃ M, AM M := fun x hx => by
    obtain ⟨M, hM⟩ := ((WithTop.tendsto_nhds_top_iff _).1 (tendsto_exitTimeOf_top (hX'c x))
      (T : ℝ≥0)).exists
    exact mem_iUnion.2 ⟨M, hx, hM⟩
  have hAM : ∀ M : ℕ, driverLaw (κ := κ) μ (AM M) = 0 := by
    intro M
    obtain ⟨C, hC⟩ := exists_bound_ball hσ₂ M
    set V : ℕ → Fin d → DriverSample S κ → ℝ := fun n k x => ℓ k (stoppedProcess
      (fun t x => (Z n t x).2) (fun x => min (exitTime (Z n) n x) (exitTimeOf X' M x)) T x)
    set K : Fin d → ℝ≥0∞ := fun k => 2 * ‖ℓ k‖ₑ ^ 2 * (ENNReal.ofReal T + Fintype.card κ) *
      (ENNReal.ofReal C ^ 2 * ENNReal.ofReal T)
    have hK : ∑ k, K k ≠ ⊤ := ENNReal.sum_ne_top.2 fun k _ => by
      simp only [K]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
        (by simp)) (by simp)) (ENNReal.mul_ne_top (by simp) (by simp))
    have hbd : ∀ n : ℕ, M < n → driverLaw (κ := κ) μ (AM M) ≤
        ∑ k, K k / ((n ^ 2 : ℕ) : ℝ≥0∞) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (lt_of_le_of_lt (Nat.zero_le M) hn)
      have hU := ae_fst_eq_of_joint hb hσ hn0 hX (hZ n) hX'a hX'c hXX'
      have hsub : AM M ≤ᵐ[driverLaw (κ := κ) μ]
          (⋃ k, {x | ((n ^ 2 : ℕ) : ℝ≥0∞) ≤ ‖V n k x‖ₑ ^ 2} : Set _) := by
        filter_upwards [hU, hXX'] with x hu hx hxA
        obtain ⟨hA, hT⟩ := hxA
        have he := hA n
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top he)
        have hmT : (m : WithTop ℝ≥0) ≤ (T : ℝ≥0) := hm ▸ he
        have hτ : min (exitTime (Z n) n x) (exitTimeOf X' M x) = m := by
          rw [← hm]; exact min_eq_left (hmT.trans hT.le)
        have hst : stoppedProcess (fun t x => (Z n t x).2)
            (fun x => min (exitTime (Z n) n x) (exitTimeOf X' M x)) T x = (Z n m x).2 := by
          rw [stoppedProcess_eq_stopTime, hτ, stopTime_coe,
            min_eq_right (WithTop.coe_le_coe.1 hmT)]
        have h1 : (n : ℝ) ≤ ‖Z n m x‖ := le_norm_exitTimeOf ((hZ n).continuous x) hm.symm
        have h2 : ‖(Z n m x).1‖ < M := by
          rw [hu.2 m hm.le, ← hx m]
          exact norm_lt_of_lt_exitTimeOf (lt_of_le_of_lt hmT hT)
        have h3 : (n : ℝ) ≤ ‖(Z n m x).2‖ := by
          rw [Prod.norm_def] at h1
          rcases le_max_iff.1 h1 with h | h
          · exact absurd (h.trans_lt h2) (not_lt.2 (by exact_mod_cast hn.le))
          · exact h
        obtain ⟨k, hk⟩ := hℓ _ (hn0.trans_le h3)
        refine mem_iUnion.2 ⟨k, ?_⟩
        show ((n ^ 2 : ℕ) : ℝ≥0∞) ≤ ‖V n k x‖ₑ ^ 2
        simp only [V, hst, Real.enorm_eq_ofReal_abs]
        rw [← ENNReal.ofReal_pow (abs_nonneg _), Nat.cast_pow, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_pow (Nat.cast_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hn0.le (h3.trans hk) 2)
      refine (measure_mono_ae hsub).trans ((measure_iUnion_fintype_le _ _).trans
        (Finset.sum_le_sum fun k _ => ?_))
      have hm : AEMeasurable (fun x => ‖V n k x‖ₑ ^ 2) (driverLaw (κ := κ) μ) := by
        have := aestronglyMeasurable_stoppedProcess (snd_nativeIto (hZ n).sol.1).adapted
          (Eventually.of_forall fun x => continuous_snd.comp ((hZ n).continuous x))
          (((hZ n).stopping).min (isStoppingTime_exitTimeOf hX'a hX'c M)) T
        exact ((ℓ k).continuous.comp_aestronglyMeasurable this).enorm.pow_const 2
      refine (meas_ge_le_lintegral_div hm (by simp; omega) (by simp)).trans ?_
      gcongr
      exact lintegral_sq_snd_le hb hσ hσ₂ hX hX'a hX'c hXX' hn0 (hZ n) hC (ℓ k) T
    have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun k _ =>
      tendsto_div_natSq (K k) (ne_top_of_le_ne_top hK (Finset.single_le_sum
        (f := K) (fun _ _ => bot_le) (Finset.mem_univ k)))
    simp only [Finset.sum_const_zero] at hlim
    exact le_antisymm (ge_of_tendsto hlim ((eventually_gt_atTop M).mono hbd)) bot_le
  have hA : driverLaw (κ := κ) μ A = 0 :=
    measure_mono_null hcov (measure_iUnion_null hAM)
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hA)
  simp only [mem_ofPred_eq, not_exists, not_lt] at hx
  exact hx

end BlockBand.SourceProcess.ComplexConstruct
