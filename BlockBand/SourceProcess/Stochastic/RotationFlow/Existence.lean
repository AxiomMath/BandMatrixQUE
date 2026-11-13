module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Contraction
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Existence and boundedness of the rotation flow

Matrices carry the Frobenius norm; `Ω = DriverSample S ((Fin N × Fin N) × Fin 2)`,
`P = driverLaw μ`. Coefficients: `r` continuous, symmetric, `≥ 0` and `κ` continuous, `≥ 0` on
`[a,c]`, `a ≤ c`; start time `s` (any real: only the clamped time enters).

* `isRotationFlow_norm_le`: every rotation flow is a.s. a contraction, `‖𝓜_t‖ ≤ ‖1‖` for all `t`.
* `exists_isRotationFlow`: existence. The global solution `Y` of the radially truncated
  equation (`truncCoeff`, `exists_tGlobalSol`) satisfies `‖Y_t‖ ≤ ‖1‖ < R` a.s. by the
  contraction estimate, so off a null set the truncation is inactive; modifying `Y` on that null
  set (`𝓜 = Y` on the good set, `𝓜 = 1` elsewhere) gives a solution of the untruncated equation.

Uniqueness up to indistinguishability, `isRotationFlow_unique`, is proved in the sibling module by
the Gronwall comparison `stoppedProcess_ae_eq_of_lipschitz` (coefficients bounded along the
contracted paths).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

variable {N : ℕ} {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
variable {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}

/-- Shorthand for the sample space. -/
abbrev FlowSample (S : Type*) [MeasurableSpace S] (N : ℕ) :=
  DriverSample S ((Fin N × Fin N) × Fin 2)

/-- **Contraction of every rotation flow.** -/
theorem isRotationFlow_norm_le (hs : ∀ x k l, r x k l = r x l k) (hr : ∀ x k l, 0 ≤ r x k l)
    (hk : ∀ x k, 0 ≤ κ x k) {M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) :
    ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t,
      ‖M t x‖ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ := by
  have h1 := hM.1
  have e1 : (fun (t : ℝ≥0) (x : FlowSample S N) => rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) *
      M t x) = fun (t : ℝ≥0) (x : FlowSample S N) => (fun _ _ => (1 : ℝ)) t x •
        (rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) * M t x) :=
    funext fun t => funext fun x => (one_smul ℝ _).symm
  have e2 : (fun α (t : ℝ≥0) (x : FlowSample S N) => rotationNoise (r (clampTime a c (s + t))) α
      * M t x) = fun α (t : ℝ≥0) (x : FlowSample S N) => (fun _ _ => (1 : ℝ)) t x • (rotationNoise (r (clampTime a c (s + t))) α *
        M t x) := funext fun α => funext fun t => funext fun x => (one_smul ℝ _).symm
  rw [e1, e2] at h1
  filter_upwards [norm_le_of_rotationType (fun t => r (clampTime a c (s + t)))
    (fun t => κ (clampTime a c (s + t))) (fun t => hs _) (fun t => hr _) (fun t => hk _)
    _ (fun _ _ => zero_le_one) (fun _ _ => le_rfl) h1] with x hx t
  rw [← hM.2 x]
  exact hx t

/-- Stopped coefficient functionals bounded along a.s. continuous adapted paths are native
integrands. -/
theorem nativeIntegrand_coeff_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : (Fin N × Fin N) × Fin 2 → ℝ≥0 → E → E}
    (hσ : ∀ a, Continuous fun q : ℝ≥0 × E => σ a q.1 q.2) {X : ℝ≥0 → FlowSample S N → E}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (X t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, Continuous fun t => X t x) {C : ℝ}
    (hC : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ a t, ‖σ a t (X t x)‖ ≤ C)
    (ℓ : E →L[ℝ] ℝ) (T : ℝ≥0) :
    NativeIntegrand μ T (stopIntegrand (fun _ => ⊤)
      (functionalIntegrand ℓ fun a t x => σ a t (X t x))) := by
  intro a
  have hm : AEStronglyMeasurable[rawPredictable S ((Fin N × Fin N) × Fin 2)]
      (fun p : ℝ × FlowSample S N => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)))
      (timeProbMeasure T (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ)) :=
    ℓ.continuous.comp_aestronglyMeasurable (aesm_coeff_comp (hσ a) (aesm_processFun hXa hXc))
  have he : stopIntegrand (fun _ => ⊤) (functionalIntegrand ℓ fun a t x => σ a t (X t x)) a =
      fun p : ℝ × FlowSample S N => ℓ (σ a p.1.toNNReal (X p.1.toNNReal p.2)) := by
    funext p
    simp only [stopIntegrand, le_top, ite_true, functionalIntegrand]
  rw [he]
  refine ⟨hm, MemLp.of_bound (hm.mono (predictableSpace_le _)) (‖ℓ‖ * C) ?_⟩
  filter_upwards [ae_timeProb_of_ae (T := T) hC] with p hp
  exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hp a _) (norm_nonneg _))

/-- **Existence of the rotation flow.** -/
theorem exists_isRotationFlow (hac : a ≤ c) (hrc : ContinuousOn r (Set.Icc a c))
    (hκc : ContinuousOn κ (Set.Icc a c)) (hs : ∀ x k l, r x k l = r x l k)
    (hr : ∀ x k l, 0 ≤ r x k l) (hk : ∀ x k, 0 ≤ κ x k) (s : ℝ) :
    ∃ M, IsRotationFlow μ r κ a c s M := by
  classical
  set cf := truncCoeff (N := N) s hac hrc hκc with hcf
  have hξ : StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ 0]
      (fun _ : FlowSample S N => (1 : Matrix (Fin N) (Fin N) ℂ)) := stronglyMeasurable_const
  obtain ⟨Y, hYsol⟩ := exists_tGlobalSol (μ := μ) cf hξ
  have hY := hYsol.isNativeItoProcess
  have e1 : (fun (t : ℝ≥0) (x : FlowSample S N) => cf.b t (Y t x)) =
      fun (t : ℝ≥0) (x : FlowSample S N) => truncFactor N (Y t x) •
        (rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) * Y t x) :=
    funext fun t => funext fun x => truncCoeff_b_eq s hac hrc hκc t (Y t x)
  have e2 : (fun α (t : ℝ≥0) (x : FlowSample S N) => cf.σ α t (Y t x)) =
      fun α (t : ℝ≥0) (x : FlowSample S N) => truncFactor N (Y t x) •
        (rotationNoise (r (clampTime a c (s + t))) α * Y t x) :=
    funext fun α => funext fun t => funext fun x => truncCoeff_σ_eq s hac hrc hκc α t (Y t x)
  rw [e1, e2] at hY
  have hbd := norm_le_of_rotationType (fun t => r (clampTime a c (s + t)))
    (fun t => κ (clampTime a c (s + t))) (fun _ => hs _) (fun _ => hr _) (fun _ => hk _)
    (fun t x => truncFactor N (Y t x)) (fun _ _ => truncFactor_nonneg _)
    (fun _ _ => truncFactor_le_one _) hY
  obtain ⟨G, hGm, hG0, hGb⟩ := exists_good_set μ hbd
  have hGae : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  have hY0 : ∀ x, Y 0 x = 1 := hYsol.2.2.1
  set M : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ :=
    fun t => G.piecewise (Y t) (fun _ => 1) with hMdef
  have hR : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ truncRadius N :=
    le_add_of_nonneg_right zero_le_one
  have hMb : ∀ t x, ‖M t x‖ ≤ truncRadius N := by
    intro t x
    by_cases hx : x ∈ G
    · simp only [hMdef, Set.piecewise_eq_of_mem _ _ _ hx]
      have := hGb x hx t
      rw [hY0] at this
      exact this.trans hR
    · simp only [hMdef, Set.piecewise_eq_of_notMem _ _ _ hx]
      exact hR
  have hM0 : ∀ x, M 0 x = 1 := by
    intro x
    by_cases hx : x ∈ G
    · simp only [hMdef, Set.piecewise_eq_of_mem _ _ _ hx, hY0]
    · simp only [hMdef, Set.piecewise_eq_of_notMem _ _ _ hx]
  have hMsol : TGlobalSol μ cf (fun _ => 1) M := by
    refine ⟨fun t => ?_, fun x => ?_, hM0, fun T ρ hρ => ?_⟩
    · exact StronglyMeasurable.piecewise (measurableSet_aug_of_full μ hGm hG0 t) (hYsol.1 t)
        stronglyMeasurable_const
    · by_cases hx : x ∈ G
      · have : (fun t => M t x) = fun t => Y t x := by
          funext t
          simp only [hMdef, Set.piecewise_eq_of_mem _ _ _ hx]
        rw [this]
        exact hYsol.2.1 x
      · have : (fun t => M t x) = fun _ => 1 := by
          funext t
          simp only [hMdef, Set.piecewise_eq_of_notMem _ _ _ hx]
        rw [this]
        exact continuous_const
    · refine StoppedIdentity.tcongr ?_ (hYsol.2.2.2 T ρ hρ)
      filter_upwards [hGae] with x hx t _
      simp only [hMdef, Set.piecewise_eq_of_mem _ _ _ hx]
  have hM := hMsol.isNativeItoProcess
  have e3 : (fun (t : ℝ≥0) (x : FlowSample S N) => cf.b t (M t x)) =
      fun (t : ℝ≥0) (x : FlowSample S N) =>
        rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t))) * M t x :=
    funext fun t => funext fun x => truncCoeff_b_of_norm_le s hac hrc hκc (hMb t x)
  have e4 : (fun α (t : ℝ≥0) (x : FlowSample S N) => cf.σ α t (M t x)) =
      fun α (t : ℝ≥0) (x : FlowSample S N) => rotationNoise (r (clampTime a c (s + t))) α * M t x :=
    funext fun α => funext fun t => funext fun x => truncCoeff_σ_of_norm_le s hac hrc hκc (hMb t x)
  rw [e3, e4] at hM
  exact ⟨M, hM, hM0⟩

end BlockBand.SourceProcess.Stochastic.RotationFlow
