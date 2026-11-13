module
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Forms
public import BlockBand.SourceProcess.Stochastic.RotationFlow.TExport
public import BlockBand.SourceProcess.Stochastic.SDE.Truncation
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Clamped coefficients of the rotation flow and their radial truncation

Matrices carry the Frobenius norm. For rates `r` and damping `κ` continuous on `[a,c]`
(`a ≤ c`) and a start time `s`, the coefficients along the flow time `t ≥ 0` are
`driftAt t = rotationDrift (r x) (κ x)` and `noiseAt α t = rotationNoise (r x) α` at the clamped
time `x = clampTime a c (s + t) ∈ [a,c]`. They are continuous in `t` and uniformly bounded
(`exists_coeff_bound`, compactness of `[a,c]`).

`truncCoeff`: the time-dependent coefficients `b(t, M) = driftAt t · π_R M`,
`σ_α(t, M) = noiseAt α t · π_R M` (`π_R` the radial retraction, `R = ‖1‖ + 1`) form a
`TLipCoeff`; since `π_R M = λ M` with `λ = R / max R ‖M‖ ∈ (0, 1]`, they keep the structure used
by the contraction estimate (`truncCoeff_b_eq`, `truncCoeff_σ_eq`).
-/

namespace BlockBand.SourceProcess.Stochastic.RotationFlow
open Matrix BlockBand.Internal.Contracts.TransmissionFlow
open scoped NNReal BigOperators

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ}

theorem clampTime_mem {a c : ℝ} (hac : a ≤ c) (x : ℝ) : clampTime a c x ∈ Set.Icc a c :=
  ⟨le_max_left _ _, max_le hac (min_le_right _ _)⟩

theorem clampTime_of_mem {a c x : ℝ} (hx : x ∈ Set.Icc a c) : clampTime a c x = x := by
  rw [clampTime, min_eq_left hx.2, max_eq_right hx.1]

theorem continuous_clampTime (a c : ℝ) : Continuous (clampTime a c) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuous_clamped {X : Type*} [TopologicalSpace X] {f : ℝ → X} {a c : ℝ} (hac : a ≤ c)
    (hf : ContinuousOn f (Set.Icc a c)) (s : ℝ) :
    Continuous fun t : ℝ≥0 => f (clampTime a c (s + t)) :=
  hf.comp_continuous ((continuous_clampTime a c).comp (continuous_const.add NNReal.continuous_coe))
    fun _ => clampTime_mem hac _

theorem continuous_rotationDrift :
    Continuous fun p : (Fin N → Fin N → ℝ) × (Fin N → ℝ) => rotationDrift p.1 p.2 := by
  unfold rotationDrift
  refine Continuous.matrix_diagonal (continuous_pi fun k => ?_)
  refine Complex.continuous_ofReal.comp (continuous_const.mul ?_)
  refine (continuous_finsetSum _ fun m _ => ?_).add ?_
  · exact (continuous_apply m).comp ((continuous_apply k).comp continuous_fst)
  · exact (continuous_apply k).comp continuous_snd

theorem continuous_rotationNoise (α : (Fin N × Fin N) × Fin 2) :
    Continuous fun r : Fin N → Fin N → ℝ => rotationNoise r α := by
  unfold rotationNoise
  by_cases h : α.1.1 < α.1.2
  · simp only [h, ite_true]
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      ((((continuous_apply α.1.2).comp (continuous_apply α.1.1))).div_const 2))).smul
      continuous_const
  · simp only [h, ite_false]
    exact continuous_const

variable (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (a c s : ℝ)

/-- The drift matrix along the flow time `t`. -/
def driftAt (t : ℝ≥0) : Matrix (Fin N) (Fin N) ℂ :=
  rotationDrift (r (clampTime a c (s + t))) (κ (clampTime a c (s + t)))

/-- The noise matrices along the flow time `t`. -/
def noiseAt (α : (Fin N × Fin N) × Fin 2) (t : ℝ≥0) : Matrix (Fin N) (Fin N) ℂ :=
  rotationNoise (r (clampTime a c (s + t))) α

variable {r κ a c}

theorem continuous_driftAt (hac : a ≤ c) (hr : ContinuousOn r (Set.Icc a c))
    (hκ : ContinuousOn κ (Set.Icc a c)) : Continuous (driftAt r κ a c s) := by
  have h := (continuous_rotationDrift (N := N)).comp
    ((continuous_clamped hac hr s).prodMk (continuous_clamped hac hκ s))
  exact h

theorem continuous_noiseAt (hac : a ≤ c) (hr : ContinuousOn r (Set.Icc a c))
    (α : (Fin N × Fin N) × Fin 2) : Continuous (noiseAt r a c s α) := by
  have h := (continuous_rotationNoise α).comp (continuous_clamped hac hr s)
  exact h

/-- Uniform bound on the clamped coefficients. -/
theorem exists_coeff_bound (hac : a ≤ c) (hr : ContinuousOn r (Set.Icc a c))
    (hκ : ContinuousOn κ (Set.Icc a c)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s t, ‖driftAt r κ a c s t‖ ≤ K ∧ ∀ α, ‖noiseAt r a c s α t‖ ≤ K := by
  have hc1 := (continuous_rotationDrift (N := N)).comp_continuousOn (hr.prodMk hκ)
  have hc2 := fun α : (Fin N × Fin N) × Fin 2 => (continuous_rotationNoise α).comp_continuousOn hr
  obtain ⟨K1, hK1⟩ := (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn hc1
  have hK2 := fun α : (Fin N × Fin N) × Fin 2 =>
    (isCompact_Icc (a := a) (b := c)).exists_bound_of_continuousOn (hc2 α)
  choose K2 hK2 using hK2
  refine ⟨max K1 0 + ∑ α, max (K2 α) 0, add_nonneg (le_max_right _ _)
    (Finset.sum_nonneg fun _ _ => le_max_right _ _), fun s t => ⟨?_, fun α => ?_⟩⟩
  · exact (hK1 _ (clampTime_mem hac _)).trans ((le_max_left _ _).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => le_max_right _ _)))
  · exact (hK2 α _ (clampTime_mem hac _)).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (f := fun α => max (K2 α) 0) (fun _ _ => le_max_right _ _)
        (Finset.mem_univ α)).trans (le_add_of_nonneg_left (le_max_right _ _))))

/-- Left multiplication by a matrix of norm `≤ K` is `K`-Lipschitz. -/
theorem lipschitzWith_mul_left {A : Matrix (Fin N) (Fin N) ℂ} {K : ℝ} (hA : ‖A‖ ≤ K) :
    LipschitzWith K.toNNReal fun M : Matrix (Fin N) (Fin N) ℂ => A * M := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← Matrix.mul_sub]
  exact (frobenius_norm_mul _ _).trans (mul_le_mul_of_nonneg_right
    (hA.trans (Real.le_coe_toNNReal K)) (norm_nonneg _))

/-- The truncation radius `R = ‖1‖ + 1`. -/
def truncRadius (N : ℕ) : ℝ := ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ + 1

theorem truncRadius_pos : 0 < truncRadius N := by
  unfold truncRadius
  positivity

variable (hac : a ≤ c) (hr : ContinuousOn r (Set.Icc a c)) (hκ : ContinuousOn κ (Set.Icc a c))

/-- The radially truncated, time-dependent coefficients of the rotation flow. -/
def truncCoeff : TLipCoeff ((Fin N × Fin N) × Fin 2) (Matrix (Fin N) (Fin N) ℂ) where
  b t M := driftAt r κ a c s t * SDE.radialRetraction (truncRadius N) M
  σ α t M := noiseAt r a c s α t * SDE.radialRetraction (truncRadius N) M
  K := (exists_coeff_bound hac hr hκ).choose.toNNReal * 2
  C := (exists_coeff_bound hac hr hκ).choose * truncRadius N
  cont_b := ((continuous_driftAt s hac hr hκ).comp continuous_fst).matrix_mul
    ((SDE.lipschitzWith_radialRetraction truncRadius_pos).continuous.comp continuous_snd)
  cont_σ α := ((continuous_noiseAt s hac hr α).comp continuous_fst).matrix_mul
    ((SDE.lipschitzWith_radialRetraction truncRadius_pos).continuous.comp continuous_snd)
  lip_b t := (lipschitzWith_mul_left ((exists_coeff_bound hac hr hκ).choose_spec.2 s t).1).comp
    (SDE.lipschitzWith_radialRetraction truncRadius_pos)
  lip_σ α t := (lipschitzWith_mul_left
    (((exists_coeff_bound hac hr hκ).choose_spec.2 s t).2 α)).comp
    (SDE.lipschitzWith_radialRetraction truncRadius_pos)
  bd_b t M := (frobenius_norm_mul _ _).trans (mul_le_mul
    ((exists_coeff_bound hac hr hκ).choose_spec.2 s t).1
    (SDE.norm_radialRetraction_le truncRadius_pos.le M) (norm_nonneg _)
    (exists_coeff_bound hac hr hκ).choose_spec.1)
  bd_σ α t M := (frobenius_norm_mul _ _).trans (mul_le_mul
    (((exists_coeff_bound hac hr hκ).choose_spec.2 s t).2 α)
    (SDE.norm_radialRetraction_le truncRadius_pos.le M) (norm_nonneg _)
    (exists_coeff_bound hac hr hκ).choose_spec.1)

/-- The truncation factor `λ(M) = R / max R ‖M‖`. -/
def truncFactor (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  truncRadius N / max (truncRadius N) ‖M‖

theorem truncFactor_nonneg (M : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ truncFactor N M :=
  div_nonneg truncRadius_pos.le (le_max_of_le_left truncRadius_pos.le)

theorem truncFactor_le_one (M : Matrix (Fin N) (Fin N) ℂ) : truncFactor N M ≤ 1 :=
  div_le_one_of_le₀ (le_max_left _ _) (le_max_of_le_left truncRadius_pos.le)

theorem truncCoeff_b_eq (t : ℝ≥0) (M : Matrix (Fin N) (Fin N) ℂ) :
    (truncCoeff s hac hr hκ).b t M = truncFactor N M • (driftAt r κ a c s t * M) := by
  show driftAt r κ a c s t * ((truncRadius N / max (truncRadius N) ‖M‖) • M) = _
  rw [Matrix.mul_smul]
  rfl

theorem truncCoeff_σ_eq (α : (Fin N × Fin N) × Fin 2) (t : ℝ≥0) (M : Matrix (Fin N) (Fin N) ℂ) :
    (truncCoeff s hac hr hκ).σ α t M = truncFactor N M • (noiseAt r a c s α t * M) := by
  show noiseAt r a c s α t * ((truncRadius N / max (truncRadius N) ‖M‖) • M) = _
  rw [Matrix.mul_smul]
  rfl

theorem truncCoeff_b_of_norm_le {t : ℝ≥0} {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : ‖M‖ ≤ truncRadius N) : (truncCoeff s hac hr hκ).b t M = driftAt r κ a c s t * M := by
  show driftAt r κ a c s t * SDE.radialRetraction (truncRadius N) M = _
  rw [SDE.radialRetraction_of_norm_le hM]

theorem truncCoeff_σ_of_norm_le {α : (Fin N × Fin N) × Fin 2} {t : ℝ≥0}
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : ‖M‖ ≤ truncRadius N) :
    (truncCoeff s hac hr hκ).σ α t M = noiseAt r a c s α t * M := by
  show noiseAt r a c s α t * SDE.radialRetraction (truncRadius N) M = _
  rw [SDE.radialRetraction_of_norm_le hM]

end BlockBand.SourceProcess.Stochastic.RotationFlow
