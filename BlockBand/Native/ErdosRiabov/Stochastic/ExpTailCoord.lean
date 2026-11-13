module

public import BlockBand.Native.ErdosRiabov.Stochastic.ExpTail
public import BlockBand.SourceProcess.Stochastic.Bridges.Structural

set_option autoImplicit false

/-!
# Exponential maximal tail: coordinates, linear functionals, complex martingales

* `measure_exists_norm_complex_compensated_ge_le`: for two real continuous
  semimartingales (the real and imaginary parts) with martingale parts `N¹`, `N²`, each with
  bracket integral `≤ y` on `{t ≤ T, t ≤ τ}`,
  `Q(∃ t ≤ T, t ≤ τ, λ ≤ |N¹_t + i N²_t|) ≤ 4 exp(-λ²/(4y))`. The zero-drift form for a complex
  process `M` (`Re M`, `Im M` continuous semimartingales with zero drift) is
  `measure_exists_norm_complex_sub_ge_le`: `Q(∃ t ≤ T, t ≤ τ, λ ≤ |M_t - M_0|) ≤ 4 exp(-λ²/(4y))`.
  No joint semimartingale property of `(Re M, Im M)` is needed (union bound at level `λ/√2`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Stochastic
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Bridges
open scoped NNReal ENNReal Matrix

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Coordinate form of the exponential maximal tail.** Let `Y` be a continuous
semimartingale in `ℝ^d` with characteristics `(β, α)`, `i` a coordinate, `τ` a `𝓖`-stopping
time, `T` a deterministic horizon and `y > 0` deterministic with a.s. `∫_0^t α^{ii} ≤ y` for every
`t ≤ T` with `t ≤ τ`. Then for every `λ ≥ 0`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |N^i_t|) ≤ 2 exp(-λ²/(2y))`, `N^i_t = Y^i_t - Y^i_0 - ∫_0^t β^i`. -/
theorem measure_exists_abs_compensated_coord_ge_le {d : ℕ} {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    (i : Fin d) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i i ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ |smCompensated Y β i t ω|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (2 * y)))) := by
  exact measure_exists_abs_compensated_ge_le (H.comp_index fun _ : Fin 1 => i) hτ T hy hA hlam

/-- **Exponential maximal tail for a real linear functional.** Let `Y` be a continuous
semimartingale in `ℝ^d` with characteristics `(β, α)` and `a ∈ ℝ^d` fixed. If a.s.
`∫_0^t ∑_{ij} a_i a_j α^{ij} ≤ y` for every `t ≤ T` with `t ≤ τ` (`y > 0` deterministic), then
for every `λ ≥ 0`: `Q(∃ t ≤ T, t ≤ τ, λ ≤ |∑_i a_i N^i_t|) ≤ 2 exp(-λ²/(2y))`. -/
theorem measure_exists_abs_linear_compensated_ge_le {d : ℕ} {Y β : ℝ≥0 → Ω → Fin d → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} (H : IsContinuousSemimartingale Q 𝓖 Y β α)
    (a : Fin d → ℝ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ}
    (hy : 0 < y)
    (hA : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, ∑ i, ∑ j, a i * a j * α s.toNNReal ω i j ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
        lam ≤ |∑ i, a i * smCompensated Y β i t ω|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (2 * y)))) := by
  have HA := H.affine (Matrix.of fun (_ : Fin 1) j => a j) 0
  have hA' : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, ((Matrix.of fun (_ : Fin 1) j => a j) * α s.toNNReal ω *
        (Matrix.of fun (_ : Fin 1) j => a j)ᵀ) 0 0 ≤ y := by
    filter_upwards [hA] with ω hω t htT htτ
    simpa only [mul_mul_transpose_apply, Matrix.of_apply] using hω t htT htτ
  refine le_trans (measure_mono_ae ?_) (measure_exists_abs_compensated_ge_le HA hτ T hy hA' hlam)
  filter_upwards [H.integrable] with ω hω
  rintro ⟨t, htT, htτ, hlt⟩
  refine ⟨t, htT, htτ, ?_⟩
  rw [smCompensated_affine _ 0 (hω t).1 0]
  simpa only [Matrix.of_apply] using hlt

theorem div_sqrt_two_sq_div {lam y : ℝ} (hy : 0 < y) :
    (lam / √2) ^ 2 / (2 * y) = lam ^ 2 / (4 * y) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- **Complex exponential maximal tail.** Let `Y¹`, `Y²` be continuous
semimartingales in `ℝ¹` with characteristics `(β¹, α¹)`, `(β², α²)` (the real and imaginary
parts; no joint property is assumed), with martingale parts `N^k_t = Y^k_t - Y^k_0 - ∫_0^t β^k`.
If `τ` is a `𝓖`-stopping time, `T` a deterministic horizon and `y > 0` deterministic with a.s.
`∫_0^t α¹ ≤ y` and `∫_0^t α² ≤ y` for every `t ≤ T` with `t ≤ τ`, then for every `λ ≥ 0`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |N¹_t + i N²_t|) ≤ 4 exp(-λ²/(4y))`. -/
theorem measure_exists_norm_complex_compensated_ge_le
    {Y₁ β₁ Y₂ β₂ : ℝ≥0 → Ω → Fin 1 → ℝ} {α₁ α₂ : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
    (H₁ : IsContinuousSemimartingale Q 𝓖 Y₁ β₁ α₁)
    (H₂ : IsContinuousSemimartingale Q 𝓖 Y₂ β₂ α₂)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA₁ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α₁ s.toNNReal ω 0 0 ≤ y)
    (hA₂ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α₂ s.toNNReal ω 0 0 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
        lam ≤ ‖(smCompensated Y₁ β₁ 0 t ω : ℂ) + (smCompensated Y₂ β₂ 0 t ω : ℂ) * Complex.I‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) := by
  have hl : 0 ≤ lam / √2 := div_nonneg hlam (Real.sqrt_nonneg _)
  have h1 := measure_exists_abs_compensated_ge_le H₁ hτ T hy hA₁ hl
  have h2 := measure_exists_abs_compensated_ge_le H₂ hτ T hy hA₂ hl
  rw [div_sqrt_two_sq_div hy] at h1 h2
  have hs : (0 : ℝ) < √2 := by positivity
  calc Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
          lam ≤ ‖(smCompensated Y₁ β₁ 0 t ω : ℂ) + (smCompensated Y₂ β₂ 0 t ω : ℂ) * Complex.I‖}
      ≤ Q ({ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
            lam / √2 ≤ |smCompensated Y₁ β₁ 0 t ω|} ∪
          {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧
            lam / √2 ≤ |smCompensated Y₂ β₂ 0 t ω|}) := by
        refine measure_mono ?_
        rintro ω ⟨t, htT, htτ, hlt⟩
        have hz := Complex.norm_le_sqrt_two_mul_max
          ((smCompensated Y₁ β₁ 0 t ω : ℂ) + (smCompensated Y₂ β₂ 0 t ω : ℂ) * Complex.I)
        have hre : ((smCompensated Y₁ β₁ 0 t ω : ℂ) +
            (smCompensated Y₂ β₂ 0 t ω : ℂ) * Complex.I).re = smCompensated Y₁ β₁ 0 t ω := by
          simp
        have him : ((smCompensated Y₁ β₁ 0 t ω : ℂ) +
            (smCompensated Y₂ β₂ 0 t ω : ℂ) * Complex.I).im = smCompensated Y₂ β₂ 0 t ω := by
          simp
        rw [hre, him] at hz
        have hmax : lam / √2 ≤
            max |smCompensated Y₁ β₁ 0 t ω| |smCompensated Y₂ β₂ 0 t ω| := by
          rw [div_le_iff₀ hs]
          linarith
        rcases le_max_iff.1 hmax with h | h
        · exact Or.inl ⟨t, htT, htτ, h⟩
        · exact Or.inr ⟨t, htT, htτ, h⟩
    _ ≤ _ := measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) +
          2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) := add_le_add h1 h2
    _ = 4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) := by
        rw [← add_mul]
        norm_num

/-- **Complex exponential maximal tail, zero-drift form.** Let `M : ℝ≥0 → Ω → ℂ` be such that
`Re M` and `Im M` are continuous semimartingales in `ℝ¹` with zero drift and bracket densities
`α¹`, `α²`. If `y > 0` is deterministic with a.s. `∫_0^t α¹ ≤ y` and `∫_0^t α² ≤ y` for every
`t ≤ T` with `t ≤ τ`, then for every `λ ≥ 0`:
`Q(∃ t ≤ T, t ≤ τ, λ ≤ |M_t - M_0|) ≤ 4 exp(-λ²/(4y))`. -/
theorem measure_exists_norm_complex_sub_ge_le {M : ℝ≥0 → Ω → ℂ}
    {α₁ α₂ : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ}
    (H₁ : IsContinuousSemimartingale Q 𝓖 (fun t ω _ => (M t ω).re) (fun _ _ => 0) α₁)
    (H₂ : IsContinuousSemimartingale Q 𝓖 (fun t ω _ => (M t ω).im) (fun _ _ => 0) α₂)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (hA₁ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α₁ s.toNNReal ω 0 0 ≤ y)
    (hA₂ : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (t : WithTop ℝ≥0) ≤ τ ω →
      ∫ s in Ioc (0 : ℝ) t, α₂ s.toNNReal ω 0 0 ≤ y)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Q {ω | ∃ t : ℝ≥0, t ≤ T ∧ (t : WithTop ℝ≥0) ≤ τ ω ∧ lam ≤ ‖M t ω - M 0 ω‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (4 * y)))) := by
  refine le_trans (measure_mono ?_)
    (measure_exists_norm_complex_compensated_ge_le H₁ H₂ hτ T hy hA₁ hA₂ hlam)
  rintro ω ⟨t, htT, htτ, hlt⟩
  refine ⟨t, htT, htτ, ?_⟩
  have e : ((smCompensated (fun t ω (_ : Fin 1) => (M t ω).re) (fun _ _ => 0) 0 t ω : ℝ) : ℂ) +
      ((smCompensated (fun t ω (_ : Fin 1) => (M t ω).im) (fun _ _ => 0) 0 t ω : ℝ) : ℂ) *
        Complex.I = M t ω - M 0 ω := by
    apply Complex.ext <;> simp [smCompensated]
  rw [e]
  exact hlt

end BlockBand.Native.ErdosRiabov.Stochastic
