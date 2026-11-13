module

public import BlockBand.SourceProcess.Stochastic.Dyson.GUEMoments
public import BlockBand.SourceProcess.Stochastic.Dyson.GapStop

/-!
# Dyson Brownian motion: coordinate martingales of the Hermitian Brownian motion

In the orthonormal coordinates `hermCoord`, restarted at any time `s`,
the increments `W_t^x = hermCoord (G_{s+t} - G_s) x` satisfy, for the shifted filtration
`u ↦ 𝓖_{s+u}`:
* `W^x` is a martingale;
* `W^x W^y - t δ_xy / N` is a martingale

(`martingale_coordIncr`, `martingale_coordIncr_mul`, which use the lemmas of this file).

Only the fields `adapted`, `indep`, `law` of `IsHermitianBrownian` are used (independence of
increments from the past and their GUE law), through `integral_mul_increment` (factorisation of
`E[X g(G_t - G_r)]` for `𝓖_r`-measurable `X`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ}

theorem hermCoord_add (A B : Matrix (Fin N) (Fin N) ℂ) (x : Fin N × Fin N) :
    hermCoord N (A + B) x = hermCoord N A x + hermCoord N B x := by
  simp [hermCoord, Matrix.mul_add, Matrix.trace_add]

theorem continuous_hermCoord (x : Fin N × Fin N) :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ => hermCoord N H x := by
  unfold hermCoord
  refine Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}

theorem measurable_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t u : ℝ≥0} (hr : r ≤ u)
    (ht : t ≤ u) : Measurable[𝓖 u] fun ω => G t ω - G r ω :=
  ((hG.adapted t).mono (𝓖.mono ht) le_rfl).sub ((hG.adapted r).mono (𝓖.mono hr) le_rfl)

theorem measurable_increment' (hG : IsHermitianBrownian Q 𝓖 N G) (r t : ℝ≥0) :
    Measurable fun ω => G t ω - G r ω :=
  ((hG.adapted t).mono (𝓖.le t) le_rfl).sub ((hG.adapted r).mono (𝓖.le r) le_rfl)

/-- Factorisation through the independence of increments:
`E[X g(G_t - G_r)] = E[X] E[g(G_t - G_r)]` for `𝓖_r`-measurable `X`. -/
theorem integral_mul_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    {X : Ω → ℝ} (hX : Measurable[𝓖 r] X) {g : Matrix (Fin N) (Fin N) ℂ → ℝ} (hg : Measurable g) :
    ∫ ω, X ω * g (G t ω - G r ω) ∂Q = (∫ ω, X ω ∂Q) * ∫ ω, g (G t ω - G r ω) ∂Q := by
  have hind : IndepFun X (fun ω => g (G t ω - G r ω)) Q := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hG.indep r t hrt).symm
      (measurable_iff_comap_le.mp hX)) ?_
    change MeasurableSpace.comap (g ∘ fun ω => G t ω - G r ω) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hg)
  exact IndepFun.integral_fun_mul_eq_mul_integral hind
    (hX.mono (𝓖.le r) le_rfl).aestronglyMeasurable
    (hg.comp (measurable_increment' hG r t)).aestronglyMeasurable

theorem integrable_mul_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    {X : Ω → ℝ} (hX : Measurable[𝓖 r] X) (hXi : Integrable X Q)
    {g : Matrix (Fin N) (Fin N) ℂ → ℝ} (hg : Measurable g)
    (hgi : Integrable (fun ω => g (G t ω - G r ω)) Q) :
    Integrable (fun ω => X ω * g (G t ω - G r ω)) Q := by
  have hind : IndepFun X (fun ω => g (G t ω - G r ω)) Q := by
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (hG.indep r t hrt).symm
      (measurable_iff_comap_le.mp hX)) ?_
    change MeasurableSpace.comap (g ∘ fun ω => G t ω - G r ω) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hg)
  exact hind.integrable_mul hXi hgi

theorem integral_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    {g : Matrix (Fin N) (Fin N) ℂ → ℝ} (hg : Measurable g) :
    ∫ ω, g (G t ω - G r ω) ∂Q = ∫ Z, g Z ∂gueIncrementLaw N (t - r) :=
  (hG.law r t hrt).integral_comp hg.aestronglyMeasurable

theorem integrable_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    {g : Matrix (Fin N) (Fin N) ℂ → ℝ} (hgi : Integrable g (gueIncrementLaw N (t - r))) :
    Integrable (fun ω => g (G t ω - G r ω)) Q :=
  (hG.law r t hrt).integrable_comp hgi

/-- Set integrals of increments factorise: `∫_A g(G_t - G_r) = Q(A) E g(G_t - G_r)`. -/
theorem setIntegral_increment (hG : IsHermitianBrownian Q 𝓖 N G) {r t : ℝ≥0} (hrt : r ≤ t)
    {A : Set Ω} (hA : MeasurableSet[𝓖 r] A) {g : Matrix (Fin N) (Fin N) ℂ → ℝ}
    (hg : Measurable g) :
    ∫ ω in A, g (G t ω - G r ω) ∂Q = Q.real A * ∫ ω, g (G t ω - G r ω) ∂Q := by
  have hAm : MeasurableSet A := 𝓖.le r A hA
  have e : ∫ ω in A, g (G t ω - G r ω) ∂Q =
      ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * g (G t ω - G r ω) ∂Q := by
    rw [← integral_indicator hAm]
    congr 1; funext ω
    by_cases h : ω ∈ A <;> simp [h]
  have h1 : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂Q = Q.real A := by
    rw [integral_indicator hAm]; simp
  rw [e, integral_mul_increment hG hrt (measurable_const.indicator hA) hg, h1]

end BlockBand.SourceProcess.Stochastic.Dyson
