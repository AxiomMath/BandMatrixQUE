module

public import BlockBand.Model.Construction.GaussianIntegrationByParts
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian divergence identity for tangent fields

This file is the real-coordinate layer: for a product of centered Gaussians on `κ → ℝ`,
* `measurePreserving_update`: resampling one coordinate preserves the product law;
* `integral_coord_mul_eq`: `E[x_c f] = v_c E[∂_c f]` when `f` is differentiable along
  coordinate lines at every nonzero point (lines through the origin are null), with Gaussian
  integrability of `f`, `∂_c f` and `x_c f`;
* `integral_sum_partial_eq_zero`: for a tangent field (`Σ_c x_c f_c(x) = 0`) and equal
  variances, `Σ_c E[∂_c f_c] = 0`.
No smoothness at the origin is assumed: degree-one homogeneous fields built from degree-zero
angular functions are differentiable only off `0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.ConeDivergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Resampling coordinate `c` of a product law by an independent copy preserves the law. -/
theorem measurePreserving_update (μ : κ → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (c : κ) :
    MeasurePreserving (fun q : (κ → ℝ) × ℝ => Function.update q.1 c q.2)
      ((Measure.pi μ).prod (μ c)) (Measure.pi μ) := by
  have hmeas : Measurable (fun q : (κ → ℝ) × ℝ => Function.update q.1 c q.2) :=
    measurable_update' (a := c)
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (κ → ℝ) × ℝ => Function.update q.1 c q.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s c Set.univ)) ×ˢ s c := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h c⟩
      by_cases hj : j = c
      · subst hj; simp
      · have := h j
        rw [Function.update_of_ne hj] at this ⊢
        exact this
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = c
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this ⊢
        exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => μ j (s j)) (Finset.mem_univ c),
    ← Finset.mul_prod_erase Finset.univ (fun j => μ j (Function.update s c Set.univ j))
      (Finset.mem_univ c)]
  have hrest : ∏ j ∈ Finset.univ.erase c, μ j (Function.update s c Set.univ j) =
      ∏ j ∈ Finset.univ.erase c, μ j (s j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Function.update_self, measure_univ, one_mul, mul_comm]

omit [DecidableEq κ] in
/-- Under a product law with a nondegenerate Gaussian coordinate `j`, almost surely
`x j ≠ 0`. -/
theorem ae_coord_ne_zero (v : κ → ℝ≥0) (j : κ) (hj : v j ≠ 0) :
    ∀ᵐ x ∂(Measure.pi fun i => gaussianReal 0 (v i)), x j ≠ 0 := by
  have hnull : (gaussianReal 0 (v j)) {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 hj (Real.volume_singleton)
  have hmp : MeasurePreserving (fun x : κ → ℝ => x j)
      (Measure.pi fun i => gaussianReal 0 (v i)) (gaussianReal 0 (v j)) :=
    measurePreserving_eval (fun i => gaussianReal 0 (v i)) j
  rw [ae_iff]
  have : {x : κ → ℝ | ¬ x j ≠ 0} = (fun x : κ → ℝ => x j) ⁻¹' {0} := by
    ext x; simp
  rw [this, hmp.measure_preimage (measurableSet_singleton 0).nullMeasurableSet, hnull]

/-- **Coordinate Gaussian integration by parts off the origin.** Product law
`Π_j N(0, v_j)` on `κ → ℝ`. If `f` has partial derivative `f' x` along coordinate `c` at every
nonzero point `x`, some other coordinate is nondegenerate, and `f`, `f'`, `x_c f` are
integrable, then `E[x_c f] = v_c E[f']`. -/
theorem integral_coord_mul_eq (v : κ → ℝ≥0) (c : κ) (f f' : (κ → ℝ) → ℝ)
    (hother : ∃ j, j ≠ c ∧ v j ≠ 0)
    (hderiv : ∀ x : κ → ℝ, x ≠ 0 → HasDerivAt (fun t => f (Function.update x c t)) (f' x) (x c))
    (hf : Integrable f (Measure.pi fun i => gaussianReal 0 (v i)))
    (hf' : Integrable f' (Measure.pi fun i => gaussianReal 0 (v i)))
    (hcf : Integrable (fun x => x c * f x) (Measure.pi fun i => gaussianReal 0 (v i))) :
    (∫ x, x c * f x ∂(Measure.pi fun i => gaussianReal 0 (v i))) =
      (v c : ℝ) * ∫ x, f' x ∂(Measure.pi fun i => gaussianReal 0 (v i)) := by
  set γ : Measure (κ → ℝ) := Measure.pi fun i => gaussianReal 0 (v i) with hγ
  set μc : Measure ℝ := gaussianReal 0 (v c) with hμc
  have hmp : MeasurePreserving (fun q : (κ → ℝ) × ℝ => Function.update q.1 c q.2)
      (γ.prod μc) γ := measurePreserving_update (fun i => gaussianReal 0 (v i)) c
  -- integrals and integrability transported to the product space
  have htrans : ∀ g : (κ → ℝ) → ℝ, Integrable g γ →
      Integrable (fun q : (κ → ℝ) × ℝ => g (Function.update q.1 c q.2)) (γ.prod μc) ∧
      (∫ x, g x ∂γ) = ∫ q, g (Function.update q.1 c q.2) ∂(γ.prod μc) := by
    intro g hg
    refine ⟨hmp.integrable_comp_of_integrable hg, ?_⟩
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hg.1)
  obtain ⟨hF, eF⟩ := htrans f hf
  obtain ⟨hF', eF'⟩ := htrans f' hf'
  obtain ⟨hCF, eCF⟩ := htrans _ hcf
  rw [eCF, eF', integral_prod _ hCF, integral_prod _ hF', ← integral_const_mul]
  apply integral_congr_ae
  obtain ⟨j, hjc, hj⟩ := hother
  filter_upwards [ae_coord_ne_zero v j hj, hF.prod_right_ae, hF'.prod_right_ae,
    hCF.prod_right_ae] with x hx h1 h2 h3
  simp only [Function.update_self] at h3 ⊢
  have hd : ∀ t : ℝ, HasDerivAt (fun s => f (Function.update x c s))
      (f' (Function.update x c t)) t := by
    intro t
    have hy : Function.update x c t ≠ 0 := by
      intro h0
      apply hx
      have := congrFun h0 j
      rwa [Function.update_of_ne hjc] at this
    have := hderiv (Function.update x c t) hy
    simpa only [Function.update_idem, Function.update_self] using this
  exact BlockBand.Model.Construction.centered_gaussian_integration_by_parts (v c) hd h1 h2 h3

/-- **Divergence identity for tangent fields.** Product law with all variances equal to
`v > 0`, at least two coordinates. If each component `f c` has partial derivative `f' c x`
along coordinate `c` at every nonzero `x`, the field is tangent (`Σ_c x_c f_c(x) = 0`), and
all `f c`, `f' c`, `x_c f_c` are integrable, then `Σ_c E[∂_c f_c] = 0`. -/
theorem integral_sum_partial_eq_zero [Nontrivial κ] (v : ℝ≥0) (hv : v ≠ 0)
    (f f' : κ → (κ → ℝ) → ℝ)
    (hderiv : ∀ c (x : κ → ℝ), x ≠ 0 →
      HasDerivAt (fun t => f c (Function.update x c t)) (f' c x) (x c))
    (htan : ∀ x : κ → ℝ, ∑ c, x c * f c x = 0)
    (hf : ∀ c, Integrable (f c) (Measure.pi fun _ : κ => gaussianReal 0 v))
    (hf' : ∀ c, Integrable (f' c) (Measure.pi fun _ : κ => gaussianReal 0 v))
    (hcf : ∀ c, Integrable (fun x => x c * f c x) (Measure.pi fun _ : κ => gaussianReal 0 v)) :
    (∑ c, ∫ x, f' c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v)) = 0 := by
  have hcoord : ∀ c, (∫ x, x c * f c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v)) =
      (v : ℝ) * ∫ x, f' c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v) := by
    intro c
    obtain ⟨j, hj⟩ := exists_ne c
    exact integral_coord_mul_eq (fun _ => v) c (f c) (f' c) ⟨j, hj, hv⟩ (hderiv c) (hf c)
      (hf' c) (hcf c)
  have hsum : (∑ c, ∫ x, x c * f c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v)) = 0 := by
    rw [← integral_finsetSum _ (fun c _ => hcf c)]
    simp [htan]
  simp_rw [hcoord, ← Finset.mul_sum] at hsum
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  exact (mul_eq_zero.mp hsum).resolve_left hv'

/-- **Divergence identity, general form.** Product law with all variances equal to `v > 0`,
at least two coordinates: `Σ_c E[∂_c f_c] = v⁻¹ E[Σ_c x_c f_c]`. -/
theorem integral_sum_partial_eq [Nontrivial κ] (v : ℝ≥0) (hv : v ≠ 0)
    (f f' : κ → (κ → ℝ) → ℝ)
    (hderiv : ∀ c (x : κ → ℝ), x ≠ 0 →
      HasDerivAt (fun t => f c (Function.update x c t)) (f' c x) (x c))
    (hf : ∀ c, Integrable (f c) (Measure.pi fun _ : κ => gaussianReal 0 v))
    (hf' : ∀ c, Integrable (f' c) (Measure.pi fun _ : κ => gaussianReal 0 v))
    (hcf : ∀ c, Integrable (fun x => x c * f c x) (Measure.pi fun _ : κ => gaussianReal 0 v)) :
    (∑ c, ∫ x, f' c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v)) =
      (v : ℝ)⁻¹ * ∫ x, ∑ c, x c * f c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v) := by
  have hcoord : ∀ c, (∫ x, x c * f c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v)) =
      (v : ℝ) * ∫ x, f' c x ∂(Measure.pi fun _ : κ => gaussianReal 0 v) := by
    intro c
    obtain ⟨j, hj⟩ := exists_ne c
    exact integral_coord_mul_eq (fun _ => v) c (f c) (f' c) ⟨j, hj, hv⟩ (hderiv c) (hf c)
      (hf' c) (hcf c)
  rw [integral_finsetSum _ (fun c _ => hcf c)]
  simp_rw [hcoord, ← Finset.mul_sum]
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp

end BlockBand.Angular.ConeDivergence
