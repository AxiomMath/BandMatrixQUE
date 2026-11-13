module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Andréief identity

For a finite measure `ν` and bounded measurable `f, g : ι → α → ℝ`,
`∫ det [f i (x j)] * det [g i (x j)] dν^ι(x) = (card ι)! * det [∫ f i a * g j a dν]` (`andreief`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix

/-- A bounded measurable real function on a space with a finite measure is
integrable. -/
theorem integrable_of_measurable_of_abs_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {h : α → ℝ} (hm : Measurable h) (C : ℝ)
    (hC : ∀ a, |h a| ≤ C) : Integrable h ν :=
  Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- Permutation reindexing behind the Andréief identity: for a finite type `ι`,
a real matrix `G : Matrix ι ι ℝ` and a fixed permutation `σ`,
`∑ τ, sign σ * sign τ * ∏ i, G (σ i) (τ i) = det G`. -/
theorem sum_perm_sign_mul_prod_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (σ : Equiv.Perm ι) :
    ∑ τ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
      ∏ i, G (σ i) (τ i) = G.det := by
  rw [← Equiv.sum_comp (Equiv.mulRight σ), ← det_transpose, det_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hprod : ∏ i, G (σ i) ((ρ * σ) i) = ∏ i, G i (ρ i) :=
    Equiv.prod_comp σ (fun j => G j (ρ j))
  have hsign : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign (ρ * σ) : ℤ) : ℝ) =
      ((Equiv.Perm.sign ρ : ℤ) : ℝ) := by
    rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, mul_comm (((Equiv.Perm.sign ρ : ℤ) : ℝ)),
      ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  simp only [Equiv.coe_mulRight, hprod, transpose_apply, Units.smul_def, zsmul_eq_mul]
  rw [hsign]

/-- Andréief identity. Let `ν` be a finite measure on a measurable space `α`, `ι` a finite type,
and `f g : ι → α → ℝ` measurable and uniformly bounded (`|f i a| ≤ C`, `|g i a| ≤ C'` for all
`i, a`). Then, integrating over `x : ι → α` against the product measure `ν^ι`,
`∫ det [f i (x j)] * det [g i (x j)] = (card ι)! * det [∫ f i a * g j a dν]`. -/
theorem andreief {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → α → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfb : ∃ C, ∀ i a, |f i a| ≤ C) (hgb : ∃ C, ∀ i a, |g i a| ≤ C) :
    ∫ x : ι → α, (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det
        ∂Measure.pi (fun _ => ν) =
      ((Fintype.card ι).factorial : ℝ) * (Matrix.of fun i j => ∫ a, f i a * g j a ∂ν).det := by
  obtain ⟨C, hC⟩ := hfb
  obtain ⟨D, hD⟩ := hgb
  set G : Matrix ι ι ℝ := Matrix.of fun i j => ∫ a, f i a * g j a ∂ν with hG
  -- pointwise expansion of the integrand
  have hpt : ∀ x : ι → α,
      (Matrix.of fun i j => f i (x j)).det * (Matrix.of fun i j => g i (x j)).det =
        ∑ σ : Equiv.Perm ι, ∑ τ : Equiv.Perm ι,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            ∏ i, (f (σ i) (x i) * g (τ i) (x i)) := by
    intro x
    rw [det_apply, det_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul, of_apply, Finset.prod_mul_distrib]
    ring
  have hint : ∀ σ τ : Equiv.Perm ι, Integrable
      (fun x : ι → α => ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ∏ i, (f (σ i) (x i) * g (τ i) (x i))) (Measure.pi fun _ => ν) := by
    intro σ τ
    refine Integrable.const_mul (Integrable.fintype_prod (𝕜 := ℝ) (μ := fun _ => ν)
      (f := fun i a => f (σ i) a * g (τ i) a) fun i => ?_) _
    refine integrable_of_measurable_of_abs_le ((hf _).mul (hg _)) (C * D) fun a => ?_
    rw [abs_mul]
    exact mul_le_mul (hC _ _) (hD _ _) (abs_nonneg _) ((abs_nonneg _).trans (hC (σ i) a))
  have hI : ∀ σ τ : Equiv.Perm ι,
      ∫ x : ι → α, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
        ∏ i, (f (σ i) (x i) * g (τ i) (x i)) ∂Measure.pi (fun _ => ν) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) * ∏ i, G (σ i) (τ i) := by
    intro σ τ
    rw [integral_const_mul,
      integral_fintype_prod_eq_prod (fun i a => f (σ i) a * g (τ i) a)]
    simp [hG]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => hint σ τ]
  simp_rw [integral_finsetSum _ fun τ _ => hint _ τ, hI, sum_perm_sign_mul_prod_eq_det]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

end BlockBand.Endpoints
