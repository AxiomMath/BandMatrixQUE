module

public import BlockBand.SourceProcess.PhysApprox.B3BirthMDiag
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Tools for the newborn Gram overlaps

Resampling, Gaussian and Cauchy–Schwarz bounds used for the overlaps of a newborn Gram column:


* `lintegral_pi_update`: resampling one coordinate of a product law,
  `∫ f = ∫∫ f(x[i ↦ a]) dρ(a)`.
* `lintegral_dot_le`: for `a ~ CN(0, I)`, `E|⟨w, a⟩| ≤ ‖w‖`.
* `norm_dot_le`: Cauchy–Schwarz `|⟨u, v⟩| ≤ ‖u‖‖v‖`.
* `re_dot_mulVec_le`: `Re⟨u, Yu⟩ ≤ ‖Y‖_HS ‖u‖²`, `‖Y‖²_HS = Re Tr YYᴴ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthM

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess.ClosingLeak
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal ComplexConjugate

/-- **Resampling one coordinate of a product law.** -/
theorem lintegral_pi_update {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*}
    [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ] (i : ι)
    {f : (ι → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂Measure.pi (fun _ => ρ) =
      ∫⁻ x, ∫⁻ a, f (Function.update x i a) ∂ρ ∂Measure.pi (fun _ => ρ) := by
  set g : (ι → X) → ℝ≥0∞ := fun x => ∫⁻ a, f (Function.update x i a) ∂ρ
  have hg' : g = ∫⋯∫⁻_{i}, f ∂(fun _ => ρ) :=
    (lmarginal_singleton (μ := fun _ : ι => ρ) f i).symm
  have hg : Measurable g := by rw [hg']; exact hf.lmarginal _
  refine lintegral_eq_of_lmarginal_eq {i} hf hg ?_
  rw [lmarginal_singleton, lmarginal_singleton]
  funext x
  simp only [Function.update_idem, lintegral_const, measure_univ, mul_one]

variable {ι : Type*} [Fintype ι]

theorem norm_dot_le (u v : ι → ℂ) : ‖star u ⬝ᵥ v‖ ≤ l2 u * l2 v := by
  refine (norm_sum_le _ _).trans ?_
  simp only [Pi.star_apply, norm_mul, norm_star]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- The row matrix of `w`: `(row w) *ᵥ a = ⟨w, a⟩`. -/
def rowOf (w : ι → ℂ) : Matrix Unit ι ℂ := Matrix.of fun _ b => star (w b)

theorem rowOf_mulVec (w a : ι → ℂ) (x : Unit) : (rowOf w *ᵥ a) x = star w ⬝ᵥ a := by
  simp [rowOf, mulVec, dotProduct]

theorem l2_rowOf_mulVec (w a : ι → ℂ) : l2 (rowOf w *ᵥ a) = ‖star w ⬝ᵥ a‖ := by
  simp only [l2, Fintype.univ_unit, Finset.sum_singleton, rowOf_mulVec]
  exact Real.sqrt_sq (norm_nonneg _)

theorem trace_rowOf (w : ι → ℂ) : ((rowOf w)ᴴ * rowOf w).trace.re = l2 w ^ 2 := by
  rw [l2_sq_eq_sum]
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, rowOf, of_apply,
    Fintype.univ_unit, Finset.sum_singleton, star_star, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **A Gaussian linear functional**: `E|⟨w, a⟩| ≤ ‖w‖` for `a ~ CN(0, I_W)`. -/
theorem lintegral_dot_le {W : ℕ} (w : Fin W → ℂ) :
    ∫⁻ a, ENNReal.ofReal ‖star w ⬝ᵥ a‖ ∂circularVectorLaw (Fin W) ≤ ENNReal.ofReal (l2 w) := by
  have hm : Measurable fun a : Fin W → ℂ => l2 (rowOf w *ᵥ a) ^ 2 :=
    (continuous_l2.measurable.comp (RawTag.measurable_mulVec' measurable_const
      measurable_id)).pow_const 2
  have hpt : ∀ a : Fin W → ℂ, ‖star w ⬝ᵥ a‖ = Real.sqrt (l2 (rowOf w *ᵥ a) ^ 2) := fun a => by
    rw [Real.sqrt_sq (l2_nonneg _), l2_rowOf_mulVec]
  simp_rw [hpt]
  refine (lintegral_sqrt_le hm fun _ => sq_nonneg _).trans (le_of_eq ?_)
  rw [lintegral_l2_sq_mulVec, trace_rowOf, ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _)
    (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_sq (l2_nonneg _)]

/-- `Re⟨u, Yu⟩ ≤ ‖Y‖_HS ‖u‖²`. -/
theorem re_dot_mulVec_le [DecidableEq ι] (Y : Matrix ι ι ℂ) (u : ι → ℂ) :
    (star u ⬝ᵥ (Y *ᵥ u)).re ≤ Real.sqrt (Y * Yᴴ).trace.re * l2 u ^ 2 := by
  have hY : (Y * Yᴴ).trace.re = ∑ p : ι × ι, ‖Y p.1 p.2‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hu : ∑ p : ι × ι, (‖u p.1‖ * ‖u p.2‖) ^ 2 = (l2 u ^ 2) ^ 2 := by
    rw [l2_sq_eq_sum, sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl fun p _ => by ring
  calc (star u ⬝ᵥ (Y *ᵥ u)).re ≤ ‖star u ⬝ᵥ (Y *ᵥ u)‖ := Complex.re_le_norm _
    _ ≤ ∑ p : ι × ι, ‖Y p.1 p.2‖ * (‖u p.1‖ * ‖u p.2‖) := by
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
        refine (norm_sum_le _ _).trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [norm_mul, norm_mul, norm_star]; ring
    _ ≤ Real.sqrt (∑ p : ι × ι, ‖Y p.1 p.2‖ ^ 2) *
          Real.sqrt (∑ p : ι × ι, (‖u p.1‖ * ‖u p.2‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by rw [← hY, hu, Real.sqrt_sq (sq_nonneg _)]

/-!
## Resampling the newborn probe
-/

section Resample

variable {W : ℕ}

/-- Resample the probe of tag `i`. -/
def updProbe {np : ℕ} (i : Fin np) (y : ProbedPath W np × ℝ) (a : Fin W → ℂ) :
    ProbedPath W np × ℝ :=
  ((y.1.1, Function.update y.1.2 i a), y.2)

theorem measurable_updProbe {np : ℕ} (i : Fin np) :
    Measurable fun p : (ProbedPath W np × ℝ) × (Fin W → ℂ) => updProbe i p.1 p.2 :=
  ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_update'.comp ((measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd))).prodMk (measurable_snd.comp measurable_fst)

/-- **Resampling the probe of tag `i` under the closed law.** -/
theorem lintegral_closedLaw_update (b : ℝ) {np : ℕ} (i : Fin np)
    {G : ProbedPath W np × ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G y ∂B3.closedLaw b W np =
      ∫⁻ y, ∫⁻ a, G (updProbe i y a) ∂circularVectorLaw (Fin W) ∂B3.closedLaw b W np := by
  have hU : Measurable fun p : (ProbedPath W np × ℝ) × (Fin W → ℂ) => G (updProbe i p.1 p.2) :=
    hG.comp (measurable_updProbe i)
  have hU1 : Measurable fun y : ProbedPath W np × ℝ =>
      ∫⁻ a, G (updProbe i y a) ∂circularVectorLaw (Fin W) := hU.lintegral_prod_right'
  simp only [B3.closedLaw, probedPathLaw]
  rw [lintegral_prod _ hG.aemeasurable, lintegral_prod _ hU1.aemeasurable,
    lintegral_prod _ (hG.lintegral_prod_right' (ν := phaseLaw)).aemeasurable,
    lintegral_prod _ (hU1.lintegral_prod_right' (ν := phaseLaw)).aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hH : Measurable fun g : Fin np → Fin W → ℂ => ∫⁻ θ, G ((ω, g), θ) ∂phaseLaw :=
    (hG.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).lintegral_prod_right'
  rw [lintegral_pi_update (circularVectorLaw (Fin W)) i hH]
  refine lintegral_congr fun g => ?_
  refine (lintegral_lintegral_swap ?_).symm
  have hm : Measurable fun q : ℝ × (Fin W → ℂ) => G ((ω, Function.update g i q.2), q.1) :=
    hG.comp ((measurable_const.prodMk (measurable_update'.comp (measurable_const.prodMk
      measurable_snd))).prodMk measurable_fst)
  exact hm.aemeasurable

end Resample

end BlockBand.SourceProcess.PhysApprox.B3.BirthM
