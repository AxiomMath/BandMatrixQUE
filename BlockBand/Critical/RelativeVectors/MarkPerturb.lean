module

public import BlockBand.Critical.RelativeVectors.MarkedLaplace
public import BlockBand.Critical.RelativeVectors.ChainRule
public import BlockBand.Critical.Herglotz.GaussianQuad

/-!
# The Gaussian mark average after a frame change

The bound `|ψ_S - ψ| ≲ K ‖S^{1/2} - I‖ E‖g‖`, here in the equivalent product form on
`I_L(x) = ∫ e^{-φ(x, L g)} γ_r(dg)` (no logarithm is needed).

*Law.* `γ_r = circularVectorLaw (Fin r)`. *Norms.* sup norm on `ℂ^r`, entrywise moduli of
`L - I`.

* `integrable_norm_circular`: `E‖g‖ < ∞` (`gaussNormMean r = E‖g‖`), from the coordinate moments
  `Herglotz.memLp_circularVectorLaw_apply`.
* `IsC2Bounded.abs_sub_le`: a bounded-`C²` function with bound `K` is `K`-Lipschitz.
* `markAverageL_mem`, `markAverageL_eq_one`: `0 ≤ I_L ≤ 1`, `I_L(x) = 1` for `|x| > R`.
* `abs_markAverageL_sub_le`: if `|(L - I)_{ij}| ≤ β` then `|I_L(x) - I(x)| ≤ K rβ E‖g‖`,
  uniformly in `x`.
* `abs_prod_sub_prod_le`: `|Π a_i - Π b_i| ≤ Σ |a_i - b_i|` for `a_i, b_i ∈ [0,1]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm

variable {r : ℕ}

theorem integrable_norm_circular (r : ℕ) :
    Integrable (fun g : Fin r → ℂ => ‖g‖) (circularVectorLaw (Fin r)) := by
  have hcoord : ∀ a : Fin r, Integrable (fun g : Fin r → ℂ => ‖g a‖) (circularVectorLaw (Fin r)) :=
    fun a => (memLp_one_iff_integrable.1
      (BlockBand.Critical.Herglotz.memLp_circularVectorLaw_apply (p := 1) ENNReal.one_ne_top a)).norm
  refine Integrable.mono' (g := fun g : Fin r → ℂ => ∑ a, ‖g a‖)
    (integrable_finsetSum Finset.univ fun a _ => hcoord a)
    continuous_norm.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_norm]
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)).2 fun a => ?_
  exact Finset.single_le_sum (f := fun a => ‖g a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ a)

/-- `E‖g‖` under the standard circular Gaussian on `ℂ^r` (sup norm). -/
def gaussNormMean (r : ℕ) : ℝ := ∫ g, ‖g‖ ∂circularVectorLaw (Fin r)

theorem gaussNormMean_nonneg (r : ℕ) : 0 ≤ gaussNormMean r :=
  integral_nonneg fun _ => norm_nonneg _

/-- A bounded-`C²` function with bound `K` is `K`-Lipschitz (mean value theorem). -/
theorem IsC2Bounded.abs_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {K : ℝ}
    {f : X → ℝ} (hf : IsC2Bounded K f) (w w' : X) : |f w - f w'| ≤ K * ‖w - w'‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hf.contDiff.differentiable (by norm_num)).differentiableAt)
    (fun x _ => hf.deriv_bound x) (Set.mem_univ w') (Set.mem_univ w)
  rwa [Real.norm_eq_abs] at h

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : -(b - a) + 1 ≤ Real.exp (-(b - a)) := Real.add_one_le_exp _
  have h4 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 < Real.exp (-a) := Real.exp_pos _
  rw [h2]
  nlinarith

/-- `I_L(x) = ∫ e^{-φ(x, L g)} γ_r(dg)`: the Gaussian mark average after the frame change
`z ↦ L z`. -/
def markAverageL (r : ℕ) (φ : ℝ × (Fin r → ℂ) → ℝ) (L : Matrix (Fin r) (Fin r) ℂ) (x : ℝ) : ℝ :=
  ∫ g, Real.exp (-φ (x, L *ᵥ g)) ∂circularVectorLaw (Fin r)

theorem markAverageL_one (φ : ℝ × (Fin r → ℂ) → ℝ) : markAverageL r φ 1 = markAverage r φ := by
  funext x; simp [markAverageL, markAverage]

theorem continuous_exp_neg_L {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (L : Matrix (Fin r) (Fin r) ℂ) (x : ℝ) :
    Continuous (fun g : Fin r → ℂ => Real.exp (-φ (x, L *ᵥ g))) :=
  Real.continuous_exp.comp ((hφ.continuous.comp
    (continuous_const.prodMk (matCLM L).continuous)).neg)

theorem integrable_exp_neg_L {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (L : Matrix (Fin r) (Fin r) ℂ) (x : ℝ) :
    Integrable (fun g : Fin r → ℂ => Real.exp (-φ (x, L *ᵥ g))) (circularVectorLaw (Fin r)) := by
  refine Integrable.of_bound (C := 1) (continuous_exp_neg_L hφ L x).aestronglyMeasurable ?_
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))

theorem markAverageL_mem {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (L : Matrix (Fin r) (Fin r) ℂ) (x : ℝ) : 0 ≤ markAverageL r φ L x ∧ markAverageL r φ L x ≤ 1 := by
  refine ⟨integral_nonneg fun _ => (Real.exp_pos _).le, ?_⟩
  have h : markAverageL r φ L x ≤ ∫ _g, (1 : ℝ) ∂circularVectorLaw (Fin r) :=
    integral_mono (integrable_exp_neg_L hφ L x) (integrable_const _) fun g =>
      Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))
  simpa using h

theorem markAverageL_eq_one {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (L : Matrix (Fin r) (Fin r) ℂ) {x : ℝ} (hx : R < |x|) : markAverageL r φ L x = 1 := by
  simp [markAverageL, hφ.support x _ hx]

/-- **Frame change of the mark average.** If `|(L - I)_{ij}| ≤ β` for all `i, j`, then
`|I_L(x) - I(x)| ≤ K · rβ · E‖g‖` for every `x`. -/
theorem abs_markAverageL_sub_le {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (L : Matrix (Fin r) (Fin r) ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hL : ∀ i j, ‖(L - 1) i j‖ ≤ β) (x : ℝ) :
    |markAverageL r φ L x - markAverage r φ x| ≤ K * (r * β) * gaussNormMean r := by
  have hK : 0 ≤ K := (hφ.c2 x).nonneg
  unfold markAverageL markAverage gaussNormMean
  rw [← integral_sub (integrable_exp_neg_L hφ L x) (integrable_exp_neg hφ x)]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    ((integrable_norm_circular r).const_mul _) (Filter.Eventually.of_forall fun g => ?_)
  refine (abs_exp_neg_sub_exp_neg_le (hφ.nonneg _) (hφ.nonneg _)).trans ?_
  refine ((hφ.c2 x).abs_sub_le _ _).trans ?_
  have hsub : L *ᵥ g - g = (L - 1) *ᵥ g := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hsub]
  have := norm_mulVec_le (L - 1) hβ hL g
  calc K * ‖(L - 1) *ᵥ g‖ ≤ K * (r * β * ‖g‖) := mul_le_mul_of_nonneg_left this hK
    _ = K * (r * β) * ‖g‖ := by ring

/-- `|Π_{i∈s} a_i - Π_{i∈s} b_i| ≤ Σ_{i∈s} |a_i - b_i|` for `a_i, b_i ∈ [0, 1]`. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hpb0 : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i _ => (hb i).1
    have hpb1 : ∏ i ∈ s, b i ≤ 1 := Finset.prod_le_one₀ (fun i _ => (hb i).1) fun i _ => (hb i).2
    have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (ha j).1, abs_of_nonneg hpb0]
    have h1 : a j * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ |∏ i ∈ s, a i - ∏ i ∈ s, b i| :=
      mul_le_of_le_one_left (abs_nonneg _) (ha j).2
    have h2 : |a j - b j| * ∏ i ∈ s, b i ≤ |a j - b j| :=
      mul_le_of_le_one_right (abs_nonneg _) hpb1
    linarith

end BlockBand.Critical.RelativeVectors
