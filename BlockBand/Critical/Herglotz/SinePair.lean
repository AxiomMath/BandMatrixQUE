module

public import BlockBand.Endpoints.Sine.Law

/-!
# The sine pair form and positivity of the squared sine kernel

The second moment of a linear statistic of the unit-intensity sine process involves the second
Fredholm integral
`∫∫ det[[K(x,x), K(x,y)], [K(y,x), K(y,y)]] a(x) a(y) dx dy = ∫∫ (1 - K(x,y)²) a(x) a(y) dx dy`,
`K = sineKernel` (`K(x,y) = sinc(π(x - y))`). The variance bound uses that `K` is an
orthogonal-projection kernel, i.e. `Var Σ f(x_j) ≤ ∫ |f|²`; here this is the positivity
`∫∫ K(x,y)² a(x) a(y) dx dy ≥ 0` for every real integrable `a` (signed), proved from the
finite-rank approximants `cueKernel M x y = Σ_i ψ_i(x) ψ_i(y)` and dominated convergence
`M → ∞`.

Measure: Lebesgue measure on `ℝ` and its square `volume.prod volume` on `ℝ × ℝ`.

* `sinePairForm a b = ∫∫ (1 - K(x,y)²) a(x) b(y)`, `sineSqForm a b = ∫∫ K(x,y)² a(x) b(y)`.
* `fredholmIntegral_two_sineKernel` — the second sine Fredholm integral is `sinePairForm a a`.
* `sineSqForm_self_nonneg` — positivity (`K²` is a positive-definite kernel).
* `sinePairForm_eq` — `sinePairForm a b = (∫ a)(∫ b) - sineSqForm a b`.
* `sinePairForm_self_le` — `sinePairForm a a ≤ (∫ a)²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BlockBand.Critical.Herglotz

open BlockBand.Endpoints

/-- The sine kernel is symmetric. -/
theorem sineKernel_symm (x y : ℝ) : sineKernel y x = sineKernel x y := by
  unfold sineKernel
  rw [← Real.sinc_neg]
  ring_nf

/-- `|K(x,y)| ≤ 1` for the sine kernel. -/
theorem abs_sineKernel_le_one (x y : ℝ) : |sineKernel x y| ≤ 1 :=
  abs_le.2 ⟨Real.neg_one_le_sinc _, Real.sinc_le_one _⟩

theorem continuous_sineKernel : Continuous fun p : ℝ × ℝ => sineKernel p.1 p.2 :=
  Real.continuous_sinc.comp (continuous_const.mul (continuous_fst.sub continuous_snd))

theorem cueKernel_symm (M : ℕ) (x y : ℝ) : cueKernel M y x = cueKernel M x y := by
  unfold cueKernel
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `|cueKernel M x y| ≤ 1`: the `2 × 2` Gram determinant `1 - K(x,y)²` is nonnegative. -/
theorem abs_cueKernel_le_one (M : ℕ) (x y : ℝ) : |cueKernel M x y| ≤ 1 := by
  have h := (kernel_det_nonneg_and_le_one (cueBasis M) (cueKernel M) (fun _ _ => rfl)
    (cueKernel_self M) 2 ![x, y]).1
  have hd : Matrix.det (fun a b : Fin 2 => cueKernel M (![x, y] a) (![x, y] b)) =
      cueKernel M x x * cueKernel M y y - cueKernel M x y * cueKernel M y x :=
    Matrix.det_fin_two _
  rw [hd] at h
  simp only [cueKernel_self, cueKernel_symm M x y] at h
  rw [← sq_le_one_iff_abs_le_one, sq]
  linarith

/-- Pair form `∫∫ (1 - K(x,y)²) a(x) b(y) dx dy` of the sine kernel `K` (Lebesgue measure). -/
def sinePairForm (a b : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, (1 - sineKernel p.1 p.2 ^ 2) * (a p.1 * b p.2) ∂(volume.prod volume)

/-- Squared-kernel form `∫∫ K(x,y)² a(x) b(y) dx dy` of the sine kernel `K`. -/
def sineSqForm (a b : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, sineKernel p.1 p.2 ^ 2 * (a p.1 * b p.2) ∂(volume.prod volume)

/-- **Second sine Fredholm integral**: `fredholmIntegral sineKernel volume a 2 = sinePairForm a a`
(`det [[1, K], [K, 1]] = 1 - K²`, and `Fin 2 → ℝ ≃ ℝ × ℝ` preserves Lebesgue measure). -/
theorem fredholmIntegral_two_sineKernel (a : ℝ → ℝ) :
    fredholmIntegral sineKernel volume a 2 = sinePairForm a a := by
  unfold fredholmIntegral sinePairForm
  rw [← (measurePreserving_finTwoArrow (volume : Measure ℝ)).integral_comp']
  congr 1
  funext x
  have hd : Matrix.det (fun i j : Fin 2 => sineKernel (x i) (x j)) =
      sineKernel (x 0) (x 0) * sineKernel (x 1) (x 1) -
        sineKernel (x 0) (x 1) * sineKernel (x 1) (x 0) := Matrix.det_fin_two _
  rw [hd, Fin.prod_univ_two]
  simp only [MeasurableEquiv.finTwoArrow_apply, sineKernel_self, sineKernel_symm (x 0) (x 1)]
  ring

/-- Products of integrable functions of the two coordinates are integrable on `ℝ × ℝ`. -/
theorem integrable_mul_prod {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun p : ℝ × ℝ => a p.1 * b p.2) (volume.prod volume) :=
  ha.mul_prod hb

/-- A bounded continuous kernel times `a(x) b(y)` is integrable. -/
theorem integrable_kernel_mul_prod {k : ℝ × ℝ → ℝ} (hk : Continuous k) {c : ℝ}
    (hkc : ∀ p, |k p| ≤ c) {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun p : ℝ × ℝ => k p * (a p.1 * b p.2)) (volume.prod volume) :=
  (integrable_mul_prod ha hb).bdd_mul hk.aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hkc p)

/-- Positivity for the finite-rank approximants: `∫∫ cueKernel M (x,y)² a(x) a(y) ≥ 0`. -/
theorem integral_cueKernel_sq_mul_nonneg (M : ℕ) {a : ℝ → ℝ} (ha : Integrable a) :
    0 ≤ ∫ p : ℝ × ℝ, cueKernel M p.1 p.2 ^ 2 * (a p.1 * a p.2) ∂(volume.prod volume) := by
  set u : Fin (2 * M + 1) → Fin (2 * M + 1) → ℝ → ℝ :=
    fun i j x => cueBasis M i x * cueBasis M j x * a x with hu
  have hui (i j : Fin (2 * M + 1)) : Integrable (u i j) := by
    refine ha.bdd_mul (c := 1)
      ((continuous_cueBasis M i).mul (continuous_cueBasis M j)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |cueBasis M i x| * |cueBasis M j x| ≤ 1 * 1 :=
          mul_le_mul (abs_cueBasis_le_one M i x) (abs_cueBasis_le_one M j x) (abs_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have hexp (p : ℝ × ℝ) : cueKernel M p.1 p.2 ^ 2 * (a p.1 * a p.2) =
      ∑ i, ∑ j, u i j p.1 * u i j p.2 := by
    simp only [hu, cueKernel, sq, Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold cueBasis
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hui i j).mul_prod (hui i j)]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hui i j).mul_prod (hui i j)]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [integral_prod_mul (u i j) (u i j)]
  exact mul_self_nonneg _

/-- **Positivity of the squared sine kernel**: for every real (signed) Lebesgue-integrable `a`,
`sineSqForm a a = ∫∫ K(x,y)² a(x) a(y) dx dy ≥ 0`. Limit `M → ∞` of
`integral_cueKernel_sq_mul_nonneg` by dominated convergence (`|cueKernel M| ≤ 1`, pointwise
`cueKernel M → sineKernel`, `tendsto_cueKernel`). -/
theorem sineSqForm_self_nonneg {a : ℝ → ℝ} (ha : Integrable a) : 0 ≤ sineSqForm a a := by
  have hlim : Tendsto (fun M : ℕ => ∫ p : ℝ × ℝ, cueKernel M p.1 p.2 ^ 2 * (a p.1 * a p.2)
      ∂(volume.prod volume)) atTop (𝓝 (sineSqForm a a)) := by
    refine tendsto_integral_of_dominated_convergence (fun p => |a p.1 * a p.2|)
      (fun M => ((continuous_cueKernel M).pow 2).aestronglyMeasurable.mul
        (integrable_mul_prod ha ha).aestronglyMeasurable)
      (integrable_mul_prod ha ha).abs (fun M => Eventually.of_forall fun p => ?_)
      (Eventually.of_forall fun p => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_of_le_one_left (abs_nonneg _) ?_
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (abs_cueKernel_le_one M p.1 p.2)
    · exact ((tendsto_cueKernel p.1 p.2).pow 2).mul_const _
  exact ge_of_tendsto' hlim fun M => integral_cueKernel_sq_mul_nonneg M ha

/-- `sinePairForm a b = (∫ a)(∫ b) - sineSqForm a b` for Lebesgue-integrable `a, b`. -/
theorem sinePairForm_eq {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    sinePairForm a b = (∫ x, a x) * (∫ x, b x) - sineSqForm a b := by
  unfold sinePairForm sineSqForm
  simp_rw [sub_mul, one_mul]
  rw [integral_sub (integrable_mul_prod ha hb)
    (integrable_kernel_mul_prod (k := fun p : ℝ × ℝ => sineKernel p.1 p.2 ^ 2)
      (continuous_sineKernel.pow 2) (c := 1) (fun p => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_sineKernel_le_one _ _)) ha hb),
    integral_prod_mul a b]

/-- **Projection-kernel bound**: `sinePairForm a a ≤ (∫ a)²` for every real integrable `a`. -/
theorem sinePairForm_self_le {a : ℝ → ℝ} (ha : Integrable a) :
    sinePairForm a a ≤ (∫ x, a x) ^ 2 := by
  rw [sinePairForm_eq ha ha, sq]
  linarith [sineSqForm_self_nonneg ha]

/-- `|1 - K(x,y)²| ≤ 1` for the sine kernel. -/
theorem abs_one_sub_sineKernel_sq_le_one (x y : ℝ) : |1 - sineKernel x y ^ 2| ≤ 1 := by
  have h2 : sineKernel x y ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact abs_sineKernel_le_one x y
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (sineKernel x y)]

/-- The sine pair form is integrable-kernel well defined: integrability of its integrand. -/
theorem integrable_sinePairForm_integrand {a b : ℝ → ℝ} (ha : Integrable a)
    (hb : Integrable b) :
    Integrable (fun p : ℝ × ℝ => (1 - sineKernel p.1 p.2 ^ 2) * (a p.1 * b p.2))
      (volume.prod volume) :=
  integrable_kernel_mul_prod (k := fun p : ℝ × ℝ => 1 - sineKernel p.1 p.2 ^ 2)
    (continuous_const.sub (continuous_sineKernel.pow 2)) (c := 1)
    (fun p => by
      have h1 := abs_sineKernel_le_one p.1 p.2
      have h2 : sineKernel p.1 p.2 ^ 2 ≤ 1 := by
        rw [sq_le_one_iff_abs_le_one]; exact h1
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (sineKernel p.1 p.2)]) ha hb

end BlockBand.Critical.Herglotz
