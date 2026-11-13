module

public import BlockBand.Critical.RelativeVectors.Statement
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Internal.Contracts.CriticalEntire

/-!
# The Gaussian mark average `ψ`

The Gaussian side of the decorated-sine clause factorizes as `exp(-Σψ(x_j))`, with
`ψ = -log ∫e^{-φ(x,g)} γ_r(dg)`; `ψ` is nonnegative and continuous, and vanishes off `[-R,R]`.

*Law.* `γ_r = circularVectorLaw (Fin r)` (standard circular Gaussian on `ℂ^r`).
*Domain.* every test `φ` of `IsDecoratedTest r R K φ` (continuous, `φ ≥ 0`, supported in
`[-R,R] × ℂ^r`, bounded `C²` in the mark with bound `K`, no decay in the mark).

* `markAverage_mem`: `e^{-K} ≤ ∫ e^{-φ(x,g)} γ_r(dg) ≤ 1`;
* `markPsi_nonneg`, `markPsi_le`: `0 ≤ ψ ≤ K`; `markPsi_eq_zero`: `ψ(x) = 0` for `|x| > R`;
  `continuous_markPsi`: `ψ` is continuous; `markPsiC`: `ψ` as a compactly supported continuous
  function; `one_sub_exp_neg_markPsi`: `1 - e^{-ψ(x)} = 1 - ∫e^{-φ(x,g)}γ_r(dg)`;
* `markedSineLaplace_eq_sineLaplace`: the decorated sine Laplace functional of `φ` is the unit
  sine Laplace functional of `ψ` (`markedSineLaplace r φ = sineLaplaceFunctional ψ`);
* `decoratedSineLaplace_eq_markedSineLaplace`: on `C_c(ℝ × ℂ^r)` the series `markedSineLaplace`
  is `CriticalEntire.decoratedSineLaplace` (same formula).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {r : ℕ}

/-- `I_φ(x) = ∫ e^{-φ(x,g)} γ_r(dg)`. -/
def markAverage (r : ℕ) (φ : ℝ × (Fin r → ℂ) → ℝ) (x : ℝ) : ℝ :=
  ∫ g, Real.exp (-φ (x, g)) ∂circularVectorLaw (Fin r)

/-- `ψ_φ(x) = -log I_φ(x)`. -/
def markPsi (r : ℕ) (φ : ℝ × (Fin r → ℂ) → ℝ) (x : ℝ) : ℝ :=
  -Real.log (markAverage r φ x)

theorem integrable_exp_neg {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (x : ℝ) : Integrable (fun g => Real.exp (-φ (x, g))) (circularVectorLaw (Fin r)) := by
  refine Integrable.of_bound (C := 1)
    ((Real.continuous_exp.comp ((hφ.continuous.comp (Continuous.prodMk_right x)).neg)).aestronglyMeasurable) ?_
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))

/-- `e^{-K} ≤ I_φ(x) ≤ 1`. -/
theorem markAverage_mem {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (x : ℝ) : Real.exp (-K) ≤ markAverage r φ x ∧ markAverage r φ x ≤ 1 := by
  have hint := integrable_exp_neg hφ x
  constructor
  · have h : ∫ _g, Real.exp (-K) ∂circularVectorLaw (Fin r) ≤ markAverage r φ x := by
      refine integral_mono (integrable_const _) hint fun g => ?_
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have hb := (hφ.c2 x).bound g
      exact (le_abs_self _).trans hb
    simpa using h
  · have h : markAverage r φ x ≤ ∫ _g, (1 : ℝ) ∂circularVectorLaw (Fin r) :=
      integral_mono hint (integrable_const _) fun g =>
        Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))
    simpa using h

theorem markAverage_pos {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (x : ℝ) : 0 < markAverage r φ x :=
  lt_of_lt_of_le (Real.exp_pos _) (markAverage_mem hφ x).1

theorem markPsi_nonneg {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (x : ℝ) : 0 ≤ markPsi r φ x :=
  neg_nonneg.2 (Real.log_nonpos (markAverage_pos hφ x).le (markAverage_mem hφ x).2)

theorem markPsi_le {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    (x : ℝ) : markPsi r φ x ≤ K := by
  unfold markPsi
  have h := Real.log_le_log (Real.exp_pos _) (markAverage_mem hφ x).1
  rw [Real.log_exp] at h
  linarith

/-- `ψ(x) = 0` for `|x| > R`. -/
theorem markPsi_eq_zero {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ)
    {x : ℝ} (hx : R < |x|) : markPsi r φ x = 0 := by
  unfold markPsi markAverage
  simp [hφ.support x _ hx]

/-- `1 - e^{-ψ(x)} = 1 - ∫ e^{-φ(x,g)} γ_r(dg)`. -/
theorem one_sub_exp_neg_markPsi {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) (x : ℝ) :
    1 - Real.exp (-markPsi r φ x) = 1 - markAverage r φ x := by
  unfold markPsi
  rw [neg_neg, Real.exp_log (markAverage_pos hφ x)]

theorem continuous_markAverage {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) : Continuous (markAverage r φ) := by
  unfold markAverage
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ (integrable_const _) ?_
  · intro x
    exact (Real.continuous_exp.comp
      ((hφ.continuous.comp (Continuous.prodMk_right x)).neg)).aestronglyMeasurable
  · intro x
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (hφ.nonneg _))
  · filter_upwards with g
    exact Real.continuous_exp.comp ((hφ.continuous.comp (Continuous.prodMk_left g)).neg)

theorem continuous_markPsi {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) : Continuous (markPsi r φ) :=
  ((continuous_markAverage hφ).log fun x => (markAverage_pos hφ x).ne').neg

theorem hasCompactSupport_markPsi {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) : HasCompactSupport (markPsi r φ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => ?_
  apply markPsi_eq_zero hφ
  by_contra h
  push Not at h
  exact hx (abs_le.1 h)

/-- `ψ` as a compactly supported continuous function on `ℝ`. -/
def markPsiC {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : IsDecoratedTest r R K φ) :
    CompactlySupportedContinuousMap ℝ ℝ where
  toFun := markPsi r φ
  continuous_toFun := continuous_markPsi hφ
  hasCompactSupport' := hasCompactSupport_markPsi hφ

/-- **Decorated sine = sine of `ψ`.** For every admissible test,
`markedSineLaplace r φ = sineLaplaceFunctional ψ` (Fredholm series term by term,
`1 - e^{-ψ(x)} = 1 - ∫ e^{-φ(x,g)} γ_r(dg)`). -/
theorem markedSineLaplace_eq_sineLaplace {R K : ℝ} {φ : ℝ × (Fin r → ℂ) → ℝ}
    (hφ : IsDecoratedTest r R K φ) :
    markedSineLaplace r φ = BlockBand.sineLaplaceFunctional (markPsiC hφ) := by
  unfold markedSineLaplace BlockBand.sineLaplaceFunctional
  congr 1
  funext k
  congr 1
  congr 1
  funext x
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (one_sub_exp_neg_markPsi hφ (x i)).symm

/-- On `C_c(ℝ × ℂ^r)` the series `markedSineLaplace` is `CriticalEntire.decoratedSineLaplace`. -/
theorem decoratedSineLaplace_eq_markedSineLaplace
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) :
    BlockBand.Internal.Contracts.CriticalEntire.decoratedSineLaplace r f =
      markedSineLaplace r f :=
  rfl

end BlockBand.Critical.RelativeVectors
