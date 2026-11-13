module

public import BlockBand.Critical.RelativeVectors.Window
public import BlockBand.Critical.RelativeVectors.MarkedLaplace
public import BlockBand.Critical.Herglotz.MarkTruncation
public import BlockBand.Critical.DecoratedSine.Existence
public import BlockBand.Endpoints.Sine.Law
public import BlockBand.Endpoints.VagueMeasurability

/-!
# Laplace functionals of marked configurations under perturbation of the test

*Finite side.* Law: any probability law `ν` of `G`; points `x_ℓ = Nρ(λ_ℓ(F + G) - E)`, marks
`z_ℓ = √N e^{iθ_ℓ}V^*u_ℓ` with uniform phases (`RelativeVectors.markedIntegrand`).
* `abs_exp_sum_sub_le`, **`abs_integral_markedIntegrand_sub_le`**: if `0 ≤ f, g`, `|f - g| ≤ η`
  and both vanish for `|x| > R`, then the Laplace functionals differ by at most
  `ηk + P(#{ℓ : |x_ℓ| ≤ R} > k)`.
* `countTest R t = t β_R(x)` (a decorated test, constant in the mark) and
  **`measureReal_windowCard_le`**: `P(#{|x_ℓ| ≤ R} > k) ≤ 2(1 - E e^{-t Σ β_R(x_ℓ)})` when
  `e^{-t(k+1)} ≤ 1/2`.

* **`abs_decoratedSineLaplace_sub_le`**: `|L(f) - L(g)| ≤ η(2R + 2)` under the same hypotheses
  (`E Ξ([-R-1, R+1] × ℂ^r) = 2R + 2`, Herglotz C1 `lintegral_lintegral_ofReal_of_decoratedSine`).
* **`exists_markedSineLaplace_countTest`**: `1 - markedSineLaplace r (countTest R t) ≤ τ` for some
  `t > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open BlockBand.Internal.Contracts.CriticalEntire
open scoped NNReal ENNReal

variable {N r : ℕ}

/-!
## Elementary exponential bounds
-/

theorem abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hab)
  have h1 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h3 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
    have := Real.add_one_le_exp (-(b - a)); linarith
  have h4 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : 0 ≤ 1 - Real.exp (-(b - a)) := by
    have := Real.exp_le_one_iff.2 (show -(b - a) ≤ 0 by linarith); linarith
  have h2 : Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ 1 * (b - a) := by
    calc Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤ 1 * (1 - Real.exp (-(b - a))) :=
          mul_le_mul_of_nonneg_right h4 h5
      _ ≤ 1 * (b - a) := by linarith
  have h6 : Real.exp (-a) * (1 - Real.exp (-(b - a))) = Real.exp (-a) - Real.exp (-b) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show -a + -(b - a) = -b by ring]
  linarith

theorem abs_exp_neg_sub_le_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ 1 := by
  have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 := Real.exp_pos (-a)
  have h4 := Real.exp_pos (-b)
  rw [abs_le]; constructor <;> linarith

/-!
## The finite side
-/

/-- **Pointwise comparison** of `exp(-Σ f(p_ℓ))` and `exp(-Σ g(p_ℓ))`. -/
theorem abs_exp_sum_sub_le {n : ℕ} (p : Fin n → ℝ × (Fin r → ℂ)) {f g : ℝ × (Fin r → ℂ) → ℝ}
    (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q) {η R : ℝ} (hη : 0 ≤ η)
    (hfg : ∀ q, |f q - g q| ≤ η) (hfR : ∀ x z, R < |x| → f (x, z) = 0)
    (hgR : ∀ x z, R < |x| → g (x, z) = 0) (k : ℕ) :
    |Real.exp (-∑ ℓ, f (p ℓ)) - Real.exp (-∑ ℓ, g (p ℓ))| ≤
      η * k + (if k < (Finset.univ.filter fun ℓ => |(p ℓ).1| ≤ R).card then 1 else 0) := by
  classical
  set S := Finset.univ.filter fun ℓ => |(p ℓ).1| ≤ R
  have hS : ∀ ℓ, ℓ ∉ S → |f (p ℓ) - g (p ℓ)| = 0 := by
    intro ℓ hℓ
    have hR : R < |(p ℓ).1| := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hℓ; exact hℓ
    have h1 := hfR (p ℓ).1 (p ℓ).2 hR
    have h2 := hgR (p ℓ).1 (p ℓ).2 hR
    simp only [Prod.mk.eta] at h1 h2
    rw [h1, h2, sub_self, abs_zero]
  have hsum : |∑ ℓ, f (p ℓ) - ∑ ℓ, g (p ℓ)| ≤ η * S.card := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ℓ, |f (p ℓ) - g (p ℓ)| ≤ ∑ ℓ, (if ℓ ∈ S then η else 0) := by
          refine Finset.sum_le_sum fun ℓ _ => ?_
          split_ifs with h
          · exact hfg _
          · rw [hS ℓ h]
      _ = η * S.card := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
          simp
  have hsf : 0 ≤ ∑ ℓ, f (p ℓ) := Finset.sum_nonneg fun ℓ _ => hf _
  have hsg : 0 ≤ ∑ ℓ, g (p ℓ) := Finset.sum_nonneg fun ℓ _ => hg _
  split_ifs with hk
  · have := abs_exp_neg_sub_le_one hsf hsg
    have : 0 ≤ η * k := mul_nonneg hη (Nat.cast_nonneg _)
    linarith
  · push Not at hk
    have hk' : (S.card : ℝ) ≤ k := by exact_mod_cast hk
    calc _ ≤ |∑ ℓ, f (p ℓ) - ∑ ℓ, g (p ℓ)| := abs_exp_neg_sub_le hsf hsg
      _ ≤ η * S.card := hsum
      _ ≤ η * k := mul_le_mul_of_nonneg_left hk' hη
      _ = η * k + 0 := (add_zero _).symm

theorem measurable_markedIntegrand_of_continuous {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : Continuous φ)
    (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) : Measurable (markedIntegrand ρ E V φ) := by
  have h : Measurable (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) =>
      Real.exp (-∑ ℓ : Fin N, φ ((N : ℝ) * ρ * (freshEigenvalue p.1 ℓ - E),
        relativeMark V p.1 p.2 ℓ))) := by
    refine Real.measurable_exp.comp (Measurable.neg ?_)
    refine Finset.measurable_sum _ fun ℓ _ => hφ.measurable.comp ?_
    refine Measurable.prodMk ?_ (measurable_relativeMark V ℓ)
    exact measurable_const.mul
      (((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).comp measurable_fst).sub
        measurable_const)
  exact (h.stronglyMeasurable.integral_prod_right' (ν := phaseVectorLaw N)).measurable

theorem measurable_markedIntegrand_inner {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : Continuous φ)
    (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    Measurable fun θ : Fin N → ℂ => Real.exp (-∑ ℓ : Fin N,
      φ ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E), relativeMark V K θ ℓ)) := by
  refine Real.measurable_exp.comp (Measurable.neg ?_)
  refine Finset.measurable_sum _ fun ℓ _ => hφ.measurable.comp ?_
  refine Measurable.prodMk measurable_const ?_
  exact (measurable_relativeMark V ℓ).comp (measurable_const.prodMk measurable_id)

theorem markedIntegrand_mem {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ0 : ∀ p, 0 ≤ φ p) (ρ E : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ markedIntegrand ρ E V φ K ∧ markedIntegrand ρ E V φ K ≤ 1 := by
  constructor
  · exact integral_nonneg fun θ => (Real.exp_pos _).le
  · calc markedIntegrand ρ E V φ K ≤ ∫ _θ, (1 : ℝ) ∂phaseVectorLaw N := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun θ => (Real.exp_pos _).le)
            (integrable_const 1) (Eventually.of_forall fun θ => ?_)
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun ℓ _ => hφ0 _))
      _ = 1 := by simp

theorem integrable_markedIntegrand {φ : ℝ × (Fin r → ℂ) → ℝ} (hφ : Continuous φ)
    (hφ0 : ∀ p, 0 ≤ φ p) (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) (F : Matrix (Fin N) (Fin N) ℂ)
    (ν : Measure (Matrix (Fin N) (Fin N) ℂ)) [IsProbabilityMeasure ν] :
    Integrable (fun G => markedIntegrand ρ E V φ (F + G)) ν := by
  refine Integrable.of_bound
    ((measurable_markedIntegrand_of_continuous hφ ρ E V).comp
      (measurable_const_add F)).aestronglyMeasurable 1 (Eventually.of_forall fun G => ?_)
  have := markedIntegrand_mem hφ0 ρ E V (F + G)
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

theorem measurableSet_windowCard' (ρ E R : ℝ) (k : ℕ) :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R K).card} := by
  classical
  have h : {K : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R K).card} =
      ⋃ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S => k < S.card),
        {K | windowSet ρ E R K = S} := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      exists_prop]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨S, hS, hK⟩ => hK ▸ hS⟩
  rw [h]
  refine Finset.measurableSet_biUnion _ fun S _ => ?_
  exact measurableSet_filter_eq (fun K ℓ => (N : ℝ) * ρ * (freshEigenvalue K ℓ - E))
    (fun ℓ => measurable_const.mul
      ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).sub measurable_const)) R S

/-- **Comparison of finite Laplace functionals** for sup-close tests with a common window. -/
theorem abs_integral_markedIntegrand_sub_le (ν : Measure (Matrix (Fin N) (Fin N) ℂ))
    [IsProbabilityMeasure ν] (F : Matrix (Fin N) (Fin N) ℂ) (ρ E : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) {f g : ℝ × (Fin r → ℂ) → ℝ} (hfc : Continuous f)
    (hgc : Continuous g) (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q) {η R : ℝ} (hη : 0 ≤ η)
    (hfg : ∀ q, |f q - g q| ≤ η) (hfR : ∀ x z, R < |x| → f (x, z) = 0)
    (hgR : ∀ x z, R < |x| → g (x, z) = 0) (k : ℕ) :
    |∫ G, markedIntegrand ρ E V f (F + G) ∂ν - ∫ G, markedIntegrand ρ E V g (F + G) ∂ν| ≤
      η * k + ν.real {G | k < (windowSet ρ E R (F + G)).card} := by
  classical
  set A := {G : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R (F + G)).card}
  have hA : MeasurableSet A := (measurable_const_add F) (measurableSet_windowCard' ρ E R k)
  have hpt : ∀ K : Matrix (Fin N) (Fin N) ℂ,
      |markedIntegrand ρ E V f K - markedIntegrand ρ E V g K| ≤
        η * k + (if k < (windowSet ρ E R K).card then 1 else 0) := by
    intro K
    unfold markedIntegrand
    have hi : ∀ φ : ℝ × (Fin r → ℂ) → ℝ, Continuous φ → (∀ q, 0 ≤ φ q) →
        Integrable (fun θ : Fin N → ℂ => Real.exp (-∑ ℓ : Fin N,
          φ ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E), relativeMark V K θ ℓ)))
          (phaseVectorLaw N) := fun φ hφ hφ0 =>
      Integrable.of_bound (measurable_markedIntegrand_inner hφ ρ E V K).aestronglyMeasurable 1
        (Eventually.of_forall fun θ => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Finset.sum_nonneg fun ℓ _ => hφ0 _)))
    rw [← integral_sub (hi f hfc hf) (hi g hgc hg)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ θ, |_| ∂phaseVectorLaw N ≤ ∫ _θ, (η * k + (if k < (windowSet ρ E R K).card then 1
          else 0)) ∂phaseVectorLaw N := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun θ => ?_)
          exact abs_exp_sum_sub_le (fun ℓ => ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E),
            relativeMark V K θ ℓ)) hf hg hη hfg hfR hgR k
      _ = _ := by simp
  rw [← integral_sub (integrable_markedIntegrand hfc hf ρ E V F ν)
    (integrable_markedIntegrand hgc hg ρ E V F ν)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hind : ∀ G, (if k < (windowSet ρ E R (F + G)).card then (1 : ℝ) else 0) =
      A.indicator 1 G := by
    intro G
    by_cases h : k < (windowSet ρ E R (F + G)).card
    · simp [h, Set.indicator_of_mem (show G ∈ A from h)]
    · simp [h, Set.indicator_of_notMem (show G ∉ A from h)]
  calc ∫ G, |_| ∂ν ≤ ∫ G, (η * k + A.indicator 1 G) ∂ν := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun G => abs_nonneg _)
          ((integrable_const _).add ((integrable_const 1).indicator hA))
          (Eventually.of_forall fun G => ?_)
        have := hpt (F + G)
        rw [hind G] at this
        exact this
    _ = η * k + ν.real A := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hA),
          integral_indicator_one hA]
        simp

/-!
## The count test
-/

/-- `β_R(x) = max(0, min(1, R + 1 - |x|))`: `1` on `[-R, R]`, `0` off `(-R-1, R+1)`. -/
def cutBump (R x : ℝ) : ℝ := max 0 (min 1 (R + 1 - |x|))

theorem continuous_cutBump (R : ℝ) : Continuous (cutBump R) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem cutBump_nonneg (R x : ℝ) : 0 ≤ cutBump R x := le_max_left _ _

theorem cutBump_le_one (R x : ℝ) : cutBump R x ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutBump_eq_one {R x : ℝ} (h : |x| ≤ R) : cutBump R x = 1 := by
  unfold cutBump; rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutBump_eq_zero {R x : ℝ} (h : R + 1 ≤ |x|) : cutBump R x = 0 := by
  unfold cutBump; rw [max_eq_left]; exact min_le_of_right_le (by linarith)

theorem cutBump_le_indicator (R x : ℝ) :
    cutBump R x ≤ (Set.Icc (-(R + 1)) (R + 1)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ Set.Icc (-(R + 1)) (R + 1)
  · rw [Set.indicator_of_mem h]; exact cutBump_le_one R x
  · rw [Set.indicator_of_notMem h, cutBump_eq_zero]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]

theorem hasCompactSupport_cutBump (R : ℝ) : HasCompactSupport (cutBump R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun x hx => ?_
  refine cutBump_eq_zero ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · linarith [neg_le_abs x]
  · linarith [le_abs_self x]

/-- `β_R` as a compactly supported continuous function. -/
def cutBumpC (R : ℝ) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨cutBump R, continuous_cutBump R⟩, hasCompactSupport_cutBump R⟩

/-- The count test `(x, z) ↦ t β_R(x)`, constant in the mark. -/
def countTest (R t : ℝ) : ℝ × (Fin r → ℂ) → ℝ := fun p => t * cutBump R p.1

theorem isDecoratedTest_countTest (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsDecoratedTest r (R + 1) t (countTest R t) where
  continuous := continuous_const.mul ((continuous_cutBump R).comp continuous_fst)
  nonneg p := mul_nonneg ht (cutBump_nonneg _ _)
  support x z hx := by
    simp only [countTest]
    rw [cutBump_eq_zero hx.le, mul_zero]
  c2 x := by
    refine ⟨by simp only [countTest]; exact contDiff_const, fun z => ?_, fun z => ?_, fun z => ?_⟩
    · simp only [countTest]
      rw [abs_of_nonneg (mul_nonneg ht (cutBump_nonneg _ _))]
      calc t * cutBump R x ≤ t * 1 := mul_le_mul_of_nonneg_left (cutBump_le_one _ _) ht
        _ = t := mul_one t
    · simp only [countTest, fderiv_const_apply, norm_zero]; exact ht
    · simp only [countTest]
      rw [iteratedFDeriv_const_of_ne (by norm_num), Pi.zero_apply, norm_zero]
      exact ht

theorem markedIntegrand_countTest (R t ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) :
    markedIntegrand ρ E V (countTest R t) K =
      Real.exp (-∑ ℓ : Fin N, t * cutBump R ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E))) := by
  simp [markedIntegrand, countTest]

/-- **Count tail from the Laplace functional of the count test.** -/
theorem measureReal_windowCard_le (ν : Measure (Matrix (Fin N) (Fin N) ℂ))
    [IsProbabilityMeasure ν] (F : Matrix (Fin N) (Fin N) ℂ) (ρ E R : ℝ)
    (V : Matrix (Fin N) (Fin r) ℂ) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hk : Real.exp (-(t * (k + 1))) ≤ 1 / 2) :
    ν.real {G | k < (windowSet ρ E R (F + G)).card} ≤
      2 * (1 - ∫ G, markedIntegrand ρ E V (countTest R t) (F + G) ∂ν) := by
  classical
  set A := {G : Matrix (Fin N) (Fin N) ℂ | k < (windowSet ρ E R (F + G)).card}
  have hA : MeasurableSet A := (measurable_const_add F) (measurableSet_windowCard' ρ E R k)
  have hcont : Continuous (countTest (r := r) R t) :=
    (isDecoratedTest_countTest (r := r) R ht).continuous
  have hpt : ∀ G, A.indicator (fun _ => (1 : ℝ)) G ≤
      2 * (1 - markedIntegrand ρ E V (countTest R t) (F + G)) := by
    intro G
    have hm := markedIntegrand_mem (isDecoratedTest_countTest (r := r) R ht).nonneg ρ E V (F + G)
    by_cases hG : G ∈ A
    · rw [Set.indicator_of_mem hG, markedIntegrand_countTest]
      have hsum : (k : ℝ) + 1 ≤ ∑ ℓ : Fin N,
          cutBump R ((N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)) := by
        have hcard : ((k + 1 : ℕ) : ℝ) ≤ (windowSet ρ E R (F + G)).card := by
          exact_mod_cast hG
        calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
          _ ≤ (windowSet ρ E R (F + G)).card := hcard
          _ = ∑ ℓ ∈ windowSet ρ E R (F + G), (1 : ℝ) := by simp
          _ = ∑ ℓ ∈ windowSet ρ E R (F + G),
                cutBump R ((N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)) := by
              refine Finset.sum_congr rfl fun ℓ hℓ => (cutBump_eq_one ?_).symm
              simp only [windowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
              exact hℓ
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              fun ℓ _ _ => cutBump_nonneg _ _
      rw [← Finset.mul_sum]
      have he : Real.exp (-(t * ∑ ℓ : Fin N,
          cutBump R ((N : ℝ) * ρ * (freshEigenvalue (F + G) ℓ - E)))) ≤ 1 / 2 :=
        le_trans (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hsum ht))) hk
      linarith
    · rw [Set.indicator_of_notMem hG]
      linarith [hm.2]
  have hint := integrable_markedIntegrand hcont
    (isDecoratedTest_countTest (r := r) R ht).nonneg ρ E V F ν
  calc ν.real A = ∫ G, A.indicator (fun _ => (1 : ℝ)) G ∂ν := (integral_indicator_one hA).symm
    _ ≤ ∫ G, 2 * (1 - markedIntegrand ρ E V (countTest R t) (F + G)) ∂ν :=
        integral_mono ((integrable_const 1).indicator hA)
          (((integrable_const 1).sub hint).const_mul 2) hpt
    _ = 2 * (1 - ∫ G, markedIntegrand ρ E V (countTest R t) (F + G) ∂ν) := by
        rw [integral_const_mul, integral_sub (integrable_const 1) hint]
        simp

/-!
## The sine side
-/

/-- **`1 - L_sine(t β_R) ≤ τ` for small `t`.** -/
theorem exists_markedSineLaplace_countTest (R : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∃ t : ℝ, 0 < t ∧ 1 - markedSineLaplace r (countTest R t) ≤ τ := by
  obtain ⟨P₀, hP₀⟩ := BlockBand.Endpoints.exists_isSineLaw
  set μ : Measure (VaguePointMeasure ℝ) := (P₀ : Measure (VaguePointMeasure ℝ))
  set Y : VaguePointMeasure ℝ → ℝ := fun ξ => ∫ x, cutBumpC (R + 1) x ∂ξ.measure
  have hY : Measurable Y := BlockBand.Endpoints.measurable_coordinate (cutBumpC (R + 1))
  have hY0 : ∀ ξ, 0 ≤ Y ξ := fun ξ => integral_nonneg fun x => cutBump_nonneg _ _
  have hcont : Tendsto (fun s : ℝ≥0 => ∫ ξ, Real.exp (-((s : ℝ) * Y ξ)) ∂μ) (𝓝 0) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0 : ℝ≥0))
      (F := fun (s : ℝ≥0) ξ => Real.exp (-((s : ℝ) * Y ξ))) (f := fun _ => (1 : ℝ))
      (fun _ => (1 : ℝ))
      (Eventually.of_forall fun s => ((hY.const_mul (s : ℝ)).neg.exp).aestronglyMeasurable)
      (Eventually.of_forall fun s => Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg s.2 (hY0 ξ))))
      (integrable_const 1)
      (Eventually.of_forall fun ξ => by
        have : Tendsto (fun s : ℝ≥0 => Real.exp (-((s : ℝ) * Y ξ))) (𝓝 0)
            (𝓝 (Real.exp (-(((0 : ℝ≥0) : ℝ) * Y ξ)))) :=
          ((Real.continuous_exp.comp ((NNReal.continuous_coe.mul continuous_const).neg)).tendsto 0)
        simpa using this)
    simpa using h
  have hev : ∀ᶠ s : ℝ≥0 in 𝓝[>] 0, |∫ ξ, Real.exp (-((s : ℝ) * Y ξ)) ∂μ - 1| < τ := by
    have := (Metric.tendsto_nhds.1 hcont) τ hτ
    simpa [Real.dist_eq] using this.filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs1, hs0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hs : (0 : ℝ) < s := hs0
  refine ⟨s, hs, ?_⟩
  have hτt := isDecoratedTest_countTest (r := r) R hs.le
  rw [markedSineLaplace_eq_sineLaplace hτt, ← hP₀.2 (markPsiC hτt) (markPsi_nonneg hτt)]
  have hle : ∫ ξ, Real.exp (-((s : ℝ) * Y ξ)) ∂μ ≤
      ∫ ξ, Real.exp (-∫ x, markPsiC hτt x ∂ξ.measure) ∂μ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => (Real.exp_pos _).le) ?_
      (Eventually.of_forall fun ξ => ?_)
    · refine Integrable.of_bound ((BlockBand.Endpoints.measurable_coordinate
        (markPsiC hτt)).neg.exp).aestronglyMeasurable 1 (Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (integral_nonneg fun x => markPsi_nonneg hτt x))
    · refine Real.exp_le_exp.2 (neg_le_neg ?_)
      rw [← integral_const_mul]
      refine integral_mono ((markPsiC hτt).continuous.integrable_of_hasCompactSupport
        (markPsiC hτt).hasCompactSupport) (((cutBumpC (R + 1)).continuous.integrable_of_hasCompactSupport
        (cutBumpC (R + 1)).hasCompactSupport).const_mul _) fun x => ?_
      change markPsi r (countTest R s) x ≤ s * cutBump (R + 1) x
      by_cases hx : |x| ≤ R + 1
      · rw [cutBump_eq_one hx, mul_one]; exact markPsi_le hτt x
      · rw [markPsi_eq_zero hτt (not_le.1 hx)]
        exact mul_nonneg hs.le (cutBump_nonneg _ _)
  rw [abs_lt] at hs1
  linarith [hs1.1]

/-- **Comparison of decorated sine Laplace functionals** for sup-close tests with a common
window. -/
theorem abs_decoratedSineLaplace_sub_le (f g : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ)
    (hf : ∀ q, 0 ≤ f q) (hg : ∀ q, 0 ≤ g q) {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hfg : ∀ q, |f q - g q| ≤ η) (hfR : ∀ x z, R < |x| → f (x, z) = 0)
    (hgR : ∀ x z, R < |x| → g (x, z) = 0) :
    |decoratedSineLaplace r f - decoratedSineLaplace r g| ≤ η * (2 * R + 2) := by
  obtain ⟨Ω, _, P, Ξ, hΞ⟩ := BlockBand.Critical.DecoratedSine.exists_isDecoratedSineProcess r
  have := hΞ.prob
  have := BlockBand.Critical.DecoratedSine.isProbabilityMeasure_circularVectorLaw (Fin r)
  rw [← hΞ.laplace f hf, ← hΞ.laplace g hg]
  set β : ℝ × (Fin r → ℂ) → ℝ := fun p => cutBump R p.1
  have hβc : Continuous β := (continuous_cutBump R).comp continuous_fst
  have hβ0 : ∀ p, 0 ≤ β p := fun p => cutBump_nonneg _ _
  have hβS : ∀ x (z : Fin r → ℂ), x ∉ Set.Icc (-(R + 1)) (R + 1) → β (x, z) = 0 := by
    intro x z hx
    simp only [β]
    refine cutBump_eq_zero ?_
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · linarith [neg_le_abs x]
    · linarith [le_abs_self x]
  obtain ⟨hBm, hBint⟩ := Herglotz.lintegral_lintegral_ofReal_of_decoratedSine hΞ hβc hβ0
    isCompact_Icc hβS
  set B : Ω → ℝ≥0∞ := fun ω => ∫⁻ p, ENNReal.ofReal (β p) ∂(Ξ ω).measure
  set u : Ω → ℝ := fun ω => Real.exp (-∫ z, f z ∂(Ξ ω).measure)
  set v : Ω → ℝ := fun ω => Real.exp (-∫ z, g z ∂(Ξ ω).measure)
  have hum : Measurable u :=
    ((BlockBand.Endpoints.measurable_coordinate f).comp hΞ.measurable).neg.exp
  have hvm : Measurable v :=
    ((BlockBand.Endpoints.measurable_coordinate g).comp hΞ.measurable).neg.exp
  have hbd : ∀ (w : Ω → ℝ), Measurable w → (∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) → Integrable w P :=
    fun w hw hw1 => Integrable.of_bound hw.aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw1 ω).1]; exact (hw1 ω).2)
  have hu1 : ∀ ω, 0 ≤ u ω ∧ u ω ≤ 1 := fun ω =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (integral_nonneg fun z => hf z))⟩
  have hv1 : ∀ ω, 0 ≤ v ω ∧ v ω ≤ 1 := fun ω =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 (integral_nonneg fun z => hg z))⟩
  -- pointwise
  have hpt : ∀ ω, ENNReal.ofReal |u ω - v ω| ≤ ENNReal.ofReal η * B ω := by
    intro ω
    by_cases hB : B ω = ∞
    · rw [hB, ENNReal.mul_top (by simpa using hη)]; exact le_top
    · have hβi : Integrable β (Ξ ω).measure := by
        refine ⟨hβc.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hβ0)]
        exact lt_top_iff_ne_top.2 hB
      have hfi : Integrable f (Ξ ω).measure :=
        f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
      have hgi : Integrable g (Ξ ω).measure :=
        g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      have h1 : |u ω - v ω| ≤ |∫ z, f z ∂(Ξ ω).measure - ∫ z, g z ∂(Ξ ω).measure| :=
        abs_exp_neg_sub_le (integral_nonneg fun z => hf z) (integral_nonneg fun z => hg z)
      have h2 : |∫ z, f z ∂(Ξ ω).measure - ∫ z, g z ∂(Ξ ω).measure| ≤
          η * ∫ p, β p ∂(Ξ ω).measure := by
        rw [← integral_sub hfi hgi, ← integral_const_mul]
        refine (abs_integral_le_integral_abs).trans (integral_mono (hfi.sub hgi).abs
          (hβi.const_mul η) fun p => ?_)
        by_cases hp : |p.1| ≤ R
        · simp only [β, cutBump_eq_one hp, mul_one]; exact hfg p
        · have hp' : R < |p.1| := not_le.1 hp
          have e1 := hfR p.1 p.2 hp'
          have e2 := hgR p.1 p.2 hp'
          simp only [Prod.mk.eta] at e1 e2
          simp only [e1, e2, sub_self, abs_zero]
          exact mul_nonneg hη.le (hβ0 p)
      have h3 : ENNReal.ofReal (∫ p, β p ∂(Ξ ω).measure) = B ω :=
        ofReal_integral_eq_lintegral_ofReal hβi (Eventually.of_forall hβ0)
      calc ENNReal.ofReal |u ω - v ω| ≤ ENNReal.ofReal (η * ∫ p, β p ∂(Ξ ω).measure) :=
            ENNReal.ofReal_le_ofReal (h1.trans h2)
        _ = ENNReal.ofReal η * B ω := by rw [ENNReal.ofReal_mul hη.le, h3]
  -- the mean of `B`
  have hmean : ∫⁻ ω, B ω ∂P ≤ ENNReal.ofReal (2 * R + 2) := by
    rw [hBint]
    calc ∫⁻ x, ∫⁻ _g, ENNReal.ofReal (β (x, _g)) ∂circularVectorLaw (Fin r)
        = ∫⁻ x, ENNReal.ofReal (cutBump R x) := by
          refine lintegral_congr fun x => ?_
          simp [β, lintegral_const, measure_univ]
      _ ≤ ∫⁻ x, (Set.Icc (-(R + 1)) (R + 1)).indicator 1 x := by
          refine lintegral_mono fun x => ?_
          have := cutBump_le_indicator R x
          by_cases hx : x ∈ Set.Icc (-(R + 1)) (R + 1)
          · rw [Set.indicator_of_mem hx] at this ⊢
            exact ENNReal.ofReal_le_one.2 this
          · rw [Set.indicator_of_notMem hx] at this ⊢
            rw [ENNReal.ofReal_eq_zero.2 this]
      _ = ENNReal.ofReal (2 * R + 2) := by
          rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
          congr 1; ring
  have hdiff : |∫ ω, u ω ∂P - ∫ ω, v ω ∂P| ≤ ∫ ω, |u ω - v ω| ∂P := by
    rw [← integral_sub (hbd u hum hu1) (hbd v hvm hv1)]
    exact abs_integral_le_integral_abs
  refine hdiff.trans ?_
  have hm' : Measurable fun ω => |u ω - v ω| := (hum.sub hvm).abs
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => abs_nonneg (u ω - v ω))
    hm'.aestronglyMeasurable]
  have hfin : ∫⁻ ω, ENNReal.ofReal η * B ω ∂P ≤ ENNReal.ofReal (η * (2 * R + 2)) := by
    rw [lintegral_const_mul _ hBm, ENNReal.ofReal_mul hη.le]
    exact mul_le_mul_right hmean _
  have hle := (lintegral_mono hpt).trans hfin
  have hnn : 0 ≤ η * (2 * R + 2) := by positivity
  calc (∫⁻ ω, ENNReal.ofReal |u ω - v ω| ∂P).toReal ≤
        (ENNReal.ofReal (η * (2 * R + 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = η * (2 * R + 2) := ENNReal.toReal_ofReal hnn

end BlockBand.Critical.MatrixClosing.Poles
