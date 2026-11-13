module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineInclusion
public import BlockBand.GaussianBulk.ExternalSineCount
public import BlockBand.GaussianBulk.ExternalSineSine
public import BlockBand.GaussianBulk.KernelAlgebra

/-!
# Finite Laplace expansion of the unfolded deformed-GUE spectrum

The finite-`N` side of the Laplace clause of the external-source sine-kernel theorem.

Law: `deformedGUELaw N t F hF` (`F + √t G_N`, Johansson coordinates at `S = t/N`), for every
`N`, `t`, Hermitian `F`, real `E`, `ρ`. For a nonnegative continuous `f` and
`φ = 1 - e^{-f}` (`laplaceWeight f`):

* `unfoldedLaplace_eq_sum`: `E exp(-Σ_i f(Nρ(λ_i-E))) = Σ_{k=0}^N (-1)^k/k! ∫ ∏_j φ(Nρ(x_j-E))
  d(deformedFactorialCorrelation k)` (exact inclusion–exclusion);
* `integral_unfoldedObservable_le`: if `f = 0` off `[-L,L]`, `N, t, ρ > 0`, the `k`-th term is
  in `[0, (C/√t · N · 2L/(Nρ))^k]`, `C` the PSSS constant (`PSSS.SourceContract` only);
* `integral_withDensity_rescale` (proved in the sibling module `ExternalSineRescale`): for a correlation measure `withDensity (ofReal Re det[K])`
  with continuous kernel and any real gauge `h`, the `k`-th term equals
  `∫ ∏ φ(ξ_j) · max(Re det[e^{-h(ξ_i)} K(E+ξ_i/s, E+ξ_j/s) e^{h(ξ_j)}/s], 0) dξ`, `s = Nρ > 0`,
  Lebesgue measure on `ℝ^k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory ProbabilityTheory Set Finset
open BlockBand.External
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- `φ = 1 - e^{-f}`. -/
def laplaceWeight (f : ℝ → ℝ) (y : ℝ) : ℝ := 1 - Real.exp (-f y)

/-- The unfolded product observable `∏_j φ(s (x_j - E))` on `ℝ^k`. -/
def unfoldedObservable (s E : ℝ) (φ : ℝ → ℝ) {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  ∏ j, φ (s * (x j - E))

/-- `φ = 1 - e^{-f} ≥ 0` for `f ≥ 0`. -/
theorem laplaceWeight_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (y : ℝ) : 0 ≤ laplaceWeight f y := by
  have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf y))
  unfold laplaceWeight
  linarith

/-- `φ = 1 - e^{-f} ≤ 1` for every real `f`. -/
theorem laplaceWeight_le_one (f : ℝ → ℝ) (y : ℝ) : laplaceWeight f y ≤ 1 := by
  have := Real.exp_pos (-f y)
  unfold laplaceWeight
  linarith

/-- `φ = 1 - e^{-f}` is continuous for continuous `f`. -/
theorem continuous_laplaceWeight {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (laplaceWeight f) :=
  continuous_const.sub (Real.continuous_exp.comp hf.neg)

/-- The unfolded product observable is continuous on `ℝ^k`. -/
theorem continuous_unfoldedObservable (s E : ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ) (k : ℕ) :
    Continuous (fun x : Fin k → ℝ => unfoldedObservable s E φ x) :=
  continuous_finsetProd _ fun j _ =>
    hφ.comp (continuous_const.mul ((continuous_apply j).sub continuous_const))

/-- The unfolded product observable lies in `[0, 1]` for weights in `[0, 1]`. -/
theorem unfoldedObservable_nonneg_le_one {φ : ℝ → ℝ} (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ 1)
    (s E : ℝ) {k : ℕ} (x : Fin k → ℝ) :
    0 ≤ unfoldedObservable s E φ x ∧ unfoldedObservable s E φ x ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => h0 _, Finset.prod_le_one₀ (fun _ _ => h0 _) fun _ _ => h1 _⟩

/-- Pointwise inclusion–exclusion for the unfolded spectrum of one matrix. -/
theorem exp_neg_sum_eq_sum (N : ℕ) (A : Johansson.HermitianMatrix N) (E ρ : ℝ) (f : ℝ → ℝ) :
    Real.exp (-(∑ i, f ((N : ℝ) * ρ * (Model.Construction.orderedEigenvalue A i - E)))) =
      ∑ k ∈ range (N + 1), (-1 : ℝ) ^ k / (k.factorial : ℝ) *
        ∑ e : Fin k ↪ Fin N,
          unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f) (Johansson.spectralTuple e A) := by
  set u : Fin (Fintype.card (Fin N)) → ℝ :=
    fun i => (N : ℝ) * ρ * (Model.Construction.orderedEigenvalue A i - E) with hu
  have h1 : Real.exp (-(∑ i, f (u i))) = ∏ i, (1 - laplaceWeight f (u i)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [laplaceWeight]
  have h2 : ∏ i, (1 - laplaceWeight f (u i)) =
      ∏ i : Fin N, (1 - laplaceWeight f (u (Fin.cast (Fintype.card_fin N).symm i))) :=
    (Fintype.prod_equiv (finCongr (Fintype.card_fin N).symm) _ _ (fun i => rfl)).symm
  rw [h1, h2, prod_one_sub_eq_sum_embeddingSum]
  exact Finset.sum_congr (by rw [Fintype.card_fin]) fun k _ => rfl

/-- Integrals against the factorial correlation measure are integrals of tuple sums. -/
theorem integral_deformedFactorialCorrelation (N : ℕ) (t : ℝ≥0)
    (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (k : ℕ) (G : (Fin k → ℝ) → ℝ)
    (hG : Continuous G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) :
    (∫ x, G x ∂deformedFactorialCorrelation N t F hF k) =
      ∫ A, ∑ e : Fin k ↪ Fin N, G (Johansson.spectralTuple e A) ∂deformedGUELaw N t F hF := by
  have hP := isProbabilityMeasure_deformedGUELaw N t F hF
  have hint : ∀ e : Fin k ↪ Fin N,
      Integrable (fun A => G (Johansson.spectralTuple e A)) (deformedGUELaw N t F hF) := fun e =>
    Integrable.of_bound (hG.measurable.comp (Johansson.measurable_spectralTuple e)).aestronglyMeasurable
      B (Filter.Eventually.of_forall fun A => hB _)
  rw [integral_finsetSum _ fun e _ => hint e, deformedFactorialCorrelation,
    integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_map (Johansson.measurable_spectralTuple e).aemeasurable
      hG.aestronglyMeasurable]
  · intro e _
    have : IsProbabilityMeasure ((deformedGUELaw N t F hF).map (Johansson.spectralTuple e)) := by
      constructor
      rw [Measure.map_apply (Johansson.measurable_spectralTuple e) MeasurableSet.univ]
      simp
    exact Integrable.of_bound hG.aestronglyMeasurable B (Filter.Eventually.of_forall hB)

/-- Exact finite expansion of the unfolded Laplace functional of `F + √t G_N` (every `N`, `t`,
Hermitian `F`, real `E`, `ρ`; `f` continuous and nonnegative). -/
theorem unfoldedLaplace_eq_sum (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (E ρ : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    unfoldedLaplace N t F hF E ρ f =
      ∑ k ∈ range (N + 1), (-1 : ℝ) ^ k / (k.factorial : ℝ) *
        ∫ x, unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f) x
          ∂deformedFactorialCorrelation N t F hF k := by
  have hP := isProbabilityMeasure_deformedGUELaw N t F hF
  have hb := unfoldedObservable_nonneg_le_one (laplaceWeight_nonneg hf0) (laplaceWeight_le_one f)
  have hcont := continuous_unfoldedObservable ((N : ℝ) * ρ) E (continuous_laplaceWeight hf)
  have hnorm : ∀ k (x : Fin k → ℝ),
      ‖unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f) x‖ ≤ 1 := fun k x => by
    rw [Real.norm_of_nonneg (hb _ _ x).1]
    exact (hb _ _ x).2
  unfold unfoldedLaplace
  simp_rw [exp_neg_sum_eq_sum]
  have hint : ∀ k, Integrable (fun A : Johansson.HermitianMatrix N =>
      ∑ e : Fin k ↪ Fin N, unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f)
        (Johansson.spectralTuple e A)) (deformedGUELaw N t F hF) := fun k =>
    integrable_finsetSum _ fun e _ =>
      Integrable.of_bound ((hcont k).measurable.comp
        (Johansson.measurable_spectralTuple e)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun A => hnorm k _)
  rw [integral_finsetSum _ fun k _ => (hint k).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_deformedFactorialCorrelation N t F hF k _ (hcont k) 1
    (hnorm k)]

/-- Count of eigenvalues whose unfolded position lies in `[-L, L]`. -/
theorem eigenCount_eq_card_unfolded (N : ℕ) (A : Johansson.HermitianMatrix N) (E s L : ℝ)
    (hs : 0 < s) :
    PSSS.eigenCount A (Icc (E - L / s) (E + L / s)) =
      (univ.filter fun i : Fin N => s * (Model.Construction.orderedEigenvalue A
        (Fin.cast (Fintype.card_fin N).symm i) - E) ∈ Icc (-L) L).card := by
  classical
  unfold PSSS.eigenCount
  have hiff : ∀ y : ℝ, y ∈ Icc (E - L / s) (E + L / s) ↔ s * (y - E) ∈ Icc (-L) L := by
    intro y
    simp only [Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : -(L / s) ≤ y - E := by linarith
      have h2' : y - E ≤ L / s := by linarith
      constructor
      · have := mul_le_mul_of_nonneg_left h1' hs.le
        rwa [mul_neg, mul_div_cancel₀ _ hs.ne'] at this
      · have := mul_le_mul_of_nonneg_left h2' hs.le
        rwa [mul_div_cancel₀ _ hs.ne'] at this
    · rintro ⟨h1, h2⟩
      constructor
      · have : -(y - E) ≤ L / s := by
          rw [le_div_iff₀ hs]
          nlinarith
        linarith
      · have : y - E ≤ L / s := by
          rw [le_div_iff₀ hs]
          nlinarith
        linarith
  symm
  apply Finset.card_bij (fun i _ => Fin.cast (Fintype.card_fin N).symm i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact (hiff _).mpr hi
  · intro i _ j _ hij
    exact Fin.cast_injective _ hij
  · intro j hj
    refine ⟨Fin.cast (Fintype.card_fin N) j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have h := (hiff _).mp hj
    simpa [Model.Construction.orderedEigenvalue] using h

/-- PSSS bound for the `k`-th term of the expansion (`N, t, ρ > 0`; `f ≥ 0` continuous, zero
off `[-L, L]`, `L ≥ 0`). `C` is the constant of `deformedGUELaw_factorialCount_le`. -/
theorem integral_unfoldedObservable_le {C : ℝ}
    (hC : ∀ (N : ℕ), 0 < N → ∀ (t : ℝ≥0), 0 < t →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (a b : ℝ), a ≤ b →
      ∀ r : ℕ, 1 ≤ r →
        (∫ A, ((PSSS.eigenCount A (Icc a b)).descFactorial r : ℝ) ∂deformedGUELaw N t F hF) ≤
          (C / Real.sqrt t * (N : ℝ) * (b - a)) ^ r)
    (N : ℕ) (hN : 0 < N) (t : ℝ≥0) (ht : 0 < t) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (E ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (L : ℝ) (hL : 0 ≤ L) (hsupp : ∀ x, x ∉ Icc (-L) L → f x = 0) (k : ℕ) :
    0 ≤ (∫ x, unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f) x
          ∂deformedFactorialCorrelation N t F hF k) ∧
      (∫ x, unfoldedObservable ((N : ℝ) * ρ) E (laplaceWeight f) x
          ∂deformedFactorialCorrelation N t F hF k) ≤
        (C / Real.sqrt t * (2 * L / ρ)) ^ k := by
  have hP := isProbabilityMeasure_deformedGUELaw N t F hF
  set s : ℝ := (N : ℝ) * ρ with hs_def
  have hs : 0 < s := mul_pos (by exact_mod_cast hN) hρ
  have hb := unfoldedObservable_nonneg_le_one (laplaceWeight_nonneg hf0) (laplaceWeight_le_one f)
  have hcont := continuous_unfoldedObservable s E (continuous_laplaceWeight hf) k
  have hnorm : ∀ x : Fin k → ℝ, ‖unfoldedObservable s E (laplaceWeight f) x‖ ≤ 1 := fun x => by
    rw [Real.norm_of_nonneg (hb _ _ x).1]
    exact (hb _ _ x).2
  rw [integral_deformedFactorialCorrelation N t F hF k _ hcont 1 hnorm]
  -- pointwise bound by the factorial count
  set a : ℝ := E - L / s
  set b : ℝ := E + L / s
  have hpt : ∀ A : Johansson.HermitianMatrix N,
      0 ≤ ∑ e : Fin k ↪ Fin N, unfoldedObservable s E (laplaceWeight f)
          (Johansson.spectralTuple e A) ∧
        ∑ e : Fin k ↪ Fin N, unfoldedObservable s E (laplaceWeight f)
          (Johansson.spectralTuple e A) ≤
          ((PSSS.eigenCount A (Icc a b)).descFactorial k : ℝ) := by
    intro A
    rw [eigenCount_eq_card_unfolded N A E s L hs]
    exact embeddingSum_nonneg_le
      (fun i => laplaceWeight f (s * (Model.Construction.orderedEigenvalue A
        (Fin.cast (Fintype.card_fin N).symm i) - E))) _
      (fun i => laplaceWeight_nonneg hf0 _)
      (fun i => by
        split_ifs with hi
        · exact laplaceWeight_le_one f _
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp [laplaceWeight, hsupp _ hi])
      k
  have hmeas : Measurable (fun A : Johansson.HermitianMatrix N =>
      ((PSSS.eigenCount A (Icc a b)).descFactorial k : ℝ)) :=
    (Measurable.of_discrete (f := fun n : ℕ => (n.descFactorial k : ℝ))).comp
      (Counting.measurable_nativeEigenCount (Icc a b) measurableSet_Icc)
  have hcnt_int : Integrable (fun A : Johansson.HermitianMatrix N =>
      ((PSSS.eigenCount A (Icc a b)).descFactorial k : ℝ)) (deformedGUELaw N t F hF) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable ((N ^ k : ℕ) : ℝ)
      (Filter.Eventually.of_forall fun A => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := PSSS.eigenCount_le_dimension A (Icc a b)
    rw [Fintype.card_fin] at h1
    exact_mod_cast (Nat.descFactorial_le_pow _ k).trans (Nat.pow_le_pow_left h1 k)
  have hsum_int : Integrable (fun A : Johansson.HermitianMatrix N =>
      ∑ e : Fin k ↪ Fin N, unfoldedObservable s E (laplaceWeight f)
        (Johansson.spectralTuple e A)) (deformedGUELaw N t F hF) :=
    integrable_finsetSum _ fun e _ =>
      Integrable.of_bound (hcont.measurable.comp
        (Johansson.measurable_spectralTuple e)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun A => hnorm _)
  refine ⟨integral_nonneg fun A => (hpt A).1, ?_⟩
  refine (integral_mono hsum_int hcnt_int fun A => (hpt A).2).trans ?_
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · refine (hC N hN t ht F hF a b (by
      have : 0 ≤ L / s := div_nonneg hL hs.le
      simp only [a, b]; linarith) k hk).trans (le_of_eq ?_)
    congr 1
    simp only [a, b, hs_def]
    field_simp
    ring

end BlockBand.GaussianBulk
