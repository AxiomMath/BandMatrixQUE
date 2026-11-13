module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Uniform weak comparison of nonnegative random vectors from Laplace transforms

Support for the common-port ratios theorem and Step 2 of the two-positive-clocks lemma: their
Gaussian integral identities compare the joint Laplace transforms of all required positive
quadratic forms; uniform first moments give tightness, and uniqueness of multivariate Laplace
transforms gives uniform weak comparison. The subsequence/uniqueness argument is replaced here
by a direct quantitative one: on the compactified variables `u = e^{-x} ∈ [0,1]^n`,
Stone–Weierstrass approximates `ψ(min(x,R))` uniformly by a polynomial in `e^{-x_i}`, i.e. by a
finite combination of exponentials `e^{-⟨m,x⟩}`, `m ∈ ℕ^n`; the tails `x_i > R` are paid by the
exponential bound `1_{x > R} ≤ (1 - e^{-1})⁻¹ (1 - e^{-x/R})` and the first moments of the
reference law, transferred to the compared law by the Laplace transform at `e_i/R`.

Main statement (unconditional, no contract consumed): `exists_laplace_comparison`. Fixed first:
the dimension `n`, a continuous test `ψ : ℝⁿ → ℝ` with `|ψ| ≤ M`, a first-moment bound `K` and
`ε > 0`. Then there are `η > 0` and `N` such that for **all** probability spaces and measurable
random vectors `X, Y ≥ 0` (pointwise) with `E Y_i ≤ K` and
`|E e^{-⟨λ,X⟩} - E e^{-⟨λ,Y⟩}| ≤ η` for all `λ ∈ [0,N]ⁿ`, one has `|E ψ(X) - E ψ(Y)| ≤ ε`.
`η, N` depend only on `n, ψ, M, K, ε` (uniformity).

Also: `CommonPortRatios.abs_sub_le_two_mul_exp_neg` (`1_{x<u} ≤ e·e^{-x/u}`, the small-denominator
device of the common-port ratios theorem and the two-positive-clocks lemma).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory

universe u v

/-!
## 1. Polynomials in `e^{-x_i}`
-/

/-- `P(e^{-x})` for a real polynomial `P` in `n` variables. -/
def CommonPortRatios.expPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval (fun i => Real.exp (-x i)) p

theorem CommonPortRatios.continuous_expPoly {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Continuous (CommonPortRatios.expPoly p) :=
  (MvPolynomial.continuous_eval p).comp (by fun_prop)

/-- `P(e^{-x}) = Σ_m c_m e^{-⟨m,x⟩}`. -/
theorem CommonPortRatios.expPoly_eq_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    CommonPortRatios.expPoly p x = ∑ m ∈ p.support, p.coeff m * Real.exp (-∑ i, (m i : ℝ) * x i) := by
  unfold CommonPortRatios.expPoly
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.exp_nat_mul]
  ring_nf

/-- `|P(e^{-x})| ≤ Σ_m |c_m|` on the nonnegative orthant. -/
theorem CommonPortRatios.abs_expPoly_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 ≤ x i) : |CommonPortRatios.expPoly p x| ≤ ∑ m ∈ p.support, |p.coeff m| := by
  rw [CommonPortRatios.expPoly_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  have h0 : 0 ≤ ∑ i, (m i : ℝ) * x i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hx i)
  have h1 : |Real.exp (-∑ i, (m i : ℝ) * x i)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_one_iff.mpr (by linarith)
  calc |p.coeff m| * |Real.exp (-∑ i, (m i : ℝ) * x i)| ≤ |p.coeff m| * 1 :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |p.coeff m| := mul_one _

/-- `-log(max(e^{-x}, e^{-R})) = min(x, R)`. -/
theorem CommonPortRatios.neg_log_max_exp (x R : ℝ) : -Real.log (max (Real.exp (-x)) (Real.exp (-R))) = min x R := by
  rcases le_total x R with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (by linarith)), Real.log_exp, min_eq_left h, neg_neg]
  · rw [max_eq_right (Real.exp_le_exp.mpr (by linarith)), Real.log_exp, min_eq_right h, neg_neg]

/-- **Stone–Weierstrass in the compactified variables.** For a continuous `ψ`, a cutoff `R`
and `η > 0` there is a polynomial `P` with `|ψ(min(x,R)) - P(e^{-x})| ≤ η` on the whole
nonnegative orthant. -/
theorem CommonPortRatios.exists_expPoly_approx {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) (hψ : Continuous ψ) (R : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ p : MvPolynomial (Fin n) ℝ, ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      |ψ (fun i => min (x i) R) - CommonPortRatios.expPoly p x| ≤ η := by
  let S : Set (Fin n → ℝ) := Set.Icc 0 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let φ : (Fin n → ℝ) → ℝ := fun w => ψ (fun i => -Real.log (max (w i) (Real.exp (-R))))
  have hφ : Continuous φ := by
    refine hψ.comp (continuous_pi fun i => ?_)
    have hmax : Continuous (fun w : Fin n → ℝ => max (w i) (Real.exp (-R))) :=
      (continuous_apply i).max continuous_const
    exact (hmax.log fun w => (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne').neg
  let f : C(S, ℝ) := ⟨fun w => φ w, hφ.comp continuous_subtype_val⟩
  let c : Fin n → C(S, ℝ) := fun i => ⟨fun w => (w : Fin n → ℝ) i,
    (continuous_apply i).comp continuous_subtype_val⟩
  let A : Subalgebra ℝ C(S, ℝ) := (MvPolynomial.aeval c).range
  have hev : ∀ (q : MvPolynomial (Fin n) ℝ) (w : S),
      (MvPolynomial.aeval c q) w = MvPolynomial.eval (fun i => (w : Fin n → ℝ) i) q := by
    intro q w
    induction q using MvPolynomial.induction_on with
    | C a => simp [c]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, c]
  have hsep : A.SeparatesPoints := by
    intro w w' hne
    have : ∃ i, (w : Fin n → ℝ) i ≠ (w' : Fin n → ℝ) i := by
      by_contra hcon
      push Not at hcon
      exact hne (Subtype.ext (funext hcon))
    obtain ⟨i, hi⟩ := this
    refine ⟨c i, ⟨c i, ⟨MvPolynomial.X i, MvPolynomial.aeval_X c i⟩, rfl⟩, hi⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    A hsep f η hη
  obtain ⟨p, hp⟩ := g.2
  have hp' : MvPolynomial.aeval c p = (g : C(S, ℝ)) := hp
  refine ⟨p, fun x hx => ?_⟩
  let w : S := ⟨fun i => Real.exp (-x i), fun i => (Real.exp_pos _).le,
    fun i => Real.exp_le_one_iff.mpr (by linarith [hx i])⟩
  have hfw : f w = ψ (fun i => min (x i) R) := by
    show φ (fun i => Real.exp (-x i)) = _
    simp only [φ, CommonPortRatios.neg_log_max_exp]
  have hgw : (g : C(S, ℝ)) w = CommonPortRatios.expPoly p x := by
    rw [← hp', hev]; rfl
  rw [← hfw, ← hgw, abs_sub_comm]
  have := ContinuousMap.norm_coe_le_norm ((g : C(S, ℝ)) - f) w
  rw [Real.norm_eq_abs] at this
  exact this.trans hg.le

/-!
## 2. Elementary exponential bounds
-/

/-- `1 - e^{-t} ≤ t`. -/
theorem CommonPortRatios.one_sub_exp_neg_le (t : ℝ) : 1 - Real.exp (-t) ≤ t := by
  linarith [Real.add_one_le_exp (-t)]

/-- `0 ≤ 1 - e^{-t}` for `t ≥ 0`. -/
theorem CommonPortRatios.one_sub_exp_neg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 - Real.exp (-t) := by
  have : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- The tail constant `c = (1 - e^{-1})⁻¹`. -/
def CommonPortRatios.tailConst : ℝ := (1 - Real.exp (-1))⁻¹

theorem CommonPortRatios.one_sub_exp_neg_one_pos : 0 < 1 - Real.exp (-1) := by
  have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

theorem CommonPortRatios.tailConst_pos : 0 < CommonPortRatios.tailConst := inv_pos.mpr CommonPortRatios.one_sub_exp_neg_one_pos

/-- `1 ≤ c (1 - e^{-x/R})` when `x > R > 0`. -/
theorem CommonPortRatios.one_le_tailConst_mul {x R : ℝ} (hR : 0 < R) (hx : R < x) :
    1 ≤ CommonPortRatios.tailConst * (1 - Real.exp (-(x / R))) := by
  have h1 : 1 < x / R := (one_lt_div hR).mpr hx
  have h2 : Real.exp (-(x / R)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h3 : 1 - Real.exp (-1) ≤ 1 - Real.exp (-(x / R)) := by linarith
  unfold CommonPortRatios.tailConst
  rw [← div_eq_inv_mul, le_div_iff₀ CommonPortRatios.one_sub_exp_neg_one_pos]
  linarith

/-- The cutoff error: `|ψ(x) - ψ(min(x,R))| ≤ 2Mc Σ_i (1 - e^{-x_i/R})` on the orthant. -/
theorem CommonPortRatios.abs_sub_cutoff_le {n : ℕ} (ψ : (Fin n → ℝ) → ℝ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M)
    {R : ℝ} (hR : 0 < R) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    |ψ x - ψ (fun i => min (x i) R)| ≤
      2 * M * CommonPortRatios.tailConst * ∑ i, (1 - Real.exp (-(x i / R))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hterm : ∀ i, 0 ≤ 1 - Real.exp (-(x i / R)) := fun i =>
    CommonPortRatios.one_sub_exp_neg_nonneg (div_nonneg (hx i) hR.le)
  have hsum0 : 0 ≤ ∑ i, (1 - Real.exp (-(x i / R))) := Finset.sum_nonneg fun i _ => hterm i
  by_cases hall : ∀ i, x i ≤ R
  · have : (fun i => min (x i) R) = x := funext fun i => min_eq_left (hall i)
    rw [this, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by linarith) CommonPortRatios.tailConst_pos.le) hsum0
  · push Not at hall
    obtain ⟨j, hj⟩ := hall
    have h1 : 1 ≤ CommonPortRatios.tailConst * ∑ i, (1 - Real.exp (-(x i / R))) :=
      (CommonPortRatios.one_le_tailConst_mul hR hj).trans (mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ j)) CommonPortRatios.tailConst_pos.le)
    calc |ψ x - ψ (fun i => min (x i) R)| ≤ |ψ x| + |ψ (fun i => min (x i) R)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM x, hM (fun i => min (x i) R)]
      _ = 2 * M * 1 := (mul_one _).symm
      _ ≤ 2 * M * (CommonPortRatios.tailConst * ∑ i, (1 - Real.exp (-(x i / R)))) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = _ := by ring

/-- Small-denominator device: if `f = g` wherever `x ≥ u`, `|f|, |g| ≤ M` and `x ≥ 0`, then
`|f - g| ≤ 2M e · e^{-x/u}` (`1_{x<u} ≤ e·e^{-x/u}`). -/
theorem CommonPortRatios.abs_sub_le_two_mul_exp_neg {f g x u M : ℝ} (hu : 0 < u)
    (hf : |f| ≤ M) (hg : |g| ≤ M) (hfg : u ≤ x → f = g) :
    |f - g| ≤ 2 * M * Real.exp 1 * Real.exp (-(x / u)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hf
  by_cases hxu : u ≤ x
  · rw [hfg hxu, sub_self, abs_zero]; positivity
  · push Not at hxu
    have h1 : 1 ≤ Real.exp 1 * Real.exp (-(x / u)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have : x / u < 1 := (div_lt_one hu).mpr hxu
      linarith
    calc |f - g| ≤ |f| + |g| := abs_sub _ _
      _ ≤ 2 * M * 1 := by linarith
      _ ≤ 2 * M * (Real.exp 1 * Real.exp (-(x / u))) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = _ := by ring

/-!
## 3. The uniform comparison
-/

/-- A bounded measurable function is integrable for a probability measure. -/
theorem CommonPortRatios.integrable_of_abs_le {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- `e^{-Σ λ_i x_i}` is in `(0,1]` on the orthant. -/
theorem CommonPortRatios.abs_exp_neg_sum_le_one {n : ℕ} {lam x : Fin n → ℝ} (hl : ∀ i, 0 ≤ lam i)
    (hx : ∀ i, 0 ≤ x i) : |Real.exp (-∑ i, lam i * x i)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (hx i)

/-- **Uniform weak comparison from Laplace transforms.**
`n`, a continuous `ψ` with `|ψ| ≤ M`, a first-moment bound `K` and `ε > 0` are fixed first; the
resulting `η > 0` and `N` work for every pair of laws. -/
theorem exists_laplace_comparison (n : ℕ) (ψ : (Fin n → ℝ) → ℝ) (hψ : Continuous ψ) {M : ℝ}
    (hM : ∀ x, |ψ x| ≤ M) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N : ℝ, 1 ≤ N ∧
      ∀ {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (μ : Measure Ω) (ν : Measure Ω'), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      ∀ (X : Ω → Fin n → ℝ) (Y : Ω' → Fin n → ℝ), Measurable X → Measurable Y →
        (∀ ω i, 0 ≤ X ω i) → (∀ ω i, 0 ≤ Y ω i) →
        (∀ i, Integrable (fun ω => Y ω i) ν) → (∀ i, ∫ ω, Y ω i ∂ν ≤ K) →
        (∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, lam i ≤ N) →
          |(∫ ω, Real.exp (-∑ i, lam i * X ω i) ∂μ) -
            ∫ ω, Real.exp (-∑ i, lam i * Y ω i) ∂ν| ≤ η) →
        |(∫ ω, ψ (X ω) ∂μ) - ∫ ω, ψ (Y ω) ∂ν| ≤ ε := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set K' := max K 0
  set A := 2 * M * CommonPortRatios.tailConst * n
  have hA0 : 0 ≤ A := by have := CommonPortRatios.tailConst_pos; positivity
  set R := max 1 (8 * A * K' / ε)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hAKR : A * K' / R ≤ ε / 8 := by
    rw [div_le_iff₀ hR0]
    have h8 : 8 * A * K' / ε ≤ R := le_max_right _ _
    rw [div_le_iff₀ hε] at h8
    nlinarith
  obtain ⟨p, hp⟩ := CommonPortRatios.exists_expPoly_approx ψ hψ R (show 0 < ε / 8 by positivity)
  set B := ∑ m ∈ p.support, |p.coeff m|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun m _ => abs_nonneg _
  set N : ℝ := 1 + ∑ m ∈ p.support, ∑ i, (m i : ℝ)
  have hN1 : 1 ≤ N := by
    have : 0 ≤ ∑ m ∈ p.support, ∑ i, (m i : ℝ) :=
      Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    linarith
  have hmN : ∀ m ∈ p.support, ∀ i, (m i : ℝ) ≤ N := by
    intro m hm i
    have h1 : (m i : ℝ) ≤ ∑ j, (m j : ℝ) :=
      Finset.single_le_sum (fun j _ => Nat.cast_nonneg (m j)) (Finset.mem_univ i)
    have h2 : ∑ j, (m j : ℝ) ≤ ∑ m' ∈ p.support, ∑ j, (m' j : ℝ) :=
      Finset.single_le_sum (f := fun m' : Fin n →₀ ℕ => ∑ j, (m' j : ℝ))
        (fun m' _ => Finset.sum_nonneg fun j _ => Nat.cast_nonneg _) hm
    linarith
  set η := ε / (2 * (A + B + 1))
  have hη : 0 < η := by positivity
  refine ⟨η, hη, N, hN1, ?_⟩
  intro Ω Ω' _ _ μ ν hμ hν X Y hX hY hX0 hY0 hYi hYK hlap
  -- pointwise approximation with tails
  have hpt : ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) →
      |ψ x - CommonPortRatios.expPoly p x| ≤ ε / 8 + 2 * M * CommonPortRatios.tailConst * ∑ i, (1 - Real.exp (-(x i / R))) := by
    intro x hx
    have h1 := CommonPortRatios.abs_sub_cutoff_le ψ hM hR0 hx
    have h2 := hp x hx
    calc |ψ x - CommonPortRatios.expPoly p x| ≤ |ψ x - ψ (fun i => min (x i) R)| +
          |ψ (fun i => min (x i) R) - CommonPortRatios.expPoly p x| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  -- integrability
  have hψX : Integrable (fun ω => ψ (X ω)) μ :=
    CommonPortRatios.integrable_of_abs_le μ (hψ.measurable.comp hX) M fun ω => hM _
  have hψY : Integrable (fun ω => ψ (Y ω)) ν :=
    CommonPortRatios.integrable_of_abs_le ν (hψ.measurable.comp hY) M fun ω => hM _
  have hPX : Integrable (fun ω => CommonPortRatios.expPoly p (X ω)) μ :=
    CommonPortRatios.integrable_of_abs_le μ ((CommonPortRatios.continuous_expPoly p).measurable.comp hX) B
      fun ω => CommonPortRatios.abs_expPoly_le p (hX0 ω)
  have hPY : Integrable (fun ω => CommonPortRatios.expPoly p (Y ω)) ν :=
    CommonPortRatios.integrable_of_abs_le ν ((CommonPortRatios.continuous_expPoly p).measurable.comp hY) B
      fun ω => CommonPortRatios.abs_expPoly_le p (hY0 ω)
  have hexpX : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) →
      Integrable (fun ω => Real.exp (-∑ i, lam i * X ω i)) μ := fun lam hl =>
    CommonPortRatios.integrable_of_abs_le μ (by fun_prop) 1 fun ω => CommonPortRatios.abs_exp_neg_sum_le_one hl (hX0 ω)
  have hexpY : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) →
      Integrable (fun ω => Real.exp (-∑ i, lam i * Y ω i)) ν := fun lam hl =>
    CommonPortRatios.integrable_of_abs_le ν (by fun_prop) 1 fun ω => CommonPortRatios.abs_exp_neg_sum_le_one hl (hY0 ω)
  have hIX : ∀ i, Integrable (fun ω => 1 - Real.exp (-(X ω i / R))) μ := fun i =>
    (integrable_const 1).sub (CommonPortRatios.integrable_of_abs_le μ (by fun_prop) 1 fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by have := div_nonneg (hX0 ω i) hR0.le; linarith))
  have hIY : ∀ i, Integrable (fun ω => 1 - Real.exp (-(Y ω i / R))) ν := fun i =>
    (integrable_const 1).sub (CommonPortRatios.integrable_of_abs_le ν (by fun_prop) 1 fun ω => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by have := div_nonneg (hY0 ω i) hR0.le; linarith))
  -- the tail functional
  set tl : (Fin n → ℝ) → ℝ := fun x => ∑ i, (1 - Real.exp (-(x i / R)))
  have htlX : Integrable (fun ω => tl (X ω)) μ :=
    integrable_finsetSum Finset.univ fun i _ => hIX i
  have htlY : Integrable (fun ω => tl (Y ω)) ν :=
    integrable_finsetSum Finset.univ fun i _ => hIY i
  -- tails of `Y`: `E(1 - e^{-Y_i/R}) ≤ K'/R`
  have htailY : ∀ i, ∫ ω, (1 - Real.exp (-(Y ω i / R))) ∂ν ≤ K' / R := by
    intro i
    calc ∫ ω, (1 - Real.exp (-(Y ω i / R))) ∂ν ≤ ∫ ω, Y ω i / R ∂ν := by
          exact integral_mono (hIY i) ((hYi i).div_const R) fun ω => CommonPortRatios.one_sub_exp_neg_le _
      _ = (∫ ω, Y ω i ∂ν) / R := integral_div _ _
      _ ≤ K' / R := div_le_div_of_nonneg_right ((hYK i).trans (le_max_left _ _)) hR0.le
  -- tails of `X` through the Laplace transform at `e_i / R`
  have htailX : ∀ i, ∫ ω, (1 - Real.exp (-(X ω i / R))) ∂μ ≤ K' / R + η := by
    intro i
    set lam : Fin n → ℝ := fun j => if j = i then R⁻¹ else 0
    have hl0 : ∀ j, 0 ≤ lam j := fun j => by
      simp only [lam]; split_ifs <;> positivity
    have hlN : ∀ j, lam j ≤ N := fun j => by
      simp only [lam]; split_ifs
      · exact (inv_le_one_of_one_le₀ hR1).trans hN1
      · linarith
    have hsum : ∀ x : Fin n → ℝ, ∑ j, lam j * x j = x i / R := by
      intro x
      simp only [lam, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hL := hlap lam hl0 hlN
    simp only [hsum] at hL
    have eX : ∫ ω, (1 - Real.exp (-(X ω i / R))) ∂μ = 1 - ∫ ω, Real.exp (-(X ω i / R)) ∂μ := by
      rw [integral_sub (integrable_const 1), integral_const, probReal_univ, one_smul]
      have := hexpX lam hl0; simp only [hsum] at this; exact this
    have eY : ∫ ω, (1 - Real.exp (-(Y ω i / R))) ∂ν = 1 - ∫ ω, Real.exp (-(Y ω i / R)) ∂ν := by
      rw [integral_sub (integrable_const 1), integral_const, probReal_univ, one_smul]
      have := hexpY lam hl0; simp only [hsum] at this; exact this
    have := htailY i
    rw [eY] at this
    rw [eX]
    linarith [(abs_le.mp hL).1]
  have hTX : ∫ ω, tl (X ω) ∂μ ≤ n * (K' / R + η) := by
    simp only [tl]
    rw [integral_finsetSum _ fun i _ => hIX i]
    calc ∑ i, ∫ ω, (1 - Real.exp (-(X ω i / R))) ∂μ ≤ ∑ _i : Fin n, (K' / R + η) :=
          Finset.sum_le_sum fun i _ => htailX i
      _ = n * (K' / R + η) := by simp; ring
  have hTY : ∫ ω, tl (Y ω) ∂ν ≤ n * (K' / R) := by
    simp only [tl]
    rw [integral_finsetSum _ fun i _ => hIY i]
    calc ∑ i, ∫ ω, (1 - Real.exp (-(Y ω i / R))) ∂ν ≤ ∑ _i : Fin n, K' / R :=
          Finset.sum_le_sum fun i _ => htailY i
      _ = n * (K' / R) := by simp
  -- the three pieces
  have hX1 : |(∫ ω, ψ (X ω) ∂μ) - ∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ| ≤
      ε / 8 + 2 * M * CommonPortRatios.tailConst * (n * (K' / R + η)) := by
    rw [← integral_sub hψX hPX]
    calc |∫ ω, (ψ (X ω) - CommonPortRatios.expPoly p (X ω)) ∂μ|
        ≤ ∫ ω, (ε / 8 + 2 * M * CommonPortRatios.tailConst * tl (X ω)) ∂μ := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le ((integrable_const _).add (htlX.const_mul _))
            (Filter.Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]; exact hpt _ (hX0 ω)
      _ = ε / 8 + 2 * M * CommonPortRatios.tailConst * ∫ ω, tl (X ω) ∂μ := by
          rw [integral_add (integrable_const _) (htlX.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul]
      _ ≤ _ := by
          have : 0 ≤ 2 * M * CommonPortRatios.tailConst := by have := CommonPortRatios.tailConst_pos; positivity
          nlinarith
  have hY1 : |(∫ ω, ψ (Y ω) ∂ν) - ∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν| ≤
      ε / 8 + 2 * M * CommonPortRatios.tailConst * (n * (K' / R)) := by
    rw [← integral_sub hψY hPY]
    calc |∫ ω, (ψ (Y ω) - CommonPortRatios.expPoly p (Y ω)) ∂ν|
        ≤ ∫ ω, (ε / 8 + 2 * M * CommonPortRatios.tailConst * tl (Y ω)) ∂ν := by
          rw [← Real.norm_eq_abs]
          refine norm_integral_le_of_norm_le ((integrable_const _).add (htlY.const_mul _))
            (Filter.Eventually.of_forall fun ω => ?_)
          rw [Real.norm_eq_abs]; exact hpt _ (hY0 ω)
      _ = ε / 8 + 2 * M * CommonPortRatios.tailConst * ∫ ω, tl (Y ω) ∂ν := by
          rw [integral_add (integrable_const _) (htlY.const_mul _), integral_const,
            probReal_univ, one_smul, integral_const_mul]
      _ ≤ _ := by
          have : 0 ≤ 2 * M * CommonPortRatios.tailConst := by have := CommonPortRatios.tailConst_pos; positivity
          nlinarith
  have hP : |(∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ) - ∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν| ≤ B * η := by
    have hm0 : ∀ m : Fin n →₀ ℕ, ∀ i, 0 ≤ (m i : ℝ) := fun m i => Nat.cast_nonneg _
    have eX : ∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ =
        ∑ m ∈ p.support, p.coeff m * ∫ ω, Real.exp (-∑ i, (m i : ℝ) * X ω i) ∂μ := by
      simp_rw [CommonPortRatios.expPoly_eq_sum]
      rw [integral_finsetSum _ fun m _ => (hexpX _ (hm0 m)).const_mul _]
      simp_rw [integral_const_mul]
    have eY : ∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν =
        ∑ m ∈ p.support, p.coeff m * ∫ ω, Real.exp (-∑ i, (m i : ℝ) * Y ω i) ∂ν := by
      simp_rw [CommonPortRatios.expPoly_eq_sum]
      rw [integral_finsetSum _ fun m _ => (hexpY _ (hm0 m)).const_mul _]
      simp_rw [integral_const_mul]
    rw [eX, eY, ← Finset.sum_sub_distrib, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hlap _ (hm0 m) (hmN m hm)) (abs_nonneg _)
  -- assemble
  have hfin : (A + B) * η ≤ ε / 2 := by
    have h1 : (A + B) * η ≤ (A + B + 1) * η := by nlinarith
    have h2 : (A + B + 1) * η = ε / 2 := by
      simp only [η]; field_simp
    linarith
  have hAeq : 2 * M * CommonPortRatios.tailConst * (n * (K' / R + η)) = A * K' / R + A * η := by
    simp only [A]; ring
  have hAeq' : 2 * M * CommonPortRatios.tailConst * (n * (K' / R)) = A * K' / R := by
    simp only [A]; ring
  calc |(∫ ω, ψ (X ω) ∂μ) - ∫ ω, ψ (Y ω) ∂ν|
      ≤ |(∫ ω, ψ (X ω) ∂μ) - ∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ| +
        |(∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ) - ∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν| +
        |(∫ ω, ψ (Y ω) ∂ν) - ∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν| := by
        have := abs_sub_le (∫ ω, ψ (X ω) ∂μ) (∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ) (∫ ω, ψ (Y ω) ∂ν)
        have h2 := abs_sub_le (∫ ω, CommonPortRatios.expPoly p (X ω) ∂μ) (∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν)
          (∫ ω, ψ (Y ω) ∂ν)
        rw [abs_sub_comm (∫ ω, CommonPortRatios.expPoly p (Y ω) ∂ν)] at h2
        linarith
    _ ≤ (ε / 8 + (A * K' / R + A * η)) + B * η + (ε / 8 + A * K' / R) := by
        rw [← hAeq, ← hAeq']; linarith
    _ ≤ ε := by nlinarith

end BlockBand.Endpoints.Clock
