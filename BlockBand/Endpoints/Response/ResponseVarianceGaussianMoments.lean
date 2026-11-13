module

public import BlockBand.Endpoints.Response.ResponseVarianceDefs
public import BlockBand.Model.Construction.GaussianIntegrationByParts

/-!
# Gaussian moments for the variance lower bound of the signed response

* Real centered Gaussian `x ~ N(0, v)`: `E x^{n+2} = (n+1) v E x^n` (Gaussian integration by
  parts), hence `E x² = v`, `E x⁴ = 3v²`, `E x⁸ = 105 v⁴`; for `d = x² - v`: `E d = 0`,
  `E d² = 2v²`, `E d⁴ ≤ 106 v⁴`.
* Independent centered real variables `Z_i` (any probability space, `iIndepFun`) with
  `E Z_i⁴ ≤ K (E Z_i²)²`, `K ≥ 3`: `E(Σ Z_i)² = Σ E Z_i²` and `E(Σ Z_i)⁴ ≤ K (Σ E Z_i²)²`
  (dimension-free).
* Applied to `Z_i = μ_i (r_i² - v)` under the product law `Π_i N(0, v)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
### Scalar Gaussian moments
-/

theorem rvG_integrable_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  have hn := (memLp_id_gaussianReal' (μ := 0) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow'
  refine hn.mono' (by fun_prop) ?_
  filter_upwards with x
  simp only [norm_pow, id_eq]
  exact le_rfl

/-- Gaussian integration by parts on monomials: `E x^{n+2} = (n+1) v E x^n`. -/
theorem rvG_integral_pow_add_two (v : ℝ≥0) (n : ℕ) :
    ∫ x : ℝ, x ^ (n + 2) ∂gaussianReal 0 v = (n + 1) * v * ∫ x : ℝ, x ^ n ∂gaussianReal 0 v := by
  have h := BlockBand.Model.Construction.centered_gaussian_integration_by_parts v
    (f := fun x : ℝ => x ^ (n + 1)) (f' := fun x : ℝ => ((n + 1 : ℕ) : ℝ) * x ^ n)
    (fun x => by simpa using hasDerivAt_pow (n + 1) x)
    (rvG_integrable_pow_gaussianReal v (n + 1))
    ((rvG_integrable_pow_gaussianReal v n).const_mul _)
    (by simpa [pow_succ, mul_comm] using rvG_integrable_pow_gaussianReal v (n + 2))
  have e : (fun x : ℝ => x * x ^ (n + 1)) = fun x => x ^ (n + 2) := by
    funext x; ring
  rw [e, integral_const_mul] at h
  rw [h]
  push_cast
  ring

theorem rvG_integral_pow_zero_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 0 ∂gaussianReal 0 v = 1 := by
  simp

theorem rvG_integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = v := by
  have := rvG_integral_pow_add_two v 0
  simp only [zero_add] at this
  rw [this]; simp

theorem rvG_integral_pow_four_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v = 3 * (v : ℝ) ^ 2 := by
  have := rvG_integral_pow_add_two v 2
  rw [this, rvG_integral_sq_gaussianReal]; push_cast; ring

theorem rvG_integral_pow_six_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 6 ∂gaussianReal 0 v = 15 * (v : ℝ) ^ 3 := by
  have := rvG_integral_pow_add_two v 4
  rw [this, rvG_integral_pow_four_gaussianReal]; push_cast; ring

theorem rvG_integral_pow_eight_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 8 ∂gaussianReal 0 v = 105 * (v : ℝ) ^ 4 := by
  have := rvG_integral_pow_add_two v 6
  rw [this, rvG_integral_pow_six_gaussianReal]; push_cast; ring

/-!
### The centered square `d = x² - v`
-/

theorem rvG_integrable_sqsub_pow (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => (x ^ 2 - v) ^ n) (gaussianReal 0 v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (fun x : ℝ => (x ^ 2 - v) ^ (n + 1)) =
        fun x => ((x ^ 2 - v) ^ n * x ^ 2) - (v : ℝ) * (x ^ 2 - v) ^ n := by
      funext x; ring
    rw [e]
    refine Integrable.sub ?_ (ih.const_mul _)
    -- `(x² - v)^n x²` is a polynomial: expand by the binomial theorem
    have e2 : (fun x : ℝ => (x ^ 2 - v) ^ n * x ^ 2) = fun x => ∑ k ∈ Finset.range (n + 1),
        (x ^ (2 * k + 2) * ((-(v : ℝ)) ^ (n - k) * (n.choose k : ℝ))) := by
      funext x
      rw [sub_eq_add_neg, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e2]
    exact integrable_finsetSum _ fun k _ =>
      (rvG_integrable_pow_gaussianReal v (2 * k + 2)).mul_const _

theorem rvG_integral_sqsub (v : ℝ≥0) :
    ∫ x : ℝ, (x ^ 2 - v) ∂gaussianReal 0 v = 0 := by
  rw [integral_sub (rvG_integrable_pow_gaussianReal v 2) (integrable_const _),
    rvG_integral_sq_gaussianReal]
  simp

theorem rvG_integral_sqsub_sq (v : ℝ≥0) :
    ∫ x : ℝ, (x ^ 2 - v) ^ 2 ∂gaussianReal 0 v = 2 * (v : ℝ) ^ 2 := by
  have e : (fun x : ℝ => (x ^ 2 - v) ^ 2) =
      fun x => x ^ 4 - (2 * (v : ℝ)) * x ^ 2 + (v : ℝ) ^ 2 := by
    funext x; ring
  have h1 : Integrable (fun x : ℝ => x ^ 4 - (2 * (v : ℝ)) * x ^ 2) (gaussianReal 0 v) :=
    (rvG_integrable_pow_gaussianReal v 4).sub ((rvG_integrable_pow_gaussianReal v 2).const_mul _)
  rw [e, integral_add h1 (integrable_const _),
    integral_sub (rvG_integrable_pow_gaussianReal v 4)
      ((rvG_integrable_pow_gaussianReal v 2).const_mul _),
    integral_const_mul, rvG_integral_pow_four_gaussianReal, rvG_integral_sq_gaussianReal]
  simp; ring

theorem rvG_integral_sqsub_four_le (v : ℝ≥0) :
    ∫ x : ℝ, (x ^ 2 - v) ^ 4 ∂gaussianReal 0 v ≤ 106 * (v : ℝ) ^ 4 := by
  have hb : ∀ x : ℝ, (x ^ 2 - v) ^ 4 ≤ x ^ 8 + (v : ℝ) ^ 4 := by
    intro x
    have hv : (0 : ℝ) ≤ v := v.2
    have hx : 0 ≤ x ^ 2 := sq_nonneg x
    rcases le_total (x ^ 2) (v : ℝ) with h | h
    · have h1 : (x ^ 2 - v) ^ 4 = ((v : ℝ) - x ^ 2) ^ 4 := by ring
      have h2 : ((v : ℝ) - x ^ 2) ^ 4 ≤ (v : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 4
      nlinarith [pow_nonneg hx 4, show x ^ 8 = (x ^ 2) ^ 4 by ring]
    · have h2 : (x ^ 2 - (v : ℝ)) ^ 4 ≤ (x ^ 2) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 4
      nlinarith [pow_nonneg hv 4, show x ^ 8 = (x ^ 2) ^ 4 by ring]
  calc ∫ x : ℝ, (x ^ 2 - v) ^ 4 ∂gaussianReal 0 v
      ≤ ∫ x : ℝ, (x ^ 8 + (v : ℝ) ^ 4) ∂gaussianReal 0 v :=
        integral_mono (rvG_integrable_sqsub_pow v 4)
          ((rvG_integrable_pow_gaussianReal v 8).add (integrable_const _)) hb
    _ = 106 * (v : ℝ) ^ 4 := by
        rw [integral_add (rvG_integrable_pow_gaussianReal v 8) (integrable_const _),
          rvG_integral_pow_eight_gaussianReal]
        simp; ring

/-!
### Fourth moment of an independent centered sum
-/

theorem rvG_integrable_pow_of_four {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ) {n : ℕ} (hn : n ≤ 4) :
    Integrable (fun ω => f ω ^ n) μ := by
  refine ((integrable_const (1 : ℝ)).add h4).mono' (hf.pow n) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow, Pi.add_apply]
  rcases le_total |f ω| 1 with h | h
  · have := pow_le_one₀ (abs_nonneg (f ω)) h (n := n)
    nlinarith [pow_nonneg (sq_nonneg (f ω)) 2, show f ω ^ 4 = (f ω ^ 2) ^ 2 by ring]
  · have h1 : |f ω| ^ n ≤ |f ω| ^ 4 := pow_le_pow_right₀ h hn
    have h2 : |f ω| ^ 4 = f ω ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    linarith

theorem rvG_indep_sum_moments {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq κ] (Z : κ → Ω → ℝ) (hZ : iIndepFun Z μ)
    (hmeas : ∀ i, Measurable (Z i)) (hint : ∀ i, Integrable (fun ω => Z i ω ^ 4) μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0) (K : ℝ) (hK : 3 ≤ K)
    (hfour : ∀ i, ∫ ω, Z i ω ^ 4 ∂μ ≤ K * (∫ ω, Z i ω ^ 2 ∂μ) ^ 2) (s : Finset κ) :
    Integrable (fun ω => (∑ i ∈ s, Z i ω) ^ 4) μ ∧ ∫ ω, ∑ i ∈ s, Z i ω ∂μ = 0 ∧
      ∫ ω, (∑ i ∈ s, Z i ω) ^ 2 ∂μ = ∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ ∧
      ∫ ω, (∑ i ∈ s, Z i ω) ^ 4 ∂μ ≤ K * (∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨hS4, hS1, hS2, hS4le⟩ := ih
    set S : Ω → ℝ := fun ω => ∑ j ∈ s, Z j ω with hSdef
    set W : Ω → ℝ := Z i with hWdef
    have hSm : Measurable S := Finset.measurable_sum s (fun j _ => hmeas j)
    have hWm : Measurable W := hmeas i
    have hind : IndepFun S W μ := by
      have := hZ.indepFun_finsetSum_of_notMem hmeas hi
      convert this using 1
      funext ω; simp [S]
    have hpow (a b : ℕ) : IndepFun (fun ω => S ω ^ a) (fun ω => W ω ^ b) μ :=
      hind.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
    have hSi (n : ℕ) (hn : n ≤ 4) : Integrable (fun ω => S ω ^ n) μ :=
      rvG_integrable_pow_of_four hSm.aestronglyMeasurable hS4 hn
    have hWi (n : ℕ) (hn : n ≤ 4) : Integrable (fun ω => W ω ^ n) μ :=
      rvG_integrable_pow_of_four hWm.aestronglyMeasurable (hint i) hn
    have hprodI (a b : ℕ) (ha : a ≤ 4) (hb : b ≤ 4) :
        Integrable (fun ω => S ω ^ a * W ω ^ b) μ :=
      (hpow a b).integrable_mul (hSi a ha) (hWi b hb)
    have hprod (a b : ℕ) :
        ∫ ω, S ω ^ a * W ω ^ b ∂μ = (∫ ω, S ω ^ a ∂μ) * ∫ ω, W ω ^ b ∂μ :=
      (hpow a b).integral_fun_mul_eq_mul_integral (hSm.pow_const a).aestronglyMeasurable
        (hWm.pow_const b).aestronglyMeasurable
    have hS1' : ∫ ω, S ω ^ 1 ∂μ = 0 := by simpa [S] using hS1
    have hW1' : ∫ ω, W ω ^ 1 ∂μ = 0 := by simpa [W] using hmean i
    have hsum (ω : Ω) : ∑ j ∈ insert i s, Z j ω = W ω + S ω := by
      rw [Finset.sum_insert hi]
    simp_rw [hsum]
    have e4 : (fun ω => (W ω + S ω) ^ 4) = fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * W ω ^ 1) +
        6 * (S ω ^ 2 * W ω ^ 2) + 4 * (S ω ^ 1 * W ω ^ 3) + W ω ^ 4 := by
      funext ω; ring
    have e2 : (fun ω => (W ω + S ω) ^ 2) = fun ω => S ω ^ 2 + 2 * (S ω ^ 1 * W ω ^ 1) +
        W ω ^ 2 := by
      funext ω; ring
    have i4 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * W ω ^ 1) +
        6 * (S ω ^ 2 * W ω ^ 2) + 4 * (S ω ^ 1 * W ω ^ 3) + W ω ^ 4) μ :=
      (((hS4.add ((hprodI 3 1 (by norm_num) (by norm_num)).const_mul 4)).add
        ((hprodI 2 2 (by norm_num) (by norm_num)).const_mul 6)).add
        ((hprodI 1 3 (by norm_num) (by norm_num)).const_mul 4)).add (hint i)
    have I4 : ∫ ω, (W ω + S ω) ^ 4 ∂μ =
        ∫ ω, S ω ^ 4 ∂μ + 6 * ((∫ ω, S ω ^ 2 ∂μ) * ∫ ω, W ω ^ 2 ∂μ) + ∫ ω, W ω ^ 4 ∂μ := by
      rw [e4, integral_add, integral_add, integral_add, integral_add, integral_const_mul,
        integral_const_mul, integral_const_mul, hprod, hprod, hprod, hS1', hW1']
      · ring
      all_goals first
        | exact hS4
        | exact hint i
        | exact (hprodI _ _ (by norm_num) (by norm_num)).const_mul _
        | exact hS4.add ((hprodI 3 1 (by norm_num) (by norm_num)).const_mul 4)
        | exact (hS4.add ((hprodI 3 1 (by norm_num) (by norm_num)).const_mul 4)).add
            ((hprodI 2 2 (by norm_num) (by norm_num)).const_mul 6)
        | exact ((hS4.add ((hprodI 3 1 (by norm_num) (by norm_num)).const_mul 4)).add
            ((hprodI 2 2 (by norm_num) (by norm_num)).const_mul 6)).add
            ((hprodI 1 3 (by norm_num) (by norm_num)).const_mul 4)
    have I2 : ∫ ω, (W ω + S ω) ^ 2 ∂μ = ∫ ω, S ω ^ 2 ∂μ + ∫ ω, W ω ^ 2 ∂μ := by
      rw [e2, integral_add, integral_add, integral_const_mul, hprod, hS1']
      · ring
      all_goals first
        | exact hSi 2 (by norm_num)
        | exact hWi 2 (by norm_num)
        | exact (hprodI _ _ (by norm_num) (by norm_num)).const_mul _
        | exact (hSi 2 (by norm_num)).add ((hprodI 1 1 (by norm_num) (by norm_num)).const_mul 2)
    have hQ : 0 ≤ ∫ ω, S ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hσ : 0 ≤ ∫ ω, W ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have hW4 := hfour i
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e4]; exact i4
    · rw [integral_add (hWi 1 (by norm_num) |>.congr (by simp)) (hSi 1 (by norm_num) |>.congr
        (by simp))]
      simp only [W] at hW1' ⊢
      simpa [S, hmean i] using hS1
    · rw [I2, Finset.sum_insert hi, hS2]
      simp only [W]; ring
    · rw [I4, Finset.sum_insert hi, ← hS2]
      have hS4le' : ∫ ω, S ω ^ 4 ∂μ ≤ K * (∫ ω, S ω ^ 2 ∂μ) ^ 2 := by
        rw [← hS2] at hS4le; exact hS4le
      have hW4' : ∫ ω, W ω ^ 4 ∂μ ≤ K * (∫ ω, W ω ^ 2 ∂μ) ^ 2 := hW4
      change _ ≤ K * (∫ ω, W ω ^ 2 ∂μ + ∫ ω, S ω ^ 2 ∂μ) ^ 2
      nlinarith [mul_nonneg hQ hσ]

/-!
### The product Gaussian law
-/

/-- Diagonal real Gaussian chaos `Z(r) = Σ_i m_i (r_i² - v)` under `Π_i N(0, v)`:
`E Z = 0`, `E Z² = 2v² Σ m_i²`, `E Z⁴ ≤ 27 (2v² Σ m_i²)²`. -/
theorem rvG_pi_chaos_moments {κ : Type*} [Fintype κ] [DecidableEq κ] (v : ℝ≥0) (m : κ → ℝ) :
    Integrable (fun r : κ → ℝ => (∑ i, m i * (r i ^ 2 - v)) ^ 4)
        (Measure.pi fun _ : κ => gaussianReal 0 v) ∧
      ∫ r, ∑ i, m i * (r i ^ 2 - v) ∂(Measure.pi fun _ : κ => gaussianReal 0 v) = 0 ∧
      ∫ r, (∑ i, m i * (r i ^ 2 - v)) ^ 2 ∂(Measure.pi fun _ : κ => gaussianReal 0 v) =
        2 * (v : ℝ) ^ 2 * ∑ i, m i ^ 2 ∧
      ∫ r, (∑ i, m i * (r i ^ 2 - v)) ^ 4 ∂(Measure.pi fun _ : κ => gaussianReal 0 v) ≤
        27 * (2 * (v : ℝ) ^ 2 * ∑ i, m i ^ 2) ^ 2 := by
  set P := Measure.pi fun _ : κ => gaussianReal 0 v
  let Z : κ → (κ → ℝ) → ℝ := fun i r => m i * (r i ^ 2 - v)
  have hZ : iIndepFun Z P :=
    iIndepFun_pi (X := fun i (x : ℝ) => m i * (x ^ 2 - v)) (fun i => by fun_prop)
  have hmeas : ∀ i, Measurable (Z i) := fun i => by fun_prop
  have hcomp (i : κ) (f : ℝ → ℝ) (hf : Integrable f (gaussianReal 0 v)) :
      Integrable (fun r : κ → ℝ => f (r i)) P :=
    integrable_comp_eval (μ := fun _ : κ => gaussianReal 0 v) hf
  have hcompI (i : κ) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (gaussianReal 0 v)) :
      ∫ r, f (r i) ∂P = ∫ x, f x ∂gaussianReal 0 v :=
    integral_comp_eval (μ := fun _ : κ => gaussianReal 0 v) hf
  have hint : ∀ i, Integrable (fun r => Z i r ^ 4) P := fun i => by
    have := hcomp i _ ((rvG_integrable_sqsub_pow v 4).const_mul (m i ^ 4))
    refine this.congr (Filter.Eventually.of_forall fun r => ?_)
    simp only [Z]; ring
  have hmean : ∀ i, ∫ r, Z i r ∂P = 0 := fun i => by
    simp only [Z]
    rw [integral_const_mul, hcompI i (fun x => x ^ 2 - (v : ℝ)) (by fun_prop),
      rvG_integral_sqsub, mul_zero]
  have h2 : ∀ i, ∫ r, Z i r ^ 2 ∂P = 2 * (v : ℝ) ^ 2 * m i ^ 2 := fun i => by
    have e : (fun r : κ → ℝ => Z i r ^ 2) = fun r => m i ^ 2 * (r i ^ 2 - v) ^ 2 := by
      funext r; simp only [Z]; ring
    rw [e, integral_const_mul, hcompI i (fun x => (x ^ 2 - (v : ℝ)) ^ 2) (by fun_prop),
      rvG_integral_sqsub_sq]
    ring
  have hfour : ∀ i, ∫ r, Z i r ^ 4 ∂P ≤ 27 * (∫ r, Z i r ^ 2 ∂P) ^ 2 := fun i => by
    have e : (fun r : κ → ℝ => Z i r ^ 4) = fun r => m i ^ 4 * (r i ^ 2 - v) ^ 4 := by
      funext r; simp only [Z]; ring
    rw [e, integral_const_mul, hcompI i (fun x => (x ^ 2 - (v : ℝ)) ^ 4) (by fun_prop), h2]
    have := rvG_integral_sqsub_four_le v
    have hm : 0 ≤ m i ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hm, pow_nonneg (v.2 : (0 : ℝ) ≤ v) 4]
  obtain ⟨i4, i1, i2, i4le⟩ :=
    rvG_indep_sum_moments Z hZ hmeas hint hmean 27 (by norm_num) hfour Finset.univ
  simp only [h2, ← Finset.mul_sum] at i2 i4le
  exact ⟨i4, i1, i2, i4le⟩

/-- Shift by a constant: `E(T + f)² = T² + E f²`, `E(T + f)⁴ ≤ 8(T⁴ + E f⁴)` for centered `f`. -/
theorem rvG_shift_moments {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ) (h0 : ∫ ω, f ω ∂μ = 0) (T : ℝ) :
    Integrable (fun ω => (T + f ω) ^ 4) μ ∧ Integrable (fun ω => (T + f ω) ^ 2) μ ∧
      ∫ ω, (T + f ω) ^ 2 ∂μ = T ^ 2 + ∫ ω, f ω ^ 2 ∂μ ∧
      ∫ ω, (T + f ω) ^ 4 ∂μ ≤ 8 * (T ^ 4 + ∫ ω, f ω ^ 4 ∂μ) := by
  have i1 := rvG_integrable_pow_of_four hf h4 (n := 1) (by norm_num)
  have i2 := rvG_integrable_pow_of_four hf h4 (n := 2) (by norm_num)
  have i3 := rvG_integrable_pow_of_four hf h4 (n := 3) (by norm_num)
  simp only [pow_one] at i1
  have e4 : (fun ω => (T + f ω) ^ 4) = fun ω => T ^ 4 + 4 * T ^ 3 * f ω + 6 * T ^ 2 * f ω ^ 2 +
      4 * T * f ω ^ 3 + f ω ^ 4 := by
    funext ω; ring
  have e2 : (fun ω => (T + f ω) ^ 2) = fun ω => T ^ 2 + 2 * T * f ω + f ω ^ 2 := by
    funext ω; ring
  have j4 : Integrable (fun ω => (T + f ω) ^ 4) μ := by
    rw [e4]
    exact ((((integrable_const _).add (i1.const_mul _)).add (i2.const_mul _)).add
      (i3.const_mul _)).add h4
  have j2 : Integrable (fun ω => (T + f ω) ^ 2) μ := by
    rw [e2]
    exact ((integrable_const _).add (i1.const_mul _)).add i2
  refine ⟨j4, j2, ?_, ?_⟩
  · have k : Integrable (fun ω => T ^ 2 + 2 * T * f ω) μ := (integrable_const _).add
      (i1.const_mul _)
    rw [e2, integral_add k i2, integral_add (integrable_const _) (i1.const_mul _),
      integral_const_mul, h0]
    simp
  · calc ∫ ω, (T + f ω) ^ 4 ∂μ ≤ ∫ ω, 8 * (T ^ 4 + f ω ^ 4) ∂μ := by
          refine integral_mono j4 (((integrable_const _).add h4).const_mul _) fun ω => ?_
          have a := sq_nonneg (T - f ω)
          have b := sq_nonneg (T + f ω)
          nlinarith [sq_nonneg (T ^ 2 - f ω ^ 2), mul_nonneg a b, sq_nonneg (T * f ω),
            mul_nonneg (mul_nonneg a a) b]
      _ = 8 * (T ^ 4 + ∫ ω, f ω ^ 4 ∂μ) := by
          rw [integral_const_mul, integral_add (integrable_const _) h4]
          simp

end BlockBand.Endpoints
