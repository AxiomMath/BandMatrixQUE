module

public import BlockBand.SourceProcess.ContractingWords.CutRep
public import BlockBand.SourceProcess.ContractingWords.ScalarLp
public import BlockBand.SourceProcess.FullSource.MomentStep
public import BlockBand.Transmission.PassiveCovariance.ResolventBound
public import BlockBand.Transmission.PassiveCovariance.MainTerm

/-!
# One layer: a cut representation at random separators (one fresh layer)

Let `F` have a cut representation (`HasCutRep F d Γ`) and let `T_s` be random matrices (one fresh
layer) with integrable entries, means `M_s = E T_s`, `‖M_s‖ ≤ μ`, and the centered bilinear bound
`‖u*(T_s - M_s)v‖_{(d+2)r} ≤ β‖u‖‖v‖`. With `B = dβ`, `K = 2^d(1+μ)^d`:
* `cutRep_layer`: `F(T)` is integrable, `|E F(T) - F(M)| ≤ ΓKB²(1+B^d)` and
  `‖F(T) - F(M)‖_r ≤ ΓKB(1+B^d)` (Step 1's split into means and centered factors, Step 2's
  bound: `m = 0` terms give `F(M)`, `m = 1` terms have mean zero, `m ≥ 2` terms are `O(β²)`);
* `cutRep_compare`: `|F(M) - F(B')| ≤ Γ d e(1+μ₀+e)^d` when `‖M_s - B'_s‖ ≤ e`, `‖B'_s‖ ≤ μ₀`
  (the errors of the means).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Finset Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance BlockBand.SourceProcess.FullSource
open scoped ENNReal Matrix.Norms.L2Operator

variable {n S : Type} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [DecidableEq n] [IsProbabilityMeasure ν] in
theorem integrable_bilinear_of {U : Ω → Matrix n n ℂ} (hU : ∀ i j, Integrable (fun ω => U ω i j) ν)
    (u v : n → ℂ) : Integrable (fun ω => bilinear u (U ω) v) ν := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply]
  exact integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ => (hU i j).mul_const _).const_mul _

/-- **One layer at a cut representation.** -/
theorem cutRep_layer {F : (S → Matrix n n ℂ) → ℂ} {d : ℕ} {Γ : ℝ} (hF : HasCutRep F d Γ)
    (T : S → Ω → Matrix n n ℂ) (hT : ∀ s i j, Integrable (fun ω => T s ω i j) ν)
    {μ r β : ℝ} (hμ : 0 ≤ μ) (hr : 1 ≤ r) (hβ : 0 ≤ β)
    (hM : ∀ s, ‖matrixExpect ν (T s)‖ ≤ μ)
    (hB : ∀ s u v, eLpNorm (fun ω => bilinear u (T s ω - matrixExpect ν (T s)) v)
      (ENNReal.ofReal ((d + 2) * r)) ν ≤ ENNReal.ofReal (β * vecNorm u * vecNorm v)) :
    Integrable (fun ω => F fun s => T s ω) ν ∧
      ‖∫ ω, F (fun s => T s ω) ∂ν - F (fun s => matrixExpect ν (T s))‖ ≤
        Γ * (2 ^ d * (1 + μ) ^ d * (d * β) ^ 2 * (1 + (d * β) ^ d)) ∧
      eLpNorm (fun ω => F (fun s => T s ω) - F (fun s => matrixExpect ν (T s)))
        (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal (Γ * (2 ^ d * (1 + μ) ^ d * (d * β) * (1 + (d * β) ^ d))) := by
  classical
  obtain ⟨P, hP, σ, ι, hι, c, x, y, hcard, hc, hxy, hrep⟩ := hF
  set M : S → Matrix n n ℂ := fun s => matrixExpect ν (T s)
  set m : ι → P → ℂ := fun l p => bilinear (x l p) (M (σ p)) (y l p)
  set D : ι → P → Ω → ℂ := fun l p ω => bilinear (x l p) (T (σ p) ω - M (σ p)) (y l p)
  have hsplit : ∀ ω, F (fun s => T s ω) = ∑ l, c l * ∏ p, (m l p + D l p ω) := fun ω => by
    rw [hrep]
    refine sum_congr rfl fun l _ => ?_
    congr 1
    refine prod_congr rfl fun p _ => ?_
    simp only [m, D, bilinear_sub]; ring
  have hFM : F M = ∑ l, c l * ∏ p, m l p := hrep M
  have hmb : ∀ l p, ‖m l p‖ ≤ μ := fun l p => by
    refine (norm_bilinear_le _ _ _).trans ?_
    have h1 := (hxy l p).1; have h2 := (hxy l p).2
    have := hM (σ p)
    calc vecNorm (x l p) * ‖M (σ p)‖ * vecNorm (y l p) ≤ 1 * μ * 1 := by
          gcongr; exact vecNorm_nonneg _
      _ = μ := by ring
  have hDi : ∀ l p, Integrable (D l p) ν := fun l p => by
    simp only [D, bilinear_sub]
    exact (integrable_bilinear_of (hT (σ p)) _ _).sub (integrable_const _)
  have hD0 : ∀ l p, ∫ ω, D l p ω ∂ν = 0 := fun l p => by
    simp only [D, bilinear_sub]
    rw [integral_sub (integrable_bilinear_of (hT (σ p)) _ _) (integrable_const _),
      integral_bilinear _ (hT (σ p)), integral_const, probReal_univ, one_smul, sub_self]
  have hDb : ∀ l p, eLpNorm (D l p) (ENNReal.ofReal ((d + 2) * r)) ν ≤ ENNReal.ofReal β :=
    fun l p => (hB (σ p) (x l p) (y l p)).trans (ENNReal.ofReal_le_ofReal (by
      have h1 := (hxy l p).1; have h2 := (hxy l p).2
      have := vecNorm_nonneg (x l p); have := vecNorm_nonneg (y l p)
      calc β * vecNorm (x l p) * vecNorm (y l p) ≤ β * 1 * 1 := by gcongr
        _ = β := by ring))
  have hS := fun l => scalar_expansion hcard (m l) hμ (hmb l) (D l) (fun p => (hDi l p).1)
    (hD0 l) hr hβ (hDb l)
  set bm : ℝ := 2 ^ d * (1 + μ) ^ d * (d * β) ^ 2 * (1 + (d * β) ^ d)
  set bf : ℝ := 2 ^ d * (1 + μ) ^ d * (d * β) * (1 + (d * β) ^ d)
  have hbm : 0 ≤ bm := by positivity
  have hbf : 0 ≤ bf := by positivity
  have hc0 : ∀ l, 0 ≤ ‖c l‖ := fun l => norm_nonneg _
  have hInt : Integrable (fun ω => F fun s => T s ω) ν := by
    simp_rw [hsplit]
    exact integrable_finsetSum _ fun l _ => (hS l).1.const_mul _
  refine ⟨hInt, ?_, ?_⟩
  · simp_rw [hsplit]
    rw [integral_finsetSum _ fun l _ => (hS l).1.const_mul _, hFM, ← sum_sub_distrib]
    calc ‖∑ l, (∫ ω, c l * ∏ p, (m l p + D l p ω) ∂ν - c l * ∏ p, m l p)‖ ≤
          ∑ l, ‖c l‖ * bm := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)
          rw [integral_const_mul, ← mul_sub, norm_mul]
          exact mul_le_mul_of_nonneg_left (hS l).2.1 (hc0 l)
      _ = (∑ l, ‖c l‖) * bm := by rw [sum_mul]
      _ ≤ Γ * bm := mul_le_mul_of_nonneg_right hc hbm
  · have e : (fun ω => F (fun s => T s ω) - F M) =
        ∑ l, fun ω => c l * (∏ p, (m l p + D l p ω) - ∏ p, m l p) := by
      funext ω; rw [hsplit, hFM, Finset.sum_apply, ← sum_sub_distrib]
      refine sum_congr rfl fun l _ => by ring
    change eLpNorm (fun ω => F (fun s => T s ω) - F M) _ ν ≤ _
    rw [e]
    refine (eLpNorm_sum_le (by simpa using hr)).trans ?_
    calc ∑ l, eLpNorm (fun ω => c l * (∏ p, (m l p + D l p ω) - ∏ p, m l p))
          (ENNReal.ofReal r) ν ≤ ∑ l, ENNReal.ofReal (‖c l‖ * bf) := by
          refine sum_le_sum fun l _ => ?_
          have e' : (fun ω => c l * (∏ p, (m l p + D l p ω) - ∏ p, m l p)) =
              c l • fun ω => ∏ p, (m l p + D l p ω) - ∏ p, m l p := by
            funext ω; simp [smul_eq_mul]
          rw [e', eLpNorm_const_smul, ENNReal.ofReal_mul (hc0 l), ofReal_norm]
          gcongr; exact (hS l).2.2
      _ = ENNReal.ofReal ((∑ l, ‖c l‖) * bf) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => by positivity, sum_mul]
      _ ≤ ENNReal.ofReal (Γ * bf) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc hbf)

/-- **Errors of the means**: `|F(M) - F(B')| ≤ Γde(1+μ₀+e)^d`. -/
theorem cutRep_compare {F : (S → Matrix n n ℂ) → ℂ} {d : ℕ} {Γ : ℝ} (hF : HasCutRep F d Γ)
    (M B' : S → Matrix n n ℂ) {μ₀ e : ℝ} (hμ₀ : 0 ≤ μ₀) (he : 0 ≤ e)
    (hB' : ∀ s, ‖B' s‖ ≤ μ₀) (hMB : ∀ s, ‖M s - B' s‖ ≤ e) :
    ‖F M - F B'‖ ≤ Γ * (d * e * (1 + μ₀ + e) ^ d) := by
  classical
  obtain ⟨P, hP, σ, ι, hι, c, x, y, hcard, hc, hxy, hrep⟩ := hF
  set mm : ι → P → ℂ := fun l p => bilinear (x l p) (B' (σ p)) (y l p)
  set DD : ι → P → ℂ := fun l p => bilinear (x l p) (M (σ p) - B' (σ p)) (y l p)
  have hunit : ∀ l p (A : Matrix n n ℂ) (a : ℝ), ‖A‖ ≤ a → ‖bilinear (x l p) A (y l p)‖ ≤ a :=
    fun l p A a hA => by
      refine (norm_bilinear_le _ _ _).trans ?_
      have h1 := (hxy l p).1; have h2 := (hxy l p).2
      have h0 : 0 ≤ ‖A‖ := norm_nonneg _
      calc vecNorm (x l p) * ‖A‖ * vecNorm (y l p) ≤ 1 * ‖A‖ * 1 := by
            gcongr; exact vecNorm_nonneg _
        _ ≤ a := by linarith
  have hb : ∀ l, ‖∏ p, (mm l p + DD l p) - ∏ p, mm l p‖ ≤ d * e * (1 + μ₀ + e) ^ d := fun l => by
    refine ((expand_bounds (mm l) (DD l) univ).1).trans ?_
    have hS : ∑ p, ‖DD l p‖ ≤ d * e := by
      calc ∑ p, ‖DD l p‖ ≤ ∑ _p : P, e := sum_le_sum fun p _ => hunit l p _ _ (hMB (σ p))
        _ = Fintype.card P * e := by simp
        _ ≤ d * e := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) he
    have hR : ∏ p, (1 + ‖mm l p‖ + ‖DD l p‖) ≤ (1 + μ₀ + e) ^ d := by
      calc ∏ p, (1 + ‖mm l p‖ + ‖DD l p‖) ≤ ∏ _p : P, (1 + μ₀ + e) := by
            refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun p _ => ?_
            linarith [hunit l p _ _ (hB' (σ p)), hunit l p _ _ (hMB (σ p))]
        _ = (1 + μ₀ + e) ^ Fintype.card P := by rw [prod_const, card_univ]
        _ ≤ (1 + μ₀ + e) ^ d := pow_le_pow_right₀ (by linarith) hcard
    exact mul_le_mul hS hR (prod_nonneg fun _ _ => by positivity) (by positivity)
  rw [hrep M, hrep B', ← sum_sub_distrib]
  have e1 : ∀ l, c l * ∏ p, bilinear (x l p) (M (σ p)) (y l p) -
      c l * ∏ p, bilinear (x l p) (B' (σ p)) (y l p) =
      c l * (∏ p, (mm l p + DD l p) - ∏ p, mm l p) := fun l => by
    simp only [mm, DD, bilinear_sub]; ring_nf
  simp_rw [e1]
  calc ‖∑ l, c l * (∏ p, (mm l p + DD l p) - ∏ p, mm l p)‖ ≤
        ∑ l, ‖c l‖ * (d * e * (1 + μ₀ + e) ^ d) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun l _ => ?_)
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb l) (norm_nonneg _)
    _ = (∑ l, ‖c l‖) * (d * e * (1 + μ₀ + e) ^ d) := by rw [sum_mul]
    _ ≤ Γ * (d * e * (1 + μ₀ + e) ^ d) := mul_le_mul_of_nonneg_right hc (by positivity)

end BlockBand.SourceProcess.ContractingWords
