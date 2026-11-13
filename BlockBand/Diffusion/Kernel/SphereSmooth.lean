module

public import BlockBand.Diffusion.Kernel.SphereOrtho
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Joint smoothness of Legendre-type series

For a family of real polynomials `Q_n` with `deg Q_n ≤ n` and coefficients bounded by `A Kⁿ`
(`SkGrowth Q`) and `D₀ > 0`, the series
`skSer D0 Q t y = Σ_n e^{-(D₀/2)n(n+1)t} Q_n(y)`
is `C^∞` jointly in `(t, y)` on `(0, ∞) × ℝ` (`sk_ser_contDiffOn`), and it may be differentiated
termwise: its Fréchet derivative at `(t, y)` is `skSerD D0 Q (t, y)`, i.e.
`∂_t skSer D0 Q = skSer D0 (skDt D0 Q)` and `∂_y skSer D0 Q = skSer D0 (skDy Q)`
(`sk_ser_hasFDerivAt`, `sk_ser_hasDerivAt_t`, `sk_ser_hasDerivAt_y`), where
`skDt D0 Q n = -(D₀/2)n(n+1) Q_n` and `skDy Q n = Q_n'`. Both operations preserve `SkGrowth`.

The mechanism is the comparison `e^{-(D₀/2)n(n+1)δ} Lⁿ` (summable for every `L`, `δ > 0`) on the
boxes `(δ, ∞) × (-R, R)`, with Mathlib's `hasFDerivAt_tsum_of_isPreconnected`; the order of
smoothness is raised by induction, since `skDt`, `skDy` preserve the growth class.

For the Legendre families `Q_n = c_n P̃_n` (`skLegFam c`, `|c_n| ≤ A Kⁿ`) the series solves the
backward equation `∂_t u = (D₀/2)[y(1-y)∂²_y u + (1-2y)∂_y u]` at every `(t, y) ∈ (0,∞) × ℝ`
(`sk_legFam_pde`, termwise from the Legendre equation `sk_leg_ode`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open Filter Topology Set Polynomial
open scoped ContDiff

/-!
### The series and its growth class
-/

/-- The Legendre-type series `Σ_n e^{-(D₀/2)n(n+1)t} Q_n(y)`. -/
def skSer (D0 : ℝ) (Q : ℕ → ℝ[X]) (t y : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (Q n).eval y

/-- Geometric growth: `deg Q_n ≤ n` and every coefficient of `Q_n` is at most `A Kⁿ`. -/
def SkGrowth (Q : ℕ → ℝ[X]) : Prop :=
  ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧ ∀ n, (Q n).natDegree ≤ n ∧ ∀ i, |(Q n).coeff i| ≤ A * K ^ n

/-- The time derivative of the family: `Q_n ↦ -(D₀/2)n(n+1) Q_n`. -/
def skDt (D0 : ℝ) (Q : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] :=
  C (-(D0 / 2 * ((n : ℝ) * (n + 1)))) * Q n

/-- The space derivative of the family: `Q_n ↦ Q_n'`. -/
def skDy (Q : ℕ → ℝ[X]) (n : ℕ) : ℝ[X] := derivative (Q n)

/-- The candidate Fréchet derivative `∂_t · dt + ∂_y · dy` of `(t, y) ↦ skSer D0 Q t y`. -/
def skSerD (D0 : ℝ) (Q : ℕ → ℝ[X]) (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  skSer D0 (skDt D0 Q) p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
    skSer D0 (skDy Q) p.1 p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem sk_succ_le_two_pow (n : ℕ) : ((n : ℝ) + 1) ≤ 2 ^ n := by
  have h : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  exact_mod_cast h

theorem sk_rate_le (n : ℕ) : (n : ℝ) * (n + 1) ≤ 4 ^ n := by
  have h2 := sk_succ_le_two_pow n
  have h3 : (n : ℝ) ≤ 2 ^ n := by linarith
  calc (n : ℝ) * (n + 1) ≤ 2 ^ n * 2 ^ n := by gcongr
    _ = 4 ^ n := by rw [← mul_pow]; norm_num

theorem sk_growth_dt {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) (D0 : ℝ) : SkGrowth (skDt D0 Q) := by
  obtain ⟨A, K, hA, hK, h⟩ := hQ
  refine ⟨A * |D0|, 4 * K, by positivity, by positivity, fun n => ⟨?_, fun i => ?_⟩⟩
  · exact (natDegree_C_mul_le _ _).trans (h n).1
  · rw [skDt, coeff_C_mul, abs_mul]
    have h1 : |-(D0 / 2 * ((n : ℝ) * (n + 1)))| ≤ |D0| * 4 ^ n := by
      rw [abs_neg, abs_mul, abs_div, abs_two,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * (n + 1))]
      have h4 := sk_rate_le n
      have h5 : (0 : ℝ) ≤ (n : ℝ) * (n + 1) := by positivity
      nlinarith [abs_nonneg D0]
    calc |-(D0 / 2 * ((n : ℝ) * (n + 1)))| * |(Q n).coeff i|
        ≤ (|D0| * 4 ^ n) * (A * K ^ n) :=
          mul_le_mul h1 ((h n).2 i) (abs_nonneg _) (by positivity)
      _ = A * |D0| * (4 * K) ^ n := by rw [mul_pow]; ring

theorem sk_growth_dy {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) : SkGrowth (skDy Q) := by
  obtain ⟨A, K, hA, hK, h⟩ := hQ
  refine ⟨A, 2 * K, hA, by positivity, fun n => ⟨?_, fun i => ?_⟩⟩
  · exact (natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (h n).1)
  · rw [skDy, coeff_derivative]
    by_cases hi : i + 1 ≤ n
    · rw [abs_mul]
      have h1 : |((i : ℝ) + 1)| ≤ 2 ^ n := by
        rw [abs_of_nonneg (by positivity)]
        have : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi
        linarith [sk_succ_le_two_pow n]
      calc |(Q n).coeff (i + 1)| * |((i : ℝ) + 1)| ≤ A * K ^ n * 2 ^ n :=
            mul_le_mul ((h n).2 _) h1 (abs_nonneg _) (by positivity)
        _ = A * (2 * K) ^ n := by rw [mul_pow]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by have := (h n).1; omega)]
      simp only [zero_mul, abs_zero]
      positivity

/-- Evaluation bound: `|Q_n(y)| ≤ A (2KR)ⁿ` for `|y| ≤ R`, `R ≥ 1`. -/
theorem sk_growth_eval_le {Q : ℕ → ℝ[X]} {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (h : ∀ n, (Q n).natDegree ≤ n ∧ ∀ i, |(Q n).coeff i| ≤ A * K ^ n) {R y : ℝ} (hR : 1 ≤ R)
    (hy : |y| ≤ R) (n : ℕ) : |(Q n).eval y| ≤ A * (2 * K * R) ^ n := by
  have hdeg : (Q n).natDegree < n + 1 := Nat.lt_succ_of_le (h n).1
  rw [eval_eq_sum_range' hdeg]
  calc |∑ i ∈ Finset.range (n + 1), (Q n).coeff i * y ^ i|
      ≤ ∑ i ∈ Finset.range (n + 1), |(Q n).coeff i * y ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), A * K ^ n * R ^ n := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_pow]
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have : |y| ^ i ≤ R ^ n :=
          (pow_le_pow_left₀ (abs_nonneg y) hy i).trans (pow_le_pow_right₀ hR hi')
        exact mul_le_mul ((h n).2 i) this (by positivity) (by positivity)
    _ = ((n : ℝ) + 1) * (A * K ^ n * R ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ 2 ^ n * (A * K ^ n * R ^ n) := by
        have : 0 ≤ A * K ^ n * R ^ n := by
          have : (0 : ℝ) ≤ R := by linarith
          positivity
        exact mul_le_mul_of_nonneg_right (sk_succ_le_two_pow n) this
    _ = A * (2 * K * R) ^ n := by rw [mul_pow, mul_pow]; ring

/-!
### Summable majorants
-/

/-- The summable majorant `(2n+1) e^{-(D₀/2)n(n+1)t} Kⁿ` for any `K ≥ 0`. -/
theorem skp_summable_bound_gen {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) {K : ℝ} (hK : 0 ≤ K) :
    Summable fun n : ℕ => (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) *
      K ^ n := by
  have hg : Summable fun n : ℕ => (2 * (n : ℝ) + 1) * (1 / 2 : ℝ) ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
    have h0 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    convert (h1.mul_left 2).add h0 using 1
    funext n
    simp
    ring
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  have hlim : Tendsto (fun n : ℕ => K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) atTop
      (𝓝 0) := by
    have hc : 0 < D0 / 2 * t := by positivity
    have : Tendsto (fun n : ℕ => -(D0 / 2 * ((n : ℝ) + 1) * t)) atTop atBot := by
      have h := Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
      have h' := h.const_mul_atTop hc
      refine (tendsto_neg_atTop_atBot.comp h').congr fun n => ?_
      simp only [Function.comp]
      ring
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  have hexp : Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * K ^ n =
      (K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t))) ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_comm]
    congr 2
    ring
  have hb : 0 ≤ (2 * (n : ℝ) + 1) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * K ^ n := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hb, mul_assoc, hexp]
  have h0 : 0 ≤ K * Real.exp (-(D0 / 2 * ((n : ℝ) + 1) * t)) := by positivity
  gcongr

theorem sk_summable_exp_geom {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) {L : ℝ} (hL : 0 ≤ L) :
    Summable fun n : ℕ => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * L ^ n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (skp_summable_bound_gen hD0 ht hL)
  have h1 : (1 : ℝ) ≤ 2 * n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h2 : 0 ≤ Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * L ^ n := by positivity
  calc Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * L ^ n
      = 1 * (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * L ^ n) := (one_mul _).symm
    _ ≤ (2 * n + 1) * (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * L ^ n) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := by ring

theorem sk_exp_le {D0 δ t : ℝ} (hD0 : 0 ≤ D0) (ht : δ ≤ t) (n : ℕ) :
    Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) ≤
      Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * δ)) := by
  apply Real.exp_le_exp.2
  have : 0 ≤ D0 / 2 * ((n : ℝ) * (n + 1)) := by positivity
  nlinarith

/-- Termwise majorant on `[δ, ∞) × [-R, R]`. -/
theorem sk_term_bound {D0 δ R : ℝ} (hD0 : 0 ≤ D0) (hR : 1 ≤ R) {Q : ℕ → ℝ[X]} {A K : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (h : ∀ n, (Q n).natDegree ≤ n ∧ ∀ i, |(Q n).coeff i| ≤ A * K ^ n)
    {t y : ℝ} (ht : δ ≤ t) (hy : |y| ≤ R) (n : ℕ) :
    ‖Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (Q n).eval y‖ ≤
      A * (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * δ)) * (2 * K * R) ^ n) := by
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  calc Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * |(Q n).eval y|
      ≤ Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * δ)) * (A * (2 * K * R) ^ n) :=
        mul_le_mul (sk_exp_le hD0 ht n) (sk_growth_eval_le hA hK h hR hy n) (abs_nonneg _)
          (Real.exp_pos _).le
    _ = _ := by ring

theorem sk_ser_summable {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    Summable fun n : ℕ => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * (Q n).eval y := by
  obtain ⟨A, K, hA, hK, h⟩ := hQ
  have hR : (1 : ℝ) ≤ |y| + 1 := by linarith [abs_nonneg y]
  exact Summable.of_norm_bounded
    ((sk_summable_exp_geom hD0 ht (L := 2 * K * (|y| + 1)) (by positivity)).mul_left A)
    (sk_term_bound hD0.le hR hA hK h le_rfl (by linarith) )

/-!
### Termwise differentiation
-/

theorem sk_term_hasFDerivAt (lam : ℝ) (q : ℝ[X]) (p : ℝ × ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => Real.exp (-(lam * p.1)) * q.eval p.2)
      ((Real.exp (-(lam * p.1)) * (C (-lam) * q).eval p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (Real.exp (-(lam * p.1)) * (derivative q).eval p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      p := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => -(lam * p.1))
      (-(lam • ContinuousLinearMap.fst ℝ ℝ ℝ)) p := (hasFDerivAt_fst.const_mul lam).neg
  have h3 : HasFDerivAt (fun p : ℝ × ℝ => q.eval p.2)
      ((derivative q).eval p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (q.hasDerivAt p.2).comp_hasFDerivAt p hasFDerivAt_snd
  refine (h1.exp.mul h3).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, eval_mul, eval_C]
  ring

theorem sk_norm_fst_snd_le (a b : ℝ) :
    ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |a| + |b| := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
  nlinarith [abs_nonneg a, abs_nonneg b]

/-- **Termwise Fréchet differentiation** on the box `(δ, ∞) × (-R, R)`. -/
theorem sk_ser_hasFDerivAt_box {D0 δ R : ℝ} (hD0 : 0 < D0) (hδ : 0 < δ) (hR : 1 ≤ R)
    {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {p : ℝ × ℝ} (hp : p ∈ Ioi δ ×ˢ Ioo (-R) R) :
    HasFDerivAt (fun p : ℝ × ℝ => skSer D0 Q p.1 p.2) (skSerD D0 Q p) p := by
  obtain ⟨A1, K1, hA1, hK1, h1⟩ := sk_growth_dt hQ D0
  obtain ⟨A2, K2, hA2, hK2, h2⟩ := sk_growth_dy hQ
  set V : Set (ℝ × ℝ) := Ioi δ ×ˢ Ioo (-R) R with hVdef
  have hVo : IsOpen V := isOpen_Ioi.prod isOpen_Ioo
  have hVc : IsPreconnected V := ((convex_Ioi δ).prod (convex_Ioo (-R) R)).isPreconnected
  have hmem : ∀ x ∈ V, δ ≤ x.1 ∧ |x.2| ≤ R := fun x hx =>
    ⟨(mem_Ioi.1 hx.1).le, abs_le.2 ⟨hx.2.1.le, hx.2.2.le⟩⟩
  set e : ℕ → ℝ := fun n => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * δ)) with hedef
  have hu : Summable fun n => A1 * (e n * (2 * K1 * R) ^ n) + A2 * (e n * (2 * K2 * R) ^ n) := by
    have hR0 : (0 : ℝ) ≤ R := by linarith
    exact ((sk_summable_exp_geom hD0 hδ (L := 2 * K1 * R) (by positivity)).mul_left A1).add
      ((sk_summable_exp_geom hD0 hδ (L := 2 * K2 * R) (by positivity)).mul_left A2)
  have hf : ∀ (n : ℕ) x, x ∈ V → HasFDerivAt
      (fun p : ℝ × ℝ => Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * p.1)) * (Q n).eval p.2)
      ((Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * x.1)) * (skDt D0 Q n).eval x.2) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * x.1)) * (skDy Q n).eval x.2) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    fun n x _ => sk_term_hasFDerivAt (D0 / 2 * ((n : ℝ) * (n + 1))) (Q n) x
  have hf' : ∀ (n : ℕ) x, x ∈ V →
      ‖(Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * x.1)) * (skDt D0 Q n).eval x.2) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * x.1)) * (skDy Q n).eval x.2) •
          ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤
        A1 * (e n * (2 * K1 * R) ^ n) + A2 * (e n * (2 * K2 * R) ^ n) := by
    intro n x hx
    refine (sk_norm_fst_snd_le _ _).trans (add_le_add ?_ ?_)
    · have := sk_term_bound hD0.le hR hA1 hK1 h1 (hmem x hx).1 (hmem x hx).2 n
      rwa [Real.norm_eq_abs] at this
    · have := sk_term_bound hD0.le hR hA2 hK2 h2 (hmem x hx).1 (hmem x hx).2 n
      rwa [Real.norm_eq_abs] at this
  have hs0 := sk_ser_summable hD0 hQ (lt_trans hδ hp.1) p.2
  have key := hasFDerivAt_tsum_of_isPreconnected hu hVo hVc hf hf' hp hs0 hp
  refine key.congr_fderiv ?_
  have sa := (sk_ser_summable hD0 (sk_growth_dt hQ D0) (lt_trans hδ hp.1) p.2).smul_const
    (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have sb := (sk_ser_summable hD0 (sk_growth_dy hQ) (lt_trans hδ hp.1) p.2).smul_const
    (ContinuousLinearMap.snd ℝ ℝ ℝ)
  rw [sa.tsum_add sb, Summable.tsum_smul_const, Summable.tsum_smul_const]
  · rfl
  · exact sk_ser_summable hD0 (sk_growth_dy hQ) (lt_trans hδ hp.1) p.2
  · exact sk_ser_summable hD0 (sk_growth_dt hQ D0) (lt_trans hδ hp.1) p.2

/-- **Joint smoothness on boxes**, by induction on the order. -/
theorem sk_ser_contDiffOn_box {D0 δ R : ℝ} (hD0 : 0 < D0) (hδ : 0 < δ) (hR : 1 ≤ R) (k : ℕ) :
    ∀ Q : ℕ → ℝ[X], SkGrowth Q →
      ContDiffOn ℝ k (fun p : ℝ × ℝ => skSer D0 Q p.1 p.2) (Ioi δ ×ˢ Ioo (-R) R) := by
  have hVo : IsOpen (Ioi δ ×ˢ Ioo (-R) R) := isOpen_Ioi.prod isOpen_Ioo
  induction k with
  | zero =>
    intro Q hQ
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun p hp => (sk_ser_hasFDerivAt_box hD0 hδ hR hQ hp).continuousAt.continuousWithinAt
  | succ k ih =>
    intro Q hQ
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hVo]
    refine ⟨fun p hp =>
      (sk_ser_hasFDerivAt_box hD0 hδ hR hQ hp).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hD : ContDiffOn ℝ k (skSerD D0 Q) (Ioi δ ×ˢ Ioo (-R) R) :=
      ((ih _ (sk_growth_dt hQ D0)).smul contDiffOn_const).add
        ((ih _ (sk_growth_dy hQ)).smul contDiffOn_const)
    exact hD.congr fun p hp => (sk_ser_hasFDerivAt_box hD0 hδ hR hQ hp).fderiv

theorem sk_mem_box {t y : ℝ} (ht : 0 < t) :
    (t, y) ∈ Ioi (t / 2) ×ˢ Ioo (-(|y| + 1)) (|y| + 1) :=
  Set.mk_mem_prod (by show t / 2 < t; linarith)
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩

/-- **Joint `C^∞` regularity** of the series on `(0, ∞) × ℝ`. -/
theorem sk_ser_contDiffOn {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => skSer D0 Q p.1 p.2) (Ioi 0 ×ˢ univ) := by
  refine contDiffOn_infty.2 fun k => contDiffOn_of_locally_contDiffOn fun p hp => ?_
  have ht : 0 < p.1 := hp.1
  refine ⟨Ioi (p.1 / 2) ×ˢ Ioo (-(|p.2| + 1)) (|p.2| + 1), isOpen_Ioi.prod isOpen_Ioo,
    sk_mem_box ht, ?_⟩
  exact (sk_ser_contDiffOn_box hD0 (by positivity) (by linarith [abs_nonneg p.2]) k Q hQ).mono
    inter_subset_right

/-- **Termwise Fréchet derivative** at every `(t, y)` with `t > 0`. -/
theorem sk_ser_hasFDerivAt {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => skSer D0 Q p.1 p.2) (skSerD D0 Q (t, y)) (t, y) :=
  sk_ser_hasFDerivAt_box hD0 (half_pos ht) (by linarith [abs_nonneg y]) hQ (sk_mem_box ht)

/-- `∂_t skSer D0 Q = skSer D0 (skDt D0 Q)` for `t > 0`. -/
theorem sk_ser_hasDerivAt_t {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => skSer D0 Q s y) (skSer D0 (skDt D0 Q) t y) t := by
  have h := (sk_ser_hasFDerivAt hD0 hQ ht y).comp_hasDerivAt t
    ((hasDerivAt_id' t).prodMk (hasDerivAt_const t y))
  convert h using 1
  · rfl
  · simp [skSerD]

/-- `∂_y skSer D0 Q = skSer D0 (skDy Q)` for `t > 0`. -/
theorem sk_ser_hasDerivAt_y {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z => skSer D0 Q t z) (skSer D0 (skDy Q) t y) y := by
  have h := (sk_ser_hasFDerivAt hD0 hQ ht y).comp_hasDerivAt y
    ((hasDerivAt_const y t).prodMk (hasDerivAt_id' y))
  convert h using 1
  · rfl
  · simp [skSerD]

theorem sk_ser_deriv_y {D0 : ℝ} (hD0 : 0 < D0) {Q : ℕ → ℝ[X]} (hQ : SkGrowth Q) {t : ℝ}
    (ht : 0 < t) : deriv (fun z => skSer D0 Q t z) = fun z => skSer D0 (skDy Q) t z :=
  funext fun y => (sk_ser_hasDerivAt_y hD0 hQ ht y).deriv

/-!
### Legendre families and the backward equation
-/

/-- The Legendre family `Q_n = c_n P̃_n`. -/
def skLegFam (c : ℕ → ℝ) (n : ℕ) : ℝ[X] := C (c n) * skLeg n

theorem sk_leg_coeff_abs_le (n i : ℕ) : |(skLeg n).coeff i| ≤ 8 ^ n := by
  rw [sk_leg_coeff, skLegCoeff, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast, Nat.abs_cast]
  by_cases hi : i ≤ n
  · have h1 : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    have hc : ((n + i).choose n : ℝ) ≤ 4 ^ n := by
      have h1 := Nat.choose_le_two_pow (n + i) n
      have h2 : 2 ^ (n + i) ≤ 4 ^ n := by
        rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast h1.trans h2
    calc (n.choose i : ℝ) * ((n + i).choose n : ℝ) ≤ 2 ^ n * 4 ^ n :=
          mul_le_mul h1 hc (by positivity) (by positivity)
      _ = 8 ^ n := by rw [← mul_pow]; norm_num
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem sk_growth_legFam {c : ℕ → ℝ} {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : ∀ n, |c n| ≤ A * K ^ n) : SkGrowth (skLegFam c) := by
  refine ⟨A, 8 * K, hA, by positivity, fun n => ⟨?_, fun i => ?_⟩⟩
  · exact (natDegree_C_mul_le _ _).trans (skp_leg_natDegree_le n)
  · rw [skLegFam, coeff_C_mul, abs_mul]
    calc |c n| * |(skLeg n).coeff i| ≤ A * K ^ n * 8 ^ n :=
          mul_le_mul (hc n) (sk_leg_coeff_abs_le n i) (abs_nonneg _) (by positivity)
      _ = A * (8 * K) ^ n := by rw [mul_pow]; ring

/-- `|P̃_n(y)| ≤ (16R)ⁿ` for `|y| ≤ R`, `R ≥ 1`. -/
theorem sk_leg_eval_le {R y : ℝ} (hR : 1 ≤ R) (hy : |y| ≤ R) (n : ℕ) :
    |(skLeg n).eval y| ≤ (16 * R) ^ n := by
  have h := sk_growth_eval_le (Q := skLeg) zero_le_one (by norm_num : (0 : ℝ) ≤ 8)
    (fun n => ⟨skp_leg_natDegree_le n, fun i => by rw [one_mul]; exact sk_leg_coeff_abs_le n i⟩)
    hR hy n
  rw [one_mul] at h
  calc |(skLeg n).eval y| ≤ (2 * 8 * R) ^ n := h
    _ = (16 * R) ^ n := by norm_num

/-- **Backward equation for Legendre families**: for `Q_n = c_n P̃_n` with `|c_n| ≤ A Kⁿ`,
`∂_t u = (D₀/2)[y(1-y)∂²_y u + (1-2y)∂_y u]` holds for the series coefficientwise, at every
`t > 0`, `y ∈ ℝ`. -/
theorem sk_legFam_pde {D0 : ℝ} (hD0 : 0 < D0) {c : ℕ → ℝ} {A K : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : ∀ n, |c n| ≤ A * K ^ n) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    skSer D0 (skDt D0 (skLegFam c)) t y =
      D0 / 2 * (y * (1 - y) * skSer D0 (skDy (skDy (skLegFam c))) t y +
        (1 - 2 * y) * skSer D0 (skDy (skLegFam c)) t y) := by
  have hG := sk_growth_legFam hA hK hc
  have s2 := sk_ser_summable hD0 (sk_growth_dy (sk_growth_dy hG)) ht y
  have s1 := sk_ser_summable hD0 (sk_growth_dy hG) ht y
  unfold skSer
  rw [← tsum_mul_left, ← tsum_mul_left, ← (s2.mul_left _).tsum_add (s1.mul_left _),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [skDt, skDy, skLegFam, derivative_C_mul, eval_mul, eval_C]
  have hode := congrArg (Polynomial.eval y) (sk_leg_ode n)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_X_pow, eval_add, eval_mul,
    eval_sub, eval_X, eval_pow, eval_one, eval_neg, eval_C] at hode
  push_cast at hode
  linear_combination (-(D0 / 2) * Real.exp (-(D0 / 2 * ((n : ℝ) * (n + 1)) * t)) * c n) * hode

end BlockBand.Diffusion
