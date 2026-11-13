module

public import BlockBand.Endpoints.Clock.OpenClockRiemann

/-!
# The discrete determinant-Laplace equation converges to the Feynman–Kac functional

## Abstract form

The theorem is stated for an **arbitrary** double sequence of probability laws `μ W j` on
`[0,∞)` (in the application `μ W j` is the law of `g*Q_j^q g`, whose Laplace transform at `a`
is `E F_a(Q_j^q)` by the Gaussian identity), so that the analytic core is
independent of the random-matrix chain:

* `clockRemainder Dseq c q μ W j b` is the remainder `r_{W,j}(b)` of the deterministic clock step,
  with `∂_b² f = ∫ x² e^{-bx} dμ` (`lap2`), `d = c`, and a width-dependent diffusion coefficient
  `D_W = Dseq W` (moving energies `E_W → E`, `D_W = D₀(b, E_W)`);
* `ClockEquation Dseq c q T μ j₀`: for every `K ≥ 1` there are `δ_{W,j}` with
  `|r_{W,j}(b)| ≤ δ_{W,j}` for `j₀ ≤ j ≤ TW`, `b ∈ [K⁻¹, K]`, and
  `Σ_{j=j₀}^{⌊TW⌋} δ_{W,j} → 0` (that is, `Σ_j sup_a |r_{W,j}(a)| → 0` on compacts).

Main theorem `tendsto_lap_of_clockEquation`: if moreover `D_W → D ≥ 0`, `j₀/W → 0`,
`lap (μ W (j₀ W)) b → 1` for each `b > 0`, `q` is continuous with `0 ≤ q ≤ Q̄`, and
`n_W/W → t ∈ (0, T]` with `n_W ≤ TW`, then for every `a > 0`
`lap (μ W (n W)) a → openClockLaplace D c q t a = E exp{-a c ∫₀^t q(t-s) e^{√D B_s - Ds/2} ds}`.

## Proof

Instead of equicontinuity, a weak PDE limit and uniqueness of bounded solutions via a stopped
Feynman–Kac formula, the comparison is **direct and quantitative at each width**: the discrete
dual (geometric Brownian
motion sampled on the grid `1/W`, killed at the first exit from `[K⁻¹, K]`, with Riemann-sum
killing) is tested against the discrete equation; one step costs `O(W^{-3/2})` uniformly
(`step_consistency`) plus `W⁻¹|D_W - D|` plus the remainder `δ_{W,j}`;
the exit costs `1 - E A_N`, small uniformly in `W` (`exists_dualAlive_ge`); the killing Riemann
sums converge pathwise (`tendsto_integral_dualKill`). No PDE, regularity theory, Itô formula or
uniqueness theorem is used, and no property of the limit beyond its definition.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock
namespace OpenClock

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BlockBand.SourceProcess
open scoped NNReal ENNReal

/-- The remainder `r_{W,j}(b)` of the deterministic clock step for the laws
`μ W j` on `[0,∞)` with Laplace transforms `lap (μ W j)`, diffusion coefficient `Dseq W`,
killing constant `c = d` and clock weight `q`:
`r = f_{j+1}(b) - f_j(b) - W⁻¹[(D_W/2) b² ∂_b² f_j(b) - c q((j+1)/W) b f_j(b)]`, with
`∂_b² f_j(b) = lap2 (μ W j) b = ∫ x² e^{-bx} dμ`. -/
def clockRemainder (Dseq : ℕ → ℝ) (c : ℝ) (q : ℝ → ℝ) (μ : ℕ → ℕ → Measure ℝ) (W j : ℕ)
    (b : ℝ) : ℝ :=
  lap (μ W (j + 1)) b - lap (μ W j) b - (W : ℝ)⁻¹ * (Dseq W / 2 * b ^ 2 * lap2 (μ W j) b -
    c * q (((j + 1 : ℕ) : ℝ) / W) * b * lap (μ W j) b)

/-- The discrete equation the deterministic clock step with summable remainder, uniformly on compact
subsets of `(0,∞)` (every compact subset lies in some `[K⁻¹, K]`), for `j₀ ≤ j ≤ TW`. -/
def ClockEquation (Dseq : ℕ → ℝ) (c : ℝ) (q : ℝ → ℝ) (T : ℝ) (μ : ℕ → ℕ → Measure ℝ)
    (j₀ : ℕ → ℕ) : Prop :=
  ∀ K : ℝ, 1 ≤ K → ∃ δ : ℕ → ℕ → ℝ,
    (∀ W j, j₀ W ≤ j → (j : ℝ) ≤ T * W → ∀ b ∈ Icc K⁻¹ K,
      |clockRemainder Dseq c q μ W j b| ≤ δ W j) ∧
    Tendsto (fun W => ∑ j ∈ Finset.Icc (j₀ W) ⌊T * W⌋₊, δ W j) atTop (𝓝 0)

/-- **One-step consistency.** For `0 ≤ b ≤ K`, `0 ≤ q_* ≤ Q̄`, `0 < h ≤ 1`, `10 D h ≤ 1`,
`c Q̄ K h ≤ 1`: the dual step `e^{-c h q_* b} E lap μ₀ (b M_h)` reproduces
`lap μ₁ b` up to `C₁ h^{3/2} + h |D_W - D| + |r|`, where `r` is the discrete-equation
remainder with coefficient `D_W`. -/
theorem step_consistency {D c : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) (Dw : ℝ) {qs Qb K : ℝ}
    (hqs0 : 0 ≤ qs) (hqsQ : qs ≤ Qb) (s hh : ℝ≥0) (hh0 : 0 < hh) (hh1 : (hh : ℝ) ≤ 1)
    (hDh : 10 * D * hh ≤ 1) (hz : c * Qb * K * hh ≤ 1) (μ₀ μ₁ : Measure ℝ)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] (hμ₀ : ∀ᵐ x ∂μ₀, 0 ≤ x) {b : ℝ}
    (hb0 : 0 ≤ b) (hbK : b ≤ K) :
    |lap μ₁ b - exp (-(c * hh * qs * b)) * ∫ ω, lap μ₀ (b * lognormal D s hh ω) ∂canonicalWienerLaw|
      ≤ ((c * Qb * K) ^ 2 + D * (c * Qb * K) + 24 * (4 * D + 88 * D ^ 2) + D ^ 2) *
          Real.sqrt hh ^ 3 + hh * |Dw - D| +
        |lap μ₁ b - lap μ₀ b - hh * (Dw / 2 * b ^ 2 * lap2 μ₀ b - c * qs * b * lap μ₀ b)| := by
  set I := ∫ ω, lap μ₀ (b * lognormal D s hh ω) ∂canonicalWienerLaw
  set F₀ := lap μ₀ b
  set m := b ^ 2 * lap2 μ₀ b
  set z := c * hh * qs * b with hzdef
  set r := lap μ₁ b - lap μ₀ b - hh * (Dw / 2 * b ^ 2 * lap2 μ₀ b - c * qs * b * lap μ₀ b)
  set E₁ := I - F₀ - hh * (D / 2) * m with hE₁
  have hE₁b : |E₁| ≤ 24 * (4 * D + 88 * D ^ 2) * Real.sqrt hh ^ 3 + D ^ 2 * hh ^ 2 := by
    have := abs_integral_lap_lognormal_step hD s hh hh0 hDh μ₀ hμ₀ hb0
    simpa [hE₁, m, mul_assoc] using this
  have hF₀ : |F₀| ≤ 1 := abs_lap_le_one μ₀ hμ₀ hb0
  have hm := sq_mul_lap2_le μ₀ hμ₀ hb0
  have hhr : (0 : ℝ) < hh := hh0
  have hQb0 : 0 ≤ Qb := hqs0.trans hqsQ
  have hz0 : 0 ≤ z := by positivity
  have hzZ : z ≤ c * Qb * K * hh := by
    rw [hzdef]
    have h1 : qs * b ≤ Qb * K := mul_le_mul hqsQ hbK hb0 hQb0
    calc c * hh * qs * b = c * hh * (qs * b) := by ring
      _ ≤ c * hh * (Qb * K) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = c * Qb * K * hh := by ring
  have hz1 : z ≤ 1 := hzZ.trans hz
  have hexp1 : |exp (-z) - 1 - (-z)| ≤ z ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -z) (by rw [abs_neg, abs_of_nonneg hz0]; exact hz1)
    simpa using this
  have hexp2 : 0 ≤ 1 - exp (-z) ∧ 1 - exp (-z) ≤ z := by
    constructor
    · have : exp (-z) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      linarith
    · have := add_one_le_exp (-z); linarith
  have hexp3 : 0 < exp (-z) ∧ exp (-z) ≤ 1 := ⟨exp_pos _, exp_le_one_iff.mpr (by linarith)⟩
  have hdecomp : lap μ₁ b - exp (-z) * I =
      r + (1 - z - exp (-z)) * F₀ + hh * ((Dw - D) / 2) * m + hh * (D / 2) * m * (1 - exp (-z))
        - exp (-z) * E₁ := by
    simp only [r, E₁, F₀, m, hzdef]; ring
  have hzexp : (fun x : ℝ => exp (-(c * hh * qs * x))) b = exp (-z) := rfl
  rw [show exp (-(c * hh * qs * b)) = exp (-z) from rfl, hdecomp]
  -- term bounds
  set Z := c * Qb * K
  have hK0 : 0 ≤ K := hb0.trans hbK
  have hZ0 : 0 ≤ Z := mul_nonneg (mul_nonneg hc hQb0) hK0
  have hsh : Real.sqrt hh ^ 2 = hh := Real.sq_sqrt hhr.le
  have hsh0 : 0 ≤ Real.sqrt hh := Real.sqrt_nonneg _
  have hsh1 : Real.sqrt hh ≤ 1 := Real.sqrt_le_one.mpr hh1
  have hh2 : (hh : ℝ) ^ 2 ≤ Real.sqrt hh ^ 3 := by
    have e : (hh : ℝ) ^ 2 = Real.sqrt hh ^ 3 * Real.sqrt hh := by
      calc (hh : ℝ) ^ 2 = (Real.sqrt hh ^ 2) ^ 2 := by rw [hsh]
        _ = Real.sqrt hh ^ 3 * Real.sqrt hh := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsh1 (pow_nonneg hsh0 3)
    linarith
  have t1 : |(1 - z - exp (-z)) * F₀| ≤ Z ^ 2 * Real.sqrt hh ^ 3 := by
    rw [abs_mul]
    have h1 : |1 - z - exp (-z)| ≤ z ^ 2 := by
      have : 1 - z - exp (-z) = -(exp (-z) - 1 - (-z)) := by ring
      rw [this, abs_neg]; exact hexp1
    have h2 : z ^ 2 ≤ (Z * hh) ^ 2 := pow_le_pow_left₀ hz0 hzZ 2
    calc |1 - z - exp (-z)| * |F₀| ≤ z ^ 2 * 1 := mul_le_mul h1 hF₀ (abs_nonneg _) (sq_nonneg _)
      _ ≤ (Z * hh) ^ 2 := by linarith
      _ = Z ^ 2 * hh ^ 2 := by ring
      _ ≤ Z ^ 2 * Real.sqrt hh ^ 3 := mul_le_mul_of_nonneg_left hh2 (sq_nonneg _)
  have t2 : |hh * ((Dw - D) / 2) * m| ≤ hh * |Dw - D| := by
    rw [abs_mul, abs_mul, abs_of_pos hhr, abs_div, abs_two, abs_of_nonneg hm.1]
    have : |Dw - D| / 2 * m ≤ |Dw - D| := by nlinarith [abs_nonneg (Dw - D)]
    calc (hh : ℝ) * (|Dw - D| / 2) * m = hh * (|Dw - D| / 2 * m) := by ring
      _ ≤ hh * |Dw - D| := mul_le_mul_of_nonneg_left this hhr.le
  have t3 : |hh * (D / 2) * m * (1 - exp (-z))| ≤ D * Z * Real.sqrt hh ^ 3 := by
    rw [abs_of_nonneg (by have := hexp2.1; have := hm.1; positivity)]
    have h1 : hh * (D / 2) * m * (1 - exp (-z)) ≤ hh * (D / 2) * 2 * (Z * hh) := by
      have hA : 0 ≤ hh * (D / 2) := by positivity
      have := mul_le_mul hm.2 (hexp2.2.trans hzZ) hexp2.1 zero_le_two
      calc hh * (D / 2) * m * (1 - exp (-z)) = hh * (D / 2) * (m * (1 - exp (-z))) := by ring
        _ ≤ hh * (D / 2) * (2 * (Z * hh)) := mul_le_mul_of_nonneg_left this hA
        _ = hh * (D / 2) * 2 * (Z * hh) := by ring
    calc hh * (D / 2) * m * (1 - exp (-z)) ≤ hh * (D / 2) * 2 * (Z * hh) := h1
      _ = D * Z * hh ^ 2 := by ring
      _ ≤ D * Z * Real.sqrt hh ^ 3 := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hD hZ0)
  have t4 : |exp (-z) * E₁| ≤ (24 * (4 * D + 88 * D ^ 2) + D ^ 2) * Real.sqrt hh ^ 3 := by
    rw [abs_mul, abs_of_pos hexp3.1]
    have h1 : exp (-z) * |E₁| ≤ 1 * |E₁| := mul_le_mul_of_nonneg_right hexp3.2 (abs_nonneg _)
    have h2 : D ^ 2 * hh ^ 2 ≤ D ^ 2 * Real.sqrt hh ^ 3 := mul_le_mul_of_nonneg_left hh2 (sq_nonneg _)
    have e : (24 * (4 * D + 88 * D ^ 2) + D ^ 2) * Real.sqrt hh ^ 3 =
        24 * (4 * D + 88 * D ^ 2) * Real.sqrt hh ^ 3 + D ^ 2 * Real.sqrt hh ^ 3 := by ring
    rw [e]; linarith
  calc |r + (1 - z - exp (-z)) * F₀ + hh * ((Dw - D) / 2) * m + hh * (D / 2) * m * (1 - exp (-z))
        - exp (-z) * E₁|
      ≤ |r| + |(1 - z - exp (-z)) * F₀| + |hh * ((Dw - D) / 2) * m| +
          |hh * (D / 2) * m * (1 - exp (-z))| + |exp (-z) * E₁| := by
        have a1 := abs_sub (r + (1 - z - exp (-z)) * F₀ + hh * ((Dw - D) / 2) * m +
          hh * (D / 2) * m * (1 - exp (-z))) (exp (-z) * E₁)
        have a2 := abs_add_le (r + (1 - z - exp (-z)) * F₀ + hh * ((Dw - D) / 2) * m)
          (hh * (D / 2) * m * (1 - exp (-z)))
        have a3 := abs_add_le (r + (1 - z - exp (-z)) * F₀) (hh * ((Dw - D) / 2) * m)
        have a4 := abs_add_le r ((1 - z - exp (-z)) * F₀)
        linarith
    _ ≤ |r| + Z ^ 2 * Real.sqrt hh ^ 3 + hh * |Dw - D| + D * Z * Real.sqrt hh ^ 3 +
          (24 * (4 * D + 88 * D ^ 2) + D ^ 2) * Real.sqrt hh ^ 3 := by linarith
    _ = _ := by ring

/-- **Analytic core of the open-clock law theorem**: the discrete
determinant-Laplace equation with summable remainder, the entrance condition, and `D_W → D`
force `f_W(n_W/W, a) → E exp{-a c ∫₀^t q(t-s) e^{√D B_s - Ds/2} ds}` for every `a > 0`. -/
theorem tendsto_lap_of_clockEquation {D c T Qb : ℝ} (hD : 0 ≤ D) (hc : 0 ≤ c) (hT : 0 < T)
    {q : ℝ → ℝ} (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Qb)
    {Dseq : ℕ → ℝ} (hDseq : Tendsto Dseq atTop (𝓝 D)) (μ : ℕ → ℕ → Measure ℝ)
    [hμP : ∀ W j, IsProbabilityMeasure (μ W j)] (hμ : ∀ W j, ∀ᵐ x ∂μ W j, 0 ≤ x)
    (j₀ : ℕ → ℕ) (hj₀ : Tendsto (fun W => (j₀ W : ℝ) / W) atTop (𝓝 0))
    (hentr : ∀ b, 0 < b → Tendsto (fun W => lap (μ W (j₀ W)) b) atTop (𝓝 1))
    (heq : ClockEquation Dseq c q T μ j₀) {n : ℕ → ℕ} {t : ℝ} (ht : 0 < t)
    (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 t)) (hnT : ∀ W, (n W : ℝ) ≤ T * W)
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun W => lap (μ W (n W)) a) atTop (𝓝 (openClockLaplace D c q t a)) := by
  set P := canonicalWienerLaw
  have hQb0 : 0 ≤ Qb := (hq0 0).trans (hqb 0)
  have hsT : ∀ W, (n W : ℝ) / W ≤ T := by
    intro W
    rcases Nat.eq_zero_or_pos W with h0 | h0
    · subst h0; simp [hT.le]
    · rw [div_le_iff₀ (by exact_mod_cast h0)]; exact hnT W
  have htT : t ≤ T := le_of_tendsto' hn hsT
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / 10 with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨K, hK1, haK, hexit⟩ := exists_dualAlive_ge D ha hT.le hε'0
  obtain ⟨δ, hδ, hδsum⟩ := heq K hK1
  have hK0 : 0 < K := by linarith
  set C₁ := (c * Qb * K) ^ 2 + D * (c * Qb * K) + 24 * (4 * D + 88 * D ^ 2) + D ^ 2 with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ c * Qb * K := by positivity
    positivity
  -- eventual conditions
  have hinv : Tendsto (fun W : ℕ => (W : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun W : ℕ => Real.sqrt ((W : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hinv
    rw [Real.sqrt_zero] at this
    exact this
  have E1 : ∀ᶠ W : ℕ in atTop, 1 ≤ W := eventually_ge_atTop 1
  have E3 : ∀ᶠ W : ℕ in atTop, 10 * D * (W : ℝ)⁻¹ ≤ 1 := by
    have := (hinv.const_mul (10 * D)).eventually (ge_mem_nhds (show 10 * D * 0 < 1 by simp))
    exact this
  have E4 : ∀ᶠ W : ℕ in atTop, c * Qb * K * (W : ℝ)⁻¹ ≤ 1 := by
    have := (hinv.const_mul (c * Qb * K)).eventually
      (ge_mem_nhds (show c * Qb * K * 0 < 1 by simp))
    exact this
  have hdiffT : Tendsto (fun W => (n W : ℝ) / W - (j₀ W : ℝ) / W) atTop (𝓝 t) := by
    simpa using hn.sub hj₀
  have E5 : ∀ᶠ W in atTop, j₀ W ≤ n W := by
    have := hdiffT.eventually (lt_mem_nhds ht)
    filter_upwards [this] with W hW
    by_contra hlt
    push Not at hlt
    have : (n W : ℝ) / W - (j₀ W : ℝ) / W ≤ 0 := by
      rw [sub_nonpos]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) (Nat.cast_nonneg _)
    linarith
  have E6 : ∀ᶠ W in atTop, ∑ j ∈ Finset.Icc (j₀ W) ⌊T * W⌋₊, δ W j ≤ ε' :=
    (hδsum.eventually (ge_mem_nhds hε'0))
  have E7 : ∀ᶠ W : ℕ in atTop, T * C₁ * Real.sqrt ((W : ℝ)⁻¹) ≤ ε' := by
    have := (hsqrt.const_mul (T * C₁)).eventually (ge_mem_nhds (show T * C₁ * 0 < ε' by simpa))
    exact this
  have E8 : ∀ᶠ W in atTop, T * |Dseq W - D| ≤ ε' := by
    have h1 : Tendsto (fun W => T * |Dseq W - D|) atTop (𝓝 (T * |D - D|)) :=
      ((hDseq.sub tendsto_const_nhds).abs).const_mul T
    simp only [sub_self, abs_zero, mul_zero] at h1
    exact (h1.eventually (ge_mem_nhds hε'0))
  have E9 : ∀ᶠ W in atTop, 1 - lap (μ W (j₀ W)) K ≤ ε' := by
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub (hentr K hK0)
    simp only [sub_self] at h1
    exact (h1.eventually (ge_mem_nhds hε'0))
  have E10 : ∀ᶠ W : ℕ in atTop, |(∫ ω, dualKill D a c q ((n W : ℝ) / W) ((W : ℝ≥0)⁻¹)
      (sampleW ((W : ℝ≥0)⁻¹) ω) (n W - j₀ W) ∂P) - openClockLaplace D c q t a| < ε' := by
    have := tendsto_integral_dualKill (D := D) hq hq0 ha hc ht htT hn hnT hj₀
    have := (Metric.tendsto_nhds.mp this) ε' hε'0
    simpa [Real.dist_eq] using this
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
    (E1.and (E3.and (E4.and (E5.and (E6.and (E7.and (E8.and (E9.and E10))))))))
  refine ⟨W₀, fun W hW => ?_⟩
  obtain ⟨e1, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hW₀ W hW
  -- notation at this width
  set hh : ℝ≥0 := (W : ℝ≥0)⁻¹ with hhdef
  have hhr : (hh : ℝ) = (W : ℝ)⁻¹ := by
    show (((W : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (W : ℝ)⁻¹
    push_cast; rfl
  have hWpos : (0 : ℝ) < W := by exact_mod_cast e1
  have hh0 : 0 < hh := by
    rw [← NNReal.coe_pos, hhr]; positivity
  have hh1 : (hh : ℝ) ≤ 1 := by
    rw [hhr]; exact inv_le_one_of_one_le₀ (by exact_mod_cast e1)
  set N := n W - j₀ W with hN
  set μs : ℕ → Measure ℝ := fun k => μ W (n W - k) with hμs
  have hμsP : ∀ k, IsProbabilityMeasure (μs k) := fun k => hμP W _
  set εs : ℕ → ℝ := fun k => C₁ * Real.sqrt hh ^ 3 + hh * |Dseq W - D| + max (δ W (n W - k - 1)) 0
    with hεs
  have hεs0 : ∀ k, 0 ≤ εs k := fun k => by
    have := le_max_right (δ W (n W - k - 1)) 0
    have : 0 ≤ C₁ * Real.sqrt hh ^ 3 := by positivity
    have : 0 ≤ (hh : ℝ) * |Dseq W - D| := by positivity
    simp only [hεs]; linarith
  have hnW : (n W : ℝ) ≤ T * W := hnT W
  have hTW0 : 0 ≤ T * W := by positivity
  have hfloor : n W ≤ ⌊T * W⌋₊ := Nat.le_floor hnW
  -- nonnegativity of δ on the range
  have hδ0 : ∀ j ∈ Finset.Icc (j₀ W) ⌊T * W⌋₊, 0 ≤ δ W j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjT : (j : ℝ) ≤ T * W := (Nat.cast_le.mpr hj.2).trans (Nat.floor_le hTW0)
    have h1 : (1 : ℝ) ∈ Icc K⁻¹ K := ⟨inv_le_one_of_one_le₀ hK1, hK1⟩
    exact (abs_nonneg _).trans (hδ W j hj.1 hjT 1 h1)
  -- the step hypothesis of `dual_compare`
  have hstep : ∀ k < N, ∀ b ∈ Icc K⁻¹ K, |lap (μs k) b - exp (-(c * hh *
      q ((n W : ℝ) / W - k * hh) * b)) * ∫ ω, lap (μs (k + 1))
        (b * lognormal D ((k : ℝ≥0) * hh) hh ω) ∂P| ≤ εs k := by
    intro k hk b hb
    have hkn : k < n W := lt_of_lt_of_le hk (Nat.sub_le _ _)
    set j := n W - k - 1 with hj
    have hj1 : j + 1 = n W - k := by omega
    have hj2 : n W - (k + 1) = j := by omega
    have hjj₀ : j₀ W ≤ j := by omega
    have hjT : (j : ℝ) ≤ T * W := by
      have : (j : ℝ) ≤ n W := by exact_mod_cast (show j ≤ n W by omega)
      linarith
    have hb0 : 0 ≤ b := (inv_pos.mpr hK0).le.trans hb.1
    have hqs : q ((n W : ℝ) / W - k * hh) = q (((j + 1 : ℕ) : ℝ) / W) := by
      congr 1
      rw [hj1, Nat.cast_sub hkn.le, hhr]; field_simp
    have hcons := step_consistency hD hc (Dseq W) (hq0 ((n W : ℝ) / W - k * hh))
      (hqb ((n W : ℝ) / W - k * hh)) ((k : ℝ≥0) * hh) hh hh0 hh1 (by rw [hhr]; exact e3)
      (by rw [hhr]; exact e4) (μs (k + 1)) (μs k) (hμ W _) hb0 hb.2
    refine hcons.trans ?_
    have hrem : |lap (μs k) b - lap (μs (k + 1)) b - hh * (Dseq W / 2 * b ^ 2 *
        lap2 (μs (k + 1)) b - c * q ((n W : ℝ) / W - k * hh) * b * lap (μs (k + 1)) b)|
        ≤ δ W j := by
      have := hδ W j hjj₀ hjT b hb
      unfold clockRemainder at this
      simp only [hμs, hj2]
      rw [← hj1, hqs, hhr]
      exact this
    have : δ W j ≤ max (δ W (n W - k - 1)) 0 := le_max_left _ _
    simp only [hεs]
    linarith
  have hentr' : ∀ b ∈ Icc K⁻¹ K, |lap (μs N) b - 1| ≤ ε' := by
    intro b hb
    have hN' : n W - N = j₀ W := by omega
    simp only [hμs, hN']
    have hb0 : 0 ≤ b := (inv_pos.mpr hK0).le.trans hb.1
    have h1 := lap_le_one (μ W (j₀ W)) (hμ W _) hb0
    have h2 := lap_antitone (μ W (j₀ W)) (hμ W _) hb0 hb.2
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hcmp := dual_compare (D := D) (q := q) (t := (n W : ℝ) / W) (hh := hh) ha hc hq0 haK N μs
    (fun k => hμ W _) εs hεs0 hstep hentr'
  -- the exit term
  have hNT : (N : ℝ) * hh ≤ T := by
    have : (N : ℝ) ≤ n W := by exact_mod_cast Nat.sub_le _ _
    calc (N : ℝ) * hh ≤ n W * hh := mul_le_mul_of_nonneg_right this hh.2
      _ = (n W : ℝ) / W := by rw [hhr]; ring
      _ ≤ T := hsT W
  have hex := hexit hh N hNT
  -- the sum of the step errors
  have hsum : ∑ k ∈ Finset.range N, εs k ≤ 3 * ε' := by
    have e : ∑ k ∈ Finset.range N, εs k = N * (C₁ * Real.sqrt hh ^ 3 + hh * |Dseq W - D|) +
        ∑ k ∈ Finset.range N, max (δ W (n W - k - 1)) 0 := by
      simp only [hεs]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [e]
    have hNh : (N : ℝ) * hh ≤ T := hNT
    have hsh : Real.sqrt hh ^ 3 = hh * Real.sqrt hh := by
      have := Real.sq_sqrt (NNReal.coe_nonneg hh)
      calc Real.sqrt hh ^ 3 = Real.sqrt hh ^ 2 * Real.sqrt hh := by ring
        _ = hh * Real.sqrt hh := by rw [this]
    have h1 : (N : ℝ) * (C₁ * Real.sqrt hh ^ 3) ≤ ε' := by
      rw [hsh]
      calc (N : ℝ) * (C₁ * (hh * Real.sqrt hh)) = C₁ * Real.sqrt hh * (N * hh) := by ring
        _ ≤ C₁ * Real.sqrt hh * T := mul_le_mul_of_nonneg_left hNh (by positivity)
        _ = T * C₁ * Real.sqrt ((W : ℝ)⁻¹) := by rw [hhr]; ring
        _ ≤ ε' := e7
    have h2 : (N : ℝ) * (hh * |Dseq W - D|) ≤ ε' := by
      calc (N : ℝ) * (hh * |Dseq W - D|) = |Dseq W - D| * (N * hh) := by ring
        _ ≤ |Dseq W - D| * T := mul_le_mul_of_nonneg_left hNh (abs_nonneg _)
        _ = T * |Dseq W - D| := by ring
        _ ≤ ε' := e8
    have h3 : ∑ k ∈ Finset.range N, max (δ W (n W - k - 1)) 0 ≤ ε' := by
      have hre : ∑ k ∈ Finset.range N, max (δ W (n W - k - 1)) 0 =
          ∑ m ∈ Finset.range N, max (δ W (j₀ W + m)) 0 := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' := Finset.mem_range.mp hm
        congr 2
        omega
      have hIco : ∑ m ∈ Finset.range N, max (δ W (j₀ W + m)) 0 =
          ∑ j ∈ Finset.Ico (j₀ W) (j₀ W + N), max (δ W j) 0 := by
        rw [Finset.sum_Ico_eq_sum_range]; simp
      have hsub : Finset.Ico (j₀ W) (j₀ W + N) ⊆ Finset.Icc (j₀ W) ⌊T * W⌋₊ := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [Finset.mem_Icc]
        omega
      have hmax : ∑ j ∈ Finset.Ico (j₀ W) (j₀ W + N), max (δ W j) 0 =
          ∑ j ∈ Finset.Ico (j₀ W) (j₀ W + N), δ W j :=
        Finset.sum_congr rfl fun j hj => max_eq_left (hδ0 j (hsub hj))
      rw [hre, hIco, hmax]
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hδ0 j hj).trans e6
    nlinarith [h1, h2, h3]
  -- assemble
  have hμs0 : μs 0 = μ W (n W) := by simp [hμs]
  rw [hμs0] at hcmp
  rw [Real.dist_eq]
  calc |lap (μ W (n W)) a - openClockLaplace D c q t a|
      ≤ |lap (μ W (n W)) a - ∫ ω, dualKill D a c q ((n W : ℝ) / W) hh (sampleW hh ω) N ∂P| +
        |(∫ ω, dualKill D a c q ((n W : ℝ) / W) hh (sampleW hh ω) N ∂P) -
          openClockLaplace D c q t a| := abs_sub_le _ _ _
    _ ≤ (3 * ε' + 2 * ε' + ε') + ε' := by
        refine add_le_add (hcmp.trans ?_) e10.le
        linarith
    _ < ε := by rw [hε']; linarith

end OpenClock
end BlockBand.Endpoints.Clock
