module

public import BlockBand.Layers.CompensatedIncrement

/-!
# The compensated two-port phase: the compensated-phase lemma

This file proves the compensated-phase lemma (`CompensatedPhaseContract`) from the matched traces
and three further inputs on the conditional increments and the cores.

* A martingale moment step (`cph_moment_step`): if `s` depends on the old path only and the
  fresh-layer deviation `d` has conditional mean zero, then
  `‖s + d‖_{2m}² ≤ ‖s‖_{2m}² + 4^{m+1} ‖d‖_{2m}²` (binomial expansion, the linear term vanishes
  by Fubini, a pointwise Young inequality for the mixed terms). Iterated along the growth this is
  the martingale moment inequality of the proof.
* The growth identity (`cph_psi_pgGrow`): by Schur inertia (`negativeCount_fromBlocks_schur22`)
  and the two-ended Schur composition (`pathSchur_pgGrow`), almost surely
  `Ψ_{r+2}(grown path) = Ψ_r + N_-(A - E - X_r) + Θ_{z_∂}(X_{r+2}) - Θ_{z_∂}(X_r)`.
* `compensatedPhase_of_inputs`: `CompensatedPhaseContract` from the matched traces
  (`MatchedTracesContract.path`), the separate-port conditional mean increments
  (`CompensatedIncrementContract.separate`), and the two isolated inputs
  `CphIncrementFluctuation` (bounded `L^p` norms of the conditionally centered increments) and
  `CphCore` (the cores `r = 1, 2`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## 1. Elementary inequalities
-/

section Elementary

theorem cph_term_le {s d : ℝ} {n k : ℕ} (hn : Even n) (hk : k ≤ n) :
    |d ^ (k + 2) * s ^ (n - k)| ≤ s ^ n * d ^ 2 + d ^ (n + 2) := by
  have h1 : 0 ≤ s ^ n * d ^ 2 := mul_nonneg (hn.pow_nonneg s) (sq_nonneg d)
  have h2 : 0 ≤ d ^ (n + 2) := (hn.add even_two).pow_nonneg d
  rw [abs_mul, abs_pow, abs_pow]
  rcases le_or_gt |d| |s| with h | h
  · have : |d| ^ (k + 2) * |s| ^ (n - k) ≤ |s| ^ n * d ^ 2 := by
      have hk' : |d| ^ k ≤ |s| ^ k := pow_le_pow_left₀ (abs_nonneg d) h k
      calc |d| ^ (k + 2) * |s| ^ (n - k) = d ^ 2 * (|d| ^ k * |s| ^ (n - k)) := by
            rw [pow_add, sq_abs]; ring
        _ ≤ d ^ 2 * (|s| ^ k * |s| ^ (n - k)) := by gcongr
        _ = |s| ^ n * d ^ 2 := by rw [← pow_add, Nat.add_sub_cancel' hk]; ring
    rw [hn.pow_abs] at this
    linarith
  · have : |d| ^ (k + 2) * |s| ^ (n - k) ≤ |d| ^ (n + 2) := by
      calc |d| ^ (k + 2) * |s| ^ (n - k) ≤ |d| ^ (k + 2) * |d| ^ (n - k) := by
            gcongr
        _ = |d| ^ (n + 2) := by rw [← pow_add]; congr 1; omega
    rw [(hn.add even_two).pow_abs] at this
    linarith

theorem cph_choose_sum_le (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) := by
  have h := Nat.sum_range_choose (n + 2)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
  have h' : ∑ k ∈ Finset.range (n + 1), (n + 2).choose (k + 1 + 1) ≤ 2 ^ (n + 2) := by
    rw [← h]; omega
  exact_mod_cast h'

/-- Second-order binomial bound:
`(s + d)^{2m} ≤ s^{2m} + 2m s^{2m-1} d + 4^m (s^{2m-2} d² + d^{2m})`. -/
theorem cph_pow_bound {m : ℕ} (hm : 1 ≤ m) (s d : ℝ) :
    (s + d) ^ (2 * m) ≤ s ^ (2 * m) + 2 * m * s ^ (2 * m - 1) * d +
      4 ^ m * (s ^ (2 * m - 2) * d ^ 2 + d ^ (2 * m)) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * m = n + 2 := ⟨2 * m - 2, by omega⟩
  have hev : Even n := ⟨m - 1, by omega⟩
  have hcast : (2 * (m : ℝ)) = ((n + 2 : ℕ) : ℝ) := by rw [← hn]; push_cast; ring
  have h4 : (4 : ℝ) ^ m = 2 ^ (n + 2) := by
    rw [← hn, pow_mul]; norm_num
  rw [hcast, hn, h4, show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega,
    add_comm s d, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_one,
    Nat.choose_one_right, zero_add, Nat.sub_zero]
  have hrest : ∑ k ∈ Finset.range (n + 1), d ^ (k + 1 + 1) * s ^ (n - k) *
      ((n + 2).choose (k + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) * (s ^ n * d ^ 2 + d ^ (n + 2)) := by
    have h0 : 0 ≤ s ^ n * d ^ 2 + d ^ (n + 2) :=
      add_nonneg (mul_nonneg (hev.pow_nonneg s) (sq_nonneg d)) ((hev.add even_two).pow_nonneg d)
    calc _ ≤ ∑ k ∈ Finset.range (n + 1), (s ^ n * d ^ 2 + d ^ (n + 2)) *
          ((n + 2).choose (k + 1 + 1) : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have := cph_term_le (s := s) (d := d) hev hk'
          exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans this) (Nat.cast_nonneg _)
      _ = (s ^ n * d ^ 2 + d ^ (n + 2)) * ∑ k ∈ Finset.range (n + 1),
          ((n + 2).choose (k + 1 + 1) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (s ^ n * d ^ 2 + d ^ (n + 2)) * 2 ^ (n + 2) :=
          mul_le_mul_of_nonneg_left (cph_choose_sum_le n) h0
      _ = _ := by ring
  have hsum_eq : ∑ k ∈ Finset.range (n + 1), d ^ (k + 1 + 1) * s ^ (n + 2 - (k + 1 + 1)) *
      ((n + 2).choose (k + 1 + 1) : ℝ) = ∑ k ∈ Finset.range (n + 1), d ^ (k + 1 + 1) *
      s ^ (n - k) * ((n + 2).choose (k + 1 + 1) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [show n + 2 - (k + 1 + 1) = n - k by omega]
  rw [hsum_eq, show n + 2 - 1 = n + 1 by omega]
  push_cast
  have hlin : d * s ^ (n + 1) * ((n : ℝ) + 2) = ((n : ℝ) + 2) * s ^ (n + 1) * d := by ring
  linarith

/-- Pointwise Young inequality `u^{m-1} v ≤ λ u^m + λ^{-(m-1)} v^m` (`u, v ≥ 0`, `λ > 0`). -/
theorem cph_young {m : ℕ} (hm : 1 ≤ m) {u v lam : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hl : 0 < lam) :
    u ^ (m - 1) * v ≤ lam * u ^ m + lam⁻¹ ^ (m - 1) * v ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hA : 0 ≤ lam * u ^ (k + 1) := mul_nonneg hl.le (pow_nonneg hu _)
  have hB : 0 ≤ lam⁻¹ ^ k * v ^ (k + 1) := mul_nonneg (pow_nonneg (inv_nonneg.mpr hl.le) _)
    (pow_nonneg hv _)
  rcases le_or_gt v (lam * u) with h | h
  · have : u ^ k * v ≤ lam * u ^ (k + 1) := by
      calc u ^ k * v ≤ u ^ k * (lam * u) := mul_le_mul_of_nonneg_left h (pow_nonneg hu _)
        _ = lam * u ^ (k + 1) := by ring
    linarith
  · have hu' : u ≤ lam⁻¹ * v := by
      rw [inv_mul_eq_div, le_div_iff₀ hl]; linarith
    have : u ^ k * v ≤ lam⁻¹ ^ k * v ^ (k + 1) := by
      calc u ^ k * v ≤ (lam⁻¹ * v) ^ k * v :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu hu' k) hv
        _ = lam⁻¹ ^ k * v ^ (k + 1) := by ring
    linarith

theorem cph_bernoulli {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) (k : ℕ) :
    a ^ (k + 1) + (k + 1) * a ^ k * y ≤ (a + y) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ a + y := add_nonneg ha hy
    calc a ^ (k + 1 + 1) + ((k + 1 : ℕ) + 1 : ℝ) * a ^ (k + 1) * y
        ≤ (a ^ (k + 1) + (k + 1) * a ^ k * y) * (a + y) := by
          push_cast
          have : 0 ≤ (k + 1 : ℝ) * a ^ k * y * y := by positivity
          have e : (a ^ (k + 1) + (k + 1) * a ^ k * y) * (a + y) =
              a ^ (k + 1 + 1) + ((k : ℝ) + 1 + 1) * a ^ (k + 1) * y + (k + 1) * a ^ k * y * y := by
            ring
          linarith
      _ ≤ (a + y) ^ (k + 1) * (a + y) := mul_le_mul_of_nonneg_right ih h1
      _ = (a + y) ^ (k + 1 + 1) := (pow_succ _ _).symm

/-- `a^m + 4^m (2 a^{m-1} b + 2 b^m) ≤ (a + 4^{m+1} b)^m` for `a, b ≥ 0`, `m ≥ 1`. -/
theorem cph_final_ineq {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ m + 4 ^ m * (2 * (a ^ (m - 1) * b) + 2 * b ^ m) ≤ (a + 4 ^ (m + 1) * b) ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hc : (1 : ℝ) ≤ 4 ^ (k + 1 + 1) := one_le_pow₀ (by norm_num)
  have hy : 0 ≤ 4 ^ (k + 1 + 1) * b := by positivity
  have hB := cph_bernoulli ha hy k
  have hP := pow_add_pow_le ha hy (Nat.succ_ne_zero k)
  have h4 : (4 : ℝ) ^ (k + 1 + 1) = 4 * 4 ^ (k + 1) := by ring
  have hpow : (4 ^ (k + 1 + 1) * b) ^ (k + 1) ≥ 4 ^ (k + 1 + 1) * b ^ (k + 1) := by
    rw [mul_pow]
    have : (4 : ℝ) ^ (k + 1 + 1) ≤ (4 ^ (k + 1 + 1)) ^ (k + 1) := by
      calc (4 : ℝ) ^ (k + 1 + 1) = (4 ^ (k + 1 + 1)) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hc (by omega)
    exact mul_le_mul_of_nonneg_right this (pow_nonneg hb _)
  have hab : 0 ≤ a ^ k * b := mul_nonneg (pow_nonneg ha _) hb
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hbk : 0 ≤ b ^ (k + 1) := pow_nonneg hb _
  have h4k : (0 : ℝ) < 4 ^ (k + 1) := by positivity
  simp only [Nat.succ_eq_add_one] at hP
  rw [h4] at hB hpow hP ⊢
  have hkab := mul_nonneg hk (mul_nonneg h4k.le hab)
  nlinarith

/-- `√((a + t)² + k) ≤ √(a² + k) + t` for `a, t, k ≥ 0`. -/
theorem cph_sqrt_shift {a t k : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hk : 0 ≤ k) :
    Real.sqrt ((a + t) ^ 2 + k) ≤ Real.sqrt (a ^ 2 + k) + t := by
  rw [Real.sqrt_le_left (by positivity)]
  have hs := Real.sq_sqrt (show 0 ≤ a ^ 2 + k by positivity)
  have hA : a ≤ Real.sqrt (a ^ 2 + k) := by
    rw [Real.le_sqrt ha (by positivity)]; linarith
  nlinarith

end Elementary

/-!
## 2. Even moments and `eLpNorm`
-/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem cph_memLp_of_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ :=
  MemLp.of_bound hf B (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem cph_integrable_of_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) : Integrable f μ :=
  memLp_one_iff_integrable.mp (cph_memLp_of_bound hf hB 1)

theorem cph_integrable_of_bound' [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, |f x| ≤ B) : Integrable f μ :=
  memLp_one_iff_integrable.mp
    (MemLp.of_bound hf B (hB.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx))

theorem cph_eLpNorm_eq {f : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : MemLp f (ENNReal.ofReal (2 * (m : ℝ))) μ) :
    eLpNorm f (ENNReal.ofReal (2 * (m : ℝ))) μ =
      ENNReal.ofReal ((∫ x, f x ^ (2 * m) ∂μ) ^ (2 * (m : ℝ))⁻¹) := by
  have hp : (0 : ℝ) < 2 * m := by positivity
  rw [hf.eLpNorm_eq_integral_rpow_norm (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp)
    ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]
  congr 3
  funext x
  rw [Real.norm_eq_abs, show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, (even_two_mul m).pow_abs]

theorem cph_eLpNorm_le_of_integral {f : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : MemLp f (ENNReal.ofReal (2 * (m : ℝ))) μ) {X : ℝ} (hX : 0 ≤ X)
    (h : ∫ x, f x ^ (2 * m) ∂μ ≤ X ^ (2 * m)) :
    eLpNorm f (ENNReal.ofReal (2 * (m : ℝ))) μ ≤ ENNReal.ofReal X := by
  rw [cph_eLpNorm_eq hm hf]
  refine ENNReal.ofReal_le_ofReal ?_
  have hI : 0 ≤ ∫ x, f x ^ (2 * m) ∂μ :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  have hp : (0 : ℝ) < 2 * m := by positivity
  calc (∫ x, f x ^ (2 * m) ∂μ) ^ (2 * (m : ℝ))⁻¹ ≤ (X ^ (2 * m)) ^ (2 * (m : ℝ))⁻¹ :=
        Real.rpow_le_rpow hI h (inv_nonneg.mpr hp.le)
    _ = X := by
        rw [show (X ^ (2 * m)) = X ^ ((2 * m : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_mul hX]
        push_cast
        rw [mul_inv_cancel₀ hp.ne', Real.rpow_one]

theorem cph_integral_le_of_eLpNorm {f : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : MemLp f (ENNReal.ofReal (2 * (m : ℝ))) μ) {X : ℝ} (hX : 0 ≤ X)
    (h : eLpNorm f (ENNReal.ofReal (2 * (m : ℝ))) μ ≤ ENNReal.ofReal X) :
    ∫ x, f x ^ (2 * m) ∂μ ≤ X ^ (2 * m) := by
  rw [cph_eLpNorm_eq hm hf, ENNReal.ofReal_le_ofReal_iff hX] at h
  have hI : 0 ≤ ∫ x, f x ^ (2 * m) ∂μ :=
    integral_nonneg fun x => (even_two_mul m).pow_nonneg _
  have hp : (0 : ℝ) < 2 * m := by positivity
  have h2 := pow_le_pow_left₀ (Real.rpow_nonneg hI _) h (2 * m)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul hI, show (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) by
    push_cast; ring, inv_mul_cancel₀ hp.ne', Real.rpow_one] at h2

theorem cph_eLpNorm_const [IsProbabilityMeasure μ] (c : ℝ) {p : ℝ} (hp : 0 < p) :
    eLpNorm (fun _ : Ω => c) (ENNReal.ofReal p) μ = ENNReal.ofReal |c| := by
  rw [eLpNorm_const' c (by simpa using hp) ENNReal.ofReal_ne_top, measure_univ, ENNReal.one_rpow,
    mul_one, Real.enorm_eq_ofReal_abs]

end Moments

/-!
## 3. The martingale moment step
-/

section Step

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {ν : Measure α} {μ : Measure β} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

theorem cph_integral_comp_snd {f : β → ℝ} (hf : Measurable f) :
    ∫ z, f z.2 ∂(ν.prod μ) = ∫ y, f y ∂μ := by
  rw [← integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable, Measure.map_snd_prod,
    measure_univ, one_smul]

theorem cph_eLpNorm_comp_snd {f : β → ℝ} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun z : α × β => f z.2) p (ν.prod μ) = eLpNorm f p μ := by
  have h := eLpNorm_map_measure (μ := ν.prod μ) (p := p) (f := Prod.snd) (g := f)
    hf.aestronglyMeasurable measurable_snd.aemeasurable
  rw [Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

theorem cph_abs_pow_le {x B : ℝ} (h : |x| ≤ B) (k : ℕ) : |x ^ k| ≤ B ^ k := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg x) h k

/-- **One-step moment bound with a pointwise free parameter** `λ > 0`. -/
theorem cph_moment_step_lam {m : ℕ} (hm : 1 ≤ m) {s : β → ℝ} {d : α × β → ℝ}
    (hs : Measurable s) (hd : Measurable d) {Bs Bd : ℝ} (hsb : ∀ y, |s y| ≤ Bs)
    (hdb : ∀ z, |d z| ≤ Bd) (hd0 : ∀ y, ∫ x, d (x, y) ∂ν = 0) {lam : ℝ} (hl : 0 < lam) :
    ∫ z, (s z.2 + d z) ^ (2 * m) ∂(ν.prod μ) ≤
      (1 + 4 ^ m * lam) * ∫ y, s y ^ (2 * m) ∂μ +
        4 ^ m * (lam⁻¹ ^ (m - 1) + 1) * ∫ z, d z ^ (2 * m) ∂(ν.prod μ) := by
  have hs2 : Measurable (fun z : α × β => s z.2) := hs.comp measurable_snd
  have hI1 : Integrable (fun z : α × β => s z.2 ^ (2 * m)) (ν.prod μ) :=
    cph_integrable_of_bound (hs2.pow_const _).aestronglyMeasurable
      (fun z => cph_abs_pow_le (hsb z.2) _)
  have hI2 : Integrable (fun z : α × β => s z.2 ^ (2 * m - 1) * d z) (ν.prod μ) :=
    cph_integrable_of_bound ((hs2.pow_const _).mul hd).aestronglyMeasurable
      (B := Bs ^ (2 * m - 1) * Bd) (fun z => by
        rw [abs_mul]
        exact mul_le_mul (cph_abs_pow_le (hsb z.2) _) (hdb z) (abs_nonneg _)
          ((abs_nonneg _).trans (cph_abs_pow_le (hsb z.2) _)))
  have hI3 : Integrable (fun z : α × β => d z ^ (2 * m)) (ν.prod μ) :=
    cph_integrable_of_bound (hd.pow_const _).aestronglyMeasurable
      (fun z => cph_abs_pow_le (hdb z) _)
  have hI0 : Integrable (fun z : α × β => (s z.2 + d z) ^ (2 * m)) (ν.prod μ) :=
    cph_integrable_of_bound ((hs2.add hd).pow_const _).aestronglyMeasurable
      (fun z => cph_abs_pow_le ((abs_add_le _ _).trans (add_le_add (hsb z.2) (hdb z))) _)
  have hzero : ∫ z, s z.2 ^ (2 * m - 1) * d z ∂(ν.prod μ) = 0 := by
    rw [integral_prod_symm _ hI2]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.zero_apply]
    rw [integral_const_mul, hd0 y, mul_zero]
  have hpt : ∀ z : α × β, (s z.2 + d z) ^ (2 * m) ≤
      (1 + 4 ^ m * lam) * s z.2 ^ (2 * m) + (2 * m) * (s z.2 ^ (2 * m - 1) * d z) +
        4 ^ m * (lam⁻¹ ^ (m - 1) + 1) * d z ^ (2 * m) := by
    intro z
    have h1 := cph_pow_bound hm (s z.2) (d z)
    have h2 := cph_young hm (sq_nonneg (s z.2)) (sq_nonneg (d z)) hl
    rw [← pow_mul, ← pow_mul, ← pow_mul, show 2 * (m - 1) = 2 * m - 2 by omega] at h2
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  calc ∫ z, (s z.2 + d z) ^ (2 * m) ∂(ν.prod μ)
      ≤ ∫ z, ((1 + 4 ^ m * lam) * s z.2 ^ (2 * m) + (2 * m) * (s z.2 ^ (2 * m - 1) * d z) +
          4 ^ m * (lam⁻¹ ^ (m - 1) + 1) * d z ^ (2 * m)) ∂(ν.prod μ) :=
        integral_mono hI0 (((hI1.const_mul _).add (hI2.const_mul _)).add (hI3.const_mul _)) hpt
    _ = (1 + 4 ^ m * lam) * ∫ y, s y ^ (2 * m) ∂μ +
        4 ^ m * (lam⁻¹ ^ (m - 1) + 1) * ∫ z, d z ^ (2 * m) ∂(ν.prod μ) := by
        rw [integral_add (f := fun z => (1 + 4 ^ m * lam) * s z.2 ^ (2 * m) +
            (2 * m) * (s z.2 ^ (2 * m - 1) * d z))
            (g := fun z => 4 ^ m * (lam⁻¹ ^ (m - 1) + 1) * d z ^ (2 * m))
            ((hI1.const_mul _).add (hI2.const_mul _)) (hI3.const_mul _),
          integral_add (f := fun z => (1 + 4 ^ m * lam) * s z.2 ^ (2 * m))
            (g := fun z => (2 * m) * (s z.2 ^ (2 * m - 1) * d z))
            (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
          integral_const_mul, hzero, cph_integral_comp_snd (hs.pow_const _)]
        ring

theorem cph_max_pow_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    max a b ^ k ≤ a ^ k + b ^ k := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith [pow_nonneg ha k]
  · rw [max_eq_left h]; linarith [pow_nonneg hb k]

/-- **The martingale moment step**: `s` depends on the old path only, `d` has conditional mean
zero given the old path; then `E(s + d)^{2m} ≤ (X² + 4^{m+1} K²)^m` whenever
`E s^{2m} ≤ X^{2m}` and `E d^{2m} ≤ K^{2m}`. -/
theorem cph_moment_step {m : ℕ} (hm : 1 ≤ m) {s : β → ℝ} {d : α × β → ℝ}
    (hs : Measurable s) (hd : Measurable d) {Bs Bd : ℝ} (hsb : ∀ y, |s y| ≤ Bs)
    (hdb : ∀ z, |d z| ≤ Bd) (hd0 : ∀ y, ∫ x, d (x, y) ∂ν = 0) {X K : ℝ} (hX0 : 0 ≤ X)
    (hK0 : 0 ≤ K) (hX : ∫ y, s y ^ (2 * m) ∂μ ≤ X ^ (2 * m))
    (hK : ∫ z, d z ^ (2 * m) ∂(ν.prod μ) ≤ K ^ (2 * m)) :
    ∫ z, (s z.2 + d z) ^ (2 * m) ∂(ν.prod μ) ≤ (X ^ 2 + 4 ^ (m + 1) * K ^ 2) ^ m := by
  set I := ∫ z, (s z.2 + d z) ^ (2 * m) ∂(ν.prod μ)
  have hS0 : 0 ≤ ∫ y, s y ^ (2 * m) ∂μ := integral_nonneg fun y => (even_two_mul m).pow_nonneg _
  have hD0 : 0 ≤ ∫ z, d z ^ (2 * m) ∂(ν.prod μ) :=
    integral_nonneg fun z => (even_two_mul m).pow_nonneg _
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hXm : X ^ (2 * m) = (X ^ 2) ^ m := by rw [← pow_mul]
  have hKm : K ^ (2 * m) = (K ^ 2) ^ m := by rw [← pow_mul]
  rcases hK0.eq_or_lt with hK | hK
  · -- `K = 0`: the deviation vanishes in `L^{2m}`.
    subst hK
    have hD : ∫ z, d z ^ (2 * m) ∂(ν.prod μ) = 0 :=
      le_antisymm (hK.trans (by rw [zero_pow (by omega)])) hD0
    have hI : I ≤ X ^ (2 * m) := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hY : 0 < X ^ (2 * m) + 1 := by positivity
      have hl : 0 < ε / (4 ^ m * (X ^ (2 * m) + 1)) := by positivity
      have h := cph_moment_step_lam (ν := ν) (μ := μ) hm hs hd hsb hdb hd0 hl
      rw [hD, mul_zero, add_zero] at h
      have hlX : 4 ^ m * (ε / (4 ^ m * (X ^ (2 * m) + 1))) * X ^ (2 * m) ≤ ε := by
        rw [show 4 ^ m * (ε / (4 ^ m * (X ^ (2 * m) + 1))) * X ^ (2 * m) =
          ε * (X ^ (2 * m) / (X ^ (2 * m) + 1)) by field_simp]
        exact mul_le_of_le_one_right hε.le ((div_le_one hY).mpr (by linarith))
      have hX' : (1 + 4 ^ m * (ε / (4 ^ m * (X ^ (2 * m) + 1)))) * ∫ y, s y ^ (2 * m) ∂μ ≤
          (1 + 4 ^ m * (ε / (4 ^ m * (X ^ (2 * m) + 1)))) * X ^ (2 * m) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      nlinarith
    rw [hXm] at hI
    simpa using hI
  · -- `K > 0`: take `λ = K² / max(X, K)²`.
    set Y := max X K with hYdef
    have hY : 0 < Y := lt_of_lt_of_le hK (le_max_right _ _)
    have hXY : X ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hX0 (le_max_left _ _) 2
    set lam := K ^ 2 / Y ^ 2 with hlam
    have hl : 0 < lam := by positivity
    have h := cph_moment_step_lam (ν := ν) (μ := μ) hm hs hd hsb hdb hd0 hl
    set a := X ^ 2
    set c := K ^ 2
    have ha : 0 ≤ a := sq_nonneg X
    have hc : 0 < c := by positivity
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h ⊢
    -- the first term
    have hA : 4 ^ (k + 1) * lam * ∫ y, s y ^ (2 * (k + 1)) ∂μ ≤ 4 ^ (k + 1) * (a ^ k * c) := by
      have : lam * a ^ (k + 1) ≤ a ^ k * c := by
        rw [hlam, pow_succ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        calc K ^ 2 * (a ^ k * a) = a ^ k * c * a := by ring
          _ ≤ a ^ k * c * Y ^ 2 := mul_le_mul_of_nonneg_left hXY (by positivity)
      have h2 : lam * ∫ y, s y ^ (2 * (k + 1)) ∂μ ≤ lam * a ^ (k + 1) := by
        rw [← hXm]; exact mul_le_mul_of_nonneg_left hX hl.le
      nlinarith
    -- the second term
    have hB : lam⁻¹ ^ k * ∫ z, d z ^ (2 * (k + 1)) ∂(ν.prod μ) ≤ a ^ k * c + c ^ (k + 1) := by
      have hinv : lam⁻¹ = Y ^ 2 / c := by rw [hlam, inv_div]
      have h1 : lam⁻¹ ^ k * ∫ z, d z ^ (2 * (k + 1)) ∂(ν.prod μ) ≤ lam⁻¹ ^ k * c ^ (k + 1) := by
        rw [← hKm]; exact mul_le_mul_of_nonneg_left hK (by positivity)
      have h2 : lam⁻¹ ^ k * c ^ (k + 1) = (Y ^ 2) ^ k * c := by
        rw [hinv, div_pow, pow_succ]; field_simp; ring
      have h3 : (Y ^ 2) ^ k ≤ a ^ k + c ^ k := by
        have : Y ^ 2 = max a c := by
          rw [hYdef]
          rcases le_total X K with hxk | hxk
          · rw [max_eq_right hxk, max_eq_right (pow_le_pow_left₀ hX0 hxk 2)]
          · rw [max_eq_left hxk, max_eq_left (pow_le_pow_left₀ hK0 hxk 2)]
        rw [this]; exact cph_max_pow_le ha hc.le k
      calc _ ≤ (Y ^ 2) ^ k * c := h1.trans h2.le
        _ ≤ (a ^ k + c ^ k) * c := mul_le_mul_of_nonneg_right h3 hc.le
        _ = a ^ k * c + c ^ (k + 1) := by ring
    have hfin := cph_final_ineq (m := k + 1) (by omega) ha hc.le
    simp only [Nat.add_sub_cancel] at hfin
    have hX' : ∫ y, s y ^ (2 * (k + 1)) ∂μ ≤ a ^ (k + 1) := by rw [← hXm]; exact hX
    have hK' : ∫ z, d z ^ (2 * (k + 1)) ∂(ν.prod μ) ≤ c ^ (k + 1) := by rw [← hKm]; exact hK
    nlinarith

end Step

/-!
## 4. The path phase and its growth
-/

section Path

/-- Borel version of `Ψ_r = N_r(E) + Θ_{z_∂}(X_r)`. -/
def cphPsiM (b E : ℝ) {W r : ℕ} (ω : PathSample W r) : ℝ :=
  (pathCount E ω : ℝ) + cphPhase (boundaryZ b E) (pathSchur E ω)

theorem cph_measurable_pathCount (E : ℝ) (W r : ℕ) :
    Measurable (fun ω : PathSample W r => (pathCount E ω : ℝ)) := by
  unfold pathCount
  exact cph_measurable_negativeCount.comp ((measurable_pathMatrix W r).sub measurable_const)

theorem cph_measurable_psiM (b E : ℝ) (W r : ℕ) :
    Measurable (cphPsiM b E (W := W) (r := r)) :=
  (cph_measurable_pathCount E W r).add ((cph_measurable_phase _).comp (measurable_pathSchur W r E))

theorem cph_ae_pathBlocks (W r : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂pathLaw W r b, ∀ j, (ω.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold pathLaw
  exact (Measure.quasiMeasurePreserving_fst).ae
    (ae_blocks_isHermitian r W (Real.toNNReal ((1 - 2 * b) / W)))

theorem cph_psi_eq {b E : ℝ} {W r : ℕ} {ω : PathSample W r} (hω : ∀ j, (ω.1 j).IsHermitian) :
    compensatedPhase b E ω = cphPsiM b E ω := by
  unfold compensatedPhase cphPsiM
  rw [cph_phaseCount_eq (srec_pathSchur_isHermitian E ω hω)]

theorem cph_psi_ae_eq (b E : ℝ) (W r : ℕ) :
    (compensatedPhase b E : PathSample W r → ℝ) =ᵐ[pathLaw W r b] cphPsiM b E := by
  filter_upwards [cph_ae_pathBlocks W r b] with ω hω
  exact cph_psi_eq hω

theorem cph_abs_psiM_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W r : ℕ} (ω : PathSample W r) :
    |cphPsiM b E ω| ≤ (r + 2) * W := by
  unfold cphPsiM pathCount
  have h1 := cph_negativeCount_le (pathMatrix ω - (E : ℂ) • 1)
  have h2 := cph_abs_phase_le hz (pathSchur E ω)
  simp only [Fintype.card_prod, Fintype.card_fin] at h1 h2
  have h1' : (negativeCount (pathMatrix ω - (E : ℂ) • 1) : ℝ) ≤ r * W := by exact_mod_cast h1
  have h0 : (0 : ℝ) ≤ (negativeCount (pathMatrix ω - (E : ℂ) • 1) : ℝ) := Nat.cast_nonneg _
  push_cast at h2
  rw [abs_le] at h2 ⊢
  constructor <;> nlinarith

theorem cph_isHermitian_sub {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (E : ℝ) : (H - (E : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
  refine hH.sub ?_
  unfold IsHermitian
  rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]

/-- **The growth identity** (Schur inertia and the two-ended Schur composition): for Hermitian
blocks and invertible `H_path - E`, `A - E - X_r`,
`Ψ_{r+2}(grown) = Ψ_r + N_-(A - E - X_r) + Θ_{z_∂}(X_{r+2}) - Θ_{z_∂}(X_r)`. -/
theorem cph_psi_pgGrow {W r : ℕ} (hr : 1 ≤ r) (b E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) (hℓ : ∀ j, (ℓ.1 j).IsHermitian) (hω : ∀ j, (ω.1 j).IsHermitian)
    (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det) :
    compensatedPhase b E (pgGrow (ℓ, ω)) =
      compensatedPhase b E ω + cphSepIncrement b E (pathSchur E ω) ℓ := by
  have hG : ∀ j, ((pgGrow (ℓ, ω)).1 j).IsHermitian := by
    intro j
    change (Sum.elim ℓ.1 ω.1 (pgPos r j)).IsHermitian
    rcases pgPos r j with u | u
    · exact hℓ u
    · exact hω u
  have hHG := cph_isHermitian_sub (srec_pathMatrix_isHermitian _ hG) E
  have hsub := hHG.submatrix (pgSite W r)
  rw [pgGrow_pathMatrix_sub hr E ℓ ω] at hsub
  have hM : (Matrix.fromBlocks (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1)
      (pathPortCoupling ω)ᴴ (pathPortCoupling ω)ᴴᴴ (pathMatrix ω - (E : ℂ) • 1)).IsHermitian := by
    rw [conjTranspose_conjTranspose]; exact hsub
  have key := negativeCount_fromBlocks_schur22 hM hH.ne_zero
  rw [conjTranspose_conjTranspose] at key
  have hN : pathCount E (pgGrow (ℓ, ω)) = pathCount E ω +
      negativeCount (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω) := by
    unfold pathCount
    rw [← cph_negativeCount_submatrix (pgSite W r) hHG, pgGrow_pathMatrix_sub hr E ℓ ω, key]
    rfl
  unfold compensatedPhase cphSepIncrement
  rw [hN, pathSchur_pgGrow hr E ℓ ω hH hS]
  push_cast
  ring

/-- The almost-sure hypotheses of `cph_psi_pgGrow` under `layerLaw ⊗ pathLaw r`. -/
theorem cph_ae_grow {W r : ℕ} (hr : 1 ≤ r) {b : ℝ} (hb : b < 1 / 2) (E : ℝ) :
    ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b),
      (∀ j, (x.1.1 j).IsHermitian) ∧ (∀ j, (x.2.1 j).IsHermitian) ∧
        IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det ∧
        IsUnit (Internal.Contracts.Layers.blockDiag x.1.1 - (E : ℂ) • 1 - pathSchur E x.2).det := by
  have h1 : ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b), ∀ j, (x.1.1 j).IsHermitian :=
    (Measure.quasiMeasurePreserving_fst).ae (lct_ae_blocks_isHermitian W b .separate)
  have h2 : ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b), ∀ j, (x.2.1 j).IsHermitian :=
    (Measure.quasiMeasurePreserving_snd).ae (cph_ae_pathBlocks W r b)
  have h3 : ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b),
      IsUnit (pathMatrix x.2 - (E : ℂ) • 1).det :=
    (Measure.quasiMeasurePreserving_snd).ae (ae_isUnit_det_pathMatrix W r hb E)
  have h4 : ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b),
      IsUnit (pathMatrix (pgGrow x) - (E : ℂ) • 1).det :=
    (measurePreserving_pgGrow b hr).quasiMeasurePreserving.ae
      (ae_isUnit_det_pathMatrix W (r + 2) hb E)
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  exact ⟨hx1, hx2, hx3, (isUnit_det_pgGrow_iff hr E x.1 x.2 hx3).mp hx4⟩

/-- The Borel growth identity, almost surely under `layerLaw ⊗ pathLaw r`. -/
theorem cph_ae_psiM_pgGrow {W r : ℕ} (hr : 1 ≤ r) {b : ℝ} (hb : b < 1 / 2) (E : ℝ) :
    ∀ᵐ x ∂(layerLaw W b .separate).prod (pathLaw W r b),
      cphPsiM b E (pgGrow x) = cphPsiM b E x.2 + cphSepIncrementM b E (pathSchur E x.2) x.1 := by
  filter_upwards [cph_ae_grow hr hb E] with x ⟨hx1, hx2, hx3, hx4⟩
  have hG : ∀ j, ((pgGrow x).1 j).IsHermitian := by
    intro j
    change (Sum.elim x.1.1 x.2.1 (pgPos r j)).IsHermitian
    rcases pgPos r j with u | u
    · exact hx1 u
    · exact hx2 u
  have h := cph_psi_pgGrow hr b E x.1 x.2 hx1 hx2 hx3 hx4
  rw [← cph_psi_eq hG, ← cph_psi_eq hx2,
    ← cph_sepIncrement_eq b E (srec_pathSchur_isHermitian E x.2 hx2) hx1]
  exact h

end Path

/-!
## 5. Moment helpers on a probability space
-/

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem cph_two_m_pos {m : ℕ} (hm : 1 ≤ m) : (0 : ℝ) < 2 * m := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem cph_one_le_two_m {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (m : ℝ)) := by
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)

omit [IsProbabilityMeasure μ] in
theorem cph_memLp_of_ae_bound [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ :=
  MemLp.of_bound hf B (hB.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)

/-- `‖d²‖_{2m} ≤ B²` from `‖d‖_{4m} ≤ B`. -/
theorem cph_eLpNorm_sq_le {d : Ω → ℝ} (hd : Measurable d) {Bd : ℝ} (hdb : ∀ᵐ x ∂μ, |d x| ≤ Bd)
    {m : ℕ} (hm : 1 ≤ m) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm d (ENNReal.ofReal (2 * ((2 * m : ℕ) : ℝ))) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => d x ^ 2) (ENNReal.ofReal (2 * (m : ℝ))) μ ≤ ENNReal.ofReal (B ^ 2) := by
  have h1 := cph_integral_le_of_eLpNorm (m := 2 * m) (by omega)
    (cph_memLp_of_ae_bound hd.aestronglyMeasurable hdb _) hB h
  refine cph_eLpNorm_le_of_integral hm
    (cph_memLp_of_ae_bound (hd.pow_const 2).aestronglyMeasurable
      (hdb.mono fun x hx => cph_abs_pow_le hx 2) _)
    (sq_nonneg B) ?_
  simp_rw [← pow_mul]
  exact h1

/-- `‖C(W d² + W⁻¹)‖_{2m} ≤ C(W B² + W⁻¹)` from `‖d‖_{4m} ≤ B`. -/
theorem cph_eLpNorm_err_le {d : Ω → ℝ} (hd : Measurable d) {Bd : ℝ} (hdb : ∀ᵐ x ∂μ, |d x| ≤ Bd)
    {m : ℕ} (hm : 1 ≤ m) {B C V : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hV : 0 < V)
    (h : eLpNorm d (ENNReal.ofReal (2 * ((2 * m : ℕ) : ℝ))) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => C * (V * d x ^ 2 + V⁻¹)) (ENNReal.ofReal (2 * (m : ℝ))) μ ≤
      ENNReal.ofReal (C * (V * B ^ 2 + V⁻¹)) := by
  have hsq := cph_eLpNorm_sq_le hd hdb hm hB h
  have hp := cph_two_m_pos hm
  have heq : (fun x => C * (V * d x ^ 2 + V⁻¹)) =
      (C * V) • (fun x => d x ^ 2) + (fun _ => C * V⁻¹) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [heq]
  calc eLpNorm ((C * V) • (fun x => d x ^ 2) + (fun _ => C * V⁻¹)) (ENNReal.ofReal (2 * (m : ℝ))) μ
      ≤ eLpNorm ((C * V) • (fun x => d x ^ 2)) (ENNReal.ofReal (2 * (m : ℝ))) μ +
          eLpNorm (fun _ : Ω => C * V⁻¹) (ENNReal.ofReal (2 * (m : ℝ))) μ :=
        eLpNorm_add_le (cph_one_le_two_m hm)
    _ ≤ ENNReal.ofReal (C * V) * ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (C * V⁻¹) := by
        rw [eLpNorm_const_smul, cph_eLpNorm_const _ hp, Real.enorm_of_nonneg (by positivity),
          abs_of_nonneg (by positivity)]
        gcongr
    _ = ENNReal.ofReal (C * (V * B ^ 2 + V⁻¹)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1; ring

omit [IsProbabilityMeasure μ] in
/-- `|E g| ≤ ∫ h` for `|g| ≤ h`. -/
theorem cph_abs_integral_le_integral {g h : Ω → ℝ} (hh : Integrable h μ)
    (hg : ∀ᵐ x ∂μ, |g x| ≤ h x) : |∫ x, g x ∂μ| ≤ ∫ x, h x ∂μ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hh (hg.mono fun x hx => by rwa [Real.norm_eq_abs])

end Helpers

/-!
## 6. The isolated inputs
-/

/-- **Isolated input** (in the paper: "The conditionally centered increments have
bounded fixed `L^p` norms"): uniformly in `W ≥ 1`, Hermitian `X` and `E ∈ I`, the fresh-layer
increment minus its conditional mean has `L^p(layerLaw)` norm at most `K_p`, for the
separate-port and the common-port layer. -/
structure CphIncrementFluctuation : Prop where
  separate : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ℓ => cphSepIncrement b E X ℓ -
          ∫ ℓ', cphSepIncrement b E X ℓ' ∂layerLaw W b .separate)
        (ENNReal.ofReal p) (layerLaw W b .separate) ≤ ENNReal.ofReal K
  common : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p → ∃ K : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
    ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ℓ => cphComIncrement b E X ℓ -
          ∫ ℓ', cphComIncrement b E X ℓ' ∂layerLaw W b .common)
        (ENNReal.ofReal p) (layerLaw W b .common) ≤ ENNReal.ofReal K

/-- **Isolated input** ("It remains to fix the starting constant"):
`CompensatedPhaseContract` for the two cores `r₀ ∈ {1, 2}` (there `(r₀+1)` is bounded). -/
structure CphCore : Prop where
  fluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W r₀ b)
          (ENNReal.ofReal p) (pathLaw W r₀ b) ≤ ENNReal.ofReal C
  mean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∃ C : ℝ,
    ∀ (W : ℕ), 0 < W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ E ∈ bulkInterval κ,
      |(∫ ω, compensatedPhase b E ω ∂pathLaw W r₀ b) - r₀ * W * semicircleCDF E -
          W * (2 * phaseEll E + b * phaseH E)| ≤ C / W

/-!
## 7. The conditional mean of the Borel increment
-/

section Mean

/-- `E[Δ | X]` for the Borel separate-port increment. -/
def cphSepMean (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  ∫ ℓ, cphSepIncrementM b E X ℓ ∂layerLaw W b .separate

theorem cph_measurable_sepMean (b E : ℝ) (W : ℕ) :
    Measurable (fun X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => cphSepMean b E X) := by
  have hF : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .separate => cphSepIncrementM b E q.1 q.2) :=
    cph_measurable_sepIncrementM b E measurable_fst measurable_snd
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

theorem cph_abs_sepMean_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : |cphSepMean b E X| ≤ 6 * W :=
  cph_abs_integral_le fun ℓ => cph_abs_sepIncrementM_le hz X ℓ

theorem cph_sepIncrement_ae_eq (b E : ℝ) {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) :
    (cphSepIncrement b E X) =ᵐ[layerLaw W b .separate] cphSepIncrementM b E X := by
  filter_upwards [lct_ae_blocks_isHermitian W b .separate] with ℓ hℓ
  exact cph_sepIncrement_eq b E hX hℓ

/-- For Hermitian `X`, the Borel conditional mean is the contract's
`E[N_- + Θ_{z_∂}(X₊)] - Θ_{z_∂}(X)`. -/
theorem cph_sepMean_eq {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ)
    {W : ℕ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    cphSepMean b E X = (∫ ω, ((negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) ∂layerLaw W b .separate) -
      phaseCount (boundaryZ b E) X := by
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  unfold cphSepMean
  rw [← integral_congr_ae (cph_sepIncrement_ae_eq b E hX)]
  unfold cphSepIncrement
  have hmeas : AEStronglyMeasurable (fun ω : LayerSample W .separate =>
      (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) (layerLaw W b .separate) := by
    have hm : Measurable (fun ω : LayerSample W .separate =>
        cphRawSum cphNegInd (blockDiag ω.1 - (E : ℂ) • 1 - X) +
          cphPhase (boundaryZ b E) (layerSchur .separate E X ω)) :=
      ((cph_measurable_rawSum cph_measurable_negInd).comp
        (cph_measurable_top E measurable_const measurable_fst)).add
        ((cph_measurable_phase _).comp (srec_measurable_layerSchur E measurable_const measurable_id))
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [lct_ae_blocks_isHermitian W b .separate] with ℓ hℓ
    rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq (srec_layerSchur_isHermitian E hX ℓ hℓ)]
  have hint : Integrable (fun ω : LayerSample W .separate =>
      (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X) : ℝ) +
        phaseCount (boundaryZ b E) (layerSchur .separate E X ω)) (layerLaw W b .separate) := by
    refine cph_integrable_of_bound hmeas (B := 2 * W + 2 * W) fun ω => ?_
    have h1 := cph_negativeCount_le_two (blockDiag ω.1 - (E : ℂ) • 1 - X)
    have h2 := cph_abs_phaseCount_le hz (layerSchur .separate E X ω)
    simp only [Fintype.card_prod, Fintype.card_fin] at h2
    push_cast at h2
    have h0 := Nat.cast_nonneg (α := ℝ) (negativeCount (blockDiag ω.1 - (E : ℂ) • 1 - X))
    rw [abs_le] at h2 ⊢
    constructor <;> linarith
  rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]

/-- The separate-port mean bound in Borel form, with a nonnegative constant. -/
theorem cph_sepMean_bound (hinc : CompensatedIncrementContract) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        |cphSepMean b E X - 2 * W * semicircleCDF E| ≤
          C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹) := by
  obtain ⟨C, hC⟩ := hinc.separate b hb0 hb1 κ hκ
  refine ⟨max C 0, le_max_right _ _, fun W hW X hX E hE => ?_⟩
  rw [cph_sepMean_eq hb1 hκ hE hX]
  refine (hC W hW X hX E hE).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  positivity

end Mean

/-!
## 8. One growth step: mean and centered moments
-/

section Recursion

/-- The centered Borel phase `Ψ_r - EΨ_r`. -/
def cphS (b E : ℝ) (W r : ℕ) (ω : PathSample W r) : ℝ :=
  cphPsiM b E ω - ∫ ω', cphPsiM b E ω' ∂pathLaw W r b

/-- The centered predictable term `E[Δ | X_r] - E[Δ]`. -/
def cphE (b E : ℝ) (W r : ℕ) (ω : PathSample W r) : ℝ :=
  cphSepMean b E (pathSchur E ω) - ∫ ω', cphSepMean b E (pathSchur E ω') ∂pathLaw W r b

/-- The conditionally centered increment `Δ - E[Δ | X_r]`. -/
def cphDev (b E : ℝ) (W r : ℕ) (x : LayerSample W .separate × PathSample W r) : ℝ :=
  cphSepIncrementM b E (pathSchur E x.2) x.1 - cphSepMean b E (pathSchur E x.2)

theorem cph_measurable_S (b E : ℝ) (W r : ℕ) : Measurable (cphS b E W r) :=
  (cph_measurable_psiM b E W r).sub_const _

theorem cph_measurable_E (b E : ℝ) (W r : ℕ) : Measurable (cphE b E W r) :=
  ((cph_measurable_sepMean b E W).comp (measurable_pathSchur W r E)).sub_const _

theorem cph_measurable_dev (b E : ℝ) (W r : ℕ) : Measurable (cphDev b E W r) :=
  (cph_measurable_sepIncrementM b E ((measurable_pathSchur W r E).comp measurable_snd)
    measurable_fst).sub ((cph_measurable_sepMean b E W).comp
      ((measurable_pathSchur W r E).comp measurable_snd))

theorem cph_abs_S_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W r : ℕ} (ω : PathSample W r) :
    |cphS b E W r ω| ≤ 2 * ((r + 2) * W) := by
  have h1 := cph_abs_psiM_le hz ω
  have h2 : |∫ ω', cphPsiM b E ω' ∂pathLaw W r b| ≤ (r + 2) * W :=
    cph_abs_integral_le fun ω' => cph_abs_psiM_le hz ω'
  unfold cphS
  exact (abs_sub _ _).trans (by linarith)

theorem cph_abs_E_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W r : ℕ} (ω : PathSample W r) :
    |cphE b E W r ω| ≤ 12 * W := by
  have h1 := cph_abs_sepMean_le hz (W := W) (pathSchur E ω)
  have h2 : |∫ ω', cphSepMean b E (pathSchur E ω') ∂pathLaw W r b| ≤ 6 * W :=
    cph_abs_integral_le fun ω' => cph_abs_sepMean_le hz _
  unfold cphE
  exact (abs_sub _ _).trans (by linarith)

theorem cph_abs_dev_le {b E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {W r : ℕ}
    (x : LayerSample W .separate × PathSample W r) : |cphDev b E W r x| ≤ 12 * W := by
  have h1 := cph_abs_sepIncrementM_le hz (pathSchur E x.2) x.1
  have h2 := cph_abs_sepMean_le hz (W := W) (pathSchur E x.2)
  unfold cphDev
  exact (abs_sub _ _).trans (by linarith)

theorem cph_integral_dev (b E : ℝ) (hz : 0 ≤ (boundaryZ b E).im) {W r : ℕ}
    (ω : PathSample W r) : ∫ ℓ, cphDev b E W r (ℓ, ω) ∂layerLaw W b .separate = 0 := by
  have e : (fun ℓ => cphDev b E W r (ℓ, ω)) = fun ℓ =>
      cphSepIncrementM b E (pathSchur E ω) ℓ - cphSepMean b E (pathSchur E ω) := rfl
  rw [e]
  unfold cphSepMean
  have hi : Integrable (fun ℓ => cphSepIncrementM b E (pathSchur E ω) ℓ)
      (layerLaw W b .separate) :=
    cph_integrable_of_bound (cph_measurable_sepIncrementM b E measurable_const
      measurable_id).aestronglyMeasurable fun ℓ => cph_abs_sepIncrementM_le hz _ ℓ
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-- **Mean step**: `EΨ_{r+2} = EΨ_r + E[E(Δ | X_r)]`. -/
theorem cph_mean_step {W r : ℕ} (hr : 1 ≤ r) {b : ℝ} (hb : b < 1 / 2) {E : ℝ}
    (hz : 0 ≤ (boundaryZ b E).im) :
    ∫ ω, cphPsiM b E ω ∂pathLaw W (r + 2) b = ∫ ω, cphPsiM b E ω ∂pathLaw W r b +
      ∫ ω, cphSepMean b E (pathSchur E ω) ∂pathLaw W r b := by
  rw [← map_pgGrow_pathLaw b hr, integral_map (measurePreserving_pgGrow b hr).measurable.aemeasurable
    (cph_measurable_psiM b E W (r + 2)).aestronglyMeasurable,
    integral_congr_ae (cph_ae_psiM_pgGrow hr hb E)]
  have hi1 : Integrable (fun x : LayerSample W .separate × PathSample W r => cphPsiM b E x.2)
      ((layerLaw W b .separate).prod (pathLaw W r b)) :=
    cph_integrable_of_bound ((cph_measurable_psiM b E W r).comp measurable_snd).aestronglyMeasurable
      fun x => cph_abs_psiM_le hz x.2
  have hi2 : Integrable (fun x : LayerSample W .separate × PathSample W r =>
      cphSepIncrementM b E (pathSchur E x.2) x.1) ((layerLaw W b .separate).prod (pathLaw W r b)) :=
    cph_integrable_of_bound (cph_measurable_sepIncrementM b E
      ((measurable_pathSchur W r E).comp measurable_snd) measurable_fst).aestronglyMeasurable
      fun x => cph_abs_sepIncrementM_le hz _ _
  rw [integral_add hi1 hi2, cph_integral_comp_snd (cph_measurable_psiM b E W r),
    integral_prod_symm _ hi2]
  rfl

/-- **Moment step**: `‖S_{r+2}‖_{2m} ≤ √((‖S_r‖_{2m} + ‖E_r‖_{2m})² + 4^{m+1} K²)`, where `K`
bounds the conditional `L^{2m}` norms of the centered increment. -/
theorem cph_fluct_step {m : ℕ} (hm : 1 ≤ m) {W r : ℕ} (hr : 1 ≤ r) {b : ℝ} (hb : b < 1 / 2)
    {E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {x ε K : ℝ} (hx : 0 ≤ x) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hS : eLpNorm (cphS b E W r) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) ≤ ENNReal.ofReal x)
    (hE : eLpNorm (cphE b E W r) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) ≤ ENNReal.ofReal ε)
    (hD : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      eLpNorm (fun ℓ => cphSepIncrementM b E X ℓ - cphSepMean b E X)
        (ENNReal.ofReal (2 * (m : ℝ))) (layerLaw W b .separate) ≤ ENNReal.ofReal K) :
    eLpNorm (cphS b E W (r + 2)) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W (r + 2) b) ≤
      ENNReal.ofReal (Real.sqrt ((x + ε) ^ 2 + 4 ^ (m + 1) * K ^ 2)) := by
  have hmean := cph_mean_step hr hb hz (W := W)
  set P := (layerLaw W b .separate).prod (pathLaw W r b)
  have hae : (cphS b E W (r + 2)) ∘ pgGrow =ᵐ[P]
      fun z => (cphS b E W r z.2 + cphE b E W r z.2) + cphDev b E W r z := by
    filter_upwards [cph_ae_psiM_pgGrow hr hb E] with z hz'
    simp only [Function.comp, cphS, cphE, cphDev, hz', hmean]
    ring
  rw [← eLpNorm_comp_measurePreserving (cph_measurable_S b E W (r + 2)).aestronglyMeasurable
    (measurePreserving_pgGrow b hr), eLpNorm_congr_ae hae]
  have hsm : Measurable (fun ω => cphS b E W r ω + cphE b E W r ω) :=
    (cph_measurable_S b E W r).add (cph_measurable_E b E W r)
  have hsb : ∀ ω : PathSample W r, |cphS b E W r ω + cphE b E W r ω| ≤
      2 * ((r + 2) * W) + 12 * W := fun ω =>
    (abs_add_le _ _).trans (add_le_add (cph_abs_S_le hz ω) (cph_abs_E_le hz ω))
  have hs_norm : eLpNorm (fun ω => cphS b E W r ω + cphE b E W r ω)
      (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) ≤ ENNReal.ofReal (x + ε) := by
    refine (eLpNorm_add_le (f := cphS b E W r) (g := cphE b E W r) (cph_one_le_two_m hm)).trans ?_
    rw [ENNReal.ofReal_add hx hε]
    exact add_le_add hS hE
  have hs_int := cph_integral_le_of_eLpNorm hm (cph_memLp_of_bound hsm.aestronglyMeasurable hsb _)
    (add_nonneg hx hε) hs_norm
  have hdev_norm : eLpNorm (cphDev b E W r) (ENNReal.ofReal (2 * (m : ℝ))) P ≤ ENNReal.ofReal K := by
    refine srec_eLpNorm_prod_le (cph_measurable_dev b E W r) (cph_two_m_pos hm) ?_
    filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with ω hω
    have e : (fun ℓ => cphDev b E W r (ℓ, ω)) = fun ℓ =>
        cphSepIncrementM b E (pathSchur E ω) ℓ - cphSepMean b E (pathSchur E ω) := rfl
    rw [e]
    exact hD _ hω
  have hdev_int := cph_integral_le_of_eLpNorm hm (cph_memLp_of_bound
    (cph_measurable_dev b E W r).aestronglyMeasurable (cph_abs_dev_le hz) _) hK hdev_norm
  have hstep := cph_moment_step (ν := layerLaw W b .separate) (μ := pathLaw W r b) hm hsm
    (cph_measurable_dev b E W r) hsb (cph_abs_dev_le hz) (cph_integral_dev b E hz)
    (add_nonneg hx hε) hK hs_int hdev_int
  refine cph_eLpNorm_le_of_integral hm (cph_memLp_of_bound
    ((hsm.comp measurable_snd).add (cph_measurable_dev b E W r)).aestronglyMeasurable
    (B := 2 * ((r + 2) * W) + 12 * W + 12 * W)
    (fun z => (abs_add_le _ _).trans (add_le_add (hsb z.2) (cph_abs_dev_le hz z))) _)
    (Real.sqrt_nonneg _) ?_
  rw [pow_mul, Real.sq_sqrt (by positivity)]
  exact hstep

end Recursion

/-!
## 9. Iteration along the growth
-/

section Iteration

/-- **Iterated moment bound** (the martingale moment inequality with predictable errors):
`‖S_{r₀+2L}‖_{2m} ≤ √(x₀² + L·4^{m+1}K²) + Lε`. -/
theorem cph_fluct_iter {m : ℕ} (hm : 1 ≤ m) {W r₀ : ℕ} (hr₀ : 1 ≤ r₀) {b : ℝ} (hb : b < 1 / 2)
    {E : ℝ} (hz : 0 ≤ (boundaryZ b E).im) {x₀ ε K : ℝ} (hx₀ : 0 ≤ x₀) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hD : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      eLpNorm (fun ℓ => cphSepIncrementM b E X ℓ - cphSepMean b E X)
        (ENNReal.ofReal (2 * (m : ℝ))) (layerLaw W b .separate) ≤ ENNReal.ofReal K)
    (h0 : eLpNorm (cphS b E W r₀) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r₀ b) ≤
      ENNReal.ofReal x₀) :
    ∀ L : ℕ, (∀ j < L, eLpNorm (cphE b E W (r₀ + 2 * j)) (ENNReal.ofReal (2 * (m : ℝ)))
        (pathLaw W (r₀ + 2 * j) b) ≤ ENNReal.ofReal ε) →
      eLpNorm (cphS b E W (r₀ + 2 * L)) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W (r₀ + 2 * L) b) ≤
        ENNReal.ofReal (Real.sqrt (x₀ ^ 2 + L * (4 ^ (m + 1) * K ^ 2)) + L * ε) := by
  intro L
  induction L with
  | zero =>
    intro _
    simpa [Real.sqrt_sq hx₀] using h0
  | succ L ih =>
    intro hE
    have hL := ih fun j hj => hE j (by omega)
    have hc : 0 ≤ 4 ^ (m + 1) * K ^ 2 := by positivity
    have ha : 0 ≤ Real.sqrt (x₀ ^ 2 + L * (4 ^ (m + 1) * K ^ 2)) := Real.sqrt_nonneg _
    have hstep := cph_fluct_step hm (r := r₀ + 2 * L) (by omega) hb hz
      (add_nonneg ha (mul_nonneg (Nat.cast_nonneg L) hε)) hε hK hL (hE L (by omega)) hD
    rw [show r₀ + 2 * (L + 1) = r₀ + 2 * L + 2 by ring]
    refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsh := cph_sqrt_shift ha (mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) + 1) hε) hc
    rw [Real.sq_sqrt (by positivity)] at hsh
    push_cast
    calc Real.sqrt ((Real.sqrt (x₀ ^ 2 + L * (4 ^ (m + 1) * K ^ 2)) + L * ε + ε) ^ 2 +
          4 ^ (m + 1) * K ^ 2)
        = Real.sqrt ((Real.sqrt (x₀ ^ 2 + L * (4 ^ (m + 1) * K ^ 2)) + (L + 1) * ε) ^ 2 +
          4 ^ (m + 1) * K ^ 2) := by ring_nf
      _ ≤ Real.sqrt (x₀ ^ 2 + L * (4 ^ (m + 1) * K ^ 2) + 4 ^ (m + 1) * K ^ 2) + (L + 1) * ε := hsh
      _ = Real.sqrt (x₀ ^ 2 + (L + 1) * (4 ^ (m + 1) * K ^ 2)) + (L + 1) * ε := by ring_nf

/-- **Iterated mean**: `|EΨ_{r₀+2L} - EΨ_{r₀} - 2LW F_sc| ≤ Lδ` if each step's predictable
mean is within `δ` of `2W F_sc`. -/
theorem cph_mean_iter {W r₀ : ℕ} (hr₀ : 1 ≤ r₀) {b : ℝ} (hb : b < 1 / 2) {E : ℝ}
    (hz : 0 ≤ (boundaryZ b E).im) {δ : ℝ} :
    ∀ L : ℕ, (∀ j < L, |(∫ ω, cphSepMean b E (pathSchur E ω) ∂pathLaw W (r₀ + 2 * j) b) -
        2 * W * semicircleCDF E| ≤ δ) →
      |(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) - (∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) -
        2 * L * W * semicircleCDF E| ≤ L * δ := by
  intro L
  induction L with
  | zero => intro _; simp
  | succ L ih =>
    intro hE
    have hL := ih fun j hj => hE j (by omega)
    have hj := hE L (by omega)
    have hstep := cph_mean_step (W := W) (r := r₀ + 2 * L) (by omega) hb hz
    rw [show r₀ + 2 * (L + 1) = r₀ + 2 * L + 2 by ring, hstep]
    push_cast
    rw [abs_le] at hL hj ⊢
    constructor <;> nlinarith

end Iteration

/-!
## 10. The predictable errors from the matched traces
-/

section Errors

theorem cph_ae_matchedDistance_le {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (W r : ℕ) :
    ∀ᵐ ω ∂pathLaw W r b, |matchedDistance b E (pathSchur E ω)| ≤ ((boundaryZ b E).im)⁻¹ + 1 := by
  have hE2 : |E| ≤ 2 := (abs_le_of_mem_bulkInterval hE).trans (by linarith)
  have hz : 0 < (boundaryZ b E).im :=
    (boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ hE).1.trans_le
      (boundaryZ_im_pos_of_mem_bulkInterval (b := b) (by linarith) hκ hE).2
  filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with ω hω
  have h0 : 0 ≤ matchedDistance b E (pathSchur E ω) := le_max_of_le_left (norm_nonneg _)
  rw [abs_of_nonneg h0]
  exact srec_matchedDistance_le hE2 hz hω

/-- **Predictable errors** (general form): with `|F(X) - t| ≤ C(W d² + W⁻¹)` and
`‖d‖_2 ≤ B₂`, `‖d‖_{4m} ≤ B₄` under `pathLaw W r b`, the mean error is at most
`C(W B₂² + W⁻¹)` and the centered predictable term has `‖·‖_{2m} ≤ C(W B₄² + W⁻¹) + C(W B₂² + W⁻¹)`. -/
theorem cph_errors_gen {m : ℕ} (hm : 1 ≤ m) {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {W r : ℕ} (hW : 0 < W) {C B₂ B₄ : ℝ} (hC : 0 ≤ C) (hB₂ : 0 ≤ B₂)
    (hB₄ : 0 ≤ B₄) {F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → ℝ} (hFm : Measurable F)
    {BF t : ℝ} (hFb : ∀ X, |F X| ≤ BF)
    (hmean : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      |F X - t| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹))
    (h2 : eLpNorm (fun ω => matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal 2)
      (pathLaw W r b) ≤ ENNReal.ofReal B₂)
    (h4 : eLpNorm (fun ω => matchedDistance b E (pathSchur E ω))
      (ENNReal.ofReal (2 * ((2 * m : ℕ) : ℝ))) (pathLaw W r b) ≤ ENNReal.ofReal B₄) :
    |(∫ ω, F (pathSchur E ω) ∂pathLaw W r b) - t| ≤
        C * (W * B₂ ^ 2 + (W : ℝ)⁻¹) ∧
      eLpNorm (fun ω => F (pathSchur E ω) - ∫ ω', F (pathSchur E ω') ∂pathLaw W r b)
        (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) ≤
        ENNReal.ofReal (C * (W * B₄ ^ 2 + (W : ℝ)⁻¹) + C * (W * B₂ ^ 2 + (W : ℝ)⁻¹)) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  set d := fun ω : PathSample W r => matchedDistance b E (pathSchur E ω)
  have hdm : Measurable d := (srec_measurable_matchedDistance b E W).comp (measurable_pathSchur W r E)
  have hdb := cph_ae_matchedDistance_le hb hκ hE W r
  set g := fun ω : PathSample W r => F (pathSchur E ω) - t
  have hgm : Measurable g := (hFm.comp (measurable_pathSchur W r E)).sub_const _
  have hg : ∀ᵐ ω ∂pathLaw W r b, |g ω| ≤ C * (W * d ω ^ 2 + (W : ℝ)⁻¹) := by
    filter_upwards [srec_ae_pathSchur_isHermitian W r b E] with ω hω
    exact hmean _ hω
  -- the mean error
  have hd2 : ∫ ω, d ω ^ 2 ∂pathLaw W r b ≤ B₂ ^ 2 := by
    have := cph_integral_le_of_eLpNorm (m := 1) le_rfl
      (cph_memLp_of_ae_bound hdm.aestronglyMeasurable hdb _) hB₂
      (by rw [show (2 * ((1 : ℕ) : ℝ)) = 2 by norm_num]; exact h2)
    simpa using this
  have hdi : Integrable (fun ω => d ω ^ 2) (pathLaw W r b) :=
    cph_integrable_of_bound' (hdm.pow_const 2).aestronglyMeasurable
      (hdb.mono fun ω hω => cph_abs_pow_le hω 2)
  have hhi : Integrable (fun ω => C * (W * d ω ^ 2 + (W : ℝ)⁻¹)) (pathLaw W r b) :=
    ((hdi.const_mul _).add (integrable_const _)).const_mul _
  have hI : |∫ ω, g ω ∂pathLaw W r b| ≤ C * (W * B₂ ^ 2 + (W : ℝ)⁻¹) := by
    refine (cph_abs_integral_le_integral hhi hg).trans ?_
    rw [integral_const_mul, integral_add (hdi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    gcongr
  have hgi : ∫ ω, g ω ∂pathLaw W r b =
      (∫ ω, F (pathSchur E ω) ∂pathLaw W r b) - t := by
    have hi : Integrable (fun ω => F (pathSchur E ω)) (pathLaw W r b) :=
      cph_integrable_of_bound (hFm.comp (measurable_pathSchur W r E)).aestronglyMeasurable
        fun ω => hFb _
    simp only [g]
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  refine ⟨hgi ▸ hI, ?_⟩
  -- the centered predictable term
  have hEq : (fun ω => F (pathSchur E ω) - ∫ ω', F (pathSchur E ω') ∂pathLaw W r b) =
      fun ω => g ω - ∫ ω', g ω' ∂pathLaw W r b := by
    funext ω; simp only [g, hgi]; ring
  rw [hEq]
  have hp := cph_two_m_pos hm
  calc eLpNorm (fun ω => g ω - ∫ ω', g ω' ∂pathLaw W r b) (ENNReal.ofReal (2 * (m : ℝ)))
        (pathLaw W r b)
      ≤ eLpNorm g (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) +
          eLpNorm (fun _ : PathSample W r => -∫ ω', g ω' ∂pathLaw W r b)
            (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) := by
        have e : (fun ω => g ω - ∫ ω', g ω' ∂pathLaw W r b) =
            g + fun _ : PathSample W r => -∫ ω', g ω' ∂pathLaw W r b := by
          funext ω; simp only [Pi.add_apply]; ring
        rw [e]
        exact eLpNorm_add_le (cph_one_le_two_m hm)
    _ ≤ ENNReal.ofReal (C * (W * B₄ ^ 2 + (W : ℝ)⁻¹)) +
          ENNReal.ofReal (C * (W * B₂ ^ 2 + (W : ℝ)⁻¹)) := by
        rw [cph_eLpNorm_const _ hp, abs_neg]
        gcongr
        exact (eLpNorm_mono_ae_real hgm.aestronglyMeasurable
          (hg.mono fun ω hω => by rwa [Real.norm_eq_abs])).trans
          (cph_eLpNorm_err_le hdm hdb hm hB₄ hC hWr h4)
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- **Predictable errors** for the separate-port conditional mean `F = E[Δ | ·]`, `t = 2WF_sc`. -/
theorem cph_errors {m : ℕ} (hm : 1 ≤ m) {b κ E : ℝ} (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) {W r : ℕ} (hW : 0 < W) {C B₂ B₄ : ℝ} (hC : 0 ≤ C) (hB₂ : 0 ≤ B₂)
    (hB₄ : 0 ≤ B₄)
    (hmean : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      |cphSepMean b E X - 2 * W * semicircleCDF E| ≤
        C * (W * matchedDistance b E X ^ 2 + (W : ℝ)⁻¹))
    (h2 : eLpNorm (fun ω => matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal 2)
      (pathLaw W r b) ≤ ENNReal.ofReal B₂)
    (h4 : eLpNorm (fun ω => matchedDistance b E (pathSchur E ω))
      (ENNReal.ofReal (2 * ((2 * m : ℕ) : ℝ))) (pathLaw W r b) ≤ ENNReal.ofReal B₄) :
    |(∫ ω, cphSepMean b E (pathSchur E ω) ∂pathLaw W r b) - 2 * W * semicircleCDF E| ≤
        C * (W * B₂ ^ 2 + (W : ℝ)⁻¹) ∧
      eLpNorm (cphE b E W r) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) ≤
        ENNReal.ofReal (C * (W * B₄ ^ 2 + (W : ℝ)⁻¹) + C * (W * B₂ ^ 2 + (W : ℝ)⁻¹)) := by
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  exact cph_errors_gen hm hb hκ hE hW hC hB₂ hB₄ (cph_measurable_sepMean b E W)
    (fun X => cph_abs_sepMean_le hz X) hmean h2 h4

end Errors

/-!
## 11. `CompensatedPhaseContract`
-/

section Assembly

theorem cph_decomp (r : ℕ) (hr : 1 ≤ r) : ∃ r₀ L : ℕ, (r₀ = 1 ∨ r₀ = 2) ∧ r = r₀ + 2 * L := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' r
  · exact ⟨2, k - 1, Or.inr rfl, by omega⟩
  · exact ⟨1, k, Or.inl rfl, by omega⟩

/-- The path clause of the matched-traces theorem, phrased with `d(X_r)` and `C ≥ 0`. -/
theorem cph_path_d (hmt : MatchedTracesContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (T : ℝ) (hκ : 0 < κ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ p : ℝ, 2 ≤ p → p ≤ ε₀ * W →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => matchedDistance b E (pathSchur E ω)) (ENNReal.ofReal p)
          (pathLaw W r b) ≤ ENNReal.ofReal (C * Real.sqrt p / W) := by
  obtain ⟨ε₀, C, hε₀, h⟩ := hmt.path b hb0 hb1 κ T hκ
  refine ⟨ε₀, max C 0, hε₀, le_max_right _ _, fun W hW p hp2 hpW r hr1 hrT E hE =>
    (h W hW p hp2 hpW r hr1 hrT E hE).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  gcongr
  exact le_max_left _ _

theorem cph_sqrt_le_add {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    Real.sqrt (a ^ 2 + y ^ 2) ≤ a + y := by
  rw [Real.sqrt_le_left (by positivity)]; nlinarith

/-- The Borel conditional increment bound from `CphIncrementFluctuation.separate`. -/
theorem cph_dev_bound (hfl : CphIncrementFluctuation) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κ : ℝ} (hκ : 0 < κ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ℓ => cphSepIncrementM b E X ℓ - cphSepMean b E X) (ENNReal.ofReal p)
          (layerLaw W b .separate) ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK⟩ := hfl.separate b hb0 hb1 κ hκ p hp
  refine ⟨max K 0, le_max_right _ _, fun W hW X hX E hE => ?_⟩
  have hae := cph_sepIncrement_ae_eq b E hX (W := W)
  have hI : ∫ ℓ', cphSepIncrement b E X ℓ' ∂layerLaw W b .separate = cphSepMean b E X :=
    integral_congr_ae hae
  have h := hK W hW X hX E hE
  rw [hI] at h
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (h.trans (ENNReal.ofReal_le_ofReal
    (le_max_left _ _)))
  filter_upwards [hae] with ℓ hℓ
  rw [hℓ]

/-- The core fluctuation input in Borel form. -/
theorem cph_core_S {b E : ℝ} {W r₀ : ℕ} {p C : ℝ}
    (h : eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W r₀ b)
      (ENNReal.ofReal p) (pathLaw W r₀ b) ≤ ENNReal.ofReal C) :
    eLpNorm (cphS b E W r₀) (ENNReal.ofReal p) (pathLaw W r₀ b) ≤ ENNReal.ofReal (max C 0) := by
  have hae := cph_psi_ae_eq b E W r₀
  rw [integral_congr_ae hae] at h
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (h.trans (ENNReal.ofReal_le_ofReal
    (le_max_left _ _)))
  filter_upwards [hae] with ω hω
  simp only [cphS, hω]

/-- **The compensated-phase lemma, fluctuation clause**, from the matched traces, the separate-port
mean increments, the increment fluctuation input and the core input. -/
theorem cph_fluctuation (hmt : MatchedTracesContract) (hinc : CompensatedIncrementContract)
    (hfl : CphIncrementFluctuation) (hcore : CphCore) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ Cp : ℝ, ∀ (W : ℕ), 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      eLpNorm (fun ω => compensatedPhase b E ω - ∫ ω', compensatedPhase b E ω' ∂pathLaw W r b)
          (ENNReal.ofReal p) (pathLaw W r b) ≤
        ENNReal.ofReal (Cp * Real.sqrt (r + 1)) := by
  intro b hb0 hb1 κ T hκ p hp
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈p / 2⌉₊ := ⟨_, rfl⟩
  have hm : 1 ≤ m := by
    rw [hmdef]; exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  have hpm : p ≤ 2 * (m : ℝ) := by
    have := Nat.le_ceil (p / 2); rw [← hmdef] at this; linarith
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨ε₀, Cm, hε₀, hCm, hd⟩ := cph_path_d hmt hb0 hb1 T hκ
  obtain ⟨C, hC0, hC⟩ := cph_sepMean_bound hinc hb0 hb1 hκ
  obtain ⟨K, hK0, hK⟩ := cph_dev_bound hfl hb0 hb1 hκ (p := 2 * (m : ℝ)) (by linarith)
  obtain ⟨Cc, hCc⟩ := hcore.fluctuation b hb0 hb1 κ hκ (2 * (m : ℝ)) (by linarith)
  set T' := max T 0
  set x₀ := max Cc 0
  set W₁ : ℝ := 4 * m / ε₀
  set A := C * (4 * m * Cm ^ 2 + 1) + C * (2 * Cm ^ 2 + 1)
  set c : ℝ := 4 ^ (m + 1)
  have hT' : 0 ≤ T' := le_max_right _ _
  have hx₀ : 0 ≤ x₀ := le_max_right _ _
  have hW₁ : 0 ≤ W₁ := by positivity
  have hA : 0 ≤ A := by positivity
  have hc : 0 ≤ c := by positivity
  refine ⟨2 * (T' * W₁ + 2) * W₁ + (x₀ + Real.sqrt c * K + T' * A),
    fun W hW r hr1 hrT E hE => ?_⟩
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hsq : 1 ≤ Real.sqrt (r + 1) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ r + 1 by linarith); rwa [Real.sqrt_one] at this
  have hrT' : (r : ℝ) ≤ T' * W := hrT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWr.le)
  have hC1 : 0 ≤ 2 * (T' * W₁ + 2) * W₁ := by positivity
  have hC2 : 0 ≤ x₀ + Real.sqrt c * K + T' * A := by positivity
  -- reduce to the Borel centered phase at the even exponent `2m`
  have hconv : eLpNorm (fun ω => compensatedPhase b E ω -
      ∫ ω', compensatedPhase b E ω' ∂pathLaw W r b) (ENNReal.ofReal p) (pathLaw W r b) ≤
      eLpNorm (cphS b E W r) (ENNReal.ofReal (2 * (m : ℝ))) (pathLaw W r b) := by
    have hae := cph_psi_ae_eq b E W r
    rw [integral_congr_ae hae]
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_))
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpm))
    filter_upwards [hae] with ω hω
    simp only [cphS, hω]
  refine hconv.trans ?_
  by_cases hWs : (W : ℝ) < W₁
  · -- small `W`: the crude bound `|S_r| ≤ 2(r+2)W`
    have hcr := eLpNorm_le_of_ae_bound (p := ENNReal.ofReal (2 * (m : ℝ))) (μ := pathLaw W r b)
      (cph_measurable_S b E W r).aestronglyMeasurable (C := 2 * ((r + 2) * W))
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact cph_abs_S_le hz ω)
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hcr
    refine hcr.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (r + 2 : ℝ) * W ≤ (T' * W₁ + 2) * W₁ := by
      have : (r : ℝ) ≤ T' * W₁ := hrT'.trans (mul_le_mul_of_nonneg_left hWs.le hT')
      exact mul_le_mul (by linarith) hWs.le hWr.le (by positivity)
    calc 2 * ((r + 2 : ℝ) * W) ≤ 2 * (T' * W₁ + 2) * W₁ := by linarith
      _ ≤ 2 * (T' * W₁ + 2) * W₁ + (x₀ + Real.sqrt c * K + T' * A) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hsq
  · -- large `W`: `4m ≤ ε₀ W`
    have hW₁ : 4 * (m : ℝ) ≤ ε₀ * W := by
      have : W₁ ≤ W := le_of_not_gt hWs
      rw [div_le_iff₀ hε₀] at this; linarith
    obtain ⟨r₀, L, hr₀, rfl⟩ := cph_decomp r hr1
    have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
    have hD := fun X hX => hK W hW X hX E hE
    have h0 := cph_core_S (hCc W hW r₀ hr₀ E hE)
    have hEj : ∀ j < L, eLpNorm (cphE b E W (r₀ + 2 * j)) (ENNReal.ofReal (2 * (m : ℝ)))
        (pathLaw W (r₀ + 2 * j) b) ≤ ENNReal.ofReal (A / W) := by
      intro j hj
      have hrj : ((r₀ + 2 * j : ℕ) : ℝ) ≤ T * W := by
        refine le_trans ?_ hrT; exact_mod_cast (by omega : r₀ + 2 * j ≤ r₀ + 2 * L)
      have h2 := hd W hW 2 le_rfl (by linarith) (r₀ + 2 * j) (by omega) hrj E hE
      have h4 := hd W hW (2 * ((2 * m : ℕ) : ℝ)) (by push_cast; linarith)
        (by push_cast; linarith) (r₀ + 2 * j) (by omega) hrj E hE
      have herr := (cph_errors hm hb1 hκ hE hW hC0 (by positivity) (by positivity)
        (fun X hX => hC W hW X hX E hE) h2 h4).2
      refine herr.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      have hs4 : Real.sqrt (2 * ((2 * m : ℕ) : ℝ)) ^ 2 = 4 * m := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      simp only [A]
      rw [div_pow, mul_pow, hs4, div_pow, mul_pow, hs2]
      field_simp
    have hit := cph_fluct_iter hm hr₀1 hb1 hz hx₀ (by positivity) hK0 hD h0 L hEj
    refine hit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hL : (L : ℝ) ≤ r₀ + 2 * L + 1 := by linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
    have hLT : (L : ℝ) ≤ T' * W := by
      have : ((r₀ + 2 * L : ℕ) : ℝ) ≤ T' * W := hrT'
      push_cast at this; linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
    set R := Real.sqrt (((r₀ + 2 * L : ℕ) : ℝ) + 1)
    have hsL : Real.sqrt L ≤ R := Real.sqrt_le_sqrt (by push_cast; linarith)
    have hy : (Real.sqrt L * Real.sqrt c * K) ^ 2 = L * (c * K ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hc]; ring
    have h1 : Real.sqrt (x₀ ^ 2 + L * (c * K ^ 2)) ≤ x₀ + Real.sqrt L * Real.sqrt c * K := by
      rw [← hy]; exact cph_sqrt_le_add hx₀ (by positivity)
    have h2 : (L : ℝ) * (A / W) ≤ T' * A := by
      rw [mul_div_assoc', div_le_iff₀ hWr]; nlinarith
    have hR1 : 1 ≤ R := hsq
    have h3 : Real.sqrt L * Real.sqrt c * K ≤ Real.sqrt c * K * R := by
      have := mul_le_mul_of_nonneg_left hsL (by positivity : 0 ≤ Real.sqrt c * K)
      linarith
    have h4 : x₀ + Real.sqrt c * K * R + T' * A ≤ (x₀ + Real.sqrt c * K + T' * A) * R := by
      nlinarith [mul_nonneg hx₀ (by linarith : (0 : ℝ) ≤ R - 1),
        mul_nonneg (mul_nonneg hT' hA) (by linarith : (0 : ℝ) ≤ R - 1)]
    have h5 : (x₀ + Real.sqrt c * K + T' * A) * R ≤
        (2 * (T' * W₁ + 2) * W₁ + (x₀ + Real.sqrt c * K + T' * A)) * R := by
      have : 0 ≤ R := by linarith
      exact mul_le_mul_of_nonneg_right (by linarith) this
    calc _ ≤ x₀ + Real.sqrt L * Real.sqrt c * K + T' * A := add_le_add h1 h2
      _ ≤ x₀ + Real.sqrt c * K * R + T' * A := by linarith
      _ ≤ (x₀ + Real.sqrt c * K + T' * A) * R := h4
      _ ≤ _ := h5

/-- **The compensated-phase lemma, mean clause**, from the same inputs. -/
theorem cph_mean (hmt : MatchedTracesContract) (hinc : CompensatedIncrementContract)
    (hcore : CphCore) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ →
    ∃ C : ℝ, ∀ (W : ℕ), 0 < W → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
      |(∫ ω, compensatedPhase b E ω ∂pathLaw W r b) - r * W * semicircleCDF E -
          W * (2 * phaseEll E + b * phaseH E)| ≤ C * (r + 1) / W := by
  intro b hb0 hb1 κ T hκ
  obtain ⟨ε₀, Cm, hε₀, hCm, hd⟩ := cph_path_d hmt hb0 hb1 T hκ
  obtain ⟨C, hC0, hC⟩ := cph_sepMean_bound hinc hb0 hb1 hκ
  obtain ⟨Cco, hCco⟩ := hcore.mean b hb0 hb1 κ hκ
  set W₂ : ℝ := max (4 / ε₀) 1
  set x₀ := max Cco 0
  have hW₂ : 1 ≤ W₂ := le_max_right _ _
  have hx₀ : 0 ≤ x₀ := le_max_right _ _
  refine ⟨5 * W₂ ^ 2 + (x₀ + C * (2 * Cm ^ 2 + 1)), fun W hW r hr1 hrT E hE => ?_⟩
  have hz := cph_boundaryZ_im_nonneg (b := b) (by linarith) hκ hE
  have hE2 : |E| ≤ 2 := (abs_le_of_mem_bulkInterval hE).trans (by linarith)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  rw [integral_congr_ae (cph_psi_ae_eq b E W r)]
  have hF := BlockBand.RankLocation.semicircleCDF_nonneg E
  have hF1 := BlockBand.RankLocation.semicircleCDF_le_one E
  have hl := cph_abs_phaseEll_le E
  have hh := cph_abs_phaseH_le hE2
  have hconst : |2 * phaseEll E + b * phaseH E| ≤ 3 := by
    have := abs_add_le (2 * phaseEll E) (b * phaseH E)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hb0] at this
    nlinarith
  have hpos : 0 ≤ 5 * W₂ ^ 2 := by positivity
  have hpos2 : 0 ≤ x₀ + C * (2 * Cm ^ 2 + 1) := by positivity
  rw [le_div_iff₀ hWr]
  by_cases hWs : (W : ℝ) < 4 / ε₀
  · -- small `W`: everything is `O(rW)`
    have hI : |∫ ω, cphPsiM b E ω ∂pathLaw W r b| ≤ (r + 2) * W :=
      cph_abs_integral_le fun ω => cph_abs_psiM_le hz ω
    have hWW : (W : ℝ) ≤ W₂ := hWs.le.trans (le_max_left _ _)
    have hcrude : |(∫ ω, cphPsiM b E ω ∂pathLaw W r b) - r * W * semicircleCDF E -
        W * (2 * phaseEll E + b * phaseH E)| ≤ 5 * (r + 1) * W := by
      have h3 : |(W : ℝ) * (2 * phaseEll E + b * phaseH E)| ≤ 3 * W := by
        rw [abs_mul, abs_of_pos hWr, mul_comm 3]
        exact mul_le_mul_of_nonneg_left hconst hWr.le
      have h4 : |(r : ℝ) * W * semicircleCDF E| ≤ r * W := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ r * W * semicircleCDF E)]
        exact mul_le_of_le_one_right (by positivity) hF1
      rw [abs_le] at hI h3 h4 ⊢
      constructor <;> nlinarith
    have : 5 * (r + 1) * (W : ℝ) * W ≤ 5 * W₂ ^ 2 * (r + 1) := by
      have : (W : ℝ) * W ≤ W₂ ^ 2 := by nlinarith
      nlinarith
    nlinarith
  · have hW4 : 4 ≤ ε₀ * W := by
      have : 4 / ε₀ ≤ W := le_of_not_gt hWs
      rwa [div_le_iff₀ hε₀, mul_comm] at this
    obtain ⟨r₀, L, hr₀, rfl⟩ := cph_decomp r hr1
    have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
    have hδ : ∀ j < L, |(∫ ω, cphSepMean b E (pathSchur E ω) ∂pathLaw W (r₀ + 2 * j) b) -
        2 * W * semicircleCDF E| ≤ C * (2 * Cm ^ 2 + 1) / W := by
      intro j hj
      have hrj : ((r₀ + 2 * j : ℕ) : ℝ) ≤ T * W := by
        refine le_trans ?_ hrT; exact_mod_cast (by omega : r₀ + 2 * j ≤ r₀ + 2 * L)
      have h2 := hd W hW 2 le_rfl (by linarith) (r₀ + 2 * j) (by omega) hrj E hE
      have h4 := hd W hW (2 * ((2 * 1 : ℕ) : ℝ)) (by norm_num) (by norm_num; linarith)
        (r₀ + 2 * j) (by omega) hrj E hE
      have herr := (cph_errors (m := 1) le_rfl hb1 hκ hE hW hC0 (by positivity) (by positivity)
        (fun X hX => hC W hW X hX E hE) h2 h4).1
      refine herr.trans (le_of_eq ?_)
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have hit := cph_mean_iter (W := W) hr₀1 hb1 hz L hδ
    have hco := hCco W hW r₀ hr₀ E hE
    rw [integral_congr_ae (cph_psi_ae_eq b E W r₀)] at hco
    have hco' : |(∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - r₀ * W * semicircleCDF E -
        W * (2 * phaseEll E + b * phaseH E)| * W ≤ x₀ := by
      rw [← le_div_iff₀ hWr]; exact hco.trans (div_le_div_of_nonneg_right (le_max_left _ _) hWr.le)
    have hit' : |(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) -
        (∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - 2 * L * W * semicircleCDF E| * W ≤
        L * (C * (2 * Cm ^ 2 + 1)) := by
      have := mul_le_mul_of_nonneg_right hit hWr.le
      rwa [mul_div_assoc', div_mul_cancel₀ _ hWr.ne'] at this
    have hsplit : |(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) -
        ((r₀ + 2 * L : ℕ) : ℝ) * W * semicircleCDF E - W * (2 * phaseEll E + b * phaseH E)| ≤
        |(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) -
          (∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - 2 * L * W * semicircleCDF E| +
        |(∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - r₀ * W * semicircleCDF E -
          W * (2 * phaseEll E + b * phaseH E)| := by
      refine le_of_eq_of_le ?_ (abs_add_le _ _)
      congr 1; push_cast; ring
    have hL : (L : ℝ) ≤ ((r₀ + 2 * L : ℕ) : ℝ) + 1 := by
      push_cast; linarith [(Nat.cast_nonneg r₀ : (0 : ℝ) ≤ r₀)]
    have hR1 : (1 : ℝ) ≤ ((r₀ + 2 * L : ℕ) : ℝ) + 1 := by
      have := (Nat.cast_nonneg (r₀ + 2 * L) : (0 : ℝ) ≤ _); linarith
    have hCC : 0 ≤ C * (2 * Cm ^ 2 + 1) := by positivity
    calc |(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) -
          ((r₀ + 2 * L : ℕ) : ℝ) * W * semicircleCDF E - W * (2 * phaseEll E + b * phaseH E)| * W
        ≤ (|(∫ ω, cphPsiM b E ω ∂pathLaw W (r₀ + 2 * L) b) -
          (∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - 2 * L * W * semicircleCDF E| +
        |(∫ ω, cphPsiM b E ω ∂pathLaw W r₀ b) - r₀ * W * semicircleCDF E -
          W * (2 * phaseEll E + b * phaseH E)|) * W := mul_le_mul_of_nonneg_right hsplit hWr.le
      _ ≤ L * (C * (2 * Cm ^ 2 + 1)) + x₀ := by rw [add_mul]; exact add_le_add hit' hco'
      _ ≤ (x₀ + C * (2 * Cm ^ 2 + 1)) * (((r₀ + 2 * L : ℕ) : ℝ) + 1) := by
          have := mul_le_mul_of_nonneg_left hL hCC
          have := le_mul_of_one_le_right hx₀ hR1
          linarith
      _ ≤ (5 * W₂ ^ 2 + (x₀ + C * (2 * Cm ^ 2 + 1))) * (((r₀ + 2 * L : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)

/-- **The compensated-phase lemma** (`CompensatedPhaseContract`) from the matched traces
(`MatchedTracesContract`, path clause), the separate-port conditional mean increments
(`CompensatedIncrementContract`), and the two isolated inputs `CphIncrementFluctuation`
(bounded conditional `L^p` norms of the centered increments) and `CphCore` (the cores
`r = 1, 2`). -/
theorem compensatedPhase_of_inputs (hmt : MatchedTracesContract)
    (hinc : CompensatedIncrementContract) (hfl : CphIncrementFluctuation) (hcore : CphCore) :
    CompensatedPhaseContract where
  fluctuation := cph_fluctuation hmt hinc hfl hcore
  mean := cph_mean hmt hinc hcore

/-- `compensatedPhase_of_inputs` with the matched traces supplied by `matchedTraces_holds`. -/
theorem compensatedPhase_holds_of (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) (hinc : CompensatedIncrementContract)
    (hfl : CphIncrementFluctuation) (hcore : CphCore) : CompensatedPhaseContract :=
  compensatedPhase_of_inputs (matchedTraces_holds hcount hgrad) hinc hfl hcore

end Assembly

end BlockBand.Layers
