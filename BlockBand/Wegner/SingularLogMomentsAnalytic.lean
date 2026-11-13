module

public import Mathlib
public import BlockBand.External.PSSS.Statement

/-!
# Elementary analysis for the singular log moments

Real-analysis lemmas behind the moment bound for `½ Σ_λ log(1 + a²/(λ-e)²)`.

1. `pow_le_descFactorial_sum`: `x^n ≤ n^n Σ_{j<n} (x)_{j+1}` for natural `x`, `n ≥ 1`
   (a crude replacement for the Stirling expansion).
2. `eLpNorm_count_le`: if a measurable count `N` has integrable factorial moments with
   `E (N)_j ≤ v^j` (`v ≥ 0`, all `j ≥ 1`) on a probability space, then
   `‖N‖_{L^n} ≤ countBound n v = (n^n Σ_{j<n} v^{j+1})^{1/n}`.
3. `eLpNorm_tsum_le`: countable Minkowski for nonnegative extended-real series
   (`1 ≤ p < ∞`); `eLpNorm_const_mul_le`.
4. `log_term_le`: the deterministic dyadic bound, for `N > 0`, `0 ≤ a`, `aN ≤ K`, real `e, l`:
   `log(1 + a²/(l-e)²) ≤ Σ_m (K² + 3(m+1)) 1{|l-e| ≤ 2^{-m}/N} + Σ_m K² 4^{-m} 1{|l-e| ≤ 2^{m+1}/N}`
   (at `l = e` the left side is `0` by Lean's convention).
5. `summable_nearTerm`, `summable_farTerm`: the weighted count bounds are summable for every
   `n ≥ 1`, `K` and `L ≥ 0`, with sum depending only on `(n, K, L)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

namespace SingularLogAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-!
## 1. Powers through falling factorials
-/

theorem mul_descFactorial (x m : ℕ) :
    x * x.descFactorial m = x.descFactorial (m + 1) + m * x.descFactorial m := by
  rw [Nat.descFactorial_succ]
  rcases le_or_gt m x with h | h
  · rw [← add_mul, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    simp

/-- `x^n ≤ n^n Σ_{j<n} (x)_{j+1}` for natural `x` and `n ≥ 1`. -/
theorem pow_le_descFactorial_sum (x : ℕ) : ∀ n : ℕ, 1 ≤ n →
    x ^ n ≤ n ^ n * ∑ j ∈ Finset.range n, x.descFactorial (j + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    set T := ∑ j ∈ Finset.range (n + 1), x.descFactorial (j + 1)
    have h1 : ∑ j ∈ Finset.range n, x * x.descFactorial (j + 1) ≤ (n + 1) * T := by
      calc ∑ j ∈ Finset.range n, x * x.descFactorial (j + 1)
          = ∑ j ∈ Finset.range n,
              (x.descFactorial (j + 1 + 1) + (j + 1) * x.descFactorial (j + 1)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact mul_descFactorial x (j + 1)
        _ ≤ ∑ j ∈ Finset.range n,
              (x.descFactorial (j + 1 + 1) + n * x.descFactorial (j + 1)) := by
            apply Finset.sum_le_sum
            intro j hj
            have := Finset.mem_range.mp hj
            gcongr
            omega
        _ = ∑ j ∈ Finset.range n, x.descFactorial (j + 1 + 1) +
              n * ∑ j ∈ Finset.range n, x.descFactorial (j + 1) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ T + n * T := by
            gcongr
            · show _ ≤ ∑ j ∈ Finset.range (n + 1), x.descFactorial (j + 1)
              rw [Finset.sum_range_succ' (fun j => x.descFactorial (j + 1))]
              exact Nat.le_add_right _ _
            · exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ n))
        _ = (n + 1) * T := by ring
    calc x ^ (n + 1) = x * x ^ n := by ring
      _ ≤ x * (n ^ n * ∑ j ∈ Finset.range n, x.descFactorial (j + 1)) :=
          Nat.mul_le_mul_left x ih
      _ = n ^ n * ∑ j ∈ Finset.range n, x * x.descFactorial (j + 1) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ ≤ n ^ n * ((n + 1) * T) := Nat.mul_le_mul_left _ h1
      _ ≤ (n + 1) ^ (n + 1) * T := by
          rw [← mul_assoc]
          apply Nat.mul_le_mul_right
          calc n ^ n * (n + 1) ≤ (n + 1) ^ n * (n + 1) :=
                Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ n) n)
            _ = (n + 1) ^ (n + 1) := by ring

theorem pow_le_descFactorial_sum_real (x n : ℕ) (hn : 1 ≤ n) :
    (x : ℝ) ^ n ≤ (n : ℝ) ^ n * ∑ j ∈ Finset.range n, (x.descFactorial (j + 1) : ℝ) := by
  exact_mod_cast pow_le_descFactorial_sum x n hn

/-!
## 2. `L^n` norm of a count from its factorial moments
-/

/-- The `L^n` bound of a count whose factorial moments are at most `v^j`. -/
def countBound (n : ℕ) (v : ℝ) : ℝ :=
  ((n : ℝ) ^ n * ∑ j ∈ Finset.range n, v ^ (j + 1)) ^ (1 / (n : ℝ))

theorem countBound_nonneg (n : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ countBound n v :=
  Real.rpow_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)) _

section Count

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

theorem lintegral_pow_le {N : Ω → ℕ} (n : ℕ) (hn : 1 ≤ n) (v : ℝ)
    (hint : ∀ j, 1 ≤ j → Integrable (BlockBand.External.PSSS.factorialCount N j) P)
    (hbd : ∀ j, 1 ≤ j → ∫ w, BlockBand.External.PSSS.factorialCount N j w ∂P ≤ v ^ j) :
    ∫⁻ w, (N w : ℝ≥0∞) ^ (n : ℝ) ∂P ≤
      ENNReal.ofReal ((n : ℝ) ^ n * ∑ j ∈ Finset.range n, v ^ (j + 1)) := by
  have hpt : ∀ w, (N w : ℝ≥0∞) ^ (n : ℝ) ≤ ENNReal.ofReal ((n : ℝ) ^ n *
      ∑ j ∈ Finset.range n, BlockBand.External.PSSS.factorialCount N (j + 1) w) := by
    intro w
    rw [ENNReal.rpow_natCast]
    have he : ((N w : ℝ≥0∞)) ^ n = ENNReal.ofReal ((N w : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    simpa [BlockBand.External.PSSS.factorialCount] using pow_le_descFactorial_sum_real (N w) n hn
  have hI : Integrable (fun w => (n : ℝ) ^ n *
      ∑ j ∈ Finset.range n, BlockBand.External.PSSS.factorialCount N (j + 1) w) P :=
    (integrable_finsetSum _ (fun j _ => hint (j + 1) (by omega))).const_mul _
  have hnn : 0 ≤ᵐ[P] (fun w => (n : ℝ) ^ n *
      ∑ j ∈ Finset.range n, BlockBand.External.PSSS.factorialCount N (j + 1) w) :=
    Filter.Eventually.of_forall fun w => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
  calc ∫⁻ w, (N w : ℝ≥0∞) ^ (n : ℝ) ∂P
      ≤ ∫⁻ w, ENNReal.ofReal ((n : ℝ) ^ n *
          ∑ j ∈ Finset.range n, BlockBand.External.PSSS.factorialCount N (j + 1) w) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (∫ w, (n : ℝ) ^ n *
          ∑ j ∈ Finset.range n, BlockBand.External.PSSS.factorialCount N (j + 1) w ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hI hnn).symm
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ n * ∑ j ∈ Finset.range n, v ^ (j + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint (j + 1) (by omega))]
        gcongr with j hj
        exact hbd (j + 1) (by omega)

/-- `‖N‖_{L^n} ≤ countBound n v` from `E (N)_j ≤ v^j`, `j ≥ 1`. -/
theorem eLpNorm_count_le {N : Ω → ℕ} (hN : Measurable N) (n : ℕ) (hn : 1 ≤ n) {v : ℝ}
    (hv : 0 ≤ v)
    (hint : ∀ j, 1 ≤ j → Integrable (BlockBand.External.PSSS.factorialCount N j) P)
    (hbd : ∀ j, 1 ≤ j → ∫ w, BlockBand.External.PSSS.factorialCount N j w ∂P ≤ v ^ j) :
    eLpNorm (fun w => (N w : ℝ≥0∞)) (n : ℝ≥0∞) P ≤ ENNReal.ofReal (countBound n v) := by
  have hm : Measurable (fun w => (N w : ℝ≥0∞)) :=
    (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp hN
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hn0 (ENNReal.natCast_ne_top n)
    hm.aestronglyMeasurable]
  simp only [enorm_eq_self, ENNReal.toReal_natCast]
  have hX : 0 ≤ (n : ℝ) ^ n * ∑ j ∈ Finset.range n, v ^ (j + 1) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  calc (∫⁻ w, (N w : ℝ≥0∞) ^ (n : ℝ) ∂P) ^ (1 / (n : ℝ))
      ≤ (ENNReal.ofReal ((n : ℝ) ^ n * ∑ j ∈ Finset.range n, v ^ (j + 1))) ^ (1 / (n : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_pow_le n hn v hint hbd) (by positivity)
    _ = ENNReal.ofReal (countBound n v) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hX (by positivity)]
        rfl

/-!
## 3. Minkowski for nonnegative series
-/

theorem eLpNorm_const_mul_le {F : Ω → ℝ≥0∞} (hF : Measurable F) (c : ℝ≥0∞) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (fun w => c * F w) p P ≤ c * eLpNorm F p P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hF.const_mul c).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hF.aestronglyMeasurable]
  simp only [enorm_eq_self]
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rw [lintegral_const_mul _ (hF.pow_const _), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

theorem iSup_rpow_eq (s : ℕ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨆ n, s n) ^ r = ⨆ n, s n ^ r :=
  Monotone.map_iSup_of_continuousAt (f := fun x : ℝ≥0∞ => x ^ r)
    ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hr.le)
    (by simp [ENNReal.zero_rpow_of_pos hr])

/-- Countable Minkowski inequality for nonnegative measurable series, `1 ≤ p < ∞`. -/
theorem eLpNorm_tsum_le {F : ℕ → Ω → ℝ≥0∞} (hF : ∀ m, Measurable (F m)) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (fun w => ∑' m, F m w) p P ≤ ∑' m, eLpNorm (F m) p P := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  set g : ℕ → Ω → ℝ≥0∞ := fun n w => ∑ m ∈ Finset.range n, F m w with hg
  have hgm : ∀ n, Measurable (g n) := fun n => Finset.measurable_sum _ (fun m _ => hF m)
  have hmono : Monotone g := fun a b hab w =>
    Finset.sum_le_sum_of_subset (Finset.range_mono hab)
  have hsum : (fun w => ∑' m, F m w) = fun w => ⨆ n, g n w := by
    funext w
    exact ENNReal.tsum_eq_iSup_nat
  have hlim : eLpNorm (fun w => ⨆ n, g n w) p P = ⨆ n, eLpNorm (g n) p P := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (Measurable.iSup hgm).aestronglyMeasurable]
    simp only [enorm_eq_self]
    simp_rw [iSup_rpow_eq _ hq]
    rw [lintegral_iSup (fun n => (hgm n).pow_const _)
      (fun a b hab w => ENNReal.rpow_le_rpow (hmono hab w) hq.le)]
    rw [iSup_rpow_eq _ (by positivity)]
    congr 1
    funext n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hgm n).aestronglyMeasurable]
    simp only [enorm_eq_self]
  rw [hsum, hlim]
  refine iSup_le fun n => ?_
  calc eLpNorm (g n) p P = eLpNorm (∑ m ∈ Finset.range n, F m) p P := by
        congr 1
        funext w
        simp [hg, Finset.sum_apply]
    _ ≤ ∑ m ∈ Finset.range n, eLpNorm (F m) p P := eLpNorm_sum_le hp
    _ ≤ ∑' m, eLpNorm (F m) p P := ENNReal.sum_le_tsum _

end Count

/-!
## 4. The deterministic dyadic bound
-/

/-- Weight of the `m`-th inner shell `|u| ∈ (2^{-m-1}, 2^{-m}]`. -/
def nearWeight (K : ℝ) (m : ℕ) : ℝ := K ^ 2 + 3 * ((m : ℝ) + 1)

/-- Weight of the `m`-th outer shell `|u| ∈ [2^m, 2^{m+1})`. -/
def farWeight (K : ℝ) (m : ℕ) : ℝ := K ^ 2 / 4 ^ m

theorem nearWeight_nonneg (K : ℝ) (m : ℕ) : 0 ≤ nearWeight K m := by
  unfold nearWeight
  positivity

theorem farWeight_nonneg (K : ℝ) (m : ℕ) : 0 ≤ farWeight K m := by
  unfold farWeight
  positivity

/-- Dyadic bound of one singular-log summand, in the rescaled variable `u = N(l - e)`:
for `N > 0`, `0 ≤ a`, `aN ≤ K`, every real `e, l`,
`log(1 + a²/(l-e)²) ≤ Σ_m nearWeight_m 1{|l-e| ≤ 2^{-m}/N} + Σ_m farWeight_m 1{|l-e| ≤ 2^{m+1}/N}`.
At `l = e` the left side is `log 1 = 0` (Lean's `x/0 = 0`). -/
theorem log_term_le (K a e l : ℝ) (N : ℕ) (hN : 0 < N) (ha : 0 ≤ a) (haK : a * N ≤ K) :
    ENNReal.ofReal (Real.log (1 + a ^ 2 / (l - e) ^ 2)) ≤
      (∑' m : ℕ, ENNReal.ofReal (nearWeight K m) *
          (if l ∈ Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N) then 1 else 0)) +
        ∑' m : ℕ, ENNReal.ofReal (farWeight K m) *
          (if l ∈ Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N) then 1 else 0) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hle : l - e = 0
  · simp [hle]
  set t := |l - e| with ht
  have ht0 : 0 < t := abs_pos.mpr hle
  have hsq : (l - e) ^ 2 = t ^ 2 := (sq_abs _).symm
  set u := (N : ℝ) * t with hu
  have hu0 : 0 < u := mul_pos hN' ht0
  have hfrac : a ^ 2 / (l - e) ^ 2 ≤ K ^ 2 / u ^ 2 := by
    rw [hsq, hu, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (a * N) ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (mul_nonneg ha hN'.le) haK 2
    calc a ^ 2 * ((N : ℝ) ^ 2 * t ^ 2) = (a * N) ^ 2 * t ^ 2 := by ring
      _ ≤ K ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
  have hmem : ∀ ρ : ℝ, u ≤ ρ → l ∈ Icc (e - ρ / N) (e + ρ / N) := by
    intro ρ hρ
    have h1 : t ≤ ρ / N := by
      rw [le_div_iff₀ hN']
      linarith
    have habs := abs_le.mp h1
    constructor <;> linarith [habs.1, habs.2]
  have hx0 : 0 ≤ a ^ 2 / (l - e) ^ 2 := by positivity
  rcases le_or_gt u 1 with hu1 | hu1
  · obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (one_le_one_div hu0 hu1)
      (one_lt_two : (1 : ℝ) < 2)
    have hρ : u ≤ (1 / 2 : ℝ) ^ m := by
      rw [one_div_pow, le_one_div hu0 (by positivity)]
      exact hm1
    have hKu : K ^ 2 / u ^ 2 ≤ K ^ 2 * 4 ^ (m + 1) := by
      have h1 : (1 / u) ^ 2 ≤ ((2 : ℝ) ^ (m + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hm2.le 2
      have h2 : ((2 : ℝ) ^ (m + 1)) ^ 2 = 4 ^ (m + 1) := by
        rw [sq, ← mul_pow]
        norm_num
      rw [h2] at h1
      calc K ^ 2 / u ^ 2 = K ^ 2 * (1 / u) ^ 2 := by
            rw [one_div_pow, mul_one_div]
        _ ≤ K ^ 2 * 4 ^ (m + 1) := mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
    have hlog : Real.log (1 + a ^ 2 / (l - e) ^ 2) ≤ nearWeight K m := by
      have h4 : (1 : ℝ) ≤ 4 ^ (m + 1) := one_le_pow₀ (by norm_num)
      calc Real.log (1 + a ^ 2 / (l - e) ^ 2) ≤ Real.log ((1 + K ^ 2) * 4 ^ (m + 1)) := by
            apply Real.log_le_log (by positivity)
            nlinarith [hfrac, hKu, sq_nonneg K]
        _ = Real.log (1 + K ^ 2) + ((m : ℝ) + 1) * Real.log 4 := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ K ^ 2 + ((m : ℝ) + 1) * 3 := by
            have h1 : Real.log (1 + K ^ 2) ≤ K ^ 2 := by
              have := Real.log_le_sub_one_of_pos (show 0 < 1 + K ^ 2 by positivity)
              linarith
            have h2 : Real.log 4 ≤ 3 := by
              have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
              linarith
            have h3 : (0 : ℝ) ≤ m + 1 := by positivity
            nlinarith
        _ = nearWeight K m := by
            unfold nearWeight
            ring
    calc ENNReal.ofReal (Real.log (1 + a ^ 2 / (l - e) ^ 2))
        ≤ ENNReal.ofReal (nearWeight K m) *
            (if l ∈ Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N) then 1 else 0) := by
          simp only [hmem _ hρ, ↓reduceIte, mul_one]
          exact ENNReal.ofReal_le_ofReal hlog
      _ ≤ ∑' m : ℕ, ENNReal.ofReal (nearWeight K m) *
            (if l ∈ Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N) then 1 else 0) :=
          ENNReal.le_tsum (f := fun m : ℕ => ENNReal.ofReal (nearWeight K m) *
            (if l ∈ Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N) then 1 else 0)) m
      _ ≤ _ := le_self_add
  · obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near hu1.le (one_lt_two : (1 : ℝ) < 2)
    have hKu : K ^ 2 / u ^ 2 ≤ farWeight K m := by
      unfold farWeight
      apply div_le_div_of_nonneg_left (sq_nonneg K) (by positivity)
      calc (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by
            rw [sq, ← mul_pow]
            norm_num
        _ ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hm1 2
    have hlog : Real.log (1 + a ^ 2 / (l - e) ^ 2) ≤ farWeight K m := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + a ^ 2 / (l - e) ^ 2 by positivity)
      linarith
    calc ENNReal.ofReal (Real.log (1 + a ^ 2 / (l - e) ^ 2))
        ≤ ENNReal.ofReal (farWeight K m) *
            (if l ∈ Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N) then 1 else 0) := by
          simp only [hmem _ hm2.le, ↓reduceIte, mul_one]
          exact ENNReal.ofReal_le_ofReal hlog
      _ ≤ ∑' m : ℕ, ENNReal.ofReal (farWeight K m) *
            (if l ∈ Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N) then 1 else 0) :=
          ENNReal.le_tsum (f := fun m : ℕ => ENNReal.ofReal (farWeight K m) *
            (if l ∈ Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N) then 1 else 0)) m
      _ ≤ _ := le_add_self

/-!
## 5. Summability of the weighted count bounds
-/

/-- Contribution of the `m`-th inner disc `|u| ≤ 2^{-m}` (count parameter `L 2^{-m}`). -/
def nearTerm (n : ℕ) (K L : ℝ) (m : ℕ) : ℝ :=
  nearWeight K m * countBound n (L * (1 / 2 : ℝ) ^ m)

/-- Contribution of the `m`-th outer disc `|u| ≤ 2^{m+1}` (count parameter `L 2^{m+1}`). -/
def farTerm (n : ℕ) (K L : ℝ) (m : ℕ) : ℝ :=
  farWeight K m * countBound n (L * 2 ^ (m + 1))

theorem nearTerm_nonneg (n : ℕ) (K : ℝ) {L : ℝ} (hL : 0 ≤ L) (m : ℕ) : 0 ≤ nearTerm n K L m :=
  mul_nonneg (nearWeight_nonneg K m) (countBound_nonneg n (by positivity))

theorem farTerm_nonneg (n : ℕ) (K : ℝ) {L : ℝ} (hL : 0 ≤ L) (m : ℕ) : 0 ≤ farTerm n K L m :=
  mul_nonneg (farWeight_nonneg K m) (countBound_nonneg n (by positivity))

theorem sum_pow_le_small {L ρ : ℝ} (hL : 0 ≤ L) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ n * (max L 1) ^ n * ρ := by
  have hterm : ∀ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ (max L 1) ^ n * ρ := by
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    rw [mul_pow]
    apply mul_le_mul _ (pow_le_of_le_one hρ0 hρ1 (by omega)) (by positivity) (by positivity)
    calc L ^ (j + 1) ≤ (max L 1) ^ (j + 1) := pow_le_pow_left₀ hL (le_max_left L 1) _
      _ ≤ (max L 1) ^ n := pow_le_pow_right₀ (le_max_right L 1) hjn
  calc ∑ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ ∑ _j ∈ Finset.range n, (max L 1) ^ n * ρ :=
        Finset.sum_le_sum hterm
    _ = n * (max L 1) ^ n * ρ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem sum_pow_le_large {L ρ : ℝ} (hL : 0 ≤ L) (hρ1 : 1 ≤ ρ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ n * (max L 1) ^ n * ρ ^ n := by
  have hterm : ∀ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ (max L 1) ^ n * ρ ^ n := by
    intro j hj
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    rw [mul_pow]
    apply mul_le_mul _ (pow_le_pow_right₀ hρ1 hjn) (by positivity) (by positivity)
    calc L ^ (j + 1) ≤ (max L 1) ^ (j + 1) := pow_le_pow_left₀ hL (le_max_left L 1) _
      _ ≤ (max L 1) ^ n := pow_le_pow_right₀ (le_max_right L 1) hjn
  calc ∑ j ∈ Finset.range n, (L * ρ) ^ (j + 1) ≤ ∑ _j ∈ Finset.range n, (max L 1) ^ n * ρ ^ n :=
        Finset.sum_le_sum hterm
    _ = n * (max L 1) ^ n * ρ ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- The `(n, L)` constant in the disc bounds. -/
def discConst (n : ℕ) (L : ℝ) : ℝ := ((n : ℝ) ^ n * ((n : ℝ) * (max L 1) ^ n)) ^ (1 / (n : ℝ))

theorem discConst_nonneg (n : ℕ) (L : ℝ) : 0 ≤ discConst n L := by
  unfold discConst
  apply Real.rpow_nonneg
  have : 0 ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
  positivity

theorem countBound_small (n : ℕ) {L ρ : ℝ} (hL : 0 ≤ L) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    countBound n (L * ρ) ≤ discConst n L * ρ ^ (1 / (n : ℝ)) := by
  unfold countBound discConst
  have h1 : 0 ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
  rw [← Real.mul_rpow (by positivity) hρ0]
  apply Real.rpow_le_rpow (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => by positivity)) _ (by positivity)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (sum_pow_le_small hL hρ0 hρ1 n) (by positivity)

theorem countBound_large (n : ℕ) (hn : 1 ≤ n) {L ρ : ℝ} (hL : 0 ≤ L) (hρ1 : 1 ≤ ρ) :
    countBound n (L * ρ) ≤ discConst n L * ρ := by
  unfold countBound discConst
  have h1 : 0 ≤ max L 1 := le_trans zero_le_one (le_max_right L 1)
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ1
  have hρ : (ρ ^ n) ^ (1 / (n : ℝ)) = ρ := by
    rw [one_div]
    exact Real.pow_rpow_inv_natCast hρ0 (by omega)
  calc ((n : ℝ) ^ n * ∑ j ∈ Finset.range n, (L * ρ) ^ (j + 1)) ^ (1 / (n : ℝ))
      ≤ ((n : ℝ) ^ n * ((n : ℝ) * (max L 1) ^ n) * ρ ^ n) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => by positivity)) _ (by positivity)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_pow_le_large hL hρ1 n) (by positivity)
    _ = ((n : ℝ) ^ n * ((n : ℝ) * (max L 1) ^ n)) ^ (1 / (n : ℝ)) * ρ := by
        rw [Real.mul_rpow (by positivity) (by positivity), hρ]

theorem half_pow_rpow (n m : ℕ) :
    ((1 / 2 : ℝ) ^ m) ^ (1 / (n : ℝ)) = ((1 / 2 : ℝ) ^ (1 / (n : ℝ))) ^ m := by
  calc ((1 / 2 : ℝ) ^ m) ^ (1 / (n : ℝ)) = ((1 / 2 : ℝ) ^ (m : ℝ)) ^ (1 / (n : ℝ)) := by
        rw [Real.rpow_natCast]
    _ = (1 / 2 : ℝ) ^ ((m : ℝ) * (1 / (n : ℝ))) := by rw [← Real.rpow_mul (by norm_num)]
    _ = (1 / 2 : ℝ) ^ ((1 / (n : ℝ)) * (m : ℝ)) := by rw [mul_comm]
    _ = ((1 / 2 : ℝ) ^ (1 / (n : ℝ))) ^ (m : ℝ) := by rw [Real.rpow_mul (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ (1 / (n : ℝ))) ^ m := by rw [Real.rpow_natCast]

theorem summable_nearTerm (n : ℕ) (hn : 1 ≤ n) (K : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    Summable (nearTerm n K L) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 / 2 : ℝ) ^ (1 / (n : ℝ)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    rw [hq]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (one_div_pos.mpr hn')
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = discConst n L := ⟨_, rfl⟩
  have hbound : ∀ m : ℕ,
      nearTerm n K L m ≤ A * (K ^ 2 + 3) * q ^ m + 3 * A * ((m : ℝ) ^ 1 * q ^ m) := by
    intro m
    have hc := countBound_small n hL (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m)
      (pow_le_one₀ (by norm_num) (by norm_num))
    rw [half_pow_rpow, ← hq, ← hA] at hc
    unfold nearTerm
    calc nearWeight K m * countBound n (L * (1 / 2) ^ m) ≤ nearWeight K m * (A * q ^ m) :=
          mul_le_mul_of_nonneg_left hc (nearWeight_nonneg K m)
      _ = A * (K ^ 2 + 3) * q ^ m + 3 * A * ((m : ℝ) ^ 1 * q ^ m) := by
          unfold nearWeight
          ring
  have h1 : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0 hq1
  have h2 : Summable (fun m : ℕ => (m : ℝ) ^ 1 * q ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  have hs : Summable (fun m : ℕ => A * (K ^ 2 + 3) * q ^ m + 3 * A * ((m : ℝ) ^ 1 * q ^ m)) :=
    (h1.mul_left (A * (K ^ 2 + 3))).add (h2.mul_left (3 * A))
  exact Summable.of_nonneg_of_le (nearTerm_nonneg n K hL) hbound hs

theorem summable_farTerm (n : ℕ) (hn : 1 ≤ n) (K : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    Summable (farTerm n K L) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = discConst n L := ⟨_, rfl⟩
  have hbound : ∀ m : ℕ, farTerm n K L m ≤ 2 * A * K ^ 2 * (1 / 2 : ℝ) ^ m := by
    intro m
    have hc := countBound_large n hn hL (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ (m + 1))
    rw [← hA] at hc
    unfold farTerm
    calc farWeight K m * countBound n (L * 2 ^ (m + 1)) ≤ farWeight K m * (A * 2 ^ (m + 1)) :=
          mul_le_mul_of_nonneg_left hc (farWeight_nonneg K m)
      _ = 2 * A * K ^ 2 * (1 / 2 : ℝ) ^ m := by
          unfold farWeight
          have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by
            rw [← mul_pow]
            norm_num
          rw [h4, pow_succ, one_div_pow]
          field_simp
          ring
  have hs : Summable (fun m : ℕ => 2 * A * K ^ 2 * (1 / 2 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le (farTerm_nonneg n K hL) hbound hs

end SingularLogAnalytic

end BlockBand.Wegner
