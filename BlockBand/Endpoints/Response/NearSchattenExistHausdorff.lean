module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# The Hausdorff moment theorem on a compact interval `[0, a]` (existence)

Deterministic statement (`nse_hausdorff_exists`). Let `a ≥ 0` and `c : ℕ → ℝ` satisfy the closed
Hausdorff conditions
`H_{j,l}(c) = Σ_{i ≤ l} (-1)^i a^{l-i} C(l,i) c_{j+i} ≥ 0` for all `j, l`
(`= L(X^j (a - X)^l)` for the moment functional `L(X^k) = c_k`). Then there is a finite measure
`μ` on `ℝ` with `μ(-∞,0) = 0`, `μ(a,∞) = 0` and `∫ x^k dμ = c_k` for every `k`.

Proof (`a > 0`). The Bernstein weights `w_{n,k} = C(n,k) L(X^k (a-X)^{n-k}) ≥ 0` satisfy the
factorial-moment identity `Σ_k C(k,i) w_{n,k} = C(n,i) a^{n-i} c_i` (`L` applied to
`Σ_k C(n,k)C(k,i) X^k(a-X)^{n-k} = C(n,i) a^{n-i} X^i`). The discrete measures
`ν_n = Σ_k a^{-n} w_{n,k} δ_{ka/n}` on the compact `[0,a]` have mass `c_0` and moments
`∫ x^i dν_n → c_i`, because `|C(k,i)/C(n,i) - (k/n)^i| ≤ 2i²/n` for `k ≤ n`, `2i ≤ n`. The finite
measures of mass `≤ c_0` on `[0,a]` form a compact set (Mathlib's
`isCompact_setOfPred_finiteMeasure_le_of_compactSpace`, from Riesz–Markov–Kakutani); a cluster
point `ν` of `(ν_n)` has `∫ x^i dν = c_i` by continuity of `ν ↦ ∫ f dν` for bounded continuous
`f`. The measure is `ν` pushed to `ℝ`. For `a = 0` the conditions force `c_k = 0` (`k ≥ 1`) and
`μ = c_0 δ_0`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Polynomial Filter Topology Set
open scoped ENNReal NNReal

/-!
## The moment functional and the Hausdorff expressions
-/

/-- The moment functional `L(Σ_k p_k X^k) = Σ_k p_k c_k`. -/
def nseMomFun (c : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun k => c k • LinearMap.id

theorem nse_momFun_monomial (c : ℕ → ℝ) (k : ℕ) (r : ℝ) :
    nseMomFun c (monomial k r) = c k * r := by
  unfold nseMomFun
  rw [Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  · simp
  · simp

theorem nse_momFun_X_pow (c : ℕ → ℝ) (k : ℕ) : nseMomFun c (X ^ k) = c k := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, nse_momFun_monomial, mul_one]

/-- The Hausdorff expression `H_{j,l}(c) = Σ_{i ≤ l} (-1)^i a^{l-i} C(l,i) c_{j+i}`
(`= L(X^j (a-X)^l)`). -/
def nseHaus (c : ℕ → ℝ) (a : ℝ) (j l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (l + 1), (-1 : ℝ) ^ i * a ^ (l - i) * (l.choose i : ℝ) * c (j + i)

theorem nse_poly_expand (a : ℝ) (j l : ℕ) :
    (X ^ j * (C a - X) ^ l : ℝ[X]) = ∑ i ∈ Finset.range (l + 1),
      monomial (j + i) ((-1 : ℝ) ^ i * a ^ (l - i) * (l.choose i : ℝ)) := by
  rw [sub_eq_neg_add, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← C_mul_X_pow_eq_monomial, neg_pow, pow_add, ← C_pow]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem nse_momFun_haus (c : ℕ → ℝ) (a : ℝ) (j l : ℕ) :
    nseMomFun c (X ^ j * (C a - X) ^ l) = nseHaus c a j l := by
  rw [nse_poly_expand, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nse_momFun_monomial]
  ring

/-!
## The factorial-moment identity
-/

theorem nse_choose_identity (a : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ Finset.range (n + 1), ((n.choose k * k.choose i : ℕ) : ℝ) •
        (X ^ k * (C a - X) ^ (n - k) : ℝ[X]) =
      ((n.choose i : ℝ) * a ^ (n - i)) • (X ^ i : ℝ[X]) := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show i + M + 1 = i + (M + 1) by omega, Finset.sum_range_add]
  have h0 : ∑ k ∈ Finset.range i, ((((i + M).choose k * k.choose i : ℕ) : ℝ) •
      (X ^ k * (C a - X) ^ (i + M - k) : ℝ[X])) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hk), mul_zero, Nat.cast_zero, zero_smul]
  rw [h0, zero_add]
  have h1 : ∀ m ∈ Finset.range (M + 1), ((((i + M).choose (i + m) * (i + m).choose i : ℕ) : ℝ) •
      (X ^ (i + m) * (C a - X) ^ (i + M - (i + m)) : ℝ[X])) =
      ((i + M).choose i : ℝ) • (X ^ i * (X ^ m * (C a - X) ^ (M - m) * (M.choose m : ℝ[X]))) :=
    fun m _ => by
      rw [Nat.choose_mul (by omega : i ≤ i + m), show i + M - i = M by omega,
        show i + m - i = m by omega, show i + M - (i + m) = M - m by omega, pow_add]
      simp only [Nat.cast_mul, mul_smul]
      congr 1
      rw [Polynomial.smul_eq_C_mul, map_natCast]
      ring
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, ← Finset.mul_sum, ← add_pow,
    add_sub_cancel, show i + M - i = M by omega, mul_smul]
  congr 1
  rw [Polynomial.smul_eq_C_mul, C_pow]
  ring

/-- `Σ_k C(k,i) w_{n,k} = C(n,i) a^{n-i} c_i` for `w_{n,k} = C(n,k) L(X^k (a-X)^{n-k})`. -/
theorem nse_weight_identity (c : ℕ → ℝ) (a : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (k.choose i : ℝ) * ((n.choose k : ℝ) * nseHaus c a k (n - k)) =
      (n.choose i : ℝ) * a ^ (n - i) * c i := by
  have h := congrArg (nseMomFun c) (nse_choose_identity a hi)
  rw [map_sum, map_smul, nse_momFun_X_pow, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, nse_momFun_haus, smul_eq_mul, Nat.cast_mul]
  ring

/-!
## Ratios of binomial coefficients versus powers
-/

theorem nse_prod_sub_pow_le (f : ℕ → ℝ) (g : ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg0 : 0 ≤ g)
    (hg1 : g ≤ 1) (i : ℕ) :
    |∏ r ∈ Finset.range i, f r - g ^ i| ≤ ∑ r ∈ Finset.range i, |f r - g| := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, pow_succ]
    have hP0 : 0 ≤ ∏ r ∈ Finset.range i, f r := Finset.prod_nonneg fun r _ => (hf r).1
    have hP1 : ∏ r ∈ Finset.range i, f r ≤ 1 :=
      Finset.prod_le_one₀ (fun r _ => (hf r).1) fun r _ => (hf r).2
    have hgi0 : 0 ≤ g ^ i := pow_nonneg hg0 i
    have hgi1 : g ^ i ≤ 1 := pow_le_one₀ hg0 hg1
    have e : (∏ r ∈ Finset.range i, f r) * f i - g ^ i * g =
        (∏ r ∈ Finset.range i, f r) * (f i - g) + (∏ r ∈ Finset.range i, f r - g ^ i) * g := by
      ring
    rw [e]
    calc |(∏ r ∈ Finset.range i, f r) * (f i - g) + (∏ r ∈ Finset.range i, f r - g ^ i) * g|
        ≤ |(∏ r ∈ Finset.range i, f r) * (f i - g)| +
            |(∏ r ∈ Finset.range i, f r - g ^ i) * g| := abs_add_le _ _
      _ ≤ 1 * |f i - g| + (∑ r ∈ Finset.range i, |f r - g|) * 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hg0]
          have : 0 ≤ ∑ r ∈ Finset.range i, |f r - g| := Finset.sum_nonneg fun r _ => abs_nonneg _
          gcongr
      _ = _ := by ring

/-- `C(k,i)/C(n,i) = Π_{r<i} (k-r)/(n-r)` (truncated subtraction). -/
theorem nse_choose_ratio (k n i : ℕ) :
    (k.choose i : ℝ) / (n.choose i : ℝ) =
      ∏ r ∈ Finset.range i, ((k - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) := by
  rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ (by exact_mod_cast (Nat.factorial_pos i).ne')]

theorem nse_factor_bound {k n r : ℕ} (hk : k ≤ n) (hrn : 2 * r ≤ n) (hn : 0 < n) :
    |((k - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) - (k : ℝ) / n| ≤ 2 * r / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt r k with hrk | hrk
  · have hnr : r < n := by omega
    rw [Nat.cast_sub hrk, Nat.cast_sub hnr.le]
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hr2 : 2 * (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hnr' : (0 : ℝ) < n - r := by
      have : (r : ℝ) < n := by exact_mod_cast hnr
      linarith
    have e : ((k : ℝ) - r) / (n - r) - k / n = -(r * (n - k)) / (n * (n - r)) := by
      field_simp
      ring
    rw [e, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r * (n - k)),
      abs_of_pos (by positivity : (0 : ℝ) < n * (n - r)), div_le_div_iff₀ (by positivity) hn']
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hr0 hk0, mul_nonneg hr0 (sub_nonneg.2 hk'), mul_nonneg hr0 hr0]
  · rw [Nat.sub_eq_zero_of_le hrk.le, Nat.cast_zero, zero_div, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    have : (k : ℝ) ≤ r := by exact_mod_cast hrk.le
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    gcongr
    linarith

/-- `|C(k,i)/C(n,i) - (k/n)^i| ≤ 2i²/n` for `k ≤ n`, `2i ≤ n`. -/
theorem nse_choose_ratio_sub_pow_le {k n i : ℕ} (hk : k ≤ n) (hin : 2 * i ≤ n) (hn : 0 < n) :
    |(k.choose i : ℝ) / (n.choose i : ℝ) - ((k : ℝ) / n) ^ i| ≤ 2 * (i : ℝ) ^ 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  rw [nse_choose_ratio]
  refine (nse_prod_sub_pow_le (fun r => ((k - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ)) _ (fun r => ⟨?_, ?_⟩)
    (by positivity) ((div_le_one hn').2 hk') i).trans ?_
  · positivity
  · rcases Nat.eq_zero_or_pos (n - r) with h | h
    · rw [h, Nat.cast_zero, div_zero]; exact zero_le_one
    · exact (div_le_one (by exact_mod_cast h)).2 (by exact_mod_cast Nat.sub_le_sub_right hk r)
  · calc ∑ r ∈ Finset.range i, |((k - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) - (k : ℝ) / n|
        ≤ ∑ _r ∈ Finset.range i, 2 * (i : ℝ) / n :=
          Finset.sum_le_sum fun r hr => by
            have hr := Finset.mem_range.1 hr
            refine (nse_factor_bound hk (by omega) hn).trans ?_
            gcongr
      _ = 2 * (i : ℝ) ^ 2 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring

/-!
## The discrete Bernstein measures on `[0, a]`
-/

section Disc

variable {a : ℝ}

/-- The node `ka/n ∈ [0, a]`. -/
def nsePt (ha : 0 ≤ a) (n k : ℕ) : Icc (0 : ℝ) a := projIcc 0 a ha (k * a / n)

theorem nse_pt_val (ha : 0 ≤ a) {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    (nsePt ha n k : ℝ) = k * a / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  unfold nsePt
  rw [projIcc_of_mem]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hn']
  nlinarith

/-- The normalized Bernstein weight `a^{-n} C(n,k) L(X^k (a-X)^{n-k})`. -/
def nseWeight (c : ℕ → ℝ) (a : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * nseHaus c a k (n - k) / a ^ n

/-- The discrete measure `ν_n = Σ_{k ≤ n} w_{n,k} δ_{ka/n}` on `[0, a]`. -/
def nseDisc (c : ℕ → ℝ) (ha : 0 ≤ a) (n : ℕ) : Measure (Icc (0 : ℝ) a) :=
  ∑ k ∈ Finset.range (n + 1), (nseWeight c a n k).toNNReal • Measure.dirac (nsePt ha n k)

instance nse_disc_isFinite (c : ℕ → ℝ) (ha : 0 ≤ a) (n : ℕ) :
    IsFiniteMeasure (nseDisc c ha n) := by
  unfold nseDisc
  infer_instance

theorem nse_integral_disc (c : ℕ → ℝ) (ha : 0 ≤ a) (n : ℕ) {f : Icc (0 : ℝ) a → ℝ}
    (hf : Continuous f) :
    ∫ x, f x ∂nseDisc c ha n =
      ∑ k ∈ Finset.range (n + 1), ((nseWeight c a n k).toNNReal : ℝ) * f (nsePt ha n k) := by
  unfold nseDisc
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul]
  · intro k _
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem nse_weight_nonneg {c : ℕ → ℝ} (ha : 0 ≤ a) (hc : ∀ j l, 0 ≤ nseHaus c a j l) (n k : ℕ) :
    0 ≤ nseWeight c a n k := by
  unfold nseWeight
  have := hc k (n - k)
  positivity

/-- `c_i = Σ_k w_{n,k} a^i C(k,i)/C(n,i)` (`i ≤ n`, `a > 0`). -/
theorem nse_moment_eq_sum (c : ℕ → ℝ) (ha : 0 < a) {n i : ℕ} (hin : i ≤ n) :
    c i = ∑ k ∈ Finset.range (n + 1),
      nseWeight c a n k * (a ^ i * ((k.choose i : ℝ) / (n.choose i : ℝ))) := by
  have hW := nse_weight_identity c a hin
  have hC : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos hin
  have hpow : a ^ n = a ^ (n - i) * a ^ i := by rw [← pow_add, Nat.sub_add_cancel hin]
  have e : ∑ k ∈ Finset.range (n + 1),
      nseWeight c a n k * (a ^ i * ((k.choose i : ℝ) / (n.choose i : ℝ))) =
      a ^ i / (a ^ n * n.choose i) * ∑ k ∈ Finset.range (n + 1),
        (k.choose i : ℝ) * ((n.choose k : ℝ) * nseHaus c a k (n - k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold nseWeight
    have : (0 : ℝ) < a ^ n := pow_pos ha n
    field_simp
  rw [e, hW, hpow]
  have : (0 : ℝ) < a ^ (n - i) := pow_pos ha _
  have : (0 : ℝ) < a ^ i := pow_pos ha _
  field_simp

theorem nse_disc_moment (c : ℕ → ℝ) (ha : 0 < a) (hc : ∀ j l, 0 ≤ nseHaus c a j l) {n : ℕ}
    (hn : 0 < n) (i : ℕ) :
    ∫ x : Icc (0 : ℝ) a, (x : ℝ) ^ i ∂nseDisc c ha.le n =
      ∑ k ∈ Finset.range (n + 1), nseWeight c a n k * (a ^ i * ((k : ℝ) / n) ^ i) := by
  rw [nse_integral_disc c ha.le n (by fun_prop)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Real.coe_toNNReal _ (nse_weight_nonneg ha.le hc n k),
    nse_pt_val ha.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hn, ← mul_pow]
  ring

theorem nse_disc_moment_tendsto (c : ℕ → ℝ) (ha : 0 < a) (hc : ∀ j l, 0 ≤ nseHaus c a j l)
    (i : ℕ) :
    Tendsto (fun n => ∫ x : Icc (0 : ℝ) a, (x : ℝ) ^ i ∂nseDisc c ha.le n) atTop (𝓝 (c i)) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      |∫ x : Icc (0 : ℝ) a, (x : ℝ) ^ i ∂nseDisc c ha.le n - c i| ≤
        c 0 * a ^ i * (2 * (i : ℝ) ^ 2) / n := by
    filter_upwards [eventually_ge_atTop (2 * i + 1)] with n hn
    have hn0 : 0 < n := by omega
    rw [nse_disc_moment c ha hc hn0, nse_moment_eq_sum c ha (by omega : i ≤ n),
      ← Finset.sum_sub_distrib]
    have h0 : c 0 = ∑ k ∈ Finset.range (n + 1), nseWeight c a n k := by
      rw [nse_moment_eq_sum c ha (Nat.zero_le n)]
      simp
    calc |∑ k ∈ Finset.range (n + 1), (nseWeight c a n k * (a ^ i * ((k : ℝ) / n) ^ i) -
            nseWeight c a n k * (a ^ i * ((k.choose i : ℝ) / (n.choose i : ℝ))))|
        ≤ ∑ k ∈ Finset.range (n + 1), |nseWeight c a n k * (a ^ i * ((k : ℝ) / n) ^ i) -
            nseWeight c a n k * (a ^ i * ((k.choose i : ℝ) / (n.choose i : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1), nseWeight c a n k * (a ^ i * (2 * (i : ℝ) ^ 2 / n)) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          have hw := nse_weight_nonneg ha.le hc n k
          have hai : 0 ≤ a ^ i := pow_nonneg ha.le i
          rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hai,
            abs_sub_comm]
          have := nse_choose_ratio_sub_pow_le hk' (by omega : 2 * i ≤ n) hn0
          gcongr
      _ = c 0 * a ^ i * (2 * (i : ℝ) ^ 2) / n := by
          rw [← Finset.sum_mul, ← h0]
          ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  exact tendsto_const_div_atTop_nhds_zero_nat _

end Disc

/-!
## The Hausdorff moment theorem
-/

theorem nse_eq_of_mapClusterPt {Y : Type*} [TopologicalSpace Y] [T2Space Y] {u : ℕ → Y}
    {x y : Y} (h : MapClusterPt y atTop u) (ht : Tendsto u atTop (𝓝 x)) : y = x :=
  eq_of_nhds_neBot (ClusterPt.mono h ht)

theorem nse_hausdorff_exists_pos {a : ℝ} (ha : 0 < a) {c : ℕ → ℝ}
    (hc : ∀ j l, 0 ≤ nseHaus c a j l) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Iio 0) = 0 ∧ μ (Ioi a) = 0 ∧
      ∀ k : ℕ, ∫ x, x ^ k ∂μ = c k := by
  have : CompactSpace (Icc (0 : ℝ) a) := isCompact_iff_compactSpace.mp isCompact_Icc
  let νF : ℕ → FiniteMeasure (Icc (0 : ℝ) a) := fun n => ⟨nseDisc c ha.le n, inferInstance⟩
  have hK := isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Icc (0 : ℝ) a) (c 0).toNNReal
  have hc0 : 0 ≤ c 0 := by simpa [nseHaus] using hc 0 0
  have hmass : ∀ n : ℕ, 0 < n → (νF n).mass ≤ (c 0).toNNReal := by
    intro n hn
    have h1 := nse_disc_moment c ha hc hn 0
    have h0 : c 0 = ∑ k ∈ Finset.range (n + 1), nseWeight c a n k := by
      rw [nse_moment_eq_sum c ha (Nat.zero_le n)]
      simp
    simp only [pow_zero, mul_one, ← h0, integral_const, smul_eq_mul] at h1
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc0, ← h1]
    simp only [νF, FiniteMeasure.mass, measureReal_def]
    exact le_of_eq (ENNReal.coe_toNNReal_eq_toReal _)
  have hmap : Filter.map νF atTop ≤ 𝓟 {μ : FiniteMeasure (Icc (0 : ℝ) a) |
      μ.mass ≤ (c 0).toNNReal} := by
    rw [le_principal_iff, mem_map]
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hmass n hn
  obtain ⟨ν, -, hcl⟩ := hK.exists_mapClusterPt hmap
  have hmom : ∀ i : ℕ, ∫ x : Icc (0 : ℝ) a, (x : ℝ) ^ i ∂(ν : Measure (Icc (0 : ℝ) a)) = c i := by
    intro i
    let g : BoundedContinuousFunction (Icc (0 : ℝ) a) ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => (x : ℝ) ^ i, by fun_prop⟩
    have hcont := FiniteMeasure.continuous_integral_boundedContinuousFunction g
    exact nse_eq_of_mapClusterPt (u := (fun μ : FiniteMeasure (Icc (0 : ℝ) a) =>
      ∫ x, g x ∂(μ : Measure (Icc (0 : ℝ) a))) ∘ νF)
      (MapClusterPt.continuousAt_comp (f := fun μ : FiniteMeasure (Icc (0 : ℝ) a) =>
        ∫ x, g x ∂(μ : Measure (Icc (0 : ℝ) a))) hcont.continuousAt hcl)
      (nse_disc_moment_tendsto c ha hc i)
  refine ⟨(ν : Measure (Icc (0 : ℝ) a)).map Subtype.val, inferInstance, ?_, ?_, fun k => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_Iio]
    convert measure_empty (μ := (ν : Measure (Icc (0 : ℝ) a)))
    ext x
    simpa using x.2.1
  · rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioi]
    convert measure_empty (μ := (ν : Measure (Icc (0 : ℝ) a)))
    ext x
    simpa using x.2.2
  · rw [integral_map measurable_subtype_coe.aemeasurable
      (by fun_prop : Continuous fun x : ℝ => x ^ k).aestronglyMeasurable]
    exact hmom k

theorem nse_haus_zero (c : ℕ → ℝ) (j l : ℕ) : nseHaus c 0 j l = (-1 : ℝ) ^ l * c (j + l) := by
  unfold nseHaus
  rw [Finset.sum_eq_single l]
  · simp
  · intro i hi hil
    have : l - i ≠ 0 := by have := Finset.mem_range.1 hi; omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self l)) h

/-- **The Hausdorff moment theorem on `[0, a]` (existence).** If `a ≥ 0` and
`H_{j,l}(c) = L(X^j (a-X)^l) ≥ 0` for all `j, l`, then `c` is the moment sequence
`c_k = ∫ x^k dμ` of a finite measure `μ` carried by `[0, a]`. -/
theorem nse_hausdorff_exists {a : ℝ} (ha : 0 ≤ a) {c : ℕ → ℝ}
    (hc : ∀ j l, 0 ≤ nseHaus c a j l) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Iio 0) = 0 ∧ μ (Ioi a) = 0 ∧
      ∀ k : ℕ, ∫ x, x ^ k ∂μ = c k := by
  rcases ha.eq_or_lt with rfl | ha
  · have hc0 : 0 ≤ c 0 := by simpa [nse_haus_zero] using hc 0 0
    have hcs : ∀ k, c (k + 1) = 0 := fun k => by
      have h1 := hc k 1
      have h2 := hc (k + 1) 0
      rw [nse_haus_zero] at h1 h2
      simp only [pow_one, neg_one_mul, pow_zero, one_mul, add_zero] at h1 h2
      linarith
    refine ⟨(c 0).toNNReal • Measure.dirac 0, inferInstance, ?_, ?_, fun k => ?_⟩
    · simp
    · simp
    · rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
        Real.coe_toNNReal _ hc0]
      rcases k with _ | k
      · simp
      · simp [hcs k]
  · exact nse_hausdorff_exists_pos ha hc

end BlockBand.Endpoints
