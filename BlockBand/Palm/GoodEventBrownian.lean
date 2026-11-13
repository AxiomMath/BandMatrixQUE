module

public import BlockBand.Palm.GoodEventNet
public import BlockBand.Palm.GoodEventChain
public import BlockBand.Palm.GoodEventLaw

/-!
# Good spectral event: supremum and modulus of the matrix Brownian path

* `ChainGood K₁ T B`: every level-`n` dyadic increment of `B = hermitianBrownian` on `[0,T]` has
  operator norm at most `K₁ √T q^n`, `q = chainRatio = 2^{-1/4}`.
* `chain_event`: outside outer probability `2·2^{-N}` (`N ≥ 8`) the event `ChainGood` holds,
  from the operator-norm tail `opB_tail_gue` and the increment law `flowLaw_increment_le`.
* `chainGood_sup`, `chainGood_modulus`: on `ChainGood`, `sup_{u ≤ T} ‖B(u) - B(0)‖ ≤ K₁√T/(1-q)`
  and on each level-`m` dyadic cell `‖B(u) - B(kT2^{-m})‖ ≤ K₁√T q^m/(1-q)` (deterministic
  chaining `chain_bound`).
* `initial_norm_event`: `‖G_a‖ ≤ R₁` outside probability `2^{-N}` (`a ≤ 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.GoodEvent

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Palm.CoarseRelative BlockBand.SourceProcess
open BlockBand.Internal.Contracts.Inputs
open scoped NNReal ENNReal

/-- The dyadic chaining ratio `q = 2^{-1/4}`. -/
def chainRatio : ℝ := (2 : ℝ) ^ (-(1 / 4 : ℝ))

theorem chainRatio_pos : 0 < chainRatio := Real.rpow_pos_of_pos (by norm_num) _

theorem chainRatio_pow_four : chainRatio ^ 4 = 1 / 2 := by
  unfold chainRatio
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num [Real.rpow_neg_one]

theorem chainRatio_lt_one : chainRatio < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem chainRatio_le_one : chainRatio ≤ 1 := chainRatio_lt_one.le

/-- `√(2^{-n}) = q^{2n}`. -/
theorem sqrt_half_pow (n : ℕ) : Real.sqrt ((1 / 2 : ℝ) ^ n) = chainRatio ^ n * chainRatio ^ n := by
  have h : (chainRatio ^ n * chainRatio ^ n) ^ 2 = (1 / 2 : ℝ) ^ n := by
    rw [← pow_add, ← pow_mul, show (n + n) * 2 = 4 * n by ring, pow_mul, chainRatio_pow_four]
  rw [← h, Real.sqrt_sq (by have := chainRatio_pos; positivity)]

variable {N : ℕ}

/-- The dyadic chaining good event at level constant `K₁` on `[0,T]`. -/
def ChainGood {N : ℕ} (K₁ T : ℝ) (B : FlowNoise N) : Prop :=
  ∀ n k : ℕ, k < 2 ^ n →
    opB (hermitianBrownian B (((k : ℝ) + 1) * T / 2 ^ n) - hermitianBrownian B ((k : ℝ) * T / 2 ^ n)) ≤
      K₁ * Real.sqrt T * chainRatio ^ n

/-- Every sample path of the Hermitian matrix Brownian motion is continuous. -/
theorem continuous_hermitianBrownian (B : FlowNoise N) :
    Continuous (fun u : ℝ => hermitianBrownian B u) := by
  have hc : Continuous (gueCoord (ι := Fin N) (Real.toNNReal (1 / N))) := by
    have h1 : Continuous (circularBrownianCoordinates (ι := Fin N)) := by
      apply continuous_pi
      intro u
      unfold circularBrownianCoordinates
      fun_prop
    have h2 : Continuous (gueSample (ι := Fin N) (Real.toNNReal (1 / N))) := by
      unfold gueSample
      fun_prop
    exact h2.comp h1
  have hw : Continuous (fun u : ℝ => fun q => B q (Real.toNNReal u)) :=
    continuous_pi fun q => (B q).continuous.comp continuous_real_toNNReal
  have : (fun u : ℝ => hermitianBrownian B u) =
      fun u => gueCoord (Real.toNNReal (1 / N)) (fun q => B q (Real.toNNReal u)) := by
    funext u; exact hermitianBrownian_eq_gueCoord B u
  rw [this]
  exact hc.comp hw

theorem opB_zero : opB (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by
  unfold opB; simp

/-- Partial geometric sums of the chaining radii. -/
theorem chain_geom_le {K₁ T : ℝ} (hK₁ : 0 ≤ K₁) (m j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), K₁ * Real.sqrt T * chainRatio ^ (m + n) ≤
      K₁ * Real.sqrt T * chainRatio ^ m / (1 - chainRatio) := by
  have hq0 := chainRatio_pos
  have hq1 := chainRatio_lt_one
  have hgeom : (∑ n ∈ Finset.range (j + 1), chainRatio ^ n) * (1 - chainRatio) ≤ 1 := by
    rw [geom_sum_mul_neg]
    have : 0 ≤ chainRatio ^ (j + 1) := by positivity
    linarith
  have hs : ∑ n ∈ Finset.range (j + 1), chainRatio ^ n ≤ 1 / (1 - chainRatio) := by
    rw [le_div_iff₀ (by linarith)]; exact hgeom
  have heq : ∑ n ∈ Finset.range (j + 1), K₁ * Real.sqrt T * chainRatio ^ (m + n) =
      K₁ * Real.sqrt T * chainRatio ^ m * ∑ n ∈ Finset.range (j + 1), chainRatio ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [pow_add]; ring
  rw [heq, mul_div_assoc]
  have : 0 ≤ K₁ * Real.sqrt T * chainRatio ^ m := by positivity
  calc K₁ * Real.sqrt T * chainRatio ^ m * ∑ n ∈ Finset.range (j + 1), chainRatio ^ n
      ≤ K₁ * Real.sqrt T * chainRatio ^ m * (1 / (1 - chainRatio)) :=
        mul_le_mul_of_nonneg_left hs this
    _ = _ := by ring

theorem chainGood_modulus {N : ℕ} {K₁ T : ℝ} (hK₁ : 0 ≤ K₁) (hT : 0 < T) {B : FlowNoise N}
    (hB : ChainGood K₁ T B)
    (m k : ℕ) (hk : k < 2 ^ m) {u : ℝ} (hu1 : (k : ℝ) * T / 2 ^ m ≤ u)
    (hu2 : u ≤ ((k : ℝ) + 1) * T / 2 ^ m) :
    opB (hermitianBrownian B u - hermitianBrownian B ((k : ℝ) * T / 2 ^ m)) ≤
      K₁ * Real.sqrt T * chainRatio ^ m / (1 - chainRatio) := by
  have hq0 := chainRatio_pos
  refine chain_bound (fun u w => opB (hermitianBrownian B u - hermitianBrownian B w))
    (fun u v w => opB_sub_le _ _ _) (fun u => by simp only [sub_self, opB_zero])
    (fun w => continuous_opB.comp ((continuous_hermitianBrownian B).sub continuous_const))
    hT (fun n => K₁ * Real.sqrt T * chainRatio ^ n) (fun n => by positivity) hB m
    (fun j => chain_geom_le hK₁ m j) k hk u hu1 hu2

theorem chainGood_sup {N : ℕ} {K₁ T : ℝ} (hK₁ : 0 ≤ K₁) (hT : 0 < T) {B : FlowNoise N}
    (hB : ChainGood K₁ T B)
    {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) :
    opB (hermitianBrownian B u - hermitianBrownian B 0) ≤ K₁ * Real.sqrt T / (1 - chainRatio) := by
  have h := chainGood_modulus hK₁ hT hB 0 0 (by norm_num) (u := u) (by simpa using hu0)
    (by simpa using huT)
  simpa using h

/-- The dyadic chaining event holds outside outer probability `2·2^{-N}`. -/
theorem chain_event (hLp : GaussianLpGradient) : ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ (N : ℕ), 8 ≤ N →
    ∀ (a T : ℝ), 0 < T →
    flowLaw N a {ω | ¬ ChainGood K₁ T ω.2} ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
  obtain ⟨K, hK, htail⟩ := opB_tail_gue hLp
  refine ⟨2 * K, by positivity, ?_⟩
  intro N hN a T hT
  have hNpos : 0 < N := by omega
  have hq0 := chainRatio_pos
  have hq1 := chainRatio_le_one
  set q := chainRatio with hqdef
  set b : ℕ → ℝ := fun n => 2 * K * Real.sqrt T * q ^ n with hbdef
  set Ev : ℕ → ℕ → Set (FlowSample N) := fun n k => {ω | b n < opB
    (hermitianBrownian ω.2 (((k : ℝ) + 1) * T / 2 ^ n) - hermitianBrownian ω.2 ((k : ℝ) * T / 2 ^ n))}
    with hEv
  have hsub : {ω : FlowSample N | ¬ ChainGood (2 * K) T ω.2} ⊆
      ⋃ n, ⋃ k ∈ Finset.range (2 ^ n), Ev n k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, ChainGood, not_forall, not_le] at hω
    obtain ⟨n, k, hk, hlt⟩ := hω
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨n, k, hk, hlt⟩
  -- one increment
  have hone : ∀ n k : ℕ, flowLaw N a (Ev n k) ≤ ENNReal.ofReal ((q ^ n / 2) ^ N) := by
    intro n k
    have hu : (0 : ℝ) ≤ (k : ℝ) * T / 2 ^ n := by positivity
    have huv : (k : ℝ) * T / 2 ^ n ≤ ((k : ℝ) + 1) * T / 2 ^ n := by
      apply div_le_div_of_nonneg_right _ (by positivity); nlinarith
    have hdiff : ((k : ℝ) + 1) * T / 2 ^ n - (k : ℝ) * T / 2 ^ n = T * (1 / 2) ^ n := by
      rw [← sub_div, show ((k : ℝ) + 1) * T - (k : ℝ) * T = T by ring, one_div, inv_pow,
        div_eq_mul_inv]
    have hb : 0 < b n := by simp only [hbdef]; positivity
    refine (flowLaw_increment_le N a hu huv {M | b n < opB M}).trans ?_
    rw [hdiff]
    refine (htail N hNpos (T * (1 / 2) ^ n) (by positivity) (b n) hb).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply le_of_eq
    congr 1
    rw [Real.sqrt_mul hT.le, sqrt_half_pow, ← hqdef]
    simp only [hbdef]
    have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
    field_simp
  -- one level
  have hlevel : ∀ n : ℕ, ∑ k ∈ Finset.range (2 ^ n), flowLaw N a (Ev n k) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ N) * (2⁻¹ : ℝ≥0∞) ^ n := by
    intro n
    refine (Finset.sum_le_sum (fun k _ => hone n k)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_natCast]; push_cast; rfl
    have h3 : (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      congr 1
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    rw [h2, h3, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hqN : (q ^ n) ^ N ≤ ((1 / 4 : ℝ)) ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      calc q ^ N ≤ q ^ 8 := pow_le_pow_of_le_one hq0.le hq1 hN
        _ = (q ^ 4) ^ 2 := by ring
        _ = 1 / 4 := by rw [hqdef, chainRatio_pow_four]; norm_num
    rw [div_pow]
    have h4 : (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n = (1 / 2) ^ n := by
      rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ n * ((q ^ n) ^ N / 2 ^ N)
        ≤ (2 : ℝ) ^ n * ((1 / 4 : ℝ) ^ n / 2 ^ N) := by gcongr
      _ = (1 / 2 : ℝ) ^ N * (1 / 2) ^ n := by
        rw [← h4]; simp only [one_div, inv_pow]; ring
  calc flowLaw N a {ω | ¬ ChainGood (2 * K) T ω.2}
      ≤ flowLaw N a (⋃ n, ⋃ k ∈ Finset.range (2 ^ n), Ev n k) := measure_mono hsub
    _ ≤ ∑' n, flowLaw N a (⋃ k ∈ Finset.range (2 ^ n), Ev n k) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) ^ N) * (2⁻¹ : ℝ≥0∞) ^ n := by
        apply ENNReal.tsum_le_tsum
        intro n
        exact (measure_biUnion_finset_le _ _).trans (hlevel n)
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ N) * 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
        rw [mul_comm, ENNReal.ofReal_mul (by norm_num)]
        simp

/-- The initial Gaussian matrix has bounded operator norm outside probability `2^{-N}`. -/
theorem initial_norm_event (hLp : GaussianLpGradient) : ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ (N : ℕ), 0 < N →
    ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
    flowLaw N a {ω | R₁ < opB ω.1} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
  obtain ⟨K, hK, htail⟩ := opB_tail_gue hLp
  refine ⟨2 * K, by positivity, ?_⟩
  intro N hN a ha0 ha1
  have hset : {ω : FlowSample N | 2 * K < opB ω.1} =
      {M : Matrix (Fin N) (Fin N) ℂ | 2 * K < opB M} ×ˢ Set.univ := by
    ext ω; simp
  rw [hset, flowLaw, Measure.prod_prod, measure_univ, mul_one]
  refine (htail N hN a ha0 (2 * K) (by positivity)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (by positivity)
  have hs : Real.sqrt a ≤ 1 := Real.sqrt_le_one.mpr ha1
  rw [div_le_iff₀ (by positivity)]
  nlinarith

end BlockBand.Palm.GoodEvent
