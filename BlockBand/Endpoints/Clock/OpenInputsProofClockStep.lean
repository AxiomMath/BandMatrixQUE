module

public import BlockBand.Endpoints.Clock.OpenInputsProofStep
public import BlockBand.Endpoints.Clock.OpenInputsProofDefs
public import BlockBand.Endpoints.Clock.ClockMixingMeasure

/-!
# The open-inputs lemma: the conditional clock-moment step

`clockStep_of` proves `ClockStepBound` (Step 6 of the paper's proof) from
* `OnePortWeighted` (the clauses `clockMean`, `clockNoise`, `unrestricted` of the weighted-layer
  lemma for one block with one port; proved by `onePortWeighted_of` from `WeightedLayerContract`),
* `GaussianAbsorptionContract` (fixed moments of `‖𝒢‖`, hence of the injection
  `W⁻¹ Tr C₊ ≤ ‖𝒢‖²`),
* `TraceMatrixContract` (through `cavityMean_of`: the conditional mean and fluctuation of the next
  port trace).

## Proof

At a deterministic Hermitian past `X` and `Y ⪰ 0`, `u = W⁻¹ Tr Y`, the next clock is
`u₊ = t + ι`, `t = W⁻¹ Tr L*YL ≥ 0`, `ι = w W⁻¹ Tr C₊ ≥ 0`. With `m = E t`, `ξ = t - m`
(centered), the binomial expansion `binom_bound` gives
`E u₊^P ≤ m^P + P m^{P-1} E ι + 2^P (m^{P-2} E(ξ+ι)² + E|ξ+ι|^P)` (the linear centered term
vanishes, `moment_bound`); `‖ξ‖_P ≤ C u/√W` (the clock-noise bound), `‖ι‖_P ≤ C` and
`m ≤ (1 + Cδ₀ + CW⁻²)u` (`clockMean`) give
`E u₊^P ≤ (1 + C'δ₀ + C'/W)u^P + C(u^{P-1} + 1)`. The crude clause is Minkowski with the
unrestricted bound. For the weight, `δ₀(X₊) ≤ qδ₀ + CW⁻² + |ξ₊|` with the fresh port fluctuation
`ξ₊` (`step_bound`, the cavity-mean lemma), and the cross term is bounded without any independence
by `|ξ₊| u₊^P ≤ (λ|ξ₊|² + λ⁻¹u₊^{2P})/2`, `λ = W(u^P + 1)` (a Cauchy–Schwarz step). The choice
`K = 2C'/(1-q)` and a small scalar radius absorb the predictable term `C'δ₀ u^P`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace OpenInputsProof

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- `E‖f‖^n ≤ B^n` from `‖f‖_n ≤ B` (natural `n ≥ 1`). -/
theorem lintegral_ofReal_pow_le {F : Type*} [NormedAddCommGroup F] {f : Ω → F} {n : ℕ}
    (hn : 1 ≤ n) (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f (n : ℝ≥0∞) μ ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ n) ∂μ ≤ ENNReal.ofReal (B ^ n) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [eLpNorm_eq_eLpNorm' hn0 (ENNReal.natCast_ne_top n) hf, ENNReal.toReal_natCast] at h
  have h1 : ∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ n) ∂μ = ∫⁻ ω, ‖f ω‖ₑ ^ (n : ℝ) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.rpow_natCast]
  rw [h1, lintegral_rpow_enorm_eq_rpow_eLpNorm' hnr, ENNReal.ofReal_pow hB,
    ← ENNReal.rpow_natCast]
  exact ENNReal.rpow_le_rpow h hnr.le

omit [IsProbabilityMeasure μ] in
/-- The Bochner form: `E‖f‖^n ≤ B^n`. -/
theorem integral_norm_pow_le {F : Type*} [NormedAddCommGroup F] {f : Ω → F} {n : ℕ}
    (hn : 1 ≤ n) (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f (n : ℝ≥0∞) μ ≤ ENNReal.ofReal B) :
    ∫ ω, ‖f ω‖ ^ n ∂μ ≤ B ^ n := by
  refine (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => pow_nonneg (norm_nonneg (f ω)) n)
    (hf.norm.pow n)).trans_le ?_
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (lintegral_ofReal_pow_le hn hf hB h)

/-- `(a + b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h1 : a + b ≤ 2 * max a b := by
    have := le_max_left a b; have := le_max_right a b; linarith
  have h2 : (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by positivity) h1 n
  have h3 : max a b ^ n ≤ a ^ n + b ^ n := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; have := pow_nonneg ha n; linarith
    · rw [max_eq_left h]; have := pow_nonneg hb n; linarith
  rw [mul_pow] at h2
  calc (a + b) ^ n ≤ 2 ^ n * max a b ^ n := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- One binomial term: `w^{k+2} m^{n-k} ≤ m^n w² + |w|^{n+2}` (`k ≤ n`, `m ≥ 0`). -/
theorem binom_term_le {m w : ℝ} (hm : 0 ≤ m) {n k : ℕ} (hk : k ≤ n) :
    w ^ (k + 2) * m ^ (n - k) ≤ m ^ n * w ^ 2 + |w| ^ (n + 2) := by
  have hw2 : 0 ≤ m ^ n * w ^ 2 := by positivity
  have hwP : 0 ≤ |w| ^ (n + 2) := by positivity
  have habs : w ^ (k + 2) ≤ |w| ^ (k + 2) := by
    rw [← abs_pow]; exact le_abs_self _
  have hmk : 0 ≤ m ^ (n - k) := by positivity
  have h1 : w ^ (k + 2) * m ^ (n - k) ≤ |w| ^ (k + 2) * m ^ (n - k) :=
    mul_le_mul_of_nonneg_right habs hmk
  rcases le_total |w| m with h | h
  · have h2 : |w| ^ (k + 2) = |w| ^ k * w ^ 2 := by rw [pow_add, sq_abs]
    have h3 : |w| ^ k ≤ m ^ k := pow_le_pow_left₀ (abs_nonneg w) h k
    have h4 : m ^ k * m ^ (n - k) = m ^ n := by rw [← pow_add, Nat.add_sub_cancel' hk]
    have h5 : |w| ^ (k + 2) * m ^ (n - k) ≤ m ^ n * w ^ 2 := by
      rw [h2, ← h4]
      have := mul_le_mul_of_nonneg_right h3 (mul_nonneg (sq_nonneg w) hmk)
      nlinarith [this]
    linarith
  · have h3 : m ^ (n - k) ≤ |w| ^ (n - k) := pow_le_pow_left₀ hm h (n - k)
    have h4 : |w| ^ (k + 2) * |w| ^ (n - k) = |w| ^ (n + 2) := by
      rw [← pow_add]; congr 1; omega
    have h5 : |w| ^ (k + 2) * m ^ (n - k) ≤ |w| ^ (n + 2) := by
      rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith

/-- **The binomial bound**: `(m+w)^{n+2} ≤ m^{n+2} + (n+2)m^{n+1}w + 2^{n+2}(m^n w² + |w|^{n+2})`. -/
theorem binom_bound {m : ℝ} (hm : 0 ≤ m) (w : ℝ) (n : ℕ) :
    (m + w) ^ (n + 2) ≤ m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * w +
      2 ^ (n + 2) * (m ^ n * w ^ 2 + |w| ^ (n + 2)) := by
  rw [add_comm m w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have hch : ∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) := by
    have h := Nat.sum_range_choose (n + 2)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have h' : ((∑ k ∈ Finset.range (n + 1), (n + 2).choose (k + 1 + 1) : ℕ) : ℝ) ≤
        ((2 ^ (n + 2) : ℕ) : ℝ) := by exact_mod_cast (by omega)
    push_cast at h'; exact h'
  set A := m ^ n * w ^ 2 + |w| ^ (n + 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hrest : ∑ k ∈ Finset.range (n + 1), w ^ (k + 1 + 1) * m ^ (n + 2 - (k + 1 + 1)) *
      ((n + 2).choose (k + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) * A := by
    calc ∑ k ∈ Finset.range (n + 1), w ^ (k + 1 + 1) * m ^ (n + 2 - (k + 1 + 1)) *
          ((n + 2).choose (k + 1 + 1) : ℝ)
        ≤ ∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 1 + 1) : ℝ) * A := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have e : n + 2 - (k + 1 + 1) = n - k := by omega
          rw [e, mul_comm _ A]
          exact mul_le_mul_of_nonneg_right (binom_term_le hm hk') (by positivity)
      _ = (∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 1 + 1) : ℝ)) * A := by
          rw [Finset.sum_mul]
      _ ≤ 2 ^ (n + 2) * A := mul_le_mul_of_nonneg_right hch hA0
  have h1 : w ^ (0 + 1) * m ^ (n + 2 - (0 + 1)) * ((n + 2).choose (0 + 1) : ℝ) =
      ((n : ℝ) + 2) * m ^ (n + 1) * w := by
    simp only [zero_add, pow_one, Nat.choose_one_right]
    rw [show n + 2 - 1 = n + 1 by omega]; push_cast; ring
  have h0 : w ^ 0 * m ^ (n + 2 - 0) * ((n + 2).choose 0 : ℝ) = m ^ (n + 2) := by simp
  rw [h1, h0]
  linarith

/-- **The centered moment bound** (the linear centered term vanishes): for `m ≥ 0`,
`ξ` centered and `ι` in `L^{n+2}`, with `m + ξ + ι ≥ 0`,
`E(m + ξ + ι)^{n+2} ≤ m^{n+2} + (n+2)m^{n+1}B_ι + 2^{n+2}(m^n(B_ξ+B_ι)² + (B_ξ+B_ι)^{n+2})`. -/
theorem moment_bound (n : ℕ) {m : ℝ} (hm : 0 ≤ m) {ξ ι : Ω → ℝ}
    (hξm : AEStronglyMeasurable ξ μ) (hιm : AEStronglyMeasurable ι μ) (hξ0 : ∫ ω, ξ ω ∂μ = 0)
    (hpos : ∀ ω, 0 ≤ m + (ξ ω + ι ω)) {Bξ Bι : ℝ} (hBξ : 0 ≤ Bξ) (hBι : 0 ≤ Bι)
    (hξB : eLpNorm ξ ((n + 2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal Bξ)
    (hιB : eLpNorm ι ((n + 2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal Bι) :
    ∫⁻ ω, ENNReal.ofReal ((m + (ξ ω + ι ω)) ^ (n + 2)) ∂μ ≤
      ENNReal.ofReal (m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * Bι +
        2 ^ (n + 2) * (m ^ n * (Bξ + Bι) ^ 2 + (Bξ + Bι) ^ (n + 2))) := by
  set w : Ω → ℝ := fun ω => ξ ω + ι ω with hw
  have hwm : AEStronglyMeasurable w μ := hξm.add hιm
  have hP1 : (1 : ℝ≥0∞) ≤ ((n + 2 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : 1 ≤ n + 2)
  have hwB : eLpNorm w ((n + 2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal (Bξ + Bι) := by
    refine (eLpNorm_add_le (f := ξ) (g := ι) hP1).trans ?_
    rw [ENNReal.ofReal_add hBξ hBι]; exact add_le_add hξB hιB
  have hfin : ∀ (f : Ω → ℝ) (B : ℝ), eLpNorm f ((n + 2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal B →
      eLpNorm f ((n + 2 : ℕ) : ℝ≥0∞) μ < ⊤ := fun f B h => h.trans_lt ENNReal.ofReal_lt_top
  have hξL : MemLp ξ ((n + 2 : ℕ) : ℝ≥0∞) μ := hfin ξ Bξ hξB
  have hιL : MemLp ι ((n + 2 : ℕ) : ℝ≥0∞) μ := hfin ι Bι hιB
  have hwL : MemLp w ((n + 2 : ℕ) : ℝ≥0∞) μ := hfin w _ hwB
  have hle : ∀ k : ℕ, k ≤ n + 2 → ((k : ℕ) : ℝ≥0∞) ≤ ((n + 2 : ℕ) : ℝ≥0∞) := fun k hk => by
    exact_mod_cast hk
  have hξ1 : Integrable ξ μ := (hξL.mono_exponent (by simpa using hle 1 (by omega))).integrable le_rfl
  have hι1 : Integrable ι μ := (hιL.mono_exponent (by simpa using hle 1 (by omega))).integrable le_rfl
  have hw2 : Integrable (fun ω => w ω ^ 2) μ := by
    refine (hwL.mono_exponent ?_).integrable_sq
    have := hle 2 (by omega); simp at this ⊢
  have hwP : Integrable (fun ω => |w ω| ^ (n + 2)) μ := by
    have := hwL.integrable_norm_pow (by omega)
    simpa only [Real.norm_eq_abs] using this
  set g : Ω → ℝ := fun ω => m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * w ω +
    2 ^ (n + 2) * (m ^ n * w ω ^ 2 + |w ω| ^ (n + 2)) with hg
  have hgi : Integrable g μ :=
    ((integrable_const _).add ((hξ1.add hι1).const_mul _)).add
      (((hw2.const_mul _).add hwP).const_mul _)
  have hpt : ∀ ω, (m + (ξ ω + ι ω)) ^ (n + 2) ≤ g ω := fun ω => binom_bound hm (w ω) n
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => (pow_nonneg (hpos ω) _).trans (hpt ω)
  calc ∫⁻ ω, ENNReal.ofReal ((m + (ξ ω + ι ω)) ^ (n + 2)) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, g ω ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hwi : Integrable w μ := hξ1.add hι1
        have hA : Integrable (fun ω => m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * w ω) μ :=
          (integrable_const _).add ((hξ1.add hι1).const_mul _)
        have hB : Integrable (fun ω => 2 ^ (n + 2) * (m ^ n * w ω ^ 2 + |w ω| ^ (n + 2))) μ :=
          ((hw2.const_mul _).add hwP).const_mul _
        have I1 : ∫ ω, g ω ∂μ = ∫ ω, (m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * w ω) ∂μ +
            ∫ ω, 2 ^ (n + 2) * (m ^ n * w ω ^ 2 + |w ω| ^ (n + 2)) ∂μ := integral_add hA hB
        have I2 : ∫ ω, (m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * w ω) ∂μ =
            m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * ∫ ω, ι ω ∂μ := by
          rw [integral_add (integrable_const _) (hwi.const_mul _), integral_const,
            integral_const_mul]
          have : ∫ ω, w ω ∂μ = ∫ ω, ι ω ∂μ := by
            have h : ∫ ω, w ω ∂μ = ∫ ω, ξ ω ∂μ + ∫ ω, ι ω ∂μ := integral_add hξ1 hι1
            rw [hξ0, zero_add] at h; exact h
          rw [this]; simp
        have I3 : ∫ ω, 2 ^ (n + 2) * (m ^ n * w ω ^ 2 + |w ω| ^ (n + 2)) ∂μ =
            2 ^ (n + 2) * (m ^ n * ∫ ω, w ω ^ 2 ∂μ + ∫ ω, |w ω| ^ (n + 2) ∂μ) := by
          rw [integral_const_mul, integral_add (hw2.const_mul _) hwP, integral_const_mul]
        have hint : ∫ ω, g ω ∂μ = m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * ∫ ω, ι ω ∂μ +
            2 ^ (n + 2) * (m ^ n * ∫ ω, w ω ^ 2 ∂μ + ∫ ω, |w ω| ^ (n + 2) ∂μ) := by
          rw [I1, I2, I3]
        rw [hint]
        have hι1B : ∫ ω, ι ω ∂μ ≤ Bι := by
          have h1 : eLpNorm ι ((1 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal Bι :=
            (eLpNorm_le_eLpNorm_of_exponent_le (hle 1 (by omega))).trans hιB
          have := integral_norm_pow_le (le_refl 1) hιm hBι h1
          simp only [pow_one] at this
          exact (integral_mono hι1 hι1.norm fun ω => le_abs_self _).trans this
        have hw2B : ∫ ω, w ω ^ 2 ∂μ ≤ (Bξ + Bι) ^ 2 := by
          have h1 : eLpNorm w ((2 : ℕ) : ℝ≥0∞) μ ≤ ENNReal.ofReal (Bξ + Bι) :=
            (eLpNorm_le_eLpNorm_of_exponent_le (hle 2 (by omega))).trans hwB
          have := integral_norm_pow_le (by norm_num) hwm (by positivity) h1
          simpa only [Real.norm_eq_abs, sq_abs] using this
        have hwPB : ∫ ω, |w ω| ^ (n + 2) ∂μ ≤ (Bξ + Bι) ^ (n + 2) := by
          have := integral_norm_pow_le (by omega) hwm (by positivity) hwB
          simpa only [Real.norm_eq_abs] using this
        have hc1 : 0 ≤ ((n : ℝ) + 2) * m ^ (n + 1) := by positivity
        have hc2 : (0 : ℝ) ≤ 2 ^ (n + 2) := by positivity
        have hc3 : 0 ≤ m ^ n := by positivity
        have e1 := mul_le_mul_of_nonneg_left hι1B hc1
        have e2 := mul_le_mul_of_nonneg_left hw2B hc3
        have e3 : 2 ^ (n + 2) * (m ^ n * ∫ ω, w ω ^ 2 ∂μ + ∫ ω, |w ω| ^ (n + 2) ∂μ) ≤
            2 ^ (n + 2) * (m ^ n * (Bξ + Bι) ^ 2 + (Bξ + Bι) ^ (n + 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add e2 hwPB) hc2
        linarith

end Generic

section Layer

variable {W : ℕ} {b E : ℝ}

/-- The normalized injection `W⁻¹ Re Tr C₊`. -/
def cInj (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) : ℝ :=
  (W : ℝ)⁻¹ * (freshC b E X ω).trace.re

theorem nextClockU_eq (w : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    nextClockU b E w X Y ω = w * cInj b E X ω + clockT b E X Y ω := by
  unfold nextClockU cInj clockT
  rw [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
  ring

theorem clockU_nonneg {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosSemidef) : 0 ≤ clockU Y :=
  mul_nonneg (by positivity) (ClockMixingAlg.trace_re_nonneg hY)

theorem clockT_nonneg (X : Matrix (Fin W) (Fin W) ℂ) {Y : Matrix (Fin W) (Fin W) ℂ}
    (hY : Y.PosSemidef) (ω : OneEndedLayer W) : 0 ≤ clockT b E X Y ω :=
  mul_nonneg (by positivity) (ClockMixingAlg.trace_re_nonneg (hY.conjTranspose_mul_mul_same _))

theorem cInj_nonneg (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) : 0 ≤ cInj b E X ω :=
  mul_nonneg (by positivity) (ClockMixingAlg.trace_re_nonneg (ClockMixingAlg.freshC_posSemidef _ _ _ _))

theorem cInj_le (hW : 0 < W) (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) :
    cInj b E X ω ≤ ‖freshLayer b E X ω‖ ^ 2 := by
  unfold cInj
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have h := ClockMixingAlg.trace_freshC_le b E X ω
  rw [inv_mul_le_iff₀ hWr]; exact h

theorem nextClockU_nonneg {w : ℝ} (hw : 0 ≤ w) (X : Matrix (Fin W) (Fin W) ℂ)
    {Y : Matrix (Fin W) (Fin W) ℂ} (hY : Y.PosSemidef) (ω : OneEndedLayer W) :
    0 ≤ nextClockU b E w X Y ω := by
  rw [nextClockU_eq]
  exact add_nonneg (mul_nonneg hw (cInj_nonneg X ω)) (clockT_nonneg X hY ω)

theorem meas_pair (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun ω : OneEndedLayer W => (X, ω)) :=
  (measurable_const : Measurable (fun _ : OneEndedLayer W => X)).prodMk measurable_id

theorem meas_freshLayer' (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (fun ω : OneEndedLayer W => freshLayer b E X ω) := by
  have h := (ClockMixingProb.meas_freshLayer (W := W) b E).comp (meas_pair X)
  rw [Function.comp_def] at h
  exact h

theorem meas_cInj (X : Matrix (Fin W) (Fin W) ℂ) : Measurable (cInj b E X) := by
  have h := (ClockMixingProb.meas_freshC (W := W) b E).comp
    (meas_pair X)
  rw [Function.comp_def] at h
  unfold cInj
  exact measurable_const.mul (Complex.measurable_re.comp (ClockMixingProb.meas_trace h))

theorem meas_clockT (X Y : Matrix (Fin W) (Fin W) ℂ) : Measurable (clockT b E X Y) := by
  have h := (ClockMixingProb.meas_freshL (W := W) b E).comp
    (meas_pair X)
  rw [Function.comp_def] at h
  unfold clockT
  exact measurable_const.mul (Complex.measurable_re.comp (ClockMixingProb.meas_trace
    (ClockMixingProb.meas_mul (ClockMixingProb.meas_mul (ClockMixingProb.meas_conjTranspose h)
      measurable_const) h)))

theorem meas_nextClockU (w : ℝ) (X Y : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (nextClockU b E w X Y) := by
  have : nextClockU b E w X Y = fun ω => w * cInj b E X ω + clockT b E X Y ω :=
    funext fun ω => nextClockU_eq w X Y ω
  rw [this]
  exact (measurable_const.mul (meas_cInj X)).add (meas_clockT X Y)

theorem meas_cavityHplus (X : Matrix (Fin W) (Fin W) ℂ) (z : ℂ) :
    Measurable (fun ω : OneEndedLayer W => cavityHplus E X z ω) := by
  have h1 := (ClockMixingProb.meas_freshSchur (W := W) E).comp
    (meas_pair X)
  rw [Function.comp_def] at h1
  have h2 := (ZeroEntranceProb.measurable_nrt_joint (W := W)).comp (h1.prodMk
    (measurable_const : Measurable (fun _ : OneEndedLayer W => z)))
  rw [Function.comp_def] at h2
  exact h2

end Layer

/-- `E ∈ [-2 + κ, 2 - κ]` with `κ = 2 - |E| > 0`. -/
theorem mem_bulk {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) :
    0 < 2 - |E| ∧ E ∈ bulkInterval (2 - |E|) := by
  refine ⟨by rw [sub_pos]; exact abs_lt.mpr ⟨hE0, hE1⟩, ?_⟩
  unfold bulkInterval
  constructor
  · have := neg_abs_le E; linarith
  · have := le_abs_self E; linarith

theorem eLpNorm_nat_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : Type*}
    [NormedAddCommGroup F] (f : Ω → F) (P : ℕ) :
    eLpNorm f (ENNReal.ofReal (P : ℝ)) μ = eLpNorm f (P : ℝ≥0∞) μ := by
  rw [ENNReal.ofReal_natCast]

/-- **The fresh ingredients at order `P`**: noise and size of `t = W⁻¹ Tr L*YL`
(the clock-noise and unrestricted clauses) and the size of the injection `W⁻¹ Tr C₊`
(the Gaussian absorption lemma). -/
theorem ingredients (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract) {b E : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {P : ℕ} (hP : 1 ≤ P) :
    ∃ (Cp CG : ℝ) (W₀ : ℕ), 0 ≤ Cp ∧ 0 ≤ CG ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
            (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal (Cp * clockU Y / Real.sqrt W) ∧
        eLpNorm (clockT b E X Y) (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal (Cp * clockU Y) ∧
        eLpNorm (cInj b E X) (P : ℝ≥0∞) (freshLaw W b) ≤ ENNReal.ofReal CG := by
  obtain ⟨hκ, hEκ⟩ := mem_bulk hE0 hE1
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE]
    have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have : 0 < 1 - b := by linarith
    nlinarith
  obtain ⟨-, hnoise⟩ := hW1 b hb0 hb1 _ hκ
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  obtain ⟨Cp, W₂, hCp⟩ := hnoise P hP1
  obtain ⟨ε₁, CG, hε₁, hCG, hGAb⟩ := hGA b hb0 hb1 (boundaryZ b E).im ‖boundaryZ b E‖ hzpos
  refine ⟨max Cp 0, CG ^ 2, max W₂ ⌈2 * P / ε₁⌉₊, le_max_right _ _, by positivity, ?_⟩
  intro W hW hW₀ X hX Y hY
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨h1, h2⟩ := hCp W hW ((le_max_left _ _).trans hW₀) X hX E hEκ Y hY
  have hu := clockU_nonneg hY
  rw [eLpNorm_nat_eq] at h1 h2
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), h2.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have : 0 ≤ clockU Y / Real.sqrt W := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hu
  -- the injection
  have hpW : (2 * P : ℝ) ≤ ε₁ * W := by
    have h := (Nat.le_ceil (2 * P / ε₁)).trans (by exact_mod_cast (le_max_right _ _).trans hW₀ :
      ((⌈2 * P / ε₁⌉₊ : ℕ) : ℝ) ≤ W)
    rw [div_le_iff₀ hε₁] at h; linarith
  have hG := (hGAb W hW .oneBlockOnePort (ClockMixingAlg.physEmbed X)
    (ClockMixingAlg.physEmbed_isHermitian hX) E (boundaryZ b E) le_rfl le_rfl).2 (2 * P)
    (by linarith) hpW
  have hGm := (meas_freshLayer' (b := b) (E := E) X).aestronglyMeasurable (μ := freshLaw W b)
  have hG' : eLpNorm (fun ω => freshLayer b E X ω) (P * ENNReal.ofReal 2) (freshLaw W b) ≤
      ENNReal.ofReal CG := by
    have e : (P : ℝ≥0∞) * ENNReal.ofReal 2 = ENNReal.ofReal (2 * P) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, mul_comm]
    rw [e, ← eLpNorm_norm]
    exacts [hG, hGm]
  calc eLpNorm (cInj b E X) (P : ℝ≥0∞) (freshLaw W b)
      ≤ eLpNorm (fun ω => ‖freshLayer b E X ω‖ ^ (2 : ℝ)) (P : ℝ≥0∞) (freshLaw W b) := by
        refine eLpNorm_mono_real (meas_cInj X).aestronglyMeasurable fun ω => ?_
        rw [Real.norm_of_nonneg (cInj_nonneg X ω), Real.rpow_two]
        exact cInj_le hW X ω
    _ = eLpNorm (fun ω => freshLayer b E X ω) (P * ENNReal.ofReal 2) (freshLaw W b) ^ (2 : ℝ) :=
        eLpNorm_norm_rpow _ hGm (by norm_num)
    _ ≤ ENNReal.ofReal CG ^ (2 : ℝ) := ENNReal.rpow_le_rpow hG' (by norm_num)
    _ = ENNReal.ofReal (CG ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hCG.le (by norm_num), Real.rpow_two]

/-- `‖w ι‖_P ≤ K_q C_G` for `0 ≤ w ≤ K_q`. -/
theorem eLpNorm_inj_le {W : ℕ} {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {P : ℝ≥0∞} {w Kq CG : ℝ}
    (hw : 0 ≤ w) (hwK : w ≤ Kq)
    (h : eLpNorm (cInj b E X) P (freshLaw W b) ≤ ENNReal.ofReal CG) :
    eLpNorm (fun ω => w * cInj b E X ω) P (freshLaw W b) ≤ ENNReal.ofReal (Kq * CG) := by
  have e : (fun ω => w * cInj b E X ω) = w • cInj b E X := rfl
  rw [e]
  refine eLpNorm_const_smul_le.trans ?_
  rw [Real.enorm_eq_ofReal hw, ENNReal.ofReal_mul (hw.trans hwK)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hwK) h

/-- **The crude clause** (from the unrestricted fresh norm bounds):
`E u₊^P ≤ C(u^P + 1)` for every Hermitian past. -/
theorem crude_bound (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract) {b E : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {Kq : ℝ} (hKq : 0 ≤ Kq)
    {P : ℕ} (hP : 1 ≤ P) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
          ENNReal.ofReal (C * (clockU Y ^ P + 1)) := by
  obtain ⟨Cp, CG, W₀, hCp, hCG, hing⟩ := ingredients hW1 hGA hb0 hb1 hE0 hE1 hP
  refine ⟨2 ^ P * ((Kq * CG) ^ P + Cp ^ P), W₀, by positivity, ?_⟩
  intro W hW hW₀ X hX Y hY w hw hwK
  obtain ⟨-, ht, hc⟩ := hing W hW hW₀ X hX Y hY
  have hu := clockU_nonneg hY
  have hP1 : (1 : ℝ≥0∞) ≤ (P : ℝ≥0∞) := by exact_mod_cast hP
  have hsum : eLpNorm (nextClockU b E w X Y) (P : ℝ≥0∞) (freshLaw W b) ≤
      ENNReal.ofReal (Kq * CG + Cp * clockU Y) := by
    have e : nextClockU b E w X Y = (fun ω => w * cInj b E X ω) + clockT b E X Y :=
      funext fun ω => nextClockU_eq w X Y ω
    rw [e]
    refine (eLpNorm_add_le hP1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add (eLpNorm_inj_le hw hwK hc) ht
  have h := lintegral_ofReal_pow_le hP (meas_nextClockU w X Y).aestronglyMeasurable
    (by positivity) hsum
  have e2 : ∀ ω, ‖nextClockU b E w X Y ω‖ = nextClockU b E w X Y ω := fun ω =>
    Real.norm_of_nonneg (nextClockU_nonneg hw X hY ω)
  simp only [e2] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 := add_pow_le_two_pow (by positivity : 0 ≤ Kq * CG) (by positivity : 0 ≤ Cp * clockU Y) P
  rw [mul_pow Cp] at h1
  have h2 : 2 ^ P * ((Kq * CG) ^ P + Cp ^ P * clockU Y ^ P) ≤
      2 ^ P * ((Kq * CG) ^ P + Cp ^ P) * (clockU Y ^ P + 1) := by
    have : 0 ≤ (Kq * CG) ^ P * clockU Y ^ P := by positivity
    have : 0 ≤ Cp ^ P := by positivity
    have : (0 : ℝ) ≤ 2 ^ P := by positivity
    nlinarith
  linarith

/-- The fresh port fluctuation `|h₊(z) - E(h₊(z) | X)|`. -/
def portNoise (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) (ω : OneEndedLayer W) : ℝ :=
  ‖cavityHplus E X (boundaryZ b E) ω - ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b‖

theorem meas_portNoise {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (portNoise b E X) :=
  ((meas_cavityHplus (E := E) X (boundaryZ b E)).sub measurable_const).norm

/-- **The scalar step at the next layer** (from the cavity-mean lemma):
`δ₀(X₊) ≤ q δ₀(X) + C W⁻² + |ξ₊|` on the scalar domain, and `E|ξ₊|² ≤ C W⁻²`. -/
theorem delta_next (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract) {b E : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) :
    ∃ (r₀ q C₂ Cn : ℝ) (W₀ : ℕ), 0 < r₀ ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C₂ ∧ 0 ≤ Cn ∧
      ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian →
        (jetDistance0 b E X ≤ r₀ → ∀ ω, jetDistance0 b E (freshSchur E X ω) ≤
          q * jetDistance0 b E X + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω) ∧
        ∫⁻ ω, ENNReal.ofReal (portNoise b E X ω ^ 2) ∂freshLaw W b ≤
          ENNReal.ofReal (Cn / (W : ℝ) ^ 2) := by
  have hE : |E| ≤ 2 := abs_le.mpr ⟨hE0.le, hE1.le⟩
  have hzpos : 0 < (boundaryZ b E).im := by
    rw [BlockBand.Layers.boundaryZ_im hE]
    have := BlockBand.Layers.matchedA_im_neg (abs_lt.mpr ⟨hE0, hE1⟩)
    have : 0 < 1 - b := by linarith
    nlinarith
  obtain ⟨r₀, q, Cs, hr₀, hq0, hq1, -, hstep⟩ := step_bound hb0 hb1 hE0 hE1
  obtain ⟨⟨a₀, C, ha₀, hC, hcm⟩, -⟩ := cavityMean_of hGA hTM b hb0 hb1 (boundaryZ b E).im
    ‖boundaryZ b E‖ hzpos
  refine ⟨r₀, q, C, 2 * C ^ 2, ⌈2 / a₀⌉₊, hr₀, hq0, hq1, hC.le, by positivity, ?_⟩
  intro W hW hW₀ X hX
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, -, hmean, hfl⟩ := hcm W hW X hX E (boundaryZ b E) le_rfl le_rfl
  refine ⟨fun hδ ω => ?_, ?_⟩
  · have hsc := (hstep hW X hX hδ).1
    have e : jetDistance0 b E (freshSchur E X ω) =
        ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ := rfl
    rw [e]
    have htri : ‖cavityHplus E X (boundaryZ b E) ω - matchedA E‖ ≤ portNoise b E X ω +
        ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) - cavityU X b E (boundaryZ b E)‖ +
        ‖cavityU X b E (boundaryZ b E) - matchedA E‖ := by
      unfold portNoise
      refine (norm_sub_le_norm_sub_add_norm_sub _
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) _).trans ?_
      have := norm_sub_le_norm_sub_add_norm_sub
        (∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (cavityU X b E (boundaryZ b E))
        (matchedA E)
      linarith
    have : ‖(∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) -
        cavityU X b E (boundaryZ b E)‖ ≤ C / (W : ℝ) ^ 2 := hmean
    linarith
  · have h2W : (2 : ℝ) ≤ a₀ * W := by
      have h := (Nat.le_ceil (2 / a₀)).trans (by exact_mod_cast hW₀ : ((⌈2 / a₀⌉₊ : ℕ) : ℝ) ≤ W)
      rw [div_le_iff₀ ha₀] at h; linarith
    have h2 := hfl 2 le_rfl h2W
    rw [ENNReal.ofReal_ofNat] at h2
    have h2' : eLpNorm (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) ((2 : ℕ) : ℝ≥0∞) (freshLaw W b) ≤
        ENNReal.ofReal (C * Real.sqrt 2 / W) := by
      simpa using h2
    have hm : AEStronglyMeasurable (fun ω => cavityHplus E X (boundaryZ b E) ω -
        ∫ ω', cavityHplus E X (boundaryZ b E) ω' ∂freshLaw W b) (freshLaw W b) :=
      ((meas_cavityHplus (E := E) X (boundaryZ b E)).sub measurable_const).aestronglyMeasurable
    have h := lintegral_ofReal_pow_le (by norm_num) hm (by positivity) h2'
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring

/-- `(1 + x)^k ≤ 1 + k 2^k x` for `0 ≤ x ≤ 1`. -/
theorem one_add_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k ≤ 1 + (k : ℝ) * 2 ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h2 : (0 : ℝ) ≤ 2 ^ k := by positivity
    have h3 : (k : ℝ) * 2 ^ k * x * x ≤ (k : ℝ) * 2 ^ k * x := by
      have : 0 ≤ (k : ℝ) * 2 ^ k * x := by positivity
      nlinarith
    have h4 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    calc (1 + x) ^ k * (1 + x) ≤ (1 + (k : ℝ) * 2 ^ k * x) * (1 + x) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ = 1 + x + (k : ℝ) * 2 ^ k * x + (k : ℝ) * 2 ^ k * x * x := by ring
      _ ≤ 1 + ((k + 1 : ℕ) : ℝ) * 2 ^ (k + 1) * x := by
          push_cast; rw [pow_succ]
          have : x ≤ 2 ^ k * x := by nlinarith
          nlinarith

/-- `u^n ≤ u^{n+1} + 1` for `u ≥ 0`. -/
theorem pow_le_succ_add_one {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : u ^ n ≤ u ^ (n + 1) + 1 := by
  rcases le_total u 1 with h | h
  · have := pow_le_one₀ hu h (n := n); have := pow_nonneg hu (n + 1); linarith
  · have : u ^ n ≤ u ^ (n + 1) := pow_le_pow_right₀ h (by omega)
    linarith

/-- The real algebra of the main moment bound. -/
theorem main_algebra (n : ℕ) {u m δ W C₁ Cp Bι : ℝ} (hu : 0 ≤ u) (hm0 : 0 ≤ m)
    (hm : m ≤ (1 + C₁ * δ + C₁ / W ^ 2) * u) (hC₁ : 0 ≤ C₁) (hδ : 0 ≤ δ) (hW : 1 ≤ W)
    (hsmall : C₁ * δ + C₁ / W ^ 2 ≤ 1) (hCp : 0 ≤ Cp) (hBι : 0 ≤ Bι) :
    m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * Bι +
        2 ^ (n + 2) * (m ^ n * (Cp * u / Real.sqrt W + Bι) ^ 2 +
          (Cp * u / Real.sqrt W + Bι) ^ (n + 2)) ≤
      (1 + (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) * δ +
          (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) / W) * u ^ (n + 2) +
        (((n : ℝ) + 2) * 2 ^ (n + 1) * Bι +
          2 ^ (n + 2) * (2 ^ (n + 1) * Bι ^ 2 + 2 ^ (n + 2) * Bι ^ (n + 2))) *
          (u ^ (n + 1) + 1) := by
  have hW0 : 0 < W := by linarith
  set x := C₁ * δ + C₁ / W ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hlam2 : 1 + x ≤ 2 := by linarith
  set U := u ^ (n + 2) with hU
  set V := u ^ (n + 1) + 1 with hV
  have hU0 : 0 ≤ U := by positivity
  have hV1 : 1 ≤ V := by have := pow_nonneg hu (n + 1); linarith
  have hmu : m ≤ (1 + x) * u := by rw [hx, ← add_assoc]; exact hm
  -- the first term
  have hT1 : m ^ (n + 2) ≤ (1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * x) * U := by
    have h1 : m ^ (n + 2) ≤ ((1 + x) * u) ^ (n + 2) := pow_le_pow_left₀ hm0 hmu _
    have h2 : (1 + x) ^ (n + 2) ≤ 1 + ((n + 2 : ℕ) : ℝ) * 2 ^ (n + 2) * x :=
      one_add_pow_le hx0 (by linarith) (n + 2)
    have h2' : (1 + x) ^ (n + 2) ≤ 1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * x := by
      have e : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
      rw [e] at h2; exact h2
    have h3 : ((1 + x) * u) ^ (n + 2) = (1 + x) ^ (n + 2) * U := by rw [mul_pow]
    rw [h3] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2' hU0)
  have hWW : C₁ / W ^ 2 ≤ C₁ / W := by
    apply div_le_div_of_nonneg_left hC₁ hW0; nlinarith
  have hT1' : ((n : ℝ) + 2) * 2 ^ (n + 2) * x * U ≤
      ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (δ * U) + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (U / W) := by
    have hc : 0 ≤ ((n : ℝ) + 2) * 2 ^ (n + 2) := by positivity
    have : x * U ≤ C₁ * (δ * U) + C₁ * (U / W) := by
      rw [hx]
      have : C₁ / W ^ 2 * U ≤ C₁ / W * U := mul_le_mul_of_nonneg_right hWW hU0
      have e : C₁ / W * U = C₁ * (U / W) := by ring
      nlinarith
    have := mul_le_mul_of_nonneg_left this hc
    nlinarith
  -- the second term
  have hm2 : ∀ k : ℕ, m ^ k ≤ 2 ^ k * u ^ k := fun k => by
    rw [← mul_pow]; exact pow_le_pow_left₀ hm0 (hmu.trans (by nlinarith)) k
  have hT2 : ((n : ℝ) + 2) * m ^ (n + 1) * Bι ≤ ((n : ℝ) + 2) * 2 ^ (n + 1) * Bι * V := by
    have h := hm2 (n + 1)
    have hc : 0 ≤ ((n : ℝ) + 2) * Bι := by positivity
    have : u ^ (n + 1) ≤ V := by rw [hV]; linarith
    have h' : m ^ (n + 1) ≤ 2 ^ (n + 1) * V :=
      h.trans (mul_le_mul_of_nonneg_left this (by positivity))
    have := mul_le_mul_of_nonneg_left h' hc
    nlinarith
  -- the noise terms
  set sW := Real.sqrt W with hsW
  have hs1 : 1 ≤ sW := by rw [hsW]; exact Real.one_le_sqrt.mpr hW
  have hs2 : sW ^ 2 = W := Real.sq_sqrt hW0.le
  set a := Cp * u / sW with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = Cp ^ 2 * (u ^ 2 / W) := by rw [ha, div_pow, mul_pow, hs2]; ring
  have hT3 : m ^ n * (a + Bι) ^ 2 ≤ 2 ^ (n + 1) * Cp ^ 2 * (U / W) + 2 ^ (n + 1) * Bι ^ 2 * V := by
    have h1 : (a + Bι) ^ 2 ≤ 2 * a ^ 2 + 2 * Bι ^ 2 := by nlinarith [sq_nonneg (a - Bι)]
    have h2 := hm2 n
    have h3 : m ^ n * (a + Bι) ^ 2 ≤ 2 ^ n * u ^ n * (2 * a ^ 2 + 2 * Bι ^ 2) :=
      mul_le_mul h2 h1 (by positivity) (by positivity)
    have h4 : u ^ n * u ^ 2 = U := by rw [hU, ← pow_add]
    have h5 : u ^ n ≤ V := pow_le_succ_add_one hu n
    have e : 2 ^ n * u ^ n * (2 * a ^ 2 + 2 * Bι ^ 2) =
        2 ^ (n + 1) * Cp ^ 2 * (u ^ n * u ^ 2 / W) + 2 ^ (n + 1) * Bι ^ 2 * u ^ n := by
      rw [ha2, pow_succ]; ring
    rw [e, h4] at h3
    have : 2 ^ (n + 1) * Bι ^ 2 * u ^ n ≤ 2 ^ (n + 1) * Bι ^ 2 * V :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  have hT4 : (a + Bι) ^ (n + 2) ≤ 2 ^ (n + 2) * Cp ^ (n + 2) * (U / W) +
      2 ^ (n + 2) * Bι ^ (n + 2) * V := by
    have h1 := add_pow_le_two_pow ha0 hBι (n + 2)
    have h2 : a ^ (n + 2) ≤ Cp ^ (n + 2) * (U / W) := by
      have hsp : W ≤ sW ^ (n + 2) := by
        rw [← hs2]; exact pow_le_pow_right₀ hs1 (by omega)
      rw [ha, div_pow, mul_pow, hU, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) hW0 hsp
    have h3 : Bι ^ (n + 2) ≤ Bι ^ (n + 2) * V := le_mul_of_one_le_right (by positivity) hV1
    have h4 : 2 ^ (n + 2) * (a ^ (n + 2) + Bι ^ (n + 2)) ≤
        2 ^ (n + 2) * (Cp ^ (n + 2) * (U / W) + Bι ^ (n + 2) * V) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    linarith
  have hT34 : 2 ^ (n + 2) * (m ^ n * (a + Bι) ^ 2 + (a + Bι) ^ (n + 2)) ≤
      2 ^ (n + 2) * ((2 ^ (n + 1) * Cp ^ 2 * (U / W) + 2 ^ (n + 1) * Bι ^ 2 * V) +
        (2 ^ (n + 2) * Cp ^ (n + 2) * (U / W) + 2 ^ (n + 2) * Bι ^ (n + 2) * V)) :=
    mul_le_mul_of_nonneg_left (add_le_add hT3 hT4) (by positivity)
  have hgoal : (1 + (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) * δ +
          (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) / W) * U =
      U + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (δ * U) + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (U / W) +
        2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)) * (δ * U) +
        2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)) * (U / W) := by
    ring
  have hextra : 0 ≤ 2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)) * (δ * U) := by
    positivity
  rw [hgoal]
  have e1 : (1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * x) * U = U + ((n : ℝ) + 2) * 2 ^ (n + 2) * x * U := by
    ring
  rw [e1] at hT1
  linarith only [hT1, hT1', hT2, hT34, hextra]

/-- **The main moment bound**: on the scalar domain,
`E u₊^{n+2} ≤ (1 + Aδ₀ + A/W) u^{n+2} + B(u^{n+1} + 1)`. -/
theorem main_moment (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract) {b E : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (hE0 : -2 < E) (hE1 : E < 2) {Kq : ℝ} (hKq : 0 ≤ Kq)
    (n : ℕ) :
    ∃ (dstar A B : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 ≤ A ∧ 0 ≤ B ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ dstar →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ (n + 2)) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + A * jetDistance0 b E X + A / W) * clockU Y ^ (n + 2) +
            B * (clockU Y ^ (n + 1) + 1)) := by
  obtain ⟨hκ, hEκ⟩ := mem_bulk hE0 hE1
  obtain ⟨⟨dstar₀, C₁, W₁, hd₀, hmean⟩, -⟩ := hW1 b hb0 hb1 _ hκ
  obtain ⟨Cp, CG, W₂, hCp, hCG, hing⟩ := ingredients hW1 hGA hb0 hb1 hE0 hE1
    (P := n + 2) (by omega)
  set C₁' := max C₁ 0 with hC₁'
  have hC₁0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨min dstar₀ (1 / (2 * C₁' + 1)),
    ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁' +
      2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)),
    ((n : ℝ) + 2) * 2 ^ (n + 1) * (Kq * CG) +
      2 ^ (n + 2) * (2 ^ (n + 1) * (Kq * CG) ^ 2 + 2 ^ (n + 2) * (Kq * CG) ^ (n + 2)),
    max (max W₁ W₂) (⌈2 * C₁'⌉₊ + 1), lt_min hd₀ (by positivity), by positivity,
    by positivity, ?_⟩
  intro W hW hW₀ X hX hδ Y hY w hw hwK
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW2' : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hW3 : 2 * C₁' + 1 ≤ (W : ℝ) := by
    have h := Nat.le_ceil (2 * C₁')
    have h2 : ((⌈2 * C₁'⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
    push_cast at h h2; linarith
  have hWr1 : (1 : ℝ) ≤ W := by linarith
  have hWr : (0 : ℝ) < W := by linarith
  set δ := jetDistance0 b E X with hδdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδd : δ ≤ dstar₀ := hδ.trans (min_le_left _ _)
  have hδs : δ ≤ 1 / (2 * C₁' + 1) := hδ.trans (min_le_right _ _)
  obtain ⟨hint, hm⟩ := hmean W hW hW1' X hX E hEκ hδd Y hY
  obtain ⟨hξB, -, hιB⟩ := hing W hW hW2' X hX Y hY
  have hu := clockU_nonneg hY
  set m := ∫ ω, clockT b E X Y ω ∂freshLaw W b with hmdef
  have hm0 : 0 ≤ m := integral_nonneg fun ω => clockT_nonneg X hY ω
  have hm' : m ≤ (1 + C₁' * δ + C₁' / (W : ℝ) ^ 2) * clockU Y := by
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ hu)
    have h1 : C₁ * δ ≤ C₁' * δ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h2 : C₁ / (W : ℝ) ^ 2 ≤ C₁' / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have hsmall : C₁' * δ + C₁' / (W : ℝ) ^ 2 ≤ 1 := by
    have h1 : C₁' * δ ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδs
      nlinarith
    have h2 : C₁' / (W : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hξ0 : ∫ ω, (clockT b E X Y ω - m) ∂freshLaw W b = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp [hmdef]
  have hmb := moment_bound n hm0 (ξ := fun ω => clockT b E X Y ω - m)
    (ι := fun ω => w * cInj b E X ω) ((meas_clockT X Y).sub measurable_const).aestronglyMeasurable
    (measurable_const.mul (meas_cInj X)).aestronglyMeasurable hξ0
    (fun ω => by
      have := clockT_nonneg (b := b) (E := E) X hY ω
      have := mul_nonneg hw (cInj_nonneg (b := b) (E := E) X ω)
      linarith)
    (by positivity : 0 ≤ Cp * clockU Y / Real.sqrt W) (by positivity : 0 ≤ Kq * CG)
    hξB (eLpNorm_inj_le hw hwK hιB)
  have hpt : ∀ ω, m + ((clockT b E X Y ω - m) + w * cInj b E X ω) = nextClockU b E w X Y ω := by
    intro ω; rw [nextClockU_eq]; ring
  simp only [hpt] at hmb
  refine hmb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact main_algebra n hu hm0 hm' hC₁0 hδ0 hWr1 hsmall hCp (by positivity)

/-- The real algebra of the weighted step: absorption of the predictable scalar term by the
weight `K = 2A/(1-q)` and of the cross term `λ = W(u^P+1)`. -/
theorem weighted_algebra {U U2 V δ q K A B W C₂ Cn Cc : ℝ} (hU : 0 ≤ U) (hV : 1 ≤ V)
    (hU2 : U2 = U ^ 2) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hKqδ : K * q * δ ≤ 1) (hq0 : 0 ≤ q)
    (hK0 : 0 ≤ K) (hK : K = K * q + 2 * A) (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : 1 ≤ W)
    (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCc : 0 ≤ Cc) :
    (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A * δ + A / W) * U + B * V) +
        K * (W * (U + 1)) / 2 * (Cn / W ^ 2) + K / (2 * (W * (U + 1))) * (Cc * (U2 + 1)) ≤
      (1 + (2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B) / W) *
          (1 + K * δ) * U +
        (2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B) * V := by
  have hW0 : 0 < W := by linarith
  have hU1 : 0 < U + 1 := by linarith
  set iW := 1 / W with hiW
  have hiW0 : 0 ≤ iW := by positivity
  have hiW1 : iW ≤ 1 := by rw [hiW, div_le_one hW0]; exact hW
  have hiW2 : 1 / W ^ 2 ≤ iW := by
    rw [hiW]; apply div_le_div_of_nonneg_left zero_le_one hW0; nlinarith
  -- the noise terms
  have hn1 : K * (W * (U + 1)) / 2 * (Cn / W ^ 2) = K * Cn / 2 * (U + 1) * iW := by
    rw [hiW]; field_simp
  have hn2 : K / (2 * (W * (U + 1))) * (Cc * (U2 + 1)) ≤ K * Cc / 2 * (U + 1) * iW := by
    rw [hiW, hU2]
    have h1 : U ^ 2 + 1 ≤ (U + 1) ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : K * Cc / 2 * (U + 1) * (1 / W) * (2 * (W * (U + 1))) = K * Cc * (U + 1) ^ 2 := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 hCc)
    linarith
  -- the main product
  have hKA : (1 + K * q * δ) * (1 + A * δ) ≤ 1 + K * δ := by
    have h1 : K * q * δ * (A * δ) ≤ A * δ := by
      have := mul_le_mul_of_nonneg_right hKqδ (mul_nonneg hA hδ0); linarith
    have e : (1 + K * q * δ) * (1 + A * δ) = 1 + (K * q + A) * δ + K * q * δ * (A * δ) := by ring
    rw [e]
    have : (K * q + A) * δ + A * δ = K * δ := by linear_combination (-δ) * hK
    nlinarith
  set D := 2 * A + K * C₂ * (1 + 2 * A) with hD
  have hprod : (1 + K * q * δ + K * C₂ / W ^ 2) * (1 + A * δ + A / W) ≤ 1 + K * δ + D * iW := by
    have e : (1 + K * q * δ + K * C₂ / W ^ 2) * (1 + A * δ + A / W) =
        (1 + K * q * δ) * (1 + A * δ) + (1 + K * q * δ) * A * iW +
          K * C₂ * (1 / W ^ 2) * (1 + A * δ + A * iW) := by rw [hiW]; ring
    rw [e]
    have h2 : (1 + K * q * δ) * A * iW ≤ 2 * A * iW := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 + K * q * δ ≤ 2) (mul_nonneg hA hiW0)
      linarith
    have h3 : K * C₂ * (1 / W ^ 2) * (1 + A * δ + A * iW) ≤ K * C₂ * (1 + 2 * A) * iW := by
      have hb : 1 + A * δ + A * iW ≤ 1 + 2 * A := by
        have : A * δ ≤ A := mul_le_of_le_one_right hA hδ1
        have : A * iW ≤ A := mul_le_of_le_one_right hA hiW1
        linarith
      have hKC : 0 ≤ K * C₂ := mul_nonneg hK0 hC₂
      calc K * C₂ * (1 / W ^ 2) * (1 + A * δ + A * iW) ≤ K * C₂ * iW * (1 + 2 * A) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hiW2 hKC) hb (by positivity) (by positivity)
        _ = K * C₂ * (1 + 2 * A) * iW := by ring
    rw [hD]; linarith
  have hD0 : 0 ≤ D := by positivity
  have hc0 : 1 + K * q * δ + K * C₂ / W ^ 2 ≤ 2 + K * C₂ := by
    have : K * C₂ / W ^ 2 ≤ K * C₂ := div_le_self (mul_nonneg hK0 hC₂) (by nlinarith)
    linarith
  have hc0' : 0 ≤ 1 + K * q * δ + K * C₂ / W ^ 2 := by positivity
  set F := 2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B with hF
  have hKδ : 1 ≤ 1 + K * δ := by have := mul_nonneg hK0 hδ0; linarith
  have t1 : (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A * δ + A / W) * U) ≤
      (1 + K * δ) * U + D * iW * U := by
    have h := mul_le_mul_of_nonneg_right hprod hU
    have e1 : (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A * δ + A / W) * U) =
        (1 + K * q * δ + K * C₂ / W ^ 2) * (1 + A * δ + A / W) * U := by ring
    have e2 : (1 + K * δ + D * iW) * U = (1 + K * δ) * U + D * iW * U := by ring
    rw [e1]; rw [e2] at h; exact h
  have t2 : (1 + K * q * δ + K * C₂ / W ^ 2) * (B * V) ≤ (2 + K * C₂) * B * V := by
    have h := mul_le_mul_of_nonneg_right hc0 (mul_nonneg hB (by linarith : (0 : ℝ) ≤ V))
    have e1 : (2 + K * C₂) * B * V = (2 + K * C₂) * (B * V) := by ring
    rw [e1]; exact h
  have t3 : K * Cn / 2 * (U + 1) * iW + K * Cc / 2 * (U + 1) * iW ≤
      K * (Cn + Cc) / 2 * iW * U + K * (Cn + Cc) / 2 * V := by
    have h0 : 0 ≤ K * (Cn + Cc) / 2 := by positivity
    have h : K * (Cn + Cc) / 2 * iW ≤ K * (Cn + Cc) / 2 * V :=
      mul_le_mul_of_nonneg_left (hiW1.trans hV) h0
    have e : K * Cn / 2 * (U + 1) * iW + K * Cc / 2 * (U + 1) * iW =
        K * (Cn + Cc) / 2 * iW * U + K * (Cn + Cc) / 2 * iW := by ring
    rw [e]; linarith
  have hgoal : (1 + F / W) * (1 + K * δ) * U = (1 + K * δ) * U + F * iW * ((1 + K * δ) * U) := by
    rw [hiW]; ring
  rw [hgoal, hn1]
  have hFiW : D * iW * U + K * (Cn + Cc) / 2 * iW * U ≤ F * iW * ((1 + K * δ) * U) := by
    have h1 : (D + K * (Cn + Cc) / 2) * iW * U ≤ F * iW * U := by
      have : D + K * (Cn + Cc) / 2 ≤ F := by
        rw [hF, hD]; have : 0 ≤ (2 + K * C₂) * B := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hiW0) hU
    have h2 : F * iW * U ≤ F * iW * ((1 + K * δ) * U) := by
      have hF0 : 0 ≤ F * iW := by
        have : 0 ≤ F := by rw [hF]; positivity
        positivity
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hU hKδ) hF0
    have e : D * iW * U + K * (Cn + Cc) / 2 * iW * U = (D + K * (Cn + Cc) / 2) * iW * U := by
      ring
    rw [e]; exact h1.trans h2
  have hV' : (2 + K * C₂) * B * V + K * (Cn + Cc) / 2 * V ≤ F * V := by
    have : (2 + K * C₂) * B + K * (Cn + Cc) / 2 ≤ F := by
      rw [hF]; have : 0 ≤ D := hD0; rw [hD] at this; linarith
    have h := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ V)
    have e : (2 + K * C₂) * B * V + K * (Cn + Cc) / 2 * V =
        ((2 + K * C₂) * B + K * (Cn + Cc) / 2) * V := by ring
    rw [e]; exact h
  linarith only [t1, t2, t3, hn2, hFiW, hV']

/-- `2NV ≤ λN² + V²/λ` (`λ > 0`). -/
theorem two_mul_le_weighted {N V lam : ℝ} (hl : 0 < lam) :
    N * V ≤ lam / 2 * N ^ 2 + 1 / (2 * lam) * V ^ 2 := by
  have h : 0 ≤ (lam * N - V) ^ 2 / lam := by positivity
  have e : (lam * N - V) ^ 2 / lam = lam * N ^ 2 - 2 * (N * V) + V ^ 2 / lam := by
    field_simp; ring
  have e2 : lam / 2 * N ^ 2 + 1 / (2 * lam) * V ^ 2 = (lam * N ^ 2 + V ^ 2 / lam) / 2 := by
    field_simp
  rw [e2]; linarith

/-- **`ClockStepBound`**, from `OnePortWeighted` (the weighted-layer lemma for one block),
`GaussianAbsorptionContract` and `TraceMatrixContract`.
-/
theorem clockStep_of (hW1 : OnePortWeighted) (hGA : GaussianAbsorptionContract)
    (hTM : TraceMatrixContract) : ClockStepBound := by
  intro b hb0 hb1 E hE0 hE1 Kq hKq P hP
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨C, W₀, -, h⟩ := crude_bound hW1 hGA hb0 hb1 hE0 hE1 hKq (P := n + 2) (by omega)
    exact ⟨C, W₀, h⟩
  obtain ⟨r₀, q, C₂, Cn, Wd, hr₀, hq0, hq1, hC₂, hCn, hdel⟩ := delta_next hGA hTM hb0 hb1 hE0 hE1
  obtain ⟨dstar, A, B, Wm, hd, hA, hB, hmain⟩ := main_moment hW1 hGA hb0 hb1 hE0 hE1 hKq n
  obtain ⟨Cc, Wc, hCc, hcrude⟩ :=
    crude_bound hW1 hGA hb0 hb1 hE0 hE1 hKq (P := 2 * n + 4) (by omega)
  have h1q : 0 < 1 - q := by linarith
  set K := 2 * A / (1 - q) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : K = K * q + 2 * A := by rw [hKdef]; field_simp; ring
  refine ⟨min (min r₀ dstar) (min 1 (1 / (K + 1))), K,
    2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B, max (max Wd Wm) Wc,
    lt_min (lt_min hr₀ hd) (lt_min one_pos (by positivity)), hK0, ?_⟩
  intro W hW hW₀ X hX hδ Y hY w hw hwK
  have hWd : Wd ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hWm : Wm ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hWc : Wc ≤ W := (le_max_right _ _).trans hW₀
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set δ := jetDistance0 b E X with hδdef
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδr : δ ≤ r₀ := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδd : δ ≤ dstar := hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδK : δ ≤ 1 / (K + 1) := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKqδ : K * q * δ ≤ 1 := by
    have h1 : K * q * δ ≤ K * δ := by
      have := mul_le_mul_of_nonneg_left (by linarith : q ≤ 1) hK0
      exact mul_le_mul_of_nonneg_right (by linarith) hδ0
    rw [le_div_iff₀ (by positivity)] at hδK
    nlinarith
  obtain ⟨hstep, hN⟩ := hdel W hW hWd X hX
  have hstep' := hstep hδr
  have hM := hmain W hW hWm X hX hδd Y hY w hw hwK
  have hCr := hcrude W hW hWc X hX Y hY w hw hwK
  have hu := clockU_nonneg hY
  set U := clockU Y ^ (n + 2) with hU
  have hU0 : 0 ≤ U := by positivity
  set lam := (W : ℝ) * (U + 1) with hlam
  have hlam0 : 0 < lam := by positivity
  set c₀ := 1 + K * q * δ + K * C₂ / (W : ℝ) ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set c₁ := K * lam / 2 with hc₁
  set c₂ := K / (2 * lam) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set V : OneEndedLayer W → ℝ := fun ω => nextClockU b E w X Y ω ^ (n + 2) with hV
  have hV0 : ∀ ω, 0 ≤ V ω := fun ω => pow_nonneg (nextClockU_nonneg hw X hY ω) _
  have hV2 : ∀ ω, V ω ^ 2 = nextClockU b E w X Y ω ^ (2 * n + 4) := fun ω => by
    rw [hV, ← pow_mul]; ring_nf
  -- pointwise bound
  have hpt : ∀ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) * V ω) ≤
      ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
        ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2) +
        ENNReal.ofReal c₂ * ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4)) := by
    intro ω
    rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
      ← ENNReal.ofReal_add (mul_nonneg hc₀0 (hV0 ω)) (mul_nonneg hc₁0 (sq_nonneg _)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hc₀0 (hV0 ω)) (mul_nonneg hc₁0 (sq_nonneg _)))
        (mul_nonneg hc₂0 (pow_nonneg (nextClockU_nonneg hw X hY ω) _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := hstep' ω
    have hN0 : 0 ≤ portNoise b E X ω := norm_nonneg _
    have h1 : (1 + K * jetDistance0 b E (freshSchur E X ω)) * V ω ≤
        (1 + K * (q * δ + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω)) * V ω := by
      refine mul_le_mul_of_nonneg_right ?_ (hV0 ω)
      have := mul_le_mul_of_nonneg_left hs hK0
      linarith
    have h2 := two_mul_le_weighted (N := portNoise b E X ω) (V := V ω) hlam0
    have h3 : K * (portNoise b E X ω * V ω) ≤
        K * (lam / 2 * portNoise b E X ω ^ 2 + 1 / (2 * lam) * V ω ^ 2) :=
      mul_le_mul_of_nonneg_left h2 hK0
    have e1 : (1 + K * (q * δ + C₂ / (W : ℝ) ^ 2 + portNoise b E X ω)) * V ω =
        c₀ * V ω + K * (portNoise b E X ω * V ω) := by rw [hc₀]; ring
    have e2 : K * (lam / 2 * portNoise b E X ω ^ 2 + 1 / (2 * lam) * V ω ^ 2) =
        c₁ * portNoise b E X ω ^ 2 + c₂ * V ω ^ 2 := by rw [hc₁, hc₂]; ring
    rw [← hV2 ω]
    linarith
  have hmV : Measurable (fun ω => ENNReal.ofReal (V ω)) :=
    ENNReal.measurable_ofReal.comp ((meas_nextClockU w X Y).pow_const _)
  have hmN : Measurable (fun ω => ENNReal.ofReal (portNoise b E X ω ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((meas_portNoise b E X).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
          nextClockU b E w X Y ω ^ (n + 2)) ∂freshLaw W b
      ≤ ∫⁻ ω, (ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4)))
          ∂freshLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal c₀ * ∫⁻ ω, ENNReal.ofReal (V ω) ∂freshLaw W b +
          ENNReal.ofReal c₁ * ∫⁻ ω, ENNReal.ofReal (portNoise b E X ω ^ 2) ∂freshLaw W b +
          ENNReal.ofReal c₂ * ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ (2 * n + 4))
            ∂freshLaw W b := by
        have hm1 : Measurable (fun ω => ENNReal.ofReal c₀ * ENNReal.ofReal (V ω) +
            ENNReal.ofReal c₁ * ENNReal.ofReal (portNoise b E X ω ^ 2)) :=
          (hmV.const_mul _).add (hmN.const_mul _)
        have hm2 : Measurable (fun ω => ENNReal.ofReal c₀ * ENNReal.ofReal (V ω)) :=
          hmV.const_mul _
        rw [lintegral_add_left hm1, lintegral_add_left hm2, lintegral_const_mul _ hmV,
          lintegral_const_mul _ hmN, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal c₀ * ENNReal.ofReal ((1 + A * δ + A / W) * U +
            B * (clockU Y ^ (n + 1) + 1)) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (Cn / (W : ℝ) ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (Cc * (clockU Y ^ (2 * n + 4) + 1)) := by
        gcongr
    _ = ENNReal.ofReal (c₀ * ((1 + A * δ + A / W) * U + B * (clockU Y ^ (n + 1) + 1)) +
          c₁ * (Cn / (W : ℝ) ^ 2) + c₂ * (Cc * (clockU Y ^ (2 * n + 4) + 1))) := by
        rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hU2 : clockU Y ^ (2 * n + 4) = U ^ 2 := by rw [hU, ← pow_mul]; ring_nf
        have hV1 : 1 ≤ clockU Y ^ (n + 1) + 1 := by have := pow_nonneg hu (n + 1); linarith
        have h := weighted_algebra (U2 := clockU Y ^ (2 * n + 4)) (Cn := Cn) (Cc := Cc) hU0 hV1
          hU2 hδ0 hδ1 hKqδ hq0 hK0 hK hA hB hW1r hC₂ hCn hCc
        rw [hc₀, hc₁, hc₂, hlam]
        exact h

end OpenInputsProof

end BlockBand.Endpoints.Clock
