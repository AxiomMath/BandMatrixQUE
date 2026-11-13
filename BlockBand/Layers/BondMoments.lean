module

public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.Nets

/-!
# Operator-norm tails and moments of the layer bond matrix

In the Gaussian absorption lemma, Gaussian norm tails give `‖K‖_{L^q} ≤ C_b(1 + √(q/W))`, with
`K = ‖B‖` the `ℓ²` operator norm (`Matrix.Norms.L2Operator`) of the bond matrix
`B = bondMatrix σ ω.2 : Matrix (PhysSite W σ) (PortSite W σ) ℂ`.

## Law and normalization

`ω ~ layerLaw W b σ`: the bond blocks are independent `Gin(b/W)`, i.e. `E|B_ij|² = b/W` for
incident (block, port) pairs (non-incident entries of `bondMatrix` are `0`). Throughout `b > 0`;
the diagonal blocks play no role.

## Results (uniform in the shape `σ` and in `W ≥ 1`; constants depend only on `b`)

* `bond_exists_net`: `1/4`-nets of the unit sphere of `EuclideanSpace ℂ ι` with
  `|N| ≤ 12^(2 |ι|)` (instance of `exists_sphere_net_euclidean`).
* `bond_opNorm_tail`: unconditional tail
  `P(‖B‖ ≥ a) ≤ 12^(2(|Phys| + |Port|)) exp(-a² W/(4b))` for `a > 0`
  (nets plugged into `layerLaw_bondMatrix_opNorm_tail_of_net`).
* `bond_opNorm_tail_exp`: since `|Phys|, |Port| ≤ 2W` and `12 ≤ e³`,
  `P(‖B‖ ≥ a) ≤ exp(W (24 - a²/(4b)))`.
* `bond_opNorm_tail_subGaussian`: with `a₀ = 10 √b`, for every `s ≥ 0`,
  `P(‖B‖ ≥ a₀ + s) ≤ exp(-W (1 + s²/(4b)))`.
* `bond_measurable_opNorm`: `ω ↦ ‖B(ω)‖` is Borel measurable.
* `bond_lintegral_rpow_le`: for real `1 ≤ q ≤ W`,
  `E (1 + ‖B‖)^q ≤ C₂(b)^q` with `C₂(b) = bondMomentConst b = 6 (1 + 10 √b)`.
* `bond_eLpNorm_le`: `‖1 + ‖B‖‖_{L^q(layerLaw)} ≤ C₂(b)` for real `1 ≤ q ≤ W`.

The moment bound is the `q ≤ W` form of the statement in the paper (`1 + √(q/W) ≤ 2` there);
the proof is a dyadic layer cake: `(1 + K)^q ≤ (1 + a₀)^q + Σ_n 1{K ≥ 2^n a₀} (2^{n+1}(1 + a₀))^q`,
and each term is `≤ (2(1 + a₀))^q 2^{-n}` by `bond_opNorm_tail_exp` and `q ≤ W`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## Nets and dimension counts
-/

/-- `1/4`-net of the unit sphere of `EuclideanSpace ℂ ι` with `|N| ≤ 12^(2 |ι|)`
(`exists_sphere_net_euclidean` at `ε = 1/4`; real dimension `2 |ι|`). -/
theorem bond_exists_net (ι : Type*) [Fintype ι] :
    ∃ N : Finset (EuclideanSpace ℂ ι), (∀ u ∈ N, ‖u‖ = 1) ∧
      (N.card : ℝ) ≤ 12 ^ (2 * Fintype.card ι) ∧
      ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ 1 / 4 := by
  obtain ⟨N, h1, h2, h3⟩ :=
    exists_sphere_net_euclidean (ι := ι) (ε := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨N, h1, ?_, h3⟩
  have h12 : (3 : ℝ) / (1 / 4) = 12 := by norm_num
  rwa [h12] at h2

/-- `|PhysSite W σ| = blocks · W ≤ 2W`. -/
theorem bond_card_physSite_le (W : ℕ) (σ : LayerShape) :
    Fintype.card (PhysSite W σ) ≤ 2 * W := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  cases σ <;> simp only [LayerShape.blocks] <;> omega

/-- `|PortSite W σ| = ports · W ≤ 2W`. -/
theorem bond_card_portSite_le (W : ℕ) (σ : LayerShape) :
    Fintype.card (PortSite W σ) ≤ 2 * W := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  cases σ <;> simp only [LayerShape.ports] <;> omega

/-- `12 ≤ e³`. -/
theorem bond_twelve_le_exp_three : (12 : ℝ) ≤ Real.exp 3 := by
  have he := Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  calc (12 : ℝ) ≤ 2.7182818283 ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3

/-- The net cardinality factor is at most `e^{24 W}`. -/
theorem bond_net_factor_le (W : ℕ) (σ : LayerShape) :
    (12 : ℝ) ^ (2 * (Fintype.card (PhysSite W σ) + Fintype.card (PortSite W σ))) ≤
      Real.exp (24 * W) := by
  have hP := bond_card_physSite_le W σ
  have hQ := bond_card_portSite_le W σ
  set d := 2 * (Fintype.card (PhysSite W σ) + Fintype.card (PortSite W σ)) with hd
  have hd8 : (d : ℝ) ≤ 8 * W := by
    have : d ≤ 8 * W := by omega
    exact_mod_cast this
  calc (12 : ℝ) ^ d ≤ Real.exp 3 ^ d := pow_le_pow_left₀ (by norm_num) bond_twelve_le_exp_three d
    _ = Real.exp (d * 3) := (Real.exp_nat_mul 3 d).symm
    _ ≤ Real.exp (24 * W) := Real.exp_le_exp.mpr (by linarith)

/-!
## Tails
-/

/-- **Operator-norm tail of the bond matrix, unconditional** (law `layerLaw W b σ`,
`E|B_ij|² = b/W`, `ℓ²` operator norm): for every shape, `W ≥ 1`, `b > 0`, `a > 0`,
`P(‖bondMatrix σ ω.2‖ ≥ a) ≤ 12^(2(|Phys| + |Port|)) exp(-a² W/(4b))`. -/
theorem bond_opNorm_tail (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    {a : ℝ} (ha : 0 < a) :
    layerLaw W b σ {ω | a ≤ ‖bondMatrix σ ω.2‖} ≤
      ENNReal.ofReal ((12 : ℝ) ^ (2 * (Fintype.card (PhysSite W σ) +
        Fintype.card (PortSite W σ))) * Real.exp (-(a ^ 2 * W) / (4 * b))) := by
  obtain ⟨Nu, hNu1, hNuc, hNu⟩ := bond_exists_net (PhysSite W σ)
  obtain ⟨Nw, hNw1, hNwc, hNw⟩ := bond_exists_net (PortSite W σ)
  refine (layerLaw_bondMatrix_opNorm_tail_of_net σ hW hb Nu Nw hNu1 hNw1 hNu hNw ha).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_add, pow_add]
  gcongr

/-- **Exponential form of the tail** (law `layerLaw W b σ`, `E|B_ij|² = b/W`, `ℓ²` operator norm;
uniform in `σ`, `W ≥ 1`): `P(‖bondMatrix σ ω.2‖ ≥ a) ≤ exp(W (24 - a²/(4b)))` for `b > 0`,
`a > 0`. -/
theorem bond_opNorm_tail_exp (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ} (hb : 0 < b)
    {a : ℝ} (ha : 0 < a) :
    layerLaw W b σ {ω | a ≤ ‖bondMatrix σ ω.2‖} ≤
      ENNReal.ofReal (Real.exp (W * (24 - a ^ 2 / (4 * b)))) := by
  refine (bond_opNorm_tail σ hW hb ha).trans (ENNReal.ofReal_le_ofReal ?_)
  calc (12 : ℝ) ^ (2 * (Fintype.card (PhysSite W σ) + Fintype.card (PortSite W σ))) *
        Real.exp (-(a ^ 2 * W) / (4 * b))
      ≤ Real.exp (24 * W) * Real.exp (-(a ^ 2 * W) / (4 * b)) := by
        gcongr; exact bond_net_factor_le W σ
    _ = Real.exp (W * (24 - a ^ 2 / (4 * b))) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **Sub-Gaussian tail of the bond norm** (law `layerLaw W b σ`, `E|B_ij|² = b/W`, `ℓ²` operator
norm; uniform in `σ`, `W ≥ 1`): with `a₀ = 10 √b`, for every `s ≥ 0`,
`P(‖bondMatrix σ ω.2‖ ≥ 10 √b + s) ≤ exp(-W (1 + s²/(4b)))`. -/
theorem bond_opNorm_tail_subGaussian (σ : LayerShape) {W : ℕ} (hW : 0 < W) {b : ℝ}
    (hb : 0 < b) {s : ℝ} (hs : 0 ≤ s) :
    layerLaw W b σ {ω | 10 * Real.sqrt b + s ≤ ‖bondMatrix σ ω.2‖} ≤
      ENNReal.ofReal (Real.exp (-(W * (1 + s ^ 2 / (4 * b))))) := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  refine (bond_opNorm_tail_exp σ hW hb (by positivity)).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hx : 100 * b + s ^ 2 ≤ (10 * Real.sqrt b + s) ^ 2 := by nlinarith
  have h25 : 25 + s ^ 2 / (4 * b) ≤ (10 * Real.sqrt b + s) ^ 2 / (4 * b) := by
    have : 25 + s ^ 2 / (4 * b) = (100 * b + s ^ 2) / (4 * b) := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right hx (by positivity)
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have : 24 - (10 * Real.sqrt b + s) ^ 2 / (4 * b) ≤ -(1 + s ^ 2 / (4 * b)) := by linarith
  nlinarith

/-!
## Measurability
-/

/-- The bond matrix is measurable in the Gaussian coordinates (entrywise). -/
theorem bond_measurable_bondMatrix {W : ℕ} (σ : LayerShape) :
    Measurable (fun ω : LayerSample W σ => bondMatrix σ ω.2) := by
  have hcoordB : ∀ (a : Fin σ.blocks) (k : Fin σ.ports) (i j : Fin W),
      Measurable (fun ω : LayerSample W σ => ω.2 a k i j) := fun a k i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply k).comp ((measurable_pi_apply a).comp measurable_snd)))
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
  unfold bondMatrix
  split_ifs
  · exact hcoordB _ _ _ _
  · exact measurable_const

/-- **The bond norm is measurable**: `ω ↦ ‖bondMatrix σ ω.2‖` (`ℓ²` operator norm) is Borel. -/
theorem bond_measurable_opNorm {W : ℕ} (σ : LayerShape) :
    Measurable (fun ω : LayerSample W σ => ‖bondMatrix σ ω.2‖) :=
  continuous_norm.measurable.comp (bond_measurable_bondMatrix σ)

/-!
## Moments
-/

/-- `layerLaw W b σ` is a probability measure. -/
theorem bond_isProbabilityMeasure_layerLaw (W : ℕ) (b : ℝ) (σ : LayerShape) :
    IsProbabilityMeasure (layerLaw W b σ) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold layerLaw
  infer_instance

/-- The moment constant `C₂(b) = 6 (1 + 10 √b)`. -/
def bondMomentConst (b : ℝ) : ℝ := 6 * (1 + 10 * Real.sqrt b)

theorem bondMomentConst_pos (b : ℝ) : 0 < bondMomentConst b := by
  unfold bondMomentConst; positivity

/-- Deterministic dyadic layer cake: for `K ≥ 0`, `a₀ > 0`, `q ≥ 0`,
`(1 + K)^q ≤ (1 + a₀)^q + Σ_n 1{2^n a₀ ≤ K} (2^{n+1}(1 + a₀))^q`. -/
theorem bond_rpow_le_tsum {K a₀ q : ℝ} (hK : 0 ≤ K) (ha : 0 < a₀) (hq : 0 ≤ q) :
    ENNReal.ofReal ((1 + K) ^ q) ≤ ENNReal.ofReal ((1 + a₀) ^ q) +
      ∑' n : ℕ, if (2 : ℝ) ^ n * a₀ ≤ K then
        ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) else 0 := by
  classical
  by_cases hKa : K < a₀
  · refine le_trans ?_ le_self_add
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith) (by linarith) hq)
  · push Not at hKa
    have hex : ∃ n : ℕ, K < 2 ^ n * a₀ := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K / a₀) (by norm_num : (1 : ℝ) < 2)
      exact ⟨n, by rwa [div_lt_iff₀ ha] at hn⟩
    have hnK : K < 2 ^ (Nat.find hex) * a₀ := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hnK
      linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hmK : (2 : ℝ) ^ m * a₀ ≤ K := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      push Not at this
      exact this
    rw [hm] at hnK
    refine le_trans ?_ le_add_self
    refine le_trans ?_ (ENNReal.le_tsum m)
    simp only [hmK, ↓reduceIte]
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by linarith) ?_ hq)
    have h1 : (1 : ℝ) ≤ 2 ^ (m + 1) := one_le_pow₀ (by norm_num)
    have h2 : K < 2 ^ (m + 1) * a₀ := hnK
    calc 1 + K ≤ 2 ^ (m + 1) + 2 ^ (m + 1) * a₀ := add_le_add h1 h2.le
      _ = 2 ^ (m + 1) * (1 + a₀) := by ring

/-- One dyadic term: `(2^{n+1}(1+a₀))^q exp(W(24 - (2^n a₀)²/(4b))) ≤ (2(1+a₀))^q 2^{-n}` for
`a₀ = 10 √b`, `b > 0`, `1 ≤ q ≤ W`. -/
theorem bond_dyadic_term_le {W : ℕ} {b q : ℝ} (hb : 0 < b) (hq1 : 1 ≤ q) (hqW : q ≤ W)
    (n : ℕ) :
    ((2 : ℝ) ^ (n + 1) * (1 + 10 * Real.sqrt b)) ^ q *
        Real.exp (W * (24 - ((2 : ℝ) ^ n * (10 * Real.sqrt b)) ^ 2 / (4 * b))) ≤
      (2 * (1 + 10 * Real.sqrt b)) ^ q * (1 / 2) ^ n := by
  set a₀ := 10 * Real.sqrt b with ha₀
  set t : ℝ := 2 ^ n with ht
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have ha0 : 0 ≤ a₀ := by positivity
  have ht1 : 1 ≤ t := one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  -- `(t a₀)²/(4b) = 25 t²`
  have hexp : (t * a₀) ^ 2 / (4 * b) = 25 * t ^ 2 := by
    rw [ha₀, mul_pow, mul_pow, hsq]; field_simp; ring
  -- exponent `≤ -q t²`
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hexpo : (W : ℝ) * (24 - (t * a₀) ^ 2 / (4 * b)) ≤ -t ^ 2 * q := by
    rw [hexp]
    have h1 : 24 - 25 * t ^ 2 ≤ -t ^ 2 := by nlinarith
    have h2 : (W : ℝ) * (24 - 25 * t ^ 2) ≤ W * (-t ^ 2) := mul_le_mul_of_nonneg_left h1 hW0
    have h3 : (W : ℝ) * (-t ^ 2) ≤ q * (-t ^ 2) :=
      mul_le_mul_of_nonpos_right hqW (by nlinarith)
    linarith
  have he : Real.exp (-t ^ 2) ≤ (t ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (t ^ 2)])
  have hbase : (2 : ℝ) ^ (n + 1) * (1 + a₀) * Real.exp (-t ^ 2) ≤ 2 * (1 + a₀) * (1 / 2) ^ n := by
    calc (2 : ℝ) ^ (n + 1) * (1 + a₀) * Real.exp (-t ^ 2)
        = 2 * (1 + a₀) * t * Real.exp (-t ^ 2) := by rw [ht, pow_succ]; ring
      _ ≤ 2 * (1 + a₀) * t * (t ^ 2)⁻¹ := by gcongr
      _ = 2 * (1 + a₀) * (1 / 2) ^ n := by
        rw [_root_.one_div_pow, ← ht]; field_simp
  have hhalf0 : (0 : ℝ) < (1 / 2) ^ n := by positivity
  have hhalf1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc ((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q * Real.exp (W * (24 - (t * a₀) ^ 2 / (4 * b)))
      ≤ ((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q * Real.exp (-t ^ 2 * q) := by
        gcongr
    _ = ((2 : ℝ) ^ (n + 1) * (1 + a₀) * Real.exp (-t ^ 2)) ^ q := by
        rw [Real.exp_mul, ← Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (2 * (1 + a₀) * (1 / 2) ^ n) ^ q :=
        Real.rpow_le_rpow (by positivity) hbase hq0
    _ = (2 * (1 + a₀)) ^ q * ((1 / 2) ^ n) ^ q :=
        Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (2 * (1 + a₀)) ^ q * (1 / 2) ^ n := by
        gcongr
        calc (((1 : ℝ) / 2) ^ n) ^ q ≤ ((1 / 2) ^ n) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hhalf0 hhalf1 hq1
          _ = (1 / 2) ^ n := Real.rpow_one _

/-- **Moments of the bond norm** (the `‖K‖_{L^q} ≤ C_b(1 + √(q/W))` step in the range `q ≤ W`).
Law `layerLaw W b σ` (`E|B_ij|² = b/W`), `K = ‖bondMatrix σ ω.2‖` the `ℓ²` operator norm. For every
shape `σ`, `b > 0` and real `1 ≤ q ≤ W`: `E (1 + K)^q ≤ C₂(b)^q`,
`C₂(b) = bondMomentConst b = 6 (1 + 10 √b)`, uniformly in `W`, `σ`, `q`. -/
theorem bond_lintegral_rpow_le (σ : LayerShape) {W : ℕ} {b : ℝ} (hb : 0 < b) {q : ℝ}
    (hq1 : 1 ≤ q) (hqW : q ≤ W) :
    ∫⁻ ω, ENNReal.ofReal ((1 + ‖bondMatrix σ ω.2‖) ^ q) ∂layerLaw W b σ ≤
      ENNReal.ofReal (bondMomentConst b ^ q) := by
  have hW : 0 < W := by
    have : (1 : ℝ) ≤ W := hq1.trans hqW
    exact_mod_cast this
  have := bond_isProbabilityMeasure_layerLaw W b σ
  set μ := layerLaw W b σ with hμ
  set K : LayerSample W σ → ℝ := fun ω => ‖bondMatrix σ ω.2‖ with hK
  set a₀ := 10 * Real.sqrt b with ha₀
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ha0 : 0 < a₀ := by positivity
  have hq0 : 0 ≤ q := by linarith
  have hKm : Measurable K := bond_measurable_opNorm σ
  set S : ℕ → Set (LayerSample W σ) := fun n => {ω | (2 : ℝ) ^ n * a₀ ≤ K ω} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n => measurableSet_le measurable_const hKm
  set d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) with hd
  set D : ℝ := (2 * (1 + a₀)) ^ q with hD
  have hpt : ∀ ω, ENNReal.ofReal ((1 + K ω) ^ q) ≤
      ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω := by
    intro ω
    refine (bond_rpow_le_tsum (norm_nonneg _) ha0 hq0).trans (le_of_eq ?_)
    congr 1
  have hterm : ∀ n, d n * μ (S n) ≤ ENNReal.ofReal D * 2⁻¹ ^ n := by
    intro n
    have htail := bond_opNorm_tail_exp σ hW hb (a := (2 : ℝ) ^ n * a₀) (by positivity)
    calc d n * μ (S n)
        ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q) *
            ENNReal.ofReal (Real.exp (W * (24 - ((2 : ℝ) ^ n * a₀) ^ 2 / (4 * b)))) := by
          gcongr
      _ = ENNReal.ofReal (((2 : ℝ) ^ (n + 1) * (1 + a₀)) ^ q *
            Real.exp (W * (24 - ((2 : ℝ) ^ n * a₀) ^ 2 / (4 * b)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (D * (1 / 2) ^ n) :=
          ENNReal.ofReal_le_ofReal (bond_dyadic_term_le hb hq1 hqW n)
      _ = ENNReal.ofReal D * 2⁻¹ ^ n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), one_div,
            ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, ENNReal.ofReal ((1 + K ω) ^ q) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, (S n).indicator (fun _ => d n) ω) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((1 + a₀) ^ q) * μ Set.univ +
          ∑' n, ∫⁻ ω, (S n).indicator (fun _ => d n) ω ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum fun n => (measurable_const.indicator (hSm n)).aemeasurable]
    _ = ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, d n * μ (S n) := by
        rw [measure_univ, mul_one]
        congr 1
        exact tsum_congr fun n => lintegral_indicator_const (hSm n) _
    _ ≤ ENNReal.ofReal ((1 + a₀) ^ q) + ∑' n, ENNReal.ofReal D * 2⁻¹ ^ n := by
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal ((1 + a₀) ^ q + 2 * D) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat, mul_comm (2 : ℝ≥0∞)]
    _ ≤ ENNReal.ofReal (bondMomentConst b ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (1 + a₀) ^ q ≤ D := Real.rpow_le_rpow (by positivity) (by linarith) hq0
        have h3 : (3 : ℝ) ≤ 3 ^ q := by
          calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
            _ ≤ 3 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
        have hC : bondMomentConst b ^ q = 3 ^ q * D := by
          rw [hD, ← Real.mul_rpow (by norm_num) (by positivity)]
          unfold bondMomentConst
          congr 1
          ring
        have hD0 : 0 ≤ D := by positivity
        rw [hC]
        nlinarith

/-- **`L^q` form of the bond moment bound** (law `layerLaw W b σ`, `E|B_ij|² = b/W`, `ℓ²` operator
norm): for every shape, `b > 0` and real `1 ≤ q ≤ W`,
`‖1 + ‖bondMatrix σ ω.2‖‖_{L^q(layerLaw W b σ)} ≤ C₂(b) = 6 (1 + 10 √b)`, uniformly in `W`, `σ`,
`q`. -/
theorem bond_eLpNorm_le (σ : LayerShape) {W : ℕ} {b : ℝ} (hb : 0 < b) {q : ℝ}
    (hq1 : 1 ≤ q) (hqW : q ≤ W) :
    eLpNorm (fun ω : LayerSample W σ => 1 + ‖bondMatrix σ ω.2‖) (ENNReal.ofReal q)
      (layerLaw W b σ) ≤ ENNReal.ofReal (bondMomentConst b) := by
  have hq0 : 0 < q := by linarith
  have hp0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq0
  have hm : Measurable (fun ω : LayerSample W σ => 1 + ‖bondMatrix σ ω.2‖) :=
    measurable_const.add (bond_measurable_opNorm σ)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0.le]
  have hint : ∫⁻ ω, ‖1 + ‖bondMatrix σ ω.2‖‖ₑ ^ q ∂layerLaw W b σ =
      ∫⁻ ω, ENNReal.ofReal ((1 + ‖bondMatrix σ ω.2‖) ^ q) ∂layerLaw W b σ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le]
  rw [hint]
  have hC := bondMomentConst_pos b
  calc (∫⁻ ω, ENNReal.ofReal ((1 + ‖bondMatrix σ ω.2‖) ^ q) ∂layerLaw W b σ) ^ (1 / q)
      ≤ ENNReal.ofReal (bondMomentConst b ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (bond_lintegral_rpow_le σ hb hq1 hqW) (by positivity)
    _ = ENNReal.ofReal (bondMomentConst b) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul hC.le, mul_one_div_cancel hq0.ne', Real.rpow_one]

end BlockBand.Layers
