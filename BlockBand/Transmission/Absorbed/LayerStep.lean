module

public import BlockBand.Transmission.LawFinite.InjectionMean
public import BlockBand.Transmission.LawFinite.Drift

/-!
# One absorbed fresh layer of the mass-moment recursion

The fresh layer of the absorbed path sees the input `X' = X - iε`, `0 ≤ ε ≤ K/W²`
(`LawFinite.absorbedInput`). The passive mass layer step `LengthUniform.massLayer_step_bulk` is
applied at `X'`, and the result is moved back
to `X` with the deterministic comparisons
* `q(X) ≤ (1+ε/η)²q(X')` (`passiveMass_le_absorb`), so `q(X)ⁿ ≤ 2q(X')ⁿ` for `W ≥ W₀`;
* `q(X') ≤ (1+ε/η)²q(X) + εW/η²` (`passiveMass_absorb_le`) and `q ≤ W/(4η)`, so
  `q(X') ≤ q(X) + B/W`, `B = 2K/η_κ²`: this is the injection `ε Tr C = O(1/W)`;
* `δ₀(X') ≤ δ₀(X) + ε/η²` (`jetDistance0_absorb_le`).

The injection `B/W` raises `q(X')ⁿ` by `O(qⁿ⁻¹/W)`. This is absorbed by half of the drift
`-c l qⁿ/W` for `l ≥ l₀` (`shift_absorb`, `absorbed_layer_alg`), at the price of a constant
`G/W`. So the absorbed step holds in the form of `massLayer_step_bulk` only for `l ≥ 2n/c` (not
for every `l ≥ 0`),
which is the range used by `SourceMixing.logistic_bound`.

* `shift_absorb`, `absorbed_layer_alg` (pure algebra);
* `absorbed_input_facts` (deterministic, bulk-uniform);
* **`absorbedLayer_step_bulk`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- `(m+1)B(q+B)^m ≤ 2(m+1)q^(m+1) + G_B`, `G_B = (m+1)B(2^m B + B)^m`. -/
theorem shift_absorb (m : ℕ) {B q : ℝ} (hB : 0 ≤ B) (hq : 0 ≤ q) :
    (m + 1) * B * (q + B) ^ m ≤
      2 * (m + 1) * q ^ (m + 1) + (m + 1) * B * (B * 2 ^ m + B) ^ m := by
  have hm : (0 : ℝ) ≤ m + 1 := by positivity
  have h5 : 0 ≤ (m + 1) * B * (B * 2 ^ m + B) ^ m := by positivity
  rcases le_or_gt (B * 2 ^ m) q with hq' | hq'
  · have hBq : B ≤ q :=
      le_trans (le_mul_of_one_le_right hB (one_le_pow₀ (by norm_num))) hq'
    have h1 : (q + B) ^ m ≤ (2 * q) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
    have h2 : (m + 1) * B * (q + B) ^ m ≤ (m + 1) * (B * 2 ^ m) * q ^ m := by
      calc (m + 1) * B * (q + B) ^ m ≤ (m + 1) * B * (2 * q) ^ m :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (m + 1) * (B * 2 ^ m) * q ^ m := by rw [mul_pow]; ring
    have h3 : (m + 1) * (B * 2 ^ m) * q ^ m ≤ (m + 1) * q * q ^ m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hm) (by positivity)
    have h4 : (m + 1) * q * q ^ m = (m + 1) * q ^ (m + 1) := by ring
    have h6 : 0 ≤ (m + 1) * q ^ (m + 1) := by positivity
    linarith
  · have h1 : (q + B) ^ m ≤ (B * 2 ^ m + B) ^ m :=
      pow_le_pow_left₀ (by positivity) (by linarith) m
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (m + 1) * B)
    have h6 : 0 ≤ 2 * (m + 1) * q ^ (m + 1) := by positivity
    linarith

/-- **The absorbed layer algebra.** With `qⁿ ≤ 2q'ⁿ`, `q' ≤ q + B/W` and the absorption bound
`hG` at `l₀ ≤ μ/2`, the step at `l = μ/2` from `q'` is a step at `μ` from `q` with drift
constant `c/4` and the extra constant `G`. Here `n = m + 1`. -/
theorem absorbed_layer_alg (m : ℕ) {c W q q' B G R l₀ μ : ℝ} (hc : 0 < c) (hW : 1 ≤ W)
    (hq : 0 ≤ q) (hq' : 0 ≤ q') (hB : 0 ≤ B) (hG0 : 0 ≤ G)
    (h2 : q ^ (m + 1) ≤ 2 * q' ^ (m + 1)) (hup : q' ≤ q + B / W)
    (hG : (m + 1) * B * (q + B) ^ m ≤ c * l₀ / 2 * q ^ (m + 1) + G)
    (hl0 : 0 ≤ l₀) (hl₀ : l₀ ≤ μ / 2) :
    q' ^ (m + 1) * (1 - c * (μ / 2) / W) + (c * (μ / 2) ^ (m + 1 + 1) + R) / W ≤
      q ^ (m + 1) * (1 - c / 4 * μ / W) + (c / 4 * μ ^ (m + 1 + 1) + (R + G)) / W := by
  have hW0 : 0 < W := by linarith
  have hμ : 0 ≤ μ := by linarith
  set u := c * (μ / 2) / W with hu
  have hu0 : 0 ≤ u := by positivity
  have hqn : 0 ≤ q ^ (m + 1) := by positivity
  have hdrift : c / 4 * μ / W = u / 2 := by rw [hu]; ring
  -- the error terms
  have herr : c * (μ / 2) ^ (m + 1 + 1) ≤ c / 4 * μ ^ (m + 1 + 1) := by
    have h4 : (4 : ℝ) ≤ 2 ^ (m + 1 + 1) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [div_pow]
    have hμp : 0 ≤ μ ^ (m + 1 + 1) := by positivity
    have : μ ^ (m + 1 + 1) / 2 ^ (m + 1 + 1) ≤ μ ^ (m + 1 + 1) / 4 :=
      div_le_div_of_nonneg_left hμp (by norm_num) h4
    nlinarith
  -- the main term
  have hmain : q' ^ (m + 1) * (1 - u) ≤ q ^ (m + 1) * (1 - u / 2) + G / W := by
    rcases le_or_gt u 1 with hu1 | hu1
    · have hBW : B / W ≤ B := div_le_self hB hW
      have hBW0 : 0 ≤ B / W := by positivity
      have hp1 : q' ^ (m + 1) ≤ (q + B / W) ^ (m + 1) := pow_le_pow_left₀ hq' hup _
      have hd := ma_pow_sub_pow_le m hq (by linarith : q ≤ q + B / W)
      have hd2 : (m + 1) * (q + B / W) ^ m * (q + B / W - q) ≤ (m + 1) * B * (q + B) ^ m / W := by
        have e : q + B / W - q = B / W := by ring
        rw [e]
        have : (q + B / W) ^ m ≤ (q + B) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        have e2 : (m + 1) * B * (q + B) ^ m / W = (m + 1) * (q + B) ^ m * (B / W) := by ring
        rw [e2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by positivity))
          (by positivity)
      have hGW : (m + 1) * B * (q + B) ^ m / W ≤ c * l₀ / 2 / W * q ^ (m + 1) + G / W := by
        have := div_le_div_of_nonneg_right hG hW0.le
        rw [add_div] at this
        calc (m + 1) * B * (q + B) ^ m / W ≤ c * l₀ / 2 * q ^ (m + 1) / W + G / W := this
          _ = c * l₀ / 2 / W * q ^ (m + 1) + G / W := by ring
      have hcl : c * l₀ / 2 / W ≤ u / 2 := by
        rw [hu]
        have : c * l₀ ≤ c * (μ / 2) := mul_le_mul_of_nonneg_left hl₀ hc.le
        have := div_le_div_of_nonneg_right this hW0.le
        calc c * l₀ / 2 / W = c * l₀ / W / 2 := by ring
          _ ≤ c * (μ / 2) / W / 2 := by linarith
      have h1u : 0 ≤ 1 - u := by linarith
      have hD : 0 ≤ (q + B / W) ^ (m + 1) - q ^ (m + 1) := by
        have := pow_le_pow_left₀ hq (by linarith : q ≤ q + B / W) (m + 1)
        linarith
      calc q' ^ (m + 1) * (1 - u) ≤ (q + B / W) ^ (m + 1) * (1 - u) :=
            mul_le_mul_of_nonneg_right hp1 h1u
        _ = q ^ (m + 1) * (1 - u) + ((q + B / W) ^ (m + 1) - q ^ (m + 1)) * (1 - u) := by ring
        _ ≤ q ^ (m + 1) * (1 - u) + ((q + B / W) ^ (m + 1) - q ^ (m + 1)) := by
            have : ((q + B / W) ^ (m + 1) - q ^ (m + 1)) * (1 - u) ≤
                (q + B / W) ^ (m + 1) - q ^ (m + 1) :=
              mul_le_of_le_one_right hD (by linarith)
            linarith
        _ ≤ q ^ (m + 1) * (1 - u) + (u / 2 * q ^ (m + 1) + G / W) := by
            have := mul_le_mul_of_nonneg_right hcl hqn
            linarith
        _ = q ^ (m + 1) * (1 - u / 2) + G / W := by ring
    · have hneg : 1 - u < 0 := by linarith
      have hp : q ^ (m + 1) / 2 ≤ q' ^ (m + 1) := by linarith
      have h3 : q' ^ (m + 1) * (1 - u) ≤ q ^ (m + 1) / 2 * (1 - u) :=
        mul_le_mul_of_nonpos_right hp hneg.le
      have hGW : 0 ≤ G / W := by positivity
      nlinarith
  rw [hdrift]
  have e1 : (c * (μ / 2) ^ (m + 1 + 1) + R) / W = c * (μ / 2) ^ (m + 1 + 1) / W + R / W := by
    rw [add_div]
  have e2 : (c / 4 * μ ^ (m + 1 + 1) + (R + G)) / W =
      c / 4 * μ ^ (m + 1 + 1) / W + R / W + G / W := by
    rw [add_div, add_div]; ring
  have herr' := div_le_div_of_nonneg_right herr hW0.le
  rw [e1, e2]
  linarith

/-- `(1+x)^(2n) ≤ 2` for `0 ≤ x`, `2nx ≤ 1/2`. -/
theorem one_add_pow_le_two {x : ℝ} (n : ℕ) (hx : 0 ≤ x) (hnx : 2 * n * x ≤ 1 / 2) :
    (1 + x) ^ (2 * n) ≤ 2 := by
  have h1 : (1 + x) ^ (2 * n) ≤ Real.exp x ^ (2 * n) :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) _
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp ((2 * n : ℕ) * x) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  have h3 : Real.exp (1 / 2) ≤ 2 := by
    have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have he := Real.exp_one_lt_d9
    have hp := Real.exp_pos (1 / 2)
    nlinarith
  linarith

/-- **The deterministic absorbed-input comparisons**, bulk-uniform: for `W ≥ W₀(n, K, κ')`,
passive `X`, `0 ≤ ε ≤ K/W²`, with `X' = X - iε` and `η_L = etaLow b κ'`:
`qc(X)ⁿ ≤ 2 qc(X')ⁿ`, `qc(X') ≤ qc(X) + (2K/η_L²)/W`, `Wδ₀(X') ≤ Wδ₀(X) + K/η_L²`. -/
theorem absorbed_input_facts {b κ' K : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ' : 0 < κ')
    (hK : 0 ≤ K) (n : ℕ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ', ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosSemidef → ∀ ε : ℝ, 0 ≤ ε → ε ≤ K / (W : ℝ) ^ 2 →
        qc b E X ^ n ≤ 2 * qc b E (absorbedInput X ε) ^ n ∧
        qc b E (absorbedInput X ε) ≤ qc b E X + 2 * K / etaLow b κ' ^ 2 / W ∧
        W * jetDistance0 b E (absorbedInput X ε) ≤
          W * jetDistance0 b E X + K / etaLow b κ' ^ 2 := by
  set ηL := etaLow b κ'
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ'
  refine ⟨⌈(4 * n + 1) * K / ηL⌉₊ + 1, fun W hW E hE X hY ε hε hεK => ?_⟩
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηle : ηL ≤ etaZ b E := etaLow_le (by linarith) hκ' hE
  set η := etaZ b E
  have hWc : (4 * n + 1) * K / ηL < W := by
    have := Nat.le_ceil ((4 * n + 1) * K / ηL)
    have : ((⌈(4 * n + 1) * K / ηL⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at this; linarith
  have hW1 : (1 : ℝ) ≤ W := by
    have : ((⌈(4 * n + 1) * K / ηL⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at this; linarith [Nat.cast_nonneg (α := ℝ) ⌈(4 * n + 1) * K / ηL⌉₊]
  have hW0 : (0 : ℝ) < W := by linarith
  have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  have hY' := passiveY_absorbedInput hY hε
  rw [qc_eq hY, qc_eq hY']
  have hq0 := passiveMass_nonneg b E hY
  have hq'0 := passiveMass_nonneg b E hY'
  set q := passiveMass b E X
  set q' := passiveMass b E (absorbedInput X ε)
  -- `x = ε/η ≤ K/(ηL W)`
  set x := ε / η with hx
  have hx0 : 0 ≤ x := by positivity
  have hεW : ε * W ≤ K / W := by
    rw [le_div_iff₀ hW0]
    calc ε * W * W = ε * (W : ℝ) ^ 2 := by ring
      _ ≤ K / (W : ℝ) ^ 2 * (W : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hεK (by positivity)
      _ = K := by field_simp
  have hxK : x ≤ K / (ηL * W) := by
    rw [hx, div_le_div_iff₀ hη (by positivity)]
    have : ε * W ≤ K / W := hεW
    have h3 : ε * (ηL * W) ≤ ε * (η * W) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηle hW0.le) hε
    have h4 : ε * (η * W) ≤ K / W * η := by nlinarith
    have h5 : K / W * η ≤ K * η := by
      have : K / W ≤ K := div_le_self hK hW1
      nlinarith
    linarith
  have hKW : K / (ηL * W) ≤ 1 / (4 * n + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_lt_iff₀ hηL] at hWc
    nlinarith
  have hnx : 2 * n * x ≤ 1 / 2 := by
    have : x ≤ 1 / (4 * n + 1) := hxK.trans hKW
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hx1 : x ≤ 1 := by
    have : x ≤ 1 / (4 * n + 1) := hxK.trans hKW
    have : 1 / (4 * (n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) n; linarith
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hle := passiveMass_le_absorb hb0 hb h1 h2 hY hε
    have hp : q ^ n ≤ ((1 + x) ^ 2 * q') ^ n := pow_le_pow_left₀ hq0 hle n
    rw [mul_pow, ← pow_mul] at hp
    have := one_add_pow_le_two n hx0 hnx
    calc q ^ n ≤ (1 + x) ^ (2 * n) * q' ^ n := hp
      _ ≤ 2 * q' ^ n := mul_le_mul_of_nonneg_right this (by positivity)
  · have hup : q' ≤ (1 + x) ^ 2 * q + ε * W / η ^ 2 := passiveMass_absorb_le hb0 hb h1 h2 hY hε
    have hqW : q ≤ W / (4 * η) := passiveMass_le_width (by linarith) h1 h2 X
    have hxq : x * q ≤ ε * W / (4 * η ^ 2) := by
      calc x * q ≤ x * (W / (4 * η)) := mul_le_mul_of_nonneg_left hqW hx0
        _ = ε * W / (4 * η ^ 2) := by rw [hx]; field_simp
    have e : (1 + x) ^ 2 * q = q + x * (2 + x) * q := by ring
    have hx3 : x * (2 + x) * q ≤ 3 * (x * q) := by
      have : x * (2 + x) ≤ 3 * x := by nlinarith
      nlinarith
    have hεη : ε * W / η ^ 2 ≤ K / ηL ^ 2 / W := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : ε * W * W ≤ K := by
        have := hεW; rw [le_div_iff₀ hW0] at this; linarith
      have h4 : ηL ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hηL.le hηle 2
      have h5 : ε * W * (ηL ^ 2 * W) ≤ K * η ^ 2 := by
        have : ε * W * (ηL ^ 2 * W) = (ε * W * W) * ηL ^ 2 := by ring
        rw [this]
        exact mul_le_mul h3 h4 (by positivity) hK
      linarith
    have e2 : 2 * K / ηL ^ 2 / W = 2 * (K / ηL ^ 2 / W) := by ring
    rw [e2]
    have h6 : ε * W / (4 * η ^ 2) = (ε * W / η ^ 2) / 4 := by ring
    rw [h6] at hxq
    have hT0 : 0 ≤ K / ηL ^ 2 / W := by positivity
    linarith
  · have hδ := jetDistance0_absorb_le hb0 hb h1 h2 hY hε
    have hεη : ε / η ^ 2 ≤ K / ηL ^ 2 / W := by
      have h4 : ηL ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hηL.le hηle 2
      have h3 : ε ≤ K / W := hεK.trans (div_le_div_of_nonneg_left hK hW0 hWW)
      calc ε / η ^ 2 ≤ (K / W) / η ^ 2 := div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ (K / W) / ηL ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) h4
        _ = K / ηL ^ 2 / W := by ring
    have h7 : (W : ℝ) * (K / ηL ^ 2 / W) = K / ηL ^ 2 := by field_simp
    have := mul_le_mul_of_nonneg_left (hδ.trans (add_le_add_right hεη _)) hW0.le
    change (W : ℝ) * jetDistance0 b E (absorbedInput X ε) ≤ _
    calc (W : ℝ) * jetDistance0 b E (absorbedInput X ε)
        ≤ W * (jetDistance0 b E X + K / ηL ^ 2 / W) := this
      _ = W * jetDistance0 b E X + K / ηL ^ 2 := by rw [mul_add, h7]

/-- **One absorbed fresh layer of the mass-moment recursion, bulk-uniform** (the absorbed
analogue of `LengthUniform.massLayer_step_bulk`): for every passive `X` and every absorption
`0 ≤ ε ≤ K/W²` of the fresh block, in the same form, for `l ≥ 2n/c`. -/
theorem absorbedLayer_step_bulk (hA : PassiveBoundsStatement) {b κ' K : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ' : 0 < κ') (hK : 0 ≤ K) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (c D₁ D₂ : ℝ) (W₀ : ℕ), 0 < c ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κ', ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ K / (W : ℝ) ^ 2 → ∀ l : ℝ, 2 * n / c ≤ l →
        ∫ ω, qc b E (freshSchur E (absorbedInput X ε) ω) ^ n ∂freshLaw W b ≤
          qc b E X ^ n * (1 - c * l / W) +
            (c * l ^ (n + 1) + D₁ + D₂ * (W * jetDistance0 b E X) ^ (n + 1)) / W := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, D₁, D₂, W₁, hc, hD₁, hD₂, hstep⟩ := LengthUniform.massLayer_step_bulk hA hb0 hb hκ'
    (m + 1) hn
  obtain ⟨W₂, hfacts⟩ := absorbed_input_facts hb0 hb hκ' hK (m + 1)
  set ηL := etaLow b κ'
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ'
  set B := 2 * K / ηL ^ 2
  have hB : 0 ≤ B := by positivity
  set K₁ := K / ηL ^ 2
  have hK₁ : 0 ≤ K₁ := by positivity
  set G := (m + 1) * B * (B * 2 ^ m + B) ^ m
  have hG0 : 0 ≤ G := by positivity
  refine ⟨c / 4, D₁ + G + D₂ * 2 ^ (m + 1) * K₁ ^ (m + 1 + 1), D₂ * 2 ^ (m + 1), max W₁ (max W₂ 1),
    by positivity, by positivity, by positivity, fun W hW E hE X hY ε hε hεK l hl => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW₁, hW₂, hW1⟩ := hW
  have hW1' : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  obtain ⟨hpow, hup, hδ⟩ := hfacts W hW₂ E hE X hY ε hε hεK
  have hY' := passiveY_absorbedInput hY hε
  set l₀ := 4 * ((m + 1 : ℕ) : ℝ) / c
  have hl0 : 0 ≤ l₀ := by positivity
  have hl₀ : l₀ ≤ l / 2 := by
    have e : 2 * ((m + 1 : ℕ) : ℝ) / (c / 4) = 2 * l₀ := by
      simp only [l₀]; field_simp
    rw [e] at hl; linarith
  have hcl : c * l₀ / 2 = 2 * ((m : ℝ) + 1) := by
    simp only [l₀]; push_cast; field_simp; norm_num
  have hGq : (m + 1) * B * (qc b E X + B) ^ m ≤ c * l₀ / 2 * qc b E X ^ (m + 1) + G := by
    rw [hcl]; exact shift_absorb m hB (qc_nonneg b E X)
  have h1 := hstep W hW₁ E hE (absorbedInput X ε) hY' (l / 2) (by linarith)
  have hδ0 : 0 ≤ (W : ℝ) * jetDistance0 b E (absorbedInput X ε) :=
    mul_nonneg hW0.le (norm_nonneg _)
  set R := D₁ + D₂ * ((W : ℝ) * jetDistance0 b E (absorbedInput X ε)) ^ (m + 1 + 1)
  have h2 := absorbed_layer_alg m (R := R) hc hW1' (qc_nonneg b E X)
    (qc_nonneg b E _) hB hG0 hpow hup hGq hl0 hl₀
  have hR : R ≤ D₁ + D₂ * (2 ^ (m + 1) *
      (((W : ℝ) * jetDistance0 b E X) ^ (m + 1 + 1) + K₁ ^ (m + 1 + 1))) := by
    have hp := pow_le_pow_left₀ hδ0 hδ (m + 1 + 1)
    have ha := add_pow_le (mul_nonneg hW0.le (show (0 : ℝ) ≤ jetDistance0 b E X from norm_nonneg _)) hK₁ (m + 1 + 1)
    rw [show m + 1 + 1 - 1 = m + 1 by omega] at ha
    have := mul_le_mul_of_nonneg_left (hp.trans ha) hD₂
    simp only [R]; linarith
  have h1' : ∫ ω, qc b E (freshSchur E (absorbedInput X ε) ω) ^ (m + 1) ∂freshLaw W b ≤
      qc b E (absorbedInput X ε) ^ (m + 1) * (1 - c * (l / 2) / W) +
        (c * (l / 2) ^ (m + 1 + 1) + R) / W := by
    refine h1.trans_eq ?_
    simp only [R]; ring
  refine h1'.trans (h2.trans ?_)
  have hfin : c / 4 * l ^ (m + 1 + 1) + (R + G) ≤ c / 4 * l ^ (m + 1 + 1) +
      (D₁ + G + D₂ * 2 ^ (m + 1) * K₁ ^ (m + 1 + 1)) +
      D₂ * 2 ^ (m + 1) * ((W : ℝ) * jetDistance0 b E X) ^ (m + 1 + 1) := by
    nlinarith
  have := div_le_div_of_nonneg_right hfin hW0.le
  have e : c / 4 * l / W = c / 4 * l / W := rfl
  linarith

end BlockBand.Transmission.Absorbed
