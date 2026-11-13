module

public import BlockBand.Endpoints.Clock.OpenInputsBUniformStep

/-!
# The open-inputs lemma, uniformly in `b`: the radius of the conditional clock-moment step

In `main_moment_unif` the single constant `A` of
`E u₊^{n+2} ≤ (1 + Aδ₀ + A/W) u^{n+2} + B(u^{n+1}+1)` is the sum of the clock-mean part
`A₁ = (n+2) 2^{n+2} C₁` (`C₁` from the clock-mean bound) and of a noise part containing the
`clockNoise`/`unrestricted` constant `Cp` of the weighted-layer lemma. The noise part is needed
only in front of `1/W` (`main_algebra` adds it to the `δ₀` coefficient as slack).
The weight `K = 2A/(1-q)` enters the radius `r₁ ≤ 1/(K+1)` of `clockStep_weighted_unif`, so the
noise constant `Cp`, which `LayersBUniformHyp` does not make `b`-uniform, would enter `ε`.
Here the two parts are kept apart:
* `main_algebra_split`: `main_algebra` with conclusion
  `(1 + A₁ δ + A₂/W) u^{n+2} + B(u^{n+1}+1)`, `A₂ = A₁ + (noise part)`;
* `weighted_algebra_split`: `weighted_algebra` at `A = A₁` (so `K = 2A₁/(1-q)`),
  with the extra `(A₂-A₁)/W` term absorbed into the constant `C`;
* `clockStep_weighted_unifB`: the weighted clause of `ClockStepBound` with `r₁` before `b`
  (`r₁ = min(r₀, dstar, 1, 1/(K+1))`, `r₀, q` from `delta_next_unifB`), `K, C, W₀` after `b`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
  BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix ComplexOrder Matrix.Norms.L2Operator

namespace MovingEnergy

open OpenInputsProof

/-- The real algebra of the main moment bound with the clock-mean part
`A₁ = (n+2) 2^{n+2} C₁` of the `δ` coefficient separated from the noise part, which appears only
in front of `1/W` (`OpenInputsProof.main_algebra` without its slack term). -/
theorem main_algebra_split (n : ℕ) {u m δ W C₁ Cp Bι : ℝ} (hu : 0 ≤ u) (hm0 : 0 ≤ m)
    (hm : m ≤ (1 + C₁ * δ + C₁ / W ^ 2) * u) (hC₁ : 0 ≤ C₁) (hδ : 0 ≤ δ) (hW : 1 ≤ W)
    (hsmall : C₁ * δ + C₁ / W ^ 2 ≤ 1) (hCp : 0 ≤ Cp) (hBι : 0 ≤ Bι) :
    m ^ (n + 2) + ((n : ℝ) + 2) * m ^ (n + 1) * Bι +
        2 ^ (n + 2) * (m ^ n * (Cp * u / Real.sqrt W + Bι) ^ 2 +
          (Cp * u / Real.sqrt W + Bι) ^ (n + 2)) ≤
      (1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * δ +
          (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) / W) * u ^ (n + 2) +
        (((n : ℝ) + 2) * 2 ^ (n + 1) * Bι +
          2 ^ (n + 2) * (2 ^ (n + 1) * Bι ^ 2 + 2 ^ (n + 2) * Bι ^ (n + 2))) *
          (u ^ (n + 1) + 1) := by
  have hW0 : 0 < W := by linarith
  set x := C₁ * δ + C₁ / W ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  set U := u ^ (n + 2) with hU
  set V := u ^ (n + 1) + 1 with hV
  have hU0 : 0 ≤ U := by positivity
  have hV1 : 1 ≤ V := by have := pow_nonneg hu (n + 1); linarith
  have hmu : m ≤ (1 + x) * u := by rw [hx, ← add_assoc]; exact hm
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
  have hgoal : (1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * δ +
          (((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ +
          2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2))) / W) * U =
      U + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (δ * U) + ((n : ℝ) + 2) * 2 ^ (n + 2) * C₁ * (U / W) +
        2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)) * (U / W) := by
    ring
  rw [hgoal]
  have e1 : (1 + ((n : ℝ) + 2) * 2 ^ (n + 2) * x) * U =
      U + ((n : ℝ) + 2) * 2 ^ (n + 2) * x * U := by
    ring
  rw [e1] at hT1
  linarith only [hT1, hT1', hT2, hT34]

/-- The real algebra of the weighted step with the `δ` coefficient `A₁` and the `1/W`
coefficient `A₂ ≥ A₁` of the main moment bound separated: the weight is `K = 2A₁/(1-q)` and the
extra `(A₂-A₁)/W` term is absorbed into the constant (from `weighted_algebra` at
`A = A₁`). -/
theorem weighted_algebra_split {U U2 V δ q K A₁ A₂ B W C₂ Cn Cc : ℝ} (hU : 0 ≤ U) (hV : 1 ≤ V)
    (hU2 : U2 = U ^ 2) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hKqδ : K * q * δ ≤ 1) (hq0 : 0 ≤ q)
    (hK0 : 0 ≤ K) (hK : K = K * q + 2 * A₁) (hA : 0 ≤ A₁) (hA₁₂ : A₁ ≤ A₂) (hB : 0 ≤ B)
    (hW : 1 ≤ W) (hC₂ : 0 ≤ C₂) (hCn : 0 ≤ Cn) (hCc : 0 ≤ Cc) :
    (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A₁ * δ + A₂ / W) * U + B * V) +
        K * (W * (U + 1)) / 2 * (Cn / W ^ 2) + K / (2 * (W * (U + 1))) * (Cc * (U2 + 1)) ≤
      (1 + (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B +
          (2 + K * C₂) * (A₂ - A₁)) / W) * (1 + K * δ) * U +
        (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B +
          (2 + K * C₂) * (A₂ - A₁)) * V := by
  have h := weighted_algebra hU hV hU2 hδ0 hδ1 hKqδ hq0 hK0 hK hA hB hW hC₂ hCn hCc
  have hW0 : 0 < W := by linarith
  have hc0 : 1 + K * q * δ + K * C₂ / W ^ 2 ≤ 2 + K * C₂ := by
    have : K * C₂ / W ^ 2 ≤ K * C₂ := div_le_self (mul_nonneg hK0 hC₂) (by nlinarith)
    linarith
  have hd0 : 0 ≤ (A₂ - A₁) / W * U := by
    have : 0 ≤ A₂ - A₁ := by linarith
    positivity
  have hKδ : 1 ≤ 1 + K * δ := by have := mul_nonneg hK0 hδ0; linarith
  have hG0 : 0 ≤ (2 + K * C₂) * (A₂ - A₁) := by
    have : 0 ≤ A₂ - A₁ := by linarith
    positivity
  have h1 : (1 + K * q * δ + K * C₂ / W ^ 2) * ((A₂ - A₁) / W * U) ≤
      (2 + K * C₂) * (A₂ - A₁) / W * ((1 + K * δ) * U) := by
    have e : (2 + K * C₂) * (A₂ - A₁) / W * ((1 + K * δ) * U) =
        (2 + K * C₂) * ((A₂ - A₁) / W * U) * (1 + K * δ) := by ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_right hc0 hd0
    have h3 : 0 ≤ (2 + K * C₂) * ((A₂ - A₁) / W * U) := by
      have : 0 ≤ 2 + K * C₂ := by have := mul_nonneg hK0 hC₂; linarith
      positivity
    have h4 := le_mul_of_one_le_right h3 hKδ
    linarith
  have hGV : 0 ≤ (2 + K * C₂) * (A₂ - A₁) * V := by
    have : (0 : ℝ) ≤ V := by linarith
    positivity
  have eL : (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A₁ * δ + A₂ / W) * U + B * V) =
      (1 + K * q * δ + K * C₂ / W ^ 2) * ((1 + A₁ * δ + A₁ / W) * U + B * V) +
        (1 + K * q * δ + K * C₂ / W ^ 2) * ((A₂ - A₁) / W * U) := by
    field_simp; ring
  have eR : (1 + (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B +
          (2 + K * C₂) * (A₂ - A₁)) / W) * (1 + K * δ) * U +
        (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B +
          (2 + K * C₂) * (A₂ - A₁)) * V =
      ((1 + (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B) / W) *
          (1 + K * δ) * U +
        (2 * A₁ + K * C₂ * (1 + 2 * A₁) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B) * V) +
      (2 + K * C₂) * (A₂ - A₁) / W * ((1 + K * δ) * U) + (2 + K * C₂) * (A₂ - A₁) * V := by
    field_simp; ring
  rw [eL, eR]
  linarith

/-- **The main moment bound, `δ`-coefficient uniform in `b ∈ Icc β (1/2-β)`**
(`main_moment_unif` with `A` split): `dstar` and the `δ₀` coefficient `A₁` depend only on
`(β, κ, n)`; the `1/W` coefficient `A₂ ≥ A₁`, `B` and `W₀` depend on `b`. -/
theorem main_moment_unifB (hB : LayersBUniformHyp) (hWL : WeightedLayerContract)
    (hGA : GaussianAbsorptionContract) {β : ℝ} (hβ : 0 < β) (hβ4 : β < 1 / 4) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Kq : ℝ} (hKq : 0 ≤ Kq) (n : ℕ) :
    ∃ dstar A₁ : ℝ, 0 < dstar ∧ 0 ≤ A₁ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β),
      ∃ (A₂ B : ℝ) (W₀ : ℕ), A₁ ≤ A₂ ∧ 0 ≤ B ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ dstar →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal (nextClockU b E w X Y ω ^ (n + 2)) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + A₁ * jetDistance0 b E X + A₂ / W) * clockU Y ^ (n + 2) +
            B * (clockU Y ^ (n + 1) + 1)) := by
  obtain ⟨dstar₀, C₁, W₁, hd₀, hmean⟩ := onePortClockMeanB hB hGA hβ hβ4 hκ
  have hC₁0 : 0 ≤ max C₁ 0 := le_max_right _ _
  refine ⟨min dstar₀ (1 / (2 * max C₁ 0 + 1)), ((n : ℝ) + 2) * 2 ^ (n + 2) * max C₁ 0,
    lt_min hd₀ (by positivity), by positivity, fun b hb => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨Cp, CG, W₂, hCp, hCG, hing⟩ := ingredients_unif (onePortWeighted_of hWL hGA) hGA
    hb0 hb1 hκ hκ4 (P := n + 2) (by omega)
  refine ⟨((n : ℝ) + 2) * 2 ^ (n + 2) * max C₁ 0 +
      2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)),
    ((n : ℝ) + 2) * 2 ^ (n + 1) * (Kq * CG) +
      2 ^ (n + 2) * (2 ^ (n + 1) * (Kq * CG) ^ 2 + 2 ^ (n + 2) * (Kq * CG) ^ (n + 2)),
    max (max W₁ W₂) (⌈2 * max C₁ 0⌉₊ + 1), ?_, by positivity, ?_⟩
  · have : 0 ≤ 2 ^ (n + 2) * (2 ^ (n + 1) * Cp ^ 2 + 2 ^ (n + 2) * Cp ^ (n + 2)) := by
      positivity
    linarith
  intro W hW hW₀ E hEκ X hX hδ Y hY w hw hwK
  have hW1' : W₁ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hW₀)
  have hW2' : W₂ ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hW₀)
  have hW3 : 2 * max C₁ 0 + 1 ≤ (W : ℝ) := by
    have h := Nat.le_ceil (2 * max C₁ 0)
    have h2 : ((⌈2 * max C₁ 0⌉₊ + 1 : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (le_max_right _ _).trans hW₀
    push_cast at h h2; linarith
  have hWr1 : (1 : ℝ) ≤ W := by linarith
  have hWr : (0 : ℝ) < W := by linarith
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδd : jetDistance0 b E X ≤ dstar₀ := hδ.trans (min_le_left _ _)
  have hδs : jetDistance0 b E X ≤ 1 / (2 * max C₁ 0 + 1) := hδ.trans (min_le_right _ _)
  obtain ⟨hint, hm⟩ := hmean b hb W hW hW1' X hX E hEκ hδd Y hY
  obtain ⟨hξB, -, hιB⟩ := hing W hW hW2' E hEκ X hX Y hY
  have hu := clockU_nonneg hY
  have hm0 : 0 ≤ ∫ ω, clockT b E X Y ω ∂freshLaw W b :=
    integral_nonneg fun ω => clockT_nonneg X hY ω
  have hm' : ∫ ω, clockT b E X Y ω ∂freshLaw W b ≤
      (1 + max C₁ 0 * jetDistance0 b E X + max C₁ 0 / (W : ℝ) ^ 2) * clockU Y := by
    refine hm.trans (mul_le_mul_of_nonneg_right ?_ hu)
    have h1 : C₁ * jetDistance0 b E X ≤ max C₁ 0 * jetDistance0 b E X :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
    have h2 : C₁ / (W : ℝ) ^ 2 ≤ max C₁ 0 / (W : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  have hsmall : max C₁ 0 * jetDistance0 b E X + max C₁ 0 / (W : ℝ) ^ 2 ≤ 1 := by
    have h1 : max C₁ 0 * jetDistance0 b E X ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hδs
      nlinarith
    have h2 : max C₁ 0 / (W : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hξ0 : ∫ ω, (clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b) ∂freshLaw W b
      = 0 := by
    rw [integral_sub hint (integrable_const _), integral_const]; simp
  have hmb := moment_bound n hm0
    (ξ := fun ω => clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b)
    (ι := fun ω => w * cInj b E X ω) ((meas_clockT X Y).sub measurable_const).aestronglyMeasurable
    (measurable_const.mul (meas_cInj X)).aestronglyMeasurable hξ0
    (fun ω => by
      have := clockT_nonneg (b := b) (E := E) X hY ω
      have := mul_nonneg hw (cInj_nonneg (b := b) (E := E) X ω)
      linarith)
    (by positivity : 0 ≤ Cp * clockU Y / Real.sqrt W) (by positivity : 0 ≤ Kq * CG)
    hξB (eLpNorm_inj_le hw hwK hιB)
  have hpt : ∀ ω, (∫ ω', clockT b E X Y ω' ∂freshLaw W b) +
      ((clockT b E X Y ω - ∫ ω', clockT b E X Y ω' ∂freshLaw W b) + w * cInj b E X ω) =
        nextClockU b E w X Y ω := by
    intro ω; rw [nextClockU_eq]; ring
  simp only [hpt] at hmb
  refine hmb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact main_algebra_split n hu hm0 hm' hC₁0 hδ0 hWr1 hsmall hCp (by positivity)

/-- **The weighted clause of `ClockStepBound` with its radius uniform in `b ∈ Icc β (1/2-β)`**
(the `b`-uniform version of `clockStep_weighted_unif`): `r₁` depends only on
`(β, κ, Kq, P)`; the weight `K`, the constant `C` and `W₀` depend on `b`. -/
theorem clockStep_weighted_unifB (hB : LayersBUniformHyp) (hWL : WeightedLayerContract)
    (hGA : GaussianAbsorptionContract) (hTM : TraceMatrixContract) {β : ℝ} (hβ : 0 < β)
    (hβ4 : β < 1 / 4) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {Kq : ℝ} (hKq : 0 ≤ Kq) {P : ℕ}
    (hP : 2 ≤ P) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ b ∈ Set.Icc β (1 / 2 - β), ∃ (K C : ℝ) (W₀ : ℕ), 0 ≤ K ∧
      ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, X.IsHermitian → jetDistance0 b E X ≤ r₁ →
      ∀ Y : Matrix (Fin W) (Fin W) ℂ, Y.PosSemidef → ∀ w : ℝ, 0 ≤ w → w ≤ Kq →
        ∫⁻ ω, ENNReal.ofReal ((1 + K * jetDistance0 b E (freshSchur E X ω)) *
            nextClockU b E w X Y ω ^ P) ∂freshLaw W b ≤
          ENNReal.ofReal ((1 + C / W) * (1 + K * jetDistance0 b E X) * clockU Y ^ P +
            C * (clockU Y ^ (P - 1) + 1)) := by
  have hκ4 : κ < 4 := by linarith
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  obtain ⟨r₀, q, hr₀, hq0, hq1, hdel⟩ := delta_next_unifB hGA hTM hβ hκ hκ1
  obtain ⟨dstar, A, hd, hA, hmain⟩ := main_moment_unifB hB hWL hGA hβ hβ4 hκ hκ4 hKq n
  have h1q : 0 < 1 - q := by linarith
  set K := 2 * A / (1 - q) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : K = K * q + 2 * A := by rw [hKdef]; field_simp; ring
  refine ⟨min (min r₀ dstar) (min 1 (1 / (K + 1))),
    lt_min (lt_min hr₀ hd) (lt_min one_pos (by positivity)), fun b hb => ?_⟩
  obtain ⟨hb0, hb1, -⟩ := mem_IccB_facts hβ hb
  obtain ⟨C₂, Cn, Wd, hC₂, hCn, hdelb⟩ := hdel b hb
  obtain ⟨A₂, B, Wm, hA₂, hBn, hmainb⟩ := hmain b hb
  obtain ⟨Cc, Wc, hCc, hcrude⟩ := crude_bound_unif (onePortWeighted_of hWL hGA) hGA hb0 hb1 hκ
    hκ4 hKq (P := 2 * n + 4) (by omega)
  refine ⟨K, 2 * A + K * C₂ * (1 + 2 * A) + K * (Cn + Cc) / 2 + (2 + K * C₂) * B +
    (2 + K * C₂) * (A₂ - A), max (max Wd Wm) Wc, hK0, ?_⟩
  intro W hW hW₀ E hEκ X hX hδ Y hY w hw hwK
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
  obtain ⟨hstep, hN⟩ := hdelb W hW hWd E hEκ X hX
  have hstep' := hstep hδr
  have hM := hmainb W hW hWm E hEκ X hX hδd Y hY w hw hwK
  have hCr := hcrude W hW hWc E hEκ X hX Y hY w hw hwK
  have hu := clockU_nonneg hY
  have hA₂0 : 0 ≤ A₂ := hA.trans hA₂
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
    _ ≤ ENNReal.ofReal c₀ * ENNReal.ofReal ((1 + A * δ + A₂ / W) * U +
            B * (clockU Y ^ (n + 1) + 1)) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (Cn / (W : ℝ) ^ 2) +
          ENNReal.ofReal c₂ * ENNReal.ofReal (Cc * (clockU Y ^ (2 * n + 4) + 1)) := by
        gcongr
    _ = ENNReal.ofReal (c₀ * ((1 + A * δ + A₂ / W) * U + B * (clockU Y ^ (n + 1) + 1)) +
          c₁ * (Cn / (W : ℝ) ^ 2) + c₂ * (Cc * (clockU Y ^ (2 * n + 4) + 1))) := by
        rw [← ENNReal.ofReal_mul hc₀0, ← ENNReal.ofReal_mul hc₁0, ← ENNReal.ofReal_mul hc₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hU2 : clockU Y ^ (2 * n + 4) = U ^ 2 := by rw [hU, ← pow_mul]; ring_nf
        have hV1 : 1 ≤ clockU Y ^ (n + 1) + 1 := by have := pow_nonneg hu (n + 1); linarith
        have h := weighted_algebra_split (U2 := clockU Y ^ (2 * n + 4)) (Cn := Cn) (Cc := Cc)
          hU0 hV1 hU2 hδ0 hδ1 hKqδ hq0 hK0 hK hA hA₂ hBn hW1r hC₂ hCn hCc
        rw [hc₀, hc₁, hc₂, hlam]
        exact h

end MovingEnergy

end BlockBand.Endpoints.Clock
