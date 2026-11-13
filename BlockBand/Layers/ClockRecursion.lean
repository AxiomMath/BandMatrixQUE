module

public import BlockBand.Layers.ClockPath

/-!
# One step of the clock recursion, conditional on the old path

Setting: one separate-port layer `ℓ ~ layerLaw W b .separate`, a deterministic Hermitian old
Schur matrix `X` and a deterministic old clock `Y ⪰ 0` (conditioning on the old path is Fubini),
`E ∈ bulkInterval κ`, `z = z_∂(E)`, `u = W⁻¹ Tr Y`, `δ = d(X)`, `δ₊ = d(X₊)`,
`X₊ = layerSchur .separate E X ℓ`; `t = W⁻¹ Tr L*YL` and `s = W⁻¹ Tr 𝒢₁₂* P 𝒢₁₂`.

* `clk_step_weighted`: for each integer `m ≥ 2` there are `K ≥ 0`, a radius
  `d₁ > 0` and `C` with
  `E[(1 + K δ₊) t^m] ≤ (1 + C/W)(1 + K δ) u^m` on `δ ≤ d₁`, `W ≥ W₀`.
  Proof: expanding `t^m` around its mean `μ = E t ≤ (1 + Cδ + CW⁻²)u` (the clock-mean identity), the
  linear centered term vanishes and the others cost `2^m(μ^{m-2} E η² + E|η|^m) ≤ C u^m/W`
  (the clock-noise bound, `clk_pow_expand`); then `δ₊ ≤ qδ + CW⁻² + ξ` (the one-step matched-trace recursion) and the
  correlated estimate `E[ξ t^m] ≤ ‖ξ‖₂ ‖t‖_{2m}^m ≤ C u^m/W` (Hölder; the `unrestricted`
  bound of the weighted-layer lemma); finally `K(1-q) > 2C` and the reduced radius `d₁ ≤ 1/K`
  give the polynomial inequality (`clk_poly_ineq`).
* `clk_step_source`: `E[(1 + K δ₊) s^n] ≤ B` for every Hermitian `X` (`s ≤ 2‖𝒢‖²`,
  `δ₊ ≤ (Im z)⁻¹ + 1`, the Gaussian absorption lemma).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. Real inequalities
-/

theorem clk_matchedDistance_nonneg (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    0 ≤ matchedDistance b E X :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem clk_pow_mul_pow_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) {k n : ℕ} (hk : k ≤ n) :
    a ^ k * c ^ (n - k) ≤ a ^ n + c ^ n := by
  have hM : a ^ k * c ^ (n - k) ≤ (max a c) ^ k * (max a c) ^ (n - k) :=
    mul_le_mul (pow_le_pow_left₀ ha (le_max_left _ _) k)
      (pow_le_pow_left₀ hc (le_max_right _ _) _) (by positivity)
      (pow_nonneg (ha.trans (le_max_left _ _)) _)
  rw [← pow_add, Nat.add_sub_cancel' hk] at hM
  rcases le_total a c with h | h
  · rw [max_eq_right h] at hM; linarith [pow_nonneg ha n]
  · rw [max_eq_left h] at hM; linarith [pow_nonneg hc n]

/-- **Expansion around the mean**: `(μ + η)^{n+2} ≤ μ^{n+2} + (n+2) μ^{n+1} η +
2^{n+2} (μ^n η² + |η|^{n+2})` for `μ ≥ 0`. -/
theorem clk_pow_expand {μ : ℝ} (hμ : 0 ≤ μ) (η : ℝ) (n : ℕ) :
    (μ + η) ^ (n + 2) ≤ μ ^ (n + 2) + (n + 2) * μ ^ (n + 1) * η +
      2 ^ (n + 2) * (μ ^ n * η ^ 2 + |η| ^ (n + 2)) := by
  rw [add_comm μ η, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have hsum : ∑ k ∈ Finset.range (n + 1), η ^ (k + 1 + 1) * μ ^ (n + 2 - (k + 1 + 1)) *
      ((n + 2).choose (k + 1 + 1) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), η ^ (k + 1 + 1) * μ ^ (n - k) *
      ((n + 2).choose (k + 1 + 1) : ℝ) :=
    Finset.sum_congr rfl fun k _ => by rw [show n + 2 - (k + 1 + 1) = n - k by omega]
  rw [hsum]
  have hR : ∀ k ∈ Finset.range (n + 1), η ^ (k + 1 + 1) * μ ^ (n - k) *
      ((n + 2).choose (k + 1 + 1) : ℝ) ≤
      ((n + 2).choose (k + 1 + 1) : ℝ) * (μ ^ n * η ^ 2 + |η| ^ (n + 2)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [mul_comm _ ((n + 2).choose (k + 1 + 1) : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 : η ^ (k + 1 + 1) ≤ |η| ^ (k + 1 + 1) := by
      rw [← abs_pow]; exact le_abs_self _
    have h2 := clk_pow_mul_pow_le (abs_nonneg η) hμ hkn
    have hη2 : |η| ^ (k + 1 + 1) = η ^ 2 * |η| ^ k := by
      rw [pow_succ, pow_succ, mul_assoc, abs_mul_abs_self, sq]; ring
    calc η ^ (k + 1 + 1) * μ ^ (n - k) ≤ |η| ^ (k + 1 + 1) * μ ^ (n - k) :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hμ _)
      _ = η ^ 2 * (|η| ^ k * μ ^ (n - k)) := by rw [hη2]; ring
      _ ≤ η ^ 2 * (|η| ^ n + μ ^ n) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = μ ^ n * η ^ 2 + |η| ^ (n + 2) := by
          rw [show |η| ^ (n + 2) = |η| ^ n * η ^ 2 by rw [pow_add, sq_abs]]; ring
  have hS := Finset.sum_le_sum hR
  rw [← Finset.sum_mul] at hS
  have hC : ∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 1 + 1) : ℝ) ≤ 2 ^ (n + 2) := by
    have h := Nat.sum_range_choose (n + 2)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    have h' : ∑ k ∈ Finset.range (n + 1), (n + 2).choose (k + 1 + 1) ≤ 2 ^ (n + 2) := by omega
    exact_mod_cast h'
  have hP : 0 ≤ μ ^ n * η ^ 2 + |η| ^ (n + 2) := by positivity
  have hb := mul_le_mul_of_nonneg_right hC hP
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add, pow_one,
    Nat.choose_one_right, Nat.sub_zero]
  have e1 : n + 2 - 1 = n + 1 := by omega
  rw [e1]
  push_cast
  linarith [hS, hb]

/-- `(1 + x)^m ≤ 1 + m (1 + x₀)^m x` for `0 ≤ x ≤ x₀`. -/
theorem clk_one_add_pow_le {x x₀ : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) :
    ∀ m : ℕ, (1 + x) ^ m ≤ 1 + m * (1 + x₀) ^ m * x
  | 0 => by simp
  | m + 1 => by
    have ih := clk_one_add_pow_le hx hxx m
    have h1 : (1 : ℝ) ≤ (1 + x₀) ^ m := one_le_pow₀ (by linarith)
    have h0 : (0 : ℝ) ≤ (1 + x₀) ^ m := by linarith
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [pow_succ, pow_succ]
    push_cast
    have hxm : 0 ≤ (m : ℝ) * (1 + x₀) ^ m * x := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hxx hxm, mul_le_mul_of_nonneg_right h1 hx,
      mul_le_mul_of_nonneg_left hxx (mul_nonneg h0 hx)]

/-!
## 2. Moments from `L^p` bounds
-/

theorem clk_lintegral_pow_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) {n : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f (ENNReal.ofReal n) ν ≤ ENNReal.ofReal B) :
    ∫⁻ x, ‖f x‖ₑ ^ n ∂ν ≤ ENNReal.ofReal (B ^ n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hn0)
    ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hn0.le] at h
  have h2 := ENNReal.rpow_le_rpow h hn0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hB] at h2
  simpa only [ENNReal.rpow_natCast] using h2

theorem clk_integral_pow_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) {n : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm f (ENNReal.ofReal n) ν ≤ ENNReal.ofReal B) :
    Integrable (fun x => |f x| ^ n) ν ∧ ∫ x, |f x| ^ n ∂ν ≤ B ^ n := by
  have hmem : MemLp f n ν := by
    rw [memLp_iff, ← ENNReal.ofReal_natCast]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hi := hmem.integrable_norm_pow (by omega)
  simp only [Real.norm_eq_abs] at hi
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hi.aestronglyMeasurable]
  have hl := clk_lintegral_pow_le hf hn hB h
  have e : ∀ x, ENNReal.ofReal (|f x| ^ n) = ‖f x‖ₑ ^ n := fun x => by
    rw [ENNReal.ofReal_pow (abs_nonneg _), Real.enorm_eq_ofReal_abs]
  simp_rw [e]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- **Correlated estimate**: `E[|f| |g|^m] ≤ ‖f‖₂ ‖g‖_{2m}^m` (Hölder). -/
theorem clk_lintegral_mul_pow_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) {m : ℕ} (hm : 1 ≤ m)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfA : eLpNorm f (ENNReal.ofReal 2) ν ≤ ENNReal.ofReal A)
    (hgB : eLpNorm g (ENNReal.ofReal ((2 * m : ℕ) : ℝ)) ν ≤ ENNReal.ofReal B) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ^ m ∂ν ≤ ENNReal.ofReal (A * B ^ m) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖ₑ) (g := fun x => ‖g x‖ₑ ^ m) hf.enorm (hg.enorm.pow_const m)
  refine hH.trans ?_
  have h1 : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal A := by
    have := hfA
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal (by norm_num)] at this
    exact this
  have h2 : (∫⁻ x, (‖g x‖ₑ ^ m) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (B ^ m) := by
    have hl := clk_lintegral_pow_le hg (n := 2 * m) (by omega) hB hgB
    have e : ∀ x, (‖g x‖ₑ ^ m) ^ (2 : ℝ) = ‖g x‖ₑ ^ (2 * m) := fun x => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, ← pow_mul, mul_comm]
    simp_rw [e]
    calc (∫⁻ x, ‖g x‖ₑ ^ (2 * m) ∂ν) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal (B ^ (2 * m)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hl (by norm_num)
      _ = ENNReal.ofReal (B ^ m) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), pow_mul',
            ← Real.rpow_natCast (B ^ m) 2, ← Real.rpow_mul (by positivity)]
          norm_num
  calc (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (∫⁻ x, (‖g x‖ₑ ^ m) ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))
      ≤ ENNReal.ofReal A * ENNReal.ofReal (B ^ m) := mul_le_mul' h1 h2
    _ = ENNReal.ofReal (A * B ^ m) := (ENNReal.ofReal_mul hA).symm

/-!
## 3. The injected source
-/

/-- **Injection step**: `E[(1 + K δ₊) s^n] ≤ B` for every Hermitian `X`,
every tag `τ`, `E ∈ I` and `W ≥ W₀`. -/
theorem clk_step_source (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ K : ℝ, 0 ≤ K → ∀ n : ℕ, 1 ≤ n →
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      ∀ τ : Fin 2 → Bool,
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj τ * clkG12 b E X ℓ)‖ₑ ^ n
          ∂layerLaw W b .separate ≤ ENNReal.ofReal B := by
  intro b hb0 hb1 κ hκ K hK n hn
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  set M0 := η₀⁻¹ + 1 with hM0
  refine ⟨(1 + K * M0) * (2 ^ n * CA ^ (2 * n)), ⌈2 * n / ε₁⌉₊, by positivity, ?_⟩
  intro W hW hWW X hX E hE τ
  obtain ⟨hz, hzM, hE2⟩ := hbulk E hE
  obtain ⟨-, hmom⟩ := habs W hW .separate X hX E (boundaryZ b E) hz hzM
  have hq2 : (2 * n : ℝ) ≤ ε₁ * W := by
    have h1 : 2 * n / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := hmom (2 * n) (by linarith) hq2
  have hGm := measurable_norm_layerResolvent .separate E (boundaryZ b E) X (W := W)
  have hl := clk_lintegral_pow_le hGm.aestronglyMeasurable (n := 2 * n) (by omega) hCA.le
    (by push_cast; exact hm)
  have hzpos : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ hz
  have hpt : ∀ᵐ ℓ ∂layerLaw W b .separate,
      ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
        ‖clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj τ * clkG12 b E X ℓ)‖ₑ ^ n ≤
      ENNReal.ofReal ((1 + K * M0) * 2 ^ n) *
        ‖‖layerResolvent .separate E (boundaryZ b E) X ℓ‖‖ₑ ^ (2 * n) := by
    filter_upwards [lct_ae_blocks_isHermitian W b .separate] with ℓ hA
    have hXp := srec_layerSchur_isHermitian E hX ℓ hA
    have hd := srec_matchedDistance_le (b := b) hE2 hzpos hXp
    have hd' : matchedDistance b E (layerSchur .separate E X ℓ) ≤ M0 :=
      hd.trans (by rw [hM0]; linarith [inv_anti₀ hη₀ hz])
    have hs0 := clkTrace_nonneg ((clkProj_posSemidef (W := W) τ).conjTranspose_mul_mul_same
      (clkG12 b E X ℓ))
    have hs := clkTrace_source_le τ (layerResolvent .separate E (boundaryZ b E) X ℓ)
    set G := layerResolvent .separate E (boundaryZ b E) X ℓ
    rw [Real.enorm_eq_ofReal hs0, Real.enorm_eq_ofReal (norm_nonneg _), ← ENNReal.ofReal_pow hs0,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by
        have := clk_matchedDistance_nonneg b E (layerSchur .separate E X ℓ); positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 + K * matchedDistance b E (layerSchur .separate E X ℓ) ≤ 1 + K * M0 := by
      nlinarith
    have h2 : (clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj τ * clkG12 b E X ℓ)) ^ n ≤ 2 ^ n * ‖G‖ ^ (2 * n) := by
      rw [pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ hs0 hs n
    have h0 : 0 ≤ 1 + K * matchedDistance b E (layerSchur .separate E X ℓ) := by
      have := clk_matchedDistance_nonneg b E (layerSchur .separate E X ℓ); positivity
    calc (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
          clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj τ * clkG12 b E X ℓ) ^ n
        ≤ (1 + K * M0) * (2 ^ n * ‖G‖ ^ (2 * n)) :=
          mul_le_mul h1 h2 (pow_nonneg hs0 _) (by positivity)
      _ = (1 + K * M0) * 2 ^ n * ‖G‖ ^ (2 * n) := by ring
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul _ ((hGm.enorm).pow_const _)]
  calc ENNReal.ofReal ((1 + K * M0) * 2 ^ n) *
        ∫⁻ ℓ, ‖‖layerResolvent .separate E (boundaryZ b E) X ℓ‖‖ₑ ^ (2 * n) ∂layerLaw W b .separate
      ≤ ENNReal.ofReal ((1 + K * M0) * 2 ^ n) * ENNReal.ofReal (CA ^ (2 * n)) := by gcongr
    _ = ENNReal.ofReal ((1 + K * M0) * (2 ^ n * CA ^ (2 * n))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-!
## 4. The weighted untagged step
-/

/-- **The polynomial inequality**, with the `W⁻¹` corrections: for
`0 ≤ q < 1`, `K = 2A₁/(1-q) + 1`, `0 ≤ δ ≤ min(1, K⁻¹)` and `0 < w ≤ 1`,
`(1 + Kqδ + KC₄w²)(1 + A₁δ + A₁w² + A₂w) + K B₂ w ≤ (1 + Cw)(1 + Kδ)`. -/
theorem clk_poly_ineq {q A₁ A₂ C₄ B₂ δ w : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hC₄ : 0 ≤ C₄) (hB₂ : 0 ≤ B₂) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδK : δ ≤ (2 * A₁ / (1 - q) + 1)⁻¹) (hw0 : 0 < w) (hw1 : w ≤ 1) :
    let K := 2 * A₁ / (1 - q) + 1
    (1 + K * q * δ + K * C₄ * w ^ 2) * (1 + A₁ * δ + A₁ * w ^ 2 + A₂ * w) + K * B₂ * w ≤
      (1 + ((1 + K) * (A₁ + A₂) + K * C₄ * (1 + 2 * A₁ + A₂) + K * B₂) * w) * (1 + K * δ) := by
  intro K
  have h1q : 0 < 1 - q := by linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 2 * A₁ / (1 - q) := div_nonneg (by linarith) h1q.le
    show 1 ≤ 2 * A₁ / (1 - q) + 1; linarith
  have hK0 : 0 < K := by linarith
  have hKq : K * (1 - q) = 2 * A₁ + (1 - q) := by
    show (2 * A₁ / (1 - q) + 1) * (1 - q) = _
    field_simp
  have hKδ : K * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hδK hK0.le
    rwa [mul_inv_cancel₀ hK0.ne'] at this
  -- main part: `(1 + Kqδ)(1 + A₁δ) ≤ 1 + Kδ`
  have hmain : (1 + K * q * δ) * (1 + A₁ * δ) ≤ 1 + K * δ := by
    have e : 1 + K * δ - (1 + K * q * δ) * (1 + A₁ * δ) =
        δ * (K * (1 - q) - A₁) - K * q * A₁ * δ ^ 2 := by ring
    have h2 : K * q * A₁ * δ ^ 2 ≤ A₁ * δ := by
      have : K * q * A₁ * δ ^ 2 = (A₁ * δ) * (q * (K * δ)) := by ring
      rw [this]
      have hq' : q * (K * δ) ≤ 1 := by nlinarith
      have h0 : 0 ≤ A₁ * δ := mul_nonneg hA₁ hδ0
      nlinarith
    have h3 : δ * (K * (1 - q) - A₁) ≥ δ * A₁ := by
      rw [hKq]; nlinarith
    nlinarith
  have hw2 : w ^ 2 ≤ w := by nlinarith
  have hP : 1 + K * q * δ ≤ 1 + K := by nlinarith [mul_le_mul_of_nonneg_left hδ1 hq0]
  have hP0 : 0 ≤ 1 + K * q * δ := by positivity
  have hE : A₁ * w ^ 2 + A₂ * w ≤ (A₁ + A₂) * w := by nlinarith
  have hE0 : 0 ≤ A₁ * w ^ 2 + A₂ * w := by positivity
  have hQ : 1 + A₁ * δ + A₁ * w ^ 2 + A₂ * w ≤ 1 + 2 * A₁ + A₂ := by nlinarith
  have hf : K * C₄ * w ^ 2 * (1 + A₁ * δ + A₁ * w ^ 2 + A₂ * w) ≤
      K * C₄ * w * (1 + 2 * A₁ + A₂) := by
    have h0 : 0 ≤ K * C₄ := by positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left hw2 h0) hQ (by positivity) (by positivity)
    linarith
  have hg : (1 + K * q * δ) * (A₁ * w ^ 2 + A₂ * w) ≤ (1 + K) * ((A₁ + A₂) * w) :=
    mul_le_mul hP hE hE0 (by positivity)
  have hKd0 : 0 ≤ K * δ := by positivity
  have hCw : 0 ≤ ((1 + K) * (A₁ + A₂) + K * C₄ * (1 + 2 * A₁ + A₂) + K * B₂) * w := by positivity
  nlinarith

/-- **Expansion of the `m`-th moment around the mean**: for `t ≥ 0` with
`E t ≤ M`, `‖t - E t‖_m ≤ σ` and `‖t‖_m < ∞` (`m = n + 2`),
`E t^m ≤ M^m + 2^m (M^n σ² + σ^m)`: the linear centered term vanishes. -/
theorem clk_mean_pow_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {t : Ω → ℝ} (htm : Measurable t) (ht0 : ∀ x, 0 ≤ t x) (hti : Integrable t ν) (n : ℕ)
    {M σ B : ℝ} (hM : ∫ x, t x ∂ν ≤ M) (hσ0 : 0 ≤ σ) (hB0 : 0 ≤ B)
    (hσ : eLpNorm (fun x => t x - ∫ y, t y ∂ν) (ENNReal.ofReal ((n + 2 : ℕ) : ℝ)) ν ≤
      ENNReal.ofReal σ)
    (hB : eLpNorm t (ENNReal.ofReal ((n + 2 : ℕ) : ℝ)) ν ≤ ENNReal.ofReal B) :
    Integrable (fun x => t x ^ (n + 2)) ν ∧
      ∫ x, t x ^ (n + 2) ∂ν ≤ M ^ (n + 2) + 2 ^ (n + 2) * (M ^ n * σ ^ 2 + σ ^ (n + 2)) := by
  set μt := ∫ x, t x ∂ν with hμtdef
  have hμ0 : 0 ≤ μt := integral_nonneg ht0
  have hηm : AEStronglyMeasurable (fun x => t x - μt) ν :=
    (htm.sub measurable_const).aestronglyMeasurable
  obtain ⟨hηmi, hηmb⟩ := clk_integral_pow_le hηm (n := n + 2) (by omega) hσ0 hσ
  have hη2' : eLpNorm (fun x => t x - μt) (ENNReal.ofReal ((2 : ℕ) : ℝ)) ν ≤ ENNReal.ofReal σ :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by
      push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))).trans hσ
  obtain ⟨hη2i, hη2b⟩ := clk_integral_pow_le hηm (n := 2) (by omega) hσ0 hη2'
  obtain ⟨htmi, -⟩ := clk_integral_pow_le htm.aestronglyMeasurable (n := n + 2) (by omega) hB0 hB
  have htmi' : Integrable (fun x => t x ^ (n + 2)) ν := by
    refine htmi.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [abs_of_nonneg (ht0 x)]
  refine ⟨htmi', ?_⟩
  have hpt : ∀ x, t x ^ (n + 2) ≤ μt ^ (n + 2) + ((n + 2 : ℕ) : ℝ) * μt ^ (n + 1) * (t x - μt) +
      2 ^ (n + 2) * (μt ^ n * |t x - μt| ^ 2 + |t x - μt| ^ (n + 2)) := by
    intro x
    have := clk_pow_expand hμ0 (t x - μt) n
    rw [add_sub_cancel] at this
    rw [sq_abs]
    push_cast
    linarith
  have hi1 : Integrable (fun x => t x - μt) ν := hti.sub (integrable_const _)
  set f₁ : Ω → ℝ := fun x => ((n + 2 : ℕ) : ℝ) * μt ^ (n + 1) * (t x - μt)
  set f₂ : Ω → ℝ := fun x => 2 ^ (n + 2) * (μt ^ n * |t x - μt| ^ 2 + |t x - μt| ^ (n + 2))
  have hf₁ : Integrable f₁ ν := hi1.const_mul _
  have hf₂ : Integrable f₂ ν := ((hη2i.const_mul _).add hηmi).const_mul _
  have hiR : Integrable (fun x => μt ^ (n + 2) + f₁ x + f₂ x) ν :=
    ((integrable_const _).add hf₁).add hf₂
  have hI1 : ∫ x, f₁ x ∂ν = 0 := by
    simp only [f₁]
    rw [integral_const_mul, integral_sub hti (integrable_const _), integral_const]
    simp [← hμtdef]
  have hμM : μt ≤ M := hM
  have hI2 : ∫ x, f₂ x ∂ν ≤ 2 ^ (n + 2) * (M ^ n * σ ^ 2 + σ ^ (n + 2)) := by
    simp only [f₂]
    rw [integral_const_mul, integral_add (hη2i.const_mul _) hηmi, integral_const_mul]
    have h1 : μt ^ n ≤ M ^ n := pow_le_pow_left₀ hμ0 hμM n
    have h2 : 0 ≤ ∫ x, |t x - μt| ^ 2 ∂ν := integral_nonneg fun x => by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul h1 hη2b h2
      (pow_nonneg (hμ0.trans hμM) _)) hηmb) (by positivity)
  calc ∫ x, t x ^ (n + 2) ∂ν ≤ ∫ x, (μt ^ (n + 2) + f₁ x + f₂ x) ∂ν :=
        integral_mono htmi' hiR hpt
    _ = μt ^ (n + 2) + ∫ x, f₁ x ∂ν + ∫ x, f₂ x ∂ν := by
        rw [integral_add (f := fun x => μt ^ (n + 2) + f₁ x) ((integrable_const _).add hf₁) hf₂,
          integral_add (integrable_const _) hf₁, integral_const]
        simp
    _ ≤ M ^ (n + 2) + 2 ^ (n + 2) * (M ^ n * σ ^ 2 + σ ^ (n + 2)) := by
        rw [hI1]
        have := pow_le_pow_left₀ hμ0 hμM (n + 2)
        linarith

/-- **Weighted combination**: if `δ₊ ≤ a + ξ` a.e. with `ξ ≥ 0`,
`E t^m ≤ P` and `E[ξ t^m] ≤ Q`, then `E[(1 + K δ₊) t^m] ≤ (1 + K a) P + K Q`. -/
theorem clk_weighted_combine {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {t ξ dp : Ω → ℝ} (htm : Measurable t) (hξm : Measurable ξ) (ht0 : ∀ x, 0 ≤ t x)
    (hξ0 : ∀ x, 0 ≤ ξ x) (hdp0 : ∀ x, 0 ≤ dp x) {m : ℕ} {a K P Q : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hd : ∀ᵐ x ∂ν, dp x ≤ a + ξ x)
    (hP : ∫⁻ x, ENNReal.ofReal (t x ^ m) ∂ν ≤ ENNReal.ofReal P)
    (hQ : ∫⁻ x, ‖ξ x‖ₑ * ‖t x‖ₑ ^ m ∂ν ≤ ENNReal.ofReal Q) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) :
    ∫⁻ x, ENNReal.ofReal (1 + K * dp x) * ‖t x‖ₑ ^ m ∂ν ≤
      ENNReal.ofReal ((1 + K * a) * P + K * Q) := by
  have ha0 : 0 ≤ 1 + K * a := by positivity
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (1 + K * dp x) * ‖t x‖ₑ ^ m ≤
      ENNReal.ofReal (1 + K * a) * ENNReal.ofReal (t x ^ m) +
        ENNReal.ofReal K * (‖ξ x‖ₑ * ‖t x‖ₑ ^ m) := by
    filter_upwards [hd] with x hx
    have htn : ‖t x‖ₑ ^ m = ENNReal.ofReal (t x ^ m) := by
      rw [Real.enorm_eq_ofReal (ht0 x), ENNReal.ofReal_pow (ht0 x)]
    have hd0 := hdp0 x
    have hξx := hξ0 x
    have htm0 : 0 ≤ t x ^ m := pow_nonneg (ht0 x) m
    rw [htn, Real.enorm_eq_ofReal hξx, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hξx, ← ENNReal.ofReal_mul hK,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 1 + K * dp x ≤ (1 + K * a) + K * ξ x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 htm0]
  have hm1 : Measurable (fun x => ENNReal.ofReal (t x ^ m)) :=
    ENNReal.measurable_ofReal.comp (htm.pow_const m)
  have hm2 : Measurable (fun x => ‖ξ x‖ₑ * ‖t x‖ₑ ^ m) := hξm.enorm.mul (htm.enorm.pow_const m)
  calc ∫⁻ x, ENNReal.ofReal (1 + K * dp x) * ‖t x‖ₑ ^ m ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal (1 + K * a) * ENNReal.ofReal (t x ^ m) +
          ENNReal.ofReal K * (‖ξ x‖ₑ * ‖t x‖ₑ ^ m)) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (1 + K * a) * ∫⁻ x, ENNReal.ofReal (t x ^ m) ∂ν +
          ENNReal.ofReal K * ∫⁻ x, ‖ξ x‖ₑ * ‖t x‖ₑ ^ m ∂ν := by
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]
    _ ≤ ENNReal.ofReal (1 + K * a) * ENNReal.ofReal P + ENNReal.ofReal K * ENNReal.ofReal Q := by
        gcongr
    _ = ENNReal.ofReal ((1 + K * a) * P + K * Q) := by
        rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hK,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- The arithmetic of the mean bound: with `D = C₁δ + C₁w²`, `σ = C₂ u √w`,
`M = (1 + D)u ≤ Cμ u`: `M^m + 2^m(M^n σ² + σ^m) ≤ (1 + A₁δ + A₁w² + A₂w)u^m`. -/
theorem clk_mean_arith {C₁ C₂ δ w u : ℝ} (n : ℕ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1) (hu : 0 ≤ u) :
    ((1 + (C₁ * δ + C₁ * w ^ 2)) * u) ^ (n + 2) + 2 ^ (n + 2) *
        (((1 + (C₁ * δ + C₁ * w ^ 2)) * u) ^ n * (C₂ * u * Real.sqrt w) ^ 2 +
          (C₂ * u * Real.sqrt w) ^ (n + 2)) ≤
      (1 + ((n + 2 : ℕ) : ℝ) * (1 + 2 * C₁) ^ (n + 2) * C₁ * δ +
          ((n + 2 : ℕ) : ℝ) * (1 + 2 * C₁) ^ (n + 2) * C₁ * w ^ 2 +
          2 ^ (n + 2) * ((1 + 2 * C₁) ^ n * C₂ ^ 2 + C₂ ^ (n + 2)) * w) * u ^ (n + 2) := by
  set D := C₁ * δ + C₁ * w ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hw2 : w ^ 2 ≤ 1 := by nlinarith
  have hDle : D ≤ 2 * C₁ := by nlinarith
  have h1 := clk_one_add_pow_le hD0 hDle (n + 2)
  have hsw : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0.le
  have hsw0 : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
  have hswm : Real.sqrt w ^ (n + 2) ≤ w := by
    rw [pow_add, hsw]
    have : Real.sqrt w ^ n ≤ 1 := pow_le_one₀ hsw0 (Real.sqrt_le_one.mpr hw1)
    nlinarith
  have hMn : (1 + D) ^ n ≤ (1 + 2 * C₁) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
  -- main term
  have hA : ((1 + D) * u) ^ (n + 2) ≤
      (1 + ((n + 2 : ℕ) : ℝ) * (1 + 2 * C₁) ^ (n + 2) * C₁ * δ +
        ((n + 2 : ℕ) : ℝ) * (1 + 2 * C₁) ^ (n + 2) * C₁ * w ^ 2) * u ^ (n + 2) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right (h1.trans (le_of_eq ?_)) (pow_nonneg hu _)
    rw [hD]; ring
  -- fluctuation terms
  have hB1 : ((1 + D) * u) ^ n * (C₂ * u * Real.sqrt w) ^ 2 ≤
      (1 + 2 * C₁) ^ n * C₂ ^ 2 * w * u ^ (n + 2) := by
    rw [mul_pow, mul_pow, mul_pow, hsw, pow_add u n 2]
    have h0 : 0 ≤ u ^ n * (C₂ ^ 2 * u ^ 2 * w) := by positivity
    calc (1 + D) ^ n * u ^ n * (C₂ ^ 2 * u ^ 2 * w) = (1 + D) ^ n * (u ^ n * (C₂ ^ 2 * u ^ 2 * w)) := by ring
      _ ≤ (1 + 2 * C₁) ^ n * (u ^ n * (C₂ ^ 2 * u ^ 2 * w)) := mul_le_mul_of_nonneg_right hMn h0
      _ = (1 + 2 * C₁) ^ n * C₂ ^ 2 * w * (u ^ n * u ^ 2) := by ring
  have hB2 : (C₂ * u * Real.sqrt w) ^ (n + 2) ≤ C₂ ^ (n + 2) * w * u ^ (n + 2) := by
    rw [mul_pow, mul_pow]
    have h0 : 0 ≤ C₂ ^ (n + 2) * u ^ (n + 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hswm h0]
  have h2 : (0 : ℝ) ≤ 2 ^ (n + 2) := by positivity
  have hB := mul_le_mul_of_nonneg_left (add_le_add hB1 hB2) h2
  nlinarith [hA, hB]

/-- **Untagged step with the Lyapunov weight**: for each integer `m = n + 2`
there are `K ≥ 0`, a radius `d₁ > 0` and `C ≥ 0` such that, for `W ≥ W₀`, Hermitian `X` with
`d(X) ≤ d₁`, `E ∈ I` and `Y ⪰ 0`,
`E[(1 + K d(X₊)) t^m] ≤ (1 + C/W)(1 + K d(X)) u^m`, `t = W⁻¹ Tr L*YL`, `u = W⁻¹ Tr Y`. -/
theorem clk_step_weighted (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ n : ℕ,
    ∃ (K d₁ C : ℝ) (W₀ : ℕ), 0 ≤ K ∧ 0 < d₁ ∧ 0 ≤ C ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W →
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ E ∈ bulkInterval κ,
      matchedDistance b E X ≤ d₁ → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)‖ₑ ^ (n + 2) ∂layerLaw W b .separate ≤
          ENNReal.ofReal ((1 + C / W) * ((1 + K * matchedDistance b E X) * clkTrace Y ^ (n + 2))) := by
  intro b hb0 hb1 κ hκ n
  have hWL := weightedLayer_holds hcount hgrad
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨dstar₁, C₁, W₁, hd₁, hmean⟩ := hWL.clockMean b hb0 hb1 κ hκ
  obtain ⟨C₂, W₂, hnoise⟩ := hWL.clockNoise b hb0 hb1 κ hκ ((n + 2 : ℕ) : ℝ)
    (by push_cast; linarith)
  obtain ⟨C₃, W₃, hunr⟩ := hWL.unrestricted b hb0 hb1 κ hκ ((2 * (n + 2) : ℕ) : ℝ)
    (by push_cast; linarith)
  obtain ⟨d₀, q, C₄, ε₄, hd₀, hq1, hε₄, hstep⟩ :=
    (scalarRecursionContract_holds hcount hgrad).oneStep b hb0 hb1 κ hκ
  -- constants
  obtain ⟨C₁', hC₁0, hC₁⟩ : ∃ c, 0 ≤ c ∧ C₁ ≤ c := ⟨max C₁ 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C₂', hC₂0, hC₂⟩ : ∃ c, 0 ≤ c ∧ C₂ ≤ c := ⟨max C₂ 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C₃', hC₃0, hC₃⟩ : ∃ c, 0 ≤ c ∧ C₃ ≤ c := ⟨max C₃ 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C₄', hC₄0, hC₄⟩ : ∃ c, 0 ≤ c ∧ C₄ ≤ c := ⟨max C₄ 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨q', hq'0, hq', hq'1⟩ : ∃ c, 0 ≤ c ∧ q ≤ c ∧ c < 1 :=
    ⟨max q 0, le_max_right _ _, le_max_left _ _, max_lt hq1 one_pos⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A, A = ((n + 2 : ℕ) : ℝ) * (1 + 2 * C₁') ^ (n + 2) * C₁' := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A, A = 2 ^ (n + 2) * ((1 + 2 * C₁') ^ n * C₂' ^ 2 + C₂' ^ (n + 2)) :=
    ⟨_, rfl⟩
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = C₄' * Real.sqrt 2 * C₃' ^ (n + 2) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hA₂0 : 0 ≤ A₂ := by rw [hA₂]; positivity
  have hB₂0 : 0 ≤ B₂ := by rw [hB₂]; positivity
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * A₁ / (1 - q') + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 2 * A₁ / (1 - q') := div_nonneg (by linarith) (by linarith)
    linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨C, hC⟩ : ∃ C, C = (1 + K) * (A₁ + A₂) + K * C₄' * (1 + 2 * A₁ + A₂) + K * B₂ :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨K, min (min dstar₁ d₀) (min 1 K⁻¹), C, max (max W₁ W₂) (max W₃ ⌈2 / ε₄⌉₊), hK0,
    lt_min (lt_min hd₁ hd₀) (lt_min one_pos (inv_pos.mpr (by linarith))), hC0, ?_⟩
  intro W hW hWW X hX E hE hd Y hY
  have hW1 : W₁ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hWW)
  have hW2 : W₂ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hWW)
  have hW3 : W₃ ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hWW)
  have hW4 : ⌈2 / ε₄⌉₊ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hWW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hWge1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hδ0 : 0 ≤ matchedDistance b E X := clk_matchedDistance_nonneg b E X
  have hδd : matchedDistance b E X ≤ dstar₁ := hd.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ₀ : matchedDistance b E X ≤ d₀ := hd.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : matchedDistance b E X ≤ 1 := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδK : matchedDistance b E X ≤ K⁻¹ := hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu0 : 0 ≤ clkTrace Y := clkTrace_nonneg hY
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hLm : Measurable (fun ℓ : LayerSample W .separate => clkL b E X ℓ) :=
    clk_measurable_L b E measurable_const measurable_id
  have htm : Measurable (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)) :=
    clk_measurable_trace (srec_measurable_mul
      (srec_measurable_mul (srec_measurable_conjTranspose hLm) measurable_const) hLm)
  have ht0 : ∀ ℓ, 0 ≤ clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ) := fun ℓ =>
    clkTrace_nonneg (hY.conjTranspose_mul_mul_same _)
  set w : ℝ := (W : ℝ)⁻¹ with hw
  have hw0 : 0 < w := inv_pos.mpr hWr
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hWge1
  have hsW : (Real.sqrt W)⁻¹ = Real.sqrt w := by rw [hw, Real.sqrt_inv]
  -- the mean (the clock-mean identity)
  obtain ⟨hti, hμle⟩ := hmean W hW hW1 X hX E hE hδd Y hY
  have hM : ∫ ℓ, clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ) ∂layerLaw W b .separate ≤
      (1 + (C₁' * matchedDistance b E X + C₁' * w ^ 2)) * clkTrace Y := by
    refine hμle.trans (mul_le_mul_of_nonneg_right ?_ hu0)
    have h1 : C₁ * matchedDistance b E X ≤ C₁' * matchedDistance b E X :=
      mul_le_mul_of_nonneg_right hC₁ hδ0
    have h2 : C₁ / (W : ℝ) ^ 2 ≤ C₁' * w ^ 2 := by
      rw [hw, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hC₁ (by positivity)
    linarith
  -- the noise (the clock-noise bound)
  obtain ⟨hn1, hn2⟩ := hnoise W hW hW2 X hX E hE Y hY
  have hσ : eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ) -
      ∫ ℓ', clkTrace ((clkL b E X ℓ')ᴴ * Y * clkL b E X ℓ') ∂layerLaw W b .separate)
      (ENNReal.ofReal ((n + 2 : ℕ) : ℝ)) (layerLaw W b .separate) ≤
      ENNReal.ofReal (C₂' * clkTrace Y * Real.sqrt w) := by
    refine hn1.trans (ENNReal.ofReal_le_ofReal (hn2.trans ?_))
    rw [← hsW, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ hu0) (Real.sqrt_nonneg _)
  -- the unrestricted bound
  have hu' : eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ))
      (ENNReal.ofReal ((2 * (n + 2) : ℕ) : ℝ)) (layerLaw W b .separate) ≤
      ENNReal.ofReal (C₃' * clkTrace Y) :=
    (hunr W hW hW3 X hX E hE Y hY).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC₃ hu0))
  have htm' : eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ))
      (ENNReal.ofReal ((n + 2 : ℕ) : ℝ)) (layerLaw W b .separate) ≤
      ENNReal.ofReal (C₃' * clkTrace Y) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by push_cast; linarith))).trans
      hu'
  obtain ⟨htmi, hEt⟩ := clk_mean_pow_le htm ht0 hti n hM (by positivity) (by positivity) hσ htm'
  have hEt' := hEt.trans (clk_mean_arith n hC₁0 hC₂0 hδ0 hδ1 hw0 hw1 hu0)
  rw [← hA₁, ← hA₂] at hEt'
  have hP : ∫⁻ ℓ, ENNReal.ofReal (clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ) ^ (n + 2))
      ∂layerLaw W b .separate ≤ ENNReal.ofReal ((1 + A₁ * matchedDistance b E X + A₁ * w ^ 2 +
        A₂ * w) * clkTrace Y ^ (n + 2)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal htmi
      (Filter.Eventually.of_forall fun ℓ => pow_nonneg (ht0 ℓ) _)]
    exact ENNReal.ofReal_le_ofReal hEt'
  -- the scalar recursion and the correlated term
  obtain ⟨hasξ, hξp⟩ := hstep W hW X hX E hE hδ₀
  have hξm : Measurable (srecXi b E X) := srec_measurable_xi b E X
  have hξ2 : eLpNorm (srecXi b E X) (ENNReal.ofReal 2) (layerLaw W b .separate) ≤
      ENNReal.ofReal (C₄' * Real.sqrt 2 * w) := by
    have h2W : (2 : ℝ) ≤ ε₄ * W := by
      have h1 : 2 / ε₄ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hW4)
      rw [div_le_iff₀ hε₄] at h1; linarith
    refine (hξp 2 le_rfl h2W).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hw, div_eq_mul_inv]
    gcongr
  have hQ : ∫⁻ ℓ, ‖srecXi b E X ℓ‖ₑ * ‖clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)‖ₑ ^ (n + 2)
      ∂layerLaw W b .separate ≤
      ENNReal.ofReal (C₄' * Real.sqrt 2 * w * (C₃' * clkTrace Y) ^ (n + 2)) :=
    clk_lintegral_mul_pow_le hξm.aestronglyMeasurable htm.aestronglyMeasurable (by omega)
      (by positivity) (by positivity) hξ2 hu'
  have hd' : ∀ᵐ ℓ ∂layerLaw W b .separate, matchedDistance b E (layerSchur .separate E X ℓ) ≤
      (q' * matchedDistance b E X + C₄' * w ^ 2) + srecXi b E X ℓ := by
    filter_upwards [hasξ] with ℓ hℓ
    change matchedDistance b E (layerSchur .separate E X ℓ) ≤ q * matchedDistance b E X +
      C₄ / (W : ℝ) ^ 2 + srecXi b E X ℓ at hℓ
    have h1 : q * matchedDistance b E X ≤ q' * matchedDistance b E X :=
      mul_le_mul_of_nonneg_right hq' hδ0
    have h2 : C₄ / (W : ℝ) ^ 2 ≤ C₄' * w ^ 2 := by
      rw [hw, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hC₄ (by positivity)
    linarith
  have hcomb := clk_weighted_combine htm hξm ht0 (fun ℓ => (norm_nonneg _).trans (le_max_left _ _))
    (fun ℓ => clk_matchedDistance_nonneg b E (layerSchur .separate E X ℓ)) (by positivity) hK0
    hd' hP hQ (by positivity) (by positivity)
  refine hcomb.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the polynomial inequality
  have hPI := clk_poly_ineq hq'0 hq'1 hA₁0 hA₂0 hC₄0 hB₂0 hδ0 hδ1 (by rw [← hK]; exact hδK) hw0 hw1
  simp only at hPI
  rw [← hK, ← hC] at hPI
  have e : C / (W : ℝ) = C * w := by rw [hw, div_eq_mul_inv]
  have hum : 0 ≤ clkTrace Y ^ (n + 2) := pow_nonneg hu0 _
  have hrw : (1 + K * (q' * matchedDistance b E X + C₄' * w ^ 2)) *
        ((1 + A₁ * matchedDistance b E X + A₁ * w ^ 2 + A₂ * w) * clkTrace Y ^ (n + 2)) +
      K * (C₄' * Real.sqrt 2 * w * (C₃' * clkTrace Y) ^ (n + 2)) =
      ((1 + K * q' * matchedDistance b E X + K * C₄' * w ^ 2) *
        (1 + A₁ * matchedDistance b E X + A₁ * w ^ 2 + A₂ * w) + K * B₂ * w) *
        clkTrace Y ^ (n + 2) := by
    rw [hB₂, mul_pow]; ring
  rw [hrw, e, show (1 + C * w) * ((1 + K * matchedDistance b E X) * clkTrace Y ^ (n + 2)) =
    ((1 + C * w) * (1 + K * matchedDistance b E X)) * clkTrace Y ^ (n + 2) by ring]
  exact mul_le_mul_of_nonneg_right hPI hum

end BlockBand.Layers
