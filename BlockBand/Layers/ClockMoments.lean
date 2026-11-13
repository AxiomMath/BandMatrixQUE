module

public import BlockBand.Layers.ClockRecursion

/-!
# The clock-moments lemma: full and tagged clock moments along the growing path

Moments of the full and tagged clocks along the growing path. The law is the growing-path law
`growthLaw W r₀ L b` (core `r₀ ∈ {1,2}` and `L` fresh separate-port layers, all independent) or
the path law `pathLaw W r b`, so `L^p` norms are full prior moments, the scalar exit event
included. The clock is `clkClock` (the tagged clock identity along `grownSchur`, started from the
core injection), `u_r = W⁻¹ Tr Y_r`, `r = r₀ + 2k`. Quantifiers: `b ∈ (0, 1/2)`, the bulk
interval `I = bulkInterval κ`, `T` and the fixed moment order `p ≥ 1` first; then `C_p, W₀(p)`;
then uniformly in `W ≥ W₀`, `r`, both cores, every `L` with `r₀ + 2L ≤ TW`, every `k ≤ L`, every
deterministic `E ∈ I` and every tag.

## Statement (`ClockMomentsStatement`)

* full energy clock `s_r = W⁻¹ Tr R_r* X_r' R_r` (`X_r' = B_p*(H_r - E)⁻² B_p`) under
  `pathLaw W r b`, `1 ≤ r ≤ TW`: `‖s_r‖_p ≤ C_p (r + 1)`; and the same bound for the full
  recursion (`P = I` at every step and on the core) along the growth, `r = r₀ + 2k`;
* tagged clock (arbitrary core tag, `P ≠ 0` at no more than two layers):
  `‖u_{r₀+2k}‖_p ≤ C_p` (the tagged clock moments).

## Proof

* Lyapunov functional `M_k = E[1_{reg_k} (1 + K d(X_k)) u_k^m]`, `m = n + 2 ≥ p` an integer,
  `reg_k = {d(X_j) ≤ d' for j ≤ k}` (the stopped scalar process). By Minkowski for the weighted
  measure and Fubini over the fresh layer (`clk_lyap_step`, from `clk_step_weighted` and
  `clk_step_source`): `M_{k+1}^{1/m} ≤ (1 + C/W) M_k^{1/m} + β 1{layer k tagged}`. Iterating,
  `M_k^{1/m} ≤ e^{CT} (M_0^{1/m} + β N_k)`, `N_k` the number of tagged layers: bounded for at
  most two injections, linear in `k` for the full clock (in the paper: `M₊ ≤ (1+C/W)M` untagged,
  `M₊ ≤ C(1+M)` at an injection, `M₊ ≤ (1+C/W)M + CM^{1-1/p} + C` for the full clock; the
  Minkowski form covers all three at once).
* Exit removal (the scalar exit bound): crude `2m`-th moments `‖u_k‖_{2m} ≤ A^k(z₀ + kB)` from the
  unrestricted bound of the weighted-layer lemma (`clk_crude_step`), the exit probability
  `≤ exp(-cW log W)` and Hölder.
* Real `p ≥ 1` by monotonicity of `L^p` norms on a probability space; the energy clock under
  `pathLaw W r b` is the full clock at step `k` (`r = r₀ + 2k`, either parity) by
  `clk_fullClock_eq_source` and `measurePreserving_pgPath` (`clk_eLpNorm_energy`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. Fubini and Minkowski
-/

/-- **Conditional `L^q` bounds integrate**: if `‖F(a, ·)‖_q ≤ c ‖g a‖` for a.e. `a`, then
`‖F‖_{L^q(μ ⊗ ν)} ≤ c ‖g‖_{L^q(μ)}`. -/
theorem clk_eLpNorm_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {F : α × β → ℝ} {g : α → ℝ}
    (hF : Measurable F) (hg : Measurable g) {q : ℝ} (hq : 0 < q) {c : ℝ}
    (h : ∀ᵐ a ∂μ, eLpNorm (fun y => F (a, y)) (ENNReal.ofReal q) ν ≤ ENNReal.ofReal c * ‖g a‖ₑ) :
    eLpNorm F (ENNReal.ofReal q) (μ.prod ν) ≤ ENNReal.ofReal c * eLpNorm g (ENNReal.ofReal q) μ := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, lintegral_prod _ (hF.enorm.pow_const _).aemeasurable]
  have hin : ∀ᵐ a ∂μ, ∫⁻ y, ‖F (a, y)‖ₑ ^ q ∂ν ≤ ENNReal.ofReal c ^ q * ‖g a‖ₑ ^ q := by
    filter_upwards [h] with a ha
    have hFa : Measurable (fun y => F (a, y)) := hF.comp measurable_prodMk_left
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top hFa.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq.le] at ha
    have h2 := ENNReal.rpow_le_rpow ha hq.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne', ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ hq.le] at h2
  calc (∫⁻ a, ∫⁻ y, ‖F (a, y)‖ₑ ^ q ∂ν ∂μ) ^ (1 / q)
      ≤ (∫⁻ a, ENNReal.ofReal c ^ q * ‖g a‖ₑ ^ q ∂μ) ^ (1 / q) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hin) (by positivity)
    _ = ENNReal.ofReal c * (∫⁻ a, ‖g a‖ₑ ^ q ∂μ) ^ (1 / q) := by
        rw [lintegral_const_mul _ (hg.enorm.pow_const _), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
          ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- **Weighted Minkowski**: `(∫ w (f+g)^m)^{1/m} ≤ (∫ w f^m)^{1/m} + (∫ w g^m)^{1/m}`. -/
theorem clk_weighted_minkowski {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w f g : α → ℝ≥0∞} (hw : Measurable w) (hf : Measurable f) (hg : Measurable g) {m : ℕ}
    (hm : 1 ≤ m) :
    (∫⁻ x, w x * (f x + g x) ^ m ∂μ) ^ (1 / (m : ℝ)) ≤
      (∫⁻ x, w x * f x ^ m ∂μ) ^ (1 / (m : ℝ)) + (∫⁻ x, w x * g x ^ m ∂μ) ^ (1 / (m : ℝ)) := by
  have h := ENNReal.lintegral_Lp_add_le (μ := μ.withDensity w) hf.aemeasurable hg.aemeasurable
    (p := (m : ℝ)) (by exact_mod_cast hm)
  simp only [Pi.add_apply, ENNReal.rpow_natCast] at h
  have e : ∀ φ : α → ℝ≥0∞, Measurable φ →
      ∫⁻ a, φ a ∂μ.withDensity w = ∫⁻ a, w a * φ a ∂μ := fun φ hφ => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hw hφ]; rfl
  rwa [e (fun a => (f a + g a) ^ m) ((hf.add hg).pow_const m), e (fun a => f a ^ m) (hf.pow_const m),
    e (fun a => g a ^ m) (hg.pow_const m)] at h

/-!
## 2. The Lyapunov functional of the stopped clock
-/

/-- The regular event `reg_k = {d(X_j) ≤ d' for all j ≤ k}` of the stopped scalar process. -/
def clkReg {W r₀ L : ℕ} (b E d' : ℝ) (ω : GrowthSample W r₀ L) (k : ℕ) : Prop :=
  ∀ j, j ≤ k → matchedDistance b E (grownSchur E ω j) ≤ d'

open Classical in
/-- The Lyapunov weight `1_{reg_k} (1 + K d(X_k))`. -/
def clkWt {W r₀ L : ℕ} (b E K d' : ℝ) (ω : GrowthSample W r₀ L) (k : ℕ) : ℝ≥0∞ :=
  if clkReg b E d' ω k then ENNReal.ofReal (1 + K * matchedDistance b E (grownSchur E ω k)) else 0

/-- The Lyapunov functional `M_k = E[1_{reg_k} (1 + K d(X_k)) u_k^m]` under `growthLaw W r₀ k`. -/
def clkLyap (W r₀ k : ℕ) (b E K d' : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool) (m : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ ω, clkWt b E K d' ω k * ‖clkTrace (clkClock b E τ₀ τ ω k)‖ₑ ^ m ∂growthLaw W r₀ k b

theorem clk_measurableSet_reg {W r₀ L : ℕ} (b E d' : ℝ) (k : ℕ) :
    MeasurableSet {ω : GrowthSample W r₀ L | clkReg b E d' ω k} := by
  have : {ω : GrowthSample W r₀ L | clkReg b E d' ω k} =
      ⋂ j, ⋂ (_ : j ≤ k), {ω | matchedDistance b E (grownSchur E ω j) ≤ d'} := by
    ext ω; simp [clkReg]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le ((srec_measurable_matchedDistance b E W).comp
      (clk_measurable_grownSchur E j)) measurable_const

theorem clk_measurable_wt {W r₀ L : ℕ} (b E K d' : ℝ) (k : ℕ) :
    Measurable (fun ω : GrowthSample W r₀ L => clkWt b E K d' ω k) := by
  unfold clkWt
  exact Measurable.ite (clk_measurableSet_reg b E d' k) (ENNReal.measurable_ofReal.comp
    (measurable_const.add (measurable_const.mul ((srec_measurable_matchedDistance b E W).comp
      (clk_measurable_grownSchur E k))))) measurable_const

theorem clkReg_pgTrunc {W r₀ L : ℕ} {b E d' : ℝ} {ω : GrowthSample W r₀ (L + 1)}
    (h : clkReg b E d' ω (L + 1)) : clkReg b E d' (pgTrunc ω) L := fun j hj => by
  rw [clk_grownSchur_pgTrunc E ω j hj]; exact h j (by omega)

theorem clkWt_le {W r₀ L : ℕ} {b E K d' : ℝ} (hK : 0 ≤ K) (hd' : d' ≤ 1)
    (ω : GrowthSample W r₀ L) (k : ℕ) : clkWt b E K d' ω k ≤ ENNReal.ofReal (1 + K) := by
  unfold clkWt
  split_ifs with h
  · exact ENNReal.ofReal_le_ofReal (by nlinarith [h k le_rfl])
  · exact bot_le

theorem clk_one_le_wt {W r₀ L : ℕ} {b E K d' : ℝ} (hK : 0 ≤ K) {ω : GrowthSample W r₀ L} {k : ℕ}
    (h : clkReg b E d' ω k) : 1 ≤ clkWt b E K d' ω k := by
  unfold clkWt
  simp only [h, ↓reduceIte]
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by
    have := clk_matchedDistance_nonneg b E (grownSchur E ω k); nlinarith)

/-!
## 3. One step of the clock, as a function of (old growth sample, fresh layer)
-/

/-- `t = W⁻¹ Tr L*YL` of step `k` with the old `X = X_{r₀+2k}`, `Y = Y_{r₀+2k}`. -/
def clkT {W r₀ k : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (x : GrowthSample W r₀ k × LayerSample W .separate) : ℝ :=
  clkTrace ((clkL b E (grownSchur E x.1 k) x.2)ᴴ * clkClock b E τ₀ τ x.1 k *
    clkL b E (grownSchur E x.1 k) x.2)

/-- `s = W⁻¹ Tr 𝒢₁₂* P 𝒢₁₂` of step `k` with the tag `τ k`. -/
def clkS {W r₀ k : ℕ} (b E : ℝ) (τ : ℕ → Fin 2 → Bool)
    (x : GrowthSample W r₀ k × LayerSample W .separate) : ℝ :=
  clkTrace ((clkG12 b E (grownSchur E x.1 k) x.2)ᴴ * clkProj (τ k) *
    clkG12 b E (grownSchur E x.1 k) x.2)

theorem clk_trace_last {W r₀ k : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ (k + 1)) :
    clkTrace (clkClock b E τ₀ τ ω (k + 1)) =
      clkS b E τ (pgTrunc ω, ω.2 (Fin.last k)) + clkT b E τ₀ τ (pgTrunc ω, ω.2 (Fin.last k)) := by
  rw [clkClock_last, clkStep, clkTrace_add]; rfl

theorem clkT_nonneg {W r₀ k : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (x : GrowthSample W r₀ k × LayerSample W .separate) : 0 ≤ clkT b E τ₀ τ x :=
  clkTrace_nonneg ((clkClock_posSemidef b E τ₀ τ x.1 k).conjTranspose_mul_mul_same _)

theorem clkS_nonneg {W r₀ k : ℕ} (b E : ℝ) (τ : ℕ → Fin 2 → Bool)
    (x : GrowthSample W r₀ k × LayerSample W .separate) : 0 ≤ clkS b E τ x :=
  clkTrace_nonneg ((clkProj_posSemidef (τ k)).conjTranspose_mul_mul_same _)

theorem clk_measurable_T {W r₀ k : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool) :
    Measurable (clkT (W := W) (r₀ := r₀) (k := k) b E τ₀ τ) := by
  have hX : Measurable (fun x : GrowthSample W r₀ k × LayerSample W .separate =>
      grownSchur E x.1 k) := (clk_measurable_grownSchur E k).comp measurable_fst
  have hY : Measurable (fun x : GrowthSample W r₀ k × LayerSample W .separate =>
      clkClock b E τ₀ τ x.1 k) := (clk_measurable_clock b E τ₀ τ k).comp measurable_fst
  have hL := clk_measurable_L b E hX measurable_snd
  exact clk_measurable_trace (srec_measurable_mul
    (srec_measurable_mul (srec_measurable_conjTranspose hL) hY) hL)

theorem clk_measurable_S {W r₀ k : ℕ} (b E : ℝ) (τ : ℕ → Fin 2 → Bool) :
    Measurable (clkS (W := W) (r₀ := r₀) (k := k) b E τ) := by
  have hX : Measurable (fun x : GrowthSample W r₀ k × LayerSample W .separate =>
      grownSchur E x.1 k) := (clk_measurable_grownSchur E k).comp measurable_fst
  have hG := clk_measurable_G12 b E hX measurable_snd
  exact clk_measurable_trace (srec_measurable_mul
    (srec_measurable_mul (srec_measurable_conjTranspose hG) measurable_const) hG)

open Classical in
/-- The weight of the next step, `1_{reg_k} (1 + K d(X₊))`, on (old sample, layer). -/
def clkWtP {W r₀ k : ℕ} (b E K d' : ℝ) (x : GrowthSample W r₀ k × LayerSample W .separate) :
    ℝ≥0∞ :=
  if clkReg b E d' x.1 k then
    ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E (grownSchur E x.1 k) x.2))
  else 0

theorem clk_measurable_wtP {W r₀ k : ℕ} (b E K d' : ℝ) :
    Measurable (clkWtP (W := W) (r₀ := r₀) (k := k) b E K d') := by
  have hX : Measurable (fun x : GrowthSample W r₀ k × LayerSample W .separate =>
      grownSchur E x.1 k) := (clk_measurable_grownSchur E k).comp measurable_fst
  unfold clkWtP
  exact Measurable.ite (measurable_fst (clk_measurableSet_reg b E d' k))
    (ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul
      ((srec_measurable_matchedDistance b E W).comp
        (srec_measurable_layerSchur E hX measurable_snd))))) measurable_const

/-- **One step of the Lyapunov functional** (in Minkowski form):
`M_{k+1}^{1/m} ≤ (1 + C/W) M_k^{1/m} + B^{1/m} 1{layer k tagged}`, from the conditional
one-step bounds `hS1` (untagged part, on the scalar domain `d ≤ d'`) and `hS2` (injection). -/
theorem clk_lyap_step {W r₀ k m : ℕ} (hm : 1 ≤ m) {b E K d' C B : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (hS1 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ d' → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)‖ₑ ^ m ∂layerLaw W b .separate ≤
          ENNReal.ofReal ((1 + C / W) * ((1 + K * matchedDistance b E X) * clkTrace Y ^ m)))
    (hS2 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ σ : Fin 2 → Bool,
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ)‖ₑ ^ m
          ∂layerLaw W b .separate ≤ ENNReal.ofReal B) :
    clkLyap W r₀ (k + 1) b E K d' τ₀ τ m ^ (1 / (m : ℝ)) ≤
      ENNReal.ofReal (1 + C / W) * clkLyap W r₀ k b E K d' τ₀ τ m ^ (1 / (m : ℝ)) +
        (if ∃ i, τ k i = true then ENNReal.ofReal B ^ (1 / (m : ℝ)) else 0) := by
  have hpl := bond_isProbabilityMeasure_layerLaw W b .separate
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have hgl : IsProbabilityMeasure (growthLaw W r₀ k b) := by
    unfold growthLaw pathLaw; infer_instance
  have hm0 : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  set ν := (growthLaw W r₀ k b).prod (layerLaw W b .separate) with hν
  have hwm := clk_measurable_wtP (W := W) (r₀ := r₀) (k := k) b E K d'
  have hTm := clk_measurable_T (W := W) (r₀ := r₀) (k := k) b E τ₀ τ
  have hSm := clk_measurable_S (W := W) (r₀ := r₀) (k := k) b E τ
  have hΦm : Measurable (fun x => clkWtP b E K d' x *
      (‖clkT b E τ₀ τ x‖ₑ + ‖clkS b E τ x‖ₑ) ^ m) :=
    hwm.mul ((hTm.enorm.add hSm.enorm).pow_const m)
  -- the next functional is dominated by the weighted product integral
  have hA : clkLyap W r₀ (k + 1) b E K d' τ₀ τ m ≤
      ∫⁻ x, clkWtP b E K d' x * (‖clkT b E τ₀ τ x‖ₑ + ‖clkS b E τ x‖ₑ) ^ m ∂ν := by
    unfold clkLyap
    rw [← (pg_mp_splitLast W r₀ k b).lintegral_comp hΦm]
    refine lintegral_mono fun ω => ?_
    rw [clk_trace_last, Real.enorm_eq_ofReal (add_nonneg (clkS_nonneg _ _ _ _) (clkT_nonneg _ _ _ _ _)),
      ENNReal.ofReal_add (clkS_nonneg _ _ _ _) (clkT_nonneg _ _ _ _ _),
      ← Real.enorm_eq_ofReal (clkS_nonneg _ _ _ _), ← Real.enorm_eq_ofReal (clkT_nonneg _ _ _ _ _),
      add_comm (‖clkS b E τ _‖ₑ)]
    unfold clkWt
    by_cases hreg : clkReg b E d' ω (k + 1)
    · have h' := clkReg_pgTrunc hreg
      simp only [hreg, h', clkWtP, ↓reduceIte, clk_grownSchur_last]
      exact le_rfl
    · simp only [hreg, ↓reduceIte, zero_mul]
      exact bot_le
  -- the untagged part (`hS1`, Fubini)
  have hB1 : ∫⁻ x, clkWtP b E K d' x * ‖clkT b E τ₀ τ x‖ₑ ^ m ∂ν ≤
      ENNReal.ofReal (1 + C / W) * clkLyap W r₀ k b E K d' τ₀ τ m := by
    rw [hν, lintegral_prod (fun x => clkWtP b E K d' x * ‖clkT b E τ₀ τ x‖ₑ ^ m)
      (hwm.mul (hTm.enorm.pow_const m)).aemeasurable]
    unfold clkLyap
    rw [← lintegral_const_mul (ENNReal.ofReal (1 + C / W))
      (f := fun ω => clkWt b E K d' ω k * ‖clkTrace (clkClock b E τ₀ τ ω k)‖ₑ ^ m)
      ((clk_measurable_wt b E K d' k).mul
        ((clk_measurable_trace (clk_measurable_clock b E τ₀ τ k)).enorm.pow_const m))]
    refine lintegral_mono_ae ?_
    filter_upwards [clk_ae_good W r₀ k b] with o ho
    by_cases hreg : clkReg b E d' o k
    · simp only [clkWtP, clkWt, hreg, ↓reduceIte]
      refine (hS1 _ (clk_grownSchur_isHermitian E ho k) (hreg k le_rfl) _
        (clkClock_posSemidef b E τ₀ τ o k)).trans (le_of_eq ?_)
      have hu0 := clkTrace_nonneg (clkClock_posSemidef b E τ₀ τ o k)
      have hd0 := clk_matchedDistance_nonneg b E (grownSchur E o k)
      have hW0 : (0 : ℝ) ≤ C / W := div_nonneg hC (Nat.cast_nonneg _)
      rw [Real.enorm_eq_ofReal hu0, ← ENNReal.ofReal_pow hu0,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    · simp only [clkWtP, hreg, ↓reduceIte, zero_mul, lintegral_zero]
      exact bot_le
  -- the injection (`hS2`, Fubini)
  have hB2 : ∫⁻ x, clkWtP b E K d' x * ‖clkS b E τ x‖ₑ ^ m ∂ν ≤
      if ∃ i, τ k i = true then ENNReal.ofReal B else 0 := by
    split_ifs with htag
    · rw [hν, lintegral_prod (fun x => clkWtP b E K d' x * ‖clkS b E τ x‖ₑ ^ m)
        (hwm.mul (hSm.enorm.pow_const m)).aemeasurable]
      calc ∫⁻ o, ∫⁻ ℓ, clkWtP b E K d' (o, ℓ) * ‖clkS b E τ (o, ℓ)‖ₑ ^ m ∂layerLaw W b .separate
            ∂growthLaw W r₀ k b
          ≤ ∫⁻ _o, ENNReal.ofReal B ∂growthLaw W r₀ k b := by
            refine lintegral_mono_ae ?_
            filter_upwards [clk_ae_good W r₀ k b] with o ho
            refine le_trans (lintegral_mono fun ℓ => ?_) (hS2 _ (clk_grownSchur_isHermitian E ho k)
              (τ k))
            refine mul_le_mul' ?_ le_rfl
            simp only [clkWtP]
            split_ifs
            · exact le_rfl
            · exact bot_le
        _ = ENNReal.ofReal B := by rw [lintegral_const, measure_univ, mul_one]
    · simp only [not_exists, Bool.not_eq_true] at htag
      have h0 : ∀ x : GrowthSample W r₀ k × LayerSample W .separate, clkS b E τ x = 0 := by
        intro x
        simp only [clkS, clkProj_eq_zero (fun i => htag i), Matrix.zero_mul, clkTrace, trace_zero, Complex.zero_re, mul_zero]
      simp only [h0, enorm_zero, zero_pow (by omega : m ≠ 0), mul_zero, lintegral_zero, le_refl]
  -- Minkowski
  have hM := clk_weighted_minkowski (μ := ν) hwm hTm.enorm hSm.enorm hm
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + C / W) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by have : (0 : ℝ) ≤ C / W := div_nonneg hC (Nat.cast_nonneg _); linarith)
  calc clkLyap W r₀ (k + 1) b E K d' τ₀ τ m ^ (1 / (m : ℝ))
      ≤ (∫⁻ x, clkWtP b E K d' x * (‖clkT b E τ₀ τ x‖ₑ + ‖clkS b E τ x‖ₑ) ^ m ∂ν) ^ (1 / (m : ℝ)) :=
        ENNReal.rpow_le_rpow hA hm0.le
    _ ≤ _ := hM
    _ ≤ (ENNReal.ofReal (1 + C / W) * clkLyap W r₀ k b E K d' τ₀ τ m) ^ (1 / (m : ℝ)) +
          (if ∃ i, τ k i = true then ENNReal.ofReal B else 0) ^ (1 / (m : ℝ)) :=
        add_le_add (ENNReal.rpow_le_rpow hB1 hm0.le) (ENNReal.rpow_le_rpow hB2 hm0.le)
    _ ≤ ENNReal.ofReal (1 + C / W) * clkLyap W r₀ k b E K d' τ₀ τ m ^ (1 / (m : ℝ)) +
          (if ∃ i, τ k i = true then ENNReal.ofReal B ^ (1 / (m : ℝ)) else 0) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hm0.le]
        refine add_le_add (mul_le_mul' ?_ le_rfl) ?_
        · calc ENNReal.ofReal (1 + C / W) ^ (1 / (m : ℝ)) ≤ ENNReal.ofReal (1 + C / W) ^ (1 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le hone (by
                  rw [div_le_one (by exact_mod_cast hm)]; exact_mod_cast hm)
            _ = ENNReal.ofReal (1 + C / W) := ENNReal.rpow_one _
        · split_ifs
          · exact le_rfl
          · rw [ENNReal.zero_rpow_of_pos hm0]

/-!
## 4. Discrete iteration
-/

/-- `a_{j+1} ≤ ρ a_j + c_j`, `ρ ≥ 1` ⇒ `a_k ≤ ρ^k (a_0 + Σ_{j<k} c_j)`. -/
theorem clk_iter {a c : ℕ → ℝ≥0∞} {ρ : ℝ≥0∞} (hρ : 1 ≤ ρ) (h : ∀ j, a (j + 1) ≤ ρ * a j + c j) :
    ∀ k, a k ≤ ρ ^ k * (a 0 + ∑ j ∈ Finset.range k, c j)
  | 0 => by simp
  | k + 1 => by
    have ih := clk_iter hρ h k
    have h1 : (1 : ℝ≥0∞) ≤ ρ ^ (k + 1) := one_le_pow₀ hρ
    calc a (k + 1) ≤ ρ * a k + c k := h k
      _ ≤ ρ * (ρ ^ k * (a 0 + ∑ j ∈ Finset.range k, c j)) + ρ ^ (k + 1) * c k := by
          gcongr
          calc c k = 1 * c k := (one_mul _).symm
            _ ≤ ρ ^ (k + 1) * c k := mul_le_mul' h1 le_rfl
      _ = ρ ^ (k + 1) * (a 0 + ∑ j ∈ Finset.range (k + 1), c j) := by
          rw [Finset.sum_range_succ, pow_succ']; ring

theorem clk_sum_tag (τ : ℕ → Fin 2 → Bool) (β : ℝ≥0∞) (k : ℕ) :
    ∑ j ∈ Finset.range k, (if ∃ i, τ j i = true then β else 0) = clkTagCount τ k * β := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rfl

theorem clkTagCount_le (τ : ℕ → Fin 2 → Bool) (k : ℕ) : clkTagCount τ k ≤ k := by
  unfold clkTagCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_range k).le

theorem clkTagCount_mono (τ : ℕ → Fin 2 → Bool) {k L : ℕ} (h : k ≤ L) :
    clkTagCount τ k ≤ clkTagCount τ L :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- `(1 + x)^k ≤ exp(x k)`, `x ≥ 0`. -/
theorem clk_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : (1 + x) ^ k ≤ Real.exp (x * k) := by
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) k

/-- **Exit arithmetic**: `exp(βW - αW log W) (γ + γW) ≤ 1` for `W ≥ W₀`. -/
theorem clk_exit_small {α β γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → 0 < W →
      Real.exp (β * W - α * W * Real.log W) * (γ + γ * W) ≤ 1 := by
  refine ⟨⌈Real.exp ((β + γ + 1) / α)⌉₊, fun W hW hW0 => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW0
  have hlog : (β + γ + 1) / α ≤ Real.log W := by
    rw [Real.le_log_iff_exp_le hWr]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hW)
  have hαl : β + γ + 1 ≤ α * Real.log W := by
    rw [div_le_iff₀ hα] at hlog; linarith
  have h1 : β * W - α * W * Real.log W ≤ -((γ + 1) * W) := by nlinarith
  have h2 : γ + γ * W ≤ Real.exp ((γ + 1) * W) := by
    have e : Real.exp ((γ + 1) * W) = Real.exp W * Real.exp (γ * W) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have h3 : 1 + W ≤ Real.exp W := by linarith [Real.add_one_le_exp (W : ℝ)]
    have h4 : 1 + γ * W ≤ Real.exp (γ * W) := by linarith [Real.add_one_le_exp (γ * W)]
    have h5 : γ ≤ 1 + γ * W := by nlinarith
    calc γ + γ * W = γ * (1 + W) := by ring
      _ ≤ (1 + γ * W) * (1 + W) := mul_le_mul_of_nonneg_right h5 (by linarith)
      _ ≤ Real.exp (γ * W) * Real.exp W :=
          mul_le_mul h4 h3 (by linarith) (Real.exp_pos _).le
      _ = Real.exp W * Real.exp (γ * W) := mul_comm _ _
  calc Real.exp (β * W - α * W * Real.log W) * (γ + γ * W)
      ≤ Real.exp (-((γ + 1) * W)) * Real.exp ((γ + 1) * W) :=
        mul_le_mul (Real.exp_le_exp.mpr h1) h2 (by positivity) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-!
## 5. Splitting off the exit event
-/

/-- `‖u‖_m ≤ M_k^{1/m} + P(reg_kᶜ)^{1/(2m)} ‖u‖_{2m}`. -/
theorem clk_split {W r₀ k m : ℕ} (hm : 1 ≤ m) {b E K d' : ℝ} (hK : 0 ≤ K)
    (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool) :
    eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal m) (growthLaw W r₀ k b) ≤
      clkLyap W r₀ k b E K d' τ₀ τ m ^ (1 / (m : ℝ)) +
        growthLaw W r₀ k b {ω | ¬ clkReg b E d' ω k} ^ (1 / (2 * m : ℝ)) *
          eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal (2 * m))
            (growthLaw W r₀ k b) := by
  set μ := growthLaw W r₀ k b
  set u := fun ω : GrowthSample W r₀ k => clkTrace (clkClock b E τ₀ τ ω k) with hu
  have hum : Measurable u := clk_measurable_trace (clk_measurable_clock b E τ₀ τ k)
  set S := {ω : GrowthSample W r₀ k | clkReg b E d' ω k} with hS
  have hSm : MeasurableSet S := clk_measurableSet_reg b E d' k
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hm)
  have hsplit : u = S.indicator u + Sᶜ.indicator u := (Set.indicator_self_add_compl S u).symm
  calc eLpNorm u (ENNReal.ofReal m) μ = eLpNorm (S.indicator u + Sᶜ.indicator u) (ENNReal.ofReal m) μ :=
        by rw [← hsplit]
    _ ≤ _ := (eLpNorm_add_le hm1).trans (add_le_add ?_ ?_)
  · have hm0' : ENNReal.ofReal m ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hm0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hm0' ENNReal.ofReal_ne_top
      (hum.indicator hSm).aestronglyMeasurable, ENNReal.toReal_ofReal hm0.le]
    refine ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by positivity)
    rw [ENNReal.rpow_natCast]
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      calc ‖u ω‖ₑ ^ m = 1 * ‖u ω‖ₑ ^ m := (one_mul _).symm
        _ ≤ clkWt b E K d' ω k * ‖u ω‖ₑ ^ m := mul_le_mul' (clk_one_le_wt hK hω) le_rfl
    · rw [Set.indicator_of_notMem hω, enorm_zero, zero_pow (by omega)]
      exact bot_le
  · have e : Sᶜ.indicator u = fun ω => Sᶜ.indicator (fun _ => (1 : ℝ)) ω * u ω := by
      funext ω
      by_cases hω : ω ∈ Sᶜ
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [show Sᶜ.indicator u = _ from e]
    refine (wl_eLpNorm_mul_le (measurable_const.indicator hSm.compl).aestronglyMeasurable
      hum.aestronglyMeasurable hm0).trans (mul_le_mul' (le_of_eq ?_) le_rfl)
    have h2m : ENNReal.ofReal (2 * m) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    rw [eLpNorm_indicator_const hSm.compl.nullMeasurableSet h2m ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [enorm_one, one_mul]
    rfl

/-!
## 6. Crude moments (no stopping)
-/

theorem clk_isProb_growthLaw (W r₀ L : ℕ) (b : ℝ) : IsProbabilityMeasure (growthLaw W r₀ L b) := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  unfold growthLaw pathLaw; infer_instance

/-- **Crude step**: `‖u_{k+1}‖_q ≤ C₃ ‖u_k‖_q + S` from the unrestricted
bound of the weighted-layer lemma and the source bound, conditionally on the old path. -/
theorem clk_crude_step {W r₀ k : ℕ} {b E q C₃ S : ℝ} (hq1 : 1 ≤ q) (hC₃ : 0 ≤ C₃)
    (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (hU : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)) (ENNReal.ofReal q)
          (layerLaw W b .separate) ≤ ENNReal.ofReal (C₃ * clkTrace Y))
    (hG : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ σ : Fin 2 → Bool,
        eLpNorm (fun ℓ => clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ))
          (ENNReal.ofReal q) (layerLaw W b .separate) ≤ ENNReal.ofReal S) :
    eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω (k + 1))) (ENNReal.ofReal q)
        (growthLaw W r₀ (k + 1) b) ≤
      ENNReal.ofReal C₃ * eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal q)
        (growthLaw W r₀ k b) + ENNReal.ofReal S := by
  have hpl := bond_isProbabilityMeasure_layerLaw W b .separate
  have hgl := clk_isProb_growthLaw W r₀ k b
  have hTm := clk_measurable_T (W := W) (r₀ := r₀) (k := k) b E τ₀ τ
  have hSm := clk_measurable_S (W := W) (r₀ := r₀) (k := k) b E τ
  have hum : Measurable (fun ω : GrowthSample W r₀ k => clkTrace (clkClock b E τ₀ τ ω k)) :=
    clk_measurable_trace (clk_measurable_clock b E τ₀ τ k)
  have hq : 0 < q := by linarith
  have e : (fun ω : GrowthSample W r₀ (k + 1) => clkTrace (clkClock b E τ₀ τ ω (k + 1))) =
      (clkS b E τ + clkT b E τ₀ τ) ∘
        (fun ω : GrowthSample W r₀ (k + 1) => (pgTrunc ω, ω.2 (Fin.last k))) := by
    funext ω; exact clk_trace_last b E τ₀ τ ω
  rw [e, eLpNorm_comp_measurePreserving (hSm.add hTm).aestronglyMeasurable
    (pg_mp_splitLast W r₀ k b)]
  have hT : eLpNorm (clkT b E τ₀ τ) (ENNReal.ofReal q) ((growthLaw W r₀ k b).prod
      (layerLaw W b .separate)) ≤ ENNReal.ofReal C₃ * eLpNorm (fun ω => clkTrace
        (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal q) (growthLaw W r₀ k b) := by
    refine clk_eLpNorm_prod_le hTm hum hq ?_
    filter_upwards [clk_ae_good W r₀ k b] with o ho
    refine (hU _ (clk_grownSchur_isHermitian E ho k) _ (clkClock_posSemidef b E τ₀ τ o k)).trans
      (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hC₃, Real.enorm_eq_ofReal (clkTrace_nonneg
      (clkClock_posSemidef b E τ₀ τ o k))]
  have hS : eLpNorm (clkS b E τ) (ENNReal.ofReal q) ((growthLaw W r₀ k b).prod
      (layerLaw W b .separate)) ≤ ENNReal.ofReal S := by
    have h := clk_eLpNorm_prod_le (g := fun _ : GrowthSample W r₀ k => (1 : ℝ)) (c := S) hSm
      measurable_const hq (μ := growthLaw W r₀ k b) (ν := layerLaw W b .separate) (by
        filter_upwards [clk_ae_good W r₀ k b] with o ho
        simp only [enorm_one, mul_one]
        exact hG _ (clk_grownSchur_isHermitian E ho k) (τ k))
    refine h.trans (le_of_eq ?_)
    have hq0 : ENNReal.ofReal q ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq
    rw [eLpNorm_const _ hq0 (IsProbabilityMeasure.ne_zero _), measure_univ, ENNReal.one_rpow]
    simp
  have hq1' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq1
  calc eLpNorm (clkS b E τ + clkT b E τ₀ τ) (ENNReal.ofReal q)
        ((growthLaw W r₀ k b).prod (layerLaw W b .separate))
      ≤ eLpNorm (clkS b E τ) (ENNReal.ofReal q) ((growthLaw W r₀ k b).prod (layerLaw W b .separate)) +
          eLpNorm (clkT b E τ₀ τ) (ENNReal.ofReal q)
            ((growthLaw W r₀ k b).prod (layerLaw W b .separate)) := eLpNorm_add_le hq1'
    _ ≤ ENNReal.ofReal S + ENNReal.ofReal C₃ * eLpNorm (fun ω => clkTrace
        (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal q) (growthLaw W r₀ k b) := add_le_add hS hT
    _ = _ := add_comm _ _

/-!
## 7. Base, consistency and conversions
-/

theorem clk_eLpNorm_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) {n : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖f x‖ₑ ^ n ∂ν ≤ ENNReal.ofReal B) :
    eLpNorm f (ENNReal.ofReal n) ν ≤ ENNReal.ofReal (B ^ (1 / (n : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hn0)
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hn0.le, ← ENNReal.ofReal_rpow_of_nonneg hB
    (by positivity)]
  simp_rw [ENNReal.rpow_natCast]
  exact ENNReal.rpow_le_rpow h (by positivity)

/-- The core clock under any growth law is the core injection under `pathLaw`. -/
theorem clk_eLpNorm_core {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (q : ℝ≥0∞) :
    eLpNorm (fun ω : GrowthSample W r₀ L => clkTrace (clkClock b E τ₀ τ ω 0)) q
        (growthLaw W r₀ L b) =
      eLpNorm (fun ω => clkTrace (clkCoreSource b E τ₀ ω)) q (pathLaw W r₀ b) := by
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hmp : MeasurePreserving (Prod.fst : GrowthSample W r₀ L → PathSample W r₀)
      (growthLaw W r₀ L b) (pathLaw W r₀ b) := by
    unfold growthLaw; exact measurePreserving_fst
  exact eLpNorm_comp_measurePreserving
    (clk_measurable_trace (clk_measurable_coreSource W r₀ b E τ₀)).aestronglyMeasurable hmp

/-- **Consistency of the growth laws**: for `k ≤ L` the law of the clock at step `k` does not
depend on the number `L` of exposed layers. -/
theorem clk_eLpNorm_trunc {W r₀ : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (q : ℝ≥0∞) (k : ℕ) : ∀ L, k ≤ L →
    eLpNorm (fun ω : GrowthSample W r₀ L => clkTrace (clkClock b E τ₀ τ ω k)) q
        (growthLaw W r₀ L b) =
      eLpNorm (fun ω : GrowthSample W r₀ k => clkTrace (clkClock b E τ₀ τ ω k)) q
        (growthLaw W r₀ k b)
  | 0, h => by obtain rfl : k = 0 := by omega
               rfl
  | L + 1, h => by
    rcases Nat.lt_or_ge k (L + 1) with hk | hk
    · have ih := clk_eLpNorm_trunc (W := W) b E τ₀ τ q k L (by omega)
      rw [← ih]
      have e : (fun ω : GrowthSample W r₀ (L + 1) => clkTrace (clkClock b E τ₀ τ ω k)) =
          (fun ω : GrowthSample W r₀ L => clkTrace (clkClock b E τ₀ τ ω k)) ∘ pgTrunc := by
        funext ω
        simp only [Function.comp_apply, clkClock_pgTrunc b E τ₀ τ ω k (by omega)]
      rw [e, eLpNorm_comp_measurePreserving
        (clk_measurable_trace (clk_measurable_clock b E τ₀ τ k)).aestronglyMeasurable
        (clk_mp_pgTrunc W r₀ L b)]
    · obtain rfl : k = L + 1 := by omega
      rfl

theorem clk_lyap_zero {W r₀ m : ℕ} {b E K d' : ℝ} (hK : 0 ≤ K) (hd' : d' ≤ 1)
    (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool) :
    clkLyap W r₀ 0 b E K d' τ₀ τ m ≤
      ENNReal.ofReal (1 + K) * ∫⁻ ω, ‖clkTrace (clkClock b E τ₀ τ ω 0)‖ₑ ^ m ∂growthLaw W r₀ 0 b := by
  unfold clkLyap
  rw [← lintegral_const_mul _ ((clk_measurable_trace (clk_measurable_clock b E τ₀ τ 0)).enorm.pow_const m)]
  exact lintegral_mono fun ω => mul_le_mul' (clkWt_le hK hd' ω 0) le_rfl

/-- The exit event of the stopped clock is the exit event of the scalar exit bound. -/
theorem clk_not_reg_eq {W r₀ k : ℕ} (b E d' : ℝ) :
    {ω : GrowthSample W r₀ k | ¬ clkReg b E d' ω k} =
      {ω | ∃ j ≤ k, d' < matchedDistance b E (grownSchur E ω j)} := by
  ext ω; simp [clkReg]

/-!
## 8. The iterated bounds
-/

/-- **Iterated Lyapunov bound**: `M_k^{1/m} ≤ e^{C T₊} (x₀ + N_k B^{1/m})` for `k ≤ T₊ W`. -/
theorem clk_lyap_iter {W r₀ m : ℕ} (hm : 1 ≤ m) {b E K d' C B x₀ Tp : ℝ} (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hx₀ : 0 ≤ x₀) (hW : 0 < W) (τ₀ : Fin r₀ → Bool)
    (τ : ℕ → Fin 2 → Bool)
    (hS1 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ d' → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)‖ₑ ^ m ∂layerLaw W b .separate ≤
          ENNReal.ofReal ((1 + C / W) * ((1 + K * matchedDistance b E X) * clkTrace Y ^ m)))
    (hS2 : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ σ : Fin 2 → Bool,
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ)‖ₑ ^ m
          ∂layerLaw W b .separate ≤ ENNReal.ofReal B)
    (h0 : clkLyap W r₀ 0 b E K d' τ₀ τ m ^ (1 / (m : ℝ)) ≤ ENNReal.ofReal x₀)
    {k : ℕ} (hk : (k : ℝ) ≤ Tp * W) :
    clkLyap W r₀ k b E K d' τ₀ τ m ^ (1 / (m : ℝ)) ≤
      ENNReal.ofReal (Real.exp (C * Tp) * (x₀ + clkTagCount τ k * B ^ (1 / (m : ℝ)))) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hCW : 0 ≤ C / W := div_nonneg hC hWr.le
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + C / W) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hit := clk_iter (a := fun j => clkLyap W r₀ j b E K d' τ₀ τ m ^ (1 / (m : ℝ)))
    (c := fun j => if ∃ i, τ j i = true then ENNReal.ofReal B ^ (1 / (m : ℝ)) else 0) hone
    (fun j => clk_lyap_step (k := j) hm hK hC τ₀ τ hS1 hS2) k
  rw [clk_sum_tag, ENNReal.ofReal_rpow_of_nonneg hB (by positivity)] at hit
  refine hit.trans ?_
  have hβ0 : 0 ≤ B ^ (1 / (m : ℝ)) := by positivity
  have hpow : (1 + C / W) ^ k ≤ Real.exp (C * Tp) := by
    refine (clk_pow_le_exp hCW k).trans (Real.exp_le_exp.mpr ?_)
    rw [div_mul_eq_mul_div, div_le_iff₀ hWr]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hk hC
  rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc ENNReal.ofReal ((1 + C / W) ^ k) * (clkLyap W r₀ 0 b E K d' τ₀ τ m ^ (1 / (m : ℝ)) +
        ENNReal.ofReal (((clkTagCount τ k : ℕ) : ℝ) * B ^ (1 / (m : ℝ))))
      ≤ ENNReal.ofReal ((1 + C / W) ^ k) * (ENNReal.ofReal x₀ +
        ENNReal.ofReal (((clkTagCount τ k : ℕ) : ℝ) * B ^ (1 / (m : ℝ)))) := by gcongr
    _ = ENNReal.ofReal ((1 + C / W) ^ k * (x₀ + clkTagCount τ k * B ^ (1 / (m : ℝ)))) := by
        rw [← ENNReal.ofReal_add hx₀ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (by positivity))

/-- **Iterated crude bound**: `‖u_k‖_q ≤ A^k (z₀ + k S)`. -/
theorem clk_crude_iter {W r₀ : ℕ} {b E q A S z₀ : ℝ} (hq1 : 1 ≤ q) (hA : 1 ≤ A) (hS : 0 ≤ S)
    (hz₀ : 0 ≤ z₀) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (hU : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)) (ENNReal.ofReal q)
          (layerLaw W b .separate) ≤ ENNReal.ofReal (A * clkTrace Y))
    (hG : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ σ : Fin 2 → Bool,
        eLpNorm (fun ℓ => clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ))
          (ENNReal.ofReal q) (layerLaw W b .separate) ≤ ENNReal.ofReal S)
    (h0 : eLpNorm (fun ω => clkTrace (clkCoreSource b E τ₀ ω)) (ENNReal.ofReal q) (pathLaw W r₀ b) ≤
      ENNReal.ofReal z₀) (k : ℕ) :
    eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal q) (growthLaw W r₀ k b) ≤
      ENNReal.ofReal (A ^ k * (z₀ + k * S)) := by
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hA
  have hit := clk_iter (a := fun j => eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω j))
      (ENNReal.ofReal q) (growthLaw W r₀ j b)) (c := fun _ => ENNReal.ofReal S) hone
    (fun j => clk_crude_step (k := j) hq1 (by linarith) τ₀ τ hU hG) k
  rw [clk_eLpNorm_core, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hit
  refine hit.trans ?_
  rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  calc ENNReal.ofReal (A ^ k) * (eLpNorm (fun ω => clkTrace (clkCoreSource b E τ₀ ω))
        (ENNReal.ofReal q) (pathLaw W r₀ b) + ENNReal.ofReal ((k : ℝ) * S))
      ≤ ENNReal.ofReal (A ^ k) * (ENNReal.ofReal z₀ + ENNReal.ofReal ((k : ℝ) * S)) := by gcongr
    _ = ENNReal.ofReal (A ^ k * (z₀ + k * S)) := by
        rw [← ENNReal.ofReal_add hz₀ (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- **Exit removal arithmetic**: `e^{-cW log W/(2m)} A^k (z₀ + kS) ≤ 1` for `k ≤ T₊W`,
`W ≥ W₀`. -/
theorem clk_exit_final {c A z₀ S Tp : ℝ} (m : ℕ) (hm : 1 ≤ m) (hc : 0 < c) (hA : 1 ≤ A)
    (hz₀ : 0 ≤ z₀) (hS : 0 ≤ S) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ k : ℕ, (k : ℝ) ≤ Tp * W →
      Real.exp (-(c * W * Real.log W) * (1 / (2 * m : ℝ))) * (A ^ k * (z₀ + k * S)) ≤ 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨W₀, hW₀⟩ := clk_exit_small (α := c / (2 * m)) (β := Tp * Real.log A)
    (γ := max z₀ (Tp * S)) (by positivity) (le_max_of_le_left hz₀)
  refine ⟨W₀, fun W hW hW0 k hk => ?_⟩
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have h1 : A ^ k ≤ Real.exp (Tp * Real.log A * W) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < A), ← Real.exp_nat_mul, Real.exp_log (by linarith)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have h2 : z₀ + k * S ≤ max z₀ (Tp * S) + max z₀ (Tp * S) * W := by
    have h3 : (k : ℝ) * S ≤ Tp * S * W := by nlinarith
    have h4 : Tp * S * W ≤ max z₀ (Tp * S) * W :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hWr.le
    linarith [le_max_left z₀ (Tp * S)]
  have hW := hW₀ W hW hW0
  calc Real.exp (-(c * W * Real.log W) * (1 / (2 * m : ℝ))) * (A ^ k * (z₀ + k * S))
      ≤ Real.exp (-(c * W * Real.log W) * (1 / (2 * m : ℝ))) *
          (Real.exp (Tp * Real.log A * W) * (max z₀ (Tp * S) + max z₀ (Tp * S) * W)) := by
        gcongr
    _ = Real.exp (Tp * Real.log A * W - c / (2 * m) * W * Real.log W) *
          (max z₀ (Tp * S) + max z₀ (Tp * S) * W) := by
        rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 1 := hW

/-!
## 9. The master bound
-/

/-- **Master bound**: for every integer `m = n + 2`,
`‖u_{r₀+2k}‖_m ≤ Γ + β N_k` under `growthLaw W r₀ k b`, for `W ≥ W₀`, both cores,
`r₀ + 2k ≤ TW`, `E ∈ I`, every core tag `τ₀` and layer tags `τ`, with `N_k` the number of
tagged layers among the first `k`. -/
theorem clk_master (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ n : ℕ,
    ∃ (Γ β : ℝ) (W₀ : ℕ), 0 ≤ Γ ∧ 0 ≤ β ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W →
      ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ k : ℕ, ((r₀ + 2 * k : ℕ) : ℝ) ≤ T * W →
      ∀ E ∈ bulkInterval κ, ∀ (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool),
        eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal ((n + 2 : ℕ) : ℝ))
          (growthLaw W r₀ k b) ≤ ENNReal.ofReal (Γ + β * clkTagCount τ k) := by
  intro b hb0 hb1 κ T hκ n
  have hm1 : 1 ≤ n + 2 := by omega
  have hm0 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
  have h2m1 : (1 : ℝ) ≤ ((2 * (n + 2) : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  obtain ⟨K, d₁, C, W₁, hK, hd₁, hC, hS1⟩ := clk_step_weighted hcount hgrad b hb0 hb1 κ hκ n
  obtain ⟨B, W₂, hB, hS2⟩ := clk_step_source hcount b hb0 hb1 κ hκ K hK (n + 2) hm1
  obtain ⟨B', W₂', hB', hS2'⟩ := clk_step_source hcount b hb0 hb1 κ hκ 0 le_rfl (2 * (n + 2))
    (by omega)
  obtain ⟨C₃, W₃, hunr⟩ := (weightedLayer_holds hcount hgrad).unrestricted b hb0 hb1 κ hκ
    ((2 * (n + 2) : ℕ) : ℝ) h2m1
  obtain ⟨B₀, W₄, hB₀, hcore⟩ := clk_core_moments hcount b hb0 hb1 κ hκ
    ((2 * (n + 2) : ℕ) : ℝ) h2m1
  obtain ⟨d₀x, hd₀x, hexit⟩ := (scalarRecursionContract_holds hcount hgrad).exit b hb0 hb1 κ T hκ
  obtain ⟨d', hd'0, hd'1, hd'x, hd'1'⟩ : ∃ d', 0 < d' ∧ d' ≤ d₁ ∧ d' ≤ d₀x ∧ d' ≤ 1 :=
    ⟨min (min d₁ d₀x) 1, lt_min (lt_min hd₁ hd₀x) one_pos,
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  obtain ⟨c, W₅, hc, hexit'⟩ := hexit d' hd'0 hd'x
  obtain ⟨Tp, hTp0, hTp⟩ : ∃ t, 0 ≤ t ∧ T ≤ t := ⟨max T 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨A, hA1, hA⟩ : ∃ A, 1 ≤ A ∧ C₃ ≤ A := ⟨max C₃ 1, le_max_right _ _, le_max_left _ _⟩
  set S' := B' ^ (1 / ((2 * (n + 2) : ℕ) : ℝ)) with hS'
  have hS'0 : 0 ≤ S' := by positivity
  set x₀ := ((1 + K) * B₀ ^ (n + 2)) ^ (1 / ((n + 2 : ℕ) : ℝ)) with hx₀
  have hx₀0 : 0 ≤ x₀ := by positivity
  obtain ⟨W₆, hW₆⟩ := clk_exit_final (c := c) (A := A) (z₀ := B₀) (S := S') (Tp := Tp) (n + 2)
    hm1 hc hA1 hB₀ hS'0
  refine ⟨Real.exp (C * Tp) * x₀ + 1, Real.exp (C * Tp) * B ^ (1 / ((n + 2 : ℕ) : ℝ)),
    max (max (max W₁ W₂) (max W₂' W₃)) (max (max W₄ W₅) W₆), by positivity, by positivity, ?_⟩
  intro W hW hW0 r₀ hr₀ k hk E hE τ₀ τ
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hW)
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hW)
  have hW2' : W₂' ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hW)
  have hW3 : W₃ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hW)
  have hW4 : W₄ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hW)
  have hW5 : W₅ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hW)
  have hW6 : W₆ ≤ W := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hkT : (k : ℝ) ≤ Tp * W := by
    have h1 : (k : ℝ) ≤ ((r₀ + 2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ r₀ + 2 * k)
    exact h1.trans (hk.trans (mul_le_mul_of_nonneg_right hTp hWr.le))
  have hgl := clk_isProb_growthLaw W r₀ k b
  -- the core injection
  have hcore' := hcore W hW0 hW4 r₀ hr₀ E hE τ₀
  have hcm : eLpNorm (fun ω => clkTrace (clkCoreSource b E τ₀ ω)) (ENNReal.ofReal ((n + 2 : ℕ) : ℝ))
      (pathLaw W r₀ b) ≤ ENNReal.ofReal B₀ := by
    have := fun t => isProbabilityMeasure_gueMeasure W t
    have hpl : IsProbabilityMeasure (pathLaw W r₀ b) := by unfold pathLaw; infer_instance
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by push_cast; linarith))).trans
      hcore'
  -- the Lyapunov part
  have hS1' : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      matchedDistance b E X ≤ d' → ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        ∫⁻ ℓ, ENNReal.ofReal (1 + K * matchedDistance b E (layerSchur .separate E X ℓ)) *
            ‖clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ)‖ₑ ^ (n + 2) ∂layerLaw W b .separate ≤
          ENNReal.ofReal ((1 + C / W) * ((1 + K * matchedDistance b E X) * clkTrace Y ^ (n + 2))) :=
    fun X hX hd Y hY => hS1 W hW0 hW1 X hX E hE (hd.trans hd'1) Y hY
  have hS2'' := fun X hX σ => hS2 W hW0 hW2 X hX E hE σ
  have hL0 : clkLyap W r₀ 0 b E K d' τ₀ τ (n + 2) ^ (1 / ((n + 2 : ℕ) : ℝ)) ≤ ENNReal.ofReal x₀ := by
    have h1 := clk_lyap_zero (W := W) (m := n + 2) (b := b) (E := E) hK hd'1' τ₀ τ
    have h2 : ∫⁻ ω, ‖clkTrace (clkClock b E τ₀ τ ω 0)‖ₑ ^ (n + 2) ∂growthLaw W r₀ 0 b ≤
        ENNReal.ofReal (B₀ ^ (n + 2)) := by
      refine clk_lintegral_pow_le
        (clk_measurable_trace (clk_measurable_clock b E τ₀ τ 0)).aestronglyMeasurable hm1 hB₀ ?_
      rw [clk_eLpNorm_core]; exact hcm
    rw [hx₀, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.rpow_le_rpow (h1.trans ?_) (by positivity)
    rw [ENNReal.ofReal_mul (by linarith)]
    exact mul_le_mul' le_rfl h2
  have hLy := clk_lyap_iter hm1 hK hC hB hx₀0 hW0 τ₀ τ hS1' hS2'' hL0 hkT
  -- the crude part
  have hU : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, Y.PosSemidef →
        eLpNorm (fun ℓ => clkTrace ((clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ))
          (ENNReal.ofReal ((2 * (n + 2) : ℕ) : ℝ)) (layerLaw W b .separate) ≤
          ENNReal.ofReal (A * clkTrace Y) := fun X hX Y hY =>
    (hunr W hW0 hW3 X hX E hE Y hY).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hA (clkTrace_nonneg hY)))
  have hG : ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → ∀ σ : Fin 2 → Bool,
      eLpNorm (fun ℓ => clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ))
        (ENNReal.ofReal ((2 * (n + 2) : ℕ) : ℝ)) (layerLaw W b .separate) ≤ ENNReal.ofReal S' := by
    intro X hX σ
    have h := hS2' W hW0 hW2' X hX E hE σ
    simp only [zero_mul, add_zero, ENNReal.ofReal_one, one_mul] at h
    have hGm : Measurable (fun ℓ : LayerSample W .separate =>
        clkTrace ((clkG12 b E X ℓ)ᴴ * clkProj σ * clkG12 b E X ℓ)) := by
      have hg := clk_measurable_G12 b E (W := W) (measurable_const (a := X)) measurable_id
      exact clk_measurable_trace (srec_measurable_mul
        (srec_measurable_mul (srec_measurable_conjTranspose hg) measurable_const) hg)
    exact clk_eLpNorm_le_of_lintegral hGm.aestronglyMeasurable (by omega) hB' h
  have hz := clk_crude_iter (k := k) (by exact h2m1) hA1 hS'0 hB₀ τ₀ τ hU hG hcore'
  -- the exit event
  have hP : growthLaw W r₀ k b {ω | ¬ clkReg b E d' ω k} ≤
      ENNReal.ofReal (Real.exp (-(c * W * Real.log W))) := by
    rw [clk_not_reg_eq]; exact hexit' W hW5 hW0 r₀ hr₀ k hk E hE
  have hsplit := clk_split (W := W) (k := k) (m := n + 2) hm1 (d' := d') hK τ₀ τ (b := b) (E := E)
  have e2 : (2 * (((n + 2 : ℕ) : ℝ))) = ((2 * (n + 2) : ℕ) : ℝ) := by push_cast; ring
  rw [e2] at hsplit
  refine hsplit.trans ?_
  have hPr : growthLaw W r₀ k b {ω | ¬ clkReg b E d' ω k} ^ (1 / (((2 * (n + 2) : ℕ) : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-(c * W * Real.log W) * (1 / (2 * ((n + 2 : ℕ) : ℝ))))) := by
    refine (ENNReal.rpow_le_rpow hP (by positivity)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul, ← e2]
  have hex := hW₆ W hW6 hW0 k hkT
  calc clkLyap W r₀ k b E K d' τ₀ τ (n + 2) ^ (1 / ((n + 2 : ℕ) : ℝ)) +
        growthLaw W r₀ k b {ω | ¬ clkReg b E d' ω k} ^ (1 / (((2 * (n + 2) : ℕ) : ℝ))) *
          eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k))
            (ENNReal.ofReal ((2 * (n + 2) : ℕ) : ℝ)) (growthLaw W r₀ k b)
      ≤ ENNReal.ofReal (Real.exp (C * Tp) * (x₀ + clkTagCount τ k * B ^ (1 / ((n + 2 : ℕ) : ℝ)))) +
          ENNReal.ofReal (Real.exp (-(c * W * Real.log W) * (1 / (2 * ((n + 2 : ℕ) : ℝ))))) *
            ENNReal.ofReal (A ^ k * (B₀ + k * S')) := add_le_add hLy (mul_le_mul' hPr hz)
    _ ≤ ENNReal.ofReal (Real.exp (C * Tp) * (x₀ + clkTagCount τ k * B ^ (1 / ((n + 2 : ℕ) : ℝ)))) +
          ENNReal.ofReal 1 := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        gcongr
    _ = ENNReal.ofReal (Real.exp (C * Tp) * x₀ + 1 +
          Real.exp (C * Tp) * B ^ (1 / ((n + 2 : ℕ) : ℝ)) * clkTagCount τ k) := by
        rw [← ENNReal.ofReal_add (by positivity) zero_le_one]
        congr 1; ring

/-!
## 10. The clock-moments lemma
-/

/-- **The clock-moments lemma**, including the tagged clock moments; the clocks follow the tagged
clock identity along the growing path (`clkClock`).

* Law and norms: `L^p` norms of normalized traces `u_r = W⁻¹ Re Tr Y_r` (`clkTrace`) at path
  length `r`, either under the growing-path law `growthLaw W r₀ L b` (core `r₀ ∈ {1, 2}`, `L`
  independent fresh separate-port layers, `GUE_W(c/W)` blocks and `Gin(b/W)` bonds; `r = r₀ + 2k`,
  `k ≤ L`) or under the path law `pathLaw W r b`. These are full prior moments: no event, in
  particular not the scalar exit event, is removed.
* Domain: deterministic `E ∈ bulkInterval κ` (`z = z_∂(E)`, `R_r = (z - X_r)⁻¹`), `r ≤ TW`.
* Full clock (`P = I` on the core and at every layer): `‖u_r‖_p ≤ C_p (r + 1)`, (i) for the
  physical energy clock `Y_r = M* M = R_r* X_r' R_r`, `M = (H_r - E)⁻¹ B_p R_r`,
  `X_r' = B_p* (H_r - E)⁻² B_p` the energy derivative of the Schur matrix of the path
  (`clkCoreSource b E (fun _ => true)`; `clkCoreSource_eq_source`), under `pathLaw W r b` for
  every `1 ≤ r ≤ TW`; (ii) for the recursion `clkClock` with `τ₀ = τ k = true` along the growth
  (the two agree almost surely, `clk_fullClock_eq_source`).
* Tagged clock (the tagged clock moments): any core tag `τ₀` (the start `Y = 0` is `τ₀ = false`)
  and layer tags `τ` with `P ≠ 0` at no more than two layers (`clkTagCount τ L ≤ 2`; in the paper: "for
  an edge tag, `P = 0` except at at most two steps"; this contains every tag on at most two
  physical blocks): `sup_{k ≤ L} ‖u_{r₀+2k}‖_p ≤ C_p`.
* Quantifier order and uniformity: `b`, `κ`, `T` and the fixed moment order `p ≥ 1` first; then
  `C_p ≥ 0` and `W₀(p)`; then uniformly in `W ≥ W₀`, `r`, `r₀`, `L`, `k`, `E` and the tags. -/
def ClockMomentsStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → 0 < W →
      (∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ,
        eLpNorm (fun ω => clkTrace (clkCoreSource b E (fun _ => true) ω)) (ENNReal.ofReal p)
          (pathLaw W r b) ≤ ENNReal.ofReal (C * ((r : ℝ) + 1))) ∧
      ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ, ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W →
      ∀ E ∈ bulkInterval κ,
        (∀ k, k ≤ L →
          eLpNorm (fun ω => clkTrace (clkClock b E (fun _ => true) (fun _ _ => true) ω k))
            (ENNReal.ofReal p) (growthLaw W r₀ L b) ≤
            ENNReal.ofReal (C * (((r₀ + 2 * k : ℕ) : ℝ) + 1))) ∧
        ∀ (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool), clkTagCount τ L ≤ 2 →
          ∀ k, k ≤ L →
            eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal p)
              (growthLaw W r₀ L b) ≤ ENNReal.ofReal C

/-- The energy clock under `pathLaw W (r₀ + 2k)` has the law of the full clock at step `k`. -/
theorem clk_eLpNorm_energy {W r₀ k : ℕ} {b : ℝ} (hb1 : b < 1 / 2) (E : ℝ)
    (hz : 0 < (boundaryZ b E).im) (hr₀ : 1 ≤ r₀) (q : ℝ≥0∞) :
    eLpNorm (fun ω => clkTrace (clkCoreSource b E (fun _ => true) ω)) q
        (pathLaw W (r₀ + 2 * k) b) =
      eLpNorm (fun ω => clkTrace (clkClock b E (fun _ => true) (fun _ _ => true) ω k)) q
        (growthLaw W r₀ k b) := by
  have hP := measurePreserving_pgPath (W := W) b hr₀ k k le_rfl
  rw [← eLpNorm_comp_measurePreserving
    (clk_measurable_trace (clk_measurable_coreSource W _ b E _)).aestronglyMeasurable hP]
  refine eLpNorm_congr_ae ?_
  filter_upwards [clk_fullClock_eq_source (L := k) hb1 E hz hr₀] with ω hω
  simp only [Function.comp_apply, hω k le_rfl]

/-- **The clock-moments lemma**, from `ConditionalBlockGUECount` and `GaussianLpGradient`. -/
theorem clockMoments_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : Internal.Contracts.Inputs.GaussianLpGradient) : ClockMomentsStatement := by
  intro b hb0 hb1 κ T hκ p hp
  obtain ⟨Γ, β, W₀, hΓ, hβ, hM⟩ := clk_master hcount hgrad b hb0 hb1 κ T hκ ⌈p⌉₊
  obtain ⟨η, hη, hbulk⟩ := srec_boundaryZ_im_lower (b := b) (by linarith) hκ
  have hpm : ENNReal.ofReal p ≤ ENNReal.ofReal ((⌈p⌉₊ + 2 : ℕ) : ℝ) := by
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [Nat.le_ceil p]
  have key : ∀ W : ℕ, W₀ ≤ W → 0 < W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) → ∀ L : ℕ,
      ((r₀ + 2 * L : ℕ) : ℝ) ≤ T * W → ∀ E ∈ bulkInterval κ, ∀ (τ₀ : Fin r₀ → Bool)
      (τ : ℕ → Fin 2 → Bool), ∀ k, k ≤ L →
        eLpNorm (fun ω => clkTrace (clkClock b E τ₀ τ ω k)) (ENNReal.ofReal p)
          (growthLaw W r₀ L b) ≤ ENNReal.ofReal (Γ + β * clkTagCount τ k) := by
    intro W hW hW0 r₀ hr₀ L hL E hE τ₀ τ k hk
    have hgl := clk_isProb_growthLaw W r₀ L b
    refine (eLpNorm_le_eLpNorm_of_exponent_le hpm).trans ?_
    rw [clk_eLpNorm_trunc b E τ₀ τ _ k L hk]
    refine hM W hW hW0 r₀ hr₀ k ?_ E hE τ₀ τ
    refine le_trans ?_ hL
    exact_mod_cast (by omega : r₀ + 2 * k ≤ r₀ + 2 * L)
  have hfull : ∀ (r₀ k : ℕ), (Γ + β * (clkTagCount (fun _ _ => true) k : ℝ)) ≤
      (Γ + 2 * β) * (((r₀ + 2 * k : ℕ) : ℝ) + 1) := by
    intro r₀ k
    have hN : (clkTagCount (fun _ _ => true) k : ℝ) ≤ k := by exact_mod_cast clkTagCount_le _ k
    have hkr : (k : ℝ) ≤ ((r₀ + 2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ r₀ + 2 * k)
    have hr0 : (0 : ℝ) ≤ ((r₀ + 2 * k : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  refine ⟨Γ + 2 * β, W₀, by positivity, fun W hW hW0 => ⟨?_, ?_⟩⟩
  · intro r hr hrT E hE
    obtain ⟨r₀, k, hr₀, rfl⟩ : ∃ r₀ k : ℕ, (r₀ = 1 ∨ r₀ = 2) ∧ r = r₀ + 2 * k := by
      rcases Nat.even_or_odd r with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨2, t - 1, Or.inr rfl, by omega⟩
      · exact ⟨1, t, Or.inl rfl, by omega⟩
    have hr₀1 : 1 ≤ r₀ := by rcases hr₀ with h | h <;> omega
    have hgl := clk_isProb_growthLaw W r₀ k b
    rw [clk_eLpNorm_energy hb1 E (lt_of_lt_of_le hη (hbulk E hE).1) hr₀1]
    refine (key W hW hW0 r₀ hr₀ k (by exact_mod_cast hrT) E hE _ _ k le_rfl).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have := hfull r₀ k
    push_cast at this ⊢
    exact this
  intro r₀ hr₀ L hL E hE
  refine ⟨fun k hk => ?_, fun τ₀ τ hτ k hk => ?_⟩
  · exact (key W hW hW0 r₀ hr₀ L hL E hE _ _ k hk).trans (ENNReal.ofReal_le_ofReal (hfull r₀ k))
  · refine (key W hW hW0 r₀ hr₀ L hL E hE τ₀ τ k hk).trans (ENNReal.ofReal_le_ofReal ?_)
    have hN : (clkTagCount τ k : ℝ) ≤ 2 := by
      exact_mod_cast (clkTagCount_mono τ hk).trans hτ
    nlinarith

end BlockBand.Layers
