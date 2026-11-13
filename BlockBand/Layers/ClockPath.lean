module

public import BlockBand.Layers.MatchedPath
public import BlockBand.Layers.WeightedLayer

/-!
# The full and tagged clocks along the growing path

The objects of the clock-moments lemma: the tagged clock recursion `Y₊ = 𝒢₁₂* P 𝒢₁₂ + L* Y L`,
`L = K 𝒢₁₂`, `K = z - X`, along the growing two-ended path (`GrowthSample`, `growthLaw`,
`grownSchur`). The file proves deterministic facts (positivity, truncation of the growth,
measurability), the almost-sure Hermitian property of the grown Schur matrices, the moments of the
core injection (`clk_core_moments`, from the Gaussian absorption lemma), and the energy identity:
one full-clock step maps the energy source `R* X' R` of a path to that of the grown path
(`clkCoreSource_pgGrow`), hence almost surely the full clock along the growth is `R_r* X_r' R_r`
of `pgPath ω k` (`clk_fullClock_eq_source`).

## Representation

* `clkProj τ` is the projection `P` onto the tagged blocks (`τ j = true`) of a layer or core.
* The clock starts from the **core injection** `clkCoreSource b E τ₀` on the core
  `PathSample W r₀`: with `M = (H_core - E)⁻¹ B_p R_{r₀}`, `Y_{r₀} = M* P_{τ₀} M`. For a core
  sample with Hermitian blocks (almost surely) this is `R* S R` with
  `S = B_p*(H - E)⁻¹ P (H - E)⁻¹ B_p`, the source `-Ẋ` of a perturbation `Ḣ = -P` of the tagged
  core blocks (`clkCoreSource_eq_source`); `τ₀ = false` is the start `Y = 0`, `τ₀ = true`
  the energy derivative `R* X'_{r₀} R` of the core (`X' = B_p*(H - E)⁻² B_p`).
* `clkStep b E τ X Y ℓ = 𝒢₁₂* P_τ 𝒢₁₂ + L* Y L` with `𝒢 = layerResolvent .separate E z_∂ X ℓ`
  (the tagged clock identity), and `clkClock b E τ₀ τ ω k` iterates it along `grownSchur`, using the
  tag `τ k` at layer `k`. The **full clock** is `τ₀ = τ k = true` (`P = I` at every step);
  a **tagged clock** has `τ k ≠ false` for at most two layers.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

/-!
## 1. The clocks
-/

/-- The normalized clock trace `u = W⁻¹ Re Tr Y`. -/
def clkTrace {W : ℕ} (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : ℝ :=
  (W : ℝ)⁻¹ * Y.trace.re

/-- The projection `P` onto the tagged blocks `{j | τ j}`. -/
def clkProj {k W : ℕ} (τ : Fin k → Bool) : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  diagonal fun x => if τ x.1 then 1 else 0

/-- The core factor `M = (H_core - E)⁻¹ B_p R_{r₀}`. -/
def clkCoreFactor {W r : ℕ} (b E : ℝ) (ω : PathSample W r) :
    Matrix (Fin r × Fin W) (Fin 2 × Fin W) ℂ :=
  (pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω * pathPortResolvent b E ω

/-- The core injection `Y_{r₀} = M* P_{τ₀} M` (`= R* S R`, `S = B_p*(H-E)⁻¹P(H-E)⁻¹B_p`, for a
core with Hermitian blocks: `clkCoreSource_eq_source`). -/
def clkCoreSource {W r : ℕ} (b E : ℝ) (τ₀ : Fin r → Bool) (ω : PathSample W r) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (clkCoreFactor b E ω).conjTranspose * clkProj (W := W) τ₀ * clkCoreFactor b E ω

/-- `𝒢₁₂` of a separate-port layer at `z = z_∂(E)`. -/
def clkG12 {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (layerResolvent .separate E (boundaryZ b E) X ℓ).toBlocks₁₂

/-- `L = K 𝒢₁₂`, `K = z_∂ - X` (the weighted factor of the weighted-layer lemma). -/
def clkL {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X) * clkG12 b E X ℓ

/-- **The tagged clock identity**: `Y₊ = 𝒢₁₂* P 𝒢₁₂ + L* Y L`. -/
def clkStep {W : ℕ} (b E : ℝ) (τ : Fin 2 → Bool) (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (clkG12 b E X ℓ)ᴴ * clkProj τ * clkG12 b E X ℓ + (clkL b E X ℓ)ᴴ * Y * clkL b E X ℓ

/-- **The clock along the growing path**: `Y_{r₀}` is the core injection, and layer `k` maps
`Y_{r₀+2k}` to `Y_{r₀+2k+2}` by the tagged clock identity with the old Schur matrix
`X = grownSchur E ω k` and the tag `τ k` (constant after `L`). -/
def clkClock {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ L) : ℕ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | 0 => clkCoreSource b E τ₀ ω.1
  | k + 1 =>
    if h : k < L then
      clkStep b E (τ k) (grownSchur E ω k) (clkClock b E τ₀ τ ω k) (ω.2 ⟨k, h⟩)
    else clkClock b E τ₀ τ ω k

/-- Number of tagged layers among the first `k`. -/
def clkTagCount (τ : ℕ → Fin 2 → Bool) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun j => ∃ i, τ j i = true).card

/-!
## 2. Positivity and traces
-/

theorem clkProj_posSemidef {k W : ℕ} (τ : Fin k → Bool) : (clkProj (W := W) τ).PosSemidef := by
  refine posSemidef_diagonal_iff.mpr fun x => ?_
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem clkProj_eq_zero {k W : ℕ} {τ : Fin k → Bool} (h : ∀ i, τ i = false) :
    clkProj (W := W) τ = 0 := by
  ext x y
  simp [clkProj, h, diagonal_apply]

theorem clkProj_trace_le {k W : ℕ} (τ : Fin k → Bool) :
    (clkProj (W := W) τ).trace.re ≤ k * W := by
  simp only [clkProj, trace_diagonal, Complex.re_sum]
  calc ∑ x : Fin k × Fin W, (if τ x.1 then (1 : ℂ) else 0).re
      ≤ ∑ _x : Fin k × Fin W, (1 : ℝ) := Finset.sum_le_sum fun x _ => by split_ifs <;> simp
    _ = k * W := by simp

theorem clkStep_posSemidef {W : ℕ} (b E : ℝ) (τ : Fin 2 → Bool)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y.PosSemidef) (ℓ : LayerSample W .separate) : (clkStep b E τ X Y ℓ).PosSemidef :=
  ((clkProj_posSemidef τ).conjTranspose_mul_mul_same _).add (hY.conjTranspose_mul_mul_same _)

theorem clkCoreSource_posSemidef {W r : ℕ} (b E : ℝ) (τ₀ : Fin r → Bool) (ω : PathSample W r) :
    (clkCoreSource b E τ₀ ω).PosSemidef :=
  (clkProj_posSemidef τ₀).conjTranspose_mul_mul_same _

theorem clkClock_posSemidef {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ L) : ∀ k, (clkClock b E τ₀ τ ω k).PosSemidef
  | 0 => clkCoreSource_posSemidef b E τ₀ ω.1
  | k + 1 => by
    have ih := clkClock_posSemidef b E τ₀ τ ω k
    simp only [clkClock]
    split_ifs
    · exact clkStep_posSemidef b E _ _ ih _
    · exact ih

theorem clkTrace_add {W : ℕ} (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    clkTrace (A + B) = clkTrace A + clkTrace B := by
  simp only [clkTrace, trace_add, Complex.add_re, mul_add]

theorem clkTrace_nonneg {W : ℕ} {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : Y.PosSemidef) : 0 ≤ clkTrace Y :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (wl_trace_re_nonneg hY)

/-- The injected trace `s = W⁻¹ Re Tr 𝒢₁₂* P 𝒢₁₂` is at most `2 ‖𝒢‖²` (`dim P ≤ 2W`). -/
theorem clkTrace_source_le {W : ℕ} (τ : Fin 2 → Bool)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    clkTrace ((G.toBlocks₁₂)ᴴ * clkProj τ * G.toBlocks₁₂) ≤ 2 * ‖G‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [clkTrace]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, h1⟩ := wl_trace_weight_le (clkProj_posSemidef (W := W) τ) G.toBlocks₁₂
  have h2 := clkProj_trace_le (W := W) τ
  have h3 : ‖G.toBlocks₁₂‖ ^ 2 ≤ ‖G‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (wl_norm_toBlocks12_le G) 2
  unfold clkTrace
  rw [inv_mul_le_iff₀ hW0]
  calc (G.toBlocks₁₂ᴴ * clkProj τ * G.toBlocks₁₂).trace.re
      ≤ ‖G.toBlocks₁₂‖ ^ 2 * (clkProj (W := W) τ).trace.re := h1
    _ ≤ ‖G‖ ^ 2 * (2 * W) := by
        have : ((2 : ℕ) : ℝ) * W = 2 * W := by norm_num
        rw [this] at h2
        exact mul_le_mul h3 h2 (by
          have := wl_trace_re_nonneg (clkProj_posSemidef (W := W) τ); linarith) (by positivity)
    _ = W * (2 * ‖G‖ ^ 2) := by ring

/-!
## 3. Truncation of the growth
-/

theorem clk_grownSchur_pgTrunc {W r₀ L : ℕ} (E : ℝ) (ω : GrowthSample W r₀ (L + 1)) :
    ∀ j, j ≤ L → grownSchur E (pgTrunc ω) j = grownSchur E ω j
  | 0, _ => rfl
  | j + 1, hj => by
    have hjL : j < L := by omega
    have hjL' : j < L + 1 := by omega
    have ih := clk_grownSchur_pgTrunc E ω j (by omega)
    simp only [grownSchur, hjL, hjL', dite_true, ih]
    rfl

theorem clk_grownSchur_last {W r₀ L : ℕ} (E : ℝ) (ω : GrowthSample W r₀ (L + 1)) :
    grownSchur E ω (L + 1) =
      layerSchur .separate E (grownSchur E (pgTrunc ω) L) (ω.2 (Fin.last L)) := by
  rw [clk_grownSchur_pgTrunc E ω L le_rfl]
  simp only [grownSchur, Nat.lt_succ_self, dite_true]
  rfl

theorem clkClock_pgTrunc {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ (L + 1)) :
    ∀ j, j ≤ L → clkClock b E τ₀ τ (pgTrunc ω) j = clkClock b E τ₀ τ ω j
  | 0, _ => rfl
  | j + 1, hj => by
    have hjL : j < L := by omega
    have hjL' : j < L + 1 := by omega
    have ih := clkClock_pgTrunc b E τ₀ τ ω j (by omega)
    simp only [clkClock, hjL, hjL', dite_true, ih, clk_grownSchur_pgTrunc E ω j (by omega)]
    rfl

theorem clkClock_last {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool) (τ : ℕ → Fin 2 → Bool)
    (ω : GrowthSample W r₀ (L + 1)) :
    clkClock b E τ₀ τ ω (L + 1) =
      clkStep b E (τ L) (grownSchur E (pgTrunc ω) L) (clkClock b E τ₀ τ (pgTrunc ω) L)
        (ω.2 (Fin.last L)) := by
  rw [clk_grownSchur_pgTrunc E ω L le_rfl, clkClock_pgTrunc b E τ₀ τ ω L le_rfl]
  simp only [clkClock, Nat.lt_succ_self, dite_true]
  rfl

/-- `pgTrunc` is measure preserving `growthLaw (L+1) → growthLaw L`. -/
theorem clk_mp_pgTrunc (W r₀ L : ℕ) (b : ℝ) :
    MeasurePreserving (pgTrunc (W := W) (r₀ := r₀) (L := L)) (growthLaw W r₀ (L + 1) b)
      (growthLaw W r₀ L b) := by
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  exact (measurePreserving_fst (μ := growthLaw W r₀ L b) (ν := layerLaw W b .separate)).comp
    (pg_mp_splitLast W r₀ L b)

/-!
## 4. Measurability
-/

/-- The layer matrix with `X` is the one with `X = 0` minus `diag(X, 0)`. -/
theorem clk_layerMatrix_eq {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    layerMatrix σ E z X ω = layerMatrix σ E z 0 ω + fromBlocks (-X) 0 0 0 := by
  rw [layerMatrix, layerMatrix, fromBlocks_add]
  congr 1 <;> abel

/-- The layer resolvent is jointly measurable in `(X, ω)`. -/
theorem clk_measurable_layerResolvent {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (σ : LayerShape)
    (E : ℝ) (z : ℂ) {Xf : Ω → Matrix (PhysSite W σ) (PhysSite W σ) ℂ} {ℓf : Ω → LayerSample W σ}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => layerResolvent σ E z (Xf t) (ℓf t)) := by
  have e : (fun t => layerMatrix σ E z (Xf t) (ℓf t)) =
      fun t => layerMatrix σ E z 0 (ℓf t) + fromBlocks (-Xf t) 0 0 0 :=
    funext fun t => clk_layerMatrix_eq σ E z (Xf t) (ℓf t)
  have hc : Continuous (fun A : Matrix (PhysSite W σ) (PhysSite W σ) ℂ =>
      (fromBlocks (-A) 0 0 0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) :=
    continuous_id.neg.matrix_fromBlocks continuous_const continuous_const continuous_const
  have hM : Measurable (fun t => layerMatrix σ E z (Xf t) (ℓf t)) := by
    rw [e]
    exact ((measurable_layerMatrix σ E z 0).comp hℓ).add (hc.measurable.comp hX)
  exact measurable_matrix_inv.comp hM

theorem clk_measurable_G12 {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (b E : ℝ)
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .separate}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => clkG12 b E (Xf t) (ℓf t)) :=
  wl_continuous_toBlocks12.measurable.comp
    (clk_measurable_layerResolvent .separate E (boundaryZ b E) hX hℓ)

theorem clk_measurable_L {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (b E : ℝ)
    {Xf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .separate}
    (hX : Measurable Xf) (hℓ : Measurable ℓf) :
    Measurable (fun t => clkL b E (Xf t) (ℓf t)) := by
  have hK : Measurable (fun t => boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      Xf t) := measurable_const.sub hX
  exact srec_measurable_mul hK (clk_measurable_G12 b E hX hℓ)

theorem clk_measurable_step {Ω : Type*} [MeasurableSpace Ω] {W : ℕ} (b E : ℝ) (τ : Fin 2 → Bool)
    {Xf Yf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ℓf : Ω → LayerSample W .separate}
    (hX : Measurable Xf) (hY : Measurable Yf) (hℓ : Measurable ℓf) :
    Measurable (fun t => clkStep b E τ (Xf t) (Yf t) (ℓf t)) := by
  have hG := clk_measurable_G12 b E hX hℓ
  have hL := clk_measurable_L b E hX hℓ
  unfold clkStep
  exact (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hG)
    measurable_const) hG).add
    (srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose hL) hY) hL)

theorem clk_measurable_layer {W r₀ L : ℕ} (k : Fin L) :
    Measurable (fun ω : GrowthSample W r₀ L => ω.2 k) :=
  (measurable_pi_apply k).comp measurable_snd

theorem clk_measurable_grownSchur {W r₀ L : ℕ} (E : ℝ) :
    ∀ k, Measurable (fun ω : GrowthSample W r₀ L => grownSchur E ω k)
  | 0 => (measurable_pathSchur W r₀ E).comp measurable_fst
  | k + 1 => by
    have ih := clk_measurable_grownSchur (W := W) (r₀ := r₀) (L := L) E k
    by_cases h : k < L
    · simp only [grownSchur, h, dite_true]
      exact srec_measurable_layerSchur E ih (clk_measurable_layer ⟨k, h⟩)
    · simp only [grownSchur, h, dite_false]
      exact ih

theorem clk_measurable_pathPortResolvent (W r : ℕ) (b E : ℝ) :
    Measurable (fun ω : PathSample W r => pathPortResolvent b E ω) :=
  measurable_matrix_inv.comp (measurable_const.sub (measurable_pathSchur W r E))

theorem clk_measurable_coreFactor (W r : ℕ) (b E : ℝ) :
    Measurable (fun ω : PathSample W r => clkCoreFactor b E ω) := by
  have hM : Measurable (fun ω : PathSample W r => (pathMatrix ω - (E : ℂ) • 1)⁻¹) :=
    measurable_matrix_inv.comp ((measurable_pathMatrix W r).sub measurable_const)
  exact srec_measurable_mul (srec_measurable_mul hM (measurable_pathPortCoupling W r))
    (clk_measurable_pathPortResolvent W r b E)

theorem clk_measurable_coreSource (W r : ℕ) (b E : ℝ) (τ₀ : Fin r → Bool) :
    Measurable (fun ω : PathSample W r => clkCoreSource b E τ₀ ω) := by
  have h := clk_measurable_coreFactor W r b E
  exact srec_measurable_mul (srec_measurable_mul (srec_measurable_conjTranspose h)
    measurable_const) h

theorem clk_measurable_clock {W r₀ L : ℕ} (b E : ℝ) (τ₀ : Fin r₀ → Bool)
    (τ : ℕ → Fin 2 → Bool) :
    ∀ k, Measurable (fun ω : GrowthSample W r₀ L => clkClock b E τ₀ τ ω k)
  | 0 => (clk_measurable_coreSource W r₀ b E τ₀).comp measurable_fst
  | k + 1 => by
    have ih := clk_measurable_clock (W := W) (r₀ := r₀) (L := L) b E τ₀ τ k
    by_cases h : k < L
    · simp only [clkClock, h, dite_true]
      exact clk_measurable_step b E _ (clk_measurable_grownSchur E k) ih
        (clk_measurable_layer ⟨k, h⟩)
    · simp only [clkClock, h, dite_false]
      exact ih

theorem clk_measurable_trace {Ω : Type*} [MeasurableSpace Ω] {W : ℕ}
    {Yf : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : Measurable Yf) :
    Measurable (fun t => clkTrace (Yf t)) := by
  have hc : Continuous (fun Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => clkTrace Y) := by
    unfold clkTrace; fun_prop
  exact hc.measurable.comp hY

/-!
## 5. Almost surely Hermitian blocks
-/

/-- Every Gaussian block of the growth sample (core and layers) is Hermitian. -/
def clkGood {W r₀ L : ℕ} (ω : GrowthSample W r₀ L) : Prop :=
  (∀ j, (ω.1.1 j).IsHermitian) ∧ ∀ i j, ((ω.2 i).1 j).IsHermitian

theorem clk_ae_good (W r₀ L : ℕ) (b : ℝ) : ∀ᵐ ω ∂growthLaw W r₀ L b, clkGood ω := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have := bond_isProbabilityMeasure_layerLaw W b .separate
  have hpl : IsProbabilityMeasure (pathLaw W r₀ b) := by unfold pathLaw; infer_instance
  have h1 : ∀ᵐ ω ∂growthLaw W r₀ L b, ∀ j, (ω.1.1 j).IsHermitian := by
    have hA := ae_blocks_isHermitian r₀ W (Real.toNNReal ((1 - 2 * b) / W))
    have hP : ∀ᵐ y ∂pathLaw W r₀ b, ∀ j, (y.1 j).IsHermitian := by
      unfold pathLaw
      exact (Measure.quasiMeasurePreserving_fst).ae hA
    unfold growthLaw
    exact (Measure.quasiMeasurePreserving_fst).ae hP
  have h2 : ∀ᵐ ω ∂growthLaw W r₀ L b, ∀ i j, ((ω.2 i).1 j).IsHermitian := by
    rw [ae_all_iff]
    intro i
    have hl := lct_ae_blocks_isHermitian W b .separate
    have hmp : MeasurePreserving (fun ω : GrowthSample W r₀ L => ω.2 i) (growthLaw W r₀ L b)
        (layerLaw W b .separate) := by
      unfold growthLaw
      exact (measurePreserving_eval (fun _ : Fin L => layerLaw W b .separate) i).comp
        (measurePreserving_snd (μ := pathLaw W r₀ b))
    exact hmp.quasiMeasurePreserving.ae hl
  filter_upwards [h1, h2] with ω h1 h2 using ⟨h1, h2⟩

theorem clkGood_pgTrunc {W r₀ L : ℕ} {ω : GrowthSample W r₀ (L + 1)} (h : clkGood ω) :
    clkGood (pgTrunc ω) :=
  ⟨h.1, fun i j => h.2 (Fin.castSucc i) j⟩

theorem clk_grownSchur_isHermitian {W r₀ L : ℕ} (E : ℝ) {ω : GrowthSample W r₀ L}
    (h : clkGood ω) : ∀ k, (grownSchur E ω k).IsHermitian
  | 0 => srec_pathSchur_isHermitian E ω.1 h.1
  | k + 1 => by
    have ih := clk_grownSchur_isHermitian E h k
    by_cases hk : k < L
    · simp only [grownSchur, hk, dite_true]
      exact srec_layerSchur_isHermitian E ih _ (h.2 _)
    · simp only [grownSchur, hk, dite_false]
      exact ih

/-!
## 6. The core injection as an absorbing resolvent block
-/

/-- `W⁻¹ Re Tr M* P M ≤ k ‖M‖²` for the projection `P` onto tagged blocks among `k`. -/
theorem clk_trace_proj_le {k W : ℕ} (τ : Fin k → Bool) (M : Matrix (Fin k × Fin W) (Fin 2 × Fin W) ℂ) :
    clkTrace (M.conjTranspose * clkProj (W := W) τ * M) ≤ k * ‖M‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [clkTrace]; positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨-, h1⟩ := wl_trace_weight_le (clkProj_posSemidef (W := W) τ) M
  have h2 := clkProj_trace_le (W := W) τ
  unfold clkTrace
  rw [inv_mul_le_iff₀ hW0]
  calc (M.conjTranspose * clkProj (W := W) τ * M).trace.re
      ≤ ‖M‖ ^ 2 * (clkProj (W := W) τ).trace.re := h1
    _ ≤ ‖M‖ ^ 2 * (k * W) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = W * (k * ‖M‖ ^ 2) := by ring

/-- Off-diagonal block of an inverse: `(N⁻¹)₁₂ = -A⁻¹ B (N⁻¹)₂₂` for `N = [[A, B], [C, D]]`
with `N` and `A` invertible. -/
theorem clk_toBlocks12_inv {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hN : IsUnit (fromBlocks A B C D).det) (hA : IsUnit A.det) :
    ((fromBlocks A B C D)⁻¹).toBlocks₁₂ = -(A⁻¹ * B * ((fromBlocks A B C D)⁻¹).toBlocks₂₂) := by
  set G := (fromBlocks A B C D)⁻¹ with hG
  have h := mul_nonsing_inv (fromBlocks A B C D) hN
  rw [← hG, ← fromBlocks_toBlocks G, fromBlocks_multiply] at h
  have h12 : A * G.toBlocks₁₂ + B * G.toBlocks₂₂ = 0 := by
    have := congrArg Matrix.toBlocks₁₂ h
    rw [toBlocks_fromBlocks₁₂] at this
    rw [this]
    ext i j
    simp [toBlocks₁₂, one_apply]
  have hA' := nonsing_inv_mul A hA
  calc G.toBlocks₁₂ = A⁻¹ * (A * G.toBlocks₁₂) := by rw [← Matrix.mul_assoc, hA', Matrix.one_mul]
    _ = A⁻¹ * (-(B * G.toBlocks₂₂)) := by rw [eq_neg_of_add_eq_zero_left h12]
    _ = -(A⁻¹ * B * G.toBlocks₂₂) := by rw [Matrix.mul_neg, Matrix.mul_assoc]

/-- The one-block core factor is `-𝒢₁₂` of the `.oneBlockTwoPorts` layer with `X = 0`. -/
theorem clk_coreFactor_one {W : ℕ} (b E : ℝ) (ℓ : LayerSample W .oneBlockTwoPorts)
    (hH : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - 0).det)
    (hN : IsUnit (layerMatrix .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ).det) :
    clkCoreFactor b E (coreOne ℓ) =
      -(layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ).toBlocks₁₂ := by
  have h12 := clk_toBlocks12_inv _ _ _ _ hN hH
  rw [layerResolvent, layerMatrix] at *
  rw [h12, neg_neg, clkCoreFactor, coreOne_portResolvent b E ℓ hH, coreOne_pathMatrix,
    coreOne_portCoupling, sub_zero, layerResolvent, layerMatrix]
  simp only [sub_zero]

/-- The two-block core factor is `-𝒢₁₂` of the `.separate` layer with `X = -coreOff β`. -/
theorem clk_coreFactor_two {W : ℕ} (b E : ℝ)
    (q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate)
    (hH : IsUnit (Internal.Contracts.Layers.blockDiag q.2.1 - (E : ℂ) • 1 - -coreOff q.1).det)
    (hN : IsUnit (layerMatrix .separate E (boundaryZ b E) (-coreOff q.1) q.2).det) :
    clkCoreFactor b E (coreTwo q) =
      -(layerResolvent .separate E (boundaryZ b E) (-coreOff q.1) q.2).toBlocks₁₂ := by
  have h12 := clk_toBlocks12_inv _ _ _ _ hN hH
  have hP : pathMatrix (coreTwo q) - (E : ℂ) • 1 =
      Internal.Contracts.Layers.blockDiag q.2.1 - (E : ℂ) • 1 - -coreOff q.1 := by
    rw [coreTwo_pathMatrix]; abel
  rw [layerResolvent, layerMatrix] at *
  rw [h12, neg_neg, clkCoreFactor, coreTwo_portResolvent b E q hH, hP, coreTwo_portCoupling,
    layerResolvent, layerMatrix]

/-- `‖f‖_q ≤ 2 C²` when `|f| ≤ 2 g²` a.e. and `‖g‖_{2q} ≤ C`. -/
theorem clk_eLpNorm_sq_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) {q C : ℝ} (hq : 0 < q)
    (hC : 0 ≤ C) (hfg : ∀ᵐ x ∂ν, ‖f x‖ ≤ 2 * g x ^ 2)
    (hgC : eLpNorm g (ENNReal.ofReal (2 * q)) ν ≤ ENNReal.ofReal C) :
    eLpNorm f (ENNReal.ofReal q) ν ≤ ENNReal.ofReal (2 * C ^ 2) := by
  refine (eLpNorm_mono_ae_real hf hfg).trans ?_
  have e : (fun x => 2 * g x ^ 2) = (2 : ℝ) • fun x => g x * g x := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e, eLpNorm_const_smul]
  have h2 := wl_eLpNorm_mul_le hg hg hq (μ := ν)
  calc ‖(2 : ℝ)‖ₑ * eLpNorm (fun x => g x * g x) (ENNReal.ofReal q) ν
      ≤ ‖(2 : ℝ)‖ₑ * (ENNReal.ofReal C * ENNReal.ofReal C) := by
        gcongr; exact h2.trans (mul_le_mul' hgC hgC)
    _ = ENNReal.ofReal (2 * C ^ 2) := by
        rw [Real.enorm_eq_ofReal (by norm_num), ← ENNReal.ofReal_mul hC,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

/-- **Moments of the core injection** (in the paper: "the finite core injection moments
follow from the Gaussian absorption lemma"): for each `q ≥ 1` there are `B, W₀` with
`‖W⁻¹ Tr Y_{r₀}‖_{L^q(pathLaw)} ≤ B` for `W ≥ W₀`, both cores, every core tag and `E ∈ I`. -/
theorem clk_core_moments (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
    ∃ (B : ℝ) (W₀ : ℕ), 0 ≤ B ∧ ∀ W : ℕ, 0 < W → W₀ ≤ W → ∀ r₀ : ℕ, (r₀ = 1 ∨ r₀ = 2) →
      ∀ E ∈ bulkInterval κ, ∀ τ₀ : Fin r₀ → Bool,
        eLpNorm (fun ω => clkTrace (clkCoreSource b E τ₀ ω)) (ENNReal.ofReal q) (pathLaw W r₀ b) ≤
          ENNReal.ofReal B := by
  intro b hb0 hb1 κ hκ q hq
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨2 * CA ^ 2, ⌈2 * q / ε₁⌉₊, by positivity, ?_⟩
  intro W hW hWW r₀ hr₀ E hE τ₀
  obtain ⟨hz, hzM, -⟩ := hbulk E hE
  have hq2 : 2 * q ≤ ε₁ * W := by
    have h1 : 2 * q / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
    rw [div_le_iff₀ hε₁] at h1; linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have := fun t => isProbabilityMeasure_gueMeasure W t
  have hsm : ∀ r (τ : Fin r → Bool), Measurable (fun ω : PathSample W r =>
      clkTrace (clkCoreSource b E τ ω)) := fun r τ =>
    clk_measurable_trace (clk_measurable_coreSource W r b E τ)
  rcases hr₀ with rfl | rfl
  · -- one block: `pathLaw W 1 = coreOne_* layerLaw .oneBlockTwoPorts`
    rw [← eLpNorm_comp_measurePreserving (hsm 1 τ₀).aestronglyMeasurable
      (coreOne_measurePreserving W b)]
    obtain ⟨hinv, hmom⟩ := habs W hW .oneBlockTwoPorts 0 isHermitian_zero E (boundaryZ b E) hz hzM
    have htop := srec_ae_isUnit_top (W := W) hb1 .oneBlockTwoPorts E 0
    have hmc : Measurable (coreOne (W := W)) := (coreOne_measurePreserving W b).measurable
    refine clk_eLpNorm_sq_le ((hsm 1 τ₀).comp hmc).aestronglyMeasurable
      (measurable_norm_layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0).aestronglyMeasurable
      hq0 hCA.le ?_ (hmom (2 * q) (by linarith) hq2)
    filter_upwards [hinv, htop] with ℓ hN hH
    simp only [Function.comp_apply]
    rw [clkCoreSource, clk_coreFactor_one b E ℓ hH hN, Real.norm_of_nonneg
      (clkTrace_nonneg ((clkProj_posSemidef τ₀).conjTranspose_mul_mul_same _))]
    refine (clk_trace_proj_le τ₀ _).trans ?_
    have h1 : ‖-(layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ).toBlocks₁₂‖ ≤
        ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ‖ := by
      rw [norm_neg]; exact wl_norm_toBlocks12_le _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    push_cast
    linarith [sq_nonneg ‖layerResolvent .oneBlockTwoPorts E (boundaryZ b E) 0 ℓ‖]
  · -- two blocks: `pathLaw W 2 = coreTwo_* (Gin ⊗ layerLaw .separate)`
    rw [← eLpNorm_comp_measurePreserving (hsm 2 τ₀).aestronglyMeasurable
      (coreTwo_measurePreserving W b)]
    have hinv : ∀ X : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ, X.IsHermitian →
        ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E (boundaryZ b E) X ω).det :=
      fun X hX => (habs W hW .separate X hX E (boundaryZ b E) hz hzM).1
    have hN2 := core_ae_unit2 (b := b) hinv
    have hmeasH : MeasurableSet {r : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
        IsUnit (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 - -coreOff r.1).det} := by
      have hm : Measurable (fun r : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
          (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 - -coreOff r.1).det) := by
        refine (continuous_id.matrix_det).measurable.comp ?_
        exact (((srec_continuous_blockDiag 2 W).measurable.comp
          (measurable_fst.comp measurable_snd)).sub measurable_const).sub
          ((measurable_coreOff W).comp measurable_fst).neg
      have : {r : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate |
          IsUnit (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 - -coreOff r.1).det} =
          (fun r => (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 -
            -coreOff r.1).det) ⁻¹' {0}ᶜ := by
        ext r; simp [isUnit_iff_ne_zero]
      rw [this]
      exact hm (measurableSet_singleton 0).compl
    have hH2 : ∀ᵐ r ∂coreLaw2 W b,
        IsUnit (Internal.Contracts.Layers.blockDiag r.2.1 - (E : ℂ) • 1 - -coreOff r.1).det := by
      rw [coreLaw2]
      exact core_ae_prod _ _ hmeasH fun β =>
        srec_ae_isUnit_top (W := W) hb1 .separate E (-coreOff β)
    have hmom : eLpNorm (fun r => ‖coreG2 E (boundaryZ b E) r‖) (ENNReal.ofReal (2 * q))
        (coreLaw2 W b) ≤ ENNReal.ofReal CA :=
      core_mom2 (by simp; linarith) ENNReal.ofReal_ne_top fun X hX =>
        (habs W hW .separate X hX E (boundaryZ b E) hz hzM).2 (2 * q) (by linarith) hq2
    have hmc : Measurable (coreTwo (W := W)) := (coreTwo_measurePreserving W b).measurable
    refine clk_eLpNorm_sq_le ((hsm 2 τ₀).comp hmc).aestronglyMeasurable
      (measurable_coreG2 E (boundaryZ b E)).norm.aestronglyMeasurable hq0 hCA.le ?_ hmom
    filter_upwards [hN2, hH2] with r hN hH
    simp only [Function.comp_apply]
    rw [clkCoreSource, clk_coreFactor_two b E r hH hN, Real.norm_of_nonneg
      (clkTrace_nonneg ((clkProj_posSemidef τ₀).conjTranspose_mul_mul_same _))]
    refine (clk_trace_proj_le τ₀ _).trans ?_
    have h1 : ‖-(layerResolvent .separate E (boundaryZ b E) (-coreOff r.1) r.2).toBlocks₁₂‖ ≤
        ‖coreG2 E (boundaryZ b E) r‖ := by
      rw [norm_neg]; exact wl_norm_toBlocks12_le _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    push_cast
    linarith

/-!
## 7. The full clock is the energy derivative of the grown Schur matrix
-/

theorem clkProj_true {k W : ℕ} : clkProj (W := W) (fun _ : Fin k => true) = 1 := by
  ext x y
  simp [clkProj, diagonal_apply, one_apply]

/-- `K = z - X` is invertible for Hermitian `X` and `Im z > 0`. -/
theorem clk_K_isUnit {n : Type*} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) : IsUnit (z • (1 : Matrix n n ℂ) - X).det := by
  have e : z • (1 : Matrix n n ℂ) - X =
      ((z.re : ℂ) • (1 : Matrix n n ℂ) - X) + Complex.I • diagonal (fun _ => ((z.im : ℝ) : ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.diagonal_apply, smul_eq_mul]
    split_ifs
    · conv_lhs => rw [← Complex.re_add_im z]
      ring
    · simp
  have hH : ((z.re : ℂ) • (1 : Matrix n n ℂ) - X).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq, Complex.star_def,
      Complex.conj_ofReal]
  refine (isUnit_det_and_norm_inv_le_of_lower hz fun ξ => ?_).1
  rw [e]
  exact tfl_lower_of_herm_add_diag hH (fun _ => z.im) (fun _ => le_rfl) ξ

/-- For Hermitian `H`, the full core injection is `R* X' R` with `X' = B_p*(H - E)⁻² B_p`, the
energy derivative of `X = B_p*(H - E)⁻¹ B_p` (`d/dE (H - E)⁻¹ = (H - E)⁻²`). -/
theorem clkCoreSource_eq_source {W r : ℕ} (b E : ℝ) (τ₀ : Fin r → Bool) (ω : PathSample W r)
    (hH : (pathMatrix ω).IsHermitian) :
    clkCoreSource b E τ₀ ω = (pathPortResolvent b E ω)ᴴ *
      ((pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1)⁻¹ * clkProj (W := W) τ₀ *
        (pathMatrix ω - (E : ℂ) • 1)⁻¹ * pathPortCoupling ω) * pathPortResolvent b E ω := by
  have hD : ((pathMatrix ω - (E : ℂ) • 1)⁻¹)ᴴ = (pathMatrix ω - (E : ℂ) • 1)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, hH.eq, conjTranspose_smul,
      conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  rw [clkCoreSource, clkCoreFactor, conjTranspose_mul, conjTranspose_mul, hD]
  simp only [Matrix.mul_assoc]

/-- `M* M` is invariant under reindexing the rows of `M`. -/
theorem clk_gram_reindex {m m' n : Type*} [Fintype m] [Fintype m'] (e : m' ≃ m)
    (M : Matrix m n ℂ) : Mᴴ * M = (M.submatrix e id)ᴴ * M.submatrix e id := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id]

/-- **Energy identity along one growth step**: for invertible `H - E`, `A - E - X_r`, `𝒢⁻¹`
and `K`, the full clock step (`P = I`) maps the energy source of the path to the energy
source of the grown path: `Y_{r+2} = R_{r+2}* X'_{r+2} R_{r+2}`. -/
theorem clkCoreSource_pgGrow {W r : ℕ} (hr : 1 ≤ r) (b E : ℝ) (ℓ : LayerSample W .separate)
    (ω : PathSample W r) (hH : IsUnit (pathMatrix ω - (E : ℂ) • 1).det)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - pathSchur E ω).det)
    (hN : IsUnit (layerMatrix .separate E (boundaryZ b E) (pathSchur E ω) ℓ).det)
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      pathSchur E ω).det) :
    clkCoreSource b E (fun _ => true) (pgGrow (ℓ, ω)) =
      clkStep b E (fun _ => true) (pathSchur E ω) (clkCoreSource b E (fun _ => true) ω) ℓ := by
  set D := pathMatrix ω - (E : ℂ) • 1 with hDdef
  set Bp := pathPortCoupling ω with hBp
  set A := Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 with hA
  set Bl := bondMatrix .separate ℓ.2 with hBl
  set G := layerResolvent .separate E (boundaryZ b E) (pathSchur E ω) ℓ with hG
  set T := A - pathSchur E ω with hT
  have hX : pathSchur E ω = Bpᴴ * D⁻¹ * Bp := rfl
  -- the layer blocks
  have h12 : G.toBlocks₁₂ = -(T⁻¹ * Bl * G.toBlocks₂₂) := by
    have := clk_toBlocks12_inv (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 -
      pathSchur E ω) Bl Blᴴ (boundaryZ b E • 1) hN hS
    exact this
  have hR' : pathPortResolvent b E (pgGrow (ℓ, ω)) = G.toBlocks₂₂ :=
    pathPortResolvent_pgGrow hr b E ℓ ω hH hS
  -- the grown factor in split coordinates
  let _ := invertibleOfIsUnitDet _ hH
  have hS' : IsUnit (A - Bpᴴ * ⅟D * Bp).det := by rw [invOf_eq_nonsing_inv]; exact hS
  let _ := invertibleOfIsUnitDet _ hS'
  let _ := fromBlocks₂₂Invertible A Bpᴴ Bp D
  have hF : (clkCoreFactor b E (pgGrow (ℓ, ω))).submatrix (pgSite W r) id =
      Matrix.fromRows (T⁻¹ * Bl) (-(D⁻¹ * Bp * T⁻¹ * Bl)) * G.toBlocks₂₂ := by
    unfold clkCoreFactor
    have hsub : ∀ {o : Type} [Fintype o] (M : Matrix (Fin (r + 2) × Fin W) o ℂ)
        (N : Matrix o (Fin 2 × Fin W) ℂ),
        (M * N).submatrix (pgSite W r) id = M.submatrix (pgSite W r) id * N := by
      intro o _ M N; ext i j; simp [Matrix.mul_apply]
    rw [hR', hsub, ← submatrix_mul_equiv _ _ (pgSite W r) (pgSite W r) id, ← inv_submatrix_equiv,
      pgGrow_pathMatrix_sub hr, pgGrow_portCoupling ℓ ω]
    congr 1
    change (fromBlocks A Bpᴴ Bp D)⁻¹ * fromRows Bl 0 = _
    rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, fromBlocks_mul_fromRows]
    simp only [Matrix.mul_zero, add_zero, invOf_eq_nonsing_inv]
    simp only [Matrix.neg_mul]; rfl
  -- the old factor
  have hRK : pathPortResolvent b E ω * (boundaryZ b E • 1 - pathSchur E ω) = 1 :=
    nonsing_inv_mul _ hK
  have hML : clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ = -(D⁻¹ * Bp * T⁻¹ * Bl * G.toBlocks₂₂) := by
    unfold clkCoreFactor clkL clkG12
    rw [show D⁻¹ * Bp * pathPortResolvent b E ω * ((boundaryZ b E • 1 - pathSchur E ω) * G.toBlocks₁₂)
      = D⁻¹ * Bp * (pathPortResolvent b E ω * (boundaryZ b E • 1 - pathSchur E ω)) * G.toBlocks₁₂ by
        simp only [Matrix.mul_assoc], hRK, Matrix.mul_one, h12]
    simp only [Matrix.mul_neg, Matrix.mul_assoc]
  -- assemble
  rw [clkCoreSource, clkProj_true, Matrix.mul_one, clk_gram_reindex (pgSite W r), hF, clkStep,
    clkProj_true, Matrix.mul_one, clkCoreSource, clkProj_true, Matrix.mul_one]
  rw [show (clkL b E (pathSchur E ω) ℓ)ᴴ * ((clkCoreFactor b E ω)ᴴ * clkCoreFactor b E ω) *
      clkL b E (pathSchur E ω) ℓ = (clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ)ᴴ *
        (clkCoreFactor b E ω * clkL b E (pathSchur E ω) ℓ) by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], hML]
  change _ = (G.toBlocks₁₂)ᴴ * G.toBlocks₁₂ + _
  rw [h12, conjTranspose_mul, conjTranspose_fromRows_eq_fromCols_conjTranspose]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fromCols _ _), fromCols_mul_fromRows]
  simp only [conjTranspose_neg, conjTranspose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- The layer matrix is invertible when its top block and `z - X₊` are. -/
theorem clk_layerMatrix_isUnit {W : ℕ} (E : ℝ) (z : ℂ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate)
    (hS : IsUnit (Internal.Contracts.Layers.blockDiag ℓ.1 - (E : ℂ) • 1 - X).det)
    (hP : IsUnit (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - layerSchur .separate E X ℓ).det) :
    IsUnit (layerMatrix .separate E z X ℓ).det := by
  let _ := invertibleOfIsUnitDet _ hS
  rw [layerMatrix, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  exact hS.mul hP

/-- **The full clock is the energy derivative** (in the paper: "for the full physical energy
derivative, `S = X' ⪰ 0` and `P = I` at every step"): almost surely under `growthLaw`, for
every `k ≤ L`, the full clock is the energy source `M* M = R* X' R` of the grown path
`pgPath ω k` (`X' = B_p*(H - E)⁻² B_p`, `clkCoreSource_eq_source`), whenever `Im z_∂ > 0`. -/
theorem clk_fullClock_eq_source {W r₀ L : ℕ} {b : ℝ} (hb1 : b < 1 / 2) (E : ℝ)
    (hz : 0 < (boundaryZ b E).im) (hr₀ : 1 ≤ r₀) :
    ∀ᵐ ω ∂growthLaw W r₀ L b, ∀ k, k ≤ L →
      clkClock b E (fun _ => true) (fun _ _ => true) ω k =
        clkCoreSource b E (fun _ => true) (pgPath ω k) := by
  have hinv : ∀ᵐ ω ∂growthLaw W r₀ L b,
      ∀ j : ℕ, j ≤ L → IsUnit (pathMatrix (pgPath ω j) - (E : ℂ) • 1).det := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j ≤ L
    · have hP := measurePreserving_pgPath (W := W) b hr₀ L j hj
      filter_upwards [hP.quasiMeasurePreserving.ae
        (ae_isUnit_det_pathMatrix W (r₀ + 2 * j) hb1 E)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [hinv, clk_ae_good W r₀ L b] with ω hω hg
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkL : k < L := by omega
    have ih' := ih (by omega)
    have hX := grownSchur_eq_pathSchur hr₀ E ω k (by omega) (fun j hj => hω j (by omega))
    have hH := hω k (by omega)
    have hG := hω (k + 1) hk
    rw [pgPath_succ ω hkL] at hG ⊢
    have hr : 1 ≤ r₀ + 2 * k := by omega
    have hS := (isUnit_det_pgGrow_iff hr E (ω.2 ⟨k, hkL⟩) (pgPath ω k) hH).mp hG
    have hXh : (pathSchur E (pgPath ω k)).IsHermitian := by
      rw [← hX]; exact clk_grownSchur_isHermitian E hg k
    have hK := clk_K_isUnit hXh hz
    have hN := clk_layerMatrix_isUnit E (boundaryZ b E) _ _ hS
      (clk_K_isUnit (srec_layerSchur_isHermitian E hXh _ (hg.2 _)) hz)
    simp only [clkClock, hkL, dite_true]
    rw [ih', hX]
    exact (clkCoreSource_pgGrow hr b E (ω.2 ⟨k, hkL⟩) (pgPath ω k) hH hS hN hK).symm

end BlockBand.Layers
