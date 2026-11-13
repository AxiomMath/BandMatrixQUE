module

public import BlockBand.Critical.Collar.Density.EnergyStability
public import Mathlib.Probability.Distributions.Cauchy

/-!
# From the regular density clause to a regular resolvent bound on an energy window

*Law.* `collarLaw W b`, `W ≥ 1`, `0 < b < 1/2`; deterministic Hermitian `X'`.

`lintegral_collarRow_le_of_regular` (**regular phase bound**): assume the regular density clause
`CollarDensityRegularClause b κ' d_* C_r W₀` (the open `PLAN.md` §2.3 statement; here a hypothesis of
this reduction lemma, not of any contract) and that, on the energy window `|x| ≤ δ`, the energies
`e + s + x` lie in `bulkInterval κ'` with `d_{e+s+x}(X') ≤ d_*`. Then for `0 < ε ≤ 1`,
`E_collar π⁻¹ Im⟨y, (ℋ^{(e+s)}_{X'} - iε)⁻¹ y⟩ ≤ 2C(1 + M²/η²)‖q‖² + ε(1+δ⁻²) π⁻¹ C_{b,w} √W ‖q‖²`,
`y = (z + e + s - A, -B)*q`, `C = max(C_r, 0)`, `M ≥ |z - x - z_b(e+s+x)|`, `η ≤ Im z_b(e+s+x)`.
The second term vanishes as `ε ↓ 0` (the `ν = 0` kernel clause).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Critical.WeightedDensity
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

variable {W : ℕ}

/-!
## The Cauchy kernel
-/

theorem cauchyKernel_zero_sub_eq {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    cauchyKernel ε (0 - x) = cauchyPDFReal 0 (Real.toNNReal ε) x := by
  have hc : ((Real.toNNReal ε : ℝ≥0) : ℝ) = ε := Real.coe_toNNReal _ hε.le
  simp only [cauchyKernel, cauchyPDFReal, sub_zero, zero_sub, neg_sq]
  rw [hc]
  field_simp

theorem lintegral_ofReal_cauchyKernel {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x, ENNReal.ofReal (cauchyKernel ε (0 - x)) = 1 := by
  have h := lintegral_cauchyPDF_eq_one 0 (γ := Real.toNNReal ε) (Real.toNNReal_pos.2 hε).ne'
  rw [← h]
  refine lintegral_congr fun x => ?_
  rw [cauchyKernel_zero_sub_eq hε]
  rfl

/-- Tail comparison: `P_ε(x) ≤ ε (1 + δ⁻²) P_1(x)` for `|x| ≥ δ > 0`, `0 < ε`. -/
theorem cauchyKernel_le_tail {ε δ x : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hx : δ ≤ |x|) :
    cauchyKernel ε x ≤ ε * (1 + δ⁻¹ ^ 2) * cauchyKernel 1 x := by
  unfold cauchyKernel
  have hx2 : δ ^ 2 ≤ x ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg x, neg_abs_le x]) hx
    simpa [sq_abs] using this
  have hxpos : 0 < x ^ 2 := lt_of_lt_of_le (by positivity) hx2
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have key : x ^ 2 + 1 ≤ (1 + δ⁻¹ ^ 2) * x ^ 2 := by
    have : 1 ≤ δ⁻¹ ^ 2 * x ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have h1 : ε * (1 + δ⁻¹ ^ 2) * (1 / (Real.pi * (x ^ 2 + 1 ^ 2))) * (Real.pi * (x ^ 2 + ε ^ 2)) =
      ε * ((1 + δ⁻¹ ^ 2) * (x ^ 2 + ε ^ 2) / (x ^ 2 + 1)) := by
    field_simp
  rw [h1]
  have h2 : (x ^ 2 + 1) ≤ (1 + δ⁻¹ ^ 2) * (x ^ 2 + ε ^ 2) := by nlinarith [sq_nonneg ε]
  have h3 : 1 ≤ (1 + δ⁻¹ ^ 2) * (x ^ 2 + ε ^ 2) / (x ^ 2 + 1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  nlinarith

/-!
## The regular phase bound
-/

theorem collarWeightedForm_nonneg (hW : 0 < W) (b e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (z : ℂ)
    (q : Fin 2 × Fin W → ℂ) (x : ℝ) : 0 ≤ collarWeightedForm W b e X z q x :=
  quadForm_nonneg_of_posSemidef (collarDensity_posSemidef hW b e hX x) _

/-- **Window bound** for the weighted form under the regular density clause. -/
theorem collarWeightedForm_le_of_regular (hW : 0 < W) {b κ' dstar Cr : ℝ} {W₀ : ℕ}
    (hreg : CollarDensityRegularClause b κ' dstar Cr W₀) (hW₀ : W₀ ≤ W) {e' x : ℝ}
    (he : e' + x ∈ bulkInterval κ') {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (hd : matchedDistance b (e' + x) X ≤ dstar) (z : ℂ) {M η : ℝ}
    (hη : 0 < η) (hηz : η ≤ (boundaryZ b (e' + x)).im)
    (hM : ‖z - x - boundaryZ b (e' + x)‖ ≤ M) (q : Fin 2 × Fin W → ℂ) :
    collarWeightedForm W b e' X z q x ≤ 2 * max Cr 0 * (1 + M ^ 2 / η ^ 2) * ∑ a, ‖q a‖ ^ 2 := by
  have hz'' : 0 < (boundaryZ b (e' + x)).im := hη.trans_le hηz
  have hR := posSemidef_smul_one_sub_mono' (hreg W hW hW₀ (e' + x) he X hX hd) (le_max_left Cr 0)
  have hS := collarDensity_posSemidef hW b (e' + x) hX 0
  have hw := quadForm_shifted_weight_le hX hz'' hS hR (z - x - boundaryZ b (e' + x)) q
  have hK : z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X - (x : ℂ) • 1 =
      boundaryZ b (e' + x) • 1 - X + (z - x - boundaryZ b (e' + x)) • 1 := by
    rw [sub_smul, sub_smul]; abel
  have hform : collarWeightedForm W b e' X z q x = quadForm (collarDensity W b (e' + x) X 0)
      ((boundaryZ b (e' + x) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X +
        (z - x - boundaryZ b (e' + x)) • 1)ᴴ *ᵥ q) := by
    rw [collarWeightedForm, collarWeightVec, collarDensity_energy_shift hW b e' hX x, hK]
    rfl
  rw [hform]
  refine hw.trans ?_
  have hq : 0 ≤ ∑ a, ‖q a‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hC : 0 ≤ max Cr 0 := le_max_right _ _
  have h1 : ‖z - x - boundaryZ b (e' + x)‖ ^ 2 / (boundaryZ b (e' + x)).im ^ 2 ≤ M ^ 2 / η ^ 2 := by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
    gcongr
  gcongr

/-- The fresh-row bound with the factor `π⁻¹` (`lintegral_im_resolvent_collarRow_le_sqrt`). -/
theorem lintegral_pi_inv_collarRowForm_le (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) (w : ℂ)
    (q : Fin 2 × Fin W → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec w q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (Real.pi⁻¹ * collarRowConst b w * Real.sqrt W * ∑ x, ‖q x‖ ^ 2) := by
  have hRB := lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e hX (z := (⟨0, ε⟩ : ℂ)) hε w q
  calc ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec w q ω) ⬝ᵥ
        ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im) ∂collarLaw W b
      = ENNReal.ofReal Real.pi⁻¹ * ∫⁻ ω, ENNReal.ofReal ((star (collarRowVec w q ω) ⬝ᵥ
          ((collarMatrix e X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
            (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec w q ω)).im) ∂collarLaw W b := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
    _ ≤ ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal (collarRowConst b w *
          Real.sqrt W * ∑ x, ‖q x‖ ^ 2) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 Real.pi_pos.le)]
        ring_nf

/-- **Regular phase bound** (`PLAN.md` §3.3): under `CollarDensityRegularClause` and on an energy
window `|x| ≤ δ` where `e' + x ∈ bulkInterval κ'`, `d_{e'+x}(X) ≤ d_*`, `η ≤ Im z_b(e'+x)` and
`|z - x - z_b(e'+x)| ≤ M`: for every `ε > 0`,
`E π⁻¹ Im⟨y,(ℋ^{(e')}_X - iε)⁻¹y⟩ ≤ 2 max(C_r,0)(1 + M²/η²)‖q‖² + ε(1+δ⁻²) π⁻¹C_{b,w}√W‖q‖²`,
`y = collarRowVec (z̄ + e') q`. -/
theorem lintegral_collarRow_le_of_regular (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {κ' dstar Cr : ℝ} {W₀ : ℕ} (hreg : CollarDensityRegularClause b κ' dstar Cr W₀)
    (hW₀ : W₀ ≤ W) {e' δ : ℝ} (hδ : 0 < δ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (z : ℂ) {M η : ℝ} (hη : 0 < η)
    (hwin : ∀ x : ℝ, |x| ≤ δ → e' + x ∈ bulkInterval κ' ∧ matchedDistance b (e' + x) X ≤ dstar ∧
      η ≤ (boundaryZ b (e' + x)).im ∧ ‖z - x - boundaryZ b (e' + x)‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (Real.pi⁻¹ * (star (collarRowVec (star z + e') q ω) ⬝ᵥ
        ((collarMatrix e' X ω - (⟨0, ε⟩ : ℂ) • (1 : Matrix (LayerSite W .common)
          (LayerSite W .common) ℂ))⁻¹ *ᵥ collarRowVec (star z + e') q ω)).im) ∂collarLaw W b ≤
      ENNReal.ofReal (2 * max Cr 0 * (1 + M ^ 2 / η ^ 2) * ∑ a, ‖q a‖ ^ 2) +
        ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (Real.pi⁻¹ *
          collarRowConst b (star z + e') * Real.sqrt W * ∑ a, ‖q a‖ ^ 2) := by
  rw [← lintegral_cauchyKernel_collarWeightedForm hW hb e' hX z q hε]
  set A := 2 * max Cr 0 * (1 + M ^ 2 / η ^ 2) * ∑ a, ‖q a‖ ^ 2
  set ρ := collarWeightedForm W b e' X z q
  have hρ0 : ∀ x, 0 ≤ ρ x := collarWeightedForm_nonneg hW b e' hX z q
  have hP0 : ∀ ε' x, 0 < ε' → 0 ≤ cauchyKernel ε' x := fun ε' x h => cauchyKernel_nonneg h.le x
  have hc0 : 0 ≤ ε * (1 + δ⁻¹ ^ 2) := by positivity
  have hpt : ∀ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * ρ x) ≤
      ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A +
        ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
    intro x
    by_cases hx : |x| ≤ δ
    · obtain ⟨h1, h2, h3, h4⟩ := hwin x hx
      have hw := collarWeightedForm_le_of_regular hW hreg hW₀ h1 hX h2 z hη h3 h4 q
      refine le_add_right ?_
      rw [← ENNReal.ofReal_mul (hP0 ε _ hε)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw (hP0 ε _ hε))
    · push Not at hx
      have ht := cauchyKernel_le_tail hε hδ (x := 0 - x) (by rw [zero_sub, abs_neg]; exact hx.le)
      refine le_add_left ?_
      rw [← ENNReal.ofReal_mul hc0]
      refine ENNReal.ofReal_le_ofReal ?_
      calc cauchyKernel ε (0 - x) * ρ x ≤ ε * (1 + δ⁻¹ ^ 2) * cauchyKernel 1 (0 - x) * ρ x :=
            mul_le_mul_of_nonneg_right ht (hρ0 x)
        _ = _ := by ring
  have hm1 : Measurable fun x : ℝ => ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A :=
    (((continuous_cauchyKernel hε).comp (continuous_const.sub continuous_id)).measurable
      ).ennreal_ofReal.mul_const _
  calc ∫⁻ x, ENNReal.ofReal (cauchyKernel ε (0 - x) * ρ x)
      ≤ ∫⁻ x, (ENNReal.ofReal (cauchyKernel ε (0 - x)) * ENNReal.ofReal A +
          ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) * ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal A + ENNReal.ofReal (ε * (1 + δ⁻¹ ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (cauchyKernel 1 (0 - x) * ρ x) := by
        rw [lintegral_add_left hm1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_ofReal_cauchyKernel hε, one_mul, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        gcongr
        rw [lintegral_cauchyKernel_collarWeightedForm hW hb e' hX z q one_pos]
        exact lintegral_pi_inv_collarRowForm_le hW hb0 hb e' hX _ q one_pos

end BlockBand.Critical.Collar.Density
