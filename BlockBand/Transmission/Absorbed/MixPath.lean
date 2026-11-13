module

public import BlockBand.Transmission.Absorbed.JetUniform
public import BlockBand.Transmission.Absorbed.ShiftMixW
public import BlockBand.Transmission.SourceMixing.MixingErr

/-!
# Path tools for the absorbed source-mixing recursion

* `abs_eLpNorm_path_le`: Fubini over `pastLaw ⊗ freshLaw` at the absorbed input:
  `‖Ψ(X'_j, fresh_j)‖_p ≤ B‖g(X'_j)‖_p` if `‖Ψ(X,·)‖_{L^p(fresh)} ≤ B g(X)` for passive `X`;
* `mx_err_moment`: `‖C·mx_err(Y)‖_p ≤ C(2DK + K² + K)/√W` from `‖q(Y)‖_{2p} ≤ K`,
  `‖δ₀(Y)‖_{2p}, ‖δ₁(Y)‖_{2p} ≤ D/W`, for any random input `Y`;
* `linrec_from`: `eLpNorm_linrec` started at `r₀ ≥ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- The input `X_j − iε_j` of the fresh layer of step `j → j+1` along the absorbed path. -/
def absIn (b E : ℝ) (κ : ℝ → ℝ) (W j : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  stepInput b E κ W j (pastCoords W j ω)

theorem measurable_absIn (b E : ℝ) (κ : ℝ → ℝ) (j : ℕ) : Measurable (absIn b E κ W j) :=
  (measurable_stepInput b E κ j).comp (measurable_pastCoords W j)

/-- **Fubini at the absorbed input with an `X`-dependent fresh bound.** -/
theorem abs_eLpNorm_path_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ t, 0 ≤ κ t)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {g : Matrix (Fin W) (Fin W) ℂ → ℝ} (hg : Measurable g) {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (j : ℕ)
    (hbd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => Ψ (X, ω)) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (B * g X)) :
    eLpNorm (fun ω => Ψ (absIn b E κ W j ω, freshSample W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤
      ENNReal.ofReal B * eLpNorm (fun ω => g (absIn b E κ W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) := by
  set S := stepInput b E κ W j
  have hS : Measurable S := measurable_stepInput b E _ j
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ := fun x => Ψ (S x.1, x.2)
  have hΦ : Measurable Φ := hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have e1 : (fun ω => Ψ (absIn b E κ W j ω, freshSample W j ω)) =
      Φ ∘ fun ω => (pastCoords W j ω, freshSample W j ω) := rfl
  have e2 : (fun ω => g (absIn b E κ W j ω)) = (g ∘ S) ∘ pastCoords W j := rfl
  rw [e1, e2, ← eLpNorm_map_measure hΦ.aestronglyMeasurable hT.aemeasurable,
    growthPathLaw_map_past_fresh,
    ← eLpNorm_map_measure (hg.comp hS).aestronglyMeasurable
      (measurable_pastCoords W j).aemeasurable, growthPathLaw_map_pastCoords]
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hΦ.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hg.comp hS).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, lintegral_prod _ (hΦ.enorm.pow_const _).aemeasurable]
  have hsec : ∀ᵐ x ∂pastLaw W j b, ∫⁻ y, ‖Φ (x, y)‖ₑ ^ p ∂freshLaw W b ≤
      ENNReal.ofReal B ^ p * ‖(g ∘ S) x‖ₑ ^ p := by
    filter_upwards [ae_pastLaw_hermitian W j b] with x hx
    have h := hbd (S x) (passiveY_stepInput hb h1 h2 hκ hx)
    have hm : Measurable fun y => Φ (x, y) := hΦ.comp measurable_prodMk_left
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp.le, one_div, ENNReal.rpow_inv_le_iff hp] at h
    refine h.trans ?_
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
    refine ENNReal.rpow_le_rpow ?_ hp.le
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hB]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_abs_self _) hB)
  calc (∫⁻ x, ∫⁻ y, ‖Φ (x, y)‖ₑ ^ p ∂freshLaw W b ∂pastLaw W j b) ^ (1 / p)
      ≤ (∫⁻ x, ENNReal.ofReal B ^ p * ‖(g ∘ S) x‖ₑ ^ p ∂pastLaw W j b) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae hsec) (by positivity)
    _ = ENNReal.ofReal B * (∫⁻ x, ‖(g ∘ S) x‖ₑ ^ p ∂pastLaw W j b) ^ (1 / p) := by
        rw [lintegral_const_mul _ ((hg.comp hS).enorm.pow_const _),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The scalar step of `mx_err_moment`. -/
theorem mx_err_arith {C D K x : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K) (hx : 1 ≤ x) :
    C * (D / x * K + D / x * K + x⁻¹ * (K * K) + x⁻¹ ^ 2 * K) ≤
      C * (2 * D * K + K ^ 2 + K) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hWi : 0 ≤ x⁻¹ := by positivity
  have hs1 : Real.sqrt x ≤ x := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hinv : x⁻¹ ≤ (Real.sqrt x)⁻¹ := inv_anti₀ hs0 hs1
  have hinv2 : x⁻¹ ^ 2 ≤ x⁻¹ := by
    rw [sq]; exact mul_le_of_le_one_left hWi (inv_le_one_of_one_le₀ hx)
  have hK2 : 0 ≤ K * K := mul_nonneg hK hK
  have hDK : 0 ≤ D * K := mul_nonneg hD hK
  have e1 : D / x * K = D * K * x⁻¹ := by rw [div_eq_mul_inv]; ring
  have a1 : D * K * x⁻¹ ≤ D * K * (Real.sqrt x)⁻¹ := mul_le_mul_of_nonneg_left hinv hDK
  have a2 : x⁻¹ * (K * K) ≤ (Real.sqrt x)⁻¹ * (K * K) := mul_le_mul_of_nonneg_right hinv hK2
  have a3 : x⁻¹ ^ 2 * K ≤ (Real.sqrt x)⁻¹ * K :=
    mul_le_mul_of_nonneg_right (hinv2.trans hinv) hK
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add a1 a1) a2) a3) hC
  have e : C * (2 * D * K + K ^ 2 + K) / Real.sqrt x =
      C * (D * K * (Real.sqrt x)⁻¹ + D * K * (Real.sqrt x)⁻¹ + (Real.sqrt x)⁻¹ * (K * K) +
        (Real.sqrt x)⁻¹ * K) := by rw [div_eq_mul_inv]; ring
  rw [e1, e]; linarith

/-- **The mean forcing `C·mx_err(Y)` at any random input `Y`** (the first half of
`mx_step_err`). -/
theorem mx_err_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b E : ℝ} (hW : 1 ≤ W) {Y : Ω → Matrix (Fin W) (Fin W) ℂ} {C : ℝ} (hC : 0 ≤ C) {s : ℂ}
    {p : ℝ} (hp : 1 ≤ p) {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hq : eLpNorm (fun ω => passiveMass b E (Y ω)) (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal K)
    (hδ0 : eLpNorm (fun ω => jetDistance0 b E (Y ω)) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (D / W))
    (hδ1 : eLpNorm (fun ω => mx_jet1 b E s (Y ω)) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal (D / W)) :
    eLpNorm (fun ω => C * mx_err b E s (Y ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (C * (2 * D * K + K ^ 2 + K) / Real.sqrt W) := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hDW : 0 ≤ D / W := by positivity
  have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
  have hqp : eLpNorm (fun ω => passiveMass b E (Y ω)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans hq
  have t1 := mx_mul_le hp0 hDW hδ0 hq
  have t2 := mx_mul_le hp0 hDW hδ1 hq
  have t3 := mx_const_mul_le hWi (mx_mul_le hp0 hK hq hq)
  have t4 := mx_const_mul_le (sq_nonneg (W : ℝ)⁻¹) hqp
  have s12 := mx_add_le hp1 (by positivity) (by positivity) t1 t2
  have s123 := mx_add_le hp1 (by positivity) (by positivity) s12 t3
  have s1234 := mx_add_le hp1 (by positivity) (by positivity) s123 t4
  have hm := mx_const_mul_le hC s1234
  simp only [← mx_err_eq] at hm
  exact hm.trans (ENNReal.ofReal_le_ofReal (mx_err_arith hC hD hK hWr))

/-- **`eLpNorm_linrec` started at `r₀ ≥ 1`.** -/
theorem linrec_from {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {y e : ℕ → Ω → ℝ}
    {ρ A B : ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {r₀ r : ℕ} (hr₀ : 1 ≤ r₀) (hr : r₀ ≤ r) (hy0 : ∀ j ω, 0 ≤ y j ω)
    (hym : ∀ j, AEStronglyMeasurable (y j) μ)
    (hstep : ∀ j, r₀ ≤ j → j < r → ∀ᵐ ω ∂μ, y (j + 1) ω ≤ ρ * y j ω + e j ω)
    (h0 : eLpNorm (y r₀) p μ ≤ ENNReal.ofReal A)
    (he : ∀ j, r₀ ≤ j → j < r → eLpNorm (e j) p μ ≤ ENNReal.ofReal B) :
    eLpNorm (y r) p μ ≤ ENNReal.ofReal (ρ ^ (r - r₀) * A + B / (1 - ρ)) := by
  have key := PathJet.eLpNorm_linrec μ (y := fun k => y (r₀ - 1 + k))
    (e := fun k => e (r₀ - 1 + k)) (n := r - r₀ + 1) hp hρ0 hρ1 hA hB
    (fun k ω => hy0 _ _) (fun k => hym _)
    (fun k hk hkn => by
      have hidx : r₀ - 1 + (k + 1) = (r₀ - 1 + k) + 1 := by omega
      simp only [hidx]
      exact hstep _ (by omega) (by omega))
    (by simp only [show r₀ - 1 + 1 = r₀ by omega]; exact h0)
    (fun k hk hkn => he (r₀ - 1 + k) (by omega) (by omega))
    (r - r₀ + 1) (by omega) le_rfl
  simp only [show r₀ - 1 + (r - r₀ + 1) = r by omega, show r - r₀ + 1 - 1 = r - r₀ by omega]
    at key
  exact key

end BlockBand.Transmission.Absorbed
