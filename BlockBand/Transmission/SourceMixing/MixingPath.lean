module

public import BlockBand.Transmission.SourceMixing.MixingLayer
public import BlockBand.Transmission.Bridge.TransportFull

/-!
# Path tools for the source-mixing recursions

Fubini, Hölder and geometric-recursion tools for the source-mixing quantities along the growth
path.

* `mx_eLpNorm_path_le`: Fubini over `pastLaw ⊗ freshLaw` with an `X`-dependent fresh bound:
  if `‖Ψ(X,·)‖_{L^p(fresh)} ≤ B g(X)` for every passive `X`, then
  `‖Ψ(X_j, fresh_j)‖_{L^p} ≤ B ‖g(X_j)‖_{L^p}`.
* `mx_eLpNorm_mul_le`: Hölder `‖fg‖_p ≤ ‖f‖_{2p}‖g‖_{2p}`.
* `mx_rec`: the geometric recursion `G(X_{j+1}) ≤ ρG(X_j) + C e(X_j)q_j + excess_j` (a.s., the
  excess of `MixingLayer`) started at `r₀ ≥ 1` gives
  `‖G(X_r)‖_p ≤ ρ^{r-r₀}‖G(X_{r₀})‖_p + B/(1-ρ)` (`eLpNorm_linrec`, index shifted).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder

variable {W : ℕ}

/-- Fubini with an `X`-dependent fresh bound. -/
theorem mx_eLpNorm_path_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {Ψ : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort → ℝ} (hΨ : Measurable Ψ)
    {g : Matrix (Fin W) (Fin W) ℂ → ℝ} (hg : Measurable g) {p B : ℝ} (hp : 0 < p) (hB : 0 ≤ B)
    (j : ℕ)
    (hbd : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => Ψ (X, ω)) (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (B * g X)) :
    eLpNorm (fun ω => Ψ (pathX b E W j ω, freshSample W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤
      ENNReal.ofReal B * eLpNorm (fun ω => g (pathX b E W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) := by
  set S := stepInput b E (fun _ => 0) W j
  have hS : Measurable S := measurable_stepInput b E _ j
  set Φ : PastSample W j × LayerSample W .oneBlockOnePort → ℝ := fun x => Ψ (S x.1, x.2)
  have hΦ : Measurable Φ := hΨ.comp ((hS.comp measurable_fst).prodMk measurable_snd)
  have hT := (measurable_pastCoords W j).prodMk (measurable_freshSample W j)
  have e1 : (fun ω => Ψ (pathX b E W j ω, freshSample W j ω)) =
      Φ ∘ fun ω => (pastCoords W j ω, freshSample W j ω) := by
    funext ω; simp only [Function.comp, Φ, S, PathJet.stepInput_zero]
  have e2 : (fun ω => g (pathX b E W j ω)) = (g ∘ S) ∘ pastCoords W j := by
    funext ω; simp only [Function.comp, S, PathJet.stepInput_zero]
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
    have h := hbd (S x) (passiveY_stepInput hb h1 h2 (fun _ => le_rfl) hx)
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

/-- Hölder: `‖fg‖_p ≤ ‖f‖_{2p}‖g‖_{2p}`. -/
theorem mx_eLpNorm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ} {p : ℝ}
    (hp : 0 < p) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * eLpNorm g (ENNReal.ofReal (2 * p)) μ := by
  have : ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; field_simp; ring⟩
  have h := eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := μ) (φ := f) (f := g)
    (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p)
    (by simpa using hp)
  exact h

/-- The geometric recursion started at `r₀ ≥ 1`. -/
theorem mx_rec {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W)
    {G : Matrix (Fin W) (Fin W) ℂ → ℝ} (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X) {ρ C : ℝ}
    {s : ℂ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {p A B : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {r₀ r : ℕ} (hr₀ : 1 ≤ r₀) (hr : r₀ ≤ r)
    (h0 : eLpNorm (fun ω => G (pathX b E W r₀ ω)) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal A)
    (he : ∀ j, r₀ ≤ j → j < r → eLpNorm (fun ω => C * mx_err b E s (pathX b E W j ω) +
        mx_excess G ρ C b E s (pathX b E W j ω, freshSample W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => G (pathX b E W r ω)) (ENNReal.ofReal p) (growthPathLaw W b) ≤
      ENNReal.ofReal (ρ ^ (r - r₀) * A + B / (1 - ρ)) := by
  set P := growthPathLaw W b
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set y : ℕ → GrowthPath W → ℝ := fun k ω => G (pathX b E W (r₀ - 1 + k) ω)
  set e : ℕ → GrowthPath W → ℝ := fun k ω => C * mx_err b E s (pathX b E W (r₀ - 1 + k) ω) +
    mx_excess G ρ C b E s (pathX b E W (r₀ - 1 + k) ω, freshSample W (r₀ - 1 + k) ω)
  have hrec := ae_pathX_succ (b := b) hb h1 h2 hW
  have key := PathJet.eLpNorm_linrec P (y := y) (e := e) (n := r - r₀ + 1) hp1 hρ0 hρ1 hA hB
    (fun k ω => hG0 _) (fun k => (hG.comp (PathJet.measurable_pathX b E _)).aestronglyMeasurable)
    (fun k hk _ => by
      filter_upwards [hrec] with ω hω
      have hj : 1 ≤ r₀ - 1 + k := by omega
      have hidx : r₀ - 1 + (k + 1) = (r₀ - 1 + k) + 1 := by omega
      simp only [y, e, hidx, hω _ hj]
      have := le_max_right 0 (G (freshSchur E (pathX b E W (r₀ - 1 + k) ω)
        (freshSample W (r₀ - 1 + k) ω)) - ρ * G (pathX b E W (r₀ - 1 + k) ω) -
        C * mx_err b E s (pathX b E W (r₀ - 1 + k) ω))
      unfold mx_excess
      linarith)
    (by simp only [y, show r₀ - 1 + 1 = r₀ by omega]; exact h0)
    (fun k hk hkn => he (r₀ - 1 + k) (by omega) (by omega))
    (r - r₀ + 1) (by omega) le_rfl
  simp only [y, show r₀ - 1 + (r - r₀ + 1) = r by omega, show r - r₀ + 1 - 1 = r - r₀ by omega]
    at key
  exact key

end BlockBand.Transmission.SourceMixing
