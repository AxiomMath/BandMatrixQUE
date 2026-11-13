module

public import BlockBand.Transmission.PassiveLayer.TMTransfer

/-!
# The limit `ε ↓ 0`: the trace–matrix covariance bound at a passive input

`tm_core`: for passive `X`, given (i) a.s. invertibility of the layer matrix at `X` and (ii) a
moment bound `‖lbar(X')‖_{L^{4N}} ≤ C_m` **uniform over passive inputs `X'`** (`moments`),
the words of the `traceMatrix` clause satisfy the four conclusions of the clause with
`‖E(fU) - E f E U‖ ≤ (3 ℓ_f ℓ_U K_d^n / W²) · 2 C_m^N` (`n = ℓ_f + ℓ_U + 2 ≤ N`).

Route: `X_k = X - iε_k`, `ε_k = 1/(k+1)` (`regX`, `epsN`; passive). For each `k`,
`tm_cov_reg_fresh` and `E lbar(X_k)^n ≤ C_m^N`. The words at `X_k` converge to those at `X`
wherever the layer matrix at `X` is invertible (`tendsto_layerAt_reg`, joint continuity of
`tmWord`). The three expectations `E f_k U_k`, `E f_k`, `E U_k` (entrywise) converge by
**Vitali** (`PassiveCovariance.tendsto_integral_of_ae_of_eLpNorm_two`) from the uniform `L²`
bounds `|f_k|, |U_k| ≤ K_d^{ℓ+1} lbar(X_k)^N`, `|f_kU_k| ≤ K_d^{ℓ_f+ℓ_U+2} lbar(X_k)^{2N}`
(`eLpNorm_two_le_of_pow_bound`). The signed covariance is a continuous function of the three
means, so the bound passes to the limit. No Fatou argument is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

/-- `‖w‖ ≤ K_d^{ℓ+1} lbar^N` for `ℓ ≤ N`. -/
theorem norm_passiveWord_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ) {Kd : ℝ}
    (hKd : 0 ≤ Kd) (hD : ∀ j, ‖D j‖ ≤ Kd) {N : ℕ} (hN : ℓ ≤ N)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖passiveWord E w X wd D ω‖ ≤ Kd ^ (ℓ + 1) * lbar E w X ω ^ N := by
  rw [passiveWord_eq]
  refine (norm_tmWord_le _ hKd wd D _ hD).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h0 := zero_le_one.trans (one_le_lam (w • 1 - X) (layerAt E w X ω))
  exact (pow_le_pow_left₀ h0 (lam_le_lbar E w X ω) ℓ).trans
    (pow_le_pow_right₀ (one_le_lbar E w X ω) hN)

theorem norm_trW_le (M : Matrix (Fin W) (Fin W) ℂ) : ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ :=
  norm_tmTr_le M

theorem tendsto_K_reg (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Tendsto (fun k : ℕ => w • (1 : Matrix (Fin W) (Fin W) ℂ) - regX X (epsN k)) atTop
      (𝓝 (w • 1 - X)) := by
  have h := (tendsto_const_nhds (x := w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)).add
    (tendsto_epsN_I.smul_const (1 : Matrix (Fin W) (Fin W) ℂ))
  simp only [zero_smul, add_zero] at h
  refine h.congr fun k => ?_
  simp only [regX]; abel

theorem tendsto_passiveWord_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) {ℓ : ℕ}
    (wd : Fin ℓ → Fin 6 × Bool) (D : Fin (ℓ + 1) → Matrix (Fin W) (Fin W) ℂ) :
    Tendsto (fun k : ℕ => passiveWord E w (regX X (epsN k)) wd D ω) atTop
      (𝓝 (passiveWord E w X wd D ω)) := by
  have h := ((continuous_tmWord wd D).tendsto (w • 1 - X, layerAt E w X ω)).comp
    ((tendsto_K_reg w X).prodMk_nhds (tendsto_layerAt_reg E w X ω hu))
  have e : ∀ X' : Matrix (Fin W) (Fin W) ℂ,
      passiveWord E w X' wd D ω = tmWord (w • 1 - X') wd D (layerAt E w X' ω) :=
    fun X' => passiveWord_eq E w X' wd D ω
  simp only [e]
  exact h

/-- The `L²` bound from a moment bound of `lbar`, for `‖F‖ ≤ c lbar^k`. -/
theorem eLpNorm_two_le_lbar {b : ℝ} (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    {F : LayerSample W .oneBlockOnePort → ℂ} (hF : Measurable F) {c : ℝ} (hc : 0 ≤ c) {k : ℕ}
    (hk : 1 ≤ k) (hb : ∀ ω, ‖F ω‖ ≤ c * lbar E w X ω ^ k) {M : ℕ} (hkM : 2 * k ≤ M) {Cm : ℝ}
    (hm : eLpNorm (lbar E w X) (ENNReal.ofReal M) (freshLaw W b) ≤ ENNReal.ofReal Cm) :
    eLpNorm F 2 (freshLaw W b) ≤ ENNReal.ofReal c * ENNReal.ofReal Cm ^ k := by
  have hm' : eLpNorm (lbar E w X) (ENNReal.ofReal (2 * k)) (freshLaw W b) ≤ ENNReal.ofReal Cm :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by exact_mod_cast hkM))).trans hm
  exact eLpNorm_two_le_of_pow_bound hF.aestronglyMeasurable (lbar_nonneg E w X)
    (measurable_lbar E w X).aestronglyMeasurable hc k hk hb hm'

end BlockBand.Transmission.PassiveLayer
