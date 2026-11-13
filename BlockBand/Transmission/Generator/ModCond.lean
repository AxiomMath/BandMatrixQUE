module

public import BlockBand.Transmission.Generator.BrCond

/-!
# The one-step fourth moment at path level: reduction to one fresh layer

Unabsorbed path at energy `E`, `X_r = pathX b E W r`, `r ≥ 1`, `k ≥ 1`.

* `freshD4`: the clamped `Ψ(x, y) = (cl Tr T(x₊)^k - cl Tr T(x)^k)⁴` (bounded by `W⁴`);
* **`integral_powerIncrement_pow_four`**: `E(Δ^k_r)⁴ = E ∫(Tr T(X_r₊)^k - Tr T(X_r)^k)⁴dfresh`
  (as `condExp_powerIncrement_mul`, then `integral_condExp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- The clamped one-step fourth power. -/
def freshD4 (b E : ℝ) (k : ℕ)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) : ℝ :=
  (freshPow b E k x - clampW W ((passiveTransmission b E x.1) ^ k).trace.re) ^ 4

theorem measurable_freshD4 (b E : ℝ) (k : ℕ) : Measurable (freshD4 (W := W) b E k) :=
  ((measurable_freshPow b E k).sub (continuous_clampW.measurable.comp
    ((measurable_trace_pow_transmission b E k).comp measurable_fst))).pow_const 4

theorem abs_freshD4_le (b E : ℝ) (k : ℕ)
    (x : Matrix (Fin W) (Fin W) ℂ × LayerSample W .oneBlockOnePort) :
    |freshD4 b E k x| ≤ (W : ℝ) ^ 4 := by
  rw [freshD4, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_clampW_sub_le _ _) 4

theorem integral_freshD4 {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    {k : ℕ} (hk : 1 ≤ k) :
    ∫ y, freshD4 b E k (X, y) ∂freshLaw W b =
      ∫ y, (((passiveTransmission b E (freshSchur E X y)) ^ k).trace.re -
          ((passiveTransmission b E X) ^ k).trace.re) ^ 4 ∂freshLaw W b := by
  refine integral_congr_ae ?_
  filter_upwards [PassiveLayer.ae_good W hb0 hW] with y hy
  have hY := PathScalar.passiveY_freshSchur E hX y hy.1
  obtain ⟨a0, a1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hY hk
  obtain ⟨c0, c1⟩ := trace_pow_le_card (b := b) (by linarith) h1 h2 hX hk
  simp only [freshD4, freshPow]
  rw [clampW_of_mem a0 a1, clampW_of_mem c0 c1]

/-- **`E(Δ^k_r)⁴` through one fresh layer**, `r, k ≥ 1`. -/
theorem integral_powerIncrement_pow_four {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) (hW : 1 ≤ W) {k : ℕ} (hk : 1 ≤ k) {r : ℕ} (hr : 1 ≤ r) :
    ∫ ω, powerIncrement b E W k r ω ^ 4 ∂growthPathLaw W b =
      ∫ ω, ∫ y, (((passiveTransmission b E (freshSchur E (pathX b E W r ω) y)) ^ k).trace.re -
          ((passiveTransmission b E (pathX b E W r ω)) ^ k).trace.re) ^ 4 ∂freshLaw W b
        ∂growthPathLaw W b := by
  set μ := growthPathLaw W b
  have hae : (fun ω => powerIncrement b E W k r ω ^ 4)
      =ᵐ[μ] fun ω => freshD4 b E k (pathX b E W r ω, freshSample W r ω) := by
    filter_upwards [ae_pathX_succ hb h1 h2 hW, pathPower_mem (W := W) (by linarith) h1 h2]
      with ω hω hm
    obtain ⟨a0, a1, a3⟩ := hm k (r + 1) hk
    obtain ⟨b0, b1, b3⟩ := hm k r hk
    have e1 : pathPower b E W k (r + 1) ω =
        ((passiveTransmission b E (freshSchur E (pathX b E W r ω) (freshSample W r ω))) ^
          k).trace.re := by
      show ((passiveTransmission b E (pathX b E W (r + 1) ω)) ^ k).trace.re = _
      rw [hω r hr]
    have e0 : pathPower b E W k r ω =
        ((passiveTransmission b E (pathX b E W r ω)) ^ k).trace.re := rfl
    rw [powerIncrement, freshD4, freshPow, ← e1, ← e0, clampW_of_mem a0 (a1.trans a3),
      clampW_of_mem b0 (b1.trans b3)]
  rw [integral_congr_ae hae, ← integral_condExp (growthSigma_le W r)]
  refine integral_congr_ae ((condExp_fresh b E (measurable_freshD4 b E k) (M := (W : ℝ) ^ 4)
    (fun x => abs_freshD4_le b E k x) r).trans ?_)
  filter_upwards [mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω
  exact integral_freshD4 hb0 hb hW h1 h2 hω hk

end BlockBand.Transmission.Generator
