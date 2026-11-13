module

public import BlockBand.Transmission.Generator.BrInputs
public import BlockBand.Transmission.Generator.BrShape
public import BlockBand.Transmission.Generator.PowBound

/-!
# The one-layer bracket, bulk-uniform

`brY b E s X = (g+1)(Wδ₀+1)(√W(|Tr Qf| + hs(Q,f))+1)(Wδ₁+1)` (`δ₁` at the jet `s`).

**`bracket_layer_bulk hGA hLp hP`**: `b ∈ (0,1/2)`, `κ > 0`, `k, l` first; then `K ≥ 0, W₀`; for
`W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s` at `E` and every passive `X`:
`|E[(Re Tr T(X₊)^{k+1} - Re Tr T^{k+1})(Re Tr T(X₊)^{l+1} - Re Tr T^{l+1})] -
B_{k+1,l+1}(P)/W| ≤ K·brY⁶/√W³`, `B` at `D₀(E)`, `P_m = Re Tr T^m`.

Inputs: `hs_moment4_bulk`, `ubarMean_bulk` (a), PCB's `passiveCovarianceBulk_holds hGA hLp hP`,
`ml_integrable_U_bulk`, `freshU_sq_integrable_bulk`; then `br_law` and `br_rhs_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.SourceMixing
open BlockBand.Transmission.LengthUniform BlockBand.Transmission.PathScalar
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- The normalised product `Y = (g+1)(Wδ₀+1)(t+1)(Wδ₁+1)`. -/
def brY (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((passiveTransmission b E X).trace.re + 1) * (W * jetDistance0 b E X + 1) *
    (Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X)) + 1) * (W * jetDistance1 b E s X + 1)

theorem brY_ge {g a t d : ℝ} (hg : 0 ≤ g) (ha : 0 ≤ a) (ht : 0 ≤ t) (hd : 0 ≤ d) :
    1 ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) ∧ g ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) ∧
      a ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) ∧ t ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) ∧
      d ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) ∧
      (a + 1) * (g + 1) ≤ (g + 1) * (a + 1) * (t + 1) * (d + 1) := by
  have h1 : 1 ≤ (g + 1) * (a + 1) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have h2 : 1 ≤ (t + 1) * (d + 1) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have e : (g + 1) * (a + 1) * (t + 1) * (d + 1) = ((g + 1) * (a + 1)) * ((t + 1) * (d + 1)) := by
    ring
  rw [e]
  have hP : (g + 1) * (a + 1) ≤ (g + 1) * (a + 1) * ((t + 1) * (d + 1)) := le_mul_of_one_le_right
    (by positivity) h2
  have hQ : (t + 1) * (d + 1) ≤ (g + 1) * (a + 1) * ((t + 1) * (d + 1)) := le_mul_of_one_le_left
    (by positivity) h1
  refine ⟨one_le_mul_of_one_le_of_one_le h1 h2, ?_, ?_, ?_, ?_, by nlinarith⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem hsSandwich_transmission_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (hη : 0 ≤ etaZ b E) :
    hsSandwich (passiveTransmission b E X) (passiveF b E X) =
      4 * etaZ b E * hsSandwich (passiveQ b E X) (passiveF b E X) := by
  set c : ℝ := 4 * etaZ b E
  have hc : 0 ≤ c := by positivity
  unfold hsSandwich
  have e : passiveTransmission b E X * passiveF b E X * passiveTransmission b E X *
      (passiveF b E X)ᴴ = ((c * c : ℝ) : ℂ) • (passiveQ b E X * passiveF b E X *
        passiveQ b E X * (passiveF b E X)ᴴ) := by
    simp only [passiveTransmission, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1; simp only [c]; push_cast; ring
  rw [e, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, Real.sqrt_mul (by positivity),
    Real.sqrt_mul_self hc]

/-- The fresh increments as `brInc`, and the bracket as the eigenvalue sum. -/
theorem br_fresh_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) (k l : ℕ) :
    (∫ ω, (((passiveTransmission b E (freshSchur E X ω)) ^ (k + 1)).trace.re -
          ((passiveTransmission b E X) ^ (k + 1)).trace.re) *
        (((passiveTransmission b E (freshSchur E X ω)) ^ (l + 1)).trace.re -
          ((passiveTransmission b E X) ^ (l + 1)).trace.re) ∂freshLaw W b) =
      ∫ ω, brInc hT (k + 1) (freshU b E X ω) * brInc hT (l + 1) (freshU b E X ω)
        ∂freshLaw W b ∧
    transmissionBracket (transportD0 b E) (k + 1) (l + 1)
        (fun m => ((passiveTransmission b E X) ^ m).trace.re) / W =
      ((k + 1 : ℕ) : ℝ) * ((l + 1 : ℕ) : ℝ) * (2 * (transportD0 b E / (2 * W)) *
        ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i)) := by
  have hD : ∀ m, ((passiveTransmission b E X) ^ m).trace.re = ((sand hT 1) ^ m).trace.re :=
    fun m => by rw [← trace_pow_sand hT 1 m, Matrix.mul_one]
  refine ⟨integral_congr_ae ?_, ?_⟩
  · filter_upwards [ae_trace_pow_fresh hb0 hb hW1 h1 h2 hX hT (k + 1),
      ae_trace_pow_fresh hb0 hb hW1 h1 h2 hX hT (l + 1)] with ω e1 e2
    rw [e1, e2, hD, hD]; rfl
  · have hW : (W : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
                                linarith
    simp only [transmissionBracket, trace_pow_eq_powSums hT, powSums]
    rw [show ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) * (1 - ts_lam hT i) =
        ∑ i, ts_lam hT i ^ (k + 1 + (l + 1)) - ∑ i, ts_lam hT i ^ (k + 1 + (l + 1) + 1) by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp

end BlockBand.Transmission.Generator
