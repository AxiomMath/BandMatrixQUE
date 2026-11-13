module

public import BlockBand.Transmission.Generator.StepPoint

/-!
# The `k = j + 2` one-layer drift at a deterministic passive input

**`layer_point`**: for passive `X`, `T = T(X)`, `g = Tr T`, `τ = layerTau = |Tr(Tf)| + √g·hs(T,f)`,
`e = δ₀ + W⁻²`, `y = D₀g/(2W)`, given the HS moments with constant `C_b`, the covariance bound
with error `ε ≥ 0` (shape of `CovarianceBulk.PassiveCovarianceBulk`), `‖Ū - c‖ ≤ U_a` and the
weighted mean with constant `C_u`:
`|E Re Tr T(X₊)^k - Re Tr T^k - A_k(P)/W| ≤ E₁ + E₂ + E₃ + kE₄ + E₅`, where
`E₁ = k³6^{2k}(C_bg/√W)³ + k²3(k-1)2^{3(k-1)}U_a(C_bg/√W)² + ε(k-1)²g²`,
`E₂ = 2|σ₋|/W·(k-1)²τ²`, `E₃ = k6^{2k}U_a²g`, `E₄ = C_u⁺(eτ + e²g + eqg/W + W⁻²g)`,
`E₅ = k²y²g + (k-2)y·D₀k²g²/W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.SourceMixing BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- `τ = |Tr(Tf)| + √(Tr T)·hs(T,f)`. -/
def layerTau (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖(passiveTransmission b E X * passiveF b E X).trace‖ +
    Real.sqrt (passiveTransmission b E X).trace.re *
      hsSandwich (passiveTransmission b E X) (passiveF b E X)

/-- **The `k = j + 2` one-layer drift, all inputs explicit.** -/
theorem layer_point {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hU2 : Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b)) {Cb : ℝ}
    (hmom : ∀ hT : (passiveTransmission b E X).PosSemidef,
        Integrable (fun ω => frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b) ∧
        ∫ ω, frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ (Cb / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 2 ∧
        Integrable (fun ω => ‖sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))‖ * frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b) ∧
        ∫ ω, ‖sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))‖ *
          frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ (Cb / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 3)
    (σm : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        v₁ v₂ v₃ v₄ - ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
          (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
            crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
          σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
          conj σm / W * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
        ε * fourNorm v₁ v₂ v₃ v₄)
    {Ua Cu : ℝ} (hUa : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      ((meanC b E X : ℝ) : ℂ) • 1‖ ≤ Ua)
    (hwm : ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
      ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
        ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ Cu * wmErr b E X G) (j : ℕ) :
    |∫ ω, ((passiveTransmission b E (freshSchur E X ω)) ^ (j + 2)).trace.re ∂freshLaw W b -
        ((passiveTransmission b E X) ^ (j + 2)).trace.re -
        transmissionDrift (transportD0 b E) (j + 2)
          (fun m => ((passiveTransmission b E X) ^ m).trace.re) / W| ≤
      (((j + 1 + 1 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 1 + 1)) *
          (Cb / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 3 +
        ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) * (3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1)) *
          Ua)) * (Cb / Real.sqrt W * (passiveTransmission b E X).trace.re) ^ 2 +
        ε * (((j + 1 : ℕ) : ℝ) ^ 2 * (passiveTransmission b E X).trace.re ^ 2)) +
      (‖σm / W‖ + ‖conj σm / W‖) * ((j + 1 : ℕ) : ℝ) ^ 2 * layerTau b E X ^ 2 +
      ((j + 1 + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 1 + 1)) *
        (Ua ^ 2 * (passiveTransmission b E X).trace.re) +
      ((j + 2 : ℕ) : ℝ) * (max Cu 0 * ((jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * layerTau b E X +
        (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 2 * (passiveTransmission b E X).trace.re +
        (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X *
          (passiveTransmission b E X).trace.re / W +
        (W : ℝ)⁻¹ ^ 2 * (passiveTransmission b E X).trace.re)) +
      (((j + 2 : ℕ) : ℝ) ^ 2 * (transportD0 b E * (passiveTransmission b E X).trace.re /
          (2 * W)) ^ 2 * (passiveTransmission b E X).trace.re +
        j * (transportD0 b E * (passiveTransmission b E X).trace.re / (2 * W)) *
          (transportD0 b E * ((j + 2 : ℕ) : ℝ) ^ 2 * (passiveTransmission b E X).trace.re ^ 2) /
          W) := by
  have hT : (passiveTransmission b E X).PosSemidef :=
    passiveTransmission_posSemidef (by linarith) h1 h2 hX
  have ht1 : ∀ i, ts_lam hT i ≤ 1 :=
    ts_lam_le_one hT (one_sub_passiveTransmission_posSemidef b E X)
  obtain ⟨hc0, hc1⟩ := meanC_pos_le hb0 hb h1 h2 hX
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  have hSb := norm_sand_matrixExpect_le hT _ (measurable_freshU b E X) hUi hS
  obtain ⟨hI2, hm2, hI3, hm3⟩ := hmom hT
  have hQ := lp_quad hb0 hb h1 h2 hW1 hX hT ht1 hUi hU2 hI2 hm2 hI3 hm3 (sq_nonneg _) _ _ _ hε
    hcov hUa j
  have hM := step_main_term hT (transportD0 b E) (meanC b E X) (σm / W) (conj σm / W)
    (passiveF b E X) j
  have hF := step_fterm hT ht1 (σm / W) (conj σm / W) (passiveF b E X) j
  have hFre : |(((meanC b E X ^ j : ℝ) : ℂ) * ∑ i, ∑ m, ((ts_lam hT i * ts_lam hT m *
      wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) * (σm / W * (ts_ent hT (passiveF b E X) i i *
      ts_ent hT (passiveF b E X) m m) + conj σm / W * (conj (ts_ent hT (passiveF b E X) i i) *
      conj (ts_ent hT (passiveF b E X) m m)))).re| ≤
      (‖σm / W‖ + ‖conj σm / W‖) * ((j + 1 : ℕ) : ℝ) ^ 2 * layerTau b E X ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hc0.le j)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hc0.le hc1)).trans hF
  have hZ := step_zeroth hT ht1 hc0.le hc1 (matrixExpect (freshLaw W b) (freshU b E X)) hSb j
  have hG := lp_wm hX hT ht1 hwm j
  have hsc := lp_scal hb0 hb h1 h2 hW1 hT ht1 j
  have hI : ∫ ω, ((passiveTransmission b E (freshSchur E X ω)) ^ (j + 2)).trace.re
      ∂freshLaw W b = ∫ ω, ((sand hT (freshU b E X ω)) ^ (j + 2)).trace.re ∂freshLaw W b :=
    integral_congr_ae (by
      filter_upwards [ae_trace_pow_fresh hb0 hb hW1 h1 h2 hX hT (j + 2)] with ω hω
      rw [hω])
  rw [hI, trace_pow_eq_powSums hT (j + 2), funext (trace_pow_eq_powSums hT)]
  have hcomb := step_combine (k := ((j + 2 : ℕ) : ℝ)) j hQ hM hFre hZ hG hc0.le hc1
    (Nat.cast_nonneg _) hsc
  refine hcomb.trans ?_
  have hUa0 : 0 ≤ ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ :=
    norm_nonneg _
  have hg0 : 0 ≤ (passiveTransmission b E X).trace.re := (mm_trace_posSemidef hT).1
  have hE3 : ((j + 1 + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 1 + 1)) *
      (‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ ^ 2 *
        (passiveTransmission b E X).trace.re) ≤
      ((j + 1 + 1 : ℕ) : ℝ) * (3 * 2) ^ (2 * (j + 1 + 1)) *
        (Ua ^ 2 * (passiveTransmission b E X).trace.re) := by
    gcongr
  simp only [layerTau]
  exact add_le_add (add_le_add (add_le_add le_rfl hE3) le_rfl) le_rfl

end BlockBand.Transmission.Generator
