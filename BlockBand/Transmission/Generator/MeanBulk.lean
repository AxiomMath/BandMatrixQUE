module

public import BlockBand.Transmission.Generator.MeanOnDomain
public import BlockBand.Transmission.Generator.RefinedMean

/-!
# The one-layer mean `Ū = E[LL*]`: operator bound and every weighted refined mean, bulk-uniform

Hypothesis of `ubarMean_bulk`: `PassiveBoundsStatement`. `e = δ₀ + W⁻²`, `c = meanC = (1 + αq/W)⁻¹`.

This module provides the error `wmErr` and the on- and off-domain estimates (`ub_on`, `ub_off`)
for **`ubarMean_bulk`**, proved in the sibling module: `b ∈ (0,1/2)`, `κ > 0` first; then
`C, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ` and every deterministic passive `X` (`Y ⪰ 0`):
* (a) `‖Ū - c·I‖ ≤ C(e + q/W)`;
* (b) for every `G ⪰ 0`: `|Tr(GŪ) - c·Tr G| ≤ C·wmErr`,
  `wmErr = e|Tr(Gf)| + e²Tr G + eq·Tr G/W + W⁻²Tr G`.
At `G = Q`, (b) is `massMeanRefined_bulk` (`wmErr = refinedErr`). Proof: on the matched
domain `wm_onDomain_op`/`wm_onDomain_wt`; off it the crude `‖Ū‖ ≤ C₁`; passive inputs by the
`regX` limit (`G` fixed).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The `G`-weighted refined error `e|Tr(Gf)| + e²Tr G + eq·Tr G/W + W⁻²Tr G`. -/
def wmErr (b E : ℝ) (X G : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * ‖(G * passiveF b E X).trace‖ +
    (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 2 * G.trace.re +
    (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X * G.trace.re / W +
    (W : ℝ)⁻¹ ^ 2 * G.trace.re

theorem meanC_pos_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    0 < meanC b E X ∧ meanC b E X ≤ 1 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hα : 0 ≤ alphaCoef b E := by
    rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
  have hq := passiveMass_nonneg b E hY
  have h0 : 1 ≤ 1 + alphaCoef b E * passiveMass b E X / W := by
    have : 0 ≤ alphaCoef b E * passiveMass b E X / W := by positivity
    linarith
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ h0⟩

/-- `k₀a₀ + k₁a₁ + k₂a₂ + k₃a₃ ≤ K(a₀ + a₁ + a₂ + a₃)` for `0 ≤ kᵢ ≤ K`, `aᵢ ≥ 0`. -/
theorem lin4_le {k₀ k₁ k₂ k₃ a₀ a₁ a₂ a₃ K : ℝ} (h₀ : k₀ ≤ K) (h₁ : k₁ ≤ K) (h₂ : k₂ ≤ K)
    (h₃ : k₃ ≤ K) (a₀0 : 0 ≤ a₀) (a₁0 : 0 ≤ a₁) (a₂0 : 0 ≤ a₂) (a₃0 : 0 ≤ a₃) :
    k₀ * a₀ + k₁ * a₁ + k₂ * a₂ + k₃ * a₃ ≤ K * (a₀ + a₁ + a₂ + a₃) := by
  have := mul_le_mul_of_nonneg_right h₀ a₀0
  have := mul_le_mul_of_nonneg_right h₁ a₁0
  have := mul_le_mul_of_nonneg_right h₂ a₂0
  have := mul_le_mul_of_nonneg_right h₃ a₃0
  linarith

/-- The constant of `ubarMean_strict_bulk`. -/
def ubK (Cf C2 CD Cm Li b d : ℝ) : ℝ :=
  (Cf + (3 * C2 + Cf * (2 * CD)) * (2 * Li / b)) + (Cf * (5 / 2 * Cm) + Cm * Li) +
    10 * Li / b + (Cf * Cf * Cf + Cf + 1) / d +
  ((Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)) + 4 * Cm +
    (Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))) +
    (4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b) +
    (Cf * Cf * Cf + Cf + 1) / d ^ 2)

/-- **Off the matched domain**: the crude bound `‖U‖ ≤ C₁`. -/
theorem ub_off {U : Matrix (Fin W) (Fin W) ℂ} {c e d C₁ K q' : ℝ} (hUn : ‖U‖ ≤ C₁)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d) (hde : d ≤ e) (hK1 : (C₁ + 1) / d ≤ K)
    (hK2 : (C₁ + 1) / d ^ 2 ≤ K) (hq' : 0 ≤ q') :
    ‖U - (c : ℂ) • 1‖ ≤ K * (e + q') ∧ ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
      ∀ x : ℝ, 0 ≤ x → ‖(G * U).trace - (c : ℂ) * G.trace‖ ≤ K * (e ^ 2 * G.trace.re + x) := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans hUn
  have hK : 0 ≤ K := le_trans (by positivity) hK1
  have he : 0 ≤ e := hd.le.trans hde
  refine ⟨?_, fun G hGp x hx => ?_⟩
  · have hcn : ‖(c : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := by
      refine (norm_smul_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hc0.le]
      exact (mul_le_mul hc1 PassiveLayer.norm_one_le' (norm_nonneg _) zero_le_one).trans
        (by norm_num)
    have h3 : ‖U - (c : ℂ) • 1‖ ≤ C₁ + 1 := (norm_sub_le _ _).trans (add_le_add hUn hcn)
    have h4 : C₁ + 1 ≤ (C₁ + 1) / d * e := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      exact mul_le_mul_of_nonneg_left hde (by positivity)
    have h5 : (C₁ + 1) / d * e ≤ K * e := mul_le_mul_of_nonneg_right hK1 he
    have : 0 ≤ K * q' := mul_nonneg hK hq'
    linarith [mul_add K e q']
  · have hg0 := (mm_trace_posSemidef hGp).1
    have hgr : G.trace = (G.trace.re : ℂ) := (mm_trace_posSemidef hGp).2
    have h3 : ‖(G * U).trace - (c : ℂ) * G.trace‖ ≤ (C₁ + 1) * G.trace.re := by
      rw [trace_mul_comm]
      refine (norm_sub_le _ _).trans ?_
      have a1 := (norm_trace_mul_posSemidef_le hGp U).trans
        (mul_le_mul_of_nonneg_right hUn hg0)
      have a2 : ‖(c : ℂ) * G.trace‖ ≤ G.trace.re := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le, hgr, Complex.norm_real,
          Real.norm_of_nonneg hg0]
        exact mul_le_of_le_one_left hg0 hc1
      linarith
    have hde2 : d ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hd.le hde 2
    have h4 : (C₁ + 1) * G.trace.re ≤ (C₁ + 1) / d ^ 2 * (e ^ 2 * G.trace.re) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ (C₁ + 1) * G.trace.re := by positivity
      nlinarith
    have h5 : (C₁ + 1) / d ^ 2 * (e ^ 2 * G.trace.re) ≤ K * (e ^ 2 * G.trace.re) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have : 0 ≤ K * x := mul_nonneg hK hx
    linarith [mul_add K (e ^ 2 * G.trace.re) x]

/-- **On the matched domain**, both bounds with the constant `ubK`. -/
theorem ub_on {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e d : ℝ} (hC2 : 0 ≤ C2) (hd : 0 ≤ d) (hCm : 0 ≤ Cm) (hCD : 0 ≤ CD)
    (he0 : 0 ≤ e) (hWe : (W : ℝ)⁻¹ ^ 2 ≤ e)
    (hLi : (etaZ b E)⁻¹ ≤ Li) (hCme : Cm * e ≤ 1 / 2) (hCmeLi : Cm * e * Li ≤ 1)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e) (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e)
    (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hU : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hM : ‖mOf b E X‖ ≤ CD)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤
      C2 / (W : ℝ) ^ 2) :
    ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ ≤
        ubK Cf C2 CD Cm Li b d * (e + passiveMass b E X / W) ∧
      ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
        ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
          ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ ubK Cf C2 CD Cm Li b d *
          (e * ‖(G * passiveF b E X).trace‖ + e ^ 2 * G.trace.re +
            e * passiveMass b E X * G.trace.re / W + (W : ℝ)⁻¹ ^ 2 * G.trace.re) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans hsn
  have hq : 0 ≤ passiveMass b E X := passiveMass_nonneg b E hX.posSemidef
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have honA := wm_onDomain_op hb0 hb h1 h2 hW1 hX hLi hCme hzζ hKM1 hh1 hz2 hU hsn hG hB0
    hB1 hzM hS
  have honB := wm_onDomain_wt hb0 hb h1 h2 hW1 hX hCm hCD he0 hLi hCme hCmeLi hzζ hKM1 hh1
    hz2 hU hsn hM hG hB0 hB1 hzM hS
  set K := ubK Cf C2 CD Cm Li b d
  set ka1 := Cf + (3 * C2 + Cf * (2 * CD)) * (2 * Li / b)
  set ka2 := Cf * (5 / 2 * Cm) + Cm * Li
  set k0 := Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)
  set k2 := Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))
  set k3 := 4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b
  have hka1 : 0 ≤ ka1 := by positivity
  have hka2 : 0 ≤ ka2 := by positivity
  have hk0 : 0 ≤ k0 := by positivity
  have hk2 : 0 ≤ k2 := by positivity
  have hk3 : 0 ≤ k3 := by positivity
  have hr1 : 0 ≤ (Cf * Cf * Cf + Cf + 1) / d := by positivity
  have hr2 : 0 ≤ (Cf * Cf * Cf + Cf + 1) / d ^ 2 := by positivity
  have hKdef : K = ka1 + ka2 + 10 * Li / b + (Cf * Cf * Cf + Cf + 1) / d +
      (k0 + 4 * Cm + k2 + k3 + (Cf * Cf * Cf + Cf + 1) / d ^ 2) := rfl
  have h10 : 0 ≤ 10 * Li / b := by positivity
  refine ⟨?_, fun G hGp => ?_⟩
  · refine honA.trans ?_
    have a1 : ka1 * (W : ℝ)⁻¹ ^ 2 ≤ ka1 * e := mul_le_mul_of_nonneg_left hWe hka1
    have hqW : 0 ≤ passiveMass b E X / W := by positivity
    have b1 : (ka1 + ka2) * e ≤ K * e := mul_le_mul_of_nonneg_right (by linarith) he0
    have b2 : 10 * Li / b * (passiveMass b E X / W) ≤ K * (passiveMass b E X / W) :=
      mul_le_mul_of_nonneg_right (by linarith) hqW
    linarith [mul_add K e (passiveMass b E X / W)]
  · refine (honB G hGp).trans ?_
    have hg0 := (mm_trace_posSemidef hGp).1
    have h := lin4_le (k₀ := 4 * Cm) (k₁ := k2) (k₂ := k3) (k₃ := k0) (K := K)
      (by linarith) (by linarith) (by linarith) (by linarith)
      (a₀ := e * ‖(G * passiveF b E X).trace‖) (a₁ := e ^ 2 * G.trace.re)
      (a₂ := e * passiveMass b E X * G.trace.re / W) (a₃ := (W : ℝ)⁻¹ ^ 2 * G.trace.re)
      (by positivity) (by positivity) (by positivity) (by positivity)
    linarith

end BlockBand.Transmission.Generator
