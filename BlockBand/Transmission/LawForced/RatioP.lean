module

public import BlockBand.Transmission.LawForced.RatioLayer
public import BlockBand.Transmission.LawForced.RatioMom
public import BlockBand.Transmission.LawForced.RatioAlg
public import BlockBand.Transmission.LawForced.RatioLip
public import BlockBand.Transmission.Generator.PowAe

/-!
# The `κ ≡ 0` one-layer drift against the normalised product

`ratioP b E s X = (g+1)(Wδ₀+1)(t+1)(Wδ₁+1)`, `t = √W(‖Tr Qf‖ + hs(Q,f))` (the normalised
path variables at a deterministic `X`).

This module provides `ratioP` and the atom bounds (`ratio_atoms`) for **`ratio_layer_P`**, proved
in the sibling module: at a deterministic passive `X`, given the bulk constants as explicit
hypotheses (bilinear fluctuation `C_b/√W` at `p = 3, 9`; PCB covariance with
`ε = C_ε(W⁻² + W⁻¹(δ₀+δ₁+q/W))`; `ubarMean_bulk` with `C_u`; `|σ₋| ≤ C_σ`; `D₀ ≤ C_D`;
`q ≤ c_q g`):
`|E F_z(T(X₊)) − F_z(T) − ratioDrift D₀ E 0 u z μ_T/W| ≤ ratioK(…)·P²⁷·W^{-3/2}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {p W : ℕ}

/-- The normalised product `(g+1)(Wδ₀+1)(t+1)(Wδ₁+1)`. -/
def ratioP (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((passiveTransmission b E X).trace.re + 1) * (W * jetDistance0 b E X + 1) *
    (Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
      hsSandwich (passiveQ b E X) (passiveF b E X)) + 1) * (W * jetDistance1 b E s X + 1)

theorem le_prod4 {x y z w : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hw : 1 ≤ w) :
    1 ≤ x * y * z * w ∧ x ≤ x * y * z * w ∧ y ≤ x * y * z * w ∧ x * z ≤ x * y * z * w ∧
      w ≤ x * y * z * w := by
  have hxy : 1 ≤ x * y := one_le_mul_of_one_le_of_one_le hx hy
  have hxyz : 1 ≤ x * y * z := one_le_mul_of_one_le_of_one_le hxy hz
  refine ⟨one_le_mul_of_one_le_of_one_le hxyz hw, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul hxy hz zero_le_one (by linarith)]
  · nlinarith [mul_le_mul hxy hz zero_le_one (by linarith)]
  · have : x * z ≤ x * y * z := by nlinarith
    nlinarith
  · nlinarith

theorem hs_passiveTransmission_eq {b E : ℝ} (hη : 0 ≤ etaZ b E) (X : Matrix (Fin W) (Fin W) ℂ) :
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

theorem norm_sub_one_le {Ub : Matrix (Fin W) (Fin W) ℂ} {c Ua : ℝ} (hc0 : 0 ≤ 1 - c)
    (hUa : ‖Ub - (c : ℂ) • 1‖ ≤ Ua) : ‖Ub - 1‖ ≤ Ua + (1 - c) := by
  have e : Ub - 1 = (Ub - (c : ℂ) • 1) + ((c - 1 : ℝ) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    push_cast; rw [sub_smul, one_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add hUa ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hc0]
  exact mul_le_of_le_one_right hc0 PassiveLayer.norm_one_le'

/-- The normalised atoms at a deterministic passive `X` (`v = W^{-1/2}`). -/
theorem ratio_atoms {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) (s : ℂ)
    {cq : ℝ} (hcq : 0 ≤ cq) (hq : passiveMass b E X ≤ cq * (passiveTransmission b E X).trace.re) :
    1 ≤ ratioP b E s X ∧ (passiveTransmission b E X).trace.re ≤ ratioP b E s X ∧
      Real.sqrt (passiveTransmission b E X).trace.re ≤ ratioP b E s X ∧
      jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 ≤ ratioP b E s X * (Real.sqrt W)⁻¹ ^ 2 ∧
      jetDistance1 b E s X ≤ ratioP b E s X * (Real.sqrt W)⁻¹ ^ 2 ∧
      passiveMass b E X / W ≤ cq * ratioP b E s X * (Real.sqrt W)⁻¹ ^ 2 ∧
      layerTau b E X ≤ 4 * ratioP b E s X * (Real.sqrt W)⁻¹ ∧
      hsSandwich (passiveTransmission b E X) (passiveF b E X) ≤
        4 * ratioP b E s X * (Real.sqrt W)⁻¹ := by
  have hT := passiveTransmission_posSemidef (b := b) (by linarith) h1 h2 hX
  set g := (passiveTransmission b E X).trace.re
  have hg : 0 ≤ g := (mm_trace_posSemidef hT).1
  set d0 := jetDistance0 b E X
  set d1 := jetDistance1 b E s X
  have hd0 : 0 ≤ d0 := norm_nonneg _
  have hd1 : 0 ≤ d1 := norm_nonneg _
  set A := ‖(passiveQ b E X * passiveF b E X).trace‖
  set H := hsSandwich (passiveQ b E X) (passiveF b E X)
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  set sW := Real.sqrt W
  have hsW : 1 ≤ sW := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hWr
  set v := sW⁻¹
  have hv0 : 0 < v := inv_pos.2 (by linarith)
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ hsW
  have hsv : sW * v = 1 := mul_inv_cancel₀ (by linarith)
  have hW2 : (W : ℝ) = sW ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hWv : (W : ℝ) * v ^ 2 = 1 := by rw [hW2, ← mul_pow, hsv, one_pow]
  have hWi : (W : ℝ)⁻¹ = v ^ 2 := by rw [hW2, inv_pow]
  have hv42 : v ^ 4 ≤ v ^ 2 := pow_le_pow_of_le_one hv0.le hv1 (by norm_num)
  obtain ⟨hP1, hF1, hF2, hF13, hF4⟩ := le_prod4 (x := g + 1) (y := W * d0 + 1)
    (z := sW * (A + H) + 1) (w := W * d1 + 1) (by linarith)
    (le_add_of_nonneg_left (by positivity)) (le_add_of_nonneg_left (by positivity))
    (le_add_of_nonneg_left (by positivity))
  have hPdef : ratioP b E s X = (g + 1) * (W * d0 + 1) * (sW * (A + H) + 1) * (W * d1 + 1) := rfl
  rw [← hPdef] at hP1 hF1 hF2 hF13 hF4
  set P := ratioP b E s X
  have hP0 : 0 ≤ P := by linarith
  have hgP : g ≤ P := by linarith
  have hsg : Real.sqrt g ≤ P := (Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩).trans hF1
  have hAH : A + H ≤ (sW * (A + H) + 1) * v := by
    have : A + H = sW * (A + H) * v := by rw [mul_comm sW, mul_assoc, hsv, mul_one]
    nlinarith
  have hP3 : (g + 1) * ((sW * (A + H) + 1) * v) ≤ P * v := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hF13 hv0.le
  refine ⟨hP1, hgP, hsg, ?_, ?_, ?_, ?_, ?_⟩
  · have e : d0 = (W * d0) * v ^ 2 := by rw [mul_comm (W : ℝ), mul_assoc, hWv, mul_one]
    rw [hWi]
    have h3 : (W * d0 + 1) * v ^ 2 ≤ P * v ^ 2 := mul_le_mul_of_nonneg_right hF2 (by positivity)
    have h4 : (v ^ 2) ^ 2 = v ^ 4 := by ring
    calc d0 + (v ^ 2) ^ 2 ≤ W * d0 * v ^ 2 + v ^ 2 := by rw [← e]; linarith
      _ = (W * d0 + 1) * v ^ 2 := by ring
      _ ≤ P * v ^ 2 := h3
  · have e : d1 = (W * d1) * v ^ 2 := by rw [mul_comm (W : ℝ), mul_assoc, hWv, mul_one]
    have h3 : (W * d1 + 1) * v ^ 2 ≤ P * v ^ 2 := mul_le_mul_of_nonneg_right hF4 (by positivity)
    calc d1 = W * d1 * v ^ 2 := e
      _ ≤ (W * d1 + 1) * v ^ 2 := by nlinarith [sq_nonneg v]
      _ ≤ P * v ^ 2 := h3
  · rw [div_eq_mul_inv, hWi]
    have hq0 := passiveMass_nonneg b E hX
    have : cq * g ≤ cq * P := mul_le_mul_of_nonneg_left hgP hcq
    have := mul_le_mul_of_nonneg_right (hq.trans this) (sq_nonneg v)
    linarith
  · have h := layerTau_le hb0 (by linarith) h1 h2 hg
    have := mul_le_mul_of_nonneg_left hAH (show 0 ≤ 4 * (g + 1) by positivity)
    linarith
  · have hη0 := (PassiveCovariance.etaZ_pos b E (by linarith) h1 h2).le
    have hη1 := etaZ_le_one hb0 (by linarith) h1 h2
    rw [hs_passiveTransmission_eq hη0]
    have h4 : 4 * etaZ b E * H ≤ 4 * H := by
      have := mul_le_mul_of_nonneg_right hη1 hH; linarith
    have h5 : (sW * (A + H) + 1) * v ≤ (g + 1) * ((sW * (A + H) + 1) * v) := by
      have : 0 ≤ (sW * (A + H) + 1) * v := by positivity
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ g + 1 by linarith) this
      linarith
    linarith

end BlockBand.Transmission.LawForced
