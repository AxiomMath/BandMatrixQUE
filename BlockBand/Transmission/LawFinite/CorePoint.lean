module

public import BlockBand.Transmission.LawFinite.CoreAlg

/-!
# The one-layer inequality at a fresh sample

**`core_point`**: for a passive `X` and a fresh sample with `A` Hermitian and `B` invertible,
`q ≤ F₀² Re Tr(L*QL) + q/4 + m·p₀Li³ξγ`, where `m = #{s_i(B)² < h²}`,
`F₀ = (β + 3h⁻¹p₀)Li + 1` and `p₀, β, ξ, γ, Li` bound `‖A‖ + |E| + ‖X‖`, `‖B‖`, `‖X‖`,
`‖K𝒢₁₁‖`, `η⁻¹`. It combines `layer_blocks`, `core_identity` (with `G = cutInv B h²`,
`Π = cutLow B h²`), `core_trace_le` and `re_trace_cutLow_mul_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem norm_passiveY_le (X : Matrix (Fin W) (Fin W) ℂ) : ‖passiveY X‖ ≤ ‖X‖ := by
  rw [passiveY, matrixImaginaryPart, norm_neg, norm_smul]
  have h2 : ‖-Complex.I / 2‖ = 1 / 2 := by simp
  rw [h2]
  have : ‖X - Xᴴ‖ ≤ ‖X‖ + ‖X‖ := (norm_sub_le _ _).trans (by rw [l2_opNorm_conjTranspose])
  linarith

/-- The `P`-block `A - E - X` of the fresh layer. -/
def layerP (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  ω.1 0 - (E : ℂ) • 1 - X

theorem norm_layerP_le (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖layerP E X ω‖ ≤ ‖ω.1 0‖ + |E| + ‖X‖ := by
  have h1 : ‖((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))‖ ≤ |E| := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) norm_one_le'
  have h2 := norm_sub_le (ω.1 0 - (E : ℂ) • 1) X
  have h3 := norm_sub_le (ω.1 0) ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
  rw [layerP]; linarith

/-- **Pointwise one-layer bound**. For a passive `X`, a fresh sample with `A`
Hermitian and `B` invertible, `h > 0`, `‖z‖ ≤ 3`, `η⁻¹ ≤ Li`, `‖A‖ + |E| + ‖X‖ ≤ p₀`, `‖B‖ ≤ β`,
`‖X‖ ≤ ξ`, `‖K𝒢₁₁‖ ≤ γ`: with `F₀ = (β + 3h⁻¹p₀)Li + 1` and `q₊' = Re Tr(L*QL)`,
`q ≤ F₀² q₊' + q/4 + m·p₀Li³ξγ`, `m = #{s_i(B)² < h²}`. -/
theorem core_point {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    {h Li p₀ β ξ γ : ℝ} (hh : 0 < h) (hz : ‖boundaryZ b E‖ ≤ 3) (hLi : (etaZ b E)⁻¹ ≤ Li)
    (hp : ‖ω.1 0‖ + |E| + ‖X‖ ≤ p₀) (hβ : ‖ω.2 0 0‖ ≤ β) (hξ : ‖X‖ ≤ ξ)
    (hγ : ‖kG11 E (boundaryZ b E) X ω‖ ≤ γ) :
    passiveMass b E X ≤ ((β + 3 * h⁻¹ * p₀) * Li + 1) ^ 2 *
        ((freshL b E X ω)ᴴ * passiveQ b E X * freshL b E X ω).trace.re +
      passiveMass b E X / 4 + (smallSingularCount (h ^ 2) (ω.2 0 0) : ℝ) *
        (p₀ * Li * (Li ^ 2 * ξ) * γ) := by
  set z := boundaryZ b E
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hzi : 0 < z.im := Bridge.boundaryZ_im_pos (by linarith) h1 h2
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hzi
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  have hξ0 : 0 ≤ ξ := (norm_nonneg _).trans hξ
  set B := ω.2 0 0
  set P := layerP E X ω
  set R := passiveResolvent b E X
  set K : Matrix (Fin W) (Fin W) ℂ := z • 1 - X
  set G := cutInv B (h ^ 2)
  set Pm := cutLow B (h ^ 2)
  set Q := passiveQ b E X
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  obtain ⟨hSu, h11, h12⟩ := layer_blocks E hzi hY hA hB
  have hKR : K * R = 1 := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY).1
  have hid := core_identity hz0 hSu rfl h11 h12 (mul_cutInv (c := h ^ 2) B (by positivity)) hKR
  have hL : freshL b E X ω = K * g12 E z X ω := rfl
  have hk : kG11 E z X ω = K * g11 E z X ω := rfl
  rw [← hL, ← hk] at hid
  -- norm bounds
  have hR : ‖R‖ ≤ Li := (PassiveCovariance.norm_passiveResolvent_le hb0 hb h1 h2 hY).trans hLi
  have hP : ‖P‖ ≤ p₀ := (norm_layerP_le E X ω).trans hp
  have hp0 : 0 ≤ p₀ := (norm_nonneg _).trans hP
  have hG : ‖G‖ ≤ h⁻¹ := norm_cutInv_le B hh
  have hF : ‖(Bᴴ - z • (G * P)) * R‖ ≤ (β + 3 * h⁻¹ * p₀) * Li + 1 := by
    have e1 : ‖Bᴴ - z • (G * P)‖ ≤ β + 3 * h⁻¹ * p₀ := by
      refine (norm_sub_le _ _).trans (add_le_add (by rwa [l2_opNorm_conjTranspose]) ?_)
      rw [norm_smul]
      calc ‖z‖ * ‖G * P‖ ≤ 3 * (h⁻¹ * p₀) :=
            mul_le_mul hz ((norm_mul_le _ _).trans (mul_le_mul hG hP (norm_nonneg _)
              (by positivity))) (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have e2 := (norm_mul_le _ _).trans (mul_le_mul e1 hR (norm_nonneg _)
      ((norm_nonneg _).trans e1))
    linarith
  have hQn : ‖Q‖ ≤ Li ^ 2 * ξ := by
    have : ‖Q‖ ≤ ‖Rᴴ‖ * ‖passiveY X‖ * ‖R‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    rw [l2_opNorm_conjTranspose] at this
    refine this.trans ?_
    have hy := (norm_passiveY_le X).trans hξ
    calc ‖R‖ * ‖passiveY X‖ * ‖R‖ ≤ Li * ξ * Li := by gcongr
      _ = _ := by ring
  have hΓ : ‖P * R * Q * kG11 E z X ω‖ ≤ p₀ * Li * (Li ^ 2 * ξ) * γ := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul hP hR (norm_nonneg _) hp0)) hQn (norm_nonneg _)
      (by positivity))) hγ (norm_nonneg _) (by positivity))
  -- the trace inequality
  have hN : (Q * (kG11 E z X ω * Pm * P * R)).trace.re ≤
      (smallSingularCount (h ^ 2) B : ℝ) * (p₀ * Li * (Li ^ 2 * ξ) * γ) := by
    have htr : (Q * (kG11 E z X ω * Pm * P * R)).trace = (Pm * (P * R * Q * kG11 E z X ω)).trace := by
      rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
      rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [htr, ← card_eig_mul_conj_lt]
    refine (re_trace_cutLow_mul_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_left hΓ (Nat.cast_nonneg _)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hT := core_trace_le hQ (by positivity) hF hid
  have hq : passiveMass b E X = Q.trace.re := rfl
  have hN' : (Q * (kG11 E z X ω * cutLow B (h ^ 2) * (ω.1 0 - (E : ℂ) • 1 - X) * R)).trace.re ≤
      (smallSingularCount (h ^ 2) B : ℝ) * (p₀ * Li * (Li ^ 2 * ξ) * γ) := hN
  rw [hq]
  linarith

end BlockBand.Transmission.LawFinite
