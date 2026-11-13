module

public import BlockBand.Transmission.Generator.StepAlg
public import BlockBand.Transmission.Generator.Basic
public import BlockBand.Transmission.SourceMixing.MassUpdate
public import BlockBand.Transmission.Bridge.Passive
public import BlockBand.Transmission.PassiveLayer.TMWord

/-!
# The exact one-layer update `Tr T₊^k = Tr S^k` and `‖S‖ ≤ 1`

A step of the transmission generator theorem for `k ≥ 2`. `T = T(X)` for a passive `X`,
`U = LL*` (one fresh layer), `S = sand T U = Δ V*UV Δ`.
* `passiveTransmission_posSemidef`, `one_sub_passiveTransmission_posSemidef`, `ts_lam_le_one`,
  `norm_le_one_of_psd`: `0 ⪯ T ⪯ I`, so `t_i ≤ 1` and `‖T‖ ≤ 1`;
* `ae_trace_pow_fresh`: a.s. `Tr T(X₊)^k = Tr S^k` (`T₊ = L*TL`, `trace_pow_mul_comm`,
  `trace_pow_sand`);
* `ae_norm_sand_freshU_le`: a.s. `‖S‖ ≤ 1` (`S = GG*`, `G*G = L*TL = T₊`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem passiveTransmission_posSemidef {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    (passiveTransmission b E X).PosSemidef := by
  have hη := etaZ_pos b E hb h1 h2
  have hc : (0 : ℂ) ≤ ((4 * etaZ b E : ℝ) : ℂ) := by
    rw [Complex.nonneg_iff]; exact ⟨by simp; linarith, by simp⟩
  exact (hY.conjTranspose_mul_mul_same _).smul hc

theorem one_sub_passiveTransmission_posSemidef (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    (1 - passiveTransmission b E X).PosSemidef := by
  rw [Bridge.passiveTransmission_eq_one_sub, sub_sub_cancel]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem ts_lam_le_one {T : Matrix (Fin W) (Fin W) ℂ} (h0 : T.PosSemidef)
    (h1 : (1 - T).PosSemidef) (i : Fin W) : ts_lam h0 i ≤ 1 := by
  have hT := h0.1
  have he := hT.eigenvalues_eq i
  have hp := h1.re_dotProduct_nonneg (hT.eigenvectorBasis i)
  have hn : star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ (⇑(hT.eigenvectorBasis i)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hT.eigenvectorBasis.orthonormal.1 i]
    simp
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hn, map_sub] at hp
  simp only [RCLike.one_re] at hp
  have : hT.eigenvalues i = RCLike.re (star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ
      (T *ᵥ ⇑(hT.eigenvectorBasis i))) := he
  show hT.eigenvalues i ≤ 1
  linarith

theorem norm_le_one_of_psd {T : Matrix (Fin W) (Fin W) ℂ} (h0 : T.PosSemidef)
    (h1 : (1 - T).PosSemidef) : ‖T‖ ≤ 1 := by
  have h := norm_sand_le h0 (ts_lam_le_one h0 h1) 1
  rw [sand_one] at h
  have hn1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
  have hV : ‖ts_U h0‖ ≤ 1 := norm_unitary_le (ts_U_star_mul h0)
  have hV' : ‖star (ts_U h0)‖ ≤ 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose]; exact hV
  rw [ts_spectral h0]
  calc ‖ts_U h0 * diagonal (fun i => (ts_lam h0 i : ℂ)) * star (ts_U h0)‖
      ≤ ‖ts_U h0‖ * ‖diagonal (fun i => (ts_lam h0 i : ℂ))‖ * ‖star (ts_U h0)‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
          (norm_nonneg _))
    _ ≤ 1 * 1 * 1 := by gcongr; exact h.trans hn1
    _ = 1 := by ring

/-- `T₊ = L*TL` a.s. -/
theorem ae_transmission_fresh {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, passiveTransmission b E (freshSchur E X ω) =
      (freshL b E X ω)ᴴ * passiveTransmission b E X * freshL b E X ω := by
  filter_upwards [ae_passiveQ_freshSchur hb0 hb hW h1 h2 hY] with ω h
  rw [passiveTransmission, passiveTransmission, h, Matrix.mul_smul, Matrix.smul_mul]

/-- **The exact update**: `Tr T(X₊)^k = Tr (sand T (LL*))^k` a.s. -/
theorem ae_trace_pow_fresh {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) (k : ℕ) :
    ∀ᵐ ω ∂freshLaw W b, ((passiveTransmission b E (freshSchur E X ω)) ^ k).trace =
      ((sand hT (freshU b E X ω)) ^ k).trace := by
  filter_upwards [ae_transmission_fresh hb0 hb hW h1 h2 hY] with ω h
  rw [h, Matrix.mul_assoc, trace_pow_mul_comm, Matrix.mul_assoc, ← trace_pow_sand hT]
  rfl

/-- `S = GG*` with `G*G = L*TL`. -/
theorem sand_freshU_eq {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef)
    (L : Matrix (Fin W) (Fin W) ℂ) :
    sand hT (L * Lᴴ) = (sqD hT * star (ts_U hT) * L) * (sqD hT * star (ts_U hT) * L)ᴴ ∧
      (sqD hT * star (ts_U hT) * L)ᴴ * (sqD hT * star (ts_U hT) * L) = Lᴴ * T * L := by
  have hD : (sqD hT)ᴴ = sqD hT := by
    rw [sqD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hV : (star (ts_U hT))ᴴ = ts_U hT := by rw [Matrix.star_eq_conjTranspose,
    conjTranspose_conjTranspose]
  constructor
  · rw [sand]
    simp only [conjTranspose_mul, hD, hV, Matrix.mul_assoc]
  · simp only [conjTranspose_mul, hD, hV, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (sqD hT) (sqD hT), sqD_mul_sqD]
    conv_rhs => rw [ts_spectral hT]
    simp only [Matrix.mul_assoc]

/-- **`‖S‖ ≤ 1` a.s.** -/
theorem ae_norm_sand_freshU_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, ‖sand hT (freshU b E X ω)‖ ≤ 1 := by
  filter_upwards [ae_transmission_fresh hb0 hb hW h1 h2 hY] with ω h
  obtain ⟨e1, e2⟩ := sand_freshU_eq hT (freshL b E X ω)
  set G := sqD hT * star (ts_U hT) * freshL b E X ω
  have hTp : ‖passiveTransmission b E (freshSchur E X ω)‖ ≤ 1 := by
    refine norm_le_one_of_psd ?_ (one_sub_passiveTransmission_posSemidef b E _)
    rw [h]; exact hT.conjTranspose_mul_mul_same _
  have hS : sand hT (freshU b E X ω) = G * Gᴴ := e1
  rw [hS]
  have a1 : ‖G * Gᴴ‖ = ‖Gᴴ‖ * ‖Gᴴ‖ := by
    have := Matrix.l2_opNorm_conjTranspose_mul_self Gᴴ
    rwa [conjTranspose_conjTranspose] at this
  have a2 : ‖Gᴴ * G‖ = ‖G‖ * ‖G‖ := Matrix.l2_opNorm_conjTranspose_mul_self G
  rw [a1, Matrix.l2_opNorm_conjTranspose, ← a2, e2, ← h]
  exact hTp

end BlockBand.Transmission.Generator
