module

public import BlockBand.Transmission.LawFinite.CoreCheb

/-!
# The initial bond of the finite core

* `trace_passiveY_le`: `Re Tr Y ≤ ‖z - X‖² q(X)` for passive `X` (`Y = K*QK`);
* `trace_gram_ge`: `c(W - #{s_i(B)² < c}) ≤ Re Tr(BB*)`;
* `bondX`: the first-layer input `z⁻¹B₀B₀* - iε₁` as a function of the past at length `0`;
  `ae_pathNearSchur_one_bond` (from `ae_pathNearSchur_one`), `passiveY_bondX`
  (`Re Tr Y ≥ (η/|z|²) Re Tr(B₀B₀*)`), `norm_bondX_le`.

The paper's functional-calculus bound `q ≥ η Tr B*B/(|z|² + ‖B‖²)²` is replaced by
`q ≥ Re Tr Y/‖z - X‖²`, and Gaussian trace concentration by `trace_gram_ge` plus the
small-singular-value fraction of a Ginibre matrix.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

/-- **`q(X) ≥ Re Tr Y/‖z - X‖²`** for passive `X`: `Y = K*QK`, so `Re Tr Y ≤ ‖KK*‖ Re Tr Q`. -/
theorem trace_passiveY_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    (passiveY X).trace.re ≤ ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X‖ ^ 2 *
      passiveMass b E X := by
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hRK := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2 hY).2
  have hQ : (passiveQ b E X).PosSemidef := hY.conjTranspose_mul_mul_same _
  have hY' : passiveY X = Kᴴ * passiveQ b E X * K := by
    rw [passiveQ]
    have : Kᴴ * ((passiveResolvent b E X)ᴴ * passiveY X * passiveResolvent b E X) * K =
        (passiveResolvent b E X * K)ᴴ * passiveY X * (passiveResolvent b E X * K) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hRK, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have htr : (Kᴴ * passiveQ b E X * K).trace = (K * Kᴴ * passiveQ b E X).trace := by
    rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, trace_mul_comm]
  rw [hY', htr]
  refine (Complex.re_le_norm _).trans ((PassiveCovariance.norm_trace_mul_posSemidef_le hQ _).trans ?_)
  have : ‖K * Kᴴ‖ ≤ ‖K‖ ^ 2 := by
    rw [sq]; exact (norm_mul_le _ _).trans (by rw [l2_opNorm_conjTranspose])
  exact mul_le_mul_of_nonneg_right this (PassiveCovariance.passiveMass_nonneg b E hY)

/-- `c(W - #{s_i(B)² < c}) ≤ Re Tr(BB*)`. -/
theorem trace_gram_ge (B : Matrix (Fin W) (Fin W) ℂ) (c : ℝ) :
    c * (W - smallSingularCount c B) ≤ (B * Bᴴ).trace.re := by
  set hH := isHermitian_mul_conjTranspose_self B
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := (posSemidef_self_mul_conjTranspose B).eigenvalues_nonneg
  rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum, ← card_eig_mul_conj_lt]
  show _ ≤ ∑ i, ((hH.eigenvalues i : ℂ)).re
  simp only [Complex.ofReal_re]
  have hcard : ((Finset.univ.filter fun i => hH.eigenvalues i < c).card : ℝ) +
      ((Finset.univ.filter fun i => ¬ hH.eigenvalues i < c).card : ℝ) = W := by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin W => hH.eigenvalues i < c)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  calc c * (W - ((Finset.univ.filter fun i => hH.eigenvalues i < c).card : ℝ))
      = ∑ i, (if hH.eigenvalues i < c then 0 else c) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
          ← hcard]
        ring
    _ ≤ ∑ i, hH.eigenvalues i := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h
        · exact hnn i
        · exact not_lt.mp h

/-- The input of the first layer: the far lead `z⁻¹B₀B₀*` with the absorption of block `1`. -/
def bondX (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) (p : PastSample W 0) : Matrix (Fin W) (Fin W) ℂ :=
  absorbedInput ((boundaryZ b E)⁻¹ • (p.2 0 * (p.2 0)ᴴ)) (layerAbsorption W κ 1 0)

theorem measurable_bondX (b E : ℝ) (κ : ℝ → ℝ) : Measurable (bondX b E κ W) := by
  have hB : Measurable fun p : PastSample W 0 => p.2 0 :=
    (measurable_pi_apply 0).comp measurable_snd
  have hM : Measurable fun p : PastSample W 0 => p.2 0 * (p.2 0)ᴴ :=
    Bridge.measurable_matrix_mul' hB (Bridge.measurable_matrix_conjTranspose' hB)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [bondX, absorbedInput, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (measurable_const.mul hM.eval_matrix).sub measurable_const

theorem ae_pathNearSchur_one_bond {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {κ : ℝ → ℝ} (hκ : ∀ s, 0 ≤ κ s) :
    ∀ᵐ ω ∂growthPathLaw W b, pathNearSchur b E κ W (0 + 1) ω =
      freshSchur E (bondX b E κ W (pastCoords W 0 ω)) (freshSample W 0 ω) := by
  filter_upwards [ae_pathNearSchur_one hb h1 h2 hW hκ] with ω h
  rw [Nat.zero_add, h]; rfl

theorem passiveY_bondX {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ s, 0 ≤ κ s) (p : PastSample W 0) :
    (passiveY (bondX b E κ W p)).PosSemidef ∧
      etaZ b E / Complex.normSq (boundaryZ b E) * (p.2 0 * (p.2 0)ᴴ).trace.re ≤
        (passiveY (bondX b E κ W p)).trace.re := by
  have hε : 0 ≤ layerAbsorption W κ 1 0 := div_nonneg (hκ _) (sq_nonneg _)
  have hY0 : passiveY ((boundaryZ b E)⁻¹ • (p.2 0 * (p.2 0)ᴴ)) =
      ((etaZ b E / Complex.normSq (boundaryZ b E) : ℝ) : ℂ) • (p.2 0 * (p.2 0)ᴴ) := by
    rw [passiveY, matrixImaginaryPart_smul_hermitian _ _ (isHermitian_mul_conjTranspose_self _),
      Complex.inv_im, ← neg_smul]
    congr 1; push_cast; rw [etaZ]; ring
  have hc : 0 ≤ etaZ b E / Complex.normSq (boundaryZ b E) :=
    div_nonneg (boundaryZ_im_pos hb h1 h2).le (Complex.normSq_nonneg _)
  have hP0 : (passiveY ((boundaryZ b E)⁻¹ • (p.2 0 * (p.2 0)ᴴ))).PosSemidef := by
    rw [hY0]; exact (posSemidef_self_mul_conjTranspose _).smul (by exact_mod_cast hc)
  refine ⟨passiveY_absorb hP0 hε, ?_⟩
  rw [bondX, absorbedInput, passiveY_absorb_eq, trace_add, Complex.add_re, hY0, trace_smul,
    smul_eq_mul, Complex.re_ofReal_mul, trace_smul, trace_one, smul_eq_mul, Complex.re_ofReal_mul]
  have : 0 ≤ layerAbsorption W κ 1 0 * ((Fintype.card (Fin W) : ℂ)).re := by
    simp only [Complex.natCast_re]; positivity
  linarith

theorem norm_bondX_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) {κ : ℝ → ℝ}
    (hκ : ∀ s, 0 ≤ κ s) {Kκ Li : ℝ} (hK : ∀ s, κ s ≤ Kκ) (hLi : (etaZ b E)⁻¹ ≤ Li)
    (hW : 1 ≤ W) (p : PastSample W 0) :
    ‖bondX b E κ W p‖ ≤ ‖p.2 0‖ ^ 2 * Li + Kκ := by
  have hη := boundaryZ_im_pos hb h1 h2
  have hz : ‖(boundaryZ b E)⁻¹‖ ≤ Li := by
    rw [norm_inv]
    exact (inv_anti₀ hη (Complex.im_le_norm _)).trans hLi
  have hε : layerAbsorption W κ 1 0 ≤ Kκ := by
    rw [layerAbsorption]
    have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hW)
    exact (div_le_self (hκ _) hW1).trans (hK _)
  have hε0 : 0 ≤ layerAbsorption W κ 1 0 := div_nonneg (hκ _) (sq_nonneg _)
  rw [bondX, absorbedInput]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    calc ‖(boundaryZ b E)⁻¹‖ * ‖p.2 0 * (p.2 0)ᴴ‖ ≤ Li * ‖p.2 0‖ ^ 2 := by
          refine mul_le_mul hz ?_ (norm_nonneg _) ((norm_nonneg _).trans hz)
          rw [sq]; exact (norm_mul_le _ _).trans (by rw [l2_opNorm_conjTranspose])
      _ = _ := by ring
  · rw [norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hε0]
    exact mul_le_of_le_one_right hε0 PassiveLayer.norm_one_le' |>.trans hε

end BlockBand.Transmission.LawFinite
