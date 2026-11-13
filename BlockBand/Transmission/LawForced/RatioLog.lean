module

public import BlockBand.Transmission.LawForced.DualEigen
public import BlockBand.Transmission.LawForced.LogDetExpand
public import BlockBand.Transmission.Generator.StepExact
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# `log F_z` as a sum of log-determinants, and the exact fresh-layer transfer

Write `ℓ_w(M) = log Re det(I + wM)` (`ellW`) and
`logRatio z M = Σ_i (ℓ_{−y_i}(M) − ℓ_{x_i}(M))`.
* **`transmissionRatio_traceMeasure_exp`**: for `0 ⪯ M ⪯ I` and `x ≥ 0`, `0 ≤ y < 1`,
  `F_{x,y}(traceMeasure M) = exp(logRatio (x,y) M)`;
* `logRatio_eq_sum`: `logRatio z M = Σ_i Σ_k [log(1 − y_iλ_k) − log(1 + x_iλ_k)]`;
* `ellW_conjTranspose_mul` (Sylvester): `ℓ_w(G*G) = ℓ_w(GG*)`;
* `one_sub_posSemidef_of_norm_le`: Hermitian `‖S‖ ≤ 1` gives `I − S ⪰ 0`;
* **`ae_fresh_ratio`**: one fresh layer at a passive `X`, `S = sand T (LL*)`: a.s. `0 ⪯ S ⪯ I`
  and `ℓ_w(T(X₊)) = ℓ_w(S)` for every `w` (the `F_z` analogue of `ae_trace_pow_fresh`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open MeasureTheory Filter Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `ℓ_w(M) = log Re det(I + wM)`. -/
def ellW (w : ℝ) (M : Matrix n n ℂ) : ℝ := Real.log (1 + (w : ℂ) • M).det.re

/-- `log F_z(M) = Σ_i (ℓ_{−y_i}(M) − ℓ_{x_i}(M))`. -/
def logRatio {p : ℕ} (z : DualCoord p) (M : Matrix n n ℂ) : ℝ :=
  ∑ i, (ellW (-z.2 i) M - ellW (z.1 i) M)

theorem mul_ratioIntegrand {p : ℕ} (x y : Fin p → ℝ) (t : ℝ) :
    t * ratioIntegrand x y t = ∑ i, (Real.log (1 - y i * t) - Real.log (1 + x i * t)) := by
  unfold ratioIntegrand
  split_ifs with h
  · subst h; simp
  · field_simp

/-- `ℓ_w(M) = Σ_k log(1 + wλ_k)` when every `1 + wλ_k > 0`. -/
theorem ellW_eq_sum {M : Matrix n n ℂ} (hM : M.IsHermitian) {w : ℝ}
    (hpos : ∀ k, 0 < 1 + w * hM.eigenvalues k) :
    ellW w M = ∑ k, Real.log (1 + w * hM.eigenvalues k) :=
  (sum_log_eq_log_det hM w hpos).symm

theorem pos_x {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) : 0 < 1 + x * t := by
  have := mul_nonneg hx ht; linarith

theorem pos_y {y t : ℝ} (hy : y < 1) (hy0 : 0 ≤ y) (ht : t ≤ 1) :
    0 < 1 + -y * t := by
  have : y * t ≤ y := by nlinarith
  linarith

/-- `logRatio` in eigenvalues. -/
theorem logRatio_eq_sum {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y) {M : Matrix n n ℂ}
    (h0 : M.PosSemidef) (h1 : (1 - M).PosSemidef) :
    logRatio (x, y) M = ∑ i, ∑ k, (Real.log (1 - y i * h0.1.eigenvalues k) -
      Real.log (1 + x i * h0.1.eigenvalues k)) := by
  unfold logRatio
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm := eigenvalues_mem h0 h1
  rw [ellW_eq_sum h0.1 fun k => pos_y (h.2 i).2 (h.2 i).1 (hm k).2,
    ellW_eq_sum h0.1 fun k => pos_x (h.1 i) (hm k).1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [neg_mul, ← sub_eq_add_neg]

/-- **`F_{x,y}(traceMeasure M) = exp(logRatio (x,y) M)`** for `0 ⪯ M ⪯ I`. -/
theorem transmissionRatio_traceMeasure_exp {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    {M : Matrix n n ℂ} (h0 : M.PosSemidef) (h1 : (1 - M).PosSemidef) :
    transmissionRatio x y (traceMeasure M) = Real.exp (logRatio (x, y) M) := by
  unfold transmissionRatio
  congr 1
  rw [integral_traceMeasure_eq h0 h1 (continuous_ratioIntegrand h), logRatio_eq_sum h h0 h1,
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => mul_ratioIntegrand x y _

/-- Sylvester: `ℓ_w(G*G) = ℓ_w(GG*)`. -/
theorem ellW_conjTranspose_mul (w : ℝ) (G : Matrix n n ℂ) :
    ellW w (Gᴴ * G) = ellW w (G * Gᴴ) := by
  unfold ellW
  rw [← Matrix.smul_mul, det_one_add_mul_comm, Matrix.mul_smul]

theorem logRatio_conjTranspose_mul {p : ℕ} (z : DualCoord p) (G : Matrix n n ℂ) :
    logRatio z (Gᴴ * G) = logRatio z (G * Gᴴ) := by
  unfold logRatio; simp only [ellW_conjTranspose_mul]

/-- A Hermitian contraction `S` has `I − S ⪰ 0`. -/
theorem one_sub_posSemidef_of_norm_le {S : Matrix n n ℂ} (hS : S.IsHermitian) (h : ‖S‖ ≤ 1) :
    (1 - S).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_one.sub hS, fun x => ?_⟩
  have hq : star x ⬝ᵥ (S *ᵥ x) = (((star x ⬝ᵥ (S *ᵥ x)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact hS.im_star_dotProduct_mulVec_self x
  have hle : (star x ⬝ᵥ (S *ᵥ x)).re ≤ vecNorm x ^ 2 := by
    refine (Complex.re_le_norm _).trans ((norm_star_dotProduct_le _ _).trans ?_)
    have h1 := vecNorm_mulVec_le S x
    have h2 := vecNorm_nonneg x
    nlinarith [mul_le_mul_of_nonneg_right h h2]
  rw [sub_mulVec, one_mulVec, dotProduct_sub, star_self_eq, hq, ← Complex.ofReal_sub]
  exact_mod_cast sub_nonneg.2 hle

end General

section Fresh

variable {W : ℕ}

/-- **The exact fresh-layer transfer for `F_z`.** -/
theorem ae_fresh_ratio {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) {E : ℝ}
    (h1 : -2 < E) (h2 : E < 2) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, (sand hT (freshU b E X ω)).PosSemidef ∧
      (1 - sand hT (freshU b E X ω)).PosSemidef ∧
      ∀ w : ℝ, ellW w (passiveTransmission b E (freshSchur E X ω)) =
        ellW w (sand hT (freshU b E X ω)) := by
  filter_upwards [ae_transmission_fresh hb0 hb hW h1 h2 hY,
    ae_norm_sand_freshU_le hb0 hb hW h1 h2 hY hT] with ω h hn
  obtain ⟨e1, e2⟩ := sand_freshU_eq hT (freshL b E X ω)
  have hS : sand hT (freshU b E X ω) = _ := e1
  have hP : (sand hT (freshU b E X ω)).PosSemidef := by
    rw [hS]; exact posSemidef_self_mul_conjTranspose _
  refine ⟨hP, one_sub_posSemidef_of_norm_le hP.1 hn, fun w => ?_⟩
  rw [h, ← e2, hS, ellW_conjTranspose_mul]

end Fresh

end BlockBand.Transmission.LawForced
