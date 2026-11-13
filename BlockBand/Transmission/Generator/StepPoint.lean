module

public import BlockBand.Transmission.Generator.StepErr
public import BlockBand.Transmission.Generator.MeanPassive
public import BlockBand.Transmission.Generator.DriftOneBound

/-!
# The `k = j + 2` one-layer drift at a deterministic passive input (all inputs explicit)

This module provides the algebraic pieces (`lp_quad`, `lp_wm`, `lp_scal`) of the one-layer drift
bound **`layer_point`**, proved in the sibling module: for a passive `X`, `T = T(X)`, `g = Tr T`,
`τ = |Tr(Tf)| + √g·hs(T,f)`, given the HS moments (`H₂ = (C_bg/√W)²`, `H₃ = (C_bg/√W)³`), the
covariance bound with error `ε`, `‖Ū - c‖ ≤ U_a` and the weighted mean with constant `C_u`:
`|E Re Tr T(X₊)^k - Re Tr T^k - A_k(P)/W| ≤ E₁ + E₂ + E₃ + kE₄ + E₅` (explicit), with `A_k` at
`D₀(E)`, `P_m = Re Tr T^m`.
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

theorem trace_pow_eq_powSums {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (m : ℕ) :
    (T ^ m).trace.re = powSums (ts_lam hT) m := by
  have h := trace_pow_sand hT 1 m
  rw [Matrix.mul_one, sand_one, trace_diag_pow] at h
  rw [h, Complex.re_sum, powSums]
  exact Finset.sum_congr rfl fun i _ => by rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem powSums_le {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) : 0 ≤ powSums (ts_lam hT) m ∧ powSums (ts_lam hT) m ≤ T.trace.re := by
  rw [← ts_sum_lam hT]
  exact ⟨Finset.sum_nonneg fun i _ => pow_nonneg (ts_lam_nonneg hT i) m,
    Finset.sum_le_sum fun i _ => pow_le_of_le_one (ts_lam_nonneg hT i) (ht1 i) (by omega)⟩

theorem sum_w_le {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (j : ℕ) : ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m) ≤
      ((j + 1 : ℕ) : ℝ) ^ 2 * T.trace.re ^ 2 := by
  rw [← ts_sum_lam hT, sq (∑ i, ts_lam hT i), Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have := wsum_le j (ts_lam_nonneg hT i) (ht1 i) (ts_lam_nonneg hT m) (ht1 m)
  have h0 : 0 ≤ ts_lam hT i * ts_lam hT m := mul_nonneg (ts_lam_nonneg hT i) (ts_lam_nonneg hT m)
  nlinarith

theorem meanC_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (X : Matrix (Fin W) (Fin W) ℂ) :
    meanC b E X = (1 + transportD0 b E * (passiveTransmission b E X).trace.re / (2 * W))⁻¹ := by
  rw [meanC, alphaCoef_eq hb0 (by linarith) h1 h2]
  congr 1
  rw [passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul, passiveMass]
  ring

/-- Piece (1): the quadratic expansion with `‖S̄ - D'‖ ≤ U_a` and `Σw ≤ (j+1)²g²`. -/
theorem lp_quad {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1)
    (hUi : ∀ i j, Integrable (fun ω => freshU b E X ω i j) (freshLaw W b))
    (hU2 : Integrable (fun ω => ‖freshU b E X ω‖ ^ 2) (freshLaw W b)) {H₂ H₃ : ℝ}
    (hI2 : Integrable (fun ω => frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b))
    (hm2 : ∫ ω, frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ H₂)
    (hI3 : Integrable (fun ω => ‖sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X))‖ * frobSq (sand hT (freshU b E X ω -
          matrixExpect (freshLaw W b) (freshU b E X)))) (freshLaw W b))
    (hm3 : ∫ ω, ‖sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X))‖ *
          frobSq (sand hT (freshU b E X ω - matrixExpect (freshLaw W b) (freshU b E X)))
          ∂freshLaw W b ≤ H₃) (hH2 : 0 ≤ H₂)
    (a σ σ' : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hcov : ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ, ‖bilinearCovariance (freshLaw W b) (freshU b E X)
        v₁ v₂ v₃ v₄ - (a * (crossedTensor v₁ v₂ v₃ v₄ 1 (1 - passiveTransmission b E X) +
            crossedTensor v₁ v₂ v₃ v₄ (1 - passiveTransmission b E X) 1) +
          σ * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X) (passiveF b E X) +
          σ' * crossedTensor v₁ v₂ v₃ v₄ (passiveF b E X)ᴴ (passiveF b E X)ᴴ)‖ ≤
        ε * fourNorm v₁ v₂ v₃ v₄)
    {Ua : ℝ} (hUa : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      ((meanC b E X : ℝ) : ℂ) • 1‖ ≤ Ua) (j : ℕ) :
    |∫ ω, ((sand hT (freshU b E X ω)) ^ (j + 2)).trace.re ∂freshLaw W b -
        ((sand hT (matrixExpect (freshLaw W b) (freshU b E X))) ^ (j + 2)).trace.re -
        (∑ i, ∑ m, ((meanC b E X ^ j : ℝ) : ℂ) * (((ts_lam hT i * ts_lam hT m *
          wsum j (ts_lam hT i) (ts_lam hT m) : ℝ) : ℂ) *
          (a * ((2 - ts_lam hT i - ts_lam hT m : ℝ) : ℂ) +
            σ * (ts_ent hT (passiveF b E X) i i * ts_ent hT (passiveF b E X) m m) +
            σ' * (conj (ts_ent hT (passiveF b E X) i i) *
              conj (ts_ent hT (passiveF b E X) m m))))).re| ≤
      ((j + 1 + 1 : ℕ) : ℝ) ^ 3 * (3 * 2) ^ (2 * (j + 1 + 1)) * H₃ +
        ((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) * (3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1)) *
          Ua)) * H₂ + ε * (((j + 1 : ℕ) : ℝ) ^ 2 * (passiveTransmission b E X).trace.re ^ 2) := by
  set c := meanC b E X
  obtain ⟨hc0, hc1⟩ := meanC_pos_le hb0 hb h1 h2 hX
  have hS := ae_norm_sand_freshU_le hb0 hb hW1 h1 h2 hX hT
  have hSb := norm_sand_matrixExpect_le hT _ (measurable_freshU b E X) hUi hS
  have hp := freshU_hp hT _ (measurable_freshU b E X) hU2
  have hQ := step_quad hT ht1 _ (measurable_freshU b E X) hUi hp hS hSb hI2 hm2 hI3 hm3 hc0.le hc1
    (passiveF b E X) a σ σ' hcov j
  have hSD : ‖sand hT (matrixExpect (freshLaw W b) (freshU b E X)) -
      diagonal (fun i => ((c * ts_lam hT i : ℝ) : ℂ))‖ ≤ Ua := by
    rw [← sand_smul_one, ← sand_sub]; exact (norm_sand_le hT ht1 _).trans hUa
  have hwsum := sum_w_le hT ht1 j
  have hcj : |c| ^ j ≤ 1 := by rw [abs_of_pos hc0]; exact pow_le_one₀ hc0.le hc1
  have h0 : 0 ≤ ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg
      (ts_lam_nonneg hT i) (ts_lam_nonneg hT m)) (wsum_nonneg j (ts_lam_nonneg hT i)
      (ts_lam_nonneg hT m))
  have hE1 : |c| ^ j * ε * ∑ i, ∑ m, ts_lam hT i * ts_lam hT m * wsum j (ts_lam hT i) (ts_lam hT m)
      ≤ ε * (((j + 1 : ℕ) : ℝ) ^ 2 * (passiveTransmission b E X).trace.re ^ 2) := by
    calc |c| ^ j * ε * _ ≤ 1 * ε * (((j + 1 : ℕ) : ℝ) ^ 2 *
          (passiveTransmission b E X).trace.re ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcj hε) hwsum h0 (by positivity)
      _ = _ := by ring
  have hK2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hSD (by positivity : (0 : ℝ) ≤ 3 * (j + 1 : ℕ) * 2 ^ (3 * (j + 1))))
    (by positivity : (0 : ℝ) ≤ ((j + 1 + 1 : ℕ) : ℝ))) (by positivity : (0 : ℝ) ≤
      ((j + 1 + 1 : ℕ) : ℝ))) hH2
  linarith

/-- Piece (4): the weighted mean at `G = gPow T k`. -/
theorem lp_wm {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef)
    (hT : (passiveTransmission b E X).PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {Cu : ℝ}
    (hwm : ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
      ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
        ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ Cu * wmErr b E X G) (j : ℕ) :
    |(gPow hT (j + 2) * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
        meanC b E X * ∑ i, ts_lam hT i ^ (j + 2)| ≤
      max Cu 0 * ((jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * (‖(passiveTransmission b E X *
        passiveF b E X).trace‖ + Real.sqrt (passiveTransmission b E X).trace.re *
          hsSandwich (passiveTransmission b E X) (passiveF b E X)) +
        (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 2 * (passiveTransmission b E X).trace.re +
        (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X *
          (passiveTransmission b E X).trace.re / W +
        (W : ℝ)⁻¹ ^ 2 * (passiveTransmission b E X).trace.re) := by
  have hGk := gPow_posSemidef hT (j + 2)
  have hGtr := trace_gPow hT (j + 2)
  have hτk : ‖(gPow hT (j + 2) * passiveF b E X).trace‖ ≤ ‖(passiveTransmission b E X *
      passiveF b E X).trace‖ + Real.sqrt (passiveTransmission b E X).trace.re *
        hsSandwich (passiveTransmission b E X) (passiveF b E X) := by
    rw [trace_gPow_mul]; exact norm_sum_pow_fd_le hT ht1 _ (by omega)
  have hPk := powSums_le hT ht1 (m := j + 2) (by omega)
  have hre : (gPow hT (j + 2) * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
      meanC b E X * ∑ i, ts_lam hT i ^ (j + 2) =
      ((gPow hT (j + 2) * matrixExpect (freshLaw W b) (freshU b E X)).trace -
        ((meanC b E X : ℝ) : ℂ) * (gPow hT (j + 2)).trace).re := by
    rw [Complex.sub_re, Complex.re_ofReal_mul, hGtr]
  rw [hre]
  have he0 : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 :=
    add_nonneg (norm_nonneg _) (sq_nonneg _)
  have hq := passiveMass_nonneg b E hX
  have hg := (mm_trace_posSemidef hGk).1
  have hw0 : 0 ≤ wmErr b E X (gPow hT (j + 2)) := by
    unfold wmErr
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg he0 (norm_nonneg _))
      (mul_nonneg (sq_nonneg _) hg)) (div_nonneg (mul_nonneg (mul_nonneg he0 hq) hg)
      (Nat.cast_nonneg _))) (mul_nonneg (sq_nonneg _) hg)
  refine (Complex.abs_re_le_norm _).trans ((hwm _ hGk).trans ?_)
  refine (mul_le_mul_of_nonneg_right (le_max_left Cu 0) hw0).trans
    (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  have hGg : (gPow hT (j + 2)).trace.re ≤ (passiveTransmission b E X).trace.re := by
    rw [hGtr]; exact hPk.2
  unfold wmErr
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  refine add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hτk he0)
    (mul_le_mul_of_nonneg_left hGg (sq_nonneg _))) (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hGg (mul_nonneg he0 hq)) hW0))
    (mul_le_mul_of_nonneg_left hGg (sq_nonneg _))

/-- Piece (5): the scalar expansion with `c = meanC`. -/
theorem lp_scal {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ}
    (hT : (passiveTransmission b E X).PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) (j : ℕ) :
    |meanC b E X ^ (j + 2) * powSums (ts_lam hT) (j + 2) + meanC b E X ^ j *
        (transmissionDrift (transportD0 b E) (j + 2) (powSums (ts_lam hT)) +
          transportD0 b E * ((j + 2 : ℕ) : ℝ) / 2 * powSums (ts_lam hT) 1 *
            powSums (ts_lam hT) (j + 2)) / W -
        powSums (ts_lam hT) (j + 2) -
        transmissionDrift (transportD0 b E) (j + 2) (powSums (ts_lam hT)) / W| ≤
      ((j + 2 : ℕ) : ℝ) ^ 2 * (transportD0 b E * (passiveTransmission b E X).trace.re /
          (2 * W)) ^ 2 * (passiveTransmission b E X).trace.re +
        j * (transportD0 b E * (passiveTransmission b E X).trace.re / (2 * W)) *
          (transportD0 b E * ((j + 2 : ℕ) : ℝ) ^ 2 * (passiveTransmission b E X).trace.re ^ 2) /
          W := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  set g := (passiveTransmission b E X).trace.re
  set D := transportD0 b E
  have hg0 : 0 ≤ g := (mm_trace_posSemidef hT).1
  have hD0 : 0 ≤ D := by
    have : 0 < 4 - E ^ 2 := by nlinarith
    simp only [D, transportD0]; positivity
  have hy0 : 0 ≤ D * g / (2 * W) := by positivity
  have hP1 : powSums (ts_lam hT) 1 = g := by rw [← trace_pow_eq_powSums hT 1, pow_one]
  have hcy : meanC b E X = (1 + D * g / (2 * W))⁻¹ := meanC_eq hb0 hb h1 h2 X
  rw [hcy, mul_assoc D, mul_div_assoc]
  have hsc := step_scalar (D := D) (W' := W) (Pk := powSums (ts_lam hT) (j + 2))
    (P1 := powSums (ts_lam hT) 1) (A := transmissionDrift D (j + 2) (powSums (ts_lam hT)))
    hWpos (by rw [hP1]) hy0 j
  have hPk := powSums_le hT ht1 (m := j + 2) (by omega)
  have hA : |transmissionDrift D (j + 2) (powSums (ts_lam hT))| ≤
      D * ((j + 2 : ℕ) : ℝ) ^ 2 * g ^ 2 :=
    abs_transmissionDrift_le hD0 (j + 2) fun m hm _ => by
      rw [abs_of_nonneg (powSums_le hT ht1 hm).1]; exact (powSums_le hT ht1 hm).2
  rw [abs_of_nonneg hPk.1] at hsc
  refine (le_of_eq_of_le ?_ hsc).trans ?_
  · congr 2; ring
  · gcongr
    all_goals first | exact hPk.2 | exact hPk.1 | exact hA | exact hA.trans (le_of_eq (by ring)) | exact le_of_eq (by ring)

end BlockBand.Transmission.Generator
