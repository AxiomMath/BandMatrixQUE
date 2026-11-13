module

public import BlockBand.Layers.FullEnergyPath

/-!
# The full-energy trace bound: the final residual pair layer (`FetResidualBound`)

The last step of the proof of the tagged-trace lemma: "The final residual pair has a fixed
stability gap ... The final energy derivative gives the full-energy trace bound".

Law: the residual pair layer `rpLaw W b s`, realized as the image of the real white noise
`gaussianProduct (rlVar W b s)` under `rlEmbed` (`rl_law_eq_map`). The old (exterior) data `X`
(Hermitian) and `S ⪰ 0` are deterministic. `G = (V - E - X - sa)⁻¹` (`rlG`), `‖G‖ ≤ (s y)⁻¹`
deterministically, `Y = (1 + s a') + S`, `h_k = W⁻¹ Tr P_k G Y G` (so `ρ'_k = h_k - a'`).

## Method (no operator-norm moments of `V` are used)

* **S-sandwich toolkit** (§1): for `S = B*B`, `|Tr(S A Z C)| ≤ ‖Z‖ √Tr(A*SA) √Tr(CSC*)`;
  resolvents of `Hermitian - c` are normal.
* **Ward identity** (§2): `Tr(G* S G) = Im Tr(S G) / Im c` for `G = (H - c)⁻¹`; hence the residual
  clock `u_G = W⁻¹ Tr G*SG` is a linear statistic of `G`.
* **Clock moments** (§4): `E u_G ≤ C u` from the matrix mean identity
  `(C₀ - diag φ(m̄)) E G = 1 + E[diag φ(g - m̄) G]`, and `‖u_G‖_p ≤ 2 E u_G` from the Gaussian
  `L^p` gradient inequality (`|∇ u_G| ≤ √(6/W) u_G`).
* **Derivative mean equation** (§5): Gaussian integration by parts for `G Y G` gives
  `(C₀ - diag φ(m̄)) E[GYG] = Y E G + E[diag φ(g - m̄) GYG] + E[diag φ(h) G]`, whose block traces
  are the linear system `v = d + Q φ(v) + err` (`v = E h - a'`, `d = f' - a'`) with constant
  forcing `1 + z_∂' + (1-b)a' = 0` and contraction `(1 - b - s) Σ|Q| < 1`.
* **Noise** (§6): `‖h - E h‖_p ≤ C(1/W + ‖u_G‖_p/√W)`.
* **Assembly** (§11–§12): the scalar bookkeeping `fetT_err_scalar`, `fetT_noise_scalar`; the
  moment bounds at one exterior input `fetT_resid_crude`, `fetT_resid_inst`; the contraction
  `θ = 1 - s/(2(1-b))` from `rowSum` (`fetT_q_le`); the mean-field shift
  `‖Δ‖ ≤ 2 max(C_R, 0)(δ + 1/√W)` from `residualPairLayerBound_holds` (`fetT_Delta_le`).

## Result

`fetResidualBound_holds (hcount) (hgrad) : FetResidualBound` (both clauses: crude for every `X`,
fine on `δ ≤ d_*`), from `GaussianLpGradient`, `residualPairLayerBound_holds` (which uses
`ConditionalBlockGUECount`) and `strictContraction_holds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The S-sandwich toolkit
-/

section Toolkit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted trace `Re Tr(A* S A)`. -/
def fetTct (S A : Matrix n n ℂ) : ℝ := (Aᴴ * S * A).trace.re

theorem fetT_hs_eq (M : Matrix n n ℂ) : wlHS M = dcvHS M := rfl

theorem fetTct_eq_hs {S B : Matrix n n ℂ} (hSB : S = Bᴴ * B) (A : Matrix n n ℂ) :
    fetTct S A = dcvHS (B * A) := by
  unfold fetTct
  rw [hSB, show Aᴴ * (Bᴴ * B) * A = (B * A)ᴴ * (B * A) by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc], dcv_trace_conjTranspose_mul_self,
    Complex.ofReal_re]

theorem fetTct_nonneg {S : Matrix n n ℂ} (hS : S.PosSemidef) (A : Matrix n n ℂ) :
    0 ≤ fetTct S A := by
  obtain ⟨B, hB⟩ := dcv_psd_eq hS
  rw [fetTct_eq_hs hB]; exact dcvHS_nonneg _

/-- `Re Tr(C S C*) = ‖B C*‖²_HS` for `S = B*B`. -/
theorem fetT_ctr_eq_hs {S B : Matrix n n ℂ} (hSB : S = Bᴴ * B) (C : Matrix n n ℂ) :
    (C * S * Cᴴ).trace.re = dcvHS (B * Cᴴ) := by
  rw [← fetTct_eq_hs hSB, fetTct, conjTranspose_conjTranspose]

/-- **S-sandwich**: `|Tr(S A Z C)| ≤ ‖Z‖ √Re Tr(A*SA) √Re Tr(CSC*)` for `S ⪰ 0`. -/
theorem fetT_sandwich {S : Matrix n n ℂ} (hS : S.PosSemidef) (A Z C : Matrix n n ℂ) :
    ‖(S * A * Z * C).trace‖ ≤
      ‖Z‖ * Real.sqrt (fetTct S A) * Real.sqrt ((C * S * Cᴴ).trace.re) := by
  obtain ⟨B, hB⟩ := dcv_psd_eq hS
  have e : (S * A * Z * C).trace = ((B * A) * (Z * (C * Bᴴ))).trace := by
    rw [hB]
    rw [show Bᴴ * B * A * Z * C = Bᴴ * (B * A * Z * C) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (wl_norm_trace_mul_le _ _).trans ?_
  rw [fetT_hs_eq, fetT_hs_eq, fetTct_eq_hs hB, fetT_ctr_eq_hs hB]
  have h1 := dcvHS_mul_left_le Z (C * Bᴴ)
  have hCB : dcvHS (C * Bᴴ) = dcvHS (B * Cᴴ) := by
    rw [← dcvHS_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hCB] at h1
  have h2 : Real.sqrt (dcvHS (Z * (C * Bᴴ))) ≤ ‖Z‖ * Real.sqrt (dcvHS (B * Cᴴ)) := by
    rw [← Real.sqrt_sq (norm_nonneg Z), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h1
  calc Real.sqrt (dcvHS (B * A)) * Real.sqrt (dcvHS (Z * (C * Bᴴ)))
      ≤ Real.sqrt (dcvHS (B * A)) * (‖Z‖ * Real.sqrt (dcvHS (B * Cᴴ))) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- `Re Tr((AU)* S (AU)) ≤ ‖U‖² Re Tr(A* S A)`. -/
theorem fetTct_mul_right_le {S : Matrix n n ℂ} (hS : S.PosSemidef) (A U : Matrix n n ℂ) :
    fetTct S (A * U) ≤ ‖U‖ ^ 2 * fetTct S A := by
  obtain ⟨B, hB⟩ := dcv_psd_eq hS
  rw [fetTct_eq_hs hB, fetTct_eq_hs hB, ← Matrix.mul_assoc]
  have := dcvHS_mul_right_le (B * A) U
  linarith

/-- `Re Tr((UC) S (UC)*) ≤ ‖U‖² Re Tr(C S C*)`. -/
theorem fetT_ctr_mul_left_le {S : Matrix n n ℂ} (hS : S.PosSemidef) (U C : Matrix n n ℂ) :
    ((U * C) * S * (U * C)ᴴ).trace.re ≤ ‖U‖ ^ 2 * (C * S * Cᴴ).trace.re := by
  obtain ⟨B, hB⟩ := dcv_psd_eq hS
  rw [fetT_ctr_eq_hs hB, fetT_ctr_eq_hs hB, conjTranspose_mul, ← Matrix.mul_assoc]
  have := dcvHS_mul_right_le (B * Cᴴ) Uᴴ
  rw [l2_opNorm_conjTranspose] at this
  linarith

/-- The inverse of `H - c` (`H` Hermitian, `c` scalar) is normal. -/
theorem fetT_normal {H : Matrix n n ℂ} (hH : H.IsHermitian) (c : ℂ) :
    ((H - diagonal fun _ => c)⁻¹)ᴴ * (H - diagonal fun _ => c)⁻¹ =
      (H - diagonal fun _ => c)⁻¹ * ((H - diagonal fun _ => c)⁻¹)ᴴ := by
  set N := H - diagonal fun _ : n => c with hN
  have hNh : Nᴴ = H - diagonal fun _ => conj c := by
    rw [hN, conjTranspose_sub, hH.eq, diagonal_conjTranspose]; rfl
  have hc : N * Nᴴ = Nᴴ * N := by
    rw [hNh, hN, ← smul_one_eq_diagonal, ← smul_one_eq_diagonal]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_sub, smul_smul]
    rw [mul_comm ((starRingEnd ℂ) c) c]
    abel
  rw [conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hc]

/-- For a normal `C`, `Re Tr(C S C*) = Re Tr(C* S C)`. -/
theorem fetT_ctr_normal {S C : Matrix n n ℂ} (hC : Cᴴ * C = C * Cᴴ) :
    (C * S * Cᴴ).trace.re = fetTct S C := by
  unfold fetTct
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hC,
    show Cᴴ * S * C = Cᴴ * (S * C) from Matrix.mul_assoc _ _ _, Matrix.trace_mul_comm Cᴴ,
    Matrix.mul_assoc]

/-- **Normal sandwich**: `|Tr(S A Z C)| ≤ ‖Z‖ √ct(A) √ct(C)` for normal `C`. -/
theorem fetT_sandwich_normal {S : Matrix n n ℂ} (hS : S.PosSemidef) (A Z C : Matrix n n ℂ)
    (hC : Cᴴ * C = C * Cᴴ) :
    ‖(S * A * Z * C).trace‖ ≤ ‖Z‖ * Real.sqrt (fetTct S A) * Real.sqrt (fetTct S C) := by
  have h := fetT_sandwich hS A Z C
  rwa [fetT_ctr_normal hC] at h

/-- **Ward identity**: for `M = (H - c)⁻¹` (`H` Hermitian, `Im c ≠ 0`, `H - c` invertible) and `S`
Hermitian, `Re Tr(M* S M) = Im Tr(S M) / Im c`. -/
theorem fetT_ward {H : Matrix n n ℂ} (hH : H.IsHermitian) {c : ℂ} (hc : c.im ≠ 0)
    (hU : IsUnit (H - diagonal fun _ => c).det) {S : Matrix n n ℂ} (hS : S.IsHermitian) :
    fetTct S (H - diagonal fun _ => c)⁻¹ = (S * (H - diagonal fun _ => c)⁻¹).trace.im / c.im := by
  set N := H - diagonal fun _ : n => c with hN
  set M := N⁻¹ with hM
  have hNh : Nᴴ = H - diagonal fun _ => conj c := by
    rw [hN, conjTranspose_sub, hH.eq, diagonal_conjTranspose]; rfl
  have hMN : M * N = 1 := nonsing_inv_mul _ hU
  have hNM : N * M = 1 := mul_nonsing_inv _ hU
  have hNMh : Nᴴ * Mᴴ = 1 := by rw [← conjTranspose_mul, hMN, conjTranspose_one]
  have hdiff : Nᴴ - N = (c - conj c) • (1 : Matrix n n ℂ) := by
    rw [hNh, hN, sub_smul, smul_one_eq_diagonal, smul_one_eq_diagonal]; abel
  have hW : M - Mᴴ = (c - conj c) • (M * Mᴴ) := by
    have e1 : M * (Nᴴ - N) * Mᴴ = M - Mᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc M Nᴴ, hNMh, Matrix.mul_one, hMN,
        Matrix.one_mul]
    rw [← e1, hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have htr : (S * M).trace - (S * Mᴴ).trace = (c - conj c) * (S * (M * Mᴴ)).trace := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, hW, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have hconj : (S * Mᴴ).trace = conj (S * M).trace := by
    rw [show S * Mᴴ = (M * S)ᴴ by rw [conjTranspose_mul, hS.eq], trace_conjTranspose,
      Matrix.trace_mul_comm M S]; rfl
  rw [hconj, Complex.sub_conj, Complex.sub_conj] at htr
  have hT : (Mᴴ * S * M).trace = (S * (M * Mᴴ)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  unfold fetTct
  rw [hT]
  set T := (S * (M * Mᴴ)).trace
  set z := (S * M).trace
  have hc' : ((2 * c.im : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast mul_ne_zero two_ne_zero hc) Complex.I_ne_zero
  have hTe : T = ((z.im / c.im : ℝ) : ℂ) := by
    have : T = ((2 * z.im : ℝ) : ℂ) * Complex.I / (((2 * c.im : ℝ) : ℂ) * Complex.I) := by
      rw [eq_div_iff hc', htr]; ring
    rw [this]
    have hci : (c.im : ℂ) ≠ 0 := by exact_mod_cast hc
    field_simp
    push_cast
    field_simp
  rw [hTe, Complex.ofReal_re]

end Toolkit

/-!
## 2. Gaussian integration by parts for a smooth bounded matrix function
-/

section IBP

variable {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) {n : Type} [Fintype n] [DecidableEq n]
  (L : (ι → ℝ) →L[ℝ] Matrix n n ℂ)

/-- **Gaussian integration by parts**: `E[L(x) F(x)] = Σᵢ vᵢ E[Λᵢ ∂ᵢF(x)]` for a `C¹` matrix
function `F` that is bounded with bounded derivative. -/
theorem fetT_ibp {F : (ι → ℝ) → Matrix n n ℂ} (hF : ContDiff ℝ 1 F) {C C' : ℝ}
    (hFC : ∀ x, ‖F x‖ ≤ C) (hF'C : ∀ x, ‖fderiv ℝ F x‖ ≤ C') :
    ∫ x, L x * F x ∂gaussianProduct v =
      ∑ i, (v i : ℝ) • ∫ x, L (Pi.single i 1) * fderiv ℝ F x (Pi.single i 1) ∂gaussianProduct v := by
  set μ := gaussianProduct v
  have hFc : Continuous F := hF.continuous
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hFC 0)
  have hdec : ∀ x, L x * F x = ∑ i, x i • (L (Pi.single i 1) * F x) := by
    intro x
    rw [core_lin_decomp x, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  have hint : ∀ i : ι, Integrable (fun x => x i • (L (Pi.single i 1) * F x)) μ := by
    intro i
    refine ou_integrable_of_norm_le μ
      ((continuous_apply i).smul (continuous_const.mul hFc)).aestronglyMeasurable 0
      (‖L (Pi.single i 1)‖ * C) fun x => ?_
    rw [norm_smul, zero_add]
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have h2 : ‖L (Pi.single i 1) * F x‖ ≤ ‖L (Pi.single i 1)‖ * C :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hFC x) (norm_nonneg _))
    calc ‖x i‖ * ‖L (Pi.single i 1) * F x‖
        ≤ ‖x‖ * (‖L (Pi.single i 1)‖ * C) := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = ‖L (Pi.single i 1)‖ * C * ‖x‖ := by ring
  rw [integral_congr_ae (ae_of_all _ hdec), integral_finsetSum _ fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  set Λ := L (Pi.single i 1)
  have hk : ContDiff ℝ 1 (fun x => Λ * F x) :=
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).contDiff.comp hF
  have hder : ∀ x, HasFDerivAt (fun x => Λ * F x)
      ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).comp (fderiv ℝ F x)) x :=
    fun x => ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) Λ).hasFDerivAt).comp x
      ((hF.differentiable one_ne_zero x).hasFDerivAt)
  have hb : ∀ x, ‖Λ * F x‖ ≤ ‖Λ‖ * C := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hFC x) (norm_nonneg _))
  have hC'0 : 0 ≤ C' := (norm_nonneg _).trans (hF'C 0)
  have hb' : ∀ x, ‖fderiv ℝ (fun x => Λ * F x) x‖ ≤ ‖Λ‖ * C' := by
    intro x
    rw [(hder x).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']
    calc ‖Λ * fderiv ℝ F x w‖ ≤ ‖Λ‖ * ‖fderiv ℝ F x w‖ := norm_mul_le _ _
      _ ≤ ‖Λ‖ * (C' * ‖w‖) := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hF'C x)
      _ = ‖Λ‖ * C' * ‖w‖ := by ring
  rw [ou_ibp v i hk hb hb']
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [(hder x).fderiv]
  rfl

end IBP

/-!
## 3. The residual pair resolvent in Gaussian coordinates
-/

section Coords

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

/-- The insertion `Y = 1 + S + s a'` of the energy derivative. -/
def fetTY (E s : ℝ) (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 + S + ((s : ℂ) * tgtAd E) • 1

/-- `h_k(x) = W⁻¹ Tr P_k G Y G` in coordinates. -/
def fetTh (b E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ)
    (k : Fin 2) : ℂ :=
  blockTrace (rlG b E s X x * fetTY E s S * rlG b E s X x) k

/-- The residual clock `u_G(x) = W⁻¹ Re Tr G* S G`. -/
def fetTu (b E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) : ℝ :=
  (W : ℝ)⁻¹ * fetTct S (rlG b E s X x)

theorem fetT_rho_embed (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ)
    (k : Fin 2) : fetRho E s X S (rlEmbed W b s x) k = fetTh b E s X S x k - tgtAd E := by
  unfold fetRho fetTh fetTY
  rw [← rl_matrix_eq]
  rfl

/-- `G` is the inverse of `Hermitian - sa`. -/
theorem fetT_G_eq_inv (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) :
    rlG b E s X x = (rlLin W b s x + cmpTopH E X - diagonal fun _ => (s : ℂ) * matchedA E)⁻¹ :=
  rlG_eq b E s X x

theorem fetT_G_normal (hX : X.IsHermitian) (x : RlCoord W → ℝ) :
    (rlG b E s X x)ᴴ * rlG b E s X x = rlG b E s X x * (rlG b E s X x)ᴴ := by
  rw [fetT_G_eq_inv]
  exact fetT_normal (rl_herm_part b E s hX x) _

theorem fetT_hasFDerivAt_G (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im)
    (x : RlCoord W → ℝ) :
    HasFDerivAt (rlG b E s X)
      ((-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        (rlG b E s X x) (rlG b E s X x))).comp (rlLin W b s)) x := by
  have hU : IsUnit (rlC0 E s X + rlLin W b s x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (rl_isUnit_G b E hs hX hya x)
  set u := hU.unit with hu
  have hL : HasFDerivAt (fun y => rlC0 E s X + rlLin W b s y) (rlLin W b s) x :=
    (rlLin W b s).hasFDerivAt.const_add _
  have h : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
        ↑u⁻¹ ↑u⁻¹)) (rlC0 E s X + rlLin W b s x) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) u
    rwa [IsUnit.unit_spec] at this
  have hinv : (↑u⁻¹ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = rlG b E s X x := by
    rw [rlG, Matrix.nonsing_inv_eq_ringInverse, ← Ring.inverse_unit, IsUnit.unit_spec]
  rw [hinv] at h
  refine (h.comp x hL).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  show rlG b E s X y = Ring.inverse (rlC0 E s X + rlLin W b s y)
  rw [rlG, Matrix.nonsing_inv_eq_ringInverse]

theorem fetT_contDiff_G (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im) :
    ContDiff ℝ 1 (rlG b E s X) := by
  have hL : ContDiff ℝ 1 (fun y => rlC0 E s X + rlLin W b s y) :=
    contDiff_const.add (rlLin W b s).contDiff
  have he : rlG b E s X = fun y => Ring.inverse (rlC0 E s X + rlLin W b s y) := by
    funext y; rw [rlG, Matrix.nonsing_inv_eq_ringInverse]
  rw [he]
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have hU : IsUnit (rlC0 E s X + rlLin W b s x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (rl_isUnit_G b E hs hX hya x)
  have h := contDiffAt_ringInverse ℝ (n := 1) hU.unit
  rw [IsUnit.unit_spec] at h
  exact h.comp x hL.contDiffAt

theorem fetT_fderiv_G (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im)
    (x w : RlCoord W → ℝ) :
    fderiv ℝ (rlG b E s X) x w = -(rlG b E s X x * rlLin W b s w * rlG b E s X x) := by
  rw [(fetT_hasFDerivAt_G hs hX hya x).fderiv]
  rfl

theorem fetT_hasFDerivAt_GYG (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) :
    HasFDerivAt (fun y => rlG b E s X y * Y * rlG b E s X y)
      (fderiv ℝ (fun y => rlG b E s X y * Y * rlG b E s X y) x) x := by
  have h := ((fetT_hasFDerivAt_G (b := b) hs hX hya x).mul_const' Y).mul'
    (fetT_hasFDerivAt_G (b := b) hs hX hya x)
  exact h.differentiableAt.hasFDerivAt

theorem fetT_fderiv_GYG (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x w : RlCoord W → ℝ) :
    fderiv ℝ (fun y => rlG b E s X y * Y * rlG b E s X y) x w =
      -(rlG b E s X x * rlLin W b s w * rlG b E s X x) * Y * rlG b E s X x +
        rlG b E s X x * Y * -(rlG b E s X x * rlLin W b s w * rlG b E s X x) := by
  have h := ((fetT_hasFDerivAt_G (b := b) hs hX hya x).mul_const' Y).mul'
    (fetT_hasFDerivAt_G (b := b) hs hX hya x)
  have e : (fun y => rlG b E s X y * Y * rlG b E s X y) =
      (fun y => rlG b E s X y * Y) * rlG b E s X := rfl
  rw [e, h.fderiv]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul]
  rw [add_comm]
  rfl

theorem fetT_contDiff_GYG (hs : 0 < s) (hX : X.IsHermitian) (hya : 0 < -(matchedA E).im)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ContDiff ℝ 1 (fun y => rlG b E s X y * Y * rlG b E s X y) := by
  have hG := fetT_contDiff_G (b := b) hs hX hya
  exact (hG.mul contDiff_const).mul hG

end Coords

/-!
## 4. The two exact mean identities
-/

section MeanIdentities

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}

/-- The block traces of a matrix as a vector. -/
def fetTtr (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Fin 2 → ℂ := fun k => blockTrace M k

/-- The block-constant diagonal `diag φ(t)`. -/
def fetTdiag (α β : ℝ) (t : Fin 2 → ℂ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal (cmpExt (rlPhi α β t))

theorem fetT_integrable_of_bound {f : (RlCoord W → ℝ) → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f (gaussianProduct (rlVar W b s)) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

variable (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
  (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im)
include hW hs hα hβ hX hy hya

theorem fetT_G_bound (x : RlCoord W → ℝ) : ‖rlG b E s X x‖ ≤ (s * y)⁻¹ :=
  rl_norm_G_le b E hs hX hy hya x

theorem fetT_G_continuous : Continuous (rlG b E s X) :=
  (fetT_contDiff_G hs hX (lt_of_lt_of_le hy hya)).continuous

/-- **Base identity**: `C₀ E G - E[diag φ(g) G] = 1`. -/
theorem fetT_base_identity :
    rlC0 E s X * ∫ x, rlG b E s X x ∂gaussianProduct (rlVar W b s) -
      ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) * rlG b E s X x
        ∂gaussianProduct (rlVar W b s) = 1 := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hinv : ∀ᵐ x ∂gaussianProduct (rlVar W b s), IsUnit (rlC0 E s X + rlLin W b s x).det :=
    ae_of_all _ fun x => rl_isUnit_G b E hs hX hya0 x
  have hG2 : Integrable (fun x => ‖(rlC0 E s X + rlLin W b s x)⁻¹‖ ^ 2)
      (gaussianProduct (rlVar W b s)) := by
    refine Integrable.of_bound ((fetT_G_continuous hW hs hα hβ hX hy hya).norm.pow 2).aestronglyMeasurable
      ((s * y)⁻¹ ^ 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (fetT_G_bound hW hs hα hβ hX hy hya x) 2
  have h := core_limit_identity (rlVar W b s) (rl_reg b E hs.le hX) hinv hG2
  have e : ∀ x, coreS (rlVar W b s) (rlLin W b s) ((rlC0 E s X + rlLin W b s x)⁻¹) *
      (rlC0 E s X + rlLin W b s x)⁻¹ =
      fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) * rlG b E s X x := by
    intro x
    rw [rlS_eq hW hα hβ]
    rfl
  simp only [e] at h
  exact h

/-- The pointwise contraction identity of the derivative equation:
`Σᵢ vᵢ Λᵢ ∂ᵢ(GYG) = -(S(G) GYG + S(GYG) G)`. -/
theorem fetT_sum_contract (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) :
    ∑ i, (rlVar W b s i : ℝ) • (rlLin W b s (Pi.single i 1) *
      fderiv ℝ (fun y => rlG b E s X y * Y * rlG b E s X y) x (Pi.single i 1)) =
      -(coreS (rlVar W b s) (rlLin W b s) (rlG b E s X x) * (rlG b E s X x * Y * rlG b E s X x)) -
        coreS (rlVar W b s) (rlLin W b s) (rlG b E s X x * Y * rlG b E s X x) * rlG b E s X x := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  unfold coreS
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fetT_fderiv_GYG hs hX hya0]
  set Λ := rlLin W b s (Pi.single i 1)
  set G := rlG b E s X x
  have e : Λ * (-(G * Λ * G) * Y * G + G * Y * -(G * Λ * G)) =
      -((Λ * G * Λ) * (G * Y * G)) - (Λ * (G * Y * G) * Λ) * G := by noncomm_ring
  rw [e, smul_sub, smul_neg, Matrix.smul_mul, Matrix.smul_mul]

/-- **Derivative identity** (Gaussian integration by parts for `GYG`):
`C₀ E[GYG] - E[diag φ(g) GYG] - E[diag φ(h) G] = Y E G`. -/
theorem fetT_deriv_identity (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    rlC0 E s X * (∫ x, rlG b E s X x * Y * rlG b E s X x ∂gaussianProduct (rlVar W b s)) -
      (∫ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) *
          (rlG b E s X x * Y * rlG b E s X x) ∂gaussianProduct (rlVar W b s)) -
      (∫ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x * Y * rlG b E s X x)) *
          rlG b E s X x ∂gaussianProduct (rlVar W b s)) =
      Y * ∫ x, rlG b E s X x ∂gaussianProduct (rlVar W b s) := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  set μ := gaussianProduct (rlVar W b s)
  set G := rlG b E s X with hGdef
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hGb : ∀ x, ‖G x‖ ≤ K := fetT_G_bound hW hs hα hβ hX hy hya
  have hGc : Continuous G := fetT_G_continuous hW hs hα hβ hX hy hya
  set F := fun x => G x * Y * G x with hFdef
  have hFc : Continuous F := (hGc.mul continuous_const).mul hGc
  have hFb : ∀ x, ‖F x‖ ≤ K * ‖Y‖ * K := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _))) (hGb x) (norm_nonneg _) (by positivity))
  have hF'b : ∀ x, ‖fderiv ℝ F x‖ ≤ 2 * (K * ‖rlLin W b s‖ * K) * ‖Y‖ * K := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [fetT_fderiv_GYG hs hX hya0]
    have hL := (rlLin W b s).le_opNorm w
    have hGLG : ‖G x * rlLin W b s w * G x‖ ≤ K * (‖rlLin W b s‖ * ‖w‖) * K :=
      (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul (hGb x) hL (norm_nonneg _) hK0)) (hGb x) (norm_nonneg _) (by positivity))
    have t1 : ‖-(G x * rlLin W b s w * G x) * Y * G x‖ ≤ K * (‖rlLin W b s‖ * ‖w‖) * K * ‖Y‖ * K := by
      refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) (hGb x) (norm_nonneg _) (by positivity))
      rw [norm_neg]; exact hGLG
    have t2 : ‖G x * Y * -(G x * rlLin W b s w * G x)‖ ≤ K * ‖Y‖ * (K * (‖rlLin W b s‖ * ‖w‖) * K) := by
      refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _))) ?_ (norm_nonneg _) (by positivity))
      rw [norm_neg]; exact hGLG
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add t1 t2
      _ = 2 * (K * ‖rlLin W b s‖ * K) * ‖Y‖ * K * ‖w‖ := by ring
  have hibp := fetT_ibp (rlVar W b s) (rlLin W b s) (fetT_contDiff_GYG hs hX hya0 Y) hFb hF'b
  -- pointwise `(C₀ + L x) F = Y G`
  have hpt : ∀ x, rlC0 E s X * F x + rlLin W b s x * F x = Y * G x := by
    intro x
    rw [← add_mul]
    have h1 : (rlC0 E s X + rlLin W b s x) * G x = 1 :=
      mul_nonsing_inv _ (rl_isUnit_G b E hs hX hya0 x)
    simp only [hFdef]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hFi : Integrable F μ := fetT_integrable_of_bound hFc hFb
  have hGi : Integrable G μ := fetT_integrable_of_bound hGc hGb
  have hLFi : Integrable (fun x => rlLin W b s x * F x) μ := by
    refine ou_integrable_of_norm_le μ (((rlLin W b s).continuous.mul hFc).aestronglyMeasurable) 0
      (‖rlLin W b s‖ * (K * ‖Y‖ * K)) fun x => ?_
    rw [zero_add]
    calc ‖rlLin W b s x * F x‖ ≤ ‖rlLin W b s x‖ * ‖F x‖ := norm_mul_le _ _
      _ ≤ (‖rlLin W b s‖ * ‖x‖) * (K * ‖Y‖ * K) :=
          mul_le_mul ((rlLin W b s).le_opNorm x) (hFb x) (norm_nonneg _) (by positivity)
      _ = ‖rlLin W b s‖ * (K * ‖Y‖ * K) * ‖x‖ := by ring
  have hsum : ∫ x, rlLin W b s x * F x ∂μ =
      ∫ x, (-(coreS (rlVar W b s) (rlLin W b s) (G x) * F x) -
        coreS (rlVar W b s) (rlLin W b s) (F x) * G x) ∂μ := by
    rw [hibp]
    have hTi : ∀ i, Integrable (fun x => rlLin W b s (Pi.single i 1) * fderiv ℝ F x (Pi.single i 1)) μ := by
      intro i
      have hc : Continuous (fun x => fderiv ℝ F x (Pi.single i 1)) :=
        ((fetT_contDiff_GYG hs hX hya0 Y).continuous_fderiv one_ne_zero).clm_apply continuous_const
      refine Integrable.of_bound (continuous_const.mul hc).aestronglyMeasurable
        (‖rlLin W b s (Pi.single i 1)‖ * (2 * (K * ‖rlLin W b s‖ * K) * ‖Y‖ * K * ‖(Pi.single i 1 : RlCoord W → ℝ)‖))
        (ae_of_all _ fun x => ?_)
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hF'b x)
          (norm_nonneg _))) (norm_nonneg _))
    rw [← integral_congr_ae (ae_of_all _ fun x => fetT_sum_contract hW hs hα hβ hX hy hya Y x)]
    rw [integral_finsetSum _ fun i _ => (hTi i).fun_smul (rlVar W b s i : ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul]
  have hSG : ∀ x, coreS (rlVar W b s) (rlLin W b s) (G x) =
      fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (G x)) := fun x => rlS_eq hW hα hβ _
  have hSF : ∀ x, coreS (rlVar W b s) (rlLin W b s) (F x) =
      fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (F x)) := fun x => rlS_eq hW hα hβ _
  simp only [hSG, hSF] at hsum
  have hDb : ∀ t : Fin 2 → ℂ, ‖(fetTdiag (W := W) (rlAlpha b s) (rlBeta b s) t)‖ ≤
      ‖rlPhi (rlAlpha b s) (rlBeta b s) t 0‖ + ‖rlPhi (rlAlpha b s) (rlBeta b s) t 1‖ := by
    intro t
    rw [fetTdiag, l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => ?_
    simp only [cmpExt]
    rcases rng_fin2_cases q.1 with h | h <;> rw [h] <;> simp
  have hcont_tr : Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr M) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
    unfold fetTdiag fetTtr rlPhi cmpExt
    refine continuous_pi fun p => continuous_pi fun q => ?_
    simp only [diagonal_apply]
    split_ifs
    · exact ((continuous_const.mul ((rlTrCLM W p.1).continuous)).add
        (continuous_const.mul ((rlTrCLM W (1 - p.1)).continuous)))
    · exact continuous_const
  have hD1i : Integrable (fun x => fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (G x)) * F x) μ := by
    refine fetT_integrable_of_bound ((hcont_tr.comp hGc).mul hFc) (C := (2 * (2 * K)) * (K * ‖Y‖ * K))
      fun x => (norm_mul_le _ _).trans (mul_le_mul ?_ (hFb x) (norm_nonneg _) (by positivity))
    refine (hDb _).trans ?_
    have hb : ∀ k, ‖rlPhi (rlAlpha b s) (rlBeta b s) (fetTtr (G x)) k‖ ≤ 2 * K := by
      intro k
      simp only [rlPhi, fetTtr]
      have h1 := (lct_norm_blockTrace_le (G x) k).trans (hGb x)
      have h2 := (lct_norm_blockTrace_le (G x) (1 - k)).trans (hGb x)
      have ha1 : rlAlpha b s ≤ 1 := by
        unfold rlAlpha; unfold rlBeta at hβ; linarith
      have hb1 : rlBeta b s ≤ 1 := by
        unfold rlBeta; unfold rlAlpha at hα; linarith
      calc _ ≤ ‖((rlAlpha b s : ℝ) : ℂ) * blockTrace (G x) k‖ +
            ‖((rlBeta b s : ℝ) : ℂ) * blockTrace (G x) (1 - k)‖ := norm_add_le _ _
        _ ≤ 1 * K + 1 * K := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα,
              Real.norm_of_nonneg hβ]
            exact add_le_add (mul_le_mul ha1 h1 (norm_nonneg _) zero_le_one)
              (mul_le_mul hb1 h2 (norm_nonneg _) zero_le_one)
        _ = 2 * K := by ring
    linarith [hb 0, hb 1]
  have hD2i : Integrable (fun x => fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (F x)) * G x) μ := by
    refine fetT_integrable_of_bound ((hcont_tr.comp hFc).mul hGc) (C := (2 * (2 * (K * ‖Y‖ * K))) * K)
      fun x => (norm_mul_le _ _).trans (mul_le_mul ?_ (hGb x) (norm_nonneg _) (by positivity))
    refine (hDb _).trans ?_
    have hb : ∀ k, ‖rlPhi (rlAlpha b s) (rlBeta b s) (fetTtr (F x)) k‖ ≤ 2 * (K * ‖Y‖ * K) := by
      intro k
      simp only [rlPhi, fetTtr]
      have h1 := (lct_norm_blockTrace_le (F x) k).trans (hFb x)
      have h2 := (lct_norm_blockTrace_le (F x) (1 - k)).trans (hFb x)
      have ha1 : rlAlpha b s ≤ 1 := by
        unfold rlAlpha; unfold rlBeta at hβ; linarith
      have hb1 : rlBeta b s ≤ 1 := by
        unfold rlBeta; unfold rlAlpha at hα; linarith
      have hY0 : 0 ≤ K * ‖Y‖ * K := by positivity
      calc _ ≤ ‖((rlAlpha b s : ℝ) : ℂ) * blockTrace (F x) k‖ +
            ‖((rlBeta b s : ℝ) : ℂ) * blockTrace (F x) (1 - k)‖ := norm_add_le _ _
        _ ≤ 1 * (K * ‖Y‖ * K) + 1 * (K * ‖Y‖ * K) := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα,
              Real.norm_of_nonneg hβ]
            exact add_le_add (mul_le_mul ha1 h1 (norm_nonneg _) zero_le_one)
              (mul_le_mul hb1 h2 (norm_nonneg _) zero_le_one)
        _ = 2 * (K * ‖Y‖ * K) := by ring
    linarith [hb 0, hb 1]
  rw [integral_sub hD1i.fun_neg hD2i, integral_neg] at hsum
  have hmain : ∫ x, (rlC0 E s X * F x + rlLin W b s x * F x) ∂μ = Y * ∫ x, G x ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Y).integral_comp_comm hGi
  have hCFi : Integrable (fun x => rlC0 E s X * F x) μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (rlC0 E s X)).integrable_comp hFi
  have hCF : ∫ x, rlC0 E s X * F x ∂μ = rlC0 E s X * ∫ x, F x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (rlC0 E s X)).integral_comp_comm hFi
  rw [integral_add hCFi hLFi, hsum, hCF] at hmain
  rw [← hmain]
  abel

end MeanIdentities

/-!
## 5. The mean-field matrices
-/

section MeanField

variable {W : ℕ}

/-- `Ḡ = E G`. -/
def fetTGb (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∫ x, rlG b E s X x ∂gaussianProduct (rlVar W b s)

/-- `m̄ = tr Ḡ` (`= rlMean`). -/
def fetTm (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) : Fin 2 → ℂ :=
  fetTtr (fetTGb b E s X)

/-- `M̄ = (-E - X - σ(m̄))⁻¹`. -/
def fetTMb (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  cmpInv (cmpTopH E X) (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X))

/-- `R = (-E - X - (1-b)a)⁻¹ = (z_∂ - X)⁻¹`. -/
def fetTRp (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  cmpInv (cmpTopH E X) (fun _ => ((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E)

/-- `Δ = diag φ(m̄ - a)`. -/
def fetTDelta (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fetTdiag (rlAlpha b s) (rlBeta b s) (fun k => fetTm b E s X k - matchedA E)

/-- `D(x) = diag φ(g(x) - m̄)`. -/
def fetTD (b E s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  fetTdiag (rlAlpha b s) (rlBeta b s) (fun k => fetTtr (rlG b E s X x) k - fetTm b E s X k)

theorem fetTdiag_sub (α β : ℝ) (t u : Fin 2 → ℂ) :
    (fetTdiag α β (fun k => t k - u k) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      fetTdiag α β t - fetTdiag α β u := by
  unfold fetTdiag
  rw [diagonal_sub]
  congr 1
  funext q
  simp only [cmpExt, rlPhi]
  ring

theorem fetT_norm_diag_le {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (t : Fin 2 → ℂ) :
    ‖(fetTdiag α β t : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ (α + β) * (‖t 0‖ + ‖t 1‖) := by
  rw [fetTdiag, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun q => ?_
  simp only [cmpExt, rlPhi]
  have h0 := norm_nonneg (t 0)
  have h1 := norm_nonneg (t 1)
  rcases rng_fin2_cases q.1 with h | h <;> rw [h]
  · calc _ ≤ ‖(α : ℂ) * t 0‖ + ‖(β : ℂ) * t (1 - 0)‖ := norm_add_le _ _
      _ = α * ‖t 0‖ + β * ‖t 1‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα,
            Real.norm_of_nonneg hβ]; rfl
      _ ≤ _ := by nlinarith
  · calc _ ≤ ‖(α : ℂ) * t 1‖ + ‖(β : ℂ) * t (1 - 1)‖ := norm_add_le _ _
      _ = α * ‖t 1‖ + β * ‖t 0‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hα,
            Real.norm_of_nonneg hβ]; rfl
      _ ≤ _ := by nlinarith

/-- `diag(cmpExt t) = Σ_l t_l P_l`. -/
theorem fetT_diag_eq_sum (t : Fin 2 → ℂ) :
    (diagonal (cmpExt t) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      ∑ l : Fin 2, t l • rlProj l := by
  ext p q
  by_cases h : p = q
  · subst h
    rcases rng_fin2_cases p.1 with h1 | h1 <;>
      simp [Fin.sum_univ_two, rlProj, cmpExt, h1]
  · simp [Fin.sum_univ_two, rlProj, h]

theorem fetT_blockTrace_proj_mul (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : Fin 2) :
    blockTrace M k = (((W : ℝ)⁻¹ : ℝ) : ℂ) * (rlProj k * M).trace := rl_blockTrace_proj M k

theorem fetT_continuous_diag (α β : ℝ) :
    Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
      (fetTdiag α β (fetTtr M) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) := by
  unfold fetTdiag fetTtr rlPhi cmpExt
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [diagonal_apply]
  split_ifs
  · exact ((continuous_const.mul ((rlTrCLM W p.1).continuous)).add
      (continuous_const.mul ((rlTrCLM W (1 - p.1)).continuous)))
  · exact continuous_const

/-- `M ↦ Tr(A M)` as a continuous linear map. -/
def fetTtrL (A : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap _ ℂ ℂ).comp (LinearMap.mulLeft ℂ A))

theorem fetTtrL_apply (A M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    fetTtrL A M = (A * M).trace := rfl

/-- `Q̂_j = α P_j + β P_{1-j}`. -/
def fetTQh (α β : ℝ) (j : Fin 2) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (α : ℂ) • rlProj j + (β : ℂ) • rlProj (1 - j)

theorem fetTdiag_eq_Qh (α β : ℝ) (t : Fin 2 → ℂ) :
    (fetTdiag α β t : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = ∑ j, t j • fetTQh α β j := by
  unfold fetTdiag
  rw [fetT_diag_eq_sum]
  simp only [Fin.sum_univ_two, fetTQh, rlPhi, smul_add, smul_smul, add_smul]
  have h10 : (1 : Fin 2) - 0 = 1 := rfl
  have h11 : (1 : Fin 2) - 1 = 0 := rfl
  rw [h10, h11]
  simp only [mul_comm]
  abel

theorem fetTQh_sum (α β : ℝ) :
    (∑ j, fetTQh α β j : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = ((α + β : ℝ) : ℂ) • 1 := by
  have hP : (rlProj 0 + rlProj 1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) = 1 := by
    ext p q
    simp only [rlProj, Matrix.add_apply, diagonal_apply, Matrix.one_apply]
    split_ifs <;> rcases rng_fin2_cases p.1 with h | h <;> simp_all
  simp only [Fin.sum_univ_two, fetTQh]
  have h10 : (1 : Fin 2) - 0 = 1 := rfl
  have h11 : (1 : Fin 2) - 1 = 0 := rfl
  rw [h10, h11]
  calc (α : ℂ) • rlProj 0 + (β : ℂ) • rlProj 1 + ((α : ℂ) • rlProj 1 + (β : ℂ) • rlProj 0) =
      ((α : ℂ) + β) • (rlProj 0 + rlProj 1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
        rw [smul_add, add_smul, add_smul]; abel
    _ = _ := by rw [hP]; push_cast; rfl

theorem fetTQh_norm {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (j : Fin 2) :
    ‖(fetTQh α β j : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ α + β := by
  unfold fetTQh
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hα]
    exact mul_le_of_le_one_right hα (rl_norm_proj_le _)
  · refine (norm_smul_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_of_nonneg hβ]
    exact mul_le_of_le_one_right hβ (rl_norm_proj_le _)

theorem fetT_bt_sub (M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : Fin 2) :
    blockTrace M k - blockTrace N k = blockTrace (M - N) k := ((rlTrCLM W k).map_sub M N).symm

theorem fetT_norm_rlProj (k : Fin 2) : ‖(rlProj k : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ 1 :=
  rl_norm_proj_le k

end MeanField

/-!
## 7. The Hilbert–Schmidt weighted gradient bound
-/

theorem fetT_weighted_hs_le {W : ℕ} {b s : ℝ} (hW : 0 < W) (hA : (W : ℝ) * (rlTA W b s : ℝ) ≤ 1)
    (hB : (W : ℝ) * (rlTB W b s : ℝ) ≤ 1) (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    ∑ i, (rlVar W b s i : ℝ) * ‖(K * rlLin W b s (Pi.single i 1)).trace‖ ^ 2 ≤
      6 / W * dcvHS K := by
  set HS := ∑ x, ∑ y, ‖K x y‖ ^ 2 with hHS
  have hHSle : HS ≤ 2 * W * ‖K‖ ^ 2 := by
    have := tfl_hs_le K
    simpa [Fintype.card_prod, Fintype.card_fin] using this
  have hg : ∀ x y, 0 ≤ ‖K x y‖ ^ 2 := fun _ _ => sq_nonneg _
  have htA := (rlTA W b s).2
  have htB := (rlTB W b s).2
  rw [Fintype.sum_sum_type]
  have hblk : ∑ i : Fin 2 × GaussCoord W, (rlVar W b s (Sum.inl i) : ℝ) *
      ‖(K * rlLin W b s (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤ 2 * (rlTA W b s : ℝ) * HS := by
    have h1 : ∀ i : Fin 2 × GaussCoord W, (rlVar W b s (Sum.inl i) : ℝ) *
        ‖(K * rlLin W b s (Pi.single (Sum.inl i) 1)).trace‖ ^ 2 ≤
        (rlTA W b s : ℝ) / 4 * (2 * (‖K (i.1, i.2.1.2) (i.1, i.2.1.1)‖ ^ 2 +
          ‖K (i.1, i.2.1.1) (i.1, i.2.1.2)‖ ^ 2)) := by
      rintro ⟨j, ⟨⟨α, β⟩, t⟩⟩
      simp only [rlVar, Sum.elim_inl, NNReal.coe_one, one_mul]
      fin_cases t
      · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, rl_lin_A0, ← rlCA_norm_sq W b s]
        exact rl_trace_sq_le K _ _ _ _ _ (by simp) (by simp)
      · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, rl_lin_A1, ← rlCA_norm_sq W b s]
        exact rl_trace_sq_le K _ _ _ _ _ (by simp) (by simp)
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    have e1 := tfl_diag_blocks_le (fun x y => ‖K x y‖ ^ 2) hg
    have e2 : ∑ a : Fin 2, ∑ α : Fin W, ∑ β : Fin W, ‖K (a, β) (a, α)‖ ^ 2 ≤ HS := by
      have := tfl_diag_blocks_le (fun x y => ‖K y x‖ ^ 2) (fun _ _ => sq_nonneg _)
      refine this.trans (le_of_eq ?_)
      exact Finset.sum_comm
    simp only [Fin.sum_univ_two] at e1 e2
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] at *
    nlinarith
  have hbond : ∑ i : Fin W × Fin W × Fin 2, (rlVar W b s (Sum.inr i) : ℝ) *
      ‖(K * rlLin W b s (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤ 4 * (rlTB W b s : ℝ) * HS := by
    have h1 : ∀ i : Fin W × Fin W × Fin 2, (rlVar W b s (Sum.inr i) : ℝ) *
        ‖(K * rlLin W b s (Pi.single (Sum.inr i) 1)).trace‖ ^ 2 ≤
        (rlTB W b s : ℝ) / 2 * (2 * (‖K ((0 : Fin 2), i.2.1) ((1 : Fin 2), i.1)‖ ^ 2 +
          ‖K ((1 : Fin 2), i.1) ((0 : Fin 2), i.2.1)‖ ^ 2)) := by
      rintro ⟨α, β, t⟩
      simp only [rlVar, Sum.elim_inr, NNReal.coe_div, NNReal.coe_ofNat]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      fin_cases t
      · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, rl_lin_B0]
        have := rl_trace_sq_le K ((1 : Fin 2), α) ((0 : Fin 2), β) 1 1 1 (by simp) (by simp)
        simpa using this
      · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, rl_lin_B1]
        have := rl_trace_sq_le K ((1 : Fin 2), α) ((0 : Fin 2), β) 1 Complex.I (-Complex.I)
          (by simp) (by simp)
        simpa using this
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    have e1 : ∑ α : Fin W, ∑ β : Fin W, ‖K ((0 : Fin 2), β) ((1 : Fin 2), α)‖ ^ 2 ≤ HS := by
      have := rl_sub_sum_le (fun x y => ‖K y x‖ ^ 2) (fun _ _ => sq_nonneg _) 1 0
      refine this.trans (le_of_eq ?_)
      exact Finset.sum_comm
    have e2 : ∑ α : Fin W, ∑ β : Fin W, ‖K ((1 : Fin 2), α) ((0 : Fin 2), β)‖ ^ 2 ≤ HS :=
      rl_sub_sum_le (fun x y => ‖K x y‖ ^ 2) hg 1 0
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] at *
    nlinarith
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hHS0 : 0 ≤ HS := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hg x y
  have hdc : dcvHS K = HS := rfl
  rw [hdc]
  have htA' : (rlTA W b s : ℝ) ≤ 1 / W := by rw [le_div_iff₀ hW']; linarith
  have htB' : (rlTB W b s : ℝ) ≤ 1 / W := by rw [le_div_iff₀ hW']; linarith
  have e1 : 2 * (rlTA W b s : ℝ) * HS ≤ 2 * (1 / W) * HS := by gcongr
  have e2 : 4 * (rlTB W b s : ℝ) * HS ≤ 4 * (1 / W) * HS := by gcongr
  have e3 : 2 * (1 / (W : ℝ)) * HS + 4 * (1 / W) * HS = 6 / W * HS := by ring
  linarith

/-!
## 8. Scalar and `L²` helpers
-/

section Helpers

theorem fetT_sqrt_absorb {x A B : ℝ} (hx : 0 ≤ x) (h : x ≤ A + B * Real.sqrt x) :
    x ≤ 2 * A + B ^ 2 := by
  have hs := Real.sq_sqrt hx
  nlinarith [sq_nonneg (Real.sqrt x - B), Real.sqrt_nonneg x]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem fetT_memLp_two_of_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf C (ae_of_all _ hC)

/-- Cauchy–Schwarz: `∫ f g ≤ √(∫ f²) √(∫ g²)` for nonnegative `f, g ∈ L²`. -/
theorem fetT_int_mul_le {f g : Ω → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hg0) (by simpa using hf) (by simpa using hg)
  have e : ∀ φ : Ω → ℝ, (∫ x, φ x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, φ x ^ 2 ∂μ) := by
    intro φ
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    exact Real.rpow_two _
  rwa [e f, e g] at h

/-- From an `L²` bound to the second moment: `∫ ‖f‖² ≤ A²`. -/
theorem fetT_int_sq_le_of_eLpNorm {f : Ω → ℂ} (hf : MemLp f 2 μ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : eLpNorm f 2 μ ≤ ENNReal.ofReal A) : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ A ^ 2 := by
  have e := hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  simp only [ENNReal.toReal_ofNat] at e
  rw [e] at hA
  have h1 := (ENNReal.ofReal_le_ofReal_iff hA0).mp hA
  have hI0 : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun x => by positivity
  have h2 : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ ≤ A ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hI0, show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
  refine le_trans (le_of_eq ?_) h2
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  exact (Real.rpow_two _).symm

theorem fetT_ennreal_absorb {N : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a) (hN : N ≠ ⊤)
    (h : N ≤ ENNReal.ofReal a + ENNReal.ofReal (1 / 2) * N) : N ≤ ENNReal.ofReal (2 * a) := by
  rw [← ENNReal.ofReal_toReal hN] at h ⊢
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add ha (by positivity)] at h
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h ⊢
  linarith

theorem fetT_small_const {K Cg p W : ℝ} (hK : 0 ≤ K) (hCg : 0 ≤ Cg) (hp : 0 ≤ p) (hW : 0 < W)
    (hWp : 24 * (K * Cg) ^ 2 * p ≤ W) : K * Cg * Real.sqrt p * Real.sqrt (6 / W) ≤ 1 / 2 := by
  have e : K * Cg * Real.sqrt p * Real.sqrt (6 / W) = Real.sqrt ((K * Cg) ^ 2 * (6 * p / W)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), mul_assoc,
      ← Real.sqrt_mul hp, show p * (6 / W) = 6 * p / W by ring]
  rw [e]
  have h : (K * Cg) ^ 2 * (6 * p / W) ≤ (1 / 2) ^ 2 := by
    rw [show (K * Cg) ^ 2 * (6 * p / W) = 6 * ((K * Cg) ^ 2 * p) / W by ring, div_le_iff₀ hW]
    nlinarith
  calc Real.sqrt ((K * Cg) ^ 2 * (6 * p / W)) ≤ Real.sqrt ((1 / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 / 2 := Real.sqrt_sq (by norm_num)

/-- **Stable linear system**: `v = d + q v + e` with row sums `Σ_j |q_kj| ≤ θ < 1` gives
`|v_k| ≤ (max|d| + max|e|)/(1-θ)`. -/
theorem fetT_linsys {v d e : Fin 2 → ℂ} {q : Fin 2 → Fin 2 → ℂ} {θ : ℝ} (hθ : θ < 1)
    (hq : ∀ k, ∑ j, ‖q k j‖ ≤ θ) (hv : ∀ k, v k = d k + ∑ j, q k j * v j + e k) (k : Fin 2) :
    ‖v k‖ ≤ (max ‖d 0‖ ‖d 1‖ + max ‖e 0‖ ‖e 1‖) / (1 - θ) := by
  set M := max ‖v 0‖ ‖v 1‖ with hM
  have hvk : ∀ k, ‖v k‖ ≤ M := fun k => by
    rcases rng_fin2_cases k with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hdk : ∀ k, ‖d k‖ ≤ max ‖d 0‖ ‖d 1‖ := fun k => by
    rcases rng_fin2_cases k with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hek : ∀ k, ‖e k‖ ≤ max ‖e 0‖ ‖e 1‖ := fun k => by
    rcases rng_fin2_cases k with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hθ0 : 0 ≤ θ := (Finset.sum_nonneg fun j _ => norm_nonneg (q 0 j)).trans (hq 0)
  have hstep : ∀ k, ‖v k‖ ≤ max ‖d 0‖ ‖d 1‖ + θ * M + max ‖e 0‖ ‖e 1‖ := by
    intro k
    rw [hv k]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hdk k) ?_))
      (hek k))
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖q k j * v j‖ ≤ ∑ j, ‖q k j‖ * M := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hvk j) (norm_nonneg _)
      _ = (∑ j, ‖q k j‖) * M := by rw [Finset.sum_mul]
      _ ≤ θ * M := mul_le_mul_of_nonneg_right (hq k) ((norm_nonneg _).trans (hvk 0))
  have hMle : M ≤ max ‖d 0‖ ‖d 1‖ + θ * M + max ‖e 0‖ ‖e 1‖ := max_le (hstep 0) (hstep 1)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hvk k, (norm_nonneg (v k)), mul_le_mul_of_nonneg_left (hvk k) hθ0]

end Helpers

/-!
## 6. Mean-field facts under the standing hypotheses
-/

theorem fetT_eq_of_sub_neg {M : Type*} [AddCommGroup M] {A B C : M} (h : A - B = -C) :
    B = A + C := by
  have e : B = A - (A - B) := by abel
  rw [e, h]; abel

theorem fetT_eq_of_sub {M : Type*} [AddCommGroup M] {A B C : M} (h : B - A = C) : B = A + C := by
  rw [← h]; abel

section Standing

variable {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
  (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
  (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im)
include hW hs hα hβ hX hy hya

theorem fetT_G_integrable : Integrable (rlG b E s X) (gaussianProduct (rlVar W b s)) :=
  fetT_integrable_of_bound (fetT_G_continuous hW hs hα hβ hX hy hya)
    (fetT_G_bound hW hs hα hβ hX hy hya)

theorem fetT_m_eq (k : Fin 2) : fetTm b E s X k = rlMean b E s X k := by
  unfold fetTm fetTtr fetTGb rlMean
  rw [← rlTrCLM_apply, ← (rlTrCLM W k).integral_comp_comm (fetT_G_integrable hW hs hα hβ hX hy hya)]
  rfl

theorem fetT_shift_im (k : Fin 2) :
    s * y ≤ -(rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X) k).im := by
  rw [rlShift_im]
  have h1 := rl_mean_im_nonpos (b := b) hs hX hy hya k
  have h2 := rl_mean_im_nonpos (b := b) hs hX hy hya (1 - k)
  rw [← fetT_m_eq hW hs hα hβ hX hy hya] at h1 h2
  have : s * y ≤ s * (-(matchedA E).im) := mul_le_mul_of_nonneg_left hya hs.le
  nlinarith

theorem fetT_N1_isUnit : IsUnit (cmpTopH E X - diagonal (cmpExt
    (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X)))).det :=
  isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ (cmpTopH_isHermitian E hX) _ fun q => by
    have := fetT_shift_im hW hs hα hβ hX hy hya q.1
    simp only [cmpExt]
    nlinarith [mul_pos hs hy])

theorem fetT_Mb_bound : ‖fetTMb b E s X‖ ≤ (s * y)⁻¹ :=
  lct_norm_shifted_inv_le _ (cmpTopH_isHermitian E hX) _ (mul_pos hs hy) fun q =>
    fetT_shift_im hW hs hα hβ hX hy hya q.1

theorem fetT_lam_ge : s * y ≤ -((((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E).im) := by
  rw [Complex.im_ofReal_mul]
  have : s ≤ rlAlpha b s + rlBeta b s + s := by linarith
  have h0 : 0 ≤ -(matchedA E).im := hy.le.trans hya
  nlinarith

theorem fetT_N0_isUnit : IsUnit (cmpTopH E X - diagonal (cmpExt
    (fun _ : Fin 2 => ((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E))).det :=
  isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ (cmpTopH_isHermitian E hX) _ fun q => by
    have := fetT_lam_ge hW hs hα hβ hX hy hya
    simp only [cmpExt]
    nlinarith [mul_pos hs hy])

theorem fetT_Rp_bound : ‖fetTRp b E s X‖ ≤ (s * y)⁻¹ :=
  lct_norm_shifted_inv_le _ (cmpTopH_isHermitian E hX) _ (mul_pos hs hy) fun _ =>
    fetT_lam_ge hW hs hα hβ hX hy hya

theorem fetT_Rp_normal : (fetTRp b E s X)ᴴ * fetTRp b E s X = fetTRp b E s X * (fetTRp b E s X)ᴴ :=
  fetT_normal (cmpTopH_isHermitian E hX) _

theorem fetT_Rp_eq (hE2 : |E| ≤ 2) : fetR b E X = fetTRp b E s X := by
  unfold fetR fetTRp
  rw [cmp_resolvent_eq hE2]
  congr 1
  funext _
  congr 1
  unfold rlAlpha rlBeta
  push_cast
  ring

/-- `N₀ - N₁ = Δ`. -/
theorem fetT_N_diff :
    (cmpTopH E X - diagonal (cmpExt (fun _ : Fin 2 => ((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) *
      matchedA E))) =
    (cmpTopH E X - diagonal (cmpExt
      (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X)))) +
      fetTDelta b E s X := by
  unfold fetTDelta fetTdiag
  ext p q
  simp only [Matrix.sub_apply, Matrix.add_apply, diagonal_apply, cmpExt]
  split_ifs
  · have := rlShift_sub s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X) p.1
    simp only [rlPhi]
    rw [← this]
    ring
  · ring

theorem fetT_Mb_eq_Rp_left : fetTMb b E s X = fetTRp b E s X * (1 + fetTDelta b E s X * fetTMb b E s X) := by
  have h := tgt_inv_sub_of_add (fetT_N_diff hW hs hα hβ hX hy hya)
    (fetT_N0_isUnit hW hs hα hβ hX hy hya) (fetT_N1_isUnit hW hs hα hβ hX hy hya)
  unfold fetTMb fetTRp cmpInv
  rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc]
  exact fetT_eq_of_sub_neg h

theorem fetT_Mb_eq_Rp_right : fetTMb b E s X = (1 + fetTMb b E s X * fetTDelta b E s X) * fetTRp b E s X := by
  have hN : (cmpTopH E X - diagonal (cmpExt
      (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X)))) =
    (cmpTopH E X - diagonal (cmpExt (fun _ : Fin 2 => ((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) *
      matchedA E))) + -fetTDelta b E s X := by
    rw [fetT_N_diff hW hs hα hβ hX hy hya]; abel
  have h := tgt_inv_sub_of_add hN (fetT_N1_isUnit hW hs hα hβ hX hy hya)
    (fetT_N0_isUnit hW hs hα hβ hX hy hya)
  unfold fetTMb fetTRp cmpInv
  rw [Matrix.add_mul, Matrix.one_mul]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg] at h
  exact fetT_eq_of_sub h

theorem fetT_m_bound (k : Fin 2) : ‖fetTm b E s X k‖ ≤ (s * y)⁻¹ := by
  rw [fetT_m_eq hW hs hα hβ hX hy hya]; exact rl_mean_norm_le hs hX hy hya k

theorem fetT_D_eq (x : RlCoord W → ℝ) :
    fetTD b E s X x = fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) -
      fetTdiag (rlAlpha b s) (rlBeta b s) (fetTm b E s X) := fetTdiag_sub _ _ _ _

theorem fetT_D_continuous : Continuous (fetTD b E s X) := by
  have h : fetTD b E s X = fun x => fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) -
      fetTdiag (rlAlpha b s) (rlBeta b s) (fetTm b E s X) := funext (fetT_D_eq hW hs hα hβ hX hy hya)
  rw [h]
  exact ((fetT_continuous_diag _ _).comp (fetT_G_continuous hW hs hα hβ hX hy hya)).sub
    continuous_const

theorem fetT_D_norm_le (x : RlCoord W → ℝ) :
    ‖fetTD b E s X x‖ ≤ (rlAlpha b s + rlBeta b s) *
      (‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ +
        ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖) :=
  fetT_norm_diag_le hα hβ _

theorem fetT_D_bound (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (x : RlCoord W → ℝ) :
    ‖fetTD b E s X x‖ ≤ 8 * (s * y)⁻¹ := by
  refine (fetT_D_norm_le hW hs hα hβ hX hy hya x).trans ?_
  have hK : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have hg : ∀ k, ‖blockTrace (rlG b E s X x) k - fetTm b E s X k‖ ≤ 2 * (s * y)⁻¹ := fun k =>
    (norm_sub_le _ _).trans (by
      have h1 := (lct_norm_blockTrace_le (rlG b E s X x) k).trans (fetT_G_bound hW hs hα hβ hX hy hya x)
      have h2 := fetT_m_bound hW hs hα hβ hX hy hya k
      linarith)
  have hab : rlAlpha b s + rlBeta b s ≤ 2 := by linarith
  have h0 := hg 0
  have h1 := hg 1
  have hn0 := norm_nonneg (blockTrace (rlG b E s X x) 0 - fetTm b E s X 0)
  have hn1 := norm_nonneg (blockTrace (rlG b E s X x) 1 - fetTm b E s X 1)
  nlinarith

/-- **Mean relation**: `Ḡ = M̄ + M̄ E[D G]`. -/
theorem fetT_Gb_eq (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) :
    fetTGb b E s X = fetTMb b E s X + fetTMb b E s X *
      ∫ x, fetTD b E s X x * rlG b E s X x ∂gaussianProduct (rlVar W b s) := by
  set μ := gaussianProduct (rlVar W b s)
  have base := fetT_base_identity hW hs hα hβ hX hy hya
  have hGi := fetT_G_integrable hW hs hα hβ hX hy hya
  have hDGi : Integrable (fun x => fetTD b E s X x * rlG b E s X x) μ :=
    fetT_integrable_of_bound ((fetT_D_continuous hW hs hα hβ hX hy hya).mul
      (fetT_G_continuous hW hs hα hβ hX hy hya)) (C := 8 * (s * y)⁻¹ * (s * y)⁻¹) fun x =>
      (norm_mul_le _ _).trans (mul_le_mul (fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1 x)
        (fetT_G_bound hW hs hα hβ hX hy hya x) (norm_nonneg _) (by have := mul_pos hs hy; positivity))
  set Dm : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fetTdiag (rlAlpha b s) (rlBeta b s) (fetTm b E s X)
  have hsplit : ∀ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) * rlG b E s X x =
      Dm * rlG b E s X x + fetTD b E s X x * rlG b E s X x := by
    intro x; rw [fetT_D_eq hW hs hα hβ hX hy hya, ← Matrix.add_mul]; congr 1; abel
  have hDm : ∫ x, Dm * rlG b E s X x ∂μ = Dm * ∫ x, rlG b E s X x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Dm).integral_comp_comm hGi
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add (hGi.const_mul Dm) hDGi, hDm] at base
  have hN1 : rlC0 E s X - Dm = cmpTopH E X - diagonal (cmpExt
      (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X))) :=
    rl_C0_sub E s _ _ X _
  have hmain : (rlC0 E s X - Dm) * fetTGb b E s X = 1 + ∫ x, fetTD b E s X x * rlG b E s X x ∂μ := by
    rw [Matrix.sub_mul]; unfold fetTGb; rw [← base]; abel
  have hMN : fetTMb b E s X * (rlC0 E s X - Dm) = 1 := by
    rw [hN1]; exact nonsing_inv_mul _ (fetT_N1_isUnit hW hs hα hβ hX hy hya)
  calc fetTGb b E s X = (fetTMb b E s X * (rlC0 E s X - Dm)) * fetTGb b E s X := by
        rw [hMN, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, hmain, Matrix.mul_add, Matrix.mul_one]

end Standing

/-!
## 9. The residual clock
-/

/-- The Gaussian `L^p` gradient inequality with constant `Cg` (`GaussianLpGradient`). -/
def FetTGrad (Cg : ℝ) : Prop :=
  ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
    (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
      eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
          (gaussianProduct v) ≤
        ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v)

section Clock

variable {W : ℕ} {b E s : ℝ} {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
  (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
  (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im)
  (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (hE2 : |E| ≤ 2) (hS : S.PosSemidef)
  {Cg : ℝ} (hCg : 0 ≤ Cg) (hgr : FetTGrad Cg)
include hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr

/-- `L²` fluctuation of a block trace: `E|g_k - m̄_k|² ≤ A_f²`, `A_f = Cg √2 (16/W) K²`. -/
theorem fetT_g_L2 (k : Fin 2) :
    ∫ x, ‖blockTrace (rlG b E s X x) k - fetTm b E s X k‖ ^ 2 ∂gaussianProduct (rlVar W b s) ≤
      (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h := rl_fluct hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya (rlProj k) (p := 2) one_le_two
  have hP := rl_norm_proj_le (W := W) k
  have e : (fun x => rlF b E s X (rlProj k) x -
      ∫ x', rlF b E s X (rlProj k) x' ∂gaussianProduct (rlVar W b s)) =
      fun x => blockTrace (rlG b E s X x) k - fetTm b E s X k := by
    funext x
    rw [fetT_m_eq hW hs hα hβ hX hy hya, rlMean, rlF, ← rl_blockTrace_proj]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x' => ?_)
    show rlF b E s X (rlProj k) x' = _
    rw [rlF, ← rl_blockTrace_proj]
  rw [e] at h
  have hb : Cg * Real.sqrt 2 * (16 * ‖(rlProj k : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ / W) *
      (s * y)⁻¹ ^ 2 ≤ Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2 := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) (sq_nonneg _)
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  have h2 : eLpNorm (fun x => blockTrace (rlG b E s X x) k - fetTm b E s X k) 2
      (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact h.trans (ENNReal.ofReal_le_ofReal hb)
  have hm : MemLp (fun x => blockTrace (rlG b E s X x) k - fetTm b E s X k) 2
      (gaussianProduct (rlVar W b s)) := by
    refine MemLp.of_bound ((((rlTrCLM W k).continuous.comp
      (fetT_G_continuous hW hs hα hβ hX hy hya)).sub continuous_const).aestronglyMeasurable)
      (2 * (s * y)⁻¹) (ae_of_all _ fun x => ?_)
    refine (norm_sub_le _ _).trans ?_
    have h1 := (lct_norm_blockTrace_le (rlG b E s X x) k).trans (fetT_G_bound hW hs hα hβ hX hy hya x)
    have h2 := fetT_m_bound hW hs hα hβ hX hy hya k
    linarith
  exact fetT_int_sq_le_of_eLpNorm hm (by positivity) h2

/-- `E ‖D‖² ≤ 16 A_f²`. -/
theorem fetT_D_L2 :
    ∫ x, ‖fetTD b E s X x‖ ^ 2 ∂gaussianProduct (rlVar W b s) ≤
      16 * (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2 := by
  set μ := gaussianProduct (rlVar W b s)
  set Af := Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2
  have hcont : ∀ k, Continuous (fun x => ‖blockTrace (rlG b E s X x) k - fetTm b E s X k‖ ^ 2) :=
    fun k => ((((rlTrCLM W k).continuous.comp
      (fetT_G_continuous hW hs hα hβ hX hy hya)).sub continuous_const).norm.pow 2)
  have hbd : ∀ k x, ‖blockTrace (rlG b E s X x) k - fetTm b E s X k‖ ^ 2 ≤ (2 * (s * y)⁻¹) ^ 2 := by
    intro k x
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    have h1 := (lct_norm_blockTrace_le (rlG b E s X x) k).trans (fetT_G_bound hW hs hα hβ hX hy hya x)
    have h2 := fetT_m_bound hW hs hα hβ hX hy hya k
    linarith
  have hint : ∀ k, Integrable (fun x => ‖blockTrace (rlG b E s X x) k - fetTm b E s X k‖ ^ 2) μ :=
    fun k => Integrable.of_bound (hcont k).aestronglyMeasurable _ (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbd k x)
  have hpt : ∀ x, ‖fetTD b E s X x‖ ^ 2 ≤
      8 * (‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ ^ 2 +
        ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖ ^ 2) := by
    intro x
    have h := fetT_D_norm_le hW hs hα hβ hX hy hya x
    have hab : rlAlpha b s + rlBeta b s ≤ 2 := by linarith
    have h0 := norm_nonneg (blockTrace (rlG b E s X x) 0 - fetTm b E s X 0)
    have h1 := norm_nonneg (blockTrace (rlG b E s X x) 1 - fetTm b E s X 1)
    have h3 : ‖fetTD b E s X x‖ ≤ 2 * (‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ +
        ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖) :=
      h.trans (mul_le_mul_of_nonneg_right hab (by positivity))
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ -
        ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖)]
  calc ∫ x, ‖fetTD b E s X x‖ ^ 2 ∂μ
      ≤ ∫ x, 8 * (‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ ^ 2 +
          ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖ ^ 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          (((hint 0).add (hint 1)).const_mul 8) (ae_of_all _ hpt)
    _ = 8 * ((∫ x, ‖blockTrace (rlG b E s X x) 0 - fetTm b E s X 0‖ ^ 2 ∂μ) +
          ∫ x, ‖blockTrace (rlG b E s X x) 1 - fetTm b E s X 1‖ ^ 2 ∂μ) := by
        rw [integral_const_mul, integral_add (hint 0) (hint 1)]
    _ ≤ 8 * (Af ^ 2 + Af ^ 2) := by
        gcongr
        · exact fetT_g_L2 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr 0
        · exact fetT_g_L2 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr 1
    _ = 16 * Af ^ 2 := by ring

theorem fetT_N_eq (x : RlCoord W → ℝ) :
    rlLin W b s x + cmpTopH E X - diagonal (fun _ => (s : ℂ) * matchedA E) =
      rlC0 E s X + rlLin W b s x := by
  have := rl_C0_add b E s X x 0
  rw [zero_smul, add_zero, sub_zero] at this
  exact this.symm

theorem fetT_c_im_le : ((s : ℂ) * matchedA E).im ≤ -(s * y) := by
  rw [Complex.im_ofReal_mul]; nlinarith

/-- Ward identity for `G`: `Re Tr G*SG = Im Tr(SG) / Im(sa)`. -/
theorem fetT_ward_G (x : RlCoord W → ℝ) :
    fetTct S (rlG b E s X x) = (S * rlG b E s X x).trace.im / ((s : ℂ) * matchedA E).im := by
  have hc : ((s : ℂ) * matchedA E).im ≠ 0 := by
    have := fetT_c_im_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr; nlinarith [mul_pos hs hy]
  rw [fetT_G_eq_inv]
  refine fetT_ward (rl_herm_part b E s hX x) hc ?_ hS.isHermitian
  rw [fetT_N_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
  exact rl_isUnit_G b E hs hX (lt_of_lt_of_le hy hya) x

/-- Ward identity for `R = (z_∂ - X)⁻¹`. -/
theorem fetT_ward_Rp :
    fetTct S (fetTRp b E s X) = (S * fetTRp b E s X).trace.im /
      (((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E).im := by
  have hc : (((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E).im ≠ 0 := by
    have := fetT_lam_ge hW hs hα hβ hX hy hya; nlinarith [mul_pos hs hy]
  exact fetT_ward (cmpTopH_isHermitian E hX) hc (fetT_N0_isUnit hW hs hα hβ hX hy hya) hS.isHermitian

theorem fetT_ct_G_nonneg (x : RlCoord W → ℝ) : 0 ≤ fetTct S (rlG b E s X x) := fetTct_nonneg hS _

theorem fetT_ct_G_continuous : Continuous (fun x => fetTct S (rlG b E s X x)) := by
  unfold fetTct
  have hG := fetT_G_continuous hW hs hα hβ hX hy hya
  exact Complex.continuous_re.comp ((((hG.matrix_conjTranspose).mul continuous_const).mul
    hG).matrix_trace)

theorem fetT_ct_G_bound (x : RlCoord W → ℝ) :
    fetTct S (rlG b E s X x) ≤ 4 * W * ‖S‖ * (s * y)⁻¹ ^ 2 := by
  have hG := fetT_G_bound hW hs hα hβ hX hy hya x
  unfold fetTct
  refine (Complex.re_le_norm _).trans ((tfl_trace_le _).trans ?_)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  have h1 : ‖(rlG b E s X x)ᴴ * S * rlG b E s X x‖ ≤ (s * y)⁻¹ * ‖S‖ * (s * y)⁻¹ := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) hG (norm_nonneg _) (by
        have := mul_pos hs hy; positivity))
    rw [l2_opNorm_conjTranspose]; exact hG
  have hW0 : (0 : ℝ) ≤ W := by positivity
  have e : (s * y)⁻¹ * ‖S‖ * (s * y)⁻¹ = ‖S‖ * (s * y)⁻¹ ^ 2 := by ring
  rw [e] at h1
  nlinarith [norm_nonneg S, sq_nonneg (s * y)⁻¹, mul_nonneg hW0 (mul_nonneg (norm_nonneg S) (sq_nonneg (s * y)⁻¹))]

theorem fetT_ab_le : rlAlpha b s + rlBeta b s ≤ 1 := by
  unfold rlAlpha rlBeta at *; linarith

theorem fetT_Delta_bound : ‖fetTDelta b E s X‖ ≤ 2 * ((s * y)⁻¹ + 1) := by
  have ha1 := norm_matchedA hE2
  refine (fetT_norm_diag_le hα hβ _).trans ?_
  have hm : ∀ k, ‖fetTm b E s X k - matchedA E‖ ≤ (s * y)⁻¹ + 1 := fun k =>
    (norm_sub_le _ _).trans (by rw [ha1]; linarith [fetT_m_bound hW hs hα hβ hX hy hya k])
  have hab := fetT_ab_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have h0 := hm 0
  have h1 := hm 1
  have hn0 := norm_nonneg (fetTm b E s X 0 - matchedA E)
  have hn1 := norm_nonneg (fetTm b E s X 1 - matchedA E)
  nlinarith

/-- `κ_U = 1 + 2(K+1)K` bounds `‖1 + ΔM̄‖`, `‖1 + M̄Δ‖`. -/
theorem fetT_U_bound :
    ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + fetTDelta b E s X * fetTMb b E s X‖ ≤
      1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹ ∧
    ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + fetTMb b E s X * fetTDelta b E s X‖ ≤
      1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹ := by
  have hD := fetT_Delta_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hM := fetT_Mb_bound hW hs hα hβ hX hy hya
  have h1 : ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ 1 := dcv_norm_one_le
  have hK : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  constructor
  · exact (norm_add_le _ _).trans (add_le_add h1 ((norm_mul_le _ _).trans
      (mul_le_mul hD hM (norm_nonneg _) (by positivity))))
  · refine (norm_add_le _ _).trans (add_le_add h1 ((norm_mul_le _ _).trans ?_))
    calc ‖fetTMb b E s X‖ * ‖fetTDelta b E s X‖ ≤ (s * y)⁻¹ * (2 * ((s * y)⁻¹ + 1)) :=
          mul_le_mul hM hD (norm_nonneg _) hK
      _ = _ := by ring

set_option maxHeartbeats 400000 in
/-- **Mean of the residual clock**: `E u_G ≤ C₃ u`, `u = W⁻¹ Re Tr R* S R`. -/
theorem fetT_uG_mean :
    ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) ≤
      (2 * (s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) +
        ((s * y)⁻¹ * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹)) ^ 2 *
          (16 * (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2)) *
        ((W : ℝ)⁻¹ * fetTct S (fetTRp b E s X)) := by
  have hU := fetT_U_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hΔ := fetT_Delta_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hl := fetT_Mb_eq_Rp_left hW hs hα hβ hX hy hya
  have hr := fetT_Mb_eq_Rp_right hW hs hα hβ hX hy hya
  have hGb := fetT_Gb_eq hW hs hα hβ hX hy hya hα1 hβ1
  have hRn := fetT_Rp_normal hW hs hα hβ hX hy hya
  have hw := fetT_ward_Rp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hD2 := fetT_D_L2 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hI0 := fun x => fetT_ward_G hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x
  have hcle := fetT_c_im_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hctGc := fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hctGb := fetT_ct_G_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  have hGB := fetT_G_bound hW hs hα hβ hX hy hya
  have hDc := fetT_D_continuous hW hs hα hβ hX hy hya
  set μ := gaussianProduct (rlVar W b s) with hμ
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set G := rlG b E s X with hGdef
  set Mb := fetTMb b E s X
  set Rp := fetTRp b E s X
  set Δ := fetTDelta b E s X
  set κU := 1 + 2 * (K + 1) * K with hκU
  set κD := 2 * (K + 1) with hκD
  set Af := Cg * Real.sqrt 2 * (16 / W) * K ^ 2
  have hκD0 : 0 ≤ κD := by rw [hκD]; linarith
  have hκU0 : 0 ≤ κU := by rw [hκU]; nlinarith
  have hGi := fetT_G_integrable hW hs hα hβ hX hy hya
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  have hGn : ∀ x, (G x)ᴴ * G x = G x * (G x)ᴴ := fun x => fetT_G_normal hX x
  set ctR := fetTct S Rp with hctR
  have hctR0 : 0 ≤ ctR := fetTct_nonneg hS _
  set ctG := fun x => fetTct S (G x) with hctG
  have hctG0 : ∀ x, 0 ≤ ctG x := fun x => fetTct_nonneg hS _
  have hctGi : Integrable ctG μ := Integrable.of_bound hctGc.aestronglyMeasurable _
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hctG0 x)]; exact hctGb x)
  -- the integral of the residual clock through the Ward identity
  set c := ((s : ℂ) * matchedA E) with hc
  have hcpos : 0 < -c.im := by nlinarith [mul_pos hs hy]
  have htrGi : Integrable (fun x => (S * G x).trace) μ := (fetTtrL S).integrable_comp hGi
  have hI : ∫ x, ctG x ∂μ = (S * fetTGb b E s X).trace.im / c.im := by
    have e1 : ∀ x, ctG x = (S * G x).trace.im / c.im := hI0
    rw [integral_congr_ae (ae_of_all _ e1), integral_div]
    congr 1
    have e2 := integral_im (μ := μ) htrGi
    simp only [RCLike.im_to_complex] at e2
    rw [e2]
    have e3 : ∫ x, (S * G x).trace ∂μ = (S * fetTGb b E s X).trace := by
      have := (fetTtrL S).integral_comp_comm hGi
      simp only [fetTtrL_apply] at this
      exact this
    rw [e3]
  -- decomposition of `Tr(S Ḡ)`
  set E0 := ∫ x, fetTD b E s X x * G x ∂μ with hE0
  have hSMb : S * Mb = S * Rp + S * Rp * (Δ * (1 + Mb * Δ)) * Rp := by
    calc S * Mb = S * (Rp * (1 + Δ * Mb)) := by rw [← hl]
      _ = S * Rp + S * Rp * Δ * Mb := by noncomm_ring
      _ = S * Rp + S * Rp * Δ * ((1 + Mb * Δ) * Rp) := by rw [← hr]
      _ = _ := by noncomm_ring
  have hDGi : Integrable (fun x => fetTD b E s X x * G x) μ :=
    fetT_integrable_of_bound ((fetT_D_continuous hW hs hα hβ hX hy hya).mul hGc)
      (C := 8 * K * K) fun x => (norm_mul_le _ _).trans (mul_le_mul
        (hDb x) (hGB x) (norm_nonneg _) (by positivity))
  have hE0tr : (S * Mb * E0).trace = ∫ x, (S * Mb * (fetTD b E s X x * G x)).trace ∂μ := by
    have := (fetTtrL (S * Mb)).integral_comp_comm hDGi
    simp only [fetTtrL_apply] at this
    exact this.symm
  have htr : (S * fetTGb b E s X).trace = (S * Rp).trace +
      (S * Rp * (Δ * (1 + Mb * Δ)) * Rp).trace + (S * Mb * E0).trace := by
    rw [hGb, Matrix.mul_add, ← Matrix.mul_assoc, hSMb, Matrix.trace_add, Matrix.trace_add]
  -- the three bounds
  have hb1 : |(S * Rp).trace.im| ≤ ctR := by
    have hci : (((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E).im ≠ 0 := by
      have := fetT_lam_ge hW hs hα hβ hX hy hya; nlinarith [mul_pos hs hy]
    have e : (S * Rp).trace.im = ctR * (((rlAlpha b s + rlBeta b s + s : ℝ) : ℂ) * matchedA E).im := by
      rw [hw, div_mul_cancel₀ _ hci]
    rw [e, abs_mul, abs_of_nonneg hctR0]
    refine mul_le_of_le_one_right hctR0 ?_
    rw [Complex.im_ofReal_mul, abs_mul]
    have hlam0 : 0 ≤ rlAlpha b s + rlBeta b s + s := by linarith
    have hlam1 : rlAlpha b s + rlBeta b s + s ≤ 1 := by unfold rlAlpha rlBeta at *; linarith
    have ha := (Complex.abs_im_le_norm (matchedA E)).trans (le_of_eq (norm_matchedA hE2))
    rw [abs_of_nonneg hlam0]
    nlinarith [abs_nonneg (matchedA E).im]
  have hb2 : ‖(S * Rp * (Δ * (1 + Mb * Δ)) * Rp).trace‖ ≤ κD * κU * ctR := by
    have h := fetT_sandwich_normal hS Rp (Δ * (1 + Mb * Δ)) Rp hRn
    have e : Real.sqrt (fetTct S Rp) * Real.sqrt (fetTct S Rp) = ctR := Real.mul_self_sqrt hctR0
    calc _ ≤ _ := h
      _ = ‖Δ * (1 + Mb * Δ)‖ * ctR := by rw [mul_assoc, e]
      _ ≤ κD * κU * ctR := mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
          (mul_le_mul hΔ hU.2 (norm_nonneg _) (by positivity))) hctR0
  have hb3pt : ∀ x, ‖(S * Mb * (fetTD b E s X x * G x)).trace‖ ≤
      κU * Real.sqrt ctR * (‖fetTD b E s X x‖ * Real.sqrt (ctG x)) := by
    intro x
    have e : S * Mb * (fetTD b E s X x * G x) = S * Rp * ((1 + Δ * Mb) * fetTD b E s X x) * G x := by
      conv_lhs => rw [hl]
      noncomm_ring
    rw [e]
    refine (fetT_sandwich_normal hS Rp _ (G x) (hGn x)).trans ?_
    have h1 : ‖(1 + Δ * Mb) * fetTD b E s X x‖ ≤ κU * ‖fetTD b E s X x‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hU.1 (norm_nonneg _))
    calc ‖(1 + Δ * Mb) * fetTD b E s X x‖ * Real.sqrt ctR * Real.sqrt (fetTct S (G x))
        ≤ κU * ‖fetTD b E s X x‖ * Real.sqrt ctR * Real.sqrt (fetTct S (G x)) := by gcongr
      _ = _ := by ring
  -- Cauchy–Schwarz for the last term
  have hDn : Continuous (fun x => ‖fetTD b E s X x‖) := hDc.norm
  have hsq : Continuous (fun x => Real.sqrt (ctG x)) := hctGc.sqrt
  have hCS : ∫ x, ‖fetTD b E s X x‖ * Real.sqrt (ctG x) ∂μ ≤
      Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ctG x ∂μ) := by
    have h := fetT_int_mul_le (μ := μ) (f := fun x => ‖fetTD b E s X x‖) (g := fun x => Real.sqrt (ctG x))
      (fun x => norm_nonneg _) (fun x => Real.sqrt_nonneg _)
      (fetT_memLp_two_of_bound hDn.aestronglyMeasurable (C := 8 * K) fun x => by
        rw [norm_norm]; exact hDb x)
      (fetT_memLp_two_of_bound hsq.aestronglyMeasurable (C := Real.sqrt (4 * W * ‖S‖ * K ^ 2)) fun x => by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_sqrt (hctGb x))
    refine h.trans (le_of_eq ?_)
    congr 2
    exact integral_congr_ae (ae_of_all _ fun x => Real.sq_sqrt (hctG0 x))
  have hint3 : Integrable (fun x => ‖fetTD b E s X x‖ * Real.sqrt (ctG x)) μ :=
    Integrable.of_bound (hDn.mul hsq).aestronglyMeasurable (8 * K * Real.sqrt (4 * W * ‖S‖ * K ^ 2))
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
        exact mul_le_mul (hDb x)
          (Real.sqrt_le_sqrt (hctGb x)) (Real.sqrt_nonneg _) (by positivity))
  have hb3 : ‖(S * Mb * E0).trace‖ ≤ κU * Real.sqrt ctR *
      (Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂μ) * Real.sqrt (∫ x, ctG x ∂μ)) := by
    rw [hE0tr]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
      (hint3.const_mul (κU * Real.sqrt ctR)) (ae_of_all _ hb3pt)).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hCS (by positivity)
  -- assemble: `x ≤ A + B √x`
  set Xi := ∫ x, ctG x ∂μ with hXi
  have hXi0 : 0 ≤ Xi := integral_nonneg hctG0
  set D2 := ∫ x, ‖fetTD b E s X x‖ ^ 2 ∂μ with hD2def
  have hD20 : 0 ≤ D2 := integral_nonneg fun x => sq_nonneg _
  have hImle : |(S * fetTGb b E s X).trace.im| ≤
      ctR + κD * κU * ctR + κU * Real.sqrt ctR * (Real.sqrt D2 * Real.sqrt Xi) := by
    rw [htr, Complex.add_im, Complex.add_im]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hb1 ?_)) ?_)
    · exact (Complex.abs_im_le_norm _).trans hb2
    · exact (Complex.abs_im_le_norm _).trans hb3
  have hXle : Xi ≤ K * (ctR * (1 + κD * κU)) + K * κU * Real.sqrt ctR * Real.sqrt D2 * Real.sqrt Xi := by
    have hneg : (S * fetTGb b E s X).trace.im ≤ 0 := by
      have h1 : (S * fetTGb b E s X).trace.im = Xi * c.im := by
        rw [hI, div_mul_cancel₀ _ (ne_of_lt (by linarith : c.im < 0))]
      rw [h1]; exact mul_nonpos_of_nonneg_of_nonpos hXi0 (by linarith)
    have e : Xi = |(S * fetTGb b E s X).trace.im| / (-c.im) := by
      rw [abs_of_nonpos hneg, hI, neg_div_neg_eq]
    conv_lhs => rw [e]
    rw [div_le_iff₀ hcpos]
    have hK' : 1 ≤ K * (-c.im) := by
      rw [hK, ← div_eq_inv_mul, le_div_iff₀ (mul_pos hs hy)]; linarith
    have hR : 0 ≤ ctR + κD * κU * ctR + κU * Real.sqrt ctR * (Real.sqrt D2 * Real.sqrt Xi) :=
      add_nonneg (add_nonneg hctR0 (mul_nonneg (mul_nonneg hκD0 hκU0) hctR0))
        (mul_nonneg (mul_nonneg hκU0 (Real.sqrt_nonneg _))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    calc |(S * fetTGb b E s X).trace.im|
        ≤ ctR + κD * κU * ctR + κU * Real.sqrt ctR * (Real.sqrt D2 * Real.sqrt Xi) := hImle
      _ ≤ (K * (-c.im)) * (ctR + κD * κU * ctR + κU * Real.sqrt ctR * (Real.sqrt D2 * Real.sqrt Xi)) :=
          le_mul_of_one_le_left hR hK'
      _ = _ := by ring
  have hfin := fetT_sqrt_absorb hXi0 hXle
  -- conclusion
  have hu : ∫ x, fetTu b E s X S x ∂μ = (W : ℝ)⁻¹ * Xi := by
    unfold fetTu; rw [integral_const_mul]
  rw [hu]
  have hB2 : (K * κU * Real.sqrt ctR * Real.sqrt D2) ^ 2 = (K * κU) ^ 2 * D2 * ctR := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hctR0, Real.sq_sqrt hD20]; ring
  rw [hB2] at hfin
  have hD2' : (K * κU) ^ 2 * D2 * ctR ≤ (K * κU) ^ 2 * (16 * Af ^ 2) * ctR := by gcongr
  have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
  calc (W : ℝ)⁻¹ * Xi ≤ (W : ℝ)⁻¹ * (2 * (K * (ctR * (1 + κD * κU))) + (K * κU) ^ 2 * (16 * Af ^ 2) * ctR) :=
        mul_le_mul_of_nonneg_left (hfin.trans (by linarith)) hWi
    _ = _ := by ring

/-- The linear statistic `F_S(x) = W⁻¹ Tr(S G(x))`. -/
def fetTF (b E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (x : RlCoord W → ℝ) : ℂ :=
  (W : ℂ)⁻¹ * (S * rlG b E s X x).trace

/-- `‖G S G‖²_HS ≤ (Re Tr G*SG)²` for normal `G`. -/
theorem fetT_hs_GSG {G : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hG : Gᴴ * G = G * Gᴴ) :
    dcvHS (G * S * G) ≤ fetTct S G ^ 2 := by
  obtain ⟨B, hB⟩ := dcv_psd_eq hS
  have e : G * S * G = (G * Bᴴ) * (B * G) := by rw [hB]; simp only [Matrix.mul_assoc]
  rw [e]
  have h1 := dcvHS_mul_left_le (G * Bᴴ) (B * G)
  have h2 := dcv_opNorm_sq_le_hs (G * Bᴴ)
  have e1 : dcvHS (B * G) = fetTct S G := (fetTct_eq_hs hB G).symm
  have e2 : dcvHS (G * Bᴴ) = fetTct S G := by
    rw [← dcvHS_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      ← fetT_ctr_eq_hs hB, fetT_ctr_normal hG]
  rw [e1] at h1
  rw [e2] at h2
  have h3 := fetTct_nonneg hS G
  nlinarith

theorem fetT_wgn_F (x : RlCoord W → ℝ) :
    weightedGradientNorm (rlVar W b s) (fetTF b E s X S) x ≤
      Real.sqrt (6 / W) * fetTu b E s X S x := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ :=
    (((W : ℂ)⁻¹) • fetTtrL S).restrictScalars ℝ with hT
  have hTa : ∀ M, T M = (W : ℂ)⁻¹ * (S * M).trace := fun M => by
    simp [hT, fetTtrL_apply]
  have hF : fetTF b E s X S = fun x => T (rlG b E s X x) := by
    funext x; rw [hTa]; rfl
  have hder : HasFDerivAt (fetTF b E s X S) (T.comp (fderiv ℝ (rlG b E s X) x)) x := by
    rw [hF]
    exact T.hasFDerivAt.comp x ((fetT_hasFDerivAt_G hs hX hya0 x).differentiableAt.hasFDerivAt)
  unfold weightedGradientNorm
  rw [hder.fderiv]
  have hval : ∀ i, ‖(T.comp (fderiv ℝ (rlG b E s X) x)) (Pi.single i 1)‖ =
      (W : ℝ)⁻¹ * ‖((rlG b E s X x * S * rlG b E s X x) * rlLin W b s (Pi.single i 1)).trace‖ := by
    intro i
    rw [ContinuousLinearMap.comp_apply, fetT_fderiv_G hs hX hya0, hTa, norm_mul, norm_inv,
      Complex.norm_natCast, Matrix.mul_neg, Matrix.trace_neg, norm_neg]
    congr 2
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  simp only [hval]
  have hsum : ∑ i, (rlVar W b s i : ℝ) * ((W : ℝ)⁻¹ *
      ‖((rlG b E s X x * S * rlG b E s X x) * rlLin W b s (Pi.single i 1)).trace‖) ^ 2 ≤
      (W : ℝ)⁻¹ ^ 2 * (6 / W * fetTct S (rlG b E s X x) ^ 2) := by
    have h := fetT_weighted_hs_le hW (rl_TA_le hW hα hα1) (rl_TB_le hW hβ hβ1)
      (rlG b E s X x * S * rlG b E s X x)
    have h2 := fetT_hs_GSG hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr (fetT_G_normal (b := b) (E := E) (s := s) hX x)
    have e : ∑ i, (rlVar W b s i : ℝ) * ((W : ℝ)⁻¹ *
        ‖((rlG b E s X x * S * rlG b E s X x) * rlLin W b s (Pi.single i 1)).trace‖) ^ 2 =
        (W : ℝ)⁻¹ ^ 2 * ∑ i, (rlVar W b s i : ℝ) *
          ‖((rlG b E s X x * S * rlG b E s X x) * rlLin W b s (Pi.single i 1)).trace‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
  have hu0 : 0 ≤ fetTu b E s X S x := mul_nonneg (by positivity) (fetTct_nonneg hS _)
  rw [show (W : ℝ)⁻¹ ^ 2 * (6 / W * fetTct S (rlG b E s X x) ^ 2) =
      (6 / W) * fetTu b E s X S x ^ 2 by unfold fetTu; ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hu0]

/-- **Self-improving moment bound** for the residual clock: `‖u_G‖_p ≤ 2 E u_G` once
`24 (K Cg)² p ≤ W`. -/
theorem fetT_uG_Lp {p : ℝ} (hp : 1 ≤ p) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W) :
    eLpNorm (fetTu b E s X S) (ENNReal.ofReal p) (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)) := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  have hctc := fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hctb := fetT_ct_G_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hcle := fetT_c_im_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  set c := ((s : ℂ) * matchedA E) with hcdef
  have hc0 : c.im < 0 := by nlinarith [mul_pos hs hy]
  have huc : Continuous (fetTu b E s X S) := continuous_const.mul hctc
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => mul_nonneg (by positivity) (fetTct_nonneg hS _)
  have hub : ∀ x, fetTu b E s X S x ≤ (W : ℝ)⁻¹ * (4 * W * ‖S‖ * K ^ 2) := fun x =>
    mul_le_mul_of_nonneg_left (hctb x) (by positivity)
  have hui : Integrable (fetTu b E s X S) μ := Integrable.of_bound huc.aestronglyMeasurable _
    (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hu0 x)]; exact hub x)
  -- `F_S` and its properties
  set T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ :=
    (((W : ℂ)⁻¹) • fetTtrL S).restrictScalars ℝ with hT
  have hTa : ∀ M, T M = (W : ℂ)⁻¹ * (S * M).trace := fun M => by
    simp [hT, fetTtrL_apply]
  have hF : fetTF b E s X S = fun x => T (rlG b E s X x) := by
    funext x; rw [hTa]; rfl
  have hFcd : ContDiff ℝ 1 (fetTF b E s X S) := by
    rw [hF]; exact T.contDiff.comp (fetT_contDiff_G hs hX hya0)
  have hFc : Continuous (fetTF b E s X S) := hFcd.continuous
  have hFb : ∀ x, ‖fetTF b E s X S x‖ ≤ ‖T‖ * K := fun x => by
    rw [hF]; exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _))
  have hFi : Integrable (fetTF b E s X S) μ := Integrable.of_bound hFc.aestronglyMeasurable _
    (ae_of_all _ hFb)
  have hFm : MemLp (fetTF b E s X S) (ENNReal.ofReal p) μ :=
    MemLp.of_bound hFc.aestronglyMeasurable _ (ae_of_all _ hFb)
  -- `u_G = Im F_S / Im c`
  have hrel : ∀ x, fetTu b E s X S x = (fetTF b E s X S x).im / c.im := by
    intro x
    unfold fetTu fetTF
    rw [fetT_ward_G hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x]
    rw [show ((W : ℂ))⁻¹ = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, hcdef]
    simp only [Complex.im_ofReal_mul]
    ring
  have hmean : ∫ x, fetTu b E s X S x ∂μ = (∫ x, fetTF b E s X S x ∂μ).im / c.im := by
    rw [integral_congr_ae (ae_of_all _ hrel), integral_div]
    congr 1
    have := integral_im (μ := μ) hFi
    simpa only [RCLike.im_to_complex] using this
  have hpt : ∀ x, ‖fetTu b E s X S x - ∫ x', fetTu b E s X S x' ∂μ‖ ≤
      K * ‖fetTF b E s X S x - ∫ x', fetTF b E s X S x' ∂μ‖ := by
    intro x
    rw [hrel x, hmean, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_neg hc0]
    rw [div_le_iff₀ (by linarith)]
    have h1 := Complex.abs_im_le_norm (fetTF b E s X S x - ∫ x', fetTF b E s X S x' ∂μ)
    rw [Complex.sub_im] at h1
    have hK' : 1 ≤ K * (-c.im) := by
      rw [hK, ← div_eq_inv_mul, le_div_iff₀ (mul_pos hs hy)]; linarith
    nlinarith [norm_nonneg (fetTF b E s X S x - ∫ x', fetTF b E s X S x' ∂μ)]
  have hstep1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((huc.sub continuous_const).aestronglyMeasurable) (ae_of_all _ hpt) (ENNReal.ofReal p)
    (μ := μ)
  have hstep2 := hgr p hp _ (rlVar W b s) (fetTF b E s X S) hFcd hFm
  have hwgn : ∀ x, ‖weightedGradientNorm (rlVar W b s) (fetTF b E s X S) x‖ ≤
      Real.sqrt (6 / W) * ‖fetTu b E s X S x‖ := by
    intro x
    rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _),
      Real.norm_of_nonneg (hu0 x)]
    exact fetT_wgn_F hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x
  have hwm : AEStronglyMeasurable (weightedGradientNorm (rlVar W b s) (fetTF b E s X S)) μ := by
    have hc : Continuous (weightedGradientNorm (rlVar W b s) (fetTF b E s X S)) := by
      unfold weightedGradientNorm
      refine (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((((hFcd.continuous_fderiv one_ne_zero).clm_apply continuous_const)).norm.pow 2)).sqrt
    exact hc.aestronglyMeasurable
  have hstep3 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hwm (ae_of_all _ hwgn) (ENNReal.ofReal p)
    (μ := μ)
  have hfluct : eLpNorm (fun x => fetTu b E s X S x - ∫ x', fetTu b E s X S x' ∂μ)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (1 / 2) * eLpNorm (fetTu b E s X S) (ENNReal.ofReal p) μ := by
    refine hstep1.trans ?_
    refine (mul_le_mul' le_rfl hstep2).trans ?_
    refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hstep3)).trans ?_
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have := fetT_small_const hK0 hCg (by linarith) hW' hWp
    nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg (6 / W)]
  -- absorb
  set a := ∫ x, fetTu b E s X S x ∂μ with ha
  have ha0 : 0 ≤ a := integral_nonneg hu0
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hsplit : eLpNorm (fetTu b E s X S) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun _ => a) (ENNReal.ofReal p) μ +
        eLpNorm (fun x => fetTu b E s X S x - a) (ENNReal.ofReal p) μ := by
    have e : fetTu b E s X S = (fun _ => a) + fun x => fetTu b E s X S x - a := by
      funext x; simp
    conv_lhs => rw [e]
    exact eLpNorm_add_le hp1
  have hconst : eLpNorm (fun _ : RlCoord W → ℝ => a) (ENNReal.ofReal p) μ = ENNReal.ofReal a := by
    rw [eLpNorm_const _ (by positivity) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal ha0]
  have hfin : eLpNorm (fetTu b E s X S) (ENNReal.ofReal p) μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := (W : ℝ)⁻¹ * (4 * W * ‖S‖ * K ^ 2)))
      ((eLpNorm_le_of_ae_bound (C := (W : ℝ)⁻¹ *
      (4 * W * ‖S‖ * K ^ 2)) huc.aestronglyMeasurable (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hu0 x)]; exact hub x)).trans (le_of_eq ?_))
    rw [measure_univ, ENNReal.one_rpow, one_mul]
  rw [hconst] at hsplit
  exact fetT_ennreal_absorb ha0 hfin (hsplit.trans (add_le_add le_rfl hfluct))

theorem fetT_hs_smul (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    dcvHS (c • M) = ‖c‖ ^ 2 * dcvHS M := by
  unfold dcvHS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem fetTY_eq : fetTY E s S = (1 + (s : ℂ) * tgtAd E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + S := by
  unfold fetTY; rw [add_smul, one_smul]; abel

/-- Pointwise: `|h_k| ≤ |1 + s a'| K² + u_G`. -/
theorem fetT_h_pt (k : Fin 2) (x : RlCoord W → ℝ) :
    ‖fetTh b E s X S x k‖ ≤ ‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 2 + fetTu b E s X S x := by
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya x
  set G := rlG b E s X x
  have e : G * fetTY E s S * G = (1 + (s : ℂ) * tgtAd E) • (G * G) + G * S * G := by
    rw [fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  unfold fetTh
  rw [e]
  have hbt : ∀ M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, blockTrace (M + N) k =
      blockTrace M k + blockTrace N k := fun M N => (rlTrCLM W k).map_add M N
  have hbs : ∀ (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), blockTrace (c • M) k =
      c * blockTrace M k := fun c M => (rlTrCLM W k).map_smul c M
  rw [hbt, hbs]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((lct_norm_blockTrace_le _ k).trans ?_) (norm_nonneg _)
    refine (norm_mul_le _ _).trans ?_
    rw [sq]; exact mul_le_mul hGb hGb (norm_nonneg _) (by have := mul_pos hs hy; positivity)
  · rw [rl_blockTrace_proj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    unfold fetTu
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e2 : (rlProj k * (G * S * G)).trace = (S * G * rlProj k * G).trace := by
      rw [show rlProj k * (G * S * G) = (rlProj k * G) * (S * G) by simp only [Matrix.mul_assoc],
        Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e2]
    refine (fetT_sandwich_normal hS G (rlProj k) G (fetT_G_normal hX x)).trans ?_
    rw [mul_assoc, Real.mul_self_sqrt (fetTct_nonneg hS _)]
    exact mul_le_of_le_one_left (fetTct_nonneg hS _) (rl_norm_proj_le k)

theorem fetT_h_continuous (k : Fin 2) : Continuous (fun x => fetTh b E s X S x k) := by
  have hG := fetT_G_continuous hW hs hα hβ hX hy hya
  exact (rlTrCLM W k).continuous.comp ((hG.mul continuous_const).mul hG)

/-- The weighted gradient of `h_k`. -/
theorem fetT_wgn_h (k : Fin 2) (x : RlCoord W → ℝ) :
    weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k) x ≤
      Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
        Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W * fetTu b E s X S x := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  set c₁ := (1 : ℂ) + (s : ℂ) * tgtAd E
  set Y := fetTY E s S with hYdef
  set T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ := (rlTrCLM W k).restrictScalars ℝ with hT
  have hTa : ∀ M, T M = blockTrace M k := fun M => rfl
  have hF : (fun x => fetTh b E s X S x k) = fun x => T (rlG b E s X x * Y * rlG b E s X x) := rfl
  have hder : HasFDerivAt (fun x => fetTh b E s X S x k)
      (T.comp (fderiv ℝ (fun y => rlG b E s X y * Y * rlG b E s X y) x)) x := by
    rw [hF]
    exact T.hasFDerivAt.comp x (fetT_hasFDerivAt_GYG hs hX hya0 Y x)
  unfold weightedGradientNorm
  rw [hder.fderiv]
  set G := rlG b E s X x
  have hGb : ‖G‖ ≤ K := fetT_G_bound hW hs hα hβ hX hy hya x
  set Kh := G * Y * G * (rlProj k * G) + (G * rlProj k) * (G * Y * G) with hKh
  have hval : ∀ i, ‖(T.comp (fderiv ℝ (fun y => rlG b E s X y * Y * rlG b E s X y) x))
      (Pi.single i 1)‖ = (W : ℝ)⁻¹ * ‖(Kh * rlLin W b s (Pi.single i 1)).trace‖ := by
    intro i
    set Λ := rlLin W b s (Pi.single i 1)
    rw [ContinuousLinearMap.comp_apply, fetT_fderiv_GYG hs hX hya0, hTa, rl_blockTrace_proj,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    congr 1
    have e1 : (rlProj k * (-(G * Λ * G) * Y * G)).trace = -((G * Y * G * (rlProj k * G)) * Λ).trace := by
      rw [show rlProj k * (-(G * Λ * G) * Y * G) = -((rlProj k * G) * (Λ * (G * Y * G))) by noncomm_ring,
        Matrix.trace_neg, Matrix.trace_mul_comm (rlProj k * G),
        show Λ * (G * Y * G) * (rlProj k * G) = Λ * (G * Y * G * (rlProj k * G)) by noncomm_ring,
        Matrix.trace_mul_comm Λ]
    have e2 : (rlProj k * (G * Y * -(G * Λ * G))).trace = -(((G * rlProj k) * (G * Y * G)) * Λ).trace := by
      rw [show rlProj k * (G * Y * -(G * Λ * G)) = -((rlProj k * G * Y * G * Λ) * G) by noncomm_ring,
        Matrix.trace_neg, Matrix.trace_mul_comm]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2, hKh, Matrix.add_mul, Matrix.trace_add, ← neg_add, norm_neg]
  simp only [hval]
  -- the Hilbert–Schmidt bound for `Kh`
  have hGG : dcvHS (G * G) ≤ 2 * W * K ^ 4 := by
    refine (dcvHS_le_card _).trans ?_
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    have : ‖G * G‖ ≤ K ^ 2 := (norm_mul_le _ _).trans (by rw [sq]; exact mul_le_mul hGb hGb (norm_nonneg _) hK0)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith
  have hGSG := fetT_hs_GSG hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr (fetT_G_normal (b := b) (E := E) (s := s) hX x)
  have hY : G * Y * G = c₁ • (G * G) + G * S * G := by
    rw [hYdef, fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  set ct := fetTct S G
  have hHY : dcvHS (G * Y * G) ≤ 2 * (‖c₁‖ ^ 2 * (2 * W * K ^ 4)) + 2 * ct ^ 2 := by
    rw [hY]
    refine (dcvHS_add_le _ _).trans ?_
    rw [fetT_hs_smul hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
    gcongr
  have hPG : ‖rlProj k * G‖ ≤ K := (norm_mul_le _ _).trans
    (by have := rl_norm_proj_le (W := W) k; nlinarith [norm_nonneg G])
  have hGP : ‖G * rlProj k‖ ≤ K := (norm_mul_le _ _).trans
    (by have := rl_norm_proj_le (W := W) k; nlinarith [norm_nonneg G])
  have hKhs : dcvHS Kh ≤ 4 * K ^ 2 * (2 * (‖c₁‖ ^ 2 * (2 * W * K ^ 4)) + 2 * ct ^ 2) := by
    refine (dcvHS_add_le _ _).trans ?_
    have h1 := dcvHS_mul_right_le (G * Y * G) (rlProj k * G)
    have h2 := dcvHS_mul_left_le (G * rlProj k) (G * Y * G)
    have h1' : dcvHS (G * Y * G) * ‖rlProj k * G‖ ^ 2 ≤ dcvHS (G * Y * G) * K ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hPG 2) (dcvHS_nonneg _)
    have h2' : ‖G * rlProj k‖ ^ 2 * dcvHS (G * Y * G) ≤ K ^ 2 * dcvHS (G * Y * G) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hGP 2) (dcvHS_nonneg _)
    have h3 : K ^ 2 * dcvHS (G * Y * G) ≤ K ^ 2 * (2 * (‖c₁‖ ^ 2 * (2 * W * K ^ 4)) + 2 * ct ^ 2) :=
      mul_le_mul_of_nonneg_left hHY (sq_nonneg _)
    nlinarith
  have hsum : ∑ i, (rlVar W b s i : ℝ) * ((W : ℝ)⁻¹ * ‖(Kh * rlLin W b s (Pi.single i 1)).trace‖) ^ 2 ≤
      (W : ℝ)⁻¹ ^ 2 * (6 / W * (4 * K ^ 2 * (2 * (‖c₁‖ ^ 2 * (2 * W * K ^ 4)) + 2 * ct ^ 2))) := by
    have h := fetT_weighted_hs_le hW (rl_TA_le hW hα hα1) (rl_TB_le hW hβ hβ1) Kh
    have e : ∑ i, (rlVar W b s i : ℝ) * ((W : ℝ)⁻¹ * ‖(Kh * rlLin W b s (Pi.single i 1)).trace‖) ^ 2 =
        (W : ℝ)⁻¹ ^ 2 * ∑ i, (rlVar W b s i : ℝ) * ‖(Kh * rlLin W b s (Pi.single i 1)).trace‖ ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hKhs (by positivity)))
      (by positivity)
  refine (Real.sqrt_le_sqrt hsum).trans ?_
  have hu : fetTu b E s X S x = (W : ℝ)⁻¹ * ct := rfl
  have hct0 : 0 ≤ ct := fetTct_nonneg hS _
  have e : (W : ℝ)⁻¹ ^ 2 * (6 / W * (4 * K ^ 2 * (2 * (‖c₁‖ ^ 2 * (2 * W * K ^ 4)) + 2 * ct ^ 2))) =
      (Real.sqrt 96 * K ^ 3 * ‖c₁‖ / W) ^ 2 + (Real.sqrt 48 * K / Real.sqrt W * ((W : ℝ)⁻¹ * ct)) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), mul_pow, div_pow, mul_pow,
      Real.sq_sqrt (by norm_num), Real.sq_sqrt hW'.le]
    field_simp
    ring
  rw [e, hu]
  refine (Real.sqrt_le_sqrt (le_of_eq rfl)).trans ?_
  have hA : 0 ≤ Real.sqrt 96 * K ^ 3 * ‖c₁‖ / W := by positivity
  have hB : 0 ≤ Real.sqrt 48 * K / Real.sqrt W * ((W : ℝ)⁻¹ * ct) := by positivity
  calc Real.sqrt ((Real.sqrt 96 * K ^ 3 * ‖c₁‖ / W) ^ 2 + (Real.sqrt 48 * K / Real.sqrt W * ((W : ℝ)⁻¹ * ct)) ^ 2)
      ≤ Real.sqrt ((Real.sqrt 96 * K ^ 3 * ‖c₁‖ / W + Real.sqrt 48 * K / Real.sqrt W * ((W : ℝ)⁻¹ * ct)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = _ := Real.sqrt_sq (by positivity)

/-- `H̄ = E[GYG]`. -/
def fetTHb (b E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∫ x, rlG b E s X x * fetTY E s S * rlG b E s X x ∂gaussianProduct (rlVar W b s)

/-- The error of the derivative system:
`err_k = h̄_k - tr_k(R Y R) - Σ_j h̄_j tr_k(R Q̂_j R)`. -/
def fetTerr (b E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : Fin 2) : ℂ :=
  fetTtr (fetTHb b E s X S) k - blockTrace (fetTRp b E s X * fetTY E s S * fetTRp b E s X) k -
    ∑ j, fetTtr (fetTHb b E s X S) j *
      blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j * fetTRp b E s X) k

theorem fetT_F_continuous : Continuous (fun x => rlG b E s X x * fetTY E s S * rlG b E s X x) :=
  ((fetT_G_continuous hW hs hα hβ hX hy hya).mul continuous_const).mul
    (fetT_G_continuous hW hs hα hβ hX hy hya)

theorem fetT_F_bound (x : RlCoord W → ℝ) :
    ‖rlG b E s X x * fetTY E s S * rlG b E s X x‖ ≤ (s * y)⁻¹ * ‖fetTY E s S‖ * (s * y)⁻¹ := by
  have hG := fetT_G_bound hW hs hα hβ hX hy hya x
  exact (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right hG (norm_nonneg _))) hG (norm_nonneg _)
      (by have := mul_pos hs hy; positivity))

/-- **The derivative mean relation**: `H̄ = M̄ (Y Ḡ + diag φ(h̄) Ḡ + E[D GYG] + E[diag φ(h - h̄) G])`. -/
theorem fetT_Hb_eq :
    fetTHb b E s X S = fetTMb b E s X *
      (fetTY E s S * fetTGb b E s X +
        fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (fetTHb b E s X S)) * fetTGb b E s X +
        (∫ x, fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x)
          ∂gaussianProduct (rlVar W b s)) +
        ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s)
            (fun k => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) k -
              fetTtr (fetTHb b E s X S) k) * rlG b E s X x ∂gaussianProduct (rlVar W b s)) := by
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hid := fetT_deriv_identity hW hs hα hβ hX hy hya (fetTY E s S)
  have hGi := fetT_G_integrable hW hs hα hβ hX hy hya
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  set F := fun x => rlG b E s X x * fetTY E s S * rlG b E s X x with hFdef
  have hFc : Continuous F := fetT_F_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hFb : ∀ x, ‖F x‖ ≤ K * ‖fetTY E s S‖ * K := fetT_F_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hFi : Integrable F μ := fetT_integrable_of_bound hFc hFb
  set Dm : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fetTdiag (rlAlpha b s) (rlBeta b s) (fetTm b E s X)
  set hb := fetTtr (fetTHb b E s X S) with hhb
  set Dh : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := fetTdiag (rlAlpha b s) (rlBeta b s) hb
  have hDc := fetT_D_continuous hW hs hα hβ hX hy hya
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  have hDFi : Integrable (fun x => fetTD b E s X x * F x) μ :=
    fetT_integrable_of_bound (hDc.mul hFc) (C := 8 * K * (K * ‖fetTY E s S‖ * K)) fun x =>
      (norm_mul_le _ _).trans (mul_le_mul (hDb x) (hFb x) (norm_nonneg _) (by positivity))
  have hcd := fetT_continuous_diag (W := W) (rlAlpha b s) (rlBeta b s)
  have hE2c : Continuous (fun x => fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun k => fetTtr (F x) k - hb k) * rlG b E s X x) := by
    have e : (fun x => fetTdiag (rlAlpha b s) (rlBeta b s) (fun k => fetTtr (F x) k - hb k) *
        rlG b E s X x) = fun x => (fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (F x)) - Dh) *
          rlG b E s X x := by
      funext x; rw [fetTdiag_sub]
    rw [e]
    exact ((hcd.comp hFc).sub continuous_const).mul hGc
  have hE2b : ∀ x, ‖fetTdiag (rlAlpha b s) (rlBeta b s) (fun k => fetTtr (F x) k - hb k) *
      rlG b E s X x‖ ≤ (2 * (2 * (2 * (K * ‖fetTY E s S‖ * K)))) * K := by
    intro x
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ (hGb x) (norm_nonneg _) (by positivity))
    refine (fetT_norm_diag_le hα hβ _).trans ?_
    have hab : rlAlpha b s + rlBeta b s ≤ 2 := by linarith
    have hhbk : ∀ k, ‖hb k‖ ≤ K * ‖fetTY E s S‖ * K := fun k => by
      rw [hhb]
      refine (lct_norm_blockTrace_le _ k).trans ((norm_integral_le_integral_norm _).trans ?_)
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _)
        (ae_of_all _ hFb)).trans (le_of_eq ?_)
      rw [integral_const, probReal_univ, one_smul]
    have hk : ∀ k, ‖fetTtr (F x) k - hb k‖ ≤ 2 * (K * ‖fetTY E s S‖ * K) := fun k =>
      (norm_sub_le _ _).trans (by
        have := (lct_norm_blockTrace_le (F x) k).trans (hFb x)
        have := hhbk k
        unfold fetTtr; linarith)
    have h0 := hk 0
    have h1 := hk 1
    have hn0 := norm_nonneg (fetTtr (F x) 0 - hb 0)
    have hn1 := norm_nonneg (fetTtr (F x) 1 - hb 1)
    nlinarith [norm_nonneg (fetTY E s S)]
  have hE2i : Integrable (fun x => fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun k => fetTtr (F x) k - hb k) * rlG b E s X x) μ := fetT_integrable_of_bound hE2c hE2b
  have hs1 : ∀ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (rlG b E s X x)) * F x =
      Dm * F x + fetTD b E s X x * F x := by
    intro x; rw [fetT_D_eq hW hs hα hβ hX hy hya, ← Matrix.add_mul]; congr 1; abel
  have hs2 : ∀ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fetTtr (F x)) * rlG b E s X x =
      Dh * rlG b E s X x + fetTdiag (rlAlpha b s) (rlBeta b s)
        (fun k => fetTtr (F x) k - hb k) * rlG b E s X x := by
    intro x; rw [fetTdiag_sub, ← Matrix.add_mul]; congr 1; abel
  have hI1 : ∫ x, Dm * F x ∂μ = Dm * ∫ x, F x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Dm).integral_comp_comm hFi
  have hI2 : ∫ x, Dh * rlG b E s X x ∂μ = Dh * ∫ x, rlG b E s X x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Dh).integral_comp_comm hGi
  rw [integral_congr_ae (ae_of_all _ hs1), integral_add (hFi.const_mul Dm) hDFi, hI1,
    integral_congr_ae (ae_of_all _ hs2), integral_add (hGi.const_mul Dh) hE2i, hI2] at hid
  have hN1 : rlC0 E s X - Dm = cmpTopH E X - diagonal (cmpExt
      (rlShift s (rlAlpha b s) (rlBeta b s) (matchedA E) (fetTm b E s X))) :=
    rl_C0_sub E s _ _ X _
  have hMN : fetTMb b E s X * (rlC0 E s X - Dm) = 1 := by
    rw [hN1]; exact nonsing_inv_mul _ (fetT_N1_isUnit hW hs hα hβ hX hy hya)
  have hmain : (rlC0 E s X - Dm) * fetTHb b E s X S =
      fetTY E s S * fetTGb b E s X + Dh * fetTGb b E s X +
        (∫ x, fetTD b E s X x * F x ∂μ) +
        ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s) (fun k => fetTtr (F x) k - hb k) *
          rlG b E s X x ∂μ := by
    rw [Matrix.sub_mul]
    unfold fetTHb fetTGb
    rw [← hid]
    abel
  calc fetTHb b E s X S = (fetTMb b E s X * (rlC0 E s X - Dm)) * fetTHb b E s X S := by
        rw [hMN, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, hmain]

theorem fetT_Gb_bound : ‖fetTGb b E s X‖ ≤ (s * y)⁻¹ := by
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  unfold fetTGb
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_of_nonneg
    (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _) (ae_of_all _ hGb)).trans (le_of_eq ?_))
  rw [integral_const, probReal_univ, one_smul]

theorem fetT_Mb_sub_Rp : ‖fetTMb b E s X - fetTRp b E s X‖ ≤ (s * y)⁻¹ ^ 2 * ‖fetTDelta b E s X‖ := by
  have hl := fetT_Mb_eq_Rp_left hW hs hα hβ hX hy hya
  have e : fetTMb b E s X - fetTRp b E s X = fetTRp b E s X * fetTDelta b E s X * fetTMb b E s X := by
    conv_lhs => rw [hl]
    noncomm_ring
  rw [e]
  have h1 := fetT_Rp_bound hW hs hα hβ hX hy hya
  have h2 := fetT_Mb_bound hW hs hα hβ hX hy hya
  refine (norm_mul_le _ _).trans ?_
  calc ‖fetTRp b E s X * fetTDelta b E s X‖ * ‖fetTMb b E s X‖
      ≤ ((s * y)⁻¹ * ‖fetTDelta b E s X‖) * (s * y)⁻¹ :=
        mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))) h2
          (norm_nonneg _) (by have := mul_pos hs hy; positivity)
    _ = _ := by ring

theorem fetT_D_int_le :
    ∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s) ≤
      Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂gaussianProduct (rlVar W b s)) := by
  have hDc := (fetT_D_continuous hW hs hα hβ hX hy hya).norm
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  have h := fetT_int_mul_le (μ := gaussianProduct (rlVar W b s)) (f := fun x => ‖fetTD b E s X x‖)
    (g := fun _ => (1 : ℝ)) (fun x => norm_nonneg _) (fun _ => zero_le_one)
    (fetT_memLp_two_of_bound hDc.aestronglyMeasurable (C := 8 * (s * y)⁻¹) fun x => by
      rw [norm_norm]; exact hDb x)
    (fetT_memLp_two_of_bound aestronglyMeasurable_const (C := 1) fun _ => by norm_num)
  simp only [mul_one, one_pow, integral_const, probReal_univ, one_smul, Real.sqrt_one] at h
  exact h

theorem fetT_Gb_sub_Mb : ‖fetTGb b E s X - fetTMb b E s X‖ ≤
    (s * y)⁻¹ ^ 2 * ∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s) := by
  set μ := gaussianProduct (rlVar W b s)
  have hGB := fetT_Gb_eq hW hs hα hβ hX hy hya hα1 hβ1
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  have hM := fetT_Mb_bound hW hs hα hβ hX hy hya
  have hK0 : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have hDc := fetT_D_continuous hW hs hα hβ hX hy hya
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  rw [hGB, add_sub_cancel_left]
  refine (norm_mul_le _ _).trans ?_
  have hint : ‖∫ x, fetTD b E s X x * rlG b E s X x ∂μ‖ ≤ (s * y)⁻¹ * ∫ x, ‖fetTD b E s X x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hi : Integrable (fun x => ‖fetTD b E s X x‖) μ := Integrable.of_bound hDc.norm.aestronglyMeasurable
      (8 * (s * y)⁻¹) (ae_of_all _ fun x => by rw [norm_norm]; exact hDb x)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.const_mul _)
      (ae_of_all _ fun x => ?_)
    refine (norm_mul_le _ _).trans ?_
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
  calc ‖fetTMb b E s X‖ * ‖∫ x, fetTD b E s X x * rlG b E s X x ∂μ‖
      ≤ (s * y)⁻¹ * ((s * y)⁻¹ * ∫ x, ‖fetTD b E s X x‖ ∂μ) :=
        mul_le_mul hM hint (norm_nonneg _) hK0
    _ = _ := by ring

/-- **(A)** `|tr_k(M̄ Z Ḡ) - tr_k(R Z R)| ≤ K(2‖M̄ - R‖ + ‖Ḡ - M̄‖)` for `‖Z‖ ≤ 1`. -/
theorem fetT_err_Z (Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hZ : ‖Z‖ ≤ 1) (k : Fin 2) :
    ‖blockTrace (fetTMb b E s X * Z * fetTGb b E s X) k -
        blockTrace (fetTRp b E s X * Z * fetTRp b E s X) k‖ ≤
      (s * y)⁻¹ * (2 * ‖fetTMb b E s X - fetTRp b E s X‖ + ‖fetTGb b E s X - fetTMb b E s X‖) := by
  rw [fetT_bt_sub]
  refine (lct_norm_blockTrace_le _ k).trans ?_
  set Mb := fetTMb b E s X
  set Rp := fetTRp b E s X
  set Gb := fetTGb b E s X
  have e : Mb * Z * Gb - Rp * Z * Rp = (Mb - Rp) * Z * Gb + Rp * Z * ((Gb - Mb) + (Mb - Rp)) := by
    noncomm_ring
  rw [e]
  have hG := fetT_Gb_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hR := fetT_Rp_bound hW hs hα hβ hX hy hya
  have hK0 : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have h1 : ‖(Mb - Rp) * Z * Gb‖ ≤ ‖Mb - Rp‖ * (s * y)⁻¹ := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hG (norm_nonneg _)
      (norm_nonneg _))
    exact mul_le_of_le_one_right (norm_nonneg _) hZ
  have h2 : ‖Rp * Z * ((Gb - Mb) + (Mb - Rp))‖ ≤ (s * y)⁻¹ * (‖Gb - Mb‖ + ‖Mb - Rp‖) := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) (norm_add_le _ _)
      (norm_nonneg _) hK0)
    exact (mul_le_of_le_one_right (norm_nonneg _) hZ).trans hR
  calc _ ≤ ‖(Mb - Rp) * Z * Gb‖ + ‖Rp * Z * ((Gb - Mb) + (Mb - Rp))‖ := norm_add_le _ _
    _ ≤ ‖Mb - Rp‖ * (s * y)⁻¹ + (s * y)⁻¹ * (‖Gb - Mb‖ + ‖Mb - Rp‖) := add_le_add h1 h2
    _ = _ := by ring

/-- **(B)** the source term: `|tr_k(M̄ S Ḡ) - tr_k(R S R)| ≤ u(κ_U²K‖Δ‖ + ‖Δ‖κ_U K + κ_U²K E‖D‖)`. -/
theorem fetT_err_S (k : Fin 2) :
    ‖blockTrace (fetTMb b E s X * S * fetTGb b E s X) k -
        blockTrace (fetTRp b E s X * S * fetTRp b E s X) k‖ ≤
      ((W : ℝ)⁻¹ * fetTct S (fetTRp b E s X)) *
        ((1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) ^ 2 * (s * y)⁻¹ * ‖fetTDelta b E s X‖ +
          ‖fetTDelta b E s X‖ * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) * (s * y)⁻¹ +
          (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) ^ 2 * (s * y)⁻¹ *
            ∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s)) := by
  have hU := fetT_U_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hl := fetT_Mb_eq_Rp_left hW hs hα hβ hX hy hya
  have hr := fetT_Mb_eq_Rp_right hW hs hα hβ hX hy hya
  have hGB := fetT_Gb_eq hW hs hα hβ hX hy hya hα1 hβ1
  have hRn := fetT_Rp_normal hW hs hα hβ hX hy hya
  have hR := fetT_Rp_bound hW hs hα hβ hX hy hya
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  have hDc := fetT_D_continuous hW hs hα hβ hX hy hya
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  set Mb := fetTMb b E s X
  set Rp := fetTRp b E s X
  set Δ := fetTDelta b E s X
  set U := (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + Δ * Mb with hUdef
  set U' := (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + Mb * Δ with hU'def
  set κU := 1 + 2 * (K + 1) * K
  set ct := fetTct S Rp
  have hct0 : 0 ≤ ct := fetTct_nonneg hS _
  have hκU0 : 0 ≤ κU := by positivity
  set E0 := ∫ x, fetTD b E s X x * rlG b E s X x ∂μ
  -- decomposition
  have hMbS : Mb * S * Mb - Rp * S * Rp =
      Rp * (Δ * U') * Rp * S * Rp * U + Rp * S * Rp * (Δ * U') * Rp := by
    have e1 : Mb - Rp = Rp * Δ * (U' * Rp) := by
      rw [← hr]
      calc Mb - Rp = Rp * U - Rp := by rw [← hl]
        _ = Rp * Δ * Mb := by rw [hUdef]; noncomm_ring
    have e2 : Mb = Rp + (Mb - Rp) := by abel
    have e3 : Mb = Rp * U := hl
    calc Mb * S * Mb - Rp * S * Rp = (Mb - Rp) * S * Mb + Rp * S * (Mb - Rp) := by noncomm_ring
      _ = Rp * Δ * (U' * Rp) * S * (Rp * U) + Rp * S * (Rp * Δ * (U' * Rp)) := by
          rw [e1]; conv_lhs => rw [show (Rp * Δ * (U' * Rp)) * S * Mb = (Rp * Δ * (U' * Rp)) * S * (Rp * U) by rw [← e3]]
      _ = _ := by noncomm_ring
  have htr1 : ‖blockTrace (Rp * (Δ * U') * Rp * S * Rp * U) k‖ ≤
      (W : ℝ)⁻¹ * (κU ^ 2 * K * ‖Δ‖ * ct) := by
    rw [rl_blockTrace_proj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : (rlProj k * (Rp * (Δ * U') * Rp * S * Rp * U)).trace =
        (S * Rp * (U * rlProj k * Rp * (Δ * U')) * Rp).trace := by
      rw [show rlProj k * (Rp * (Δ * U') * Rp * S * Rp * U) =
          (rlProj k * Rp * (Δ * U') * Rp) * (S * Rp * U) by noncomm_ring, Matrix.trace_mul_comm]
      congr 1; noncomm_ring
    rw [e]
    refine (fetT_sandwich_normal hS Rp _ Rp hRn).trans ?_
    rw [mul_assoc, Real.mul_self_sqrt hct0]
    refine mul_le_mul_of_nonneg_right ?_ hct0
    have hP := rl_norm_proj_le (W := W) k
    calc ‖U * rlProj k * Rp * (Δ * U')‖ ≤ ‖U‖ * 1 * K * (‖Δ‖ * κU) := by
          refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (norm_nonneg _))) hR
            (norm_nonneg _) (by positivity))) ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
              hU.2 (norm_nonneg _))) (norm_nonneg _) (by positivity))
      _ ≤ κU * 1 * K * (‖Δ‖ * κU) := by gcongr; exact hU.1
      _ = κU ^ 2 * K * ‖Δ‖ := by ring
  have htr2 : ‖blockTrace (Rp * S * Rp * (Δ * U') * Rp) k‖ ≤ (W : ℝ)⁻¹ * (‖Δ‖ * κU * K * ct) := by
    rw [rl_blockTrace_proj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : (rlProj k * (Rp * S * Rp * (Δ * U') * Rp)).trace =
        (S * Rp * ((Δ * U') * Rp * rlProj k) * Rp).trace := by
      rw [show rlProj k * (Rp * S * Rp * (Δ * U') * Rp) = (rlProj k * Rp) * (S * Rp * (Δ * U') * Rp) by
          noncomm_ring, Matrix.trace_mul_comm]
      congr 1; noncomm_ring
    rw [e]
    refine (fetT_sandwich_normal hS Rp _ Rp hRn).trans ?_
    rw [mul_assoc, Real.mul_self_sqrt hct0]
    refine mul_le_mul_of_nonneg_right ?_ hct0
    have hP := rl_norm_proj_le (W := W) k
    calc ‖Δ * U' * Rp * rlProj k‖ ≤ ‖Δ‖ * κU * K * 1 := by
          refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hU.2 (norm_nonneg _))) hR
            (norm_nonneg _) (by positivity))) hP (norm_nonneg _) (by positivity))
      _ = _ := by ring
  -- the `E₀` term
  have hDGi : Integrable (fun x => fetTD b E s X x * rlG b E s X x) μ :=
    fetT_integrable_of_bound (hDc.mul hGc) (C := 8 * K * K) fun x =>
      (norm_mul_le _ _).trans (mul_le_mul (hDb x) (hGb x) (norm_nonneg _) (by positivity))
  have hE0 : blockTrace (Mb * S * Mb * E0) k =
      ∫ x, blockTrace (Mb * S * Mb * (fetTD b E s X x * rlG b E s X x)) k ∂μ := by
    have h1 := (rlTrCLM W k).integral_comp_comm
      (((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (Mb * S * Mb)).integrable_comp hDGi))
    have h2 := (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (Mb * S * Mb)).integral_comp_comm hDGi
    simp only [rlTrCLM_apply, ContinuousLinearMap.mul_apply'] at h1 h2
    rw [h1, h2]
  have hpt : ∀ x, ‖blockTrace (Mb * S * Mb * (fetTD b E s X x * rlG b E s X x)) k‖ ≤
      (W : ℝ)⁻¹ * (κU ^ 2 * K * ‖fetTD b E s X x‖ * ct) := by
    intro x
    rw [rl_blockTrace_proj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e : (rlProj k * (Mb * S * Mb * (fetTD b E s X x * rlG b E s X x))).trace =
        (S * Rp * (U * fetTD b E s X x * rlG b E s X x * rlProj k * U') * Rp).trace := by
      rw [show rlProj k * (Mb * S * Mb * (fetTD b E s X x * rlG b E s X x)) =
          (rlProj k * Mb) * (S * Mb * (fetTD b E s X x * rlG b E s X x)) by noncomm_ring,
        Matrix.trace_mul_comm]
      have h3 : Mb = Rp * U := hl
      have h4 : Mb = U' * Rp := hr
      calc (S * Mb * (fetTD b E s X x * rlG b E s X x) * (rlProj k * Mb)).trace
          = (S * (Rp * U) * (fetTD b E s X x * rlG b E s X x) * (rlProj k * (U' * Rp))).trace := by
            rw [← h3, ← h4]
        _ = _ := by congr 1; noncomm_ring
    rw [e]
    refine (fetT_sandwich_normal hS Rp _ Rp hRn).trans ?_
    rw [mul_assoc, Real.mul_self_sqrt hct0]
    refine mul_le_mul_of_nonneg_right ?_ hct0
    have hP := rl_norm_proj_le (W := W) k
    calc ‖U * fetTD b E s X x * rlG b E s X x * rlProj k * U'‖
        ≤ κU * ‖fetTD b E s X x‖ * K * 1 * κU := by
          refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
            ((norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
              hU.1 (norm_nonneg _))) (hGb x) (norm_nonneg _) (by positivity))) hP (norm_nonneg _)
              (by positivity))) hU.2 (norm_nonneg _) (by positivity))
      _ = κU ^ 2 * K * ‖fetTD b E s X x‖ := by ring
  have hDi : Integrable (fun x => ‖fetTD b E s X x‖) μ := Integrable.of_bound hDc.norm.aestronglyMeasurable
    (8 * K) (ae_of_all _ fun x => by rw [norm_norm]; exact hDb x)
  have hE0b : ‖blockTrace (Mb * S * Mb * E0) k‖ ≤
      (W : ℝ)⁻¹ * (κU ^ 2 * K * (∫ x, ‖fetTD b E s X x‖ ∂μ) * ct) := by
    rw [hE0]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      ((hDi.const_mul (κU ^ 2 * K)).mul_const ct |>.const_mul _) (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_mul_const, integral_const_mul]
  -- assemble
  have hsplit : blockTrace (Mb * S * fetTGb b E s X) k - blockTrace (Rp * S * Rp) k =
      blockTrace (Rp * (Δ * U') * Rp * S * Rp * U) k + blockTrace (Rp * S * Rp * (Δ * U') * Rp) k +
        blockTrace (Mb * S * Mb * E0) k := by
    rw [hGB, Matrix.mul_add, ← Matrix.mul_assoc, fetT_bt_sub, show Mb * S * Mb + Mb * S * Mb * E0 -
      Rp * S * Rp = (Mb * S * Mb - Rp * S * Rp) + Mb * S * Mb * E0 by abel, hMbS]
    have hadd : ∀ A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, blockTrace (A + B) k =
        blockTrace A k + blockTrace B k := fun A B => (rlTrCLM W k).map_add A B
    rw [hadd, hadd]
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add htr1 htr2))
    hE0b).trans (le_of_eq ?_))
  ring

/-- **Noise of the derivative trace**:
`‖h_k - E h_k‖_p ≤ Cg √p (√96 K³|1 + sa'|/W + √48 K/√W · 2 E u_G)` once `24 (K Cg)² p ≤ W`. -/
theorem fetT_noise (k : Fin 2) {p : ℝ} (hp : 1 ≤ p) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W) :
    eLpNorm (fun x => fetTh b E s X S x k - ∫ x', fetTh b E s X S x' k ∂gaussianProduct (rlVar W b s))
        (ENNReal.ofReal p) (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
        Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W *
          (2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)))) := by
  have hya0 : 0 < -(matchedA E).im := lt_of_lt_of_le hy hya
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  set T : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ →L[ℝ] ℂ := (rlTrCLM W k).restrictScalars ℝ with hT
  have hF : (fun x => fetTh b E s X S x k) = fun x => T (rlG b E s X x * fetTY E s S * rlG b E s X x) := rfl
  have hcd : ContDiff ℝ 1 (fun x => fetTh b E s X S x k) := by
    rw [hF]; exact T.contDiff.comp (fetT_contDiff_GYG hs hX hya0 _)
  have hc := hcd.continuous
  have hb : ∀ x, ‖fetTh b E s X S x k‖ ≤ K * ‖fetTY E s S‖ * K := fun x =>
    (lct_norm_blockTrace_le _ k).trans (fetT_F_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x)
  have hm : MemLp (fun x => fetTh b E s X S x k) (ENNReal.ofReal p) μ :=
    MemLp.of_bound hc.aestronglyMeasurable _ (ae_of_all _ hb)
  have h1 := hgr p hp _ (rlVar W b s) _ hcd hm
  refine h1.trans ?_
  set A := Real.sqrt 96 * K ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W
  set B := Real.sqrt 48 * K / Real.sqrt W
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => mul_nonneg (by positivity) (fetTct_nonneg hS _)
  have huc : Continuous (fetTu b E s X S) :=
    continuous_const.mul (fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hwgn : ∀ x, ‖weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k) x‖ ≤
      ‖A + B * fetTu b E s X S x‖ := by
    intro x
    rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _),
      Real.norm_of_nonneg (add_nonneg hA0 (mul_nonneg hB0 (hu0 x)))]
    exact fetT_wgn_h hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k x
  have hwm : AEStronglyMeasurable (weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k)) μ := by
    have : Continuous (weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k)) := by
      unfold weightedGradientNorm
      exact (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((((hcd.continuous_fderiv one_ne_zero).clm_apply continuous_const)).norm.pow 2)).sqrt
    exact this.aestronglyMeasurable
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have h2 : eLpNorm (weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k))
      (ENNReal.ofReal p) μ ≤ eLpNorm (fun x => A + B * fetTu b E s X S x) (ENNReal.ofReal p) μ :=
    eLpNorm_mono hwm hwgn
  have h3 : eLpNorm (fun x => A + B * fetTu b E s X S x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal A + ENNReal.ofReal B * eLpNorm (fetTu b E s X S) (ENNReal.ofReal p) μ := by
    have e : (fun x => A + B * fetTu b E s X S x) = (fun _ => A) + (fun x => B * fetTu b E s X S x) := rfl
    rw [e]
    refine (eLpNorm_add_le hp1).trans (add_le_add (le_of_eq ?_) ?_)
    · rw [eLpNorm_const _ (by positivity) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one,
        Real.enorm_eq_ofReal hA0]
    · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (huc.aestronglyMeasurable.const_mul B)
        (ae_of_all _ fun x => by rw [norm_mul, Real.norm_of_nonneg hB0]) _
  have h4 := fetT_uG_Lp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hp hWp
  have hI0 : 0 ≤ ∫ x, fetTu b E s X S x ∂μ := integral_nonneg hu0
  calc ENNReal.ofReal (Cg * Real.sqrt p) *
        eLpNorm (weightedGradientNorm (rlVar W b s) (fun x => fetTh b E s X S x k)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal A + ENNReal.ofReal B *
          ENNReal.ofReal (2 * ∫ x, fetTu b E s X S x ∂μ)) :=
        mul_le_mul' le_rfl (h2.trans (h3.trans (add_le_add le_rfl (mul_le_mul' le_rfl h4))))
    _ = _ := by
        rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_add hA0 (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-- **(C)** `|tr_k(M̄ E[D GYG])| ≤ |1+sa'| K³ E‖D‖ + K √E‖D‖² √E u_G²`. -/
theorem fetT_err_e1 (k : Fin 2) :
    ‖blockTrace (fetTMb b E s X * ∫ x, fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x)
        ∂gaussianProduct (rlVar W b s)) k‖ ≤
      ‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 3 * (∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s)) +
        (s * y)⁻¹ * (Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂gaussianProduct (rlVar W b s)) *
          Real.sqrt (∫ x, fetTu b E s X S x ^ 2 ∂gaussianProduct (rlVar W b s))) := by
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  have hM := fetT_Mb_bound hW hs hα hβ hX hy hya
  have hDc := fetT_D_continuous hW hs hα hβ hX hy hya
  have hDb := fetT_D_bound hW hs hα hβ hX hy hya hα1 hβ1
  have hFc := fetT_F_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hFb := fetT_F_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  set Mb := fetTMb b E s X
  set c₁ := (1 : ℂ) + (s : ℂ) * tgtAd E
  have hDFi : Integrable (fun x => fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x)) μ :=
    fetT_integrable_of_bound (hDc.mul hFc) (C := 8 * K * (K * ‖fetTY E s S‖ * K)) fun x =>
      (norm_mul_le _ _).trans (mul_le_mul (hDb x) (hFb x) (norm_nonneg _) (by positivity))
  have hcomm : blockTrace (Mb * ∫ x, fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x) ∂μ) k =
      ∫ x, blockTrace (Mb * (fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x))) k ∂μ := by
    have h1 := (rlTrCLM W k).integral_comp_comm
      (((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Mb).integrable_comp hDFi))
    have h2 := (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Mb).integral_comp_comm hDFi
    simp only [rlTrCLM_apply, ContinuousLinearMap.mul_apply'] at h1 h2
    rw [h1, h2]
  have hpt : ∀ x, ‖blockTrace (Mb * (fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x))) k‖ ≤
      ‖c₁‖ * K ^ 3 * ‖fetTD b E s X x‖ + K * (‖fetTD b E s X x‖ * fetTu b E s X S x) := by
    intro x
    set G := rlG b E s X x
    set D := fetTD b E s X x
    have e : Mb * (D * (G * fetTY E s S * G)) = c₁ • (Mb * D * G * G) + Mb * D * G * S * G := by
      rw [fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.mul_assoc]
      rfl
    rw [e, ← rlTrCLM_apply, map_add, map_smul, rlTrCLM_apply, rlTrCLM_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, show ‖c₁‖ * K ^ 3 * ‖D‖ = ‖c₁‖ * (K ^ 3 * ‖D‖) by ring]
      refine mul_le_mul_of_nonneg_left ((lct_norm_blockTrace_le (Mb * D * G * G) k).trans ?_)
        (norm_nonneg c₁)
      calc ‖Mb * D * G * G‖ ≤ K * ‖D‖ * K * K := by
            refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))) (hGb x)
              (norm_nonneg _) (by positivity))) (hGb x) (norm_nonneg _) (by positivity))
        _ = K ^ 3 * ‖D‖ := by ring
    · rw [rl_blockTrace_proj, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have e2 : (rlProj k * (Mb * D * G * S * G)).trace = (S * G * (rlProj k * Mb * D) * G).trace := by
        rw [show rlProj k * (Mb * D * G * S * G) = (rlProj k * Mb * D * G) * (S * G) by noncomm_ring,
          Matrix.trace_mul_comm]
        congr 1; noncomm_ring
      rw [e2]
      have h0 := fetT_sandwich_normal hS G (rlProj k * Mb * D) G (fetT_G_normal hX x)
      have h : ‖(S * G * (rlProj k * Mb * D) * G).trace‖ ≤ ‖rlProj k * Mb * D‖ * fetTct S G :=
        h0.trans (le_of_eq (by rw [mul_assoc, Real.mul_self_sqrt (fetTct_nonneg hS _)]))
      have hP := rl_norm_proj_le (W := W) k
      have hZ : ‖rlProj k * Mb * D‖ ≤ K * ‖D‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
          (by nlinarith [norm_nonneg Mb])) (norm_nonneg _))
      unfold fetTu
      calc (W : ℝ)⁻¹ * ‖(S * G * (rlProj k * Mb * D) * G).trace‖
          ≤ (W : ℝ)⁻¹ * (‖rlProj k * Mb * D‖ * fetTct S G) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ ≤ (W : ℝ)⁻¹ * (K * ‖D‖ * fetTct S G) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ (fetTct_nonneg hS _)) (by positivity)
        _ = _ := by ring
  have hDi : Integrable (fun x => ‖fetTD b E s X x‖) μ := Integrable.of_bound hDc.norm.aestronglyMeasurable
    (8 * K) (ae_of_all _ fun x => by rw [norm_norm]; exact hDb x)
  have huc : Continuous (fetTu b E s X S) :=
    continuous_const.mul (fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => mul_nonneg (by positivity) (fetTct_nonneg hS _)
  have hub : ∀ x, ‖fetTu b E s X S x‖ ≤ (W : ℝ)⁻¹ * (4 * W * ‖S‖ * K ^ 2) := fun x => by
    rw [Real.norm_of_nonneg (hu0 x)]
    exact mul_le_mul_of_nonneg_left (fetT_ct_G_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x)
      (by positivity)
  have hDui : Integrable (fun x => ‖fetTD b E s X x‖ * fetTu b E s X S x) μ :=
    Integrable.of_bound (hDc.norm.mul huc).aestronglyMeasurable (8 * K * ((W : ℝ)⁻¹ * (4 * W * ‖S‖ * K ^ 2)))
      (ae_of_all _ fun x => by
        rw [norm_mul, norm_norm]
        exact mul_le_mul (hDb x) (hub x) (norm_nonneg _) (by positivity))
  rw [hcomm]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
    ((hDi.const_mul _).fun_add (hDui.const_mul K)) (ae_of_all _ hpt)).trans ?_
  rw [integral_add (hDi.const_mul _) (hDui.const_mul K), integral_const_mul, integral_const_mul]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hK0)
  exact fetT_int_mul_le (fun x => norm_nonneg _) hu0
    (fetT_memLp_two_of_bound hDc.norm.aestronglyMeasurable (C := 8 * K) fun x => by
      rw [norm_norm]; exact hDb x)
    (fetT_memLp_two_of_bound huc.aestronglyMeasurable hub)

theorem fetT_hb_eq (j : Fin 2) :
    fetTtr (fetTHb b E s X S) j = ∫ x, fetTh b E s X S x j ∂gaussianProduct (rlVar W b s) := by
  have hFi : Integrable (fun x => rlG b E s X x * fetTY E s S * rlG b E s X x)
      (gaussianProduct (rlVar W b s)) :=
    fetT_integrable_of_bound (fetT_F_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
      (fetT_F_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  unfold fetTtr fetTHb fetTh
  rw [← rlTrCLM_apply, ← (rlTrCLM W j).integral_comp_comm hFi]
  rfl

/-- **(D)** the covariance term: `|tr_k(M̄ E[diag φ(h - h̄) G])| ≤ 2 N₂ B`. -/
theorem fetT_err_e2 (k : Fin 2) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * 2 ≤ W) :
    ‖blockTrace (fetTMb b E s X * ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s)
        (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j -
          fetTtr (fetTHb b E s X S) j) * rlG b E s X x ∂gaussianProduct (rlVar W b s)) k‖ ≤
      2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
        Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W *
          (2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)))) *
        (Cg * Real.sqrt 2 * (16 * (s * y)⁻¹ / W) * (s * y)⁻¹ ^ 2)) := by
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hGb := fetT_G_bound hW hs hα hβ hX hy hya
  have hGc := fetT_G_continuous hW hs hα hβ hX hy hya
  have hGi := fetT_G_integrable hW hs hα hβ hX hy hya
  have hM := fetT_Mb_bound hW hs hα hβ hX hy hya
  set Mb := fetTMb b E s X
  set hb := fetTtr (fetTHb b E s X S) with hhb
  set N2 := Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
    Real.sqrt 48 * K / Real.sqrt W * (2 * ∫ x, fetTu b E s X S x ∂μ))
  set B := Cg * Real.sqrt 2 * (16 * K / W) * K ^ 2
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => mul_nonneg (by positivity) (fetTct_nonneg hS _)
  have hN20 : 0 ≤ N2 := by
    have : 0 ≤ ∫ x, fetTu b E s X S x ∂μ := integral_nonneg hu0
    positivity
  have hB0 : 0 ≤ B := by positivity
  set t : Fin 2 → (RlCoord W → ℝ) → ℂ := fun j x => blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j *
    rlG b E s X x) k with htdef
  have htc : ∀ j, Continuous (t j) := fun j => (rlTrCLM W k).continuous.comp (continuous_const.mul hGc)
  have htb : ∀ j x, ‖t j x‖ ≤ K * (rlAlpha b s + rlBeta b s) * K := fun j x =>
    (lct_norm_blockTrace_le _ k).trans ((norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hM (fetTQh_norm hα hβ j) (norm_nonneg _) hK0)) (hGb x) (norm_nonneg _)
      (by have := fetTQh_norm (W := W) hα hβ j; positivity)))
  have hti : ∀ j, Integrable (t j) μ := fun j =>
    Integrable.of_bound (htc j).aestronglyMeasurable _ (ae_of_all _ (htb j))
  have hhc : ∀ j, Continuous (fun x => fetTh b E s X S x j) := fun j =>
    fetT_h_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr j
  have hhb' : ∀ j x, ‖fetTh b E s X S x j‖ ≤ K * ‖fetTY E s S‖ * K := fun j x =>
    (lct_norm_blockTrace_le _ j).trans (fetT_F_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x)
  have hhi : ∀ j, Integrable (fun x => fetTh b E s X S x j) μ := fun j =>
    Integrable.of_bound (hhc j).aestronglyMeasurable _ (ae_of_all _ (hhb' j))
  -- pointwise expansion
  have hpt : ∀ x, blockTrace (Mb * (fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x)) k =
      ∑ j, (fetTh b E s X S x j - hb j) * t j x := by
    intro x
    rw [fetTdiag_eq_Qh, Finset.sum_mul, Finset.mul_sum, ← rlTrCLM_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, map_smul, rlTrCLM_apply, smul_eq_mul]
    simp only [htdef]
    rw [Matrix.mul_assoc Mb (fetTQh (rlAlpha b s) (rlBeta b s) j) (rlG b E s X x)]
    rfl
  have hIi : Integrable (fun x => fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x) μ := by
    have e : (fun x => fetTdiag (rlAlpha b s) (rlBeta b s)
        (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x) =
        fun x => (fetTdiag (rlAlpha b s) (rlBeta b s)
          (fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x)) -
            fetTdiag (rlAlpha b s) (rlBeta b s) hb) * rlG b E s X x := by
      funext x; rw [fetTdiag_sub]
    rw [e]
    refine Integrable.of_bound ((((fetT_continuous_diag _ _).comp
      (fetT_F_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)).sub continuous_const).mul
        hGc).aestronglyMeasurable ((2 * (2 * (K * ‖fetTY E s S‖ * K)) +
          2 * (2 * (K * ‖fetTY E s S‖ * K))) * K) (ae_of_all _ fun x => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      (hGb x) (norm_nonneg _) (by positivity))
    · refine (fetT_norm_diag_le hα hβ _).trans ?_
      have hab : rlAlpha b s + rlBeta b s ≤ 2 := by linarith
      have h0 := hhb' 0 x
      have h1 := hhb' 1 x
      unfold fetTtr; unfold fetTh at h0 h1
      nlinarith [norm_nonneg (blockTrace (rlG b E s X x * fetTY E s S * rlG b E s X x) 0),
        norm_nonneg (blockTrace (rlG b E s X x * fetTY E s S * rlG b E s X x) 1), norm_nonneg (fetTY E s S)]
    · refine (fetT_norm_diag_le hα hβ _).trans ?_
      have hab : rlAlpha b s + rlBeta b s ≤ 2 := by linarith
      have hj : ∀ j, ‖hb j‖ ≤ K * ‖fetTY E s S‖ * K := fun j => by
        rw [hhb, fetT_hb_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
        refine (norm_integral_le_integral_norm _).trans ((integral_mono_of_nonneg
          (ae_of_all _ fun _ => norm_nonneg _) (integrable_const _) (ae_of_all _ (hhb' j))).trans
            (le_of_eq ?_))
        rw [integral_const, probReal_univ, one_smul]
      nlinarith [hj 0, hj 1, norm_nonneg (hb 0), norm_nonneg (hb 1), norm_nonneg (fetTY E s S)]
  have hcomm : blockTrace (Mb * ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x ∂μ) k =
      ∫ x, blockTrace (Mb * (fetTdiag (rlAlpha b s) (rlBeta b s)
        (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x)) k ∂μ := by
    have h1 := (rlTrCLM W k).integral_comp_comm
      (((ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Mb).integrable_comp hIi))
    have h2 := (ContinuousLinearMap.mul ℝ (Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) Mb).integral_comp_comm hIi
    simp only [rlTrCLM_apply, ContinuousLinearMap.mul_apply'] at h1 h2
    rw [h1, h2]
  have hterm : ∀ j, Integrable (fun x => (fetTh b E s X S x j - hb j) * t j x) μ := fun j =>
    Integrable.of_bound (((hhc j).sub continuous_const).mul (htc j)).aestronglyMeasurable
      ((K * ‖fetTY E s S‖ * K + ‖hb j‖) * (K * (rlAlpha b s + rlBeta b s) * K))
      (ae_of_all _ fun x => by
        rw [norm_mul]
        exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hhb' j x) le_rfl)) (htb j x)
          (norm_nonneg _) (by have := fetTQh_norm (W := W) hα hβ j; positivity))
  rw [hcomm, integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun j _ => hterm j]
  refine (norm_sum_le _ _).trans ?_
  have hcov : ∀ j, ‖∫ x, (fetTh b E s X S x j - hb j) * t j x ∂μ‖ ≤ N2 * B := by
    intro j
    have e : ∫ x, (fetTh b E s X S x j - hb j) * t j x ∂μ =
        (∫ x, fetTh b E s X S x j * t j x ∂μ) - (∫ x, fetTh b E s X S x j ∂μ) * ∫ x, t j x ∂μ := by
      have hhj : hb j = ∫ x, fetTh b E s X S x j ∂μ := fetT_hb_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr j
      have i1 : Integrable (fun x => fetTh b E s X S x j * t j x) μ :=
        Integrable.of_bound ((hhc j).mul (htc j)).aestronglyMeasurable _ (ae_of_all _ fun x => by
          rw [norm_mul]; exact mul_le_mul (hhb' j x) (htb j x) (norm_nonneg _)
            (by have := fetTQh_norm (W := W) hα hβ j; positivity))
      rw [← hhj, ← integral_const_mul, ← integral_sub i1 ((hti j).const_mul _)]
      congr 1; funext x; ring
    rw [e]
    have hmh : MemLp (fun x => fetTh b E s X S x j) 2 μ :=
      MemLp.of_bound (hhc j).aestronglyMeasurable _ (ae_of_all _ (hhb' j))
    have hmt : MemLp (t j) 2 μ := MemLp.of_bound (htc j).aestronglyMeasurable _ (ae_of_all _ (htb j))
    have hA : eLpNorm (fun x => fetTh b E s X S x j - ∫ x', fetTh b E s X S x' j ∂μ) 2 μ ≤
        ENNReal.ofReal N2 := by
      have := fetT_noise hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr j (p := 2) one_le_two hWp
      rwa [show ENNReal.ofReal 2 = 2 by norm_num] at this
    have hB : eLpNorm (fun x => t j x - ∫ x', t j x' ∂μ) 2 μ ≤ ENNReal.ofReal B := by
      set D' := rlProj k * Mb * fetTQh (rlAlpha b s) (rlBeta b s) j
      have hD' : ‖D'‖ ≤ K := by
        have hP := rl_norm_proj_le (W := W) k
        have hQ := fetTQh_norm (W := W) hα hβ j
        have hab : rlAlpha b s + rlBeta b s ≤ 1 := by unfold rlAlpha rlBeta at *; linarith
        refine (norm_mul_le _ _).trans ((mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hP hM
          (norm_nonneg _) zero_le_one)) (hQ.trans hab) (norm_nonneg _) (by positivity)).trans (le_of_eq ?_))
        ring
      have h := rl_fluct hCg hgr hW hs hα hβ hα1 hβ1 hX hy hya D' (p := 2) one_le_two
      have et : ∀ x, rlF b E s X D' x = t j x := by
        intro x
        simp only [htdef, rlF, D', rl_blockTrace_proj, Matrix.mul_assoc]
      simp only [et] at h
      rw [show ENNReal.ofReal 2 = 2 by norm_num] at h
      refine h.trans (ENNReal.ofReal_le_ofReal ?_)
      have : 16 * ‖D'‖ / W ≤ 16 * K / W := div_le_div_of_nonneg_right (by linarith) hW'.le
      have hc0 : 0 ≤ Cg * Real.sqrt 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc0) (sq_nonneg _)
    exact core_cov_le hmh hmt hN20 hB0 hA hB
  calc ∑ j, ‖∫ x, (fetTh b E s X S x j - hb j) * t j x ∂μ‖ ≤ ∑ _j : Fin 2, N2 * B :=
        Finset.sum_le_sum fun j _ => hcov j
    _ = 2 * (N2 * B) := by simp [Finset.sum_const]

/-- **The derivative linear system** `v = d + q v + err` (`v = h̄ - a'`, `d = f' - a'`), solved by the
stability gap: `|h̄_k - a'| ≤ (d + max|err|)/(1-θ)`. -/
theorem fetT_v_bound {θ : ℝ} (hθ : θ < 1)
    (hq : ∀ k, ∑ j, ‖blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j *
      fetTRp b E s X) k‖ ≤ θ) (hEI : E ∈ Set.Ioo (-2 : ℝ) 2) (k : Fin 2) :
    ‖fetTtr (fetTHb b E s X S) k - tgtAd E‖ ≤
      (fetDist b E X S + max ‖fetTerr b E s X S 0‖ ‖fetTerr b E s X S 1‖) / (1 - θ) := by
  set Rp := fetTRp b E s X
  set hb := fetTtr (fetTHb b E s X S)
  set q : Fin 2 → Fin 2 → ℂ := fun k j =>
    blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k with hqdef
  set d : Fin 2 → ℂ := fun k => fetFd b E X S k - tgtAd E with hddef
  have hR : fetR b E X = Rp := fetT_Rp_eq hW hs hα hβ hX hy hya hE2
  have hbt_add : ∀ M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, blockTrace (M + N) k =
      blockTrace M k + blockTrace N k := fun M N => (rlTrCLM W k).map_add M N
  have hbt_smul : ∀ (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), blockTrace (c • M) k =
      c * blockTrace M k := fun c M => (rlTrCLM W k).map_smul c M
  -- `Σ_j q_kj = (α+β) tr_k(RR)`
  have hqsum : ∑ j, q k j = ((rlAlpha b s + rlBeta b s : ℝ) : ℂ) * blockTrace (Rp * Rp) k := by
    simp only [hqdef]
    rw [show (∑ j, blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k) =
        rlTrCLM W k (∑ j, Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) from
          (map_sum (rlTrCLM W k) _ _).symm]
    have e : ∑ j, Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp =
        Rp * (∑ j, fetTQh (rlAlpha b s) (rlBeta b s) j) * Rp := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e, fetTQh_sum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, map_smul, rlTrCLM_apply,
      smul_eq_mul]
  -- `tr_k(RYR) = f'_k + (1 + s a' + z') tr_k(RR)`
  have hRYR : blockTrace (Rp * fetTY E s S * Rp) k =
      fetFd b E X S k + (1 + (s : ℂ) * tgtAd E + tgtZd b E) * blockTrace (Rp * Rp) k := by
    unfold fetFd
    rw [hR, fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
    rw [show Rp * ((1 + (s : ℂ) * tgtAd E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + S) * Rp =
        (Rp * (S - tgtZd b E • 1) * Rp) + (1 + (s : ℂ) * tgtAd E + tgtZd b E) • (Rp * Rp) by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, add_smul]
      abel]
    rw [hbt_add, hbt_smul]
  have hcancel : (1 + (s : ℂ) * tgtAd E + tgtZd b E) +
      ((rlAlpha b s + rlBeta b s : ℝ) : ℂ) * tgtAd E = 0 := by
    have h := tgt_energy_cancel b hEI
    have e : ((rlAlpha b s + rlBeta b s : ℝ) : ℂ) + s = 1 - b := by
      unfold rlAlpha rlBeta; push_cast; ring
    linear_combination h + tgtAd E * e
  -- the system
  have hsys : ∀ k, hb k - tgtAd E = d k + ∑ j, q k j * (hb j - tgtAd E) + fetTerr b E s X S k := by
    intro k'
    have hbt_add' : ∀ M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, blockTrace (M + N) k' =
        blockTrace M k' + blockTrace N k' := fun M N => (rlTrCLM W k').map_add M N
    have hbt_smul' : ∀ (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), blockTrace (c • M) k' =
        c * blockTrace M k' := fun c M => (rlTrCLM W k').map_smul c M
    have hqsum' : ∑ j, q k' j = ((rlAlpha b s + rlBeta b s : ℝ) : ℂ) * blockTrace (Rp * Rp) k' := by
      simp only [hqdef]
      rw [show (∑ j, blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k') =
          rlTrCLM W k' (∑ j, Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) from
            (map_sum (rlTrCLM W k') _ _).symm]
      have e : ∑ j, Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp =
          Rp * (∑ j, fetTQh (rlAlpha b s) (rlBeta b s) j) * Rp := by
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [e, fetTQh_sum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, map_smul, rlTrCLM_apply,
        smul_eq_mul]
    have hRYR' : blockTrace (Rp * fetTY E s S * Rp) k' =
        fetFd b E X S k' + (1 + (s : ℂ) * tgtAd E + tgtZd b E) * blockTrace (Rp * Rp) k' := by
      unfold fetFd
      rw [hR, fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
      rw [show Rp * ((1 + (s : ℂ) * tgtAd E) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + S) * Rp =
          (Rp * (S - tgtZd b E • 1) * Rp) + (1 + (s : ℂ) * tgtAd E + tgtZd b E) • (Rp * Rp) by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, add_smul]
        abel]
      rw [hbt_add', hbt_smul']
    have hsplit : ∑ j, q k' j * (hb j - tgtAd E) = ∑ j, hb j * q k' j - tgtAd E * ∑ j, q k' j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    have herr : fetTerr b E s X S k' = hb k' - blockTrace (Rp * fetTY E s S * Rp) k' -
        ∑ j, hb j * q k' j := rfl
    rw [hsplit, hqsum', herr, hRYR']
    simp only [hddef]
    linear_combination (blockTrace (Rp * Rp) k') * hcancel
  have hθ' : ∀ k, ∑ j, ‖q k j‖ ≤ θ := hq
  have h := fetT_linsys hθ hθ' hsys k
  have hd : max ‖d 0‖ ‖d 1‖ = fetDist b E X S := by rw [hddef]; rfl
  rwa [hd] at h

/-- **Bound on the system error** from (A)–(D). -/
theorem fetT_err_bound (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * 2 ≤ W) (k : Fin 2) :
    ‖fetTerr b E s X S k‖ ≤
      (‖1 + (s : ℂ) * tgtAd E‖ + 2 * (‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 2 +
          ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s))) *
        ((s * y)⁻¹ * (2 * ‖fetTMb b E s X - fetTRp b E s X‖ + ‖fetTGb b E s X - fetTMb b E s X‖)) +
      ((W : ℝ)⁻¹ * fetTct S (fetTRp b E s X)) *
        ((1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) ^ 2 * (s * y)⁻¹ * ‖fetTDelta b E s X‖ +
          ‖fetTDelta b E s X‖ * (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) * (s * y)⁻¹ +
          (1 + 2 * ((s * y)⁻¹ + 1) * (s * y)⁻¹) ^ 2 * (s * y)⁻¹ *
            ∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s)) +
      (‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 3 * (∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s)) +
        (s * y)⁻¹ * (Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂gaussianProduct (rlVar W b s)) *
          Real.sqrt (∫ x, fetTu b E s X S x ^ 2 ∂gaussianProduct (rlVar W b s)))) +
      2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
        Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W *
          (2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)))) *
        (Cg * Real.sqrt 2 * (16 * (s * y)⁻¹ / W) * (s * y)⁻¹ ^ 2)) := by
  set μ := gaussianProduct (rlVar W b s)
  set K := (s * y)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs hy; positivity
  have hHb := fetT_Hb_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hA1 := fetT_err_Z hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr 1 dcv_norm_one_le k
  have hAQ : ∀ j, ‖blockTrace (fetTMb b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j * fetTGb b E s X) k -
      blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j * fetTRp b E s X) k‖ ≤
      K * (2 * ‖fetTMb b E s X - fetTRp b E s X‖ + ‖fetTGb b E s X - fetTMb b E s X‖) := fun j =>
    fetT_err_Z hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr _ ((fetTQh_norm hα hβ j).trans
      (by unfold rlAlpha rlBeta at *; linarith)) k
  have hBS := fetT_err_S hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k
  have hC := fetT_err_e1 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k
  have hD := fetT_err_e2 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k hWp
  set Mb := fetTMb b E s X
  set Gb := fetTGb b E s X
  set Rp := fetTRp b E s X
  set hb := fetTtr (fetTHb b E s X S) with hhb
  set c₁ := (1 : ℂ) + (s : ℂ) * tgtAd E
  set E1 := ∫ x, fetTD b E s X x * (rlG b E s X x * fetTY E s S * rlG b E s X x) ∂μ
  set E2 := ∫ x, fetTdiag (rlAlpha b s) (rlBeta b s)
      (fun j => fetTtr (rlG b E s X x * fetTY E s S * rlG b E s X x) j - hb j) * rlG b E s X x ∂μ
  have hbt_add : ∀ M N : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, blockTrace (M + N) k =
      blockTrace M k + blockTrace N k := fun M N => (rlTrCLM W k).map_add M N
  have hbt_smul : ∀ (c : ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), blockTrace (c • M) k =
      c * blockTrace M k := fun c M => (rlTrCLM W k).map_smul c M
  -- `h̄_k` from the mean relation
  have hhbk : hb k = blockTrace (Mb * fetTY E s S * Gb) k +
      ∑ j, hb j * blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k +
      blockTrace (Mb * E1) k + blockTrace (Mb * E2) k := by
    have e0 : hb k = blockTrace (fetTHb b E s X S) k := rfl
    rw [e0, hHb, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, hbt_add, hbt_add, hbt_add]
    have t1 : blockTrace (Mb * (fetTY E s S * Gb)) k = blockTrace (Mb * fetTY E s S * Gb) k := by
      rw [Matrix.mul_assoc]
    have t2 : blockTrace (Mb * (fetTdiag (rlAlpha b s) (rlBeta b s) hb * Gb)) k =
        ∑ j, hb j * blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k := by
      rw [fetTdiag_eq_Qh, Finset.sum_mul, Finset.mul_sum,
        show (∑ j, Mb * (hb j • fetTQh (rlAlpha b s) (rlBeta b s) j * Gb)) =
          ∑ j, hb j • (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]]
      rw [← rlTrCLM_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, rlTrCLM_apply, smul_eq_mul]
    rw [t1, t2]
  have hY : ∀ (A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ), blockTrace (A * fetTY E s S * B) k =
      c₁ * blockTrace (A * 1 * B) k + blockTrace (A * S * B) k := by
    intro A B
    rw [fetTY_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, hbt_add, hbt_smul]
  have herr : fetTerr b E s X S k =
      c₁ * (blockTrace (Mb * 1 * Gb) k - blockTrace (Rp * 1 * Rp) k) +
      (blockTrace (Mb * S * Gb) k - blockTrace (Rp * S * Rp) k) +
      ∑ j, hb j * (blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k -
        blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k) +
      blockTrace (Mb * E1) k + blockTrace (Mb * E2) k := by
    have e : fetTerr b E s X S k = hb k - blockTrace (Rp * fetTY E s S * Rp) k -
        ∑ j, hb j * blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k := rfl
    rw [e, hhbk, hY, hY]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hhbj : ∀ j, ‖hb j‖ ≤ ‖c₁‖ * K ^ 2 + ∫ x, fetTu b E s X S x ∂μ := by
    intro j
    rw [hhb, fetT_hb_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
    refine (norm_integral_le_integral_norm _).trans ?_
    have huc : Continuous (fetTu b E s X S) :=
      continuous_const.mul (fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
    have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => mul_nonneg (by positivity) (fetTct_nonneg hS _)
    have hui : Integrable (fetTu b E s X S) μ := Integrable.of_bound huc.aestronglyMeasurable
      ((W : ℝ)⁻¹ * (4 * W * ‖S‖ * K ^ 2)) (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (hu0 x)]
        exact mul_le_mul_of_nonneg_left (fetT_ct_G_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x)
          (by positivity))
    refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      ((integrable_const (‖c₁‖ * K ^ 2)).fun_add hui)
      (ae_of_all _ fun x => fetT_h_pt hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr j x)).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) hui, integral_const, probReal_univ, one_smul]
  set A1 := K * (2 * ‖Mb - Rp‖ + ‖Gb - Mb‖)
  have hA10 : 0 ≤ A1 := by positivity
  have hsumb : ‖∑ j, hb j * (blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k -
      blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k)‖ ≤
      2 * (‖c₁‖ * K ^ 2 + ∫ x, fetTu b E s X S x ∂μ) * A1 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖hb j * (blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k -
          blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k)‖
        ≤ ∑ _j : Fin 2, (‖c₁‖ * K ^ 2 + ∫ x, fetTu b E s X S x ∂μ) * A1 :=
          Finset.sum_le_sum fun j _ => by
            rw [norm_mul]
            exact mul_le_mul (hhbj j) (hAQ j) (norm_nonneg _) ((norm_nonneg _).trans (hhbj j))
      _ = _ := by simp [Finset.sum_const]; ring
  rw [herr]
  have h1 : ‖c₁ * (blockTrace (Mb * 1 * Gb) k - blockTrace (Rp * 1 * Rp) k)‖ ≤ ‖c₁‖ * A1 := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hA1 (norm_nonneg _)
  calc _ ≤ ‖c₁ * (blockTrace (Mb * 1 * Gb) k - blockTrace (Rp * 1 * Rp) k)‖ +
        ‖blockTrace (Mb * S * Gb) k - blockTrace (Rp * S * Rp) k‖ +
        ‖∑ j, hb j * (blockTrace (Mb * fetTQh (rlAlpha b s) (rlBeta b s) j * Gb) k -
          blockTrace (Rp * fetTQh (rlAlpha b s) (rlBeta b s) j * Rp) k)‖ +
        ‖blockTrace (Mb * E1) k‖ + ‖blockTrace (Mb * E2) k‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ ‖c₁‖ * A1 + _ + 2 * (‖c₁‖ * K ^ 2 + ∫ x, fetTu b E s X S x ∂μ) * A1 + _ + _ :=
          add_le_add (add_le_add (add_le_add (add_le_add h1 hBS) hsumb) hC) hD
    _ = _ := by ring

end Clock

/-!
## 10. Final assembly
-/

theorem fetT_norm_tgtAd_le {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖tgtAd E‖ ≤ 1 / Real.sqrt (2 * κ) := by
  have hE2 := abs_le_of_mem_bulkInterval hE
  have hE1 : |E| ≤ 2 := by linarith
  have hk2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hsq := sq_le_of_mem_bulkInterval hE
  have hn1 := norm_matchedA hE1
  have hlow : 2 * κ ≤ ‖1 - matchedA E ^ 2‖ ^ 2 := by
    rw [tgt_norm_one_sub_sq hE1]; nlinarith
  have hs0 : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.mpr (by linarith)
  have hlow' : Real.sqrt (2 * κ) ≤ ‖1 - matchedA E ^ 2‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - matchedA E ^ 2))]; exact Real.sqrt_le_sqrt hlow
  unfold tgtAd
  rw [norm_div, norm_pow, hn1, one_pow]
  exact one_div_le_one_div_of_le hs0 hlow'

theorem fetT_bt_proj_eq {W : ℕ} (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k l : Fin 2) :
    blockTrace (R * rlProj l * R) k = blockPairTrace R k l := by
  rw [← cmpPair_self, rl_cmpPair_proj, rl_blockTrace_proj]
  congr 1
  simp only [Matrix.mul_assoc]

/-- The contraction of the derivative system from `rowSum` of the strict contraction bound. -/
theorem fetT_q_sum_le {W : ℕ} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (k : Fin 2) :
    ∑ j, ‖blockTrace (R * fetTQh α β j * R) k‖ ≤ (α + β) * ∑ l, ‖blockPairTrace R k l‖ := by
  have hj : ∀ j, blockTrace (R * fetTQh α β j * R) k =
      (α : ℂ) * blockPairTrace R k j + (β : ℂ) * blockPairTrace R k (1 - j) := by
    intro j
    unfold fetTQh
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, ← rlTrCLM_apply, map_add, map_smul, map_smul, rlTrCLM_apply, rlTrCLM_apply,
      fetT_bt_proj_eq, fetT_bt_proj_eq, smul_eq_mul, smul_eq_mul]
  simp only [hj, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) - 0 = 1 := rfl
  have h11 : (1 : Fin 2) - 1 = 0 := rfl
  rw [h10, h11]
  have e : ∀ (c : ℝ) (z : ℂ), 0 ≤ c → ‖(c : ℂ) * z‖ = c * ‖z‖ := fun c z hc => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  have h1 := norm_add_le ((α : ℂ) * blockPairTrace R k 0) ((β : ℂ) * blockPairTrace R k 1)
  have h2 := norm_add_le ((α : ℂ) * blockPairTrace R k 1) ((β : ℂ) * blockPairTrace R k 0)
  rw [e α _ hα, e β _ hβ] at h1
  rw [e α _ hα, e β _ hβ] at h2
  linarith

theorem fetT_int_sq_le_of_eLpNorm_real {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : eLpNorm f 2 μ ≤ ENNReal.ofReal A) : ∫ x, f x ^ 2 ∂μ ≤ A ^ 2 := by
  have hc : MemLp (fun x => (f x : ℂ)) 2 μ := (Complex.ofRealCLM.comp_memLp' hf)
  have hn : eLpNorm (fun x => (f x : ℂ)) 2 μ = eLpNorm f 2 μ := by
    refine eLpNorm_congr_norm_ae hc.aestronglyMeasurable hf.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    simp
  have h := fetT_int_sq_le_of_eLpNorm hc hA0 (hn ▸ hA)
  refine le_trans (le_of_eq ?_) h
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Complex.norm_real, sq_abs]

/-!
## 11. Scalar bookkeeping
-/

/-- The constant of `fetT_err_scalar`. -/
def fetTCerr (K Y Cg C3 L Dl : ℝ) : ℝ :=
  (Y + 2 * Y * K ^ 2 + 2 * C3) * (K * (2 * K ^ 2 * L + K ^ 2 * Dl)) +
    (((1 + 2 * (K + 1) * K) ^ 2 * K + (1 + 2 * (K + 1) * K) * K) * L +
      (1 + 2 * (K + 1) * K) ^ 2 * K * Dl) +
    (Y * K ^ 3 * Dl + K * Dl * (2 * C3)) +
    2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3))) *
      (Cg * Real.sqrt 2 * (16 * K) * K ^ 2))

theorem fetTCerr_nonneg {K Y Cg C3 L Dl : ℝ} (hK : 0 ≤ K) (hY : 0 ≤ Y) (hCg : 0 ≤ Cg)
    (hC3 : 0 ≤ C3) (hL : 0 ≤ L) (hDl : 0 ≤ Dl) : 0 ≤ fetTCerr K Y Cg C3 L Dl := by
  unfold fetTCerr; positivity

theorem fetT_err_t1 {K Y Y0 C3 L Dl u P Iu ID mR gM Δ : ℝ}
    (hK : 0 ≤ K) (hY0 : 0 ≤ Y0) (hY : Y0 ≤ Y) (hC3 : 0 ≤ C3) (hu : 0 ≤ u)
    (hIu : Iu ≤ C3 * u) (hID : ID ≤ Dl * P)
    (hΔ : Δ ≤ L * P) (hmR0 : 0 ≤ mR) (hmR : mR ≤ K ^ 2 * Δ)
    (hgM0 : 0 ≤ gM) (hgM : gM ≤ K ^ 2 * ID) :
    (Y0 + 2 * (Y0 * K ^ 2 + Iu)) * (K * (2 * mR + gM)) ≤
      (Y + 2 * Y * K ^ 2 + 2 * C3) * (K * (2 * K ^ 2 * L + K ^ 2 * Dl)) * ((1 + u) * P) := by
  have hY' : 0 ≤ Y := hY0.trans hY
  have h1a : Y0 + 2 * (Y0 * K ^ 2 + Iu) ≤ (Y + 2 * Y * K ^ 2 + 2 * C3) * (1 + u) := by
    have e1 : Y0 * K ^ 2 ≤ Y * K ^ 2 := mul_le_mul_of_nonneg_right hY (by positivity)
    have e2 : 0 ≤ C3 * u := mul_nonneg hC3 hu
    have e3 : 0 ≤ (Y + 2 * Y * K ^ 2) * u := by positivity
    have e4 : (Y + 2 * Y * K ^ 2 + 2 * C3) * (1 + u) =
        Y + 2 * Y * K ^ 2 + 2 * C3 + (Y + 2 * Y * K ^ 2) * u + 2 * (C3 * u) := by ring
    rw [e4]; linarith
  have e1 : mR ≤ K ^ 2 * L * P := hmR.trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hΔ (sq_nonneg K))
  have e2 : gM ≤ K ^ 2 * Dl * P := hgM.trans (by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hID (sq_nonneg K))
  have h1b : K * (2 * mR + gM) ≤ K * (2 * K ^ 2 * L + K ^ 2 * Dl) * P := by
    have : 2 * mR + gM ≤ (2 * K ^ 2 * L + K ^ 2 * Dl) * P := by
      have : (2 * K ^ 2 * L + K ^ 2 * Dl) * P = 2 * (K ^ 2 * L * P) + K ^ 2 * Dl * P := by ring
      rw [this]; linarith
    calc K * (2 * mR + gM) ≤ K * ((2 * K ^ 2 * L + K ^ 2 * Dl) * P) :=
          mul_le_mul_of_nonneg_left this hK
      _ = _ := by ring
  calc _ ≤ ((Y + 2 * Y * K ^ 2 + 2 * C3) * (1 + u)) * (K * (2 * K ^ 2 * L + K ^ 2 * Dl) * P) :=
        mul_le_mul h1a h1b (by positivity) (by positivity)
    _ = _ := by ring

theorem fetT_err_t2 {K L Dl u P ID Δ : ℝ} (hK : 0 ≤ K) (hu : 0 ≤ u)
    (hID0 : 0 ≤ ID) (hID : ID ≤ Dl * P) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ L * P) :
    u * ((1 + 2 * (K + 1) * K) ^ 2 * K * Δ + Δ * (1 + 2 * (K + 1) * K) * K +
        (1 + 2 * (K + 1) * K) ^ 2 * K * ID) ≤
      (((1 + 2 * (K + 1) * K) ^ 2 * K + (1 + 2 * (K + 1) * K) * K) * L +
        (1 + 2 * (K + 1) * K) ^ 2 * K * Dl) * ((1 + u) * P) := by
  set U := 1 + 2 * (K + 1) * K with hU
  have hU0 : 0 ≤ U := by positivity
  have a1 : (U ^ 2 * K + U * K) * Δ ≤ (U ^ 2 * K + U * K) * (L * P) :=
    mul_le_mul_of_nonneg_left hΔ (by positivity)
  have a2 : U ^ 2 * K * ID ≤ U ^ 2 * K * (Dl * P) := mul_le_mul_of_nonneg_left hID (by positivity)
  have e : U ^ 2 * K * Δ + Δ * U * K + U ^ 2 * K * ID ≤
      ((U ^ 2 * K + U * K) * L + U ^ 2 * K * Dl) * P := by
    calc U ^ 2 * K * Δ + Δ * U * K + U ^ 2 * K * ID =
          (U ^ 2 * K + U * K) * Δ + U ^ 2 * K * ID := by ring
      _ ≤ (U ^ 2 * K + U * K) * (L * P) + U ^ 2 * K * (Dl * P) := add_le_add a1 a2
      _ = _ := by ring
  calc _ ≤ (1 + u) * (((U ^ 2 * K + U * K) * L + U ^ 2 * K * Dl) * P) :=
        mul_le_mul (by linarith) e (by positivity) (by linarith)
    _ = _ := by ring

theorem fetT_err_t3 {K Y Y0 C3 Dl u P Iu ID sID sIu : ℝ} (hK : 0 ≤ K) (hY0 : 0 ≤ Y0)
    (hY : Y0 ≤ Y) (hC3 : 0 ≤ C3) (hDl : 0 ≤ Dl) (hu : 0 ≤ u) (hP0 : 0 ≤ P) (hIu : Iu ≤ C3 * u)
    (hID0 : 0 ≤ ID) (hID : ID ≤ Dl * P) (hsID : sID ≤ Dl * P) (hsIu0 : 0 ≤ sIu)
    (hsIu : sIu ≤ 2 * Iu) :
    Y0 * K ^ 3 * ID + K * (sID * sIu) ≤ (Y * K ^ 3 * Dl + K * Dl * (2 * C3)) * ((1 + u) * P) := by
  have hY' : 0 ≤ Y := hY0.trans hY
  have a1 : Y0 * K ^ 3 * ID ≤ Y * K ^ 3 * (Dl * P) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hY (by positivity)) hID hID0 (by positivity)
  have a2 : sID * sIu ≤ (Dl * P) * (2 * C3 * u) :=
    mul_le_mul hsID (hsIu.trans (by linarith)) hsIu0 (by positivity)
  have a3 : Y * K ^ 3 * (Dl * P) ≤ Y * K ^ 3 * Dl * ((1 + u) * P) := by
    have := mul_le_mul_of_nonneg_left (show P ≤ (1 + u) * P from le_mul_of_one_le_left hP0
      (by linarith)) (show 0 ≤ Y * K ^ 3 * Dl by positivity)
    linarith [show Y * K ^ 3 * (Dl * P) = Y * K ^ 3 * Dl * P by ring]
  have a4 : K * ((Dl * P) * (2 * C3 * u)) ≤ K * Dl * (2 * C3) * ((1 + u) * P) := by
    have : K * ((Dl * P) * (2 * C3 * u)) = K * Dl * (2 * C3) * (u * P) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hP0) (by positivity)
  have a5 : K * (sID * sIu) ≤ K * ((Dl * P) * (2 * C3 * u)) := mul_le_mul_of_nonneg_left a2 hK
  calc _ ≤ Y * K ^ 3 * Dl * ((1 + u) * P) + K * Dl * (2 * C3) * ((1 + u) * P) :=
        add_le_add (a1.trans a3) (a5.trans a4)
    _ = _ := by ring

theorem fetT_err_t4 {K Y Y0 Cg C3 u P W Iu : ℝ} (hK : 0 ≤ K) (hY0 : 0 ≤ Y0) (hY : Y0 ≤ Y)
    (hCg : 0 ≤ Cg) (hC3 : 0 ≤ C3) (hu : 0 ≤ u) (hW : 1 ≤ W) (hWP : 1 / W ≤ P)
    (hIu0 : 0 ≤ Iu) (hIu : Iu ≤ C3 * u) :
    2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y0 / W +
        Real.sqrt 48 * K / Real.sqrt W * (2 * Iu))) * (Cg * Real.sqrt 2 * (16 * K / W) * K ^ 2)) ≤
      2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3))) *
        (Cg * Real.sqrt 2 * (16 * K) * K ^ 2)) * ((1 + u) * P) := by
  have hY' : 0 ≤ Y := hY0.trans hY
  have hW0 : 0 < W := by linarith
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hsW0 : 0 < Real.sqrt W := by linarith
  have hsi : 1 / Real.sqrt W ≤ 1 := by rw [div_le_one hsW0]; exact hsW
  have hWi : 1 / W ≤ 1 := by rw [div_le_one hW0]; exact hW
  have hu1 : 1 ≤ 1 + u := by linarith
  have b1 : Real.sqrt 96 * K ^ 3 * Y0 / W ≤ Real.sqrt 96 * K ^ 3 * Y * (1 + u) := by
    rw [div_eq_mul_one_div]
    have e1 : Real.sqrt 96 * K ^ 3 * Y0 ≤ Real.sqrt 96 * K ^ 3 * Y :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    have h0 : 0 ≤ Real.sqrt 96 * K ^ 3 * Y := by positivity
    calc Real.sqrt 96 * K ^ 3 * Y0 * (1 / W) ≤ Real.sqrt 96 * K ^ 3 * Y * 1 :=
          mul_le_mul e1 hWi (by positivity) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left hu1 h0
  have b2 : Real.sqrt 48 * K / Real.sqrt W * (2 * Iu) ≤
      Real.sqrt 48 * K * (2 * C3) * (1 + u) := by
    have e1 : Real.sqrt 48 * K / Real.sqrt W * (2 * Iu) =
        Real.sqrt 48 * K * (1 / Real.sqrt W) * (2 * Iu) := by ring
    rw [e1]
    have h0 : 0 ≤ Real.sqrt 48 * K := by positivity
    have e2 : Iu ≤ C3 * (1 + u) := hIu.trans (mul_le_mul_of_nonneg_left (by linarith) hC3)
    calc Real.sqrt 48 * K * (1 / Real.sqrt W) * (2 * Iu) ≤
          Real.sqrt 48 * K * 1 * (2 * (C3 * (1 + u))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsi h0) (by linarith) (by positivity)
            (by positivity)
      _ = _ := by ring
  have b3 : Cg * Real.sqrt 2 * (16 * K / W) * K ^ 2 ≤ Cg * Real.sqrt 2 * (16 * K) * K ^ 2 * P := by
    have e1 : Cg * Real.sqrt 2 * (16 * K / W) * K ^ 2 =
        Cg * Real.sqrt 2 * (16 * K) * K ^ 2 * (1 / W) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hWP (by positivity)
  have b12 : Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y0 / W +
      Real.sqrt 48 * K / Real.sqrt W * (2 * Iu)) ≤
      Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3)) * (1 + u) := by
    calc _ ≤ Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y * (1 + u) +
          Real.sqrt 48 * K * (2 * C3) * (1 + u)) :=
          mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
      _ = _ := by ring
  calc _ ≤ 2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3)) *
        (1 + u)) * (Cg * Real.sqrt 2 * (16 * K) * K ^ 2 * P)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul b12 b3 (by positivity) (by positivity))
          (by norm_num)
    _ = _ := by ring

/-- **Scalar bookkeeping of the system error**: every term of `fetT_err_bound` is
`O((1 + u)(δ + 1/√W))`. -/
theorem fetT_err_scalar {K Y Y0 Cg C3 L Dl u δ W Iu ID sID sIu mR gM Δ : ℝ}
    (hK : 0 ≤ K) (hY0 : 0 ≤ Y0) (hY : Y0 ≤ Y) (hCg : 0 ≤ Cg) (hC3 : 0 ≤ C3)
    (hDl : 0 ≤ Dl) (hu : 0 ≤ u) (hδ : 0 ≤ δ) (hW : 1 ≤ W)
    (hIu0 : 0 ≤ Iu) (hIu : Iu ≤ C3 * u) (hID0 : 0 ≤ ID) (hID : ID ≤ Dl / W)
    (hsID : sID ≤ Dl / W) (hsIu0 : 0 ≤ sIu) (hsIu : sIu ≤ 2 * Iu)
    (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ L * (δ + 1 / Real.sqrt W)) (hmR0 : 0 ≤ mR) (hmR : mR ≤ K ^ 2 * Δ)
    (hgM0 : 0 ≤ gM) (hgM : gM ≤ K ^ 2 * ID) :
    (Y0 + 2 * (Y0 * K ^ 2 + Iu)) * (K * (2 * mR + gM)) +
      u * ((1 + 2 * (K + 1) * K) ^ 2 * K * Δ + Δ * (1 + 2 * (K + 1) * K) * K +
        (1 + 2 * (K + 1) * K) ^ 2 * K * ID) +
      (Y0 * K ^ 3 * ID + K * (sID * sIu)) +
      2 * ((Cg * Real.sqrt 2 * (Real.sqrt 96 * K ^ 3 * Y0 / W +
        Real.sqrt 48 * K / Real.sqrt W * (2 * Iu))) *
        (Cg * Real.sqrt 2 * (16 * K / W) * K ^ 2)) ≤
      fetTCerr K Y Cg C3 L Dl * ((1 + u) * (δ + 1 / Real.sqrt W)) := by
  have hW0 : 0 < W := by linarith
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hsW0 : 0 < Real.sqrt W := by linarith
  have hWw : 1 / W ≤ 1 / Real.sqrt W := by
    refine one_div_le_one_div_of_le hsW0 ?_
    calc Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := le_mul_of_one_le_left hsW0.le hsW
      _ = W := Real.mul_self_sqrt hW0.le
  have hw0 : 0 ≤ 1 / Real.sqrt W := by positivity
  have hWP : 1 / W ≤ δ + 1 / Real.sqrt W := by linarith
  have hP0 : 0 ≤ δ + 1 / Real.sqrt W := by linarith
  have hDW : Dl / W ≤ Dl * (δ + 1 / Real.sqrt W) := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hWP hDl
  have h1 := fetT_err_t1 hK hY0 hY hC3 hu hIu (hID.trans hDW) hΔ hmR0 hmR hgM0 hgM
  have h2 := fetT_err_t2 hK hu hID0 (hID.trans hDW) hΔ0 hΔ
  have h3 := fetT_err_t3 hK hY0 hY hC3 hDl hu hP0 hIu hID0 (hID.trans hDW) (hsID.trans hDW)
    hsIu0 hsIu
  have h4 := fetT_err_t4 hK hY0 hY hCg hC3 hu hW hWP hIu0 hIu
  rw [fetTCerr]
  calc _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

/-- Scalar bookkeeping of the noise term of `fetT_noise`. -/
theorem fetT_noise_scalar {K Y Y0 Cg C3 u P W Iu p : ℝ} (hK : 0 ≤ K) (hY : Y0 ≤ Y)
    (hY0 : 0 ≤ Y0) (hCg : 0 ≤ Cg) (hC3 : 0 ≤ C3) (hu : 0 ≤ u) (hW : 1 ≤ W)
    (hwP : 1 / Real.sqrt W ≤ P) (hIu0 : 0 ≤ Iu) (hIu : Iu ≤ C3 * u) :
    Cg * Real.sqrt p * (Real.sqrt 96 * K ^ 3 * Y0 / W +
        Real.sqrt 48 * K / Real.sqrt W * (2 * Iu)) ≤
      Cg * Real.sqrt p * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3)) *
        ((1 + u) * P) := by
  have hY' : 0 ≤ Y := hY0.trans hY
  have hW0 : 0 < W := by linarith
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW
  have hsW0 : 0 < Real.sqrt W := by linarith
  have hWw : 1 / W ≤ 1 / Real.sqrt W := by
    refine one_div_le_one_div_of_le hsW0 ?_
    calc Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := le_mul_of_one_le_left hsW0.le hsW
      _ = W := Real.mul_self_sqrt hW0.le
  have hP0 : 0 ≤ P := (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt W).trans hwP
  have hP1 : P ≤ (1 + u) * P := le_mul_of_one_le_left hP0 (by linarith)
  have b1 : Real.sqrt 96 * K ^ 3 * Y0 / W ≤ Real.sqrt 96 * K ^ 3 * Y * ((1 + u) * P) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hY (by positivity)) ((hWw.trans hwP).trans hP1)
      (by positivity) (by positivity)
  have b2 : Real.sqrt 48 * K / Real.sqrt W * (2 * Iu) ≤
      Real.sqrt 48 * K * (2 * C3) * ((1 + u) * P) := by
    have e1 : Real.sqrt 48 * K / Real.sqrt W * (2 * Iu) =
        Real.sqrt 48 * K * 2 * ((1 / Real.sqrt W) * Iu) := by ring
    have e2 : Real.sqrt 48 * K * (2 * C3) * ((1 + u) * P) =
        Real.sqrt 48 * K * 2 * (P * (C3 * (1 + u))) := by ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hwP (hIu.trans ?_) hIu0 hP0) (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hC3
  calc _ ≤ Cg * Real.sqrt p * (Real.sqrt 96 * K ^ 3 * Y * ((1 + u) * P) +
        Real.sqrt 48 * K * (2 * C3) * ((1 + u) * P)) :=
        mul_le_mul_of_nonneg_left (add_le_add b1 b2) (by positivity)
    _ = _ := by ring

/-- The `W`-free constant bounding the residual-clock mean factor of `fetT_uG_mean`. -/
def fetTC3 (K Cg : ℝ) : ℝ :=
  2 * K * (1 + 2 * (K + 1) * (1 + 2 * (K + 1) * K)) +
    (K * (1 + 2 * (K + 1) * K)) ^ 2 * (16 * (Cg * Real.sqrt 2 * 16 * K ^ 2) ^ 2)

theorem fetTC3_nonneg {K Cg : ℝ} (hK : 0 ≤ K) : 0 ≤ fetTC3 K Cg := by
  have := hK
  unfold fetTC3; positivity

theorem fetT_C3_le {K Cg W : ℝ} (hCg : 0 ≤ Cg) (hW : 1 ≤ W) :
    2 * K * (1 + 2 * (K + 1) * (1 + 2 * (K + 1) * K)) +
        (K * (1 + 2 * (K + 1) * K)) ^ 2 * (16 * (Cg * Real.sqrt 2 * (16 / W) * K ^ 2) ^ 2) ≤
      fetTC3 K Cg := by
  unfold fetTC3
  have hW0 : 0 < W := by linarith
  have h16 : 16 / W ≤ 16 := div_le_self (by norm_num) hW
  have h1 : Cg * Real.sqrt 2 * (16 / W) * K ^ 2 ≤ Cg * Real.sqrt 2 * 16 * K ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h16 (by positivity)) (by positivity)
  have h2 : (Cg * Real.sqrt 2 * (16 / W) * K ^ 2) ^ 2 ≤ (Cg * Real.sqrt 2 * 16 * K ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 16))
    (sq_nonneg (K * (1 + 2 * (K + 1) * K)))
  linarith

/-!
### Moment bounds at one exterior input
-/

section Assembly

variable {W : ℕ} {b E s : ℝ} {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
  (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
  (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im)
  (hα1 : rlAlpha b s ≤ 1) (hβ1 : rlBeta b s ≤ 1) (hE2 : |E| ≤ 2) (hS : S.PosSemidef)
  {Cg : ℝ} (hCg : 0 ≤ Cg) (hgr : FetTGrad Cg)
include hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr

/-- The old clock is `u = W⁻¹ Re Tr R* S R` with `R = R_p`. -/
theorem fetT_clock_eq_Rp :
    (W : ℝ)⁻¹ * fetTct S (fetTRp b E s X) = fetClock b E X S := by
  rw [← fetT_Rp_eq hW hs hα hβ hX hy hya hE2]
  rfl

/-- `ρ'_k(V(x)) = h_k(x) - a'` is continuous in the coordinates. -/
theorem fetT_rho_continuous (k : Fin 2) : Continuous (fun x => fetTh b E s X S x k - tgtAd E) :=
  (fetT_h_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k).sub continuous_const

/-- **Crude moment** `‖h_k - a'‖_p ≤ |1 + sa'| K² + |a'| + 2 E u_G` once `24 (K Cg)² p ≤ W`. -/
theorem fetT_crude_Lp (k : Fin 2) {p : ℝ} (hp : 1 ≤ p)
    (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W) :
    eLpNorm (fun x => fetTh b E s X S x k - tgtAd E) (ENNReal.ofReal p)
        (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 2 + ‖tgtAd E‖ +
        2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)) := by
  set μ := gaussianProduct (rlVar W b s)
  set c := ‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 2 + ‖tgtAd E‖ with hc
  have hc0 : 0 ≤ c := by have := mul_pos hs hy; positivity
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => by
    unfold fetTu; exact mul_nonneg (by positivity) (fetTct_nonneg hS _)
  have hpt : ∀ x, ‖fetTh b E s X S x k - tgtAd E‖ ≤ ‖c + fetTu b E s X S x‖ := fun x => by
    rw [Real.norm_of_nonneg (add_nonneg hc0 (hu0 x))]
    refine (norm_sub_le _ _).trans ?_
    have := fetT_h_pt hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k x
    rw [hc]; linarith
  refine (eLpNorm_mono (fetT_rho_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k).aestronglyMeasurable hpt).trans ?_
  refine (eLpNorm_add_le (f := fun _ => c) (g := fetTu b E s X S) hp1).trans ?_
  rw [eLpNorm_const _ (by positivity) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one,
    Real.enorm_of_nonneg hc0]
  have hu := fetT_uG_Lp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hp hWp
  have hI : 0 ≤ ∫ x, fetTu b E s X S x ∂μ := integral_nonneg hu0
  rw [ENNReal.ofReal_add hc0 (by positivity)]
  exact add_le_add le_rfl hu

/-- **Fine moment** `‖h_k - a'‖_p ≤ noise + (d + max|err|)/(1-θ)` (`fetT_noise`, `fetT_v_bound`). -/
theorem fetT_fine_Lp (k : Fin 2) {p : ℝ} (hp : 1 ≤ p) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W)
    {θ : ℝ} (hθ : θ < 1)
    (hq : ∀ k, ∑ j, ‖blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j *
      fetTRp b E s X) k‖ ≤ θ) (hEI : E ∈ Set.Ioo (-2 : ℝ) 2) :
    eLpNorm (fun x => fetTh b E s X S x k - tgtAd E) (ENNReal.ofReal p)
        (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
        Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W *
          (2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s))) +
        (fetDist b E X S + max ‖fetTerr b E s X S 0‖ ‖fetTerr b E s X S 1‖) / (1 - θ)) := by
  set μ := gaussianProduct (rlVar W b s)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hu0 : ∀ x, 0 ≤ fetTu b E s X S x := fun x => by
    unfold fetTu; exact mul_nonneg (by positivity) (fetTct_nonneg hS _)
  set c := (∫ x, fetTh b E s X S x k ∂μ) - tgtAd E with hc
  have e : (fun x => fetTh b E s X S x k - tgtAd E) =
      (fun x => fetTh b E s X S x k - ∫ x', fetTh b E s X S x' k ∂μ) + fun _ => c := by
    funext x; simp only [Pi.add_apply, hc]; ring
  rw [e]
  refine (eLpNorm_add_le hp1).trans ?_
  have hN := fetT_noise hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k hp hWp
  have hv := fetT_v_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hθ hq hEI k
  rw [fetT_hb_eq hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr] at hv
  rw [eLpNorm_const _ (by positivity) (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one,
    ← ofReal_norm]
  have hN0 : 0 ≤ Cg * Real.sqrt p * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * ‖1 + (s : ℂ) * tgtAd E‖ / W +
      Real.sqrt 48 * (s * y)⁻¹ / Real.sqrt W * (2 * ∫ x, fetTu b E s X S x ∂μ)) := by
    have := mul_pos hs hy
    have := integral_nonneg (μ := μ) (f := fetTu b E s X S) hu0
    positivity
  rw [ENNReal.ofReal_add hN0 ((norm_nonneg _).trans hv)]
  exact add_le_add hN (ENNReal.ofReal_le_ofReal hv)

/-- `ρ'` is measurable in the residual pair sample. -/
theorem fetT_measurable_rhoMax : Measurable (fetRhoMax E s X S) := by
  have hR : Measurable (fun ω : RpSample W => rpResolvent E s X ω) :=
    rp_measurable_resolvent E s (Xf := fun _ => X) (ωf := fun ω => ω) measurable_const
      measurable_id
  have hk : ∀ k : Fin 2, Measurable (fun ω => ‖fetRho E s X S ω k‖) := fun k => by
    have hc : Continuous (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ =>
        blockTrace (M * (1 + S + ((s : ℂ) * tgtAd E) • 1) * M) k) :=
      (rlTrCLM W k).continuous.comp ((continuous_id.mul continuous_const).mul continuous_id)
    exact ((hc.measurable.comp hR).sub measurable_const).norm
  exact (hk 0).max (hk 1)

/-- **Transfer to coordinates**: `‖max_k |ρ'_k|‖_{L^p(rpLaw)} ≤ Σ_k ‖h_k - a'‖_{L^p}`. -/
theorem fetT_rhoMax_le {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fetRhoMax E s X S) (ENNReal.ofReal p) (rpLaw W b s) ≤
      eLpNorm (fun x => fetTh b E s X S x 0 - tgtAd E) (ENNReal.ofReal p)
          (gaussianProduct (rlVar W b s)) +
        eLpNorm (fun x => fetTh b E s X S x 1 - tgtAd E) (ENNReal.ofReal p)
          (gaussianProduct (rlVar W b s)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  rw [rl_law_eq_map, eLpNorm_map_measure
    (fetT_measurable_rhoMax hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr).aestronglyMeasurable
    (rl_measurable_embed W b s).aemeasurable]
  have hc0 := fetT_rho_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr 0
  have hc1 := fetT_rho_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr 1
  have hpt : ∀ x, ‖(fetRhoMax E s X S ∘ rlEmbed W b s) x‖ ≤
      (fun x => ‖fetTh b E s X S x 0 - tgtAd E‖) x + (fun x => ‖fetTh b E s X S x 1 - tgtAd E‖) x :=
    fun x => by
      have h0 : 0 ≤ fetRhoMax E s X S (rlEmbed W b s x) :=
        (norm_nonneg _).trans (le_max_left _ _)
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg h0, fetRhoMax, fetT_rho_embed, fetT_rho_embed]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hm : AEStronglyMeasurable (fetRhoMax E s X S ∘ rlEmbed W b s)
      (gaussianProduct (rlVar W b s)) :=
    ((fetT_measurable_rhoMax hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr).comp
      (rl_measurable_embed W b s)).aestronglyMeasurable
  refine (eLpNorm_mono_real hm hpt).trans ?_
  refine (eLpNorm_add_le hp1).trans ?_
  rw [eLpNorm_norm _ hc0.aestronglyMeasurable, eLpNorm_norm _ hc1.aestronglyMeasurable]

theorem fetT_clock_nonneg : 0 ≤ fetClock b E X S := by
  rw [← fetT_clock_eq_Rp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
  exact mul_nonneg (by positivity) (fetTct_nonneg hS _)

theorem fetT_uG_nonneg (x : RlCoord W → ℝ) : 0 ≤ fetTu b E s X S x := by
  unfold fetTu; exact mul_nonneg (by positivity) (fetTct_nonneg hS _)

/-- `E u_G ≤ C₃ u` with the `W`-free constant `C₃ = fetTC3`. -/
theorem fetT_Iu_le :
    ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) ≤
      fetTC3 (s * y)⁻¹ Cg * fetClock b E X S := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  refine (fetT_uG_mean hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr).trans ?_
  rw [fetT_clock_eq_Rp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr]
  exact mul_le_mul_of_nonneg_right (fetT_C3_le hCg hW1)
    (fetT_clock_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)

/-- `√E‖D‖² ≤ Dl/W`, `Dl = 64 Cg √2 K²`. -/
theorem fetT_sID_le :
    Real.sqrt (∫ x, ‖fetTD b E s X x‖ ^ 2 ∂gaussianProduct (rlVar W b s)) ≤
      64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2 / W := by
  have h := fetT_D_L2 hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have e : 16 * (Cg * Real.sqrt 2 * (16 / W) * (s * y)⁻¹ ^ 2) ^ 2 =
      (64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2 / W) ^ 2 := by ring
  rw [e] at h
  have := mul_pos hs hy
  calc _ ≤ Real.sqrt ((64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2 / W) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

/-- `√E u_G² ≤ 2 E u_G` (`fetT_uG_Lp` at `p = 2`). -/
theorem fetT_sIu_le (hWp2 : 24 * ((s * y)⁻¹ * Cg) ^ 2 * 2 ≤ W) :
    Real.sqrt (∫ x, fetTu b E s X S x ^ 2 ∂gaussianProduct (rlVar W b s)) ≤
      2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) := by
  have hL2 := fetT_uG_Lp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr one_le_two hWp2
  rw [ENNReal.ofReal_ofNat] at hL2
  have huc : Continuous (fetTu b E s X S) :=
    continuous_const.mul (fetT_ct_G_continuous hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hm : MemLp (fetTu b E s X S) 2 (gaussianProduct (rlVar W b s)) :=
    fetT_memLp_two_of_bound huc.aestronglyMeasurable
      (C := (W : ℝ)⁻¹ * (4 * W * ‖S‖ * (s * y)⁻¹ ^ 2)) fun x => by
        rw [Real.norm_of_nonneg (fetT_uG_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x)]
        exact mul_le_mul_of_nonneg_left
          (fetT_ct_G_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr x) (by positivity)
  have hI0 : 0 ≤ 2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) :=
    mul_nonneg zero_le_two (integral_nonneg
      (fetT_uG_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr))
  have h := fetT_int_sq_le_of_eLpNorm_real hm hI0 hL2
  calc _ ≤ Real.sqrt ((2 * ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq hI0

/-- **The system error is `O((1 + u)(δ + 1/√W))`** given `‖Δ‖ ≤ L(δ + 1/√W)`. -/
theorem fetT_errmax_le (hWp2 : 24 * ((s * y)⁻¹ * Cg) ^ 2 * 2 ≤ W) {Y L : ℝ}
    (hY : ‖1 + (s : ℂ) * tgtAd E‖ ≤ Y)
    (hΔ : ‖fetTDelta b E s X‖ ≤ L * (matchedDistance b E X + 1 / Real.sqrt W)) :
    max ‖fetTerr b E s X S 0‖ ‖fetTerr b E s X S 1‖ ≤
      fetTCerr (s * y)⁻¹ Y Cg (fetTC3 (s * y)⁻¹ Cg) L (64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2) *
        ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W)) := by
  have hK0 : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hδ0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hceq := fetT_clock_eq_Rp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hu0 := fetT_clock_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hIu0 : 0 ≤ ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) :=
    integral_nonneg (fetT_uG_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hsID := fetT_sID_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hID := (fetT_D_int_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr).trans hsID
  have hID0 : 0 ≤ ∫ x, ‖fetTD b E s X x‖ ∂gaussianProduct (rlVar W b s) :=
    integral_nonneg fun x => norm_nonneg _
  have hk : ∀ k, ‖fetTerr b E s X S k‖ ≤ fetTCerr (s * y)⁻¹ Y Cg (fetTC3 (s * y)⁻¹ Cg) L
      (64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2) *
        ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W)) := fun k => by
    have h := fetT_err_bound hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hWp2 k
    rw [hceq] at h
    exact h.trans (fetT_err_scalar hK0 (norm_nonneg _) hY hCg (fetTC3_nonneg hK0) (by positivity)
      hu0 hδ0 hW1 hIu0 (fetT_Iu_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr) hID0 hID hsID
      (Real.sqrt_nonneg _) (fetT_sIu_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hWp2)
      (norm_nonneg _) hΔ (norm_nonneg _) (fetT_Mb_sub_Rp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr) (norm_nonneg _)
      (fetT_Gb_sub_Mb hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr))
  exact max_le (hk 0) (hk 1)

/-- **The fine moment bound at one exterior input** (both blocks): under the moment thresholds,
the contraction `hq` (`θ < 1`) and `‖Δ‖ ≤ L(δ + 1/√W)`,
`‖max_k |ρ'_k|‖_p ≤ 2 (c_N (1+u)(δ + 1/√W) + (d + C_err (1+u)(δ + 1/√W))/(1-θ))`. -/
theorem fetT_resid_inst {p : ℝ} (hp : 1 ≤ p) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W)
    (hWp2 : 24 * ((s * y)⁻¹ * Cg) ^ 2 * 2 ≤ W) {θ : ℝ} (hθ : θ < 1)
    (hq : ∀ k, ∑ j, ‖blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j *
      fetTRp b E s X) k‖ ≤ θ) (hEI : E ∈ Set.Ioo (-2 : ℝ) 2) {Y L : ℝ}
    (hY : ‖1 + (s : ℂ) * tgtAd E‖ ≤ Y) (hL : 0 ≤ L)
    (hΔ : ‖fetTDelta b E s X‖ ≤ L * (matchedDistance b E X + 1 / Real.sqrt W)) :
    eLpNorm (fetRhoMax E s X S) (ENNReal.ofReal p) (rpLaw W b s) ≤
      ENNReal.ofReal (2 * (Cg * Real.sqrt p * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * Y +
          Real.sqrt 48 * (s * y)⁻¹ * (2 * fetTC3 (s * y)⁻¹ Cg)) *
          ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W)) +
        (fetDist b E X S + fetTCerr (s * y)⁻¹ Y Cg (fetTC3 (s * y)⁻¹ Cg) L
          (64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2) *
          ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W))) / (1 - θ))) := by
  have hK0 : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hδ0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hu0 := fetT_clock_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hIu0 : 0 ≤ ∫ x, fetTu b E s X S x ∂gaussianProduct (rlVar W b s) :=
    integral_nonneg (fetT_uG_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hmax := fetT_errmax_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hWp2 hY hΔ
  have hwP : 1 / Real.sqrt W ≤ matchedDistance b E X + 1 / Real.sqrt W := by linarith
  have hN := fetT_noise_scalar (p := p) hK0 hY (norm_nonneg _) hCg (fetTC3_nonneg hK0) hu0 hW1
    hwP hIu0 (fetT_Iu_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr)
  have hθ0 : 0 < 1 - θ := by linarith
  have hk : ∀ k : Fin 2, eLpNorm (fun x => fetTh b E s X S x k - tgtAd E) (ENNReal.ofReal p)
      (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (Real.sqrt 96 * (s * y)⁻¹ ^ 3 * Y +
          Real.sqrt 48 * (s * y)⁻¹ * (2 * fetTC3 (s * y)⁻¹ Cg)) *
          ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W)) +
        (fetDist b E X S + fetTCerr (s * y)⁻¹ Y Cg (fetTC3 (s * y)⁻¹ Cg) L
          (64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2) *
          ((1 + fetClock b E X S) * (matchedDistance b E X + 1 / Real.sqrt W))) / (1 - θ)) :=
    fun k => (fetT_fine_Lp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k hp hWp hθ hq hEI).trans
      (ENNReal.ofReal_le_ofReal (add_le_add hN
        (div_le_div_of_nonneg_right (add_le_add le_rfl hmax) hθ0.le)))
  refine (fetT_rhoMax_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hp).trans
    ((add_le_add (hk 0) (hk 1)).trans ?_)
  have hd0 : 0 ≤ fetDist b E X S := (norm_nonneg _).trans (le_max_left _ _)
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans hY
  have hCe := fetTCerr_nonneg hK0 hY0 hCg (fetTC3_nonneg (Cg := Cg) hK0) hL
    (show 0 ≤ 64 * Cg * Real.sqrt 2 * ((s * y)⁻¹) ^ 2 by positivity)
  have hC30 := fetTC3_nonneg (Cg := Cg) hK0
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-- **The crude moment bound at one exterior input**: `‖max_k |ρ'_k|‖_p ≤ 2(Y K² + A) + 4 C₃ u`. -/
theorem fetT_resid_crude {p : ℝ} (hp : 1 ≤ p) (hWp : 24 * ((s * y)⁻¹ * Cg) ^ 2 * p ≤ W) {Y A : ℝ}
    (hY : ‖1 + (s : ℂ) * tgtAd E‖ ≤ Y) (hA : ‖tgtAd E‖ ≤ A) :
    eLpNorm (fetRhoMax E s X S) (ENNReal.ofReal p) (rpLaw W b s) ≤
      ENNReal.ofReal (2 * (Y * (s * y)⁻¹ ^ 2 + A) + 4 * fetTC3 (s * y)⁻¹ Cg * fetClock b E X S) := by
  have hIu := fetT_Iu_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hk : ∀ k : Fin 2, eLpNorm (fun x => fetTh b E s X S x k - tgtAd E) (ENNReal.ofReal p)
      (gaussianProduct (rlVar W b s)) ≤
      ENNReal.ofReal (Y * (s * y)⁻¹ ^ 2 + A + 2 * fetTC3 (s * y)⁻¹ Cg * fetClock b E X S) :=
    fun k => by
      refine (fetT_crude_Lp hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr k hp hWp).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h1 : ‖1 + (s : ℂ) * tgtAd E‖ * (s * y)⁻¹ ^ 2 ≤ Y * (s * y)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_right hY (sq_nonneg _)
      linarith
  have hu0 := fetT_clock_nonneg hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr
  have hK0 : 0 ≤ (s * y)⁻¹ := by have := mul_pos hs hy; positivity
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans hY
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hC30 := fetTC3_nonneg (Cg := Cg) hK0
  refine (fetT_rhoMax_le hW hs hα hβ hX hy hya hα1 hβ1 hE2 hS hCg hgr hp).trans
    ((add_le_add (hk 0) (hk 1)).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end Assembly

/-!
## 12. `FetResidualBound`
-/

/-- Final scalar step of the fine clause. -/
theorem fetT_final_scalar {cN Ce g d X Cf : ℝ} (hcN : 0 ≤ cN) (hCe : 0 ≤ Ce) (hg : 0 < g)
    (hd : 0 ≤ d) (hX : 0 ≤ X) (hCf : 2 * (cN + (1 + Ce) / g) ≤ Cf) :
    2 * (cN * X + (d + Ce * X) / g) ≤ Cf * (d + X) := by
  have h1 : (d + Ce * X) / g ≤ (1 + Ce) / g * (d + X) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hg.le
    nlinarith [mul_nonneg hCe hd]
  have h2 : cN * X ≤ cN * (d + X) := mul_le_mul_of_nonneg_left (by linarith) hcN
  calc 2 * (cN * X + (d + Ce * X) / g) ≤ 2 * (cN + (1 + Ce) / g) * (d + X) := by nlinarith
    _ ≤ Cf * (d + X) := mul_le_mul_of_nonneg_right hCf (by linarith)

/-- `‖1 + s a'‖ ≤ 1 + s/√(2κ)` and `|a'| ≤ 1/√(2κ)` on the bulk. -/
theorem fetT_norm_one_add_le {κ E s : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) (hs : 0 ≤ s) :
    ‖1 + (s : ℂ) * tgtAd E‖ ≤ 1 + s * (1 / Real.sqrt (2 * κ)) := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (fetT_norm_tgtAd_le hκ hE) hs)

/-- The contraction of the derivative system from `rowSum` (the strict contraction bound): with
`g = s/(2(1-b))`, `(1-b-s)((1-b)⁻¹ + C_rs δ) ≤ 1 - g` once `((1-b-s)|C_rs| + 1) δ ≤ g`. -/
theorem fetT_theta_le {b s Crs δ T : ℝ} (hb : b < 1) (hbs : 0 ≤ 1 - b - s) (hδ : 0 ≤ δ)
    (hd : δ ≤ s / (2 * (1 - b)) / ((1 - b - s) * |Crs| + 1))
    (hT : T ≤ (1 - b)⁻¹ + Crs * δ) :
    (1 - b - s) * T ≤ 1 - s / (2 * (1 - b)) := by
  have hb0 : 0 < 1 - b := by linarith
  have hden : 0 < (1 - b - s) * |Crs| + 1 := by positivity
  have h1 : (1 - b - s) * T ≤ (1 - b - s) * ((1 - b)⁻¹ + Crs * δ) :=
    mul_le_mul_of_nonneg_left hT hbs
  have h2 : (1 - b - s) * (1 - b)⁻¹ = 1 - 2 * (s / (2 * (1 - b))) := by
    field_simp
  have h3 : (1 - b - s) * (Crs * δ) ≤ ((1 - b - s) * |Crs| + 1) * δ := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self Crs) hδ) hbs
    nlinarith
  have h4 : ((1 - b - s) * |Crs| + 1) * δ ≤ s / (2 * (1 - b)) := by
    rw [le_div_iff₀ hden] at hd; linarith
  have e : (1 - b - s) * ((1 - b)⁻¹ + Crs * δ) = (1 - b - s) * (1 - b)⁻¹ + (1 - b - s) * (Crs * δ) := by
    ring
  linarith

/-- `1/W² ≤ 1/√W` for `W ≥ 1`. -/
theorem fetT_inv_sq_le {W : ℝ} (hW1 : 1 ≤ W) : 1 / W ^ 2 ≤ 1 / Real.sqrt W := by
  have hsW : 1 ≤ Real.sqrt W := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hW1
  refine one_div_le_one_div_of_le (by linarith) ?_
  have h1 : Real.sqrt W ≤ Real.sqrt W * Real.sqrt W := le_mul_of_one_le_left (by linarith) hsW
  rw [Real.mul_self_sqrt (by linarith)] at h1
  exact h1.trans (by nlinarith)

/-- `‖Δ‖ ≤ 2 max(C_R, 0)(δ + 1/√W)` from the residual-pair mean bound
`|m̄_j - a| ≤ C_R δ + C_R/W²`. -/
theorem fetT_Delta_le {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im)
    (hab1 : rlAlpha b s + rlBeta b s ≤ 1) {CR : ℝ}
    (hm : ∀ j, ‖rlMean b E s X j - matchedA E‖ ≤
      CR * matchedDistance b E X + CR / (W : ℝ) ^ 2) :
    ‖fetTDelta b E s X‖ ≤ 2 * max CR 0 * (matchedDistance b E X + 1 / Real.sqrt W) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hδ0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have h1 := fetT_norm_diag_le (W := W) hα hβ (fun k => fetTm b E s X k - matchedA E)
  have hm' : ∀ j, ‖fetTm b E s X j - matchedA E‖ ≤
      max CR 0 * (matchedDistance b E X + 1 / Real.sqrt W) := fun j => by
    rw [fetT_m_eq hW hs hα hβ hX hy hya]
    refine (hm j).trans ?_
    have e : CR * matchedDistance b E X + CR / (W : ℝ) ^ 2 =
        CR * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) := by ring
    rw [e]
    have hp0 : 0 ≤ matchedDistance b E X + 1 / (W : ℝ) ^ 2 := by positivity
    calc CR * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) ≤
          max CR 0 * (matchedDistance b E X + 1 / (W : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [fetT_inv_sq_le hW1]) (le_max_right _ _)
  have hs0' : 0 ≤ ‖fetTm b E s X 0 - matchedA E‖ + ‖fetTm b E s X 1 - matchedA E‖ := by
    positivity
  calc ‖fetTDelta b E s X‖ ≤ (rlAlpha b s + rlBeta b s) *
        (‖fetTm b E s X 0 - matchedA E‖ + ‖fetTm b E s X 1 - matchedA E‖) := h1
    _ ≤ 1 * (‖fetTm b E s X 0 - matchedA E‖ + ‖fetTm b E s X 1 - matchedA E‖) :=
        mul_le_mul_of_nonneg_right hab1 hs0'
    _ ≤ _ := by have := hm' 0; have := hm' 1; linarith

/-- The contraction hypothesis of `fetT_v_bound` from `rowSum` (the strict contraction bound). -/
theorem fetT_q_le {W : ℕ} {b E s : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hW : 0 < W) (hs : 0 < s) (hα : 0 ≤ rlAlpha b s) (hβ : 0 ≤ rlBeta b s)
    (hX : X.IsHermitian) {y : ℝ} (hy : 0 < y) (hya : y ≤ -(matchedA E).im) (hE2 : |E| ≤ 2)
    (hb : b < 1) (hab : rlAlpha b s + rlBeta b s = 1 - b - s) {Crs : ℝ}
    (hd : matchedDistance b E X ≤ s / (2 * (1 - b)) / ((1 - b - s) * |Crs| + 1))
    (hrs : ∀ k, ∑ j : Fin 2, ‖blockPairTrace ((boundaryZ b E • 1 - X)⁻¹) k j‖ ≤
      (1 - b)⁻¹ + Crs * matchedDistance b E X) (k : Fin 2) :
    ∑ j, ‖blockTrace (fetTRp b E s X * fetTQh (rlAlpha b s) (rlBeta b s) j *
        fetTRp b E s X) k‖ ≤ 1 - s / (2 * (1 - b)) := by
  have hR : fetTRp b E s X = (boundaryZ b E • 1 - X)⁻¹ :=
    (fetT_Rp_eq hW hs hα hβ hX hy hya hE2).symm
  have h1 := fetT_q_sum_le hα hβ (fetTRp b E s X) k
  have h2 := hrs k
  rw [← hR] at h2
  rw [hab] at h1
  have hbs : 0 ≤ 1 - b - s := by rw [← hab]; positivity
  exact h1.trans (fetT_theta_le hb hbs ((norm_nonneg _).trans (le_max_left _ _)) hd h2)

/-- **`FetResidualBound`** (in the paper: "The final residual pair has a fixed
stability gap ... The final energy derivative gives the full-energy trace bound").

*Law.* `rpLaw W b s`, conditional on the exterior data: `X` Hermitian, `S ⪰ 0` deterministic,
`E ∈ bulkInterval κ`, fixed `0 < s < 2 min(c, b)`. *Constants.* `y_lo` from `rp_im_a_lower`,
`K = (s y_lo)⁻¹`, `Cg` from `GaussianLpGradient`; `d_* = min(d_R, g/((1-b-s)|C_rs| + 1))` with
`g = s/(2(1-b))`, `d_R, C_R` of `ResidualPairLayerBound` and `C_rs` of `rowSum`;
`W₀ = ⌈24 (K Cg)² (p + 2)⌉`. *Proof.* Coordinates (`rl_law_eq_map`); crude:
`|h_k| ≤ |1+sa'|K² + u_G` and `‖u_G‖_p ≤ 2 E u_G ≤ 2 C₃ u` (`fetT_resid_crude`); fine: noise
`fetT_noise`, derivative mean system `fetT_v_bound` with `θ = 1 - g` (from `fetT_q_sum_le` and
`rowSum`), system error `fetT_err_bound` with `‖Δ‖ ≤ 2 max(C_R, 0)(δ + W⁻²)`
(`ResidualPairLayerBound`), assembled by `fetT_resid_inst`. -/
theorem fetResidualBound_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : FetResidualBound := by
  intro b hb0 hb1 κ s hκ hs0 hs1 p hp
  obtain ⟨Cg, hCg, hgr⟩ := id hgrad
  obtain ⟨ylo, hylo, hyloE⟩ := rp_im_a_lower hκ
  have hsc : s < 2 * (1 - 2 * b) := hs1.trans_le (by gcongr; exact min_le_left _ _)
  have hsb : s < 2 * b := hs1.trans_le (by gcongr; exact min_le_right _ _)
  have hα : 0 < rlAlpha b s := by rw [rlAlpha]; linarith
  have hβ : 0 < rlBeta b s := by rw [rlBeta]; linarith
  have hα1 : rlAlpha b s ≤ 1 := by rw [rlAlpha]; linarith
  have hβ1 : rlBeta b s ≤ 1 := by rw [rlBeta]; linarith
  have hab : rlAlpha b s + rlBeta b s = 1 - b - s := by rw [rlAlpha, rlBeta]; ring
  have hbs : 0 ≤ 1 - b - s := by linarith
  obtain ⟨dsR, CR, εR, hdsR, _, hRP⟩ :=
    residualPairLayerBound_holds hcount hgrad b hb0 hb1 κ s hκ hs0 hs1
  obtain ⟨Crs, hCrs⟩ := strictContraction_holds.rowSum b hb0 hb1 κ hκ
  set K := (s * ylo)⁻¹ with hK
  have hK0 : 0 ≤ K := by have := mul_pos hs0 hylo; positivity
  have hb' : 0 < 1 - b := by linarith
  set g := s / (2 * (1 - b)) with hg
  have hg0 : 0 < g := by positivity
  set dq := g / ((1 - b - s) * |Crs| + 1) with hdq
  have hdq0 : 0 < dq := by positivity
  set A := 1 / Real.sqrt (2 * κ) with hA
  have hA0 : 0 ≤ A := by positivity
  set Y := 1 + s * A with hY
  have hY0 : 0 ≤ Y := by positivity
  set L := 2 * max CR 0 with hL
  have hL0 : 0 ≤ L := by positivity
  set C3 := fetTC3 K Cg with hC3
  have hC30 : 0 ≤ C3 := fetTC3_nonneg hK0
  set Dl := 64 * Cg * Real.sqrt 2 * K ^ 2 with hDl
  set cN := Cg * Real.sqrt p * (Real.sqrt 96 * K ^ 3 * Y + Real.sqrt 48 * K * (2 * C3)) with hcN
  have hcN0 : 0 ≤ cN := by have := hCg.le; positivity
  set Ce := fetTCerr K Y Cg C3 L Dl with hCe
  have hCe0 : 0 ≤ Ce := fetTCerr_nonneg hK0 hY0 hCg.le hC30 hL0 (by have := hCg.le; positivity)
  set Cf := 2 * (cN + (1 + Ce) / g) with hCf
  set Cc := 2 * (Y * K ^ 2 + A) + 4 * C3 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨min dsR dq, max Cf Cc, ⌈24 * (K * Cg) ^ 2 * (p + 2)⌉₊, lt_min hdsR hdq0,
    hCc0.trans (le_max_right _ _), ?_⟩
  intro W hW hW0 X S hX hS E hE
  obtain ⟨hyE, hEabs⟩ := hyloE E hE
  have hEI : E ∈ Set.Ioo (-2 : ℝ) 2 := by
    have := abs_lt_two_of_mem_bulkInterval hκ hE
    exact ⟨(abs_lt.mp this).1, (abs_lt.mp this).2⟩
  have hW0' : 24 * (K * Cg) ^ 2 * (p + 2) ≤ (W : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hW0)
  have hc0 : 0 ≤ 24 * (K * Cg) ^ 2 := by positivity
  have hWp : 24 * ((s * ylo)⁻¹ * Cg) ^ 2 * p ≤ W :=
    (mul_le_mul_of_nonneg_left (by linarith) hc0).trans hW0'
  have hWp2 : 24 * ((s * ylo)⁻¹ * Cg) ^ 2 * 2 ≤ W :=
    (mul_le_mul_of_nonneg_left (by linarith) hc0).trans hW0'
  have hYE : ‖1 + (s : ℂ) * tgtAd E‖ ≤ Y := fetT_norm_one_add_le hκ hE hs0.le
  have hAE : ‖tgtAd E‖ ≤ A := fetT_norm_tgtAd_le hκ hE
  have hu0 := fetT_clock_nonneg hW hs0 hα.le hβ.le hX hylo hyE hα1 hβ1 hEabs hS hCg.le hgr
  have hδ0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hd0 : 0 ≤ fetDist b E X S := (norm_nonneg _).trans (le_max_left _ _)
  constructor
  · refine (fetT_resid_crude hW hs0 hα.le hβ.le hX hylo hyE hα1 hβ1 hEabs hS hCg.le hgr hp hWp
      hYE hAE).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 2 * (Y * K ^ 2 + A) + 4 * C3 * fetClock b E X S ≤ Cc * (1 + fetClock b E X S) := by
      have : 0 ≤ 2 * (Y * K ^ 2 + A) * fetClock b E X S := by positivity
      have e : Cc * (1 + fetClock b E X S) = 2 * (Y * K ^ 2 + A) + 4 * C3 * fetClock b E X S +
          2 * (Y * K ^ 2 + A) * fetClock b E X S + 4 * C3 := by rw [hCc]; ring
      rw [e]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  · intro hd
    have hq := fetT_q_le hW hs0 hα.le hβ.le hX hylo hyE hEabs (by linarith) hab
      (hd.trans (min_le_right _ _)) (hCrs W hW X hX E hE)
    have hm : ∀ j, ‖rlMean b E s X j - matchedA E‖ ≤
        CR * matchedDistance b E X + CR / (W : ℝ) ^ 2 := fun j => by
      have h := (hRP W hW X hX E hE).1 (hd.trans (min_le_left _ _)) j
      rwa [rl_law_eq_map, rl_integral_transfer] at h
    have hΔ := fetT_Delta_le hW hs0 hα.le hβ.le hX hylo hyE (by rw [hab]; linarith) hm
    have hθ : 1 - g < 1 := by linarith
    refine (fetT_resid_inst hW hs0 hα.le hβ.le hX hylo hyE hα1 hβ1 hEabs hS hCg.le hgr hp hWp hWp2
      hθ hq hEI hYE hL0 hΔ).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [sub_sub_cancel]
    exact fetT_final_scalar hcN0 hCe0 hg0 hd0 (by positivity) (le_max_left _ _)

end BlockBand.Layers
