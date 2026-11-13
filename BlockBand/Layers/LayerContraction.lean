module

public import BlockBand.Layers.LayerMeanBounds

/-!
# The layer-contraction lemma and its comparison clause

This file constructs the layer-contraction and layer-comparison statements of
`BlockBand.Internal.Contracts.Layers` from `ConditionalBlockGUECount` alone, through
`gaussianAbsorption_holds` (absorber moments, a.s. invertibility) and `traceCovariance_holds`
(the covariance clause of the trace–matrix lemma):

* `layerComparison_holds (hcount) : LayerComparisonContract`;
* `layerContraction_holds (hcount) : LayerContractionContract`.

Law: `layerLaw W b σ` (fresh layer, conditional on the deterministic Hermitian two-port `X`);
`σ = .separate` at `z = z_∂(E) = boundaryZ b E`, `σ = .common` at `z₀ = commonZ b E`;
`E ∈ bulkInterval κ`; norms: `ℓ²` operator norm on matrices, sup norm on `Fin 2 → ℂ`.

Proof, in an order that avoids circularity:
1. port mean equation (`meanEquation_separate_port`, `meanEquation_common_port`), sign `-Im ḡ_a ≥ 0`
   (`lct_im_meanA_nonpos`) and `|ḡ_a| ≤ K` (`lct_norm_meanA_le`): `Im(z - b ḡ) ≥ ζ₀`, so the port
   residual `r' = (z - bḡ)⁻¹ b Tr Cov` is `O(W⁻²)` and `-Im ū ≥ ζ₀/(3+K)² - |r'|`;
2. hence `-Im(c ḡ_a + b ū_a) ≥ y₃ > 0`, the mean top matrix `M̄⁻¹` is invertible with
   `‖M̄‖ ≤ y₃⁻¹` (`lct_norm_shifted_inv_le`);
3. top mean equation (`meanEquation_separate_top`, `meanEquation_common_top`): the top residual
   `W⁻¹ Tr (M̄ R_phys)` is `O(W⁻²)` (`lct_cov_one_letter`, `lct_norm_residTop_le`);
4. `cmp_comparison_branch` with `η = C W⁻²` identifies the branch: the layer means are within
   `C'' η` of the comparison solution (`LayerComparisonContract`, `W ≥ W₀`);
5. outgoing contraction: the comparison solution of `cmp_comparison_branch` is the one of
   `cmp_twoPort_stable` (uniqueness at `η = 0`, `lct_sep_qstar_branch`), so
   `|ū_i - a| ≤ q_* d(X) + C W⁻²` for `W ≥ W₀`; for `W < W₀` the deterministic bound
   `|ū_i| ≤ (Im z)⁻¹` (`lct_norm_meanP_le`) is absorbed into `C W⁻²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. Scalar helpers
-/

/-- `C / W² ≤ ε` for `W ≥ W₀(C, ε)`. -/
theorem lct_small (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, 0 < W → W₀ ≤ W → C / (W : ℝ) ^ 2 ≤ ε := by
  refine ⟨⌈C / ε⌉₊, fun W hW hWW => ?_⟩
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have h1 : C / ε ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWW)
  have h2 : C ≤ ε * W := by rwa [div_le_iff₀ hε, mul_comm] at h1
  have h3 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- A vector on `Fin 2` with entries of norm `≤ B` has sup norm `≤ B`. -/
theorem lct_pi_norm_le {v : Fin 2 → ℂ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖v i‖ ≤ B) : ‖v‖ ≤ B :=
  (pi_norm_le_iff_of_nonneg hB).mpr h

/-- `Im(z - b w) ≥ ζ₀` and `|z - b w| ≤ 3 + K` from `Im z ≥ ζ₀`, `|z| ≤ 3`, `-Im w ≥ 0`,
`|w| ≤ 2K`, `0 < b < 1/2`. -/
theorem lct_port_coef {z w : ℂ} {b ζ₀ K : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hz : ζ₀ ≤ z.im)
    (hz3 : ‖z‖ ≤ 3) (hw : 0 ≤ -w.im) (hwK : ‖w‖ ≤ 2 * K) :
    ζ₀ ≤ (z - (b : ℂ) * w).im ∧ ‖z - (b : ℂ) * w‖ ≤ 3 + K := by
  constructor
  · have : (z - (b : ℂ) * w).im = z.im + b * (-w.im) := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [this]; have := mul_nonneg hb0.le hw; linarith
  · have h1 := norm_sub_le z ((b : ℂ) * w)
    rw [cmp_norm_real_mul hb0.le] at h1
    have := mul_le_mul (show b ≤ 1 / 2 by linarith) hwK (norm_nonneg _) (by norm_num)
    linarith

/-- Port residual: from `q ū = 1 + ρ` with `Im q ≥ ζ₀ > 0`: `ū = q⁻¹ + q⁻¹ ρ`. -/
theorem lct_port_solve {q u ρ : ℂ} {ζ₀ : ℝ} (hζ₀ : 0 < ζ₀) (hq : ζ₀ ≤ q.im)
    (h : q * u = 1 + ρ) : u = q⁻¹ + q⁻¹ * ρ := by
  have hq0 : q ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hq; linarith
  rw [← mul_one_add, ← h, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul]

/-!
## 2. The residual equations of the layer means
-/

/-- The meq form of the separate-port top matrix is `twoPortTop`. -/
theorem lct_sep_top_eq {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m u : Fin 2 → ℂ) :
    (-((E : ℂ) • (1 : Matrix (PhysSite W .separate) (PhysSite W .separate) ℂ)) - X -
      diagonal (fun x : PhysSite W .separate => (1 - 2 * (b : ℂ)) * m x.1 + b * u x.1)) =
      twoPortTop b E X m u := by
  unfold twoPortTop; push_cast; rfl

/-- The meq form of the common-port top matrix is `commonPortTop`. -/
theorem lct_com_top_eq {W : ℕ} (b E : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (m : Fin 2 → ℂ) (u₀ : ℂ) :
    (-((E : ℂ) • (1 : Matrix (PhysSite W .common) (PhysSite W .common) ℂ)) - X -
      diagonal (fun x : PhysSite W .common => (1 - 2 * (b : ℂ)) * m x.1 + b * u₀)) =
      commonPortTop b E X m u₀ := by
  unfold commonPortTop; push_cast; rfl

/-- Invertibility and norm of a top matrix `cmpTopH E X - diag(s_i)` with `-Im s_i ≥ y > 0`. -/
theorem lct_top_inv {W : ℕ} (E : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (s : Fin 2 → ℂ) {y : ℝ} (hy : 0 < y) (hs : ∀ i, y ≤ -(s i).im) :
    IsUnit (cmpTopH E X - diagonal (cmpExt s)).det ∧
      ‖(cmpTopH E X - diagonal (cmpExt s))⁻¹‖ ≤ y⁻¹ := by
  have hH := cmpTopH_isHermitian E hX
  refine ⟨isUnit_iff_ne_zero.mpr (cmp_det_ne_zero _ hH _ fun p => ?_), ?_⟩
  · have := hs p.1; simp only [cmpExt]; linarith
  · exact lct_norm_shifted_inv_le _ hH _ hy fun p => hs p.1

/-- `‖W⁻¹ Tr (N R)_ii‖ ≤ ‖N‖ ‖R‖`. -/
theorem lct_norm_blockTrace_mul_le {W : ℕ} (N R : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (i : Fin 2) {y B : ℝ} (hN : ‖N‖ ≤ y⁻¹) (hR : ‖R‖ ≤ B) (hy : 0 < y) :
    ‖blockTrace (N * R) i‖ ≤ B / y := by
  refine (lct_norm_blockTrace_le _ i).trans ((norm_mul_le _ _).trans ?_)
  rw [div_eq_inv_mul]
  exact mul_le_mul hN hR (norm_nonneg _) (by positivity)

section Separate

variable {W : ℕ} {b : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {E : ℝ} {z : ℂ}

/-- **Separate ports: residual equations of the layer means** (steps 1–3 of
the module docstring). Hypotheses: `0 < b < 1/2`, `W ≥ 1`, Hermitian `X`, `Im z ≥ ζ₀ > 0`,
`|z| ≤ 3`; a.s. invertibility and `‖𝒢‖ ∈ L²`; `|ḡ_a| ≤ K`; every one-letter covariance
`≤ B`; `ζ₀⁻¹ B ≤ w₁/2`, `w₁ = ζ₀/(3+K)²`. Conclusion: `(ḡ, ū)` solves the two-port Dyson equation up to
residuals `‖r‖ ≤ 6B/(b w₁/2)`, `‖r'‖ ≤ ζ₀⁻¹ B`. -/
theorem lct_sep_residual (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    {ζ₀ K B : ℝ} (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hinv : ∀ᵐ ω ∂layerLaw W b .separate, IsUnit (layerMatrix .separate E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .separate E z X ω‖ ^ 2) (layerLaw W b .separate))
    (hKm : ∀ i, ‖meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) i‖ ≤ K)
    (hcov : ∀ P Q : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖P‖ ≤ 1 →
      ‖Q‖ ≤ 1 → ‖meqCov (layerLaw W b .separate)
        (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent .separate E z X ω).trace)
        (fun ω => Q * layerResolvent .separate E z X ω)‖ ≤ B)
    (hsmall : ζ₀⁻¹ * B ≤ ζ₀ / (3 + K) ^ 2 / 2) :
    ∃ r r' : Fin 2 → ℂ, ‖r‖ ≤ 6 * B / (b * (ζ₀ / (3 + K) ^ 2 / 2)) ∧ ‖r'‖ ≤ ζ₀⁻¹ * B ∧
      ∀ i, meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X) i =
          blockTrace (twoPortTop b E X
            (meqMeanA (layerLaw W b .separate) (layerResolvent .separate E z X))
            (meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X)))⁻¹ i + r i ∧
        meqMeanP (layerLaw W b .separate) (layerResolvent .separate E z X) i =
          (z - (b : ℂ) * meqMeanA (layerLaw W b .separate)
            (layerResolvent .separate E z X) i)⁻¹ + r' i := by
  set μ := layerLaw W b .separate with hμ
  set G := layerResolvent .separate E z X with hG
  set mb : Fin 2 → ℂ := meqMeanA μ G with hmb
  set ub : Fin 2 → ℂ := meqMeanP μ G with hub
  have hz0 : 0 ≤ z.im := hζ₀.le.trans hz
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  have hpos : ∀ i, 0 ≤ -(mb i).im := fun i => by
    have := lct_im_meanA_nonpos (σ := .separate) (b := b) E hz0 hX i; rw [hmb]; linarith
  -- step 1: the port equation
  set ρ : Fin 2 → ℂ := fun j => portBlockTrace (σ := .separate)
    (meqCov μ (fun ω => physBlockTrace (σ := .separate) (G ω) j)
    (fun ω => meqPortProj (W := W) (σ := .separate) j * G ω)) j with hρ
  have hρB : ∀ j, ‖ρ j‖ ≤ B := fun j => by
    refine (meq_norm_portBlockTrace_le (σ := .separate) _ j).trans ?_
    rw [lct_cov_phys_eq]
    exact hcov _ _ (meq_norm_physProj_le (W := W) (σ := .separate) j)
      (meq_norm_portProj_le (W := W) (σ := .separate) j)
  have hq : ∀ j, ζ₀ ≤ (z - (b : ℂ) * mb j).im ∧ ‖z - (b : ℂ) * mb j‖ ≤ 3 + K := fun j =>
    lct_port_coef hb0 hb1 hz hz3 (hpos j) ((hKm j).trans (by linarith))
  have hport := fun j => cmp_port_lower hζ₀ (hq j).1 hK (hq j).2
  set r' : Fin 2 → ℂ := fun j => (z - (b : ℂ) * mb j)⁻¹ * ((b : ℂ) * ρ j) with hr'
  have hr'j : ∀ j, ‖r' j‖ ≤ ζ₀⁻¹ * B := fun j => by
    simp only [hr', norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h1 := (hport j).2
    have h2 : b * ‖ρ j‖ ≤ B := by
      have := mul_le_mul (show b ≤ 1 by linarith) (hρB j) (norm_nonneg _) zero_le_one
      linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hueq : ∀ j, ub j = (z - (b : ℂ) * mb j)⁻¹ + r' j := fun j => by
    have h := meanEquation_separate_port hW hb0.le hb1.le hX E hz0 hinv hG2 j
    exact lct_port_solve hζ₀ (hq j).1 h
  have huim : ∀ j, w₁ / 2 ≤ -(ub j).im := fun j => by
    rw [hueq j, Complex.add_im]
    have := (le_abs_self (r' j).im).trans ((Complex.abs_im_le_norm _).trans (hr'j j))
    linarith [(hport j).1]
  -- step 2: invertibility of the mean top matrix
  have hy₃ : ∀ j, b * (w₁ / 2) ≤ -(cmpSepShift b mb ub j).im := fun j => by
    simp only [cmpSepShift]
    rw [cmp_im_comb]
    have h1 := mul_nonneg hc0 (hpos j)
    have h2 := mul_le_mul_of_nonneg_left (huim j) hb0.le
    linarith
  have hy₃0 : 0 < b * (w₁ / 2) := by positivity
  obtain ⟨hTunit, hTnorm⟩ := lct_top_inv E hX (cmpSepShift b mb ub) hy₃0 hy₃
  have hTeq : twoPortTop b E X mb ub = cmpTopH E X - diagonal (cmpExt (cmpSepShift b mb ub)) :=
    rfl
  -- step 3: the top equation
  have hT' := hTunit
  rw [← hTeq, ← lct_sep_top_eq] at hT'
  have htop := fun a => meanEquation_separate_top hW hb0.le hb1.le hX E hz0 hinv hG2 hT' a
  have hconv := lct_sep_top_eq (W := W) b E X mb ub
  set R := meqResidTop μ (1 - 2 * (b : ℂ)) b G with hR
  have hRB : ‖R‖ ≤ 6 * B := by
    have h1 : ∀ a : Fin LayerShape.separate.blocks, ‖meqCov μ (fun ω => physBlockTrace (G ω) a)
        (fun ω => meqPhysProj a * G ω)‖ ≤ B := fun a => by
      rw [lct_cov_phys_eq]
      exact hcov _ _ (meq_norm_physProj_le a) (meq_norm_physProj_le a)
    have h2 : ∀ (a : Fin LayerShape.separate.blocks) (j : Fin LayerShape.separate.ports),
        ‖meqCov μ (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)‖ ≤ B :=
      fun a j => by
        rw [lct_cov_port_eq]
        exact hcov _ _ (meq_norm_portProj_le j) (meq_norm_physProj_le a)
    have h := lct_norm_residTop_le μ hb0.le hb1.le G h1 h2
    norm_num at h
    exact h
  refine ⟨fun i => blockTrace ((twoPortTop b E X mb ub)⁻¹ * R) i, r', ?_, ?_, ?_⟩
  · refine lct_pi_norm_le (by positivity) fun i => ?_
    rw [hTeq]
    exact lct_norm_blockTrace_mul_le _ _ i hTnorm hRB hy₃0
  · exact lct_pi_norm_le (by positivity) hr'j
  · refine fun i => ⟨?_, hueq i⟩
    rw [← hconv]
    exact htop i

end Separate

section Common

variable {W : ℕ} {b : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {E : ℝ} {z : ℂ}

/-- **Common port: residual equations of the layer means** (same hypotheses as
`lct_sep_residual`, common-port law and equations). -/
theorem lct_com_residual (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    {ζ₀ K B : ℝ} (hζ₀ : 0 < ζ₀) (hz : ζ₀ ≤ z.im) (hz3 : ‖z‖ ≤ 3) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hinv : ∀ᵐ ω ∂layerLaw W b .common, IsUnit (layerMatrix .common E z X ω).det)
    (hG2 : Integrable (fun ω => ‖layerResolvent .common E z X ω‖ ^ 2) (layerLaw W b .common))
    (hKm : ∀ i, ‖meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) i‖ ≤ K)
    (hcov : ∀ P Q : Matrix (LayerSite W .common) (LayerSite W .common) ℂ, ‖P‖ ≤ 1 →
      ‖Q‖ ≤ 1 → ‖meqCov (layerLaw W b .common)
        (fun ω => (W : ℂ)⁻¹ * (P * layerResolvent .common E z X ω).trace)
        (fun ω => Q * layerResolvent .common E z X ω)‖ ≤ B)
    (hsmall : ζ₀⁻¹ * B ≤ ζ₀ / (3 + K) ^ 2 / 2) :
    ∃ (r : Fin 2 → ℂ) (r' : ℂ), ‖r‖ ≤ 6 * B / (b * (ζ₀ / (3 + K) ^ 2 / 2)) ∧
      ‖r'‖ ≤ ζ₀⁻¹ * B ∧
      (∀ i, meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) i =
          blockTrace (commonPortTop b E X
            (meqMeanA (layerLaw W b .common) (layerResolvent .common E z X))
            (meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0))⁻¹ i + r i) ∧
        meqMeanP (layerLaw W b .common) (layerResolvent .common E z X) 0 =
          (z - (b : ℂ) * (meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) 0 +
            meqMeanA (layerLaw W b .common) (layerResolvent .common E z X) 1))⁻¹ + r' := by
  set μ := layerLaw W b .common with hμ
  set G := layerResolvent .common E z X with hG
  set mb : Fin 2 → ℂ := meqMeanA μ G with hmb
  set ub : ℂ := meqMeanP μ G 0 with hub
  have hz0 : 0 ≤ z.im := hζ₀.le.trans hz
  have hc0 : 0 ≤ 1 - 2 * b := by linarith
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  have hpos : ∀ i, 0 ≤ -(mb i).im := fun i => by
    have := lct_im_meanA_nonpos (σ := .common) (b := b) E hz0 hX i; rw [hmb]; linarith
  -- step 1: the port equation
  have hρB : ∀ a : Fin LayerShape.common.blocks,
      ‖portBlockTrace (meqCov μ (fun ω => physBlockTrace (G ω) a)
        (fun ω => meqPortProj (W := W) (σ := .common) 0 * G ω)) 0‖ ≤ B := fun a => by
    refine (meq_norm_portBlockTrace_le (σ := .common) _ 0).trans ?_
    rw [lct_cov_phys_eq]
    exact hcov _ _ (meq_norm_physProj_le (W := W) (σ := .common) a)
      (meq_norm_portProj_le (W := W) (σ := .common) 0)
  have hw : 0 ≤ -(mb 0 + mb 1).im := by
    rw [Complex.add_im]; linarith [hpos 0, hpos 1]
  have hwK : ‖mb 0 + mb 1‖ ≤ 2 * K := by
    have := (norm_add_le (mb 0) (mb 1)).trans (add_le_add (hKm 0) (hKm 1)); linarith
  have hq := lct_port_coef hb0 hb1 hz hz3 hw hwK
  have hport := cmp_port_lower hζ₀ hq.1 hK hq.2
  set ρ : ℂ := portBlockTrace (meqCov μ (fun ω => physBlockTrace (G ω) 0)
      (fun ω => meqPortProj (W := W) (σ := .common) 0 * G ω)) 0 +
    portBlockTrace (meqCov μ (fun ω => physBlockTrace (G ω) 1)
      (fun ω => meqPortProj (W := W) (σ := .common) 0 * G ω)) 0 with hρ
  have hρ2 : ‖ρ‖ ≤ 2 * B := by
    have := (norm_add_le _ _).trans (add_le_add (hρB 0) (hρB 1)); linarith
  set r' : ℂ := (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ * ((b : ℂ) * ρ) with hr'
  have hr'n : ‖r'‖ ≤ ζ₀⁻¹ * B := by
    simp only [hr', norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0.le]
    have h2 : b * ‖ρ‖ ≤ B := by
      have := mul_le_mul_of_nonneg_left hρ2 hb0.le
      nlinarith
    exact mul_le_mul hport.2 h2 (by positivity) (by positivity)
  have hueq : ub = (z - (b : ℂ) * (mb 0 + mb 1))⁻¹ + r' := by
    have h := meanEquation_common_port hW hb0.le hb1.le hX E hz0 hinv hG2
    exact lct_port_solve hζ₀ hq.1 h
  have huim : w₁ / 2 ≤ -ub.im := by
    rw [hueq, Complex.add_im]
    have := (le_abs_self r'.im).trans ((Complex.abs_im_le_norm _).trans hr'n)
    linarith [hport.1]
  -- step 2: invertibility of the mean top matrix
  have hy₃ : ∀ j, b * (w₁ / 2) ≤ -(cmpComShift b mb ub j).im := fun j => by
    simp only [cmpComShift]
    rw [cmp_im_comb]
    have h1 := mul_nonneg hc0 (hpos j)
    have h2 := mul_le_mul_of_nonneg_left huim hb0.le
    linarith
  have hy₃0 : 0 < b * (w₁ / 2) := by positivity
  obtain ⟨hTunit, hTnorm⟩ := lct_top_inv E hX (cmpComShift b mb ub) hy₃0 hy₃
  have hTeq : commonPortTop b E X mb ub =
      cmpTopH E X - diagonal (cmpExt (cmpComShift b mb ub)) := rfl
  -- step 3: the top equation
  have hT' := hTunit
  rw [← hTeq, ← lct_com_top_eq] at hT'
  have htop := fun a => meanEquation_common_top hW hb0.le hb1.le hX E hz0 hinv hG2 hT' a
  have hconv := lct_com_top_eq (W := W) b E X mb ub
  set R := meqResidTop μ (1 - 2 * (b : ℂ)) b G with hR
  have hRB : ‖R‖ ≤ 6 * B := by
    have h1 : ∀ a : Fin LayerShape.common.blocks, ‖meqCov μ (fun ω => physBlockTrace (G ω) a)
        (fun ω => meqPhysProj a * G ω)‖ ≤ B := fun a => by
      rw [lct_cov_phys_eq]
      exact hcov _ _ (meq_norm_physProj_le a) (meq_norm_physProj_le a)
    have h2 : ∀ (a : Fin LayerShape.common.blocks) (j : Fin LayerShape.common.ports),
        ‖meqCov μ (fun ω => portBlockTrace (G ω) j) (fun ω => meqPhysProj a * G ω)‖ ≤ B :=
      fun a j => by
        rw [lct_cov_port_eq]
        exact hcov _ _ (meq_norm_portProj_le j) (meq_norm_physProj_le a)
    have h := lct_norm_residTop_le μ hb0.le hb1.le G h1 h2
    norm_num at h
    linarith
  refine ⟨fun i => blockTrace ((commonPortTop b E X mb ub)⁻¹ * R) i, r', ?_, hr'n, ?_, hueq⟩
  · refine lct_pi_norm_le (by positivity) fun i => ?_
    rw [hTeq]
    exact lct_norm_blockTrace_mul_le _ _ i hTnorm hRB hy₃0
  · intro i
    rw [← hconv]
    exact htop i

end Common

/-!
## 3. Constants: the layer means solve the equations up to `O(W⁻²)`
-/

/-- **The layer means as approximate solutions** (`W ≥ W₁`): `b, κ` first; then `K ≥ 0`,
`C_η ≥ 0`, `W₁`; uniformly in `W ≥ W₁`, Hermitian two-port `X` and `E ∈ bulkInterval κ`: in both
port cases `-Im ḡ_i ≥ 0`, `|ḡ_i| ≤ K`, and `(ḡ, ū)` solves the comparison equations up to
residuals of sup norm `≤ C_η W⁻²`. Only `GaussianAbsorptionContract` is used. -/
theorem lct_means (habs : GaussianAbsorptionContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∃ (K Cη : ℝ) (W₁ : ℕ), 0 ≤ K ∧ 0 ≤ Cη ∧
      ∀ W : ℕ, 0 < W → W₁ ≤ W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      X.IsHermitian → ∀ E ∈ bulkInterval κ,
        ((∀ i, 0 ≤ -(meqMeanA (layerLaw W b .separate)
            (layerResolvent .separate E (boundaryZ b E) X) i).im) ∧
          (∀ i, ‖meqMeanA (layerLaw W b .separate)
            (layerResolvent .separate E (boundaryZ b E) X) i‖ ≤ K) ∧
          ∃ r r' : Fin 2 → ℂ, ‖r‖ ≤ Cη / (W : ℝ) ^ 2 ∧ ‖r'‖ ≤ Cη / (W : ℝ) ^ 2 ∧
            ∀ i, meqMeanA (layerLaw W b .separate)
                (layerResolvent .separate E (boundaryZ b E) X) i =
                blockTrace (twoPortTop b E X
                  (meqMeanA (layerLaw W b .separate)
                    (layerResolvent .separate E (boundaryZ b E) X))
                  (meqMeanP (layerLaw W b .separate)
                    (layerResolvent .separate E (boundaryZ b E) X)))⁻¹ i + r i ∧
              meqMeanP (layerLaw W b .separate) (layerResolvent .separate E (boundaryZ b E) X) i =
                (boundaryZ b E - (b : ℂ) * meqMeanA (layerLaw W b .separate)
                  (layerResolvent .separate E (boundaryZ b E) X) i)⁻¹ + r' i) ∧
        ((∀ i, 0 ≤ -(meqMeanA (layerLaw W b .common)
            (layerResolvent .common E (commonZ b E) X) i).im) ∧
          (∀ i, ‖meqMeanA (layerLaw W b .common)
            (layerResolvent .common E (commonZ b E) X) i‖ ≤ K) ∧
          ∃ (r : Fin 2 → ℂ) (r' : ℂ), ‖r‖ ≤ Cη / (W : ℝ) ^ 2 ∧ ‖r'‖ ≤ Cη / (W : ℝ) ^ 2 ∧
            (∀ i, meqMeanA (layerLaw W b .common) (layerResolvent .common E (commonZ b E) X) i =
                blockTrace (commonPortTop b E X
                  (meqMeanA (layerLaw W b .common) (layerResolvent .common E (commonZ b E) X))
                  (meqMeanP (layerLaw W b .common)
                    (layerResolvent .common E (commonZ b E) X) 0))⁻¹ i + r i) ∧
            meqMeanP (layerLaw W b .common) (layerResolvent .common E (commonZ b E) X) 0 =
              (commonZ b E - (b : ℂ) *
                (meqMeanA (layerLaw W b .common) (layerResolvent .common E (commonZ b E) X) 0 +
                  meqMeanA (layerLaw W b .common)
                    (layerResolvent .common E (commonZ b E) X) 1))⁻¹ + r') := by
  intro b hb0 hb1 κ hκ
  obtain ⟨α₀, hα₀, hα₀1, hbulk⟩ := cmp_bulk_setup hκ
  have hc : 0 < 1 - 2 * b := by linarith
  have h1b : 0 < 1 - b := by linarith
  set ζ₀ := (1 - 2 * b) * α₀ with hζ₀def
  have hζ₀ : 0 < ζ₀ := mul_pos hc hα₀
  obtain ⟨ε₁, Ca, hε₁, hCa, habs'⟩ := habs b hb0 hb1 ζ₀ 3 hζ₀
  obtain ⟨Cv, Wc, hCv, hcov⟩ := lct_cov_one_letter habs hb0 hb1 (M := 3) hζ₀
  set K := Ca with hKdef
  set w₁ := ζ₀ / (3 + K) ^ 2 with hw₁
  have hw₁0 : 0 < w₁ := by positivity
  have hy : 0 < b * (w₁ / 2) := by positivity
  set Cη := 6 * Cv / (b * (w₁ / 2)) + ζ₀⁻¹ * Cv with hCηdef
  have hCη1 : 0 ≤ 6 * Cv / (b * (w₁ / 2)) := by positivity
  have hCη2 : 0 ≤ ζ₀⁻¹ * Cv := by positivity
  obtain ⟨Ws, hWs⟩ := lct_small (ζ₀⁻¹ * Cv) (ε := w₁ / 2) (by positivity)
  refine ⟨K, Cη, max (max ⌈2 / ε₁⌉₊ Wc) Ws, hCa.le, by positivity, ?_⟩
  intro W hW hWW X hX E hE
  have hWe : ⌈2 / ε₁⌉₊ ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hWc : Wc ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hWs' : Ws ≤ W := (le_max_right _ _).trans hWW
  have hW2 : (2 : ℝ) ≤ ε₁ * W := by
    have h1 : 2 / ε₁ ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hWe)
    rw [div_le_iff₀ hε₁] at h1
    linarith
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hzs : ζ₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs.le]
    have := mul_le_mul_of_nonneg_left haim h1b.le
    nlinarith
  have hzc : ζ₀ ≤ (commonZ b E).im := by
    rw [commonZ_im hEabs.le]
    have := mul_le_mul_of_nonneg_left haim hc.le
    nlinarith
  have hzs3 := norm_boundaryZ_le hb0.le (by linarith) hEabs.le
  have hzc3 := norm_commonZ_le hb0.le (by linarith) hEabs.le
  have hz0s : 0 ≤ (boundaryZ b E).im := hζ₀.le.trans hzs
  have hz0c : 0 ≤ (commonZ b E).im := hζ₀.le.trans hzc
  have hB : 0 ≤ Cv / (W : ℝ) ^ 2 := by positivity
  have hsmall : ζ₀⁻¹ * (Cv / (W : ℝ) ^ 2) ≤ ζ₀ / (3 + K) ^ 2 / 2 := by
    rw [← mul_div_assoc]; exact hWs W hW hWs'
  have hr1 : 6 * (Cv / (W : ℝ) ^ 2) / (b * (ζ₀ / (3 + K) ^ 2 / 2)) ≤ Cη / (W : ℝ) ^ 2 := by
    rw [show 6 * (Cv / (W : ℝ) ^ 2) / (b * (ζ₀ / (3 + K) ^ 2 / 2)) =
      (6 * Cv / (b * (w₁ / 2))) / (W : ℝ) ^ 2 by rw [hw₁]; ring]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hr2 : ζ₀⁻¹ * (Cv / (W : ℝ) ^ 2) ≤ Cη / (W : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  constructor
  · obtain ⟨hinv, hmom⟩ := habs' W hW .separate X hX E (boundaryZ b E) hzs hzs3
    have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) hW2)
    have hKm : ∀ i, ‖meqMeanA (layerLaw W b .separate)
        (layerResolvent .separate E (boundaryZ b E) X) i‖ ≤ K := fun i =>
      lct_norm_meanA_le hCa.le (hmom 1 le_rfl (by linarith)) i
    obtain ⟨r, r', hr, hr', heq⟩ := lct_sep_residual hW hb0 hb1 hX hζ₀ hzs hzs3 hCa.le hB hinv
      hG2 hKm (fun P Q hP hQ => hcov W hW hWc .separate X hX E _ hzs hzs3 P Q hP hQ) hsmall
    refine ⟨fun i => ?_, hKm, r, r', hr.trans hr1, hr'.trans hr2, heq⟩
    have := lct_im_meanA_nonpos (σ := .separate) (b := b) E hz0s hX i
    linarith
  · obtain ⟨hinv, hmom⟩ := habs' W hW .common X hX E (commonZ b E) hzc hzc3
    have hG2 := meq_sq_integrable_of_eLpNorm (hmom 2 (by norm_num) hW2)
    have hKm : ∀ i, ‖meqMeanA (layerLaw W b .common)
        (layerResolvent .common E (commonZ b E) X) i‖ ≤ K := fun i =>
      lct_norm_meanA_le hCa.le (hmom 1 le_rfl (by linarith)) i
    obtain ⟨r, r', hr, hr', heq, heq'⟩ := lct_com_residual hW hb0 hb1 hX hζ₀ hzc hzc3 hCa.le hB
      hinv hG2 hKm (fun P Q hP hQ => hcov W hW hWc .common X hX E _ hzc hzc3 P Q hP hQ) hsmall
    refine ⟨fun i => ?_, hKm, r, r', hr.trans hr1, hr'.trans hr2, heq, heq'⟩
    have := lct_im_meanA_nonpos (σ := .common) (b := b) E hz0c hX i
    linarith

/-!
## 4. The same separate-port solution for `q_*` and for the branch clause
-/

/-- **`q_*` and the branch clause for the same solution.** `cmp_twoPort_stable` and
`cmp_comparison_branch` state their solutions separately; the stable solution `(m, u)` is an
exact solution with `-Im m_i > 0` and `|m_i| ≤ 1 + C_s d_s`, so the branch clause at `η = 0`
(taken with `K' = max(K, 1 + C_s d_s)`) identifies it with the branch solution. Constants depend
only on `b, κ, K`. -/
theorem lct_sep_qstar_branch : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    ∀ K : ℝ, 0 ≤ K →
    ∃ dstar qstar η₀ C'' : ℝ, 0 < dstar ∧ 0 ≤ qstar ∧ qstar < 1 ∧ 0 < η₀ ∧
      ∀ (W : ℕ), 0 < W → ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian →
      ∀ E ∈ bulkInterval κ, matchedDistance b E X ≤ dstar →
        ∃ m u : Fin 2 → ℂ, IsTwoPortSolution b E X m u ∧
          (∀ i, ‖u i - matchedA E‖ ≤ qstar * matchedDistance b E X) ∧
          ∀ (η : ℝ) (mb ub r r' : Fin 2 → ℂ), 0 ≤ η → η ≤ η₀ → ‖r‖ ≤ η → ‖r'‖ ≤ η →
            (∀ i, 0 ≤ -(mb i).im) → (∀ i, ‖mb i‖ ≤ K) →
            (∀ i, mb i = blockTrace (twoPortTop b E X mb ub)⁻¹ i + r i ∧
              ub i = (boundaryZ b E - (b : ℂ) * mb i)⁻¹ + r' i) →
            ∀ i, ‖mb i - m i‖ + ‖ub i - u i‖ ≤ C'' * η := by
  intro b hb0 hb1 κ hκ K hK
  obtain ⟨ds, Cs, qs, ρB, CB, hds, hCs, hqs0, hqs, -, -, hst⟩ := cmp_twoPort_stable b hb0 hb1 κ hκ
  obtain ⟨α₀, -, -, hbulk⟩ := cmp_bulk_setup hκ
  set K' := max K (1 + Cs * ds) with hK'
  obtain ⟨d₁, C, η₀, C'', hd₁, hη₀, hbr⟩ :=
    cmp_comparison_branch b hb0 hb1 κ hκ K' (hK.trans (le_max_left _ _))
  refine ⟨min ds d₁, qs, η₀, C'', lt_min hds hd₁, hqs0, hqs, hη₀, ?_⟩
  intro W hW X hX E hE hd
  obtain ⟨m, u, hsol, him, hclose, hq, -⟩ := hst W hW X hX E hE (hd.trans (min_le_left _ _))
  obtain ⟨⟨m', u', -, -, -, hb'⟩, -⟩ := hbr W hW X hX E hE (hd.trans (min_le_right _ _))
  have ha1 := (hbulk E hE).2.1
  have hmK : ∀ i, ‖m i‖ ≤ K' := fun i => by
    have h1 := hclose i
    have h2 := norm_nonneg (u i - matchedA E)
    have h3 : Cs * matchedDistance b E X ≤ Cs * ds :=
      mul_le_mul_of_nonneg_left (hd.trans (min_le_left _ _)) hCs
    have h4 := norm_le_norm_add_norm_sub' (m i) (matchedA E)
    rw [ha1] at h4
    have := le_max_right K (1 + Cs * ds)
    linarith
  have heq : ∀ i, m i = m' i ∧ u i = u' i := fun i => by
    have h := hb' 0 m u 0 0 le_rfl hη₀.le (by simp) (by simp)
      (fun j => by linarith [(him j).1]) hmK
      (fun j => ⟨by rw [Pi.zero_apply, add_zero]; exact (hsol j).1,
        by rw [Pi.zero_apply, add_zero]; exact (hsol j).2⟩) i
    rw [mul_zero] at h
    have h1 := norm_nonneg (m i - m' i)
    have h2 := norm_nonneg (u i - u' i)
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (by linarith)),
      sub_eq_zero.mp (norm_eq_zero.mp (by linarith))⟩
  have hm : m = m' := funext fun i => (heq i).1
  have hu : u = u' := funext fun i => (heq i).2
  refine ⟨m, u, hsol, hq, ?_⟩
  intro η mb ub r r' hη0 hη hr hr' hpos hKm happ i
  rw [hm, hu]
  exact hb' η mb ub r r' hη0 hη hr hr' hpos (fun j => (hKm j).trans (le_max_left _ _)) happ i

/-!
## 5. The constructors
-/

/-- **`LayerComparisonContract`** (proof of the layer-contraction lemma), from
`ConditionalBlockGUECount` alone. Constants: `d_*, C` from `cmp_comparison_branch` at `K`
(absorber bound) and `C_η` (`lct_means`); `W₀` with `C_η W₀⁻² ≤ η₀`. For `W ≥ W₀` the layer
means are within `C'' C_η W⁻²` of the comparison solution. -/
theorem layerComparison_holds (hcount : Inputs.ConditionalBlockGUECount) :
    LayerComparisonContract := by
  intro b hb0 hb1 κ hκ
  have habs := gaussianAbsorption_holds hcount
  obtain ⟨K, Cη, W₁, hK, hCη, hmeans⟩ := lct_means habs b hb0 hb1 κ hκ
  obtain ⟨d₁, C, η₀, C'', hd₁, hη₀, hbr⟩ := cmp_comparison_branch b hb0 hb1 κ hκ K hK
  obtain ⟨Ws, hWs⟩ := lct_small Cη hη₀
  refine ⟨d₁, max C (C'' * Cη), max W₁ Ws, hd₁, ?_⟩
  intro W hW hWW X hX E hE hd
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hη : Cη / (W : ℝ) ^ 2 ≤ η₀ := hWs W hW ((le_max_right _ _).trans hWW)
  have hη0 : 0 ≤ Cη / (W : ℝ) ^ 2 := by positivity
  have hCd : C * matchedDistance b E X ≤ max C (C'' * Cη) * matchedDistance b E X :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  have hCW : C'' * (Cη / (W : ℝ) ^ 2) ≤ max C (C'' * Cη) / (W : ℝ) ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨⟨hpos, hKm, r, r', hr, hr', happ⟩, ⟨hposc, hKmc, rc, rc', hrc, hrc', happc, happc'⟩⟩ :=
    hmeans W hW ((le_max_left _ _).trans hWW) X hX E hE
  obtain ⟨⟨m, u, hsol, him, hclose, hbs⟩, ⟨mc, u₀, hsolc, himc, hu₀, hclosec, hcloseu, hbc⟩⟩ :=
    hbr W hW X hX E hE hd
  constructor
  · refine ⟨m, u, hsol, him, fun i => (hclose i).trans hCd, fun i => ?_⟩
    have h := (hbs _ _ _ r r' hη0 hη hr hr' hpos hKm happ i).trans hCW
    exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans h,
      (le_add_of_nonneg_left (norm_nonneg _)).trans h⟩
  · obtain ⟨h1, h2⟩ := hbc _ _ rc _ rc' hη0 hη hrc hrc' hposc hKmc ⟨happc, happc'⟩
    exact ⟨mc, u₀, hsolc, himc, hu₀, fun i => (hclosec i).trans hCd, hcloseu.trans hCd,
      fun i => (h1 i).trans hCW, h2.trans hCW⟩

/-- Deterministic bound `|ū - a| ≤ Im z⁻¹ + 1` turned into `C_det W⁻²` for `W < W₀`. -/
theorem lct_det_small {x a : ℂ} {ζ₀ : ℝ} {W W₀ : ℕ} (hζ₀ : 0 < ζ₀) (hx : ‖x‖ ≤ ζ₀⁻¹)
    (ha : ‖a‖ = 1) (hW : 0 < W) (hWW : W < W₀) :
    ‖x - a‖ ≤ (ζ₀⁻¹ + 1) * (W₀ : ℝ) ^ 2 / (W : ℝ) ^ 2 := by
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hle : (W : ℝ) ^ 2 ≤ (W₀ : ℝ) ^ 2 := by
    have : (W : ℝ) ≤ W₀ := by exact_mod_cast hWW.le
    nlinarith
  have h1 : ‖x - a‖ ≤ ζ₀⁻¹ + 1 := by
    have := norm_sub_le x a; rw [ha] at this; linarith
  rw [mul_div_assoc]
  have h2 : 1 ≤ (W₀ : ℝ) ^ 2 / (W : ℝ) ^ 2 := by
    rw [one_le_div (by positivity)]; exact hle
  have h3 : 0 ≤ ζ₀⁻¹ + 1 := by positivity
  nlinarith

/-- **`LayerContractionContract`** (the layer-contraction lemma), from `ConditionalBlockGUECount`
alone, uniformly in every `W ≥ 1`. For `W ≥ W₀`: the layer means are within `C'' C_η W⁻²` of the
comparison solution, which has `|u_i - a| ≤ q_* d(X)` (separate, `lct_sep_qstar_branch`) resp.
`|u₀ - a| ≤ C d(X)` (common). For `W < W₀`: `|ū - a| ≤ ζ₀⁻¹ + 1 ≤ (ζ₀⁻¹ + 1) W₀² W⁻²` by the
deterministic port bound `|ū| ≤ (Im z)⁻¹`, `Im z ≥ ζ₀ = (1-2b) α₀`. -/
theorem layerContraction_holds (hcount : Inputs.ConditionalBlockGUECount) :
    LayerContractionContract := by
  intro b hb0 hb1 κ hκ
  have habs := gaussianAbsorption_holds hcount
  obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
  have hc : 0 < 1 - 2 * b := by linarith
  have h1b : 0 < 1 - b := by linarith
  set ζ₀ := (1 - 2 * b) * α₀ with hζ₀def
  have hζ₀ : 0 < ζ₀ := mul_pos hc hα₀
  obtain ⟨K, Cη, W₁, hK, hCη, hmeans⟩ := lct_means habs b hb0 hb1 κ hκ
  obtain ⟨ds, qs, η₀s, C''s, hds, hqs0, hqs, hη₀s, hsep⟩ := lct_sep_qstar_branch b hb0 hb1 κ hκ K hK
  obtain ⟨d₁, Cc, η₀c, C''c, hd₁, hη₀c, hbr⟩ := cmp_comparison_branch b hb0 hb1 κ hκ K hK
  obtain ⟨Ws, hWs⟩ := lct_small Cη (lt_min hη₀s hη₀c)
  set W₀ := max W₁ Ws with hW₀
  set Cdet := (ζ₀⁻¹ + 1) * (W₀ : ℝ) ^ 2 with hCdet
  have hCdet0 : 0 ≤ Cdet := by positivity
  set Cf := max (max (C''s * Cη) (C''c * Cη)) (max Cc Cdet) with hCf
  have hCf0 : 0 ≤ Cf := hCdet0.trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨min ds d₁, Cf, qs, lt_min hds hd₁, hqs0, hqs, ?_⟩
  intro W hW X hX E hE hd
  have hd0 : 0 ≤ matchedDistance b E X := (norm_nonneg _).trans (le_max_left _ _)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hCfW0 : 0 ≤ Cf / (W : ℝ) ^ 2 := by positivity
  obtain ⟨hEabs, ha1, haim⟩ := hbulk E hE
  have hzs : ζ₀ ≤ (boundaryZ b E).im := by
    rw [boundaryZ_im hEabs.le]
    have := mul_le_mul_of_nonneg_left haim h1b.le
    nlinarith
  have hzc : ζ₀ ≤ (commonZ b E).im := by
    rw [commonZ_im hEabs.le]
    have := mul_le_mul_of_nonneg_left haim hc.le
    nlinarith
  have hCdetW : Cdet / (W : ℝ) ^ 2 ≤ Cf / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
  rcases lt_or_ge W W₀ with hWW | hWW
  · -- small `W`: the deterministic port bound
    have hps : ∀ j : Fin 2, ‖meqMeanP (layerLaw W b .separate)
        (layerResolvent .separate E (boundaryZ b E) X) j‖ ≤ ζ₀⁻¹ := fun j =>
      (lct_norm_meanP_le (σ := .separate) E (hζ₀.trans_le hzs) hX j).trans (inv_anti₀ hζ₀ hzs)
    have hpc : ‖meqMeanP (layerLaw W b .common)
        (layerResolvent .common E (commonZ b E) X) 0‖ ≤ ζ₀⁻¹ :=
      (lct_norm_meanP_le (σ := .common) E (hζ₀.trans_le hzc) hX 0).trans (inv_anti₀ hζ₀ hzc)
    have hq0 := mul_nonneg hqs0 hd0
    have hC0 := mul_nonneg hCf0 hd0
    exact ⟨fun j => ((lct_det_small hζ₀ (hps j) ha1 hW hWW).trans hCdetW).trans
        (le_add_of_nonneg_left hq0),
      ((lct_det_small hζ₀ hpc ha1 hW hWW).trans hCdetW).trans (le_add_of_nonneg_left hC0)⟩
  · -- large `W`: comparison
    have hη : Cη / (W : ℝ) ^ 2 ≤ min η₀s η₀c := hWs W hW ((le_max_right _ _).trans hWW)
    have hη0 : 0 ≤ Cη / (W : ℝ) ^ 2 := by positivity
    obtain ⟨⟨hpos, hKm, r, r', hr, hr', happ⟩, ⟨hposc, hKmc, rc, rc', hrc, hrc', happc, happc'⟩⟩ :=
      hmeans W hW ((le_max_left _ _).trans hWW) X hX E hE
    refine ⟨fun j => ?_, ?_⟩
    · obtain ⟨m, u, -, hq, hbs⟩ := hsep W hW X hX E hE (hd.trans (min_le_left _ _))
      have h := hbs _ _ _ r r' hη0 (hη.trans (min_le_left _ _)) hr hr' hpos hKm happ j
      have h2 : C''s * (Cη / (W : ℝ) ^ 2) ≤ Cf / (W : ℝ) ^ 2 := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          ((le_max_left _ _).trans (le_max_left _ _)) (by positivity)
      calc _ ≤ ‖meqMeanP (layerLaw W b .separate)
              (layerResolvent .separate E (boundaryZ b E) X) j - u j‖ + ‖u j - matchedA E‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C''s * (Cη / (W : ℝ) ^ 2) + qs * matchedDistance b E X :=
            add_le_add ((le_add_of_nonneg_left (norm_nonneg _)).trans h) (hq j)
        _ ≤ Cf / (W : ℝ) ^ 2 + qs * matchedDistance b E X := add_le_add_left h2 _
        _ = qs * matchedDistance b E X + Cf / (W : ℝ) ^ 2 := add_comm _ _
    · obtain ⟨-, ⟨mc, u₀, -, -, -, -, hcloseu, hbc⟩⟩ :=
        hbr W hW X hX E hE (hd.trans (min_le_right _ _))
      obtain ⟨-, h⟩ := hbc _ _ rc _ rc' hη0 (hη.trans (min_le_right _ _)) hrc hrc' hposc hKmc
        ⟨happc, happc'⟩
      have h2 : C''c * (Cη / (W : ℝ) ^ 2) ≤ Cf / (W : ℝ) ^ 2 := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)
      have h4 : Cc * matchedDistance b E X ≤ Cf * matchedDistance b E X :=
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hd0
      calc _ ≤ ‖meqMeanP (layerLaw W b .common)
              (layerResolvent .common E (commonZ b E) X) 0 - u₀‖ + ‖u₀ - matchedA E‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C''c * (Cη / (W : ℝ) ^ 2) + Cc * matchedDistance b E X := add_le_add h hcloseu
        _ ≤ Cf / (W : ℝ) ^ 2 + Cf * matchedDistance b E X := add_le_add h2 h4
        _ = Cf * matchedDistance b E X + Cf / (W : ℝ) ^ 2 := add_comm _ _

end BlockBand.Layers
