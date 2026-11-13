module

public import BlockBand.Center.SmoothConstructionCutoff

/-!
# Implicit differentiation of the center along a `ξ_g` line

Fix a Hermitian, ring-banded `H₀` with invertible exterior bonds, a real `E`, a direction `g` and
a Dyson root `ζ` at `(H₀, E)`. Along the line `t ↦ H₀ + t P_{S_g}` write `z(t)` for the root,
`A = (H₀ - E - ζ P_S)⁻¹`, `a_k = W⁻¹Tr P_k[A P_g A]_{SS}`, `d_k = W⁻¹Tr P_k[A P_S A]_{SS}`.
* `scb_line_root`: `z` is differentiable at `0` and is a root near `0`;
* `scb_line_derivs`: `∂_t W⁻¹Tr P_k ℛ(z(t)) = -a_k + z'(0) d_k` and the implicit equation
  `z'(0)(1 - (s/2)(d_e + d_{e+1})) = -(s/2)(a_e + a_{e+1})`;
* `scb_stability`: `Re(1 - (s/2)(d_e + d_{e+1})) ≥ 2(Im ζ)²/s` (`scn_stability`);
* **`scb_hasDerivAt_U`**: the derivative `V'` of the unclipped center
  `(s/2) Im(W⁻¹Tr P_eℛ - W⁻¹Tr P_{e+1}ℛ)/Im ζ` along the line exists and
  `|V'| ≤ (s w/2 + s³w⁵/4 + s²w³/4)(|a_e| + |a_{e+1}|)`, `w = 1/Im ζ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Layers
open scoped ComplexConjugate Matrix.Norms.L2Operator ContDiff

/-!
## 1. Linear helpers
-/

section Helpers

variable {p : Parameters} {e : ZMod p.n}

theorem scb_traceCLM_apply (k : ZMod p.n) (X : p.SiteMatrix) :
    tgtTraceCLM e k X = (p.W : ℂ)⁻¹ * ∑ x : PairSite p e, if x.1.1 = k then X x.1 x.1 else 0 :=
  rfl

theorem scb_traceCLM_smul (k : ZMod p.n) (c : ℂ) (X : p.SiteMatrix) :
    tgtTraceCLM e k (c • X) = c * tgtTraceCLM e k X := by
  rw [scb_traceCLM_apply, scb_traceCLM_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Matrix.smul_apply, smul_eq_mul]; ring
  · ring

/-- `W⁻¹Tr P_e M + W⁻¹Tr P_{e+1} M = W⁻¹ Tr M` on the pair. -/
theorem scb_pbt_add_pbt (M : PairMatrix p e) :
    pairBlockTrace p e M e + pairBlockTrace p e M (e + 1) = (p.W : ℂ)⁻¹ * M.trace := by
  unfold pairBlockTrace Matrix.trace
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply]
  rcases x.2 with h | h
  · have h' : x.1.1 ≠ e + 1 := by rw [h]; exact (rng_add_one_ne p e).symm
    rw [ite_eq_left h, ite_eq_right h', add_zero]
  · have h' : x.1.1 ≠ e := by rw [h]; exact rng_add_one_ne p e
    rw [ite_eq_right h', ite_eq_left h, zero_add]

theorem scb_pbt_sub (M N : PairMatrix p e) (k : ZMod p.n) :
    pairBlockTrace p e (M - N) k = pairBlockTrace p e M k - pairBlockTrace p e N k := by
  unfold pairBlockTrace
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Matrix.sub_apply]
  · ring

theorem scb_line_zero (H₀ : p.SiteMatrix) (E : ℝ) :
    scnLine H₀ ((0 : ZMod p.n → ℝ), E) = H₀ := by
  unfold scnLine; simp

theorem scb_add_zero_smul (H₀ P : p.SiteMatrix) : H₀ + ((0 : ℝ) : ℂ) • P = H₀ := by simp

/-- `‖W⁻¹Tr P_k ℛ(ζ)‖ ≤ 1/Im ζ`. -/
theorem scb_norm_tau_le {H : p.SiteMatrix} (hH : H.IsHermitian) (hband : IsRingBanded p H)
    (hbond : ExteriorBondsInvertible p e H) (E : ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) (k : ZMod p.n) :
    ‖tgtTraceCLM e k (ctrFull p e H E ζ)⁻¹‖ ≤ 1 / ζ.im := by
  have hdet := scn_ctrFull_det_ne hH hband hbond E hζ.ne'
  have h := scn_norm_compressed_le hH E hζ.ne' hdet
  rw [abs_of_pos hζ] at h
  rw [scn_traceCLM_eq]
  exact (scn_norm_pairBlockTrace_le _ k).trans h

/-- `‖d_k‖ = ‖W⁻¹Tr P_k ℛ²‖ ≤ 1/(Im ζ)²`. -/
theorem scb_norm_d_le {H : p.SiteMatrix} (hH : H.IsHermitian) (hband : IsRingBanded p H)
    (hbond : ExteriorBondsInvertible p e H) (E : ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) (k : ZMod p.n) :
    ‖tgtTraceCLM e k ((ctrFull p e H E ζ)⁻¹ * pairProjector p e * (ctrFull p e H E ζ)⁻¹)‖ ≤
      1 / ζ.im ^ 2 := by
  have hdet := scn_ctrFull_det_ne hH hband hbond E hζ.ne'
  have h := scn_norm_compressed_le hH E hζ.ne' hdet
  rw [abs_of_pos hζ] at h
  rw [scn_traceCLM_projector, ← scn_compressed_eq_blk]
  refine (scn_norm_pairBlockTrace_le _ k).trans ((norm_mul_le _ _).trans ?_)
  have h0 := norm_nonneg (compressedResolvent p e H E ζ)
  calc ‖compressedResolvent p e H E ζ‖ * ‖compressedResolvent p e H E ζ‖
      ≤ (1 / ζ.im) * (1 / ζ.im) := mul_le_mul h h h0 (by positivity)
    _ = 1 / ζ.im ^ 2 := by ring

/-- The Dyson equation in block-trace form: `ζ = (s/2)(W⁻¹Tr P_eℛ + W⁻¹Tr P_{e+1}ℛ)`. -/
theorem scb_root_eq_tau {H : p.SiteMatrix} {E : ℝ} {ζ : ℂ} (h : IsDysonRoot p e H E ζ) :
    ζ = (splitS p : ℂ) / 2 * (tgtTraceCLM e e (ctrFull p e H E ζ)⁻¹ +
      tgtTraceCLM e (e + 1) (ctrFull p e H E ζ)⁻¹) := by
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have h2 := h.2
  rw [scn_traceCLM_eq, scn_traceCLM_eq, ← scn_compressed_eq_blk, scb_pbt_add_pbt]
  conv_lhs => rw [h2]
  field_simp

end Helpers

/-!
## 2. The root along a `ξ_g` line
-/

section Line

variable {p : Parameters} {e : ZMod p.n}

/-- The `ξ_g` line `t ↦ H₀ + t P_{S_g}`. -/
def scbL (H₀ : p.SiteMatrix) (g : ZMod p.n) (t : ℝ) : p.SiteMatrix :=
  H₀ + (t : ℂ) • pairProjector p g

/-- The Dyson root along the line. -/
def scbZ (e : ZMod p.n) (H₀ : p.SiteMatrix) (g : ZMod p.n) (E : ℝ) (t : ℝ) : ℂ :=
  scnRoot p e (scbL H₀ g t) E

/-- `W⁻¹Tr P_k ℛ(z(t))` along the line. -/
def scbTau (e : ZMod p.n) (H₀ : p.SiteMatrix) (g : ZMod p.n) (E : ℝ) (k : ZMod p.n) (t : ℝ) : ℂ :=
  tgtTraceCLM e k (ctrFull p e (scbL H₀ g t) E (scbZ e H₀ g E t))⁻¹

theorem scb_L_zero (H₀ : p.SiteMatrix) (g : ZMod p.n) : scbL H₀ g 0 = H₀ := by
  unfold scbL; simp

theorem scb_L_isHermitian {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (g : ZMod p.n) (t : ℝ) :
    (scbL H₀ g t).IsHermitian := by
  have h := scn_line_isHermitian hH ((Pi.single g t : ZMod p.n → ℝ), (0 : ℝ))
  rwa [scn_line_single] at h

theorem scb_L_banded {H₀ : p.SiteMatrix} (hb : IsRingBanded p H₀) (g : ZMod p.n) (t : ℝ) :
    IsRingBanded p (scbL H₀ g t) := by
  have h := scn_line_banded hb ((Pi.single g t : ZMod p.n → ℝ), (0 : ℝ))
  rwa [scn_line_single] at h

theorem scb_L_bonds {H₀ : p.SiteMatrix} (hbd : ExteriorBondsInvertible p e H₀) (g : ZMod p.n)
    (t : ℝ) : ExteriorBondsInvertible p e (scbL H₀ g t) := by
  have h := scn_line_bonds hbd ((Pi.single g t : ZMod p.n → ℝ), (0 : ℝ))
  rwa [scn_line_single] at h

/-- **The root along a `ξ_g` line**: `z(0) = ζ`, `z` is differentiable at `0` and is a Dyson root
near `0` (from the implicit-function theorem `scn_root_contDiffAt`). -/
theorem scb_line_root {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} {ζ : ℂ} (hroot : IsDysonRoot p e H₀ E ζ)
    (g : ZMod p.n) :
    scbZ e H₀ g E 0 = ζ ∧ DifferentiableAt ℝ (scbZ e H₀ g E) 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), IsDysonRoot p e (scbL H₀ g t) E (scbZ e H₀ g E t) := by
  set γ : ℝ → (ZMod p.n → ℝ) × ℝ := fun t => ((Pi.single g t : ZMod p.n → ℝ), E) with hγ
  have hγ0 : γ 0 = ((0 : ZMod p.n → ℝ), E) := by simp [hγ]
  have hγd : ContDiff ℝ ∞ γ :=
    (contDiff_single (𝕜 := ℝ) (fun _ : ZMod p.n => ℝ) ∞ g).prodMk contDiff_const
  have hroot' : IsDysonRoot p e (scnLine H₀ (γ 0)) (γ 0).2 ζ := by
    rw [hγ0, scb_line_zero]; exact hroot
  obtain ⟨hcd, hev⟩ := scn_root_contDiffAt hH hb hbd hroot'
  have hfun : scbZ e H₀ g E = (fun x => scnRoot p e (scnLine H₀ x) x.2) ∘ γ := by
    funext t; simp only [Function.comp_apply, hγ, scn_line_single, scbZ, scbL]
  refine ⟨?_, ?_, ?_⟩
  · unfold scbZ; rw [scb_L_zero]; exact scn_root_eq hH hroot
  · rw [hfun]
    exact (hcd.differentiableAt (by simp)).comp 0 (hγd.differentiable (by simp) 0)
  · have ht : Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγd.continuous.tendsto 0
    filter_upwards [ht.eventually hev] with t ht
    have h1 : scnLine H₀ (γ t) = scbL H₀ g t := scn_line_single H₀ g t E
    rw [h1] at ht
    exact ht

end Line

/-!
## 3. Implicit differentiation
-/

section Derivs

variable {p : Parameters} {e : ZMod p.n}

/-- **Derivatives along the line**. With `A = (H₀ - E - ζP_S)⁻¹`, `z' = z'(0)`:
`∂_t W⁻¹Tr P_k ℛ(z(t)) = -W⁻¹Tr P_k[A P_g A] + z' W⁻¹Tr P_k[A P_S A]` at `t = 0`, and
`z'(1 - (s/2)Σ_k W⁻¹Tr P_k[A P_S A]) = -(s/2)Σ_k W⁻¹Tr P_k[A P_g A]` (`k ∈ {e, e+1}`). -/
theorem scb_line_derivs {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} {ζ : ℂ} (hroot : IsDysonRoot p e H₀ E ζ)
    (g : ZMod p.n) :
    (∀ k : ZMod p.n, HasDerivAt (scbTau e H₀ g E k)
      (-(tgtTraceCLM e k ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)) +
        deriv (scbZ e H₀ g E) 0 *
          tgtTraceCLM e k ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p e * (ctrFull p e H₀ E ζ)⁻¹))
      0) ∧
    deriv (scbZ e H₀ g E) 0 * (1 - (splitS p : ℂ) / 2 *
        (tgtTraceCLM e e ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p e * (ctrFull p e H₀ E ζ)⁻¹) +
          tgtTraceCLM e (e + 1)
            ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p e * (ctrFull p e H₀ E ζ)⁻¹))) =
      -((splitS p : ℂ) / 2 *
        (tgtTraceCLM e e ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹) +
          tgtTraceCLM e (e + 1)
            ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹))) := by
  obtain ⟨hz0, hzd, hev⟩ := scb_line_root hH hb hbd hroot g
  set z' := deriv (scbZ e H₀ g E) 0 with hz'
  set A := (ctrFull p e H₀ E ζ)⁻¹ with hA
  have hzD : HasDerivAt (scbZ e H₀ g E) z' 0 := hzd.hasDerivAt
  have hM : HasDerivAt (fun t => ctrFull p e (scbL H₀ g t) E (scbZ e H₀ g E t))
      (pairProjector p g - z' • pairProjector p e) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) • pairProjector p g) (pairProjector p g) 0 := by
      have := (hasDerivAt_id (0 : ℝ)).smul_const (pairProjector p g)
      simpa [Complex.coe_smul] using this
    have h2 := hzD.smul_const (pairProjector p e)
    have h3 := ((h1.const_add H₀).sub_const ((E : ℂ) • (1 : p.SiteMatrix))).sub h2
    convert h3 using 1
    funext t
    rfl
  have hdet0 : (ctrFull p e H₀ E ζ).det ≠ 0 := scn_ctrFull_det_ne hH hb hbd E hroot.1.ne'
  have hM0 : ctrFull p e (scbL H₀ g 0) E (scbZ e H₀ g E 0) = ctrFull p e H₀ E ζ := by
    rw [scb_L_zero, hz0]
  have hinv := tgt_hasDerivAt_inv_comp hM (by rw [hM0]; exact isUnit_iff_ne_zero.mpr hdet0)
  rw [hM0] at hinv
  have hexp : ∀ k : ZMod p.n, tgtTraceCLM e k (-(A * (pairProjector p g - z' • pairProjector p e) * A)) =
      -(tgtTraceCLM e k (A * pairProjector p g * A)) + z' * tgtTraceCLM e k (A * pairProjector p e * A) := by
    intro k
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, neg_sub, map_sub,
      scb_traceCLM_smul]
    ring
  have hτ : ∀ k : ZMod p.n, HasDerivAt (scbTau e H₀ g E k)
      (-(tgtTraceCLM e k (A * pairProjector p g * A)) + z' * tgtTraceCLM e k (A * pairProjector p e * A)) 0 := by
    intro k
    rw [← hexp k]
    exact (tgtTraceCLM e k).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hinv
  refine ⟨hτ, ?_⟩
  have hS := ((hτ e).add (hτ (e + 1))).const_mul ((splitS p : ℂ) / 2)
  have heq : scbZ e H₀ g E =ᶠ[𝓝 0]
      fun t => (splitS p : ℂ) / 2 * (scbTau e H₀ g E e t + scbTau e H₀ g E (e + 1) t) := by
    filter_upwards [hev] with t ht
    exact scb_root_eq_tau ht
  have h := hzD.unique (hS.congr_of_eventuallyEq heq)
  linear_combination h

/-- **Stability at the root** in block-trace form: `Re(1 - (s/2)(d_e + d_{e+1})) ≥ 2(Im ζ)²/s`. -/
theorem scb_stability {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) :
    2 * ζ.im ^ 2 / splitS p ≤ (1 - (splitS p : ℂ) / 2 *
      (tgtTraceCLM e e ((ctrFull p e H E ζ)⁻¹ * pairProjector p e * (ctrFull p e H E ζ)⁻¹) +
        tgtTraceCLM e (e + 1)
          ((ctrFull p e H E ζ)⁻¹ * pairProjector p e * (ctrFull p e H E ζ)⁻¹))).re := by
  have hst := scn_stability hH h
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have heq : (ctrK p : ℂ) * (compressedResolvent p e H E ζ * compressedResolvent p e H E ζ).trace =
      (splitS p : ℂ) / 2 *
        (tgtTraceCLM e e ((ctrFull p e H E ζ)⁻¹ * pairProjector p e * (ctrFull p e H E ζ)⁻¹) +
          tgtTraceCLM e (e + 1)
            ((ctrFull p e H E ζ)⁻¹ * pairProjector p e * (ctrFull p e H E ζ)⁻¹)) := by
    rw [scn_traceCLM_projector, scn_traceCLM_projector, scb_pbt_add_pbt, ctrK_coe,
      ← scn_compressed_eq_blk]
    field_simp
  rw [← heq]; exact hst

end Derivs

/-!
## 4. The derivative of the unclipped center
-/

section CenterDeriv

variable {p : Parameters} {e : ZMod p.n}

/-- Elementary real inequality behind `scb_hasDerivAt_U`. -/
theorem scb_real_bound {s y Aa Z T N' V' : ℝ} (hs : 0 < s) (hy : 0 < y)
    (hZ : Z * (2 * y ^ 2 / s) ≤ s / 2 * Aa) (hT : T ≤ Aa + 2 * Z / y ^ 2)
    (hN : |N'| ≤ s / 2 * T) (hV : |V'| ≤ |N'| / y + Z / y) :
    |V'| ≤ (s / (2 * y) + s ^ 3 / (4 * y ^ 5) + s ^ 2 / (4 * y ^ 3)) * Aa := by
  have hZ' : Z ≤ s ^ 2 * Aa / (4 * y ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : Z * (4 * y ^ 2) = Z * (2 * y ^ 2 / s) * (2 * s) := by field_simp; ring
    rw [h1]
    calc Z * (2 * y ^ 2 / s) * (2 * s) ≤ s / 2 * Aa * (2 * s) :=
          mul_le_mul_of_nonneg_right hZ (by positivity)
      _ = s ^ 2 * Aa := by ring
  calc |V'| ≤ |N'| / y + Z / y := hV
    _ ≤ s / 2 * (Aa + 2 * Z / y ^ 2) / y + Z / y := by
        gcongr
        exact hN.trans (by gcongr)
    _ ≤ s / 2 * (Aa + 2 * (s ^ 2 * Aa / (4 * y ^ 2)) / y ^ 2) / y + s ^ 2 * Aa / (4 * y ^ 2) / y := by
        gcongr
    _ = (s / (2 * y) + s ^ 3 / (4 * y ^ 5) + s ^ 2 / (4 * y ^ 3)) * Aa := by
        field_simp

/-- **The `ξ_g`-derivative of the unclipped center** (the part without the
cutoff): `V(t) = scnU(ℛ_{H₀+tP_g}(z(t)))` has a derivative `V'` at `0` with
`|V'| ≤ (s/(2y) + s³/(4y⁵) + s²/(4y³))(|a_e| + |a_{e+1}|)`, `y = Im ζ`,
`a_k = W⁻¹Tr P_k[A P_g A]_{SS}`, `A = (H₀ - E - ζP_S)⁻¹`. -/
theorem scb_hasDerivAt_U {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} {ζ : ℂ} (hroot : IsDysonRoot p e H₀ E ζ)
    (g : ZMod p.n) :
    ∃ V' : ℝ, HasDerivAt
        (fun t => scnU p e (compressedResolvent p e (scbL H₀ g t) E (scbZ e H₀ g E t))) V' 0 ∧
      |V'| ≤ (splitS p / (2 * ζ.im) + splitS p ^ 3 / (4 * ζ.im ^ 5) +
          splitS p ^ 2 / (4 * ζ.im ^ 3)) *
        (‖tgtTraceCLM e e ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)‖ +
          ‖tgtTraceCLM e (e + 1)
            ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)‖) := by
  obtain ⟨hz0, hzd, hev⟩ := scb_line_root hH hb hbd hroot g
  obtain ⟨hτ, himp⟩ := scb_line_derivs hH hb hbd hroot g
  have hst := scb_stability (e := e) hH hroot
  have hs0 : 0 < splitS p := ctr_splitS_pos
  have hy0 : 0 < ζ.im := hroot.1
  have hzD : HasDerivAt (scbZ e H₀ g E) (deriv (scbZ e H₀ g E) 0) 0 := hzd.hasDerivAt
  set z' := deriv (scbZ e H₀ g E) 0 with hz'
  set A := (ctrFull p e H₀ E ζ)⁻¹ with hA
  set ae := tgtTraceCLM e e (A * pairProjector p g * A) with hae
  set ae1 := tgtTraceCLM e (e + 1) (A * pairProjector p g * A) with hae1
  set de := tgtTraceCLM e e (A * pairProjector p e * A) with hde
  set de1 := tgtTraceCLM e (e + 1) (A * pairProjector p e * A) with hde1
  set s := splitS p with hs
  set y := ζ.im with hy
  set N : ℝ → ℝ := fun t => s / 2 * (scbTau e H₀ g E e t - scbTau e H₀ g E (e + 1) t).im with hN
  set Dn : ℝ → ℝ := fun t => (scbZ e H₀ g E t).im with hDn
  have hNd : HasDerivAt N (s / 2 * ((-ae + z' * de) - (-ae1 + z' * de1)).im) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hτ e).sub (hτ (e + 1)))
    exact h.const_mul (s / 2)
  have hDd : HasDerivAt Dn z'.im 0 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hzD
  have hD0 : Dn 0 = y := by simp only [hDn, hz0, hy]
  have hQ := hNd.div hDd (by rw [hD0]; exact hy0.ne')
  have heq : (fun t => scnU p e (compressedResolvent p e (scbL H₀ g t) E (scbZ e H₀ g E t)))
      =ᶠ[𝓝 0] N / Dn := by
    filter_upwards [hev] with t ht
    have hHt := scb_L_isHermitian hH g t
    have hdet := scn_ctrFull_det_ne hHt (scb_L_banded hb g t) (scb_L_bonds hbd g t) E ht.1.ne'
    rw [scn_scnU_eq hHt E ht.1.ne' hdet]
    rfl
  refine ⟨_, hQ.congr_of_eventuallyEq heq, ?_⟩
  -- the value at `0` is bounded by one
  have hV0 : |N 0 / Dn 0| ≤ 1 := by
    have h0 := heq.eq_of_nhds
    simp only [scb_L_zero, hz0] at h0
    rw [← Pi.div_apply, ← h0]
    exact scn_abs_scnU_root_le hH hroot
  rw [hD0] at hV0 ⊢
  -- the bound on `z'`
  set Δ : ℂ := 1 - (s : ℂ) / 2 * (de + de1) with hΔ
  have hΔ0 : 2 * y ^ 2 / s ≤ ‖Δ‖ := hst.trans (Complex.re_le_norm _)
  have hZ : ‖z'‖ * (2 * y ^ 2 / s) ≤ s / 2 * (‖ae‖ + ‖ae1‖) := by
    have h1 : ‖z'‖ * ‖Δ‖ = s / 2 * ‖ae + ae1‖ := by
      rw [← norm_mul, himp, norm_neg, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs0]
      norm_num
    calc ‖z'‖ * (2 * y ^ 2 / s) ≤ ‖z'‖ * ‖Δ‖ := mul_le_mul_of_nonneg_left hΔ0 (norm_nonneg _)
      _ = s / 2 * ‖ae + ae1‖ := h1
      _ ≤ s / 2 * (‖ae‖ + ‖ae1‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
  have hd : ∀ k : ZMod p.n, ‖tgtTraceCLM e k (A * pairProjector p e * A)‖ ≤ 1 / y ^ 2 :=
    fun k => scb_norm_d_le hH hb hbd E hy0 k
  have hT : ‖-ae + z' * de‖ + ‖-ae1 + z' * de1‖ ≤ (‖ae‖ + ‖ae1‖) + 2 * ‖z'‖ / y ^ 2 := by
    have h1 : ‖-ae + z' * de‖ ≤ ‖ae‖ + ‖z'‖ * (1 / y ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul]
      gcongr
      exact hd e
    have h2 : ‖-ae1 + z' * de1‖ ≤ ‖ae1‖ + ‖z'‖ * (1 / y ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg, norm_mul]
      gcongr
      exact hd (e + 1)
    have : ‖z'‖ * (1 / y ^ 2) + ‖z'‖ * (1 / y ^ 2) = 2 * ‖z'‖ / y ^ 2 := by ring
    linarith
  have hNb : |s / 2 * ((-ae + z' * de) - (-ae1 + z' * de1)).im| ≤
      s / 2 * (‖-ae + z' * de‖ + ‖-ae1 + z' * de1‖) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < s / 2)]
    gcongr
    exact (Complex.abs_im_le_norm _).trans (norm_sub_le _ _)
  refine scb_real_bound hs0 hy0 hZ hT hNb ?_
  -- `V' = N'/y - (N₀/y) Im z'/y`
  set N' := s / 2 * ((-ae + z' * de) - (-ae1 + z' * de1)).im
  have hform : (N' * y - N 0 * z'.im) / y ^ 2 = N' / y - (N 0 / y) * z'.im / y := by
    field_simp
  rw [hform]
  calc |N' / y - N 0 / y * z'.im / y| ≤ |N' / y| + |N 0 / y * z'.im / y| := abs_sub _ _
    _ = |N'| / y + |N 0 / y| * |z'.im| / y := by
        rw [abs_div, abs_div, abs_of_pos hy0, abs_mul (N 0 / y)]
    _ ≤ |N'| / y + 1 * ‖z'‖ / y := by
        gcongr
        exact Complex.abs_im_le_norm _
    _ = |N'| / y + ‖z'‖ / y := by ring

end CenterDeriv

end BlockBand.Center
