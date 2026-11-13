module

public import BlockBand.Center.SmoothConstructionBound

/-!
# The two pointwise bounds of the smooth center

* §1 at one configuration (Hermitian, ring-banded `H₀`, invertible exterior bonds, a Dyson root
  `ζ`, `ζ₀ = sμ(E)`): `scp_abs_U_le` (the contrast at the root is the residual difference plus
  `O(|ζ - ζ₀|)`), `scp_a_le` (off the exterior poles, `|W⁻¹Tr P_k[AP_gA]| ≤ |∂_{ξ_g}ε_{e,k}| +
  |ζ - ζ₀|(6 + 3|ζ-ζ₀|/Im ζ)/Im ζ · |λ_{eg}|`, from `scn_D_diff_le` and `scn_tgtLambda_eq`);
* §2 the `ξ_g`-derivative of `j^{sm}_e = χ_E(E)χ(ε_e²/ε₁²)j_e` on the root branch
  (`scp_deriv_phi_le`);
* §3 **`scp_level`**: for each grid level `k` one constant `C` for every `p` with `p.b = b`, every
  `ϑ`-bulk rank of level `k` and every admissible `(H₀, E)` off the exterior poles:
  `|j^{sm}_e| ≤ C(|ε_{e,e}| + |ε_{e,e+1}|)` and
  `|∂_{ξ_g} j^{sm}_e| ≤ C(Σ_k |∂_{ξ_g}ε_{e,k}| + (Σ_k |ε_{e,k}|)|λ_{eg}|)`.
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
## 1. One configuration
-/

section Config

variable {p : Parameters} {e : ZMod p.n}

theorem scp_zeta0_im_pos {E : ℝ} (hE : |E| < 2) : 0 < ((splitS p : ℂ) * tgtMu E).im :=
  tgt_zeta_im_pos (p := p) hE

/-- `Im(sμ(E)) ≥ s√θ/2` for `|E| ≤ 2 - θ`, `0 < θ ≤ 2`. -/
theorem scp_zeta0_im_ge {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ ≤ 2) {E : ℝ} (hE : |E| ≤ 2 - θ) :
    splitS p * Real.sqrt θ / 2 ≤ ((splitS p : ℂ) * tgtMu E).im := by
  have hs : 0 < splitS p := ctr_splitS_pos
  rw [Complex.im_ofReal_mul, scn_tgtMu_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hE2 : E ^ 2 ≤ (2 - θ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hE 2
  have h4 : θ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt h4
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hs.le

/-- `‖sμ(E)‖ ≤ 1` and `‖ζ - sμ‖ ≤ 2` for a root, `|E| ≤ 2`. -/
theorem scp_dist_le_two {H : p.SiteMatrix} (hH : H.IsHermitian) {E : ℝ} (hE : |E| ≤ 2) {ζ : ℂ}
    (h : IsDysonRoot p e H E ζ) : ‖ζ - (splitS p : ℂ) * tgtMu E‖ ≤ 2 := by
  have hμ : ‖tgtMu E‖ = 1 := by
    unfold tgtMu; rw [Complex.norm_conj]; exact ctr_norm_matchedA hE
  have h1 : ‖(splitS p : ℂ) * tgtMu E‖ ≤ 1 := by
    rw [norm_mul, hμ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ctr_splitS_pos]
    exact ctr_splitS_le_one
  have h2 := scn_root_norm_le hH h
  linarith [norm_sub_le ζ ((splitS p : ℂ) * tgtMu E)]

/-- **The center at the root is a residual difference**:
`|j_e| ≤ (s/2)(|ε_{e,e}| + |ε_{e,e+1}| + 2|ζ - ζ₀|/(Im ζ Im ζ₀))/Im ζ`, `ζ₀ = sμ(E)`. -/
theorem scp_abs_U_le {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} (hE : |E| < 2) {ζ : ℂ}
    (hroot : IsDysonRoot p e H₀ E ζ) :
    |scnU p e (compressedResolvent p e H₀ E ζ)| ≤
      splitS p / 2 * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖ +
        2 * ‖ζ - (splitS p : ℂ) * tgtMu E‖ / (ζ.im * ((splitS p : ℂ) * tgtMu E).im)) / ζ.im := by
  set ζ₀ := (splitS p : ℂ) * tgtMu E with hζ₀
  have hy : 0 < ζ.im := hroot.1
  have hy₀ : 0 < ζ₀.im := scp_zeta0_im_pos hE
  have hs : 0 < splitS p := ctr_splitS_pos
  have h₁ := scn_ctrFull_det_ne hH hb hbd E hy.ne'
  have h₀ := scn_ctrFull_det_ne hH hb hbd E hy₀.ne'
  set R := compressedResolvent p e H₀ E ζ with hR
  set R₀ := compressedResolvent p e H₀ E ζ₀ with hR₀
  have hRn : ‖R‖ ≤ 1 / ζ.im := by
    have := scn_norm_compressed_le hH E hy.ne' h₁; rwa [abs_of_pos hy] at this
  have hR₀n : ‖R₀‖ ≤ 1 / ζ₀.im := by
    have := scn_norm_compressed_le hH E hy₀.ne' h₀; rwa [abs_of_pos hy₀] at this
  have hsub : R - R₀ = (ζ - ζ₀) • (R * R₀) := by
    have := scn_blk_sub H₀ E h₁ h₀ e e
    rw [← scn_compressed_eq_blk, ← scn_compressed_eq_blk] at this
    exact this
  have hdiff : ‖R - R₀‖ ≤ ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) := by
    rw [hsub]
    refine (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left (norm_mul_le _ _)
      (norm_nonneg _)).trans ?_)
    calc ‖ζ - ζ₀‖ * (‖R‖ * ‖R₀‖) ≤ ‖ζ - ζ₀‖ * ((1 / ζ.im) * (1 / ζ₀.im)) := by
          gcongr
      _ = ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) := by field_simp
  have hk : ∀ k : ZMod p.n, pairBlockTrace p e R k =
      tgtEps p e H₀ E k + tgtMu E + pairBlockTrace p e (R - R₀) k := by
    intro k
    rw [scb_pbt_sub]
    unfold tgtEps tgtR0
    ring
  rw [scn_scnU_eq hH E hy.ne' h₁, abs_div, abs_mul, abs_of_pos hy,
    abs_of_pos (by positivity : 0 < splitS p / 2)]
  refine div_le_div_of_nonneg_right ?_ hy.le
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [hk e, hk (e + 1)]
  have hd : ∀ k : ZMod p.n, ‖pairBlockTrace p e (R - R₀) k‖ ≤ ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) :=
    fun k => (scn_norm_pairBlockTrace_le _ k).trans hdiff
  have heq : tgtEps p e H₀ E e + tgtMu E + pairBlockTrace p e (R - R₀) e -
      (tgtEps p e H₀ E (e + 1) + tgtMu E + pairBlockTrace p e (R - R₀) (e + 1)) =
      (tgtEps p e H₀ E e - tgtEps p e H₀ E (e + 1)) +
        (pairBlockTrace p e (R - R₀) e - pairBlockTrace p e (R - R₀) (e + 1)) := by ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_sub_le (tgtEps p e H₀ E e) (tgtEps p e H₀ E (e + 1))
  have h2 := norm_sub_le (pairBlockTrace p e (R - R₀) e) (pairBlockTrace p e (R - R₀) (e + 1))
  have h3 := hd e
  have h4 := hd (e + 1)
  have h5 : 2 * ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) =
      ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) + ‖ζ - ζ₀‖ / (ζ.im * ζ₀.im) := by ring
  linarith

/-- **The tagged derivative at the root**, off the exterior poles:
`|W⁻¹Tr P_k[A P_g A]| ≤ |∂_{ξ_g}ε_{e,k}| + |ζ - ζ₀|((6 + 3|ζ - ζ₀|/Im ζ)/Im ζ)|λ_{eg}|`. -/
theorem scp_a_le {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} (hE : |E| < 2)
    (hdet : (exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0) {ζ : ℂ}
    (hroot : IsDysonRoot p e H₀ E ζ) (g k : ZMod p.n) :
    ‖tgtTraceCLM e k ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)‖ ≤
      ‖tgtXiDeriv p (fun H => tgtEps p e H E k) g H₀‖ +
        ‖ζ - (splitS p : ℂ) * tgtMu E‖ *
          ((6 + 3 * ‖ζ - (splitS p : ℂ) * tgtMu E‖ / ζ.im) / ζ.im) * ‖tgtLambda p e g H₀ E‖ := by
  set ζ₀ := (splitS p : ℂ) * tgtMu E with hζ₀
  have hy : 0 < ζ.im := hroot.1
  have hy₀ : 0 < ζ₀.im := scp_zeta0_im_pos hE
  have h₁ := scn_ctrFull_det_ne hH hb hbd E hy.ne'
  have h₀ := scn_ctrFull_det_ne hH hb hbd E hy₀.ne'
  have hder : tgtXiDeriv p (fun H => tgtEps p e H E k) g H₀ =
      tgtTraceCLM e k (-((ctrFull p e H₀ E ζ₀)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ₀)⁻¹)) :=
    (tgt_hasDerivAt_eps_xi g h₀ k).deriv
  have hlam := scn_tgtLambda_eq hH hdet h₀ g
  have hlamn : ‖tgtLambda p e g H₀ E‖ = (p.W : ℝ)⁻¹ * scnHS (scnBlk (ctrFull p e H₀ E ζ₀)⁻¹ g e) := by
    rw [hlam, Complex.norm_real, Real.norm_of_nonneg (by
      have := scnHS_nonneg (scnBlk (ctrFull p e H₀ E ζ₀)⁻¹ g e); positivity)]
  have hD := scn_D_diff_le hH E hy hy₀ h₁ h₀ g k
  rw [← scn_traceCLM_projector, ← scn_traceCLM_projector] at hD
  rw [hder, map_neg, norm_neg, hlamn]
  have := norm_le_insert' (tgtTraceCLM e k ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g *
    (ctrFull p e H₀ E ζ)⁻¹)) (tgtTraceCLM e k ((ctrFull p e H₀ E ζ₀)⁻¹ * pairProjector p g *
    (ctrFull p e H₀ E ζ₀)⁻¹))
  linarith

end Config

/-!
## 2. The `ξ_g`-derivative of `j^{sm}_e` on the root branch
-/

section PhiDeriv

variable {p : Parameters} {e : ZMod p.n}

/-- `t ↦ ε_{e,k}(H₀ + tP_g)` has derivative `∂_{ξ_g}ε_{e,k}` at `0` (`|E| < 2`). -/
theorem scp_hasDerivAt_eps {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} (hE : |E| < 2) (g k : ZMod p.n) :
    HasDerivAt (fun t => tgtEps p e (scbL H₀ g t) E k)
      (tgtXiDeriv p (fun H => tgtEps p e H E k) g H₀) 0 := by
  have h₀ := scn_ctrFull_det_ne hH hb hbd E (scp_zeta0_im_pos (p := p) hE).ne'
  have h := tgt_hasDerivAt_eps_xi g h₀ k
  have hd : tgtXiDeriv p (fun H => tgtEps p e H E k) g H₀ = _ := h.deriv
  rw [← hd] at h
  exact h

/-- The squared residual along the line has derivative
`2⟪ε_{e,e}, ∂ε_{e,e}⟫ + 2⟪ε_{e,e+1}, ∂ε_{e,e+1}⟫` at `0`. -/
theorem scp_hasDerivAt_eps2 {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} (hE : |E| < 2) (g : ZMod p.n) :
    HasDerivAt (fun t => scnEps2 p e (scbL H₀ g t) E)
      (2 * inner ℝ (tgtEps p e H₀ E e) (tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀) +
        2 * inner ℝ (tgtEps p e H₀ E (e + 1))
          (tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀)) 0 := by
  have h1 := (scp_hasDerivAt_eps hH hb hbd hE g e).norm_sq
  have h2 := (scp_hasDerivAt_eps hH hb hbd hE g (e + 1)).norm_sq
  simp only [scb_L_zero] at h1 h2
  exact h1.add h2

/-- **The `ξ_g`-derivative of the smooth center on the root branch**:
for `p.b = b`, a `ϑ`-bulk rank and a Dyson root `ζ` at `(H₀, E)`, `|E| < 2`, with
`χ = scnBump 1 (9/4)`, `|χ'| ≤ C_b`, `ε₁ = cst0.ε₁`:
`|∂_t j^{sm}_e(H₀ + tP_g)| ≤ C_b(2|ε_{e,e}||∂ε_{e,e}| + 2|ε_{e,e+1}||∂ε_{e,e+1}|)/ε₁² +
(s/(2y) + s³/(4y⁵) + s²/(4y³))(|a_e| + |a_{e+1}|)`. -/
theorem scp_deriv_phi_le {b ϑ : ℝ} {α : Fin p.N} (hpb : p.b = b) (hα : IsBulkRank p ϑ α)
    {H₀ : p.SiteMatrix} (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀)
    (hbd : ExteriorBondsInvertible p e H₀) {E : ℝ} (hE : |E| < 2) {ζ : ℂ}
    (hroot : IsDysonRoot p e H₀ E ζ) (g : ZMod p.n) {Cb : ℝ}
    (hCb : ∀ x, |deriv (scnBump 1 (9 / 4)) x| ≤ Cb) :
    |deriv (fun t => scnPhi b ϑ p α e (scbL H₀ g t) E) 0| ≤
      Cb * ((2 * ‖tgtEps p e H₀ E e‖ * ‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
          2 * ‖tgtEps p e H₀ E (e + 1)‖ *
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖) /
          cst0.ε₁ p.b (rankMargin p α) ^ 2) +
      (splitS p / (2 * ζ.im) + splitS p ^ 3 / (4 * ζ.im ^ 5) + splitS p ^ 2 / (4 * ζ.im ^ 3)) *
        (‖tgtTraceCLM e e ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)‖ +
          ‖tgtTraceCLM e (e + 1)
            ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g * (ctrFull p e H₀ E ζ)⁻¹)‖) := by
  obtain ⟨hz0, -, hev⟩ := scb_line_root hH hb hbd hroot g
  obtain ⟨V', hV', hVb⟩ := scb_hasDerivAt_U hH hb hbd hroot g
  set a := cst0.ε₁ p.b (rankMargin p α) with ha
  set cE := scnBump (2 - rankMargin p α) (2 - scnMid (rankMargin p α)) E with hcE
  set χ := scnBump 1 (9 / 4) with hχ
  set q : ℝ → ℝ := fun t => scnEps2 p e (scbL H₀ g t) E / a ^ 2 with hq
  set V : ℝ → ℝ := fun t =>
    scnU p e (compressedResolvent p e (scbL H₀ g t) E (scbZ e H₀ g E t)) with hV
  set i0 := inner ℝ (tgtEps p e H₀ E e) (tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀)
  set i1 := inner ℝ (tgtEps p e H₀ E (e + 1))
    (tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀)
  have hqd : HasDerivAt q ((2 * i0 + 2 * i1) / a ^ 2) 0 :=
    (scp_hasDerivAt_eps2 hH hb hbd hE g).div_const (a ^ 2)
  have hχd : HasDerivAt χ (deriv χ (q 0)) (q 0) :=
    ((scn_bump_contDiff 1 (9 / 4)).differentiable (by simp) (q 0)).hasDerivAt
  have hprod := ((hχd.comp 0 hqd).const_mul cE).mul hV'
  have heq : (fun t => scnPhi b ϑ p α e (scbL H₀ g t) E) =ᶠ[𝓝 0]
      fun t => cE * (χ ∘ q) t * V t := by
    filter_upwards [hev] with t ht
    rw [scn_phi_of_good ⟨hpb, hα, scb_L_isHermitian hH g t, _, ht⟩]
    rfl
  rw [(hprod.congr_of_eventuallyEq heq).deriv]
  have hV0 : |V 0| ≤ 1 := by
    simp only [hV, scb_L_zero, hz0]
    exact scn_abs_scnU_root_le hH hroot
  have hcE : |cE| ≤ 1 := scn_abs_bump_le _ _ _
  have hχ0 : |(χ ∘ q) 0| ≤ 1 := scn_abs_bump_le _ _ _
  have hq' : |(2 * i0 + 2 * i1) / a ^ 2| ≤
      (2 * ‖tgtEps p e H₀ E e‖ * ‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
        2 * ‖tgtEps p e H₀ E (e + 1)‖ *
          ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖) / a ^ 2 := by
    have ha0 : 0 < a := cst0.ε₁_pos p.b (rankMargin p α)
    have ha2 : 0 < a ^ 2 := by positivity
    rw [abs_div, abs_of_pos ha2]
    refine div_le_div_of_nonneg_right ?_ ha2.le
    have h0 := abs_real_inner_le_norm (tgtEps p e H₀ E e)
      (tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀)
    have h1 := abs_real_inner_le_norm (tgtEps p e H₀ E (e + 1))
      (tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_two]
    linarith
  have hχ' := hCb (q 0)
  have hCb0 : 0 ≤ Cb := (abs_nonneg _).trans hχ'
  calc |cE * (deriv χ (q 0) * ((2 * i0 + 2 * i1) / a ^ 2)) * V 0 + cE * (χ ∘ q) 0 * V'|
      ≤ |cE * (deriv χ (q 0) * ((2 * i0 + 2 * i1) / a ^ 2)) * V 0| + |cE * (χ ∘ q) 0 * V'| :=
        abs_add_le _ _
    _ = |cE| * (|deriv χ (q 0)| * |(2 * i0 + 2 * i1) / a ^ 2|) * |V 0| +
          |cE| * |(χ ∘ q) 0| * |V'| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
    _ ≤ 1 * (Cb * ((2 * ‖tgtEps p e H₀ E e‖ *
            ‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
          2 * ‖tgtEps p e H₀ E (e + 1)‖ *
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖) / a ^ 2)) * 1 +
          1 * 1 * |V'| := by
        gcongr
    _ ≤ _ := by
        rw [one_mul, mul_one, one_mul, one_mul]
        exact add_le_add le_rfl hVb

end PhiDeriv

/-!
## 3. Level-uniform constants
-/

section Level

theorem scp_real_combine {Cb a KV LK C1 C2 D SΛ : ℝ} (hC2 : C2 = 3 * Cb / a + KV * (1 + 2 * LK))
    (h3 : 0 ≤ 3 * Cb / a) (hKV : 0 ≤ KV) (hLK : 0 ≤ LK) (hC1 : 0 ≤ C1) (hD : 0 ≤ D)
    (hSΛ : 0 ≤ SΛ) : 3 * Cb / a * D + KV * (D + 2 * LK * SΛ) ≤ (C1 + C2) * (D + SΛ) := by
  rw [hC2]
  nlinarith [mul_nonneg hKV (mul_nonneg hLK hD), mul_nonneg h3 hSΛ, mul_nonneg hKV hSΛ,
    mul_nonneg hC1 hD, mul_nonneg hC1 hSΛ]

theorem scp_sqrt_le_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x ^ 2 + y ^ 2) ≤ x + y := by
  calc Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt ((x + y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = x + y := Real.sqrt_sq (by positivity)

theorem scp_centerResidual_le {p : Parameters} {e : ZMod p.n} (H : p.SiteMatrix) (E : ℝ) :
    centerResidual p e H E ≤ ‖tgtEps p e H E e‖ + ‖tgtEps p e H E (e + 1)‖ := by
  rw [scn_centerResidual_eq]
  exact scp_sqrt_le_add (norm_nonneg _) (norm_nonneg _)

/-- **Both pointwise bounds with one constant per grid level**, off the exterior poles.
For `0 < b < 1/2`, `ϑ > 0` and a level `k` there is `C ≥ 0` such that for
every `p` with `p.b = b`, every `ϑ`-bulk rank `α` with `ctrLevel κ_α = k`, every edge `e`, every
Hermitian, ring-banded `H₀` with invertible exterior bonds and every real `E` with
`H₀^{(e)}_R - E` invertible: `|j^{sm}_e| ≤ C(|ε_{e,e}| + |ε_{e,e+1}|)` and, for every `g`,
`|∂_{ξ_g} j^{sm}_e| ≤ C(|∂_{ξ_g}ε_{e,e}| + |∂_{ξ_g}ε_{e,e+1}| + (|ε_{e,e}| + |ε_{e,e+1}|)|λ_{eg}|)`.
`C` depends on `b` and `k` only (through `s = min(1-2b, b)`, the certificate data at
`θ_k`, the Lipschitz constant of `scn_root_lipschitz` and the bump). -/
theorem scp_level {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {ϑ : ℝ} (hϑ : 0 < ϑ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameters), p.b = b → ∀ α : Fin p.N, IsBulkRank p ϑ α →
      ctrLevel (rankMargin p α) = k → ∀ (e : ZMod p.n) (H₀ : p.SiteMatrix) (E : ℝ),
      H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
      (exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0 →
      |scnPhi b ϑ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) ∧
      ∀ g : ZMod p.n,
        |deriv (fun t : ℝ => scnPhi b ϑ p α e (H₀ + (t : ℂ) • pairProjector p g) E) 0| ≤
          C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖ +
            (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) * ‖tgtLambda p e g H₀ E‖) := by
  set s := ctrC b with hs
  have hs0 : 0 < s := lt_min (by linarith) hb0
  have hs1 : s < 1 := (min_le_right _ _).trans_lt (by linarith)
  set θ := ctrTheta k with hθ
  have hθ0 : 0 < θ := ctrTheta_pos k
  have hθ2 : θ ≤ 2 := ctrTheta_le_two k
  have hspec := ctrCert_spec hs0 hs1 hθ0 hθ2
  set v₀ := (ctrCert s θ).2.2.2 with hv₀
  have hv0 : 0 < v₀ := hspec.2.1.2.2.2.2.2
  set a := (ctrCert s θ).1 / 2 with ha
  have ha0 : 0 < a := half_pos (ctrCert_fst_pos _ _)
  set y₁ := s * v₀ with hy₁
  have hy₁0 : 0 < y₁ := mul_pos hs0 hv0
  obtain ⟨L, hL0, hL⟩ := scn_root_lipschitz hs0 hs1 hθ0 hθ2
  obtain ⟨Cb, hCb0, hCb⟩ := scn_bump_deriv_bound 1 (9 / 4)
  set y₀ := s * Real.sqrt θ / 2 with hy₀
  have hy₀0 : 0 < y₀ := by have := Real.sqrt_pos.mpr hθ0; positivity
  set C1 := s / 2 * (1 + 2 * L / (y₁ * y₀)) / y₁ with hC1
  set KV := s / (2 * y₁) + s ^ 3 / (4 * y₁ ^ 5) + s ^ 2 / (4 * y₁ ^ 3) with hKV
  set K1 := (6 + 6 / y₁) / y₁ with hK1
  set C2 := 3 * Cb / a + KV * (1 + 2 * L * K1) with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hKV0 : 0 ≤ KV := by positivity
  have hK10 : 0 ≤ K1 := by positivity
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro p hpb α hα hk e H₀ E hH hb hbd hdet
  have hsp : splitS p = s := by rw [ctr_splitS_eq, hpb]
  set κ := rankMargin p α with hκ
  have hκ0 : 0 < κ := scn_rankMargin_pos hϑ hα
  have hθκ : θ < κ := by rw [hθ, ← hk]; exact scn_theta_lt hκ0
  have hmid : scnMid κ = (κ + θ) / 2 := by unfold scnMid; rw [hk]
  have ha' : cst0.ε₁ p.b κ = a := by rw [scn_cst0_eps1, hpb, hk]
  set S₁ := ‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖ with hS₁
  have hS₁0 : 0 ≤ S₁ := by positivity
  have hR : ∀ g : ZMod p.n, 0 ≤ ‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
      ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖ + S₁ * ‖tgtLambda p e g H₀ E‖ :=
    fun g => by positivity
  by_cases hEo : 2 - scnMid κ ≤ |E|
  · refine ⟨?_, fun g => ?_⟩
    · rw [scn_phi_zero_of_energy hEo, abs_zero]; positivity
    · have : (fun t : ℝ => scnPhi b ϑ p α e (H₀ + (t : ℂ) • pairProjector p g) E) = fun _ => 0 :=
        funext fun t => scn_phi_zero_of_energy hEo
      rw [this, deriv_const, abs_zero]
      exact mul_nonneg (by positivity) (hR g)
  push Not at hEo
  have hEθ : |E| ≤ 2 - θ := by rw [hmid] at hEo; linarith
  have hE2 : |E| < 2 := by linarith
  by_cases hεo : 9 / 4 * a ^ 2 < scnEps2 p e H₀ E
  · have hzero : ∀ H : p.SiteMatrix, 9 / 4 * a ^ 2 < scnEps2 p e H E →
        scnPhi b ϑ p α e H E = 0 := by
      intro H hH'
      refine scn_phi_zero_of_eps ?_
      rw [ha']
      have hpos : 0 < scnEps2 p e H E / a ^ 2 :=
        div_pos (lt_of_le_of_lt (by positivity) hH') (by positivity)
      rw [abs_of_pos hpos, le_div_iff₀ (by positivity)]
      exact hH'.le
    refine ⟨?_, fun g => ?_⟩
    · rw [hzero H₀ hεo, abs_zero]; positivity
    · have hc := (scp_hasDerivAt_eps2 hH hb hbd hE2 g).continuousAt
      have h0 : scnEps2 p e (scbL H₀ g 0) E = scnEps2 p e H₀ E := by rw [scb_L_zero]
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 9 / 4 * a ^ 2 < scnEps2 p e (scbL H₀ g t) E :=
        hc.eventually (lt_mem_nhds (by simp only []; rw [h0]; exact hεo))
      have heq : (fun t : ℝ => scnPhi b ϑ p α e (H₀ + (t : ℂ) • pairProjector p g) E) =ᶠ[𝓝 0]
          fun _ => 0 := by
        filter_upwards [hev] with t ht
        exact hzero _ ht
      rw [heq.deriv_eq, deriv_const, abs_zero]
      exact mul_nonneg (by positivity) (hR g)
  push Not at hεo
  -- the root branch
  have hE2def : scnEps2 p e H₀ E = ‖tgtEps p e H₀ E e‖ ^ 2 + ‖tgtEps p e H₀ E (e + 1)‖ ^ 2 :=
    rfl
  have h94 : (3 / 2 * a) ^ 2 = 9 / 4 * a ^ 2 := by ring
  have he0 : ‖tgtEps p e H₀ E e‖ ≤ 3 / 2 * a := by
    have h1 := sq_nonneg ‖tgtEps p e H₀ E (e + 1)‖
    have hsq : ‖tgtEps p e H₀ E e‖ ^ 2 ≤ (3 / 2 * a) ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have he1 : ‖tgtEps p e H₀ E (e + 1)‖ ≤ 3 / 2 * a := by
    have h1 := sq_nonneg ‖tgtEps p e H₀ E e‖
    have hsq : ‖tgtEps p e H₀ E (e + 1)‖ ^ 2 ≤ (3 / 2 * a) ^ 2 := by linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hcR : centerResidual p e H₀ E ≤ (ctrCert (splitS p) (ctrTheta k)).1 := by
    rw [hsp, scn_centerResidual_eq]
    have : Real.sqrt (scnEps2 p e H₀ E) ≤ 3 / 2 * a := by
      rw [show 3 / 2 * a = Real.sqrt ((3 / 2 * a) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2a : (ctrCert s θ).1 = 2 * a := by rw [ha]; ring
    rw [← hθ, h2a]; linarith
  obtain ⟨ζ, hroot, hζim⟩ := scn_cert_root hH hdet (by rw [← hθ]; exact hEθ) hcR
  rw [hsp] at hζim
  have hy : y₁ ≤ ζ.im := hζim
  have hy0 : 0 < ζ.im := hroot.1
  have hr : scnRoot p e H₀ E = ζ := scn_root_eq hH hroot
  set δ := ‖ζ - (splitS p : ℂ) * tgtMu E‖ with hδ
  have hδL : δ ≤ L * S₁ := by
    have h := hL p hsp e H₀ hH E hdet hEθ ζ hroot
    rw [hδ, hsp]
    exact h.trans (mul_le_mul_of_nonneg_left (scp_centerResidual_le H₀ E) hL0)
  have hδ2 : δ ≤ 2 := scp_dist_le_two hH hE2.le hroot
  have hδ0 : 0 ≤ δ := norm_nonneg _
  refine ⟨?_, fun g => ?_⟩
  · -- `|j^{sm}_e| ≤ C ε_e`
    rw [scn_phi_of_good ⟨hpb, hα, hH, ζ, hroot⟩, hr, abs_mul, abs_mul]
    have hU := scp_abs_U_le hH hb hbd hE2 hroot
    have hy₀' : y₀ ≤ ((splitS p : ℂ) * tgtMu E).im := by
      have := scp_zeta0_im_ge (p := p) hθ0 hθ2 hEθ
      rw [hsp] at this; rw [hsp]; exact this
    have hsp0 : 0 < splitS p := ctr_splitS_pos
    have hU' : |scnU p e (compressedResolvent p e H₀ E ζ)| ≤ C1 * S₁ := by
      refine hU.trans ?_
      have hX : 2 * δ / (ζ.im * ((splitS p : ℂ) * tgtMu E).im) ≤ 2 * (L * S₁) / (y₁ * y₀) := by
        gcongr
      calc splitS p / 2 * (S₁ + 2 * δ / (ζ.im * ((splitS p : ℂ) * tgtMu E).im)) / ζ.im
          ≤ splitS p / 2 * (S₁ + 2 * (L * S₁) / (y₁ * y₀)) / y₁ := by
            gcongr
        _ = C1 * S₁ := by rw [hC1, hsp]; ring
    have h1 := scn_abs_bump_le (2 - κ) (2 - scnMid κ) E
    have h2 := scn_abs_bump_le 1 (9 / 4) (scnEps2 p e H₀ E / cst0.ε₁ p.b κ ^ 2)
    calc |scnBump (2 - κ) (2 - scnMid κ) E| *
          |scnBump 1 (9 / 4) (scnEps2 p e H₀ E / cst0.ε₁ p.b κ ^ 2)| *
          |scnU p e (compressedResolvent p e H₀ E ζ)| ≤ 1 * 1 * (C1 * S₁) := by gcongr
      _ ≤ (C1 + C2) * S₁ := by
          rw [one_mul, one_mul]; exact mul_le_mul_of_nonneg_right (by linarith) hS₁0
  · -- `|∂_{ξ_g} j^{sm}_e| ≤ C(Σ|∂ε| + ε λ)`
    change |deriv (fun t => scnPhi b ϑ p α e (scbL H₀ g t) E) 0| ≤ _
    have hd := scp_deriv_phi_le hpb hα hH hb hbd hE2 hroot g hCb
    rw [ha', hsp] at hd
    have hA0 := scp_a_le hH hb hbd hE2 hdet hroot g e
    have hA1 := scp_a_le hH hb hbd hE2 hdet hroot g (e + 1)
    rw [← hδ] at hA0 hA1
    set d0 := ‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖
    set d1 := ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖
    set Λ := ‖tgtLambda p e g H₀ E‖
    set e0 := ‖tgtEps p e H₀ E e‖
    set e1 := ‖tgtEps p e H₀ E (e + 1)‖
    set A0 := ‖tgtTraceCLM e e ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g *
      (ctrFull p e H₀ E ζ)⁻¹)‖
    set A1 := ‖tgtTraceCLM e (e + 1) ((ctrFull p e H₀ E ζ)⁻¹ * pairProjector p g *
      (ctrFull p e H₀ E ζ)⁻¹)‖
    have hd0 : 0 ≤ d0 := norm_nonneg _
    have hd1 : 0 ≤ d1 := norm_nonneg _
    have hΛ : 0 ≤ Λ := norm_nonneg _
    have hfac : δ * ((6 + 3 * δ / ζ.im) / ζ.im) ≤ L * S₁ * K1 := by
      have h3 : 3 * δ / ζ.im ≤ 6 / y₁ := by
        rw [div_le_div_iff₀ hy0 hy₁0]
        calc 3 * δ * y₁ ≤ 3 * 2 * y₁ := by gcongr
          _ ≤ 6 * ζ.im := by linarith
      have h4 : (6 + 3 * δ / ζ.im) / ζ.im ≤ (6 + 6 / y₁) / y₁ :=
        div_le_div₀ (by positivity) (by linarith) hy₁0 hy
      rw [hK1]
      exact mul_le_mul hδL h4 (by positivity) (by positivity)
    have hAa : A0 + A1 ≤ d0 + d1 + 2 * (L * K1) * (S₁ * Λ) := by
      have h5 : δ * ((6 + 3 * δ / ζ.im) / ζ.im) * Λ ≤ L * S₁ * K1 * Λ :=
        mul_le_mul_of_nonneg_right hfac hΛ
      have h6 : 2 * (L * K1) * (S₁ * Λ) = L * S₁ * K1 * Λ + L * S₁ * K1 * Λ := by ring
      linarith
    have hKVy : s / (2 * ζ.im) + s ^ 3 / (4 * ζ.im ^ 5) + s ^ 2 / (4 * ζ.im ^ 3) ≤ KV := by
      rw [hKV]; gcongr
    have hfirst : Cb * ((2 * e0 * d0 + 2 * e1 * d1) / a ^ 2) ≤ 3 * Cb / a * (d0 + d1) := by
      have h6 : 2 * e0 * d0 + 2 * e1 * d1 ≤ 3 * a * (d0 + d1) := by
        have h7 : 2 * e0 * d0 ≤ 3 * a * d0 := by
          have := mul_le_mul_of_nonneg_right he0 hd0; linarith
        have h8 : 2 * e1 * d1 ≤ 3 * a * d1 := by
          have := mul_le_mul_of_nonneg_right he1 hd1; linarith
        linarith
      calc Cb * ((2 * e0 * d0 + 2 * e1 * d1) / a ^ 2) ≤ Cb * (3 * a * (d0 + d1) / a ^ 2) := by
            gcongr
        _ = 3 * Cb / a * (d0 + d1) := by field_simp
    have hA0n : 0 ≤ A0 + A1 := by positivity
    have hKVA : (s / (2 * ζ.im) + s ^ 3 / (4 * ζ.im ^ 5) + s ^ 2 / (4 * ζ.im ^ 3)) * (A0 + A1) ≤
        KV * (d0 + d1 + 2 * (L * K1) * (S₁ * Λ)) :=
      mul_le_mul hKVy hAa hA0n hKV0
    have hSΛ : 0 ≤ S₁ * Λ := by positivity
    have hLK : 0 ≤ L * K1 := by positivity
    have h3Cb : 0 ≤ 3 * Cb / a := by positivity
    calc |deriv (fun t => scnPhi b ϑ p α e (scbL H₀ g t) E) 0|
        ≤ 3 * Cb / a * (d0 + d1) + KV * (d0 + d1 + 2 * (L * K1) * (S₁ * Λ)) := by linarith
      _ ≤ (C1 + C2) * (d0 + d1 + S₁ * Λ) :=
          scp_real_combine (by rw [hC2]; ring) h3Cb hKV0 hLK hC10 (add_nonneg hd0 hd1) hSΛ

end Level

end BlockBand.Center
