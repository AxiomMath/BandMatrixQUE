module

public import BlockBand.Critical.CommonPort.Mean

/-!
# Common-port mean: the assembly inequality

Deterministic; no measure. Domain: `0 < b < 1/2`, `|e| < 2`, `|a| = 1`, `Im a ≤ -α₀ < 0`
(`a = matchedA e`), Hermitian `X`, an error scale `ε ≥ 0` with `δ = matchedDistance b e X ≤ ε`
and the smallness condition `asmSmall · ε ≤ 1`. Norms: operator norm, complex modulus.

* constants `asmY`, `asmEta`, `asmV`, `asmGap`, `asmSig`, `asmConst`, `asmSmall`
  (functions of `b, α₀` and the input constants `C_g, C_r, T₀` only);
* `diagonal_cmpExt_sub_smul`, `asmGap_pos`;
* **`mean_assembly`**: from the block identities
  `T Ḡ₁₁ = 1 + R₀`, `T F̄₁₁ = Σ Ḡ₁₁ᴴ + R₁₁`, `(z₀ - b(ḡ₀+ḡ₁)) t_p = (1 + b(t₀+t₁)) conj ḡ_p + r_p`
  (`T = -e - X - diag(c ḡ_a + b ḡ_p)`, `Σ = diag(c t_a + b t_p)`, `t_a = W⁻¹Tr F̄_aa`) and the bounds
  `|ḡ - a| ≤ C_g ε`, `‖R₀‖, ‖R₁₁‖, ‖R₁₁Kᴴ‖, |r_p| ≤ C_r ε`, `|t| ≤ T₀`:
  `‖K F̄₁₁ Kᴴ - γ I‖ ≤ asmConst · ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.CommonPort

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Layers
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- `y = (1-b) α₀ / 2`, the lower bound of `-Im` of the shifts. -/
def asmY (b α₀ : ℝ) : ℝ := (1 - b) * α₀ / 2

/-- Row-sum defect constant `η = (2y)⁻¹ + 4 y⁻³ C_g`. -/
def asmEta (b α₀ Cg : ℝ) : ℝ := (2 * asmY b α₀)⁻¹ + 4 * (asmY b α₀)⁻¹ ^ 3 * Cg

/-- `‖KM - 1‖` constant `C_g y⁻¹`. -/
def asmV (b α₀ Cg : ℝ) : ℝ := Cg * (asmY b α₀)⁻¹

/-- The ladder gap `1 - d(c + 2b²)`. -/
def asmGap (b : ℝ) : ℝ := 1 - (1 - b)⁻¹ * ((1 - 2 * b) + 2 * b ^ 2)

/-- The source-coefficient constant (output of `ladder_source_bound`). -/
def asmSig (b α₀ Cg Cr T₀ : ℝ) : ℝ :=
  2 * ((3 * b * (5 * Cg / (1 - 2 * b) + 2 * Cr) + (1 - b) / (1 - 2 * b) * asmEta b α₀ Cg +
      ((asmY b α₀)⁻¹ ^ 2 * T₀ + (asmY b α₀)⁻¹) * Cr) / (asmGap b / 2)) +
    5 * Cg / (1 - 2 * b) + 2 * Cr

/-- The final constant. -/
def asmConst (b α₀ Cg Cr T₀ : ℝ) : ℝ :=
  2 * asmV b α₀ Cg * T₀ + 2 * asmSig b α₀ Cg Cr T₀ + (1 - b) / (1 - 2 * b) * asmV b α₀ Cg +
    4 * T₀ * Cr + 2 * Cr

/-- The smallness constant: `asmSmall · ε ≤ 1` is the regularity domain of the assembly. -/
def asmSmall (b α₀ Cg : ℝ) : ℝ :=
  2 * Cg / α₀ + 5 * Cg + asmEta b α₀ Cg + 2 * (asmEta b α₀ Cg + 8 * Cg) / asmGap b +
    asmV b α₀ Cg

/-- The ladder gap is positive for `0 < b < 1/2` (`ladder_rowSum_lt_one`). -/
theorem asmGap_pos {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) : 0 < asmGap b := by
  have := ladder_rowSum_lt_one hb0 hb1
  unfold asmGap; linarith

/-- `asmSmall b α₀ C_g ≥ 0` for `0 < b < 1/2`, `α₀ > 0`, `C_g ≥ 0`. -/
theorem asmSmall_nonneg {b α₀ Cg : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (hα : 0 < α₀)
    (hCg : 0 ≤ Cg) : 0 ≤ asmSmall b α₀ Cg := by
  have hy : 0 < asmY b α₀ := by unfold asmY; have : 0 < 1 - b := by linarith
                                positivity
  have hg := asmGap_pos hb0 hb1
  have he : 0 ≤ asmEta b α₀ Cg := by unfold asmEta; positivity
  have hv : 0 ≤ asmV b α₀ Cg := by unfold asmV; positivity
  unfold asmSmall; positivity

/-- Deterministic: `diag(cmpExt σ) - γ I = diag(cmpExt (σ - γ))` (block-constant diagonals). -/
theorem diagonal_cmpExt_sub_smul {W : ℕ} (σ : Fin 2 → ℂ) (γ : ℂ) :
    (diagonal (cmpExt σ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - γ • 1 =
      diagonal (cmpExt fun j => σ j - γ) := by
  ext p q
  simp only [Matrix.sub_apply, diagonal_apply, Matrix.smul_apply, Matrix.one_apply, cmpExt,
    smul_eq_mul]
  split_ifs <;> ring

set_option maxHeartbeats 400000 in
/-- **The assembly inequality** (deterministic). See the module docstring for
the domain. Hypotheses (with `c = 1 - 2b`, `s_j = c ḡ_j + b ḡ_p`, `K = z_b - X`,
`t_j = blockTrace F̄₁₁ j`, `Σ = diag(c t_j + b t_p)`):
`hG : (H - diag s) Ḡ₁₁ = 1 + R₀`, `hF : (H - diag s) F̄₁₁ = Σ Ḡ₁₁ᴴ + R₁₁` (`H = -e - X`),
`htp : (z₀ - b(ḡ₀+ḡ₁)) t_p = (1 + b(t₀+t₁)) conj ḡ_p + r_p`, `hRK : R₁₁ Kᴴ = R_K`; bounds
`|ḡ_j - a|, |ḡ_p - a| ≤ C_g ε`, `‖R₀‖, ‖R₁₁‖, ‖R_K‖, |r_p| ≤ C_r ε`, `|t_j|, |t_p| ≤ T₀`,
`δ ≤ ε`, `asmSmall · ε ≤ 1`. Conclusion: `‖K F̄₁₁ Kᴴ - γ I‖ ≤ asmConst · ε`,
`γ = commonPortGamma b`. -/
theorem mean_assembly {W : ℕ} {b e α₀ : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (he : |e| < 2)
    (ha1 : ‖matchedA e‖ = 1) (hα : 0 < α₀) (haim : (matchedA e).im ≤ -α₀)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (g : Fin 2 → ℂ) (gp tp rp : ℂ) (G11 F11 R0 R11 RK : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hG : (cmpTopH e X - diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) * g j + (b : ℂ) * gp)) *
      G11 = 1 + R0)
    (hF : (cmpTopH e X - diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) * g j + (b : ℂ) * gp)) *
      F11 = diagonal (cmpExt fun j => ((1 - 2 * b : ℝ) : ℂ) * blockTrace F11 j + (b : ℂ) * tp) *
        G11ᴴ + R11)
    (htp : (commonZ b e - (b : ℂ) * (g 0 + g 1)) * tp =
      (1 + (b : ℂ) * (blockTrace F11 0 + blockTrace F11 1)) * conj gp + rp)
    (hRK : R11 * (matchedLeadK b e X)ᴴ = RK)
    {Cg Cr T₀ ε : ℝ} (hCg : 0 ≤ Cg) (hCr : 0 ≤ Cr) (hT₀ : 0 ≤ T₀) (hε : 0 ≤ ε)
    (hg : ∀ j, ‖g j - matchedA e‖ ≤ Cg * ε) (hgp : ‖gp - matchedA e‖ ≤ Cg * ε)
    (hR0 : ‖R0‖ ≤ Cr * ε) (hR11 : ‖R11‖ ≤ Cr * ε) (hRKn : ‖RK‖ ≤ Cr * ε) (hrp : ‖rp‖ ≤ Cr * ε)
    (ht0 : ∀ j, ‖blockTrace F11 j‖ ≤ T₀) (htp0 : ‖tp‖ ≤ T₀)
    (hδ : matchedDistance b e X ≤ ε) (hsm : asmSmall b α₀ Cg * ε ≤ 1) :
    ‖matchedLeadK b e X * F11 * (matchedLeadK b e X)ᴴ -
        ((commonPortGamma b : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤
      asmConst b α₀ Cg Cr T₀ * ε := by
  -- constants
  have hb1' : 0 < 1 - b := by linarith
  have hc0 : 0 < 1 - 2 * b := by linarith
  set a := matchedA e with ha
  set y : ℝ := asmY b α₀ with hy
  have hy0 : 0 < y := by rw [hy, asmY]; positivity
  set m₀ : ℝ := y⁻¹ with hm₀
  have hm0 : 0 ≤ m₀ := inv_nonneg.mpr hy0.le
  set kη : ℝ := asmEta b α₀ Cg with hkη
  set kV : ℝ := asmV b α₀ Cg with hkV
  set gap : ℝ := asmGap b with hgap
  have hgap0 : 0 < gap := asmGap_pos hb0 hb1
  have hkη0 : 0 ≤ kη := by rw [hkη, asmEta]; positivity
  have hkV0 : 0 ≤ kV := by rw [hkV, asmV]; positivity
  -- smallness
  have hsm' : (2 * Cg / α₀) * ε + 5 * Cg * ε + kη * ε + (2 * (kη + 8 * Cg) / gap) * ε +
      kV * ε ≤ 1 := by
    have := hsm; simp only [asmSmall, ← hkη, ← hkV, ← hgap, add_mul] at this; linarith
  have t1 : 0 ≤ (2 * Cg / α₀) * ε := by positivity
  have t2 : 0 ≤ 5 * Cg * ε := by positivity
  have t3 : 0 ≤ kη * ε := by positivity
  have t4 : 0 ≤ (2 * (kη + 8 * Cg) / gap) * ε := by positivity
  have t5 : 0 ≤ kV * ε := by positivity
  have sA : Cg * ε ≤ α₀ / 2 := by
    have h : (2 * Cg / α₀) * ε ≤ 1 := by linarith
    have e1 : (2 * Cg / α₀) * ε = 2 * (Cg * ε) / α₀ := by ring
    rw [e1, div_le_one hα] at h; linarith
  have sω : 5 * Cg * ε ≤ 1 := by linarith
  have sη : kη * ε ≤ 1 := by linarith
  have sQ : (kη + 8 * Cg) * ε ≤ gap / 2 := by
    have h : (2 * (kη + 8 * Cg) / gap) * ε ≤ 1 := by linarith
    have e1 : (2 * (kη + 8 * Cg) / gap) * ε = 2 * ((kη + 8 * Cg) * ε) / gap := by ring
    rw [e1, div_le_one hgap0] at h; linarith
  have sV : kV * ε ≤ 1 := by linarith
  have hCgε : 0 ≤ Cg * ε := by positivity
  have hCrε : 0 ≤ Cr * ε := by positivity
  -- Step A: imaginary parts of the means
  have hgim : ∀ j, α₀ / 2 ≤ -(g j).im := fun j =>
    cmp_im_of_near (by linarith) sA (hg j)
  have hgpim : α₀ / 2 ≤ -gp.im := cmp_im_of_near (by linarith) sA hgp
  -- Step B: shifts and inverses
  set H := cmpTopH e X with hH
  have hHh : H.IsHermitian := cmpTopH_isHermitian e hX
  set s : Fin 2 → ℂ := fun j => ((1 - 2 * b : ℝ) : ℂ) * g j + (b : ℂ) * gp with hs
  set s₀ : Fin 2 → ℂ := fun _ => (1 - (b : ℂ)) * a with hs₀
  have hsy : ∀ j, y ≤ -(s j).im := by
    intro j
    have e1 : (s j).im = (1 - 2 * b) * (g j).im + b * gp.im := by
      simp only [hs, Complex.add_im, Complex.im_ofReal_mul]
    rw [e1, hy, asmY]
    have h1 := mul_le_mul_of_nonneg_left (hgim j) hc0.le
    have h2 := mul_le_mul_of_nonneg_left hgpim hb0.le
    linarith
  have hsneg : ∀ j, (s j).im < 0 := fun j => by linarith [hsy j]
  have hs₀y : ∀ j, y ≤ -(s₀ j).im := by
    intro j
    have e1 : (s₀ j).im = (1 - b) * a.im := by
      simp only [hs₀, Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul, add_zero]
    rw [e1, hy, asmY]
    have h1 := mul_le_mul_of_nonneg_left haim hb1'.le
    have h2 : 0 ≤ (1 - b) * α₀ := by positivity
    linarith
  have hs₀neg : ∀ j, (s₀ j).im < 0 := fun j => by linarith [hs₀y j]
  set M := cmpInv H s with hM
  set R := cmpInv H s₀ with hR
  have hMn : ‖M‖ ≤ m₀ := lct_norm_shifted_inv_le H hHh (cmpExt s) hy0 (fun p => hsy p.1)
  have hRn : ‖R‖ ≤ m₀ := lct_norm_shifted_inv_le H hHh (cmpExt s₀) hy0 (fun p => hs₀y p.1)
  have hss₀ : ∀ j, ‖s j - s₀ j‖ ≤ Cg * ε := by
    intro j
    have e1 : s j - s₀ j = ((1 - 2 * b : ℝ) : ℂ) * (g j - a) + (b : ℂ) * (gp - a) := by
      simp only [hs, hs₀]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [cmp_norm_real_mul hc0.le, cmp_norm_real_mul hb0.le]
    have h1 := mul_le_mul_of_nonneg_left (hg j) hc0.le
    have h2 := mul_le_mul_of_nonneg_left hgp hb0.le
    have h3 : 0 ≤ b * (Cg * ε) := by positivity
    linarith
  have hmax : max ‖s 0 - s₀ 0‖ ‖s 1 - s₀ 1‖ ≤ Cg * ε := max_le (hss₀ 0) (hss₀ 1)
  -- Step C: the inverse identities
  have hMT : M * (H - diagonal (cmpExt s)) = 1 := cmp_inv_mul H hHh (cmpExt s) (fun p => hsneg p.1)
  have hG' : G11 = M + M * R0 := by
    calc G11 = M * (H - diagonal (cmpExt s)) * G11 := by rw [hMT, Matrix.one_mul]
      _ = M * (1 + R0) := by rw [Matrix.mul_assoc, hG]
      _ = M + M * R0 := by rw [Matrix.mul_add, Matrix.mul_one]
  set σ : Fin 2 → ℂ := fun j => ((1 - 2 * b : ℝ) : ℂ) * blockTrace F11 j + (b : ℂ) * tp with hσ
  set S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := diagonal (cmpExt σ) with hS
  have hF' : F11 = M * S * G11ᴴ + M * R11 := by
    calc F11 = M * (H - diagonal (cmpExt s)) * F11 := by rw [hMT, Matrix.one_mul]
      _ = M * (S * G11ᴴ + R11) := by rw [Matrix.mul_assoc, hF]
      _ = M * S * G11ᴴ + M * R11 := by rw [Matrix.mul_add, Matrix.mul_assoc]
  -- Step D: `KM`
  set K := matchedLeadK b e X with hK
  have hKM1 : ‖K * M - 1‖ ≤ kV * ε := by
    have h := norm_matchedLeadK_mul_cmpInv_sub_one_le (b := b) he.le hX s hsneg
    refine h.trans ?_
    rw [hkV, asmV, ← hy, ← hm₀]
    calc max ‖s 0 - (1 - (b : ℂ)) * matchedA e‖ ‖s 1 - (1 - (b : ℂ)) * matchedA e‖ *
          ‖cmpInv (cmpTopH e X) s‖ ≤ (Cg * ε) * m₀ :=
          mul_le_mul hmax hMn (norm_nonneg _) hCgε
      _ = Cg * m₀ * ε := by ring
  have hKM : ‖K * M‖ ≤ 2 := by
    have h1 : ‖K * M‖ ≤ ‖K * M - 1‖ + ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ := by
      have := norm_add_le (K * M - 1) 1; rwa [sub_add_cancel] at this
    have := lct_norm_one_le (n := Fin 2 × Fin W)
    linarith
  -- Step E: the source coefficients and the ladder
  have hσn : ∀ j, ‖σ j‖ ≤ T₀ := by
    intro j
    refine (norm_add_le _ _).trans ?_
    rw [cmp_norm_real_mul hc0.le, cmp_norm_real_mul hb0.le]
    have h1 := mul_le_mul_of_nonneg_left (ht0 j) hc0.le
    have h2 := mul_le_mul_of_nonneg_left htp0 hb0.le
    have h3 : 0 ≤ b * T₀ := by positivity
    linarith
  have hSn : ‖S‖ ≤ T₀ := (norm_diagonal_cmpExt_le σ).trans (max_le (hσn 0) (hσn 1))
  set A : Fin 2 → Fin 2 → ℂ := fun i j => cmpPair M Mᴴ i j with hA
  set r : Fin 2 → ℂ := fun i => blockTrace (M * S * (M * R0)ᴴ + M * R11) i with hr
  have ht_eq : ∀ i, blockTrace F11 i =
      ∑ j, A i j * (((1 - 2 * b : ℝ) : ℂ) * blockTrace F11 j + (b : ℂ) * tp) + r i := by
    intro i
    have e1 : F11 = M * S * Mᴴ + (M * S * (M * R0)ᴴ + M * R11) := by
      rw [hF', hG', conjTranspose_add, Matrix.mul_add]; abel
    have e2 := cmp_blockTrace_mul_diag_mul M Mᴴ σ i
    conv_lhs => rw [e1]
    rw [blockTrace_add, e2]
  have hrn : ∀ i, ‖r i‖ ≤ (m₀ ^ 2 * T₀ + m₀) * Cr * ε := by
    intro i
    refine (lct_norm_blockTrace_le _ i).trans ?_
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖M * S * (M * R0)ᴴ‖ ≤ m₀ * T₀ * (m₀ * (Cr * ε)) := by
      refine (l2_opNorm_mul _ _).trans ?_
      rw [l2_opNorm_conjTranspose]
      exact mul_le_mul ((l2_opNorm_mul _ _).trans (mul_le_mul hMn hSn (norm_nonneg _) hm0))
        ((l2_opNorm_mul _ _).trans (mul_le_mul hMn hR0 (norm_nonneg _) hm0)) (norm_nonneg _)
        (by positivity)
    have h2 : ‖M * R11‖ ≤ m₀ * (Cr * ε) :=
      (l2_opNorm_mul _ _).trans (mul_le_mul hMn hR11 (norm_nonneg _) hm0)
    calc ‖M * S * (M * R0)ᴴ‖ + ‖M * R11‖ ≤ m₀ * T₀ * (m₀ * (Cr * ε)) + m₀ * (Cr * ε) :=
          add_le_add h1 h2
      _ = (m₀ ^ 2 * T₀ + m₀) * Cr * ε := by ring
  -- row sums
  have hζ : 2 * y ≤ -(1 - b) * a.im := by
    rw [hy, asmY]
    have h1 := mul_le_mul_of_nonneg_left haim hb1'.le
    linarith
  have hRrow : ∀ i, |∑ j, cmpRowMass R i j - (1 - b)⁻¹| ≤ (2 * y)⁻¹ * ε := by
    intro i
    have h := rowMass_R_sum_sub_le (b := b) (by linarith) he hX i
    rw [cmp_resolvent_eq he.le X] at h
    refine h.trans ?_
    have hζ0 : 0 < -(1 - b) * (matchedA e).im := by linarith
    have hd0 : 0 ≤ matchedDistance b e X := by
      unfold matchedDistance; exact (norm_nonneg _).trans (le_max_left _ _)
    calc matchedDistance b e X / (-(1 - b) * (matchedA e).im) ≤ ε / (2 * y) :=
          div_le_div₀ hε hδ (by positivity) hζ
      _ = (2 * y)⁻¹ * ε := by ring
  have hL : ∀ i j, ‖A i j - cmpPair R Rᴴ i j‖ ≤ 2 * m₀ ^ 3 * Cg * ε := by
    intro i j
    refine (norm_ladderCoef_sub_le M R i j).trans ?_
    have hMR : ‖M - R‖ ≤ m₀ * m₀ * (Cg * ε) := by
      refine (norm_cmpInv_sub_le H hHh s s₀ hsneg hs₀neg).trans ?_
      exact mul_le_mul (mul_le_mul hMn hRn (norm_nonneg _) hm0) hmax
        ((norm_nonneg _).trans (le_max_left _ _)) (by positivity)
    calc (‖M‖ + ‖R‖) * ‖M - R‖ ≤ (m₀ + m₀) * (m₀ * m₀ * (Cg * ε)) :=
          mul_le_mul (add_le_add hMn hRn) hMR (norm_nonneg _) (by positivity)
      _ = 2 * m₀ ^ 3 * Cg * ε := by ring
  have hRpair : ∀ i j, cmpPair R Rᴴ i j = ((cmpRowMass R i j : ℝ) : ℂ) := cmpPair_conj_self R
  set ρ : ℝ := (1 - b)⁻¹ + kη * ε with hρdef
  have hρ : ∀ i, ∑ j, ‖A i j‖ ≤ ρ := by
    intro i
    have hb : ∀ j, ‖A i j‖ ≤ cmpRowMass R i j + 2 * m₀ ^ 3 * Cg * ε := by
      intro j
      have h1 := norm_le_norm_add_norm_sub' (A i j) (cmpPair R Rᴴ i j)
      rw [hRpair, Complex.norm_real, Real.norm_of_nonneg (cmpRowMass_nonneg R i j)] at h1
      have := hL i j
      rw [hRpair] at this
      linarith
    have hs1 := (abs_le.mp (hRrow i)).2
    rw [Fin.sum_univ_two] at hs1 ⊢
    have := hb 0
    have := hb 1
    rw [hρdef, hkη, asmEta, ← hy, ← hm₀]
    linarith
  have hEs : ∀ i, ‖∑ j, A i j - ((1 - b : ℝ) : ℂ)⁻¹‖ ≤ kη * ε := by
    intro i
    have e1 : ∑ j, A i j - ((1 - b : ℝ) : ℂ)⁻¹ = (∑ j, (A i j - cmpPair R Rᴴ i j)) +
        (((∑ j, cmpRowMass R i j - (1 - b)⁻¹ : ℝ)) : ℂ) := by
      simp only [Finset.sum_sub_distrib, hRpair]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖∑ j, (A i j - cmpPair R Rᴴ i j)‖ ≤ 2 * (2 * m₀ ^ 3 * Cg * ε) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Fin.sum_univ_two]
      linarith [hL i 0, hL i 1]
    have h3 := hRrow i
    rw [hkη, asmEta, ← hy, ← hm₀]
    linarith
  -- the port equation
  set e' : ℂ := (b : ℂ) * ((g 0 - a) + (g 1 - a)) with he'
  have he'n : ‖e'‖ ≤ Cg * ε := by
    rw [he', cmp_norm_real_mul hb0.le]
    have h1 := (norm_add_le _ _).trans (add_le_add (hg 0) (hg 1))
    have h2 := mul_le_mul_of_nonneg_left h1 hb0.le
    have h3 : b * (Cg * ε + Cg * ε) ≤ Cg * ε := by nlinarith
    linarith
  have he'h : ‖e'‖ ≤ 1 / 2 := by linarith
  obtain ⟨hq0, -, hqi2, -, hqia⟩ := cmp_port' ha1 he'h
  have hq : commonZ b e - (b : ℂ) * (g 0 + g 1) = a⁻¹ - e' := by
    rw [he', commonZ, ← ha]; ring
  set ω : ℂ := (a⁻¹ - e')⁻¹ * conj gp with hω
  set rp' : ℂ := (a⁻¹ - e')⁻¹ * rp with hrp'
  have htp' : tp = ω * (1 + (b : ℂ) * (blockTrace F11 0 + blockTrace F11 1)) + rp' := by
    rw [hq] at htp
    have h2 : tp = (a⁻¹ - e')⁻¹ * ((a⁻¹ - e') * tp) := by
      rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
    rw [h2, htp, hω, hrp']; ring
  have ha0 : a ≠ 0 := by intro h; rw [h, norm_zero] at ha1; exact zero_ne_one ha1
  have haa : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha1]; simp
  have hgpn : ‖gp‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' gp a
    rw [ha1] at this; linarith
  have hω1 : ‖ω - 1‖ ≤ 5 * Cg * ε := by
    have e1 : ω - 1 = ((a⁻¹ - e')⁻¹ - a) * conj gp + a * (conj gp - conj a) +
        (a * conj a - 1) := by rw [hω]; ring
    rw [e1, haa, sub_self, add_zero]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, ha1, one_mul, ← map_sub, Complex.norm_conj]
    calc ‖(a⁻¹ - e')⁻¹ - a‖ * ‖gp‖ + ‖gp - a‖ ≤ (2 * (Cg * ε)) * 2 + Cg * ε := by
          gcongr
          · exact hqia.trans (by linarith)
      _ = 5 * Cg * ε := by ring
  have hωn : ‖ω‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' ω 1
    rw [norm_one] at this; linarith
  have hrp'n : ‖rp'‖ ≤ 2 * Cr * ε := by
    rw [hrp', norm_mul]
    calc ‖(a⁻¹ - e')⁻¹‖ * ‖rp‖ ≤ 2 * (Cr * ε) :=
          mul_le_mul hqi2 hrp (norm_nonneg _) (by norm_num)
      _ = 2 * Cr * ε := by ring
  -- contraction
  set q₁ : ℝ := 1 - gap / 2 with hq₁
  have hq₁1 : q₁ < 1 := by linarith
  have hρ3 : ρ ≤ 3 := by
    have : (1 - b)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hb1' (by norm_num)]; linarith
    linarith
  have hcontr : ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖) ≤ q₁ := by
    have hω' : ‖ω‖ ≤ 1 + 5 * Cg * ε := by
      have := norm_le_norm_add_norm_sub' ω 1
      rw [norm_one] at this; linarith only [this, hω1]
    have hd2 : (1 - b)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hb1' (by norm_num)]; linarith only [hb1]
    have hd0 : 0 ≤ (1 - b)⁻¹ := by positivity
    have hbb1 : b * b ≤ b * 1 := mul_le_mul_of_nonneg_left (by linarith) hb0.le
    have hbb2 : b * b ≤ 1 / 2 * (1 / 2) := mul_le_mul hb1.le hb1.le hb0.le (by norm_num)
    have hb2 : b ^ 2 = b * b := sq b
    have hcb : (1 - 2 * b) + 2 * b ^ 2 ≤ 1 := by linarith only [hbb1, hb2]
    have hbb : 2 * b ^ 2 ≤ 1 / 2 := by linarith only [hbb2, hb2]
    have hρ0 : 0 ≤ ρ := add_nonneg hd0 (mul_nonneg hkη0 hε)
    have h1 : (1 - 2 * b) + 2 * b ^ 2 * ‖ω‖ ≤ ((1 - 2 * b) + 2 * b ^ 2) + 2 * b ^ 2 *
        (5 * Cg * ε) := by
      have := mul_le_mul_of_nonneg_left hω' (by positivity : (0 : ℝ) ≤ 2 * b ^ 2)
      linarith only [this]
    have hgdef : (1 - b)⁻¹ * ((1 - 2 * b) + 2 * b ^ 2) = 1 - gap := by
      rw [hgap, asmGap]; ring
    calc ρ * ((1 - 2 * b) + 2 * b ^ 2 * ‖ω‖)
        ≤ ρ * (((1 - 2 * b) + 2 * b ^ 2) + 2 * b ^ 2 * (5 * Cg * ε)) :=
          mul_le_mul_of_nonneg_left h1 hρ0
      _ = (1 - b)⁻¹ * ((1 - 2 * b) + 2 * b ^ 2) + kη * ε * ((1 - 2 * b) + 2 * b ^ 2) +
            ρ * (2 * b ^ 2) * (5 * Cg * ε) := by rw [hρdef]; ring
      _ ≤ (1 - gap) + kη * ε * 1 + 3 * (1 / 2) * (5 * Cg * ε) := by
          have h4 : kη * ε * ((1 - 2 * b) + 2 * b ^ 2) ≤ kη * ε * 1 :=
            mul_le_mul_of_nonneg_left hcb (mul_nonneg hkη0 hε)
          have h5 : ρ * (2 * b ^ 2) ≤ 3 * (1 / 2) :=
            mul_le_mul hρ3 hbb (by positivity) (by norm_num)
          have h6 : ρ * (2 * b ^ 2) * (5 * Cg * ε) ≤ 3 * (1 / 2) * (5 * Cg * ε) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
          rw [hgdef]
          linarith only [h4, h6]
      _ ≤ q₁ := by
          have h3 := sQ
          rw [add_mul] at h3
          rw [hq₁]
          linarith only [h3, hCgε]
  -- the ladder bound on the source coefficients
  have hsrc : ∀ i, ‖σ i - ((commonPortGamma b : ℝ) : ℂ)‖ ≤ asmSig b α₀ Cg Cr T₀ * ε := by
    intro i
    have h := ladder_source_bound (A := A) (t := fun j => blockTrace F11 j) (r := r)
      (tp := tp) (rp := rp') (ω := ω) hb0.le hb1 hρ hρ3 hcontr hq₁1 hωn ht_eq htp' hω1
      hrp'n hEs hrn i
    have e1 : 1 - q₁ = gap / 2 := by rw [hq₁]; ring
    rw [e1] at h
    refine h.trans (le_of_eq ?_)
    rw [asmSig, ← hkη, ← hgap, ← hy, ← hm₀]
    ring
  have hSg : ‖S - ((commonPortGamma b : ℝ) : ℂ) • 1‖ ≤ asmSig b α₀ Cg Cr T₀ * ε := by
    rw [hS, diagonal_cmpExt_sub_smul]
    exact (norm_diagonal_cmpExt_le _).trans (max_le (hsrc 0) (hsrc 1))
  -- the final decomposition
  have hdet := mean_det K M S F11 G11 R11 R0 ((commonPortGamma b : ℝ) : ℂ) hF' hG'
  rw [hRK] at hdet
  refine hdet.trans ?_
  have hγ0 : 0 ≤ commonPortGamma b := by unfold commonPortGamma; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg hγ0]
  have hσ0 : 0 ≤ asmSig b α₀ Cg Cr T₀ * ε := (norm_nonneg _).trans hSg
  calc ‖K * M - 1‖ * ‖S‖ * ‖K * M‖ + ‖S - ((commonPortGamma b : ℝ) : ℂ) • 1‖ * ‖K * M‖ +
        commonPortGamma b * ‖K * M - 1‖ + ‖K * M‖ ^ 2 * ‖S‖ * ‖R0‖ + ‖K * M‖ * ‖RK‖
      ≤ (kV * ε) * T₀ * 2 + (asmSig b α₀ Cg Cr T₀ * ε) * 2 + commonPortGamma b * (kV * ε) +
          2 ^ 2 * T₀ * (Cr * ε) + 2 * (Cr * ε) := by
        gcongr
    _ = asmConst b α₀ Cg Cr T₀ * ε := by
        rw [asmConst, ← hkV, commonPortGamma]; ring

end BlockBand.Critical.CommonPort
