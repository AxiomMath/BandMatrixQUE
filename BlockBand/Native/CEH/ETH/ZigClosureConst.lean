module

public import BlockBand.Native.CEH.ETH.ZigClosureRegular

/-!
# CEH ETH: constellation invariances, geometry and the initial value of `Z`

For the zig data `zcl_Data`, the quantities in each of the four constellations reduce to those at the
upper points, the geometry of the path core is valid, and the initial value of `Z` is bounded.

* `abs_w₁`, `abs_w₂`: `|Im w_i^{(b)}| = η_{i,r}` (the heights of the path core);
* the per-constellation quantities reduce to the upper-point ones of `zcl_Data.proc`:
  `‖⟨R_i^{(b)}⟩ - m_i^{(b)}‖ = ‖W_i‖` (`norm_W₁`, `norm_W₂`), `‖⟨Im R_i^{(b)}⟩‖ = imR_i`
  (`norm_imR₁`, `norm_imR₂`), `‖⟨Im R₁^{(b₁)} A Im R₂^{(b₂)} Aᴴ⟩‖ = |Z|` (`norm_chain`),
  `‖⟨Im R₁^{(b₁)} Im R₂^{(b₂)}⟩‖ = TI` (`TI_eq`);
* `geom_valid`: `d.geom.Valid` (`cᵢ = π ρᵢ` by `cehDensityOf_eq`);
* `Z0`: `|Z₀| ≤ π² ρ₁ρ₂ s₂(s)²` (`zgl_chain_eq_sTwoAt_zero`, `sTwoAt_mono`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

namespace zcl_Data

variable (d : zcl_Data Ω N)

/-- `H_r = F + G_r`. -/
def H (ω : Ω) (r : ℝ) : Matrix (Fin N) (Fin N) ℂ := d.F + d.G r.toNNReal ω

/-- The spectral parameter of `R₁^{(b)}` at time `r`. -/
def w₁ (b : Bool) (r : ℝ) : ℂ := flowSpectral (ztl_cz b d.z₁) (ztl_cz b d.m₁) d.s r.toNNReal

/-- The spectral parameter of `R₂^{(b)}` at time `r`. -/
def w₂ (b : Bool) (r : ℝ) : ℂ := flowSpectral (ztl_cz b d.z₂) (ztl_cz b d.m₂) d.s r.toNNReal

theorem R₁_res (b : Bool) (ω : Ω) (r : ℝ) :
    d.R₁ b ω r = Phase1.resolvent (d.H ω r) (d.w₁ b r) := rfl

theorem R₂_res (b : Bool) (ω : Ω) (r : ℝ) :
    d.R₂ b ω r = Phase1.resolvent (d.H ω r) (d.w₂ b r) := rfl

variable {d} (hd : d.Valid)
include hd

namespace Valid

theorem H_herm (ω : Ω) (r : ℝ) : (d.H ω r).IsHermitian := hd.herm _ ω

theorem w₁_ne (b : Bool) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) : (d.w₁ b r).im ≠ 0 :=
  zcl_flowSpectral_cz_im_ne_zero b hd.z₁_pos.ne' hd.hm₁ hr

theorem w₂_ne (b : Bool) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) : (d.w₂ b r).im ≠ 0 :=
  zcl_flowSpectral_cz_im_ne_zero b hd.z₂_pos.ne' hd.hm₂ hr

theorem w₁_pos {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) : 0 < (d.w₁ true r).im := by
  have hσ : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (d.s : ℝ) := by
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2
  exact zgl_im_flowSpectral_pos hd.z₁_pos hd.m₁_pos.le hσ

theorem w₂_pos {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) : 0 < (d.w₂ true r).im := by
  have hσ : ((r.toNNReal : ℝ≥0) : ℝ) ≤ (d.s : ℝ) := by
    rw [Real.coe_toNNReal _ hr.1]; exact hr.2
  exact zgl_im_flowSpectral_pos hd.z₂_pos hd.m₂_pos.le hσ

theorem abs_w₁ (b : Bool) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) :
    |(d.w₁ b r).im| = d.geom.e₁ r := by
  rw [w₁, zcl_abs_im_flowSpectral_cz b hd.hm₁ hr, abs_of_pos hd.z₁_pos, abs_of_pos hd.m₁_pos]
  rfl

theorem abs_w₂ (b : Bool) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) :
    |(d.w₂ b r).im| = d.geom.e₂ r := by
  rw [w₂, zcl_abs_im_flowSpectral_cz b hd.hm₂ hr, abs_of_pos hd.z₂_pos, abs_of_pos hd.m₂_pos]
  rfl

theorem norm_W₁ (b : Bool) (ω : Ω) (r : ℝ) :
    ‖normalizedTrace (d.R₁ b ω r) - ztl_cz b d.m₁‖ = ‖(d.proc ω).W₁ r‖ := by
  change _ = ‖normalizedTrace (d.R₁ true ω r) - d.m₁‖
  rw [hd.R₁_cz b ω r]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, ztl_cz]
    rw [Phase1.normalizedTrace_conjTranspose, ← map_sub, Complex.norm_conj]
  · rfl

theorem norm_W₂ (b : Bool) (ω : Ω) (r : ℝ) :
    ‖normalizedTrace (d.R₂ b ω r) - ztl_cz b d.m₂‖ = ‖(d.proc ω).W₂ r‖ := by
  change _ = ‖normalizedTrace (d.R₂ true ω r) - d.m₂‖
  rw [hd.R₂_cz b ω r]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, ztl_cz]
    rw [Phase1.normalizedTrace_conjTranspose, ← map_sub, Complex.norm_conj]
  · rfl

theorem norm_imR₁ (b : Bool) (ω : Ω) (r : ℝ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ b ω r))‖ = (d.proc ω).imR₁ r := by
  change _ = |(normalizedTrace (d.R₁ true ω r)).im|
  rw [zgl_norm_normalizedTrace_imaginaryPart, hd.R₁_cz b ω r]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Phase1.normalizedTrace_conjTranspose, Complex.conj_im, abs_neg]
  · rfl

theorem norm_imR₂ (b : Bool) (ω : Ω) (r : ℝ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (d.R₂ b ω r))‖ = (d.proc ω).imR₂ r := by
  change _ = |(normalizedTrace (d.R₂ true ω r)).im|
  rw [zgl_norm_normalizedTrace_imaginaryPart, hd.R₂_cz b ω r]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Phase1.normalizedTrace_conjTranspose, Complex.conj_im, abs_neg]
  · rfl

theorem norm_chain (b₁ b₂ : Bool) (ω : Ω) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) :
    ‖normalizedTrace (bwImChain d.A (d.R₁ b₁ ω r) (d.R₂ b₂ ω r))‖ = |(d.proc ω).Z r| := by
  have e : ‖normalizedTrace (bwImChain d.A (d.R₁ b₁ ω r) (d.R₂ b₂ ω r))‖ =
      ‖normalizedTrace (bwImChain d.A (d.R₁ true ω r) (d.R₂ true ω r))‖ := by
    rw [hd.R₁_cz b₁ ω r, hd.R₂_cz b₂ ω r]
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bf_bwImChain_conjTranspose_left,
        bf_bwImChain_conjTranspose_right, neg_neg, bf_normalizedTrace_neg, norm_neg]
  rw [e]
  change ‖normalizedTrace (bwImChain d.A (Phase1.resolvent (d.H ω r) (d.w₁ true r))
      (Phase1.resolvent (d.H ω r) (d.w₂ true r)))‖ =
    |(normalizedTrace (bwImChain d.A (Phase1.resolvent (d.H ω r) (d.w₁ true r))
      (Phase1.resolvent (d.H ω r) (d.w₂ true r)))).re|
  rw [bw_normalizedTrace_imChain_eq_re (hd.H_herm ω r) (hd.w₁_ne true hr) (hd.w₂_ne true hr),
    Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]

theorem Z_nonneg (ω : Ω) {r : ℝ} (hr : r ∈ Icc 0 (d.s : ℝ)) : 0 ≤ (d.proc ω).Z r :=
  bw_re_normalizedTrace_imChain_nonneg (hd.H_herm ω r) (hd.w₁_pos hr) (hd.w₂_pos hr) d.A

theorem TI_eq (b₁ b₂ : Bool) (ω : Ω) (r : ℝ) :
    ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ b₁ ω r) *
      External.CEH.imaginaryPart (d.R₂ b₂ ω r))‖ = (d.proc ω).TI r := by
  change _ = ‖normalizedTrace (External.CEH.imaginaryPart (d.R₁ true ω r) *
      External.CEH.imaginaryPart (d.R₂ true ω r))‖
  rw [hd.R₁_cz b₁ ω r, hd.R₂_cz b₂ ω r]
  cases b₁ <;> cases b₂ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, bf_imaginaryPart_conjTranspose, neg_mul,
      mul_neg, neg_neg, bf_normalizedTrace_neg, norm_neg]

/-!
## The geometry
-/

theorem geom_valid : d.geom.Valid where
  s_nonneg := d.s.2
  N_pos := by
    change (0 : ℝ) < N
    exact_mod_cast hd.N_pos
  η₁_pos := hd.z₁_pos
  η₂_pos := hd.z₂_pos
  ρ₁_pos := by
    change 0 < cehDensityOf d.M₁
    rw [cehDensityOf_eq]; exact div_pos hd.m₁_pos Real.pi_pos
  ρ₂_pos := by
    change 0 < cehDensityOf d.M₂
    rw [cehDensityOf_eq]; exact div_pos hd.m₂_pos Real.pi_pos
  S_pos := hd.S_pos
  c₁_eq := by
    change d.m₁.im = Real.pi * cehDensityOf d.M₁
    rw [cehDensityOf_eq]; field_simp; rfl
  c₂_eq := by
    change d.m₂.im = Real.pi * cehDensityOf d.M₂
    rw [cehDensityOf_eq]; field_simp; rfl

/-!
## The initial value of `Z`
-/

theorem Z0 (ω : Ω) : |(d.proc ω).Z 0| ≤ Real.pi ^ 2 * d.geom.UZ := by
  have hz : (d.proc ω).Z 0 = (NTrace (matrixImaginaryPart d.M₁ * d.A *
      matrixImaginaryPart d.M₂ * d.Aᴴ)).re := by
    change (fz_chain (d.R₁ true ω 0) (d.R₂ true ω 0) d.A).re = _
    rw [hd.R₁_zero, hd.R₂_zero, zgl_matrixImaginaryPart_eq, zgl_matrixImaginaryPart_eq]
    rfl
  have ht₁ : 0 < (NTrace d.M₁).im := hd.m₁_pos
  have ht₂ : 0 < (NTrace d.M₂).im := hd.m₂_pos
  rw [hz, zgl_chain_eq_sTwoAt_zero ht₁ ht₂ d.A hd.base_nonneg]
  have hρ₁ : 0 < cehDensityOf d.M₁ := by rw [cehDensityOf_eq]; exact div_pos hd.m₁_pos Real.pi_pos
  have hρ₂ : 0 < cehDensityOf d.M₂ := by rw [cehDensityOf_eq]; exact div_pos hd.m₂_pos Real.pi_pos
  have h0 : 0 ≤ sTwoAt 0 d.M₁ d.M₂ d.A := Real.sqrt_nonneg _
  have hlt := mul_norm_NTrace_lt_one_mde hd.mde₁ hd.mde₂ hd.z₁_pos.ne' hd.z₂_pos.ne' d.s.2
    AdjointChoice.plain AdjointChoice.plain
  simp only [chooseAdjoint_plain] at hlt
  have hmono := sTwoAt_mono le_rfl d.s.2 d.M₁ d.M₂ d.A hlt
  have hsq : sTwoAt 0 d.M₁ d.M₂ d.A ^ 2 ≤ sTwoAt d.s d.M₁ d.M₂ d.A ^ 2 :=
    pow_le_pow_left₀ h0 hmono 2
  rw [abs_of_nonneg (by positivity)]
  change _ ≤ Real.pi ^ 2 * (cehDensityOf d.M₁ * cehDensityOf d.M₂ *
    sTwoAt d.s d.M₁ d.M₂ d.A ^ 2)
  have hp : 0 ≤ Real.pi ^ 2 * cehDensityOf d.M₁ * cehDensityOf d.M₂ := by positivity
  calc Real.pi ^ 2 * cehDensityOf d.M₁ * cehDensityOf d.M₂ * sTwoAt 0 d.M₁ d.M₂ d.A ^ 2
      ≤ Real.pi ^ 2 * cehDensityOf d.M₁ * cehDensityOf d.M₂ * sTwoAt d.s d.M₁ d.M₂ d.A ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hp
    _ = _ := by ring

end Valid

end zcl_Data

end BlockBand.Native.CEH.ETH
