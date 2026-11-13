module

public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Palm.RegularityCertificate
public import BlockBand.RankLocation.SemicircleCDF
public import BlockBand.Layers.ResidualPair

/-!
# The regular clause of the physical center (domain constants `cst0`)

* §1 `ctr_ward` (Ward identity `Im Tr ℛ(ζ) = Im ζ · Σ|ℛ_xz|²`), `ctr_root_ward`
  (`(s/N_aux) Σ|ℛ_xz|² = 1` at a root), **`ctr_root_unique`**: for Hermitian `H^{(e)}` the
  upper-half-plane root of `ζ = (s/N_aux) Tr ℛ_e(ζ)` is globally unique.
* §2 **`ctr_compressed_eq_schur`**: off the exterior poles, `ℛ_e(ζ) = (K_e(E) - ζ)⁻¹` for
  every `ζ` (Schur complement; both totalized inverses vanish together).
* §3 `ctr_centerFormula_eq`: the clip of `centerFormula` is inactive at a root;
  `ctr_abs_dysonCenter_le`: `|j_e| ≤ 1` everywhere.
* §4 `ctr_freshDyson_eq`: `freshDyson` is the unique positive root
  (`certificate_dyson_unique_nonnegative`); `ctrCert`: certificate data selected from
  `certificate_semicircle_full`.
* §5 bookkeeping: `|χ| ≤ ε_e` (`ctr_chi_le`), `κ_α ≥ ϑ/2` for `ϑ`-bulk ranks.
* §6 **`cst0`** (`ε₁(b, κ)` = half the certificate threshold at `c = min(1-2b, b)` and grid margin
  `θ_{k(κ)} = 2/(⌈2/κ⌉+1) ≤ κ`; `ρ₀ = 3`) and **`centerDomain_regular`**: the `regular` field
  of `CenterDomainContract cst0`, with `r₀, s₀, v₀` the minima of the certificate constants over
  the finitely many grid levels `k ≤ ⌈4/ϑ⌉`, `y₀ = s v₀`, `C = 1`.
* §7 `cst0_inCenterDomain_iff`: off the exterior poles, for Hermitian `H^{(e)}` and
  `ϑ`-bulk ranks, the domain of `cst0` is exactly `{E ∈ I, ε_e(E) ≤ ε₁}`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open Matrix BlockBand.Coarea
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open scoped ComplexConjugate

/-!
## 1. The compressed resolvent: resolvent identity, Ward identity, global uniqueness
-/

section Linear

variable (p : Parameters) (i : ZMod p.n)

/-- The full shifted matrix `H^{(e)} - E - ζ P_S` whose inverse is compressed in
`compressedResolvent`. -/
def ctrFull (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) : p.SiteMatrix :=
  Hres - (E : ℂ) • 1 - ζ • pairProjector p i

/-- The normalization `s / N_aux = s/(2W)` of the Dyson equation, as a real number. -/
def ctrK : ℝ := splitS p / (2 * (p.W : ℝ))

variable {p i}

theorem ctr_compressedResolvent_apply (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ)
    (x y : PairSite p i) :
    compressedResolvent p i Hres E ζ x y = (ctrFull p i Hres E ζ)⁻¹ x.1 y.1 := rfl

theorem ctr_splitS_pos : 0 < splitS p := lt_min p.c_pos p.b_pos

theorem ctr_splitS_le_one : splitS p ≤ 1 :=
  (min_le_right _ _).trans (by linarith [p.b_lt_half])

theorem ctrK_pos : 0 < ctrK p := by
  unfold ctrK
  have : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  exact div_pos ctr_splitS_pos (by linarith)

theorem ctrK_coe : ((ctrK p : ℝ) : ℂ) = (splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ := by
  unfold ctrK
  push_cast
  ring

/-- A matrix product through `P_S` is a sum over the pair. -/
theorem ctr_mul_projector_mul_apply (A B : p.SiteMatrix) (x y : p.Site) :
    (A * pairProjector p i * B) x y = ∑ z : PairSite p i, A x z.1 * B z.1 y := by
  rw [Matrix.mul_apply]
  unfold pairProjector
  simp only [Matrix.mul_diagonal]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z : p.Site => z.1 = i ∨ z.1 = i + 1)]
  have h2 : ∑ z : {z : p.Site // ¬ (z.1 = i ∨ z.1 = i + 1)},
      A x z.1 * (if z.1.1 = i ∨ z.1.1 = i + 1 then (1 : ℂ) else 0) * B z.1 y = 0 :=
    Finset.sum_eq_zero fun z _ => by simp [z.2]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [z.2]

theorem ctr_pairProjector_conjTranspose : (pairProjector p i)ᴴ = pairProjector p i := by
  unfold pairProjector
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  rw [Pi.star_apply]
  split_ifs <;> simp only [star_one, star_zero]

theorem ctr_ctrFull_conjTranspose {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ)
    (ζ : ℂ) : (ctrFull p i Hres E ζ)ᴴ = ctrFull p i Hres E (conj ζ) := by
  unfold ctrFull
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, ctr_pairProjector_conjTranspose]
  simp

/-- Resolvent identity `R(ζ₁) - R(ζ₂) = (ζ₁ - ζ₂) R(ζ₁) P R(ζ₂)` for invertible full matrices. -/
theorem ctr_full_inv_sub (Hres : p.SiteMatrix) (E : ℝ) {ζ₁ ζ₂ : ℂ}
    (h₁ : (ctrFull p i Hres E ζ₁).det ≠ 0) (h₂ : (ctrFull p i Hres E ζ₂).det ≠ 0) :
    (ctrFull p i Hres E ζ₁)⁻¹ - (ctrFull p i Hres E ζ₂)⁻¹ =
      (ζ₁ - ζ₂) • ((ctrFull p i Hres E ζ₁)⁻¹ * pairProjector p i *
        (ctrFull p i Hres E ζ₂)⁻¹) := by
  set A := ctrFull p i Hres E ζ₁
  set B := ctrFull p i Hres E ζ₂
  have hBA : B - A = (ζ₁ - ζ₂) • pairProjector p i := by
    simp only [A, B, ctrFull, sub_smul]
    abel
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr h₁
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr h₂
  have key : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB,
      Matrix.mul_one, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  rw [← key, hBA, Matrix.mul_smul, Matrix.smul_mul]

/-- Pair-matrix form of the resolvent identity. -/
theorem ctr_compressed_sub (Hres : p.SiteMatrix) (E : ℝ) {ζ₁ ζ₂ : ℂ}
    (h₁ : (ctrFull p i Hres E ζ₁).det ≠ 0) (h₂ : (ctrFull p i Hres E ζ₂).det ≠ 0) :
    compressedResolvent p i Hres E ζ₁ - compressedResolvent p i Hres E ζ₂ =
      (ζ₁ - ζ₂) • (compressedResolvent p i Hres E ζ₁ * compressedResolvent p i Hres E ζ₂) := by
  ext x y
  have h := congrFun (congrFun (ctr_full_inv_sub Hres E h₁ h₂) x.1) y.1
  rw [Matrix.sub_apply, Matrix.smul_apply, ctr_mul_projector_mul_apply] at h
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply]
  exact h

/-- For Hermitian `H^{(e)}`, `ℛ(ζ̄) = ℛ(ζ)*`. -/
theorem ctr_compressed_conj {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) (ζ : ℂ) :
    compressedResolvent p i Hres E (conj ζ) = (compressedResolvent p i Hres E ζ)ᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply, ctr_compressedResolvent_apply, ctr_compressedResolvent_apply,
    ← ctr_ctrFull_conjTranspose hH, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_apply]

theorem ctr_full_det_conj {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) {ζ : ℂ}
    (h : (ctrFull p i Hres E ζ).det ≠ 0) : (ctrFull p i Hres E (conj ζ)).det ≠ 0 := by
  rw [← ctr_ctrFull_conjTranspose hH, Matrix.det_conjTranspose]
  exact (star_ne_zero).mpr h

/-- At a Dyson root the full matrix is invertible (otherwise `ℛ = 0` and `ζ = 0`). -/
theorem ctr_root_det_ne_zero {Hres : p.SiteMatrix} {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p i Hres E ζ) : (ctrFull p i Hres E ζ).det ≠ 0 := by
  intro h0
  have hinv : (ctrFull p i Hres E ζ)⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [h0]; exact not_isUnit_zero)
  have hR : compressedResolvent p i Hres E ζ = 0 := by
    ext x y
    rw [ctr_compressedResolvent_apply, hinv]
    rfl
  have hz := h.2
  rw [hR, Matrix.trace_zero, mul_zero] at hz
  have := h.1
  rw [hz, Complex.zero_im] at this
  exact lt_irrefl 0 this

/-- The Hilbert–Schmidt mass `Σ_{x,z} |ℛ_xz|²` of a pair matrix. -/
def ctrHS (R : PairMatrix p i) : ℝ := ∑ x, ∑ z, Complex.normSq (R x z)

theorem ctrHS_nonneg (R : PairMatrix p i) : 0 ≤ ctrHS R :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem ctr_trace_mul_conjTranspose (R : PairMatrix p i) :
    (R * Rᴴ).trace = (ctrHS R : ℂ) := by
  unfold ctrHS Matrix.trace
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]

/-- **Ward identity** `Im Tr ℛ(ζ) = Im ζ · Σ|ℛ_xz|²` (Hermitian `H^{(e)}`, invertible full
matrix). -/
theorem ctr_ward {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) {ζ : ℂ}
    (h : (ctrFull p i Hres E ζ).det ≠ 0) :
    (compressedResolvent p i Hres E ζ).trace.im =
      ζ.im * ctrHS (compressedResolvent p i Hres E ζ) := by
  have hs := ctr_compressed_sub Hres E h (ctr_full_det_conj hH E h)
  rw [ctr_compressed_conj hH] at hs
  have ht := congrArg Matrix.trace hs
  rw [Matrix.trace_sub, Matrix.trace_smul, ctr_trace_mul_conjTranspose,
    Matrix.trace_conjTranspose] at ht
  have him := congrArg Complex.im ht
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, smul_eq_mul, Complex.mul_im,
    Complex.sub_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, sub_self,
    mul_zero] at him
  linarith

/-- At a Dyson root, `(s/N_aux) Σ|ℛ_xz|² = 1`. -/
theorem ctr_root_ward {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p i Hres E ζ) :
    ctrK p * ctrHS (compressedResolvent p i Hres E ζ) = 1 := by
  have hw := ctr_ward hH E (ctr_root_det_ne_zero h)
  have hz := h.2
  rw [← ctrK_coe] at hz
  have him : ζ.im = ctrK p * (compressedResolvent p i Hres E ζ).trace.im := by
    conv_lhs => rw [hz]
    simp [Complex.mul_im]
  rw [hw] at him
  have hpos := h.1
  have : ζ.im * (ctrK p * ctrHS (compressedResolvent p i Hres E ζ) - 1) = 0 := by
    linear_combination -him
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 hpos.ne'
  · linarith

/-- **Global uniqueness of the Dyson root**: for Hermitian
`H^{(e)}` there is at most one upper-half-plane root of `ζ = (s/N_aux) Tr ℛ(ζ)`.
-/
theorem ctr_root_unique {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ} {ζ₁ ζ₂ : ℂ}
    (h₁ : IsDysonRoot p i Hres E ζ₁) (h₂ : IsDysonRoot p i Hres E ζ₂) : ζ₁ = ζ₂ := by
  by_contra hne
  set R₁ := compressedResolvent p i Hres E ζ₁
  set R₂ := compressedResolvent p i Hres E ζ₂
  have w₁ := ctr_root_ward hH h₁
  have w₂ := ctr_root_ward hH h₂
  have z₁ := h₁.2
  have z₂ := h₂.2
  rw [← ctrK_coe] at z₁ z₂
  have hs := congrArg Matrix.trace
    (ctr_compressed_sub Hres E (ctr_root_det_ne_zero h₁) (ctr_root_det_ne_zero h₂))
  rw [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at hs
  -- `k T = 1`
  have hT : (ctrK p : ℂ) * (R₁ * R₂).trace = 1 := by
    have hsub : ζ₁ - ζ₂ = (ζ₁ - ζ₂) * ((ctrK p : ℂ) * (R₁ * R₂).trace) := by
      calc ζ₁ - ζ₂ = (ctrK p : ℂ) * (R₁.trace - R₂.trace) := by
            rw [mul_sub, ← z₁, ← z₂]
        _ = _ := by rw [hs]; ring
    have hne' : ζ₁ - ζ₂ ≠ 0 := sub_ne_zero.mpr hne
    have := mul_left_cancel₀ hne' (hsub.symm.trans (mul_one _).symm)
    exact this
  -- the defect `Σ |conj R₁ xz - R₂ zx|²` vanishes
  set Q : ℝ := ∑ x, ∑ z, Complex.normSq (conj (R₁ x z) - R₂ z x) with hQ
  have hTre : (R₁ * R₂).trace.re = ∑ x, ∑ z, (R₁ x z * R₂ z x).re := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  have hQeq : Q = ctrHS R₁ + ctrHS R₂ - 2 * (R₁ * R₂).trace.re := by
    have hS₂ : ctrHS R₂ = ∑ x, ∑ z, Complex.normSq (R₂ z x) := by
      unfold ctrHS
      exact Finset.sum_comm
    rw [hQ, hS₂, hTre]
    unfold ctrHS
    rw [mul_comm, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.normSq_sub, Complex.normSq_conj]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hTre1 : ctrK p * (R₁ * R₂).trace.re = 1 := by
    have := congrArg Complex.re hT
    simpa [Complex.mul_re] using this
  have hkQ : ctrK p * Q = 0 := by
    rw [hQeq]
    linear_combination w₁ + w₂ - 2 * hTre1
  have hQ0 : Q = 0 := by
    rcases mul_eq_zero.mp hkQ with h0 | h0
    · exact absurd h0 ctrK_pos.ne'
    · exact h0
  have hzero : ∀ x z, R₂ z x = conj (R₁ x z) := by
    intro x z
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      Finset.sum_nonneg fun z _ => Complex.normSq_nonneg _)).mp hQ0 x (Finset.mem_univ _)
    have hxz := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ =>
      Complex.normSq_nonneg _)).mp hx z (Finset.mem_univ _)
    exact (sub_eq_zero.mp (Complex.normSq_eq_zero.mp hxz)).symm
  have htr : R₂.trace = conj R₁.trace := by
    unfold Matrix.trace
    rw [map_sum]
    exact Finset.sum_congr rfl fun x _ => hzero x x
  have hζ : ζ₂ = conj ζ₁ := by
    rw [z₂, htr, z₁, map_mul, Complex.conj_ofReal]
  have := h₂.1
  rw [hζ, Complex.conj_im] at this
  linarith [h₁.1]

end Linear

/-!
## 2. Schur complement: `ℛ(ζ) = (K_e(E) - ζ)⁻¹` off the exterior poles
-/

section Schur

variable {p : Parameters} {i : ZMod p.n}

theorem ctr_ctrFull_apply_ne (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) {x z : p.Site}
    (h : x ≠ z) : ctrFull p i Hres E ζ x z = Hres x z := by
  unfold ctrFull pairProjector
  simp [Matrix.sub_apply, Matrix.smul_apply, h]

theorem ctr_ctrFull_apply_ext (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) (x z : ExteriorSite p i) :
    ctrFull p i Hres E ζ x.1 z.1 = (exteriorBlock p i Hres - (E : ℂ) • 1) x z := by
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : x = z
  · subst h
    have hx : ¬ (x.1.1 = i ∨ x.1.1 = i + 1) := x.2
    rw [Matrix.one_apply_eq]
    unfold ctrFull pairProjector exteriorBlock
    simp [Matrix.sub_apply, hx]
  · have h' : x.1 ≠ z.1 := fun h'' => h (Subtype.ext h'')
    rw [ctr_ctrFull_apply_ne Hres E ζ h', Matrix.one_apply_ne h]
    simp [exteriorBlock]

theorem ctr_ctrFull_apply_pair (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) (x z : PairSite p i) :
    ctrFull p i Hres E ζ x.1 z.1 = (pairBlock p i Hres - (E : ℂ) • 1 - ζ • 1) x z := by
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul]
  by_cases h : x = z
  · subst h
    have hx : x.1.1 = i ∨ x.1.1 = i + 1 := x.2
    rw [Matrix.one_apply_eq]
    unfold ctrFull pairProjector pairBlock
    simp [Matrix.sub_apply, hx]
  · have h' : x.1 ≠ z.1 := fun h'' => h (Subtype.ext h'')
    rw [ctr_ctrFull_apply_ne Hres E ζ h', Matrix.one_apply_ne h]
    simp [pairBlock]

theorem ctr_ne_of_pair_ext (x : PairSite p i) (y : ExteriorSite p i) : x.1 ≠ y.1 := by
  intro h
  exact y.2 (h ▸ x.2)

/-- Exterior rows of `(H^{(e)} - E - ζP_S) u`. -/
theorem ctr_full_mulVec_ext (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) (u : p.Site → ℂ)
    (x : ExteriorSite p i) :
    (ctrFull p i Hres E ζ *ᵥ u) x.1 =
      (couplingBlock p i Hres *ᵥ fun z : PairSite p i => u z.1) x +
        ((exteriorBlock p i Hres - (E : ℂ) • 1) *ᵥ fun w : ExteriorSite p i => u w.1) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z : p.Site => z.1 = i ∨ z.1 = i + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [ctr_ctrFull_apply_ne Hres E ζ (ctr_ne_of_pair_ext z x).symm]
    rfl
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [ctr_ctrFull_apply_ext]

/-- Pair rows of `(H^{(e)} - E - ζP_S) u` (Hermitian `H^{(e)}`). -/
theorem ctr_full_mulVec_pair {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) (ζ : ℂ)
    (u : p.Site → ℂ) (x : PairSite p i) :
    (ctrFull p i Hres E ζ *ᵥ u) x.1 =
      ((pairBlock p i Hres - (E : ℂ) • 1 - ζ • 1) *ᵥ fun z : PairSite p i => u z.1) x +
        ((couplingBlock p i Hres)ᴴ *ᵥ fun w : ExteriorSite p i => u w.1) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun z : p.Site => z.1 = i ∨ z.1 = i + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [ctr_ctrFull_apply_pair]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [ctr_ctrFull_apply_ne Hres E ζ (ctr_ne_of_pair_ext x z)]
    simp only [couplingBlock, Matrix.conjTranspose_apply]
    rw [← hH.apply x.1 z.1]

/-- Block elimination: if the exterior rows of `(H^{(e)} - E - ζP_S) u` vanish and
`H_R - E` is invertible, then the pair rows are `(K_e(E) - ζ) u_S`, and `u` is determined by
`u_S`. -/
theorem ctr_schur_elim {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0) (ζ : ℂ) (u : p.Site → ℂ)
    (hext : ∀ x : ExteriorSite p i, (ctrFull p i Hres E ζ *ᵥ u) x.1 = 0) :
    (fun w : ExteriorSite p i => u w.1) =
        -(((exteriorBlock p i Hres - (E : ℂ) • 1)⁻¹ * couplingBlock p i Hres) *ᵥ
          fun z : PairSite p i => u z.1) ∧
      ∀ x : PairSite p i, (ctrFull p i Hres E ζ *ᵥ u) x.1 =
        ((edgeSchur p i Hres E - ζ • 1) *ᵥ fun z : PairSite p i => u z.1) x := by
  set A := exteriorBlock p i Hres - (E : ℂ) • 1
  set C := couplingBlock p i Hres
  set up : PairSite p i → ℂ := fun z => u z.1
  set ue : ExteriorSite p i → ℂ := fun w => u w.1
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : A *ᵥ ue = -(C *ᵥ up) := by
    funext x
    have := hext x
    rw [ctr_full_mulVec_ext] at this
    rw [Pi.neg_apply]
    linear_combination this
  have hue : ue = -((A⁻¹ * C) *ᵥ up) := by
    have : A⁻¹ *ᵥ (A *ᵥ ue) = ue := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    rw [← this, h1, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
  refine ⟨hue, fun x => ?_⟩
  rw [ctr_full_mulVec_pair hH]
  change ((pairBlock p i Hres - (E : ℂ) • 1 - ζ • 1) *ᵥ up) x + ((couplingBlock p i Hres)ᴴ *ᵥ ue) x = _
  have hM : pairBlock p i Hres - (E : ℂ) • 1 - ζ • 1 - (couplingBlock p i Hres)ᴴ * (A⁻¹ * C) =
      edgeSchur p i Hres E - ζ • 1 := by
    unfold edgeSchur physicalCoareaF physicalCoareaResolvent
    simp only [A, C, Matrix.mul_assoc]
    abel
  rw [hue, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Pi.neg_apply, ← sub_eq_add_neg,
    ← Pi.sub_apply, ← Matrix.sub_mulVec, hM]

/-- **Schur complement**: off the exterior poles
(`det(H_R - E) ≠ 0`) and for Hermitian `H^{(e)}`, `ℛ_e(ζ) = (K_e(E) - ζ)⁻¹` for every `ζ`
(both totalized inverses vanish together). -/
theorem ctr_compressed_eq_schur {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0) (ζ : ℂ) :
    compressedResolvent p i Hres E ζ = (edgeSchur p i Hres E - ζ • 1)⁻¹ := by
  by_cases hF : (ctrFull p i Hres E ζ).det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hF
    have hext : ∀ x : ExteriorSite p i, (ctrFull p i Hres E ζ *ᵥ v) x.1 = 0 := fun x => by
      rw [hv]; rfl
    obtain ⟨hue, hpair⟩ := ctr_schur_elim hH hdet ζ v hext
    have hup : (fun z : PairSite p i => v z.1) ≠ 0 := by
      intro h0
      apply hv0
      funext y
      by_cases hy : y.1 = i ∨ y.1 = i + 1
      · exact congrFun h0 ⟨y, hy⟩
      · have := congrFun hue ⟨y, hy⟩
        rw [h0, Matrix.mulVec_zero, neg_zero] at this
        exact this
    have hK : (edgeSchur p i Hres E - ζ • 1).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hup, ?_⟩
      funext x
      rw [← hpair x, hv]
      rfl
    have h1 : (ctrFull p i Hres E ζ)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hF]; exact not_isUnit_zero)
    have h2 : (edgeSchur p i Hres E - ζ • 1)⁻¹ = 0 :=
      Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hK]; exact not_isUnit_zero)
    rw [h2]
    ext x y
    rw [ctr_compressedResolvent_apply, h1]
    rfl
  · have hU : IsUnit (ctrFull p i Hres E ζ).det := isUnit_iff_ne_zero.mpr hF
    refine (Matrix.inv_eq_right_inv ?_).symm
    ext x y
    set u : p.Site → ℂ := fun w => (ctrFull p i Hres E ζ)⁻¹ w y.1
    have hcol : ∀ w, (ctrFull p i Hres E ζ *ᵥ u) w = (1 : p.SiteMatrix) w y.1 := by
      intro w
      rw [← Matrix.mul_nonsing_inv _ hU, Matrix.mul_apply]
      rfl
    have hext : ∀ x : ExteriorSite p i, (ctrFull p i Hres E ζ *ᵥ u) x.1 = 0 := fun x => by
      rw [hcol, Matrix.one_apply_ne (ctr_ne_of_pair_ext y x).symm]
    obtain ⟨_, hpair⟩ := ctr_schur_elim hH hdet ζ u hext
    have := hpair x
    rw [hcol] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : ((edgeSchur p i Hres E - ζ • 1) *ᵥ fun z : PairSite p i => u z.1) x =
        ∑ z, (edgeSchur p i Hres E - ζ • 1) x z * compressedResolvent p i Hres E ζ z y := rfl
    rw [← h2, ← this, Matrix.one_apply]
    simp only [Subtype.ext_iff]

end Schur

/-!
## 3. The clip of `centerFormula` is inactive at a root (Ward identity)
-/

section Clip

variable {p : Parameters} {i : ZMod p.n}

/-- The sign `±1` of `J_e = P_i - P_{i+1}` at a pair site. -/
def ctrSign (x : PairSite p i) : ℝ := if x.1.1 = i then 1 else -1

theorem ctr_abs_ctrSign (x : PairSite p i) : |ctrSign x| = 1 := by
  unfold ctrSign
  split_ifs <;> simp

theorem ctr_trace_contrast (M : PairMatrix p i) :
    (pairContrast p i * Mᴴ * M).trace =
      ((∑ x, ctrSign x * ∑ z, Complex.normSq (M z x) : ℝ) : ℂ) := by
  unfold Matrix.trace pairContrast
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply, mul_assoc, Complex.star_def,
    mul_comm (conj (M z x)), Complex.mul_conj]
  unfold ctrSign
  split_ifs <;> simp

theorem ctr_abs_contrast_le (M : PairMatrix p i) :
    |∑ x, ctrSign x * ∑ z, Complex.normSq (M z x)| ≤ ctrHS M := by
  have hS : ctrHS M = ∑ x, ∑ z, Complex.normSq (M z x) := by
    unfold ctrHS
    exact Finset.sum_comm
  rw [hS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul, ctr_abs_ctrSign, one_mul,
    abs_of_nonneg (Finset.sum_nonneg fun z _ => Complex.normSq_nonneg _)]

/-- The unclipped center value `(s/N_aux) Tr J_e ℛ*ℛ`. -/
theorem ctr_contrast_re (M : PairMatrix p i) :
    ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * (pairContrast p i * Mᴴ * M).trace).re =
      ctrK p * ∑ x, ctrSign x * ∑ z, Complex.normSq (M z x) := by
  rw [← ctrK_coe, ctr_trace_contrast, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **The clip is inactive**: at a Dyson root (Hermitian `H^{(e)}`) the clip in `centerFormula`
is inactive, since `|(s/N) Tr J ℛ*ℛ| ≤ (s/N) Tr ℛ*ℛ = 1`. -/
theorem ctr_centerFormula_eq {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ} {ζ : ℂ}
    (h : IsDysonRoot p i Hres E ζ) :
    centerFormula p i Hres E ζ =
      ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ *
        (pairContrast p i * (compressedResolvent p i Hres E ζ)ᴴ *
          compressedResolvent p i Hres E ζ).trace).re := by
  have hw := ctr_root_ward hH h
  set M := compressedResolvent p i Hres E ζ
  have hb : |((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ * (pairContrast p i * Mᴴ * M).trace).re| ≤ 1 := by
    rw [ctr_contrast_re, abs_mul, abs_of_pos ctrK_pos, ← hw]
    exact mul_le_mul_of_nonneg_left (ctr_abs_contrast_le M) ctrK_pos.le
  unfold centerFormula
  rw [min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

/-- `|centerFormula| ≤ 1` everywhere (the clip). -/
theorem ctr_abs_centerFormula_le (Hres : p.SiteMatrix) (E : ℝ) (ζ : ℂ) :
    |centerFormula p i Hres E ζ| ≤ 1 := by
  unfold centerFormula
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- `|dysonCenter| ≤ 1` everywhere. -/
theorem ctr_abs_dysonCenter_le (cst : CenterDomainConstants) (α : Fin p.N)
    (Hres : p.SiteMatrix) (E : ℝ) : |dysonCenter p i cst α Hres E| ≤ 1 := by
  unfold dysonCenter
  split_ifs
  · exact ctr_abs_centerFormula_le _ _ _
  · simp

end Clip

/-!
## 4. `freshDyson` is the certificate's canonical root
-/

section Fresh

open BlockBand.Palm

variable {N : ℕ}

theorem ctr_matrixTrace_eq (F : Matrix (Fin N) (Fin N) ℂ) (w : ℂ) :
    certificateMatrixTrace F w = (N : ℂ)⁻¹ * (F - w • 1)⁻¹.trace := by
  unfold certificateMatrixTrace certificateMatrixResolvent
  rw [Fintype.card_fin, div_eq_inv_mul]

/-- A matrix-form positive root is a spectral root. -/
theorem ctr_residual_of_matrix (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hm : 0 < m.im)
    (heq : m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace) :
    certificateDysonResidual hF.eigenvalues s z m = 0 := by
  have ha : (z + (s : ℂ) * m).im ≠ 0 := by
    have : 0 < (z + (s : ℂ) * m).im := by
      simpa using add_pos_of_nonneg_of_pos hz (mul_pos hs hm)
    exact this.ne'
  rw [certificateDysonResidual_eq_zero_iff, ← certificateMatrixTrace_eq_average F hF ha,
    ctr_matrixTrace_eq]
  exact heq

/-- **`freshDyson` selects the unique positive root** (`certificate_dyson_unique_nonnegative`):
every matrix-form root with positive imaginary part at `Im z ≥ 0` is `freshDyson F s z`. -/
theorem ctr_freshDyson_eq (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) (hN : 0 < N)
    {s : ℝ} (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hm : 0 < m.im)
    (heq : m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace) : freshDyson F s z = m := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hex : ∃ m : ℂ, 0 < m.im ∧ m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace :=
    ⟨m, hm, heq⟩
  unfold freshDyson
  rw [dite_eq_left hex]
  have hspec := Classical.choose_spec hex
  exact certificate_dyson_unique_nonnegative hF.eigenvalues hs hz hspec.1 hm
    (ctr_residual_of_matrix F hF hs hz hspec.1 hspec.2) (ctr_residual_of_matrix F hF hs hz hm heq)

/-- `FreshRegular` is monotone in its constants (smaller rectangle, smaller `v₀`). -/
theorem ctr_freshRegular_mono {F : Matrix (Fin N) (Fin N) ℂ} {c₀ E r s₀ v r' s₀' v' : ℝ}
    (h : FreshRegular F c₀ E r s₀ v) (hr : r' ≤ r) (hs : s₀' ≤ s₀) (hv : v' ≤ v) (hv' : 0 < v') :
    FreshRegular F c₀ E r' s₀' v' := by
  intro s' hs' x hx η hη
  obtain ⟨h1, h2⟩ := h s' ⟨by linarith [hs'.1], hs'.2⟩ x (hx.trans hr) η hη
  exact ⟨hv.trans h1, h2.trans (inv_anti₀ hv' hv)⟩

/-- The certificate data used for the regular clause at variance `c` and bulk margin `θ`:
`(ε, r₀, s₀, v₀)` with `FreshConstants` and the fresh regularity bound for every Hermitian `F` with
`|χ| ≤ ε` and `|E| ≤ 2 - θ`. -/
def ctrCertSpec (c θ : ℝ) (q : ℝ × ℝ × ℝ × ℝ) : Prop :=
  0 < q.1 ∧ FreshConstants c q.2.1 q.2.2.1 q.2.2.2 ∧
    ∀ (N : ℕ) (F : Matrix (Fin N) (Fin N) ℂ), 0 < N → F.IsHermitian → ∀ E : ℝ, |E| ≤ 2 - θ →
      ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤ q.1 →
      FreshRegular F c E q.2.1 q.2.2.1 q.2.2.2

/-- Existence of certificate data, from `certificate_semicircle_full`. -/
theorem ctr_cert_exists {c θ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hθ : 0 < θ) (hθ2 : θ ≤ 2) :
    ∃ q, ctrCertSpec c θ q := by
  obtain ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, _hC, hall⟩ :=
    certificate_semicircle_full.{0} hc hc1 hθ hθ2
  refine ⟨(ε, r, s₀, v₀), hε, ⟨hc, hc1, hr, hs₀, hs₀c, hv₀⟩, ?_⟩
  intro N F hN hF E hE hχ s' hs' x hx η hη
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨hrect, -⟩ := hall (Fin N) F hF E hE hχ
  obtain ⟨heq, hlo, hhi⟩ := hrect s' hs'.1 hs'.2 x hx η hη.1 hη.2
  have hz : (⟨x, η⟩ : ℂ) = (x : ℂ) + Complex.I * η := by
    apply Complex.ext <;> simp
  have hs'pos : 0 < s' := by linarith [hs'.1]
  have hfd : freshDyson F s' ⟨x, η⟩ =
      certificateCanonicalDyson hF.eigenvalues s' ((x : ℂ) + Complex.I * η) := by
    rw [hz]
    refine ctr_freshDyson_eq F hF hN hs'pos (by simpa using hη.1) (hv₀.trans_le hlo) ?_
    rw [← ctr_matrixTrace_eq]
    exact heq
  rw [hfd]
  exact ⟨hlo, hhi⟩

/-- Selected certificate data (default `(1,1,1,1)` outside `0 < c < 1`, `0 < θ ≤ 2`). -/
def ctrCert (c θ : ℝ) : ℝ × ℝ × ℝ × ℝ := by
  classical
  exact if h : (0 < c ∧ c < 1) ∧ (0 < θ ∧ θ ≤ 2) then
    Classical.choose (ctr_cert_exists h.1.1 h.1.2 h.2.1 h.2.2) else (1, 1, 1, 1)

theorem ctrCert_spec {c θ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hθ : 0 < θ) (hθ2 : θ ≤ 2) :
    ctrCertSpec c θ (ctrCert c θ) := by
  have h : (0 < c ∧ c < 1) ∧ (0 < θ ∧ θ ≤ 2) := ⟨⟨hc, hc1⟩, hθ, hθ2⟩
  unfold ctrCert
  rw [dite_eq_left h]
  exact Classical.choose_spec (ctr_cert_exists h.1.1 h.1.2 h.2.1 h.2.2)

theorem ctrCert_fst_pos (c θ : ℝ) : 0 < (ctrCert c θ).1 := by
  by_cases h : (0 < c ∧ c < 1) ∧ (0 < θ ∧ θ ≤ 2)
  · exact (ctrCert_spec h.1.1 h.1.2 h.2.1 h.2.2).1
  · unfold ctrCert
    rw [dite_eq_right h]
    norm_num

end Fresh

/-!
## 5. Pair bookkeeping: dimension, reindexing, residual
-/

section Pair

open BlockBand.Palm

variable {p : Parameters} {i : ZMod p.n}

theorem ctr_card_pairSite : Fintype.card (PairSite p i) = 2 * p.W := by
  rw [← Fintype.card_congr (BlockBand.Layers.rpPairEquiv (p := p) i), Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

theorem ctr_card_pairSite_pos : 0 < Fintype.card (PairSite p i) := by
  rw [ctr_card_pairSite]
  exact Nat.mul_pos (by norm_num) p.W_pos

theorem ctr_card_pairSite_coe : ((Fintype.card (PairSite p i) : ℕ) : ℂ) = 2 * (p.W : ℂ) := by
  rw [ctr_card_pairSite]
  push_cast
  ring

theorem ctr_pairToFin_eq (M : PairMatrix p i) :
    pairToFin M = M.submatrix (Fintype.equivFin (PairSite p i)).symm
      (Fintype.equivFin (PairSite p i)).symm := by
  unfold pairToFin
  rw [Matrix.reindex_apply]

theorem ctr_pairToFin_isHermitian {M : PairMatrix p i} (hM : M.IsHermitian) :
    (pairToFin M).IsHermitian := by
  rw [ctr_pairToFin_eq]
  exact hM.submatrix _

/-- Reindexing to `Fin (2W)` does not change shifted inverse traces. -/
theorem ctr_pairToFin_shift_trace (M : PairMatrix p i) (w : ℂ) :
    (pairToFin M - w • 1)⁻¹.trace = (M - w • 1)⁻¹.trace := by
  set e := (Fintype.equivFin (PairSite p i)).symm
  have h1 : pairToFin M - w • (1 : Matrix (Fin (Fintype.card (PairSite p i)))
      (Fin (Fintype.card (PairSite p i))) ℂ) = (M - w • 1).submatrix e e := by
    ext a b
    rw [ctr_pairToFin_eq]
    by_cases h : a = b
    · subst h; simp [e]
    · have h' : e a ≠ e b := fun h'' => h (e.injective h'')
      simp [Matrix.one_apply_ne h, Matrix.one_apply_ne h', e]
  rw [h1, Matrix.inv_submatrix_equiv]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun x => (M - w • 1)⁻¹ x x)

/-- `F = K_e(E) + E = V - C*(H_R - E)⁻¹C` is Hermitian for Hermitian `H^{(e)}`. -/
theorem ctr_edgeSchur_add_isHermitian {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) (E : ℝ) :
    (edgeSchur p i Hres E + (E : ℂ) • 1).IsHermitian := by
  unfold edgeSchur physicalCoareaF physicalCoareaResolvent
  rw [sub_add_cancel]
  have hV : (pairBlock p i Hres).IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, pairBlock]
    exact hH.apply x.1 y.1
  have hR : (exteriorBlock p i Hres).IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, exteriorBlock]
    exact hH.apply x.1 y.1
  have hE1 : ((E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).IsHermitian := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := fun h'' => h h''.symm
      simp [Matrix.one_apply_ne h, Matrix.one_apply_ne h']
  have hRE : (exteriorBlock p i Hres - (E : ℂ) • 1).IsHermitian := hR.sub hE1
  exact hV.sub (Matrix.isHermitian_conjTranspose_mul_mul _ hRE.inv)

theorem ctr_conj_matchedA (E : ℝ) : conj (matchedA E) = certificateSemicircleReference E := by
  apply Complex.ext <;> simp [matchedA, certificateSemicircleReference]
  ring

/-- `Tr M = W (W⁻¹Tr P_i M + W⁻¹Tr P_{i+1} M)`. -/
theorem ctr_trace_split (M : PairMatrix p i) :
    M.trace = (p.W : ℂ) * (pairBlockTrace p i M i + pairBlockTrace p i M (i + 1)) := by
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  unfold pairBlockTrace
  rw [← mul_add, ← mul_assoc, mul_inv_cancel₀ hW, one_mul, ← Finset.sum_add_distrib]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply]
  rcases x.2 with h | h
  · have h' : x.1.1 ≠ i + 1 := by
      rw [h]; exact (BlockBand.Layers.rng_add_one_ne p i).symm
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false h'), add_zero]
  · have h' : x.1.1 ≠ i := by
      rw [h]; exact BlockBand.Layers.rng_add_one_ne p i
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false h'), zero_add]

/-- The certificate residual `χ` of `F = K_e(E) + E` at `c = s` is bounded by the center
residual `ε_e` (off the exterior poles, Hermitian `H^{(e)}`). -/
theorem ctr_chi_le {Hres : p.SiteMatrix} (hH : Hres.IsHermitian) {E : ℝ}
    (hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0) :
    ‖certificateChi (pairToFin (edgeSchur p i Hres E + (E : ℂ) • 1)) (splitS p) E
        (certificateSemicircleReference E)‖ ≤ centerResidual p i Hres E := by
  set μ := certificateSemicircleReference E
  set R := compressedResolvent p i Hres E ((splitS p : ℂ) * μ)
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hχ : certificateChi (pairToFin (edgeSchur p i Hres E + (E : ℂ) • 1)) (splitS p) E μ =
      ((pairBlockTrace p i R i - μ) + (pairBlockTrace p i R (i + 1) - μ)) / 2 := by
    unfold certificateChi
    rw [ctr_matrixTrace_eq, ctr_pairToFin_shift_trace, ctr_card_pairSite_coe]
    have hK : edgeSchur p i Hres E + (E : ℂ) • 1 - ((E : ℂ) + (splitS p : ℂ) * μ) • 1 =
        edgeSchur p i Hres E - ((splitS p : ℂ) * μ) • 1 := by
      rw [add_smul]; abel
    rw [hK, ← ctr_compressed_eq_schur hH hdet, ctr_trace_split]
    field_simp
    ring
  have hres : centerResidual p i Hres E =
      Real.sqrt (‖pairBlockTrace p i R i - μ‖ ^ 2 + ‖pairBlockTrace p i R (i + 1) - μ‖ ^ 2) := by
    unfold centerResidual
    rw [ctr_conj_matchedA]
  rw [hχ, hres, norm_div, Complex.norm_two]
  set a := ‖pairBlockTrace p i R i - μ‖
  set b := ‖pairBlockTrace p i R (i + 1) - μ‖
  have ha : a ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg b])
  have hb : b ≤ Real.sqrt (a ^ 2 + b ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg a])
  have := norm_add_le (pairBlockTrace p i R i - μ) (pairBlockTrace p i R (i + 1) - μ)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- For `ϑ`-bulk ranks the interval margin is at least `ϑ/2`. -/
theorem ctr_rankMargin_ge {ϑ : ℝ} (hϑ : 0 < ϑ) (α : Fin p.N) (hα : IsBulkRank p ϑ α) :
    ϑ / 2 ≤ rankMargin p α := by
  have h := BlockBand.RankLocation.classicalLocation_mem_bulkInterval hϑ p α hα
  unfold bulkInterval at h
  have habs : |classicalLocation p α| ≤ 2 - ϑ := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  unfold rankMargin
  linarith

end Pair

/-!
## 6. The domain constants `cst0` and the regular clause
-/

section Regular

open BlockBand.Palm

/-- Dyadic-type grid of bulk margins `θ_k = 2/(k+1)`. -/
def ctrTheta (k : ℕ) : ℝ := 2 / ((k : ℝ) + 1)

/-- Grid level of a margin `κ`: `k(κ) = ⌈2/κ⌉`, so `θ_{k(κ)} ≤ κ` and `k` is antitone in `κ`. -/
def ctrLevel (κ : ℝ) : ℕ := ⌈2 / κ⌉₊

/-- The splitting variance `s = min(1 - 2b, b)` as a function of `b`. -/
def ctrC (b : ℝ) : ℝ := min (1 - 2 * b) b

theorem ctrTheta_pos (k : ℕ) : 0 < ctrTheta k := by
  unfold ctrTheta; positivity

theorem ctrTheta_le_two (k : ℕ) : ctrTheta k ≤ 2 := by
  unfold ctrTheta
  rw [div_le_iff₀ (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem ctrTheta_level_le {κ : ℝ} (hκ : 0 < κ) : ctrTheta (ctrLevel κ) ≤ κ := by
  unfold ctrTheta ctrLevel
  have h1 : 2 / κ ≤ (⌈2 / κ⌉₊ : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hκ] at h1
  nlinarith

theorem ctrLevel_mono {κ κ' : ℝ} (hκ : 0 < κ) (h : κ ≤ κ') : ctrLevel κ' ≤ ctrLevel κ := by
  unfold ctrLevel
  exact Nat.ceil_mono (div_le_div_of_nonneg_left (by norm_num) hκ h)

/-- **The domain constants of the center** (positive functions of `b` and `κ`):
`ε₁(b, κ)` is half the certificate threshold at `c = s(b) = min(1-2b, b)` and the grid margin
`θ_{k(κ)} ≤ κ` (the root built from the certificate then
persists on `{ε_e < 2ε₁}`, which leaves room for the smooth cutoff, equal to one on the whole
domain `{ε_e ≤ ε₁}`); `ρ₀ = 3`, a radius large enough that the disk condition is never binding on
the regular domain (the root built from the certificate has `|ζ| ≤ √s ≤ 1`, and `|s ā| = s ≤ 1`
on the bulk interval; see `cst0_inCenterDomain_iff`). -/
def cst0 : CenterDomainConstants where
  ε₁ b κ := (ctrCert (ctrC b) (ctrTheta (ctrLevel κ))).1 / 2
  ρ₀ _ _ := 3
  ε₁_pos _ _ := half_pos (ctrCert_fst_pos _ _)
  ρ₀_pos _ _ := by norm_num

theorem ctr_splitS_eq (p : Parameters) : splitS p = ctrC p.b := rfl

/-- The selected root, in the domain. -/
theorem ctr_dysonRoot_spec {p : Parameters} {i : ZMod p.n} {ρ : ℝ} {Hres : p.SiteMatrix} {E : ℝ}
    (h : ∃ ζ, IsDysonRoot p i Hres E ζ ∧ ‖ζ - (splitS p : ℂ) * conj (matchedA E)‖ < ρ) :
    IsDysonRoot p i Hres E (dysonRoot p i ρ Hres E) ∧
      ‖dysonRoot p i ρ Hres E - (splitS p : ℂ) * conj (matchedA E)‖ < ρ := by
  unfold dysonRoot
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem ctr_dysonCenter_of_mem {p : Parameters} {i : ZMod p.n} {cst : CenterDomainConstants}
    {α : Fin p.N} {Hres : p.SiteMatrix} {E : ℝ} (h : InCenterDomain p i cst α Hres E) :
    dysonCenter p i cst α Hres E =
      centerFormula p i Hres E (dysonRoot p i (cst.ρ₀ p.b (rankMargin p α)) Hres E) := by
  unfold dysonCenter
  exact ite_eq_left_of_eq_true _ _ (eq_true h)

/-- **Regular clause of the physical center theorem** (`CenterDomainContract.regular` for `cst0`;
deterministic). Constants: `r₀, s₀, v₀` are minima of
the certificate constants over the finitely many grid levels `k ≤ k(ϑ/2)`, `y₀ = s v₀`,
`C = 1`. -/
theorem centerDomain_regular : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ r₀ s₀ v₀ y₀ C : ℝ, FreshConstants (min (1 - 2 * b) b) r₀ s₀ v₀ ∧ 0 < y₀ ∧
      ∀ (p : Parameters), p.b = b → ∀ (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
        (Hres : p.SiteMatrix), Hres.IsHermitian → ∀ E : ℝ,
        (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0 → InCenterDomain p i cst0 α Hres E →
        let K := edgeSchur p i Hres E
        let ζ := dysonRoot p i (cst0.ρ₀ p.b (rankMargin p α)) Hres E
        FreshRegular (pairToFin (K + (E : ℂ) • 1)) (splitS p) E r₀ s₀ v₀ ∧
          IsDysonRoot p i Hres E ζ ∧
          compressedResolvent p i Hres E ζ = (K - ζ • 1)⁻¹ ∧
          (∀ ζ', IsDysonRoot p i Hres E ζ' →
            ‖ζ' - (splitS p : ℂ) * conj (matchedA E)‖ < cst0.ρ₀ p.b (rankMargin p α) →
              ζ' = ζ) ∧
          ζ = (splitS p : ℂ) * freshDyson (pairToFin (K + (E : ℂ) • 1)) (splitS p) E ∧
          y₀ ≤ ζ.im ∧ ‖ζ‖ ≤ C ∧
          dysonCenter p i cst0 α Hres E = ((splitS p : ℂ) * (2 * (p.W : ℂ))⁻¹ *
            (pairContrast p i * ((K - ζ • 1)⁻¹)ᴴ * (K - ζ • 1)⁻¹).trace).re := by
  intro b hb hb2 ϑ hϑ _hϑ2
  set c := ctrC b with hcdef
  have hc : 0 < c := lt_min (by linarith) hb
  have hc1 : c < 1 := (min_le_right _ _).trans_lt (by linarith)
  set K₀ := ctrLevel (ϑ / 2)
  set S := Finset.range (K₀ + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  have hspec : ∀ j, ctrCertSpec c (ctrTheta j) (ctrCert c (ctrTheta j)) := fun j =>
    ctrCert_spec hc hc1 (ctrTheta_pos j) (ctrTheta_le_two j)
  set r₀ := S.inf' hS (fun j => (ctrCert c (ctrTheta j)).2.1)
  set s₀ := S.inf' hS (fun j => (ctrCert c (ctrTheta j)).2.2.1)
  set v₀ := S.inf' hS (fun j => (ctrCert c (ctrTheta j)).2.2.2)
  have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff hS).mpr fun j _ => (hspec j).2.1.2.2.1
  have hs₀ : 0 < s₀ := (Finset.lt_inf'_iff hS).mpr fun j _ => (hspec j).2.1.2.2.2.1
  have hv₀ : 0 < v₀ := (Finset.lt_inf'_iff hS).mpr fun j _ => (hspec j).2.1.2.2.2.2.2
  have hs₀c : s₀ < c / 2 :=
    (Finset.inf'_le _ (by simp [S] : 0 ∈ S)).trans_lt (hspec 0).2.1.2.2.2.2.1
  refine ⟨r₀, s₀, v₀, c * v₀, 1, ⟨hc, hc1, hr₀, hs₀, hs₀c, hv₀⟩, mul_pos hc hv₀, ?_⟩
  intro p hpb α hα i Hres hH E hdet hdom K ζ
  have hsp : splitS p = c := by rw [ctr_splitS_eq, hpb]
  have hs : 0 < splitS p := ctr_splitS_pos
  -- the grid level of the rank
  have hκ : ϑ / 2 ≤ rankMargin p α := ctr_rankMargin_ge hϑ α hα
  have hκpos : 0 < rankMargin p α := (by linarith : 0 < ϑ / 2).trans_le hκ
  set k := ctrLevel (rankMargin p α)
  have hkS : k ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le (ctrLevel_mono (by linarith) hκ))
  have hθ : ctrTheta k ≤ rankMargin p α := ctrTheta_level_le hκpos
  have hE : |E| ≤ 2 - ctrTheta k := by
    have h1 := hdom.1
    unfold bulkInterval at h1
    exact abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
  -- fresh regularity from the certificate
  set F := pairToFin (K + (E : ℂ) • 1)
  have hF : F.IsHermitian := ctr_pairToFin_isHermitian (ctr_edgeSchur_add_isHermitian hH E)
  have hN : 0 < Fintype.card (PairSite p i) := ctr_card_pairSite_pos
  have hχ : ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤
      (ctrCert c (ctrTheta k)).1 := by
    have h1 := ctr_chi_le hH hdet
    rw [hsp] at h1
    refine h1.trans (hdom.2.1.trans ?_)
    change (ctrCert (ctrC p.b) (ctrTheta k)).1 / 2 ≤ _
    rw [hpb]
    exact half_le_self (ctrCert_fst_pos _ _).le
  have hreg0 := (hspec k).2.2 _ F hN hF E hE hχ
  have hreg : FreshRegular F (splitS p) E r₀ s₀ v₀ := by
    rw [hsp]
    exact ctr_freshRegular_mono hreg0 (Finset.inf'_le _ hkS) (Finset.inf'_le _ hkS)
      (Finset.inf'_le _ hkS) hv₀
  -- the selected root
  have hroot : IsDysonRoot p i Hres E ζ := (ctr_dysonRoot_spec hdom.2.2).1
  have hR : compressedResolvent p i Hres E ζ = (K - ζ • 1)⁻¹ := ctr_compressed_eq_schur hH hdet ζ
  -- `ζ = s m_s(E)`
  set m : ℂ := ζ / (splitS p : ℂ)
  have hsC : (splitS p : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hWC : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hζm : ζ = (splitS p : ℂ) * m := by
    simp only [m]; field_simp
  have hm : 0 < m.im := by
    have : m.im = ζ.im / splitS p := by
      simp only [m]; rw [Complex.div_ofReal_im]
    rw [this]
    exact div_pos hroot.1 hs
  have heq : m = ((Fintype.card (PairSite p i) : ℕ) : ℂ)⁻¹ *
      (F - ((E : ℂ) + (splitS p : ℂ) * m) • 1)⁻¹.trace := by
    rw [ctr_pairToFin_shift_trace, ← hζm, ctr_card_pairSite_coe]
    have hK : K + (E : ℂ) • 1 - ((E : ℂ) + ζ) • 1 = K - ζ • 1 := by
      rw [add_smul]; abel
    rw [hK, ← hR]
    have h2 := hroot.2
    simp only [m]
    rw [div_eq_iff hsC]
    nth_rewrite 1 [h2]
    ring
  have hz0 : (0 : ℝ) ≤ ((E : ℂ)).im := by simp
  have hfd : freshDyson F (splitS p) E = m := ctr_freshDyson_eq F hF hN hs hz0 hm heq
  refine ⟨hreg, hroot, hR, fun ζ' h' _ => ctr_root_unique hH h' hroot, ?_, ?_, ?_, ?_⟩
  · rw [hfd]; exact hζm
  · -- `Im ζ ≥ s v₀`
    have h1 := (hreg (splitS p) ⟨by linarith, le_refl _⟩ E (by simp [hr₀.le]) 0 ⟨le_refl _, zero_le_one⟩).1
    have h2 : (⟨E, 0⟩ : ℂ) = (E : ℂ) := rfl
    rw [h2, hfd] at h1
    rw [hζm, ← hsp]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left h1 hs.le
  · -- `|ζ| ≤ √s ≤ 1`
    have : Nonempty (Fin (Fintype.card (PairSite p i))) := ⟨⟨0, hN⟩⟩
    have hres := ctr_residual_of_matrix F hF hs hz0 hm heq
    have hsq := certificate_dyson_normSq_le hF.eigenvalues hs hz0 hm hres
    have hnorm : ‖ζ‖ ^ 2 ≤ 1 := by
      rw [hζm, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        ← Complex.normSq_eq_norm_sq]
      calc splitS p ^ 2 * Complex.normSq m ≤ splitS p ^ 2 * (splitS p)⁻¹ :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = splitS p := by field_simp
        _ ≤ 1 := ctr_splitS_le_one
    nlinarith [norm_nonneg ζ]
  · rw [ctr_dysonCenter_of_mem hdom, ctr_centerFormula_eq hH hroot, hR]

end Regular

/-!
## 7. Root existence on the regular domain of `cst0`
-/

section Existence

open BlockBand.Palm

theorem ctr_freshDyson_spec {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ)
    (h : 0 < (freshDyson F s z).im) :
    freshDyson F s z = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * freshDyson F s z) • 1)⁻¹.trace := by
  by_cases hex : ∃ m : ℂ, 0 < m.im ∧ m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace
  · have hfd : freshDyson F s z = Classical.choose hex := by
      unfold freshDyson
      rw [dite_eq_left hex]
    rw [hfd]
    exact (Classical.choose_spec hex).2
  · have hfd : freshDyson F s z = 0 := by
      unfold freshDyson
      rw [dite_eq_right hex]
    rw [hfd, Complex.zero_im] at h
    exact absurd h (lt_irrefl 0)

theorem ctr_norm_matchedA {E : ℝ} (hE : |E| ≤ 2) : ‖matchedA E‖ = 1 := by
  have h4 : 0 ≤ 4 - E ^ 2 := by
    have := abs_le.mp hE
    nlinarith
  have hsq : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]
    simp only [matchedA]
    have := Real.sq_sqrt h4
    nlinarith
  rw [← Real.sqrt_one, ← hsq, Complex.norm_def]

/-- **The root-existence conjunct is automatic for `cst0`**: for a `ϑ`-bulk
rank, Hermitian `H^{(e)}` and `E` off the exterior poles, `E ∈ I` and `ε_e(E) ≤ ε₁` already
give a Dyson root in the disk `|ζ - s ā| < ρ₀ = 3`; so the regular domain of `cst0` is
`{E ∈ I, ε_e(E) ≤ ε₁}` exactly (triage Q2).
-/
theorem cst0_inCenterDomain_iff {ϑ : ℝ} (hϑ : 0 < ϑ) (p : Parameters) (α : Fin p.N)
    (hα : IsBulkRank p ϑ α) (i : ZMod p.n) {Hres : p.SiteMatrix} (hH : Hres.IsHermitian)
    {E : ℝ} (hdet : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0) :
    InCenterDomain p i cst0 α Hres E ↔
      E ∈ bulkInterval (rankMargin p α) ∧
        centerResidual p i Hres E ≤ cst0.ε₁ p.b (rankMargin p α) := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun ⟨hI, hε⟩ => ⟨hI, hε, ?_⟩⟩
  set c := splitS p
  have hc : 0 < c := ctr_splitS_pos
  have hc1 : c < 1 := by
    have : c ≤ p.b := min_le_right _ _
    linarith [p.b_lt_half]
  have hκ : ϑ / 2 ≤ rankMargin p α := ctr_rankMargin_ge hϑ α hα
  have hκpos : 0 < rankMargin p α := (by linarith : 0 < ϑ / 2).trans_le hκ
  set k := ctrLevel (rankMargin p α)
  have hθ : ctrTheta k ≤ rankMargin p α := ctrTheta_level_le hκpos
  have hE : |E| ≤ 2 - ctrTheta k := by
    unfold bulkInterval at hI
    exact abs_le.mpr ⟨by linarith [hI.1], by linarith [hI.2]⟩
  set K := edgeSchur p i Hres E
  set F := pairToFin (K + (E : ℂ) • 1)
  have hF : F.IsHermitian := ctr_pairToFin_isHermitian (ctr_edgeSchur_add_isHermitian hH E)
  have hN : 0 < Fintype.card (PairSite p i) := ctr_card_pairSite_pos
  have hspec := ctrCert_spec hc hc1 (ctrTheta_pos k) (ctrTheta_le_two k)
  have hχ : ‖certificateChi F c E (certificateSemicircleReference E)‖ ≤
      (ctrCert c (ctrTheta k)).1 :=
    (ctr_chi_le hH hdet).trans (hε.trans (half_le_self (ctrCert_fst_pos _ _).le))
  have hreg := hspec.2.2 _ F hN hF E hE hχ
  have hv := hspec.2.1.2.2.2.2.2
  have hs₀ := hspec.2.1.2.2.2.1
  have hr₀ := hspec.2.1.2.2.1
  have h1 := (hreg c ⟨by linarith, le_refl _⟩ E (by simp [hr₀.le]) 0
    ⟨le_refl _, zero_le_one⟩).1
  have h0 : (⟨E, 0⟩ : ℂ) = (E : ℂ) := rfl
  rw [h0] at h1
  set m := freshDyson F c E
  have hm : 0 < m.im := hv.trans_le h1
  have heq : m = ((Fintype.card (PairSite p i) : ℕ) : ℂ)⁻¹ *
      (F - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace := ctr_freshDyson_spec F c E hm
  have hsC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hWC : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  refine ⟨(c : ℂ) * m, ⟨?_, ?_⟩, ?_⟩
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos hc hm
  · rw [ctr_compressed_eq_schur hH hdet]
    have htr : (F - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace =
        (K + (E : ℂ) • 1 - ((E : ℂ) + (c : ℂ) * m) • 1)⁻¹.trace :=
      ctr_pairToFin_shift_trace (K + (E : ℂ) • 1) ((E : ℂ) + (c : ℂ) * m)
    have hK : K + (E : ℂ) • 1 - ((E : ℂ) + (c : ℂ) * m) • 1 = K - ((c : ℂ) * m) • 1 := by
      rw [add_smul]; abel
    rw [hK] at htr
    rw [← htr, ← ctr_card_pairSite_coe (i := i)]
    change (c : ℂ) * m = (c : ℂ) * _ * _
    nth_rewrite 1 [heq]
    ring
  · have z0 : (0 : ℝ) ≤ ((E : ℂ)).im := by simp
    have : Nonempty (Fin (Fintype.card (PairSite p i))) := ⟨⟨0, hN⟩⟩
    have hres := ctr_residual_of_matrix F hF hc z0 hm heq
    have hsq := certificate_dyson_normSq_le hF.eigenvalues hc z0 hm hres
    have hζ : ‖(c : ℂ) * m‖ ≤ 1 := by
      have hn : ‖(c : ℂ) * m‖ ^ 2 ≤ 1 := by
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          ← Complex.normSq_eq_norm_sq]
        calc c ^ 2 * Complex.normSq m ≤ c ^ 2 * c⁻¹ :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = c := by field_simp
          _ ≤ 1 := ctr_splitS_le_one
      nlinarith [norm_nonneg ((c : ℂ) * m)]
    have hE2 : |E| ≤ 2 := hE.trans (by linarith [ctrTheta_pos k])
    have ha : ‖(c : ℂ) * conj (matchedA E)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_conj,
        ctr_norm_matchedA hE2, mul_one]
      exact ctr_splitS_le_one
    calc ‖(c : ℂ) * m - (c : ℂ) * conj (matchedA E)‖
        ≤ ‖(c : ℂ) * m‖ + ‖(c : ℂ) * conj (matchedA E)‖ := norm_sub_le _ _
      _ < cst0.ρ₀ p.b (rankMargin p α) := by
        change _ < (3 : ℝ)
        linarith

end Existence

end BlockBand.Center
