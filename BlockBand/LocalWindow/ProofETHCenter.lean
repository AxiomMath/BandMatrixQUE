module

public import BlockBand.LocalWindow.ProofETHWindow
public import BlockBand.LocalWindow.ProofBranch
public import BlockBand.LocalWindow.Statements

/-!
# Stability of the Dyson root and the ETH centre

Deterministic stability and uniqueness of the scalar Dyson root, and the comparison of the CEH
centre with the window centre, for part (ii) of the physical local-window lemma.

Setting: Hermitian `F` on a finite type `ι` (`N = |ι| > 0`), `s > 0`; a *Dyson root* at `z`
(`Im z ≥ 0`) is `m` with `Im m > 0` and `m = N⁻¹ Tr M`, `M = (F - w)⁻¹`, `w = z + s m`
(`IsDysonRoot`). With `frob X = Σ |X_ab|²`:

## Main results

* `trace_im_resolvent`: `Im Tr M = Im w · frob M`; hence `s frob M / N ≤ 1` (`s_frob_le`).
* `dyson_stability`: `Re (1 - s N⁻¹ Tr M₁M₂) ≥ (s/2)(Im m₁ + Im m₂)²` for two roots (from
  `2 Re Tr M₁M₂ = frob M₁ + frob M₂ - frob (M₁ - M₂*)` and `frob Y ≥ |Tr Y|²/N`).
* `dyson_lipschitz`: `|m₁ - m₂| (s²/2)(Im m₁ + Im m₂)² ≤ |z₁ - z₂|`; in particular the root
  is unique (`dysonRoot_unique`), so `freshDyson` (hence `pairDyson`) is the root whenever one
  exists (`freshDyson_eq_of_isDysonRoot`, `pairDyson_eq_of_isDysonRoot`; reindexing:
  `isDysonRoot_reindex`).
* `windowGamma_eq`: `Γ_E(λ) = s M₀M₀*`, `M₀ = (K - λ - s m)⁻¹`;
  `gammaMatrix_eq` (CEH centre): `Γ(M) = (Im w/Im m) MM*` for `M = (F - w)⁻¹`, `⟨M⟩ = m`.
* `centre_close`: for a root `m` at `z` (`Im z ≥ 0`), a root `m₀` at a real `x₀` and a
  contraction `J`, `|(Im w/Im m) Tr MM*J - s Tr M₀M₀*J| ≤ N (Im z/(s Im m) + 2|w - w₀|/(s Im m₀))`
  (`w = z + s m`, `w₀ = x₀ + s m₀`); with `dyson_lipschitz` this is `O(W^{-1+β})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofETH

open Matrix Finset
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-!
## Frobenius bounds
-/

/-- `frob X = Σ_{a,b} |X_ab|²`. -/
def frob (X : Matrix ι ι ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2

theorem frob_nonneg (X : Matrix ι ι ℂ) : 0 ≤ frob X := by unfold frob; positivity

theorem trace_mul_conjTranspose (X : Matrix ι ι ℂ) : (X * Xᴴ).trace = ((frob X : ℝ) : ℂ) := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, mul_comm, Complex.conj_mul']

theorem frob_conjTranspose (X : Matrix ι ι ℂ) : frob Xᴴ = frob X := by
  unfold frob
  rw [Finset.sum_comm]
  simp [Matrix.conjTranspose_apply]

/-- Trace Cauchy–Schwarz: `|Tr XY| ≤ √frob X √frob Y`. -/
theorem norm_trace_mul_le (X Y : Matrix ι ι ℂ) :
    ‖(X * Y).trace‖ ≤ Real.sqrt (frob X) * Real.sqrt (frob Y) := by
  have h1 : ‖(X * Y).trace‖ ≤ ∑ p : ι × ι, ‖X p.1 p.2‖ * ‖Y p.2 p.1‖ := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  refine h1.trans ((Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans (le_of_eq ?_))
  congr 2
  · rw [Fintype.sum_prod_type]; rfl
  · rw [Fintype.sum_prod_type, frob, Finset.sum_comm]

/-- `|Tr Y|² ≤ N frob Y`. -/
theorem norm_trace_sq_le (Y : Matrix ι ι ℂ) :
    ‖Y.trace‖ ^ 2 ≤ Fintype.card ι * frob Y := by
  have h1 : ‖Y.trace‖ ≤ ∑ a, ‖Y a a‖ := norm_sum_le _ _
  have h2 : (∑ a, ‖Y a a‖) ^ 2 ≤ Fintype.card ι * ∑ a, ‖Y a a‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun a => ‖Y a a‖)
    simpa using this
  have h3 : ∑ a, ‖Y a a‖ ^ 2 ≤ frob Y :=
    Finset.sum_le_sum fun a _ => Finset.single_le_sum (f := fun b => ‖Y a b‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ a)
  calc ‖Y.trace‖ ^ 2 ≤ (∑ a, ‖Y a a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))

/-- `frob (A X) ≤ L² frob X` if `‖A v‖² ≤ L² ‖v‖²` for every `v`. -/
theorem frob_mul_left_le {A : Matrix ι ι ℂ} {L : ℝ}
    (hA : ∀ v : ι → ℂ, sqNorm (A *ᵥ v) ≤ L ^ 2 * sqNorm v) (X : Matrix ι ι ℂ) :
    frob (A * X) ≤ L ^ 2 * frob X := by
  have hcol : ∀ b, (∑ a, ‖(A * X) a b‖ ^ 2) ≤ L ^ 2 * ∑ a, ‖X a b‖ ^ 2 := by
    intro b
    have := hA (fun c => X c b)
    simpa [sqNorm, Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  unfold frob
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖X a b‖ ^ 2), Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => hcol b

/-- `frob (X A) ≤ L² frob X` if `‖A* v‖² ≤ L² ‖v‖²` for every `v`. -/
theorem frob_mul_right_le {A : Matrix ι ι ℂ} {L : ℝ}
    (hA : ∀ v : ι → ℂ, sqNorm (Aᴴ *ᵥ v) ≤ L ^ 2 * sqNorm v) (X : Matrix ι ι ℂ) :
    frob (X * A) ≤ L ^ 2 * frob X := by
  rw [← frob_conjTranspose, conjTranspose_mul, ← frob_conjTranspose X]
  exact frob_mul_left_le hA _

/-- An `L²`-operator-norm contraction: `‖J v‖² ≤ ‖v‖²` and `‖J* v‖² ≤ ‖v‖²`. -/
theorem sqNorm_mulVec_le_of_opNorm_le {J : Matrix ι ι ℂ} (hJ : ‖J‖ ≤ 1) (v : ι → ℂ) :
    sqNorm (J *ᵥ v) ≤ 1 ^ 2 * sqNorm v := by
  have hnorm : ∀ x : ι → ℂ, ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm x) := by
    intro x; rw [EuclideanSpace.norm_eq]; rfl
  have h := Matrix.l2_opNorm_mulVec J (WithLp.toLp 2 v)
  have h' : Real.sqrt (sqNorm (J *ᵥ v)) ≤ Real.sqrt (sqNorm v) := by
    rw [← hnorm, ← hnorm]
    refine h.trans ?_
    calc ‖J‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖
        ≤ 1 * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ :=
          mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
      _ = _ := one_mul _
  rw [one_pow, one_mul]
  exact (Real.sqrt_le_sqrt_iff (sqNorm_nonneg _)).mp h'

/-!
## Resolvents
-/

/-- Resolvent identity: `X₁⁻¹ - X₂⁻¹ = X₁⁻¹ (X₂ - X₁) X₂⁻¹`. -/
theorem inv_sub_inv {X₁ X₂ : Matrix ι ι ℂ} (h₁ : X₁.det ≠ 0) (h₂ : X₂.det ≠ 0) :
    X₁⁻¹ - X₂⁻¹ = X₁⁻¹ * (X₂ - X₁) * X₂⁻¹ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr h₂),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h₁), Matrix.mul_one, Matrix.one_mul]

theorem det_resolvent_ne_zero {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    (F - w • (1 : Matrix ι ι ℂ)).det ≠ 0 :=
  BlockBand.LocalWindow.ProofCertificate.det_sub_smul_ne_zero hF hw

/-- `(F - w₁)⁻¹ - (F - w₂)⁻¹ = (w₁ - w₂)(F - w₁)⁻¹(F - w₂)⁻¹`. -/
theorem resolvent_sub {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w₁ w₂ : ℂ} (h₁ : w₁.im ≠ 0)
    (h₂ : w₂.im ≠ 0) :
    (F - w₁ • (1 : Matrix ι ι ℂ))⁻¹ - (F - w₂ • (1 : Matrix ι ι ℂ))⁻¹ =
      (w₁ - w₂) • ((F - w₁ • (1 : Matrix ι ι ℂ))⁻¹ * (F - w₂ • (1 : Matrix ι ι ℂ))⁻¹) := by
  rw [inv_sub_inv (det_resolvent_ne_zero hF h₁) (det_resolvent_ne_zero hF h₂)]
  have : F - w₂ • (1 : Matrix ι ι ℂ) - (F - w₁ • 1) = (w₁ - w₂) • (1 : Matrix ι ι ℂ) := by
    rw [sub_smul]; abel
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem resolvent_conjTranspose {F : Matrix ι ι ℂ} (hF : F.IsHermitian) (w : ℂ) :
    ((F - w • (1 : Matrix ι ι ℂ))⁻¹)ᴴ = (F - conj w • (1 : Matrix ι ι ℂ))⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, hF.eq, conjTranspose_smul,
    conjTranspose_one, Complex.star_def]

/-- `‖(F - w)⁻¹ v‖² ≤ (Im w)⁻² ‖v‖²`. -/
theorem sqNorm_resolvent_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : w.im ≠ 0)
    (v : ι → ℂ) :
    sqNorm ((F - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v) ≤ (|w.im|⁻¹) ^ 2 * sqNorm v := by
  have hnorm : ∀ x : ι → ℂ, ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = Real.sqrt (sqNorm x) := by
    intro x; rw [EuclideanSpace.norm_eq]; rfl
  have h := BlockBand.LocalWindow.ProofCertificate.norm_resolvent_le hF hw (WithLp.toLp 2 v)
  have h' : Real.sqrt (sqNorm ((F - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v)) ≤
      |w.im|⁻¹ * Real.sqrt (sqNorm v) := by
    rw [← hnorm, ← hnorm]; exact h
  have h0 := Real.sqrt_nonneg (sqNorm ((F - w • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ v))
  have := pow_le_pow_left₀ h0 h' 2
  rw [Real.sq_sqrt (sqNorm_nonneg _), mul_pow, Real.sq_sqrt (sqNorm_nonneg _)] at this
  exact this

theorem sqNorm_resolvent_conjTranspose_le {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ}
    (hw : w.im ≠ 0) (v : ι → ℂ) :
    sqNorm (((F - w • (1 : Matrix ι ι ℂ))⁻¹)ᴴ *ᵥ v) ≤ (|w.im|⁻¹) ^ 2 * sqNorm v := by
  rw [resolvent_conjTranspose hF]
  have hw' : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  have := sqNorm_resolvent_le hF hw' v
  rwa [Complex.conj_im, abs_neg] at this

/-- `Im Tr (F - w)⁻¹ = Im w · frob (F - w)⁻¹`. -/
theorem trace_im_resolvent {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    ((F - w • (1 : Matrix ι ι ℂ))⁻¹).trace.im = w.im * frob (F - w • (1 : Matrix ι ι ℂ))⁻¹ := by
  set M := (F - w • (1 : Matrix ι ι ℂ))⁻¹
  have hw' : (conj w).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr hw
  have hid : M - Mᴴ = (w - conj w) • (M * Mᴴ) := by
    rw [resolvent_conjTranspose hF w]
    exact resolvent_sub hF hw hw'
  have htr := congrArg Matrix.trace hid
  rw [trace_sub, trace_conjTranspose, trace_smul, trace_mul_conjTranspose] at htr
  have him := congrArg Complex.im htr
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, smul_eq_mul, Complex.mul_im,
    Complex.sub_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_self] at him
  linarith

/-!
## Dyson roots
-/

/-- `m` is a Dyson root at `z`: `Im m > 0` and `m = N⁻¹ Tr (F - z - s m)⁻¹`. -/
def IsDysonRoot (F : Matrix ι ι ℂ) (s : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = (Fintype.card ι : ℂ)⁻¹ * ((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹).trace

theorem dysonRoot_w_im {s : ℝ} {z m : ℂ} (hz : 0 ≤ z.im) :
    s * m.im ≤ (z + (s : ℂ) * m).im := by
  simp [Complex.mul_im]; linarith

theorem dysonRoot_w_im_pos {s : ℝ} (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hm : 0 < m.im) :
    0 < (z + (s : ℂ) * m).im :=
  (mul_pos hs hm).trans_le (dysonRoot_w_im hz)

/-- `Im m = Im w · frob M / N` at a root. -/
theorem dysonRoot_im_eq [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im) (hroot : IsDysonRoot F s z m) :
    m.im * Fintype.card ι =
      (z + (s : ℂ) * m).im * frob (F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ := by
  have hw := (dysonRoot_w_im_pos hs hz hroot.1).ne'
  rw [← trace_im_resolvent hF hw]
  have hN : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : ((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹).trace =
      (Fintype.card ι : ℂ) * m := by
    conv_rhs => rw [hroot.2]
    rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  rw [e]
  simp [Complex.mul_im, mul_comm]

/-- `s frob M ≤ N` at a root. -/
theorem s_frob_le [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {z m : ℂ} (hz : 0 ≤ z.im) (hroot : IsDysonRoot F s z m) :
    s * frob (F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ ≤ Fintype.card ι := by
  have h := dysonRoot_im_eq hF hs hz hroot
  have hw := dysonRoot_w_im (s := s) (m := m) hz
  have hf := frob_nonneg (F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm := hroot.1
  nlinarith [mul_le_mul_of_nonneg_right hw hf]

/-- **Stability of the Dyson equation**: for roots at `z₁, z₂` (`Im z_j ≥ 0`),
`Re (N - s Tr M₁M₂) ≥ (s/2) N (Im m₁ + Im m₂)²`. -/
theorem dyson_stability [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) :
    s / 2 * Fintype.card ι * (m₁.im + m₂.im) ^ 2 ≤
      Fintype.card ι - s * ((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace.re := by
  set M₁ := (F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNc : ((N : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set Y := M₁ - M₂ᴴ
  -- `frob Y = frob M₁ + frob M₂ - 2 Re Tr M₁M₂`
  have hY : frob Y = frob M₁ + frob M₂ - 2 * (M₁ * M₂).trace.re := by
    have h := trace_mul_conjTranspose Y
    have e : Y * Yᴴ = M₁ * M₁ᴴ - M₁ * M₂ - (M₁ * M₂)ᴴ + M₂ᴴ * M₂ := by
      simp only [Y, conjTranspose_sub, conjTranspose_conjTranspose, conjTranspose_mul,
        Matrix.mul_sub, Matrix.sub_mul]
      abel
    rw [e, trace_add, trace_sub, trace_sub, trace_conjTranspose, trace_mul_comm M₂ᴴ M₂,
      trace_mul_conjTranspose, trace_mul_conjTranspose] at h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.star_def,
      Complex.conj_re] at this
    linarith
  -- `frob Y ≥ N (Im m₁ + Im m₂)²`
  have htrY : Y.trace.im = N * (m₁.im + m₂.im) := by
    have e1 : M₁.trace = N * m₁ := by
      rw [h₁.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    have e2 : M₂.trace = N * m₂ := by
      rw [h₂.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    simp only [Y, trace_sub, trace_conjTranspose, e1, e2, Complex.sub_im, Complex.star_def,
      Complex.conj_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, map_mul, Complex.conj_ofReal]
    ring
  have hYlow : N * (m₁.im + m₂.im) ^ 2 ≤ frob Y := by
    have h1 := norm_trace_sq_le Y
    have h2 : |Y.trace.im| ≤ ‖Y.trace‖ := Complex.abs_im_le_norm _
    have h3 : (Y.trace.im) ^ 2 ≤ ‖Y.trace‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [htrY] at h3
    have : N ^ 2 * (m₁.im + m₂.im) ^ 2 ≤ N * frob Y := by nlinarith
    nlinarith
  have hf₁ := s_frob_le hF hs hz₁ h₁
  have hf₂ := s_frob_le hF hs hz₂ h₂
  nlinarith

/-- `|Tr M₁M₂| ≤ N/s` at two roots. -/
theorem norm_trace_mul_roots_le [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) :
    s * ‖((F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹ *
        (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤ Fintype.card ι := by
  set M₁ := (F - (z₁ + (s : ℂ) * m₁) • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F - (z₂ + (s : ℂ) * m₂) • (1 : Matrix ι ι ℂ))⁻¹
  have hf₁ := s_frob_le hF hs hz₁ h₁
  have hf₂ := s_frob_le hF hs hz₂ h₂
  have hc := norm_trace_mul_le M₁ M₂
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hsq : s * (Real.sqrt (frob M₁) * Real.sqrt (frob M₂)) ≤ Fintype.card ι := by
    have e : s * (Real.sqrt (frob M₁) * Real.sqrt (frob M₂)) =
        Real.sqrt (s * frob M₁) * Real.sqrt (s * frob M₂) := by
      rw [Real.sqrt_mul hs.le, Real.sqrt_mul hs.le]
      have := Real.mul_self_sqrt hs.le
      linear_combination (-(Real.sqrt (frob M₁) * Real.sqrt (frob M₂))) * this
    rw [e]
    calc Real.sqrt (s * frob M₁) * Real.sqrt (s * frob M₂)
        ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (Fintype.card ι) :=
          mul_le_mul (Real.sqrt_le_sqrt hf₁) (Real.sqrt_le_sqrt hf₂) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Fintype.card ι := Real.mul_self_sqrt hN
  exact (mul_le_mul_of_nonneg_left hc hs.le).trans hsq

/-- **Lipschitz bound for the Dyson root**: for roots at `z₁, z₂` (`Im z_j ≥ 0`),
`|m₁ - m₂| (s²/2)(Im m₁ + Im m₂)² ≤ |z₁ - z₂|`. -/
theorem dyson_lipschitz [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z₁ z₂ m₁ m₂ : ℂ} (hz₁ : 0 ≤ z₁.im) (hz₂ : 0 ≤ z₂.im)
    (h₁ : IsDysonRoot F s z₁ m₁) (h₂ : IsDysonRoot F s z₂ m₂) :
    ‖m₁ - m₂‖ * (s ^ 2 / 2 * (m₁.im + m₂.im) ^ 2) ≤ ‖z₁ - z₂‖ := by
  set w₁ := z₁ + (s : ℂ) * m₁
  set w₂ := z₂ + (s : ℂ) * m₂
  set M₁ := (F - w₁ • (1 : Matrix ι ι ℂ))⁻¹
  set M₂ := (F - w₂ • (1 : Matrix ι ι ℂ))⁻¹
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hNc : ((N : ℝ) : ℂ) = (Fintype.card ι : ℂ) := Complex.ofReal_natCast _
  have hNne : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw₁ := (dysonRoot_w_im_pos hs hz₁ h₁.1).ne'
  have hw₂ := (dysonRoot_w_im_pos hs hz₂ h₂.1).ne'
  set t := (M₁ * M₂).trace
  -- `N (m₁ - m₂) = (w₁ - w₂) t`
  have hdiff : (N : ℂ) * (m₁ - m₂) = (w₁ - w₂) * t := by
    have e := congrArg Matrix.trace (resolvent_sub hF hw₁ hw₂)
    rw [trace_sub, trace_smul, smul_eq_mul] at e
    have e1 : M₁.trace = N * m₁ := by
      rw [h₁.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    have e2 : M₂.trace = N * m₂ := by
      rw [h₂.2, ← mul_assoc, hNc, mul_inv_cancel₀ hNne, one_mul]
    rw [mul_sub, ← e1, ← e2]; exact e
  -- `(m₁ - m₂)(N - s t) = (z₁ - z₂) t`
  have hkey : (m₁ - m₂) * ((N : ℂ) - s * t) = (z₁ - z₂) * t := by
    have : w₁ - w₂ = (z₁ - z₂) + s * (m₁ - m₂) := by simp only [w₁, w₂]; ring
    rw [this] at hdiff
    linear_combination hdiff
  have hstab := dyson_stability hF hs hz₁ hz₂ h₁ h₂
  have ht := norm_trace_mul_roots_le hF hs hz₁ hz₂ h₁ h₂
  have hre : s / 2 * N * (m₁.im + m₂.im) ^ 2 ≤ ‖(N : ℂ) - s * t‖ := by
    refine hstab.trans (le_trans (le_of_eq ?_) (Complex.re_le_norm _))
    simp [Complex.mul_re]
    rfl
  have hnorm := congrArg norm hkey
  rw [norm_mul, norm_mul] at hnorm
  have hlhs : ‖m₁ - m₂‖ * (s / 2 * N * (m₁.im + m₂.im) ^ 2) ≤ ‖z₁ - z₂‖ * ‖t‖ := by
    rw [← hnorm]; exact mul_le_mul_of_nonneg_left hre (norm_nonneg _)
  have h2 : ‖z₁ - z₂‖ * (s * ‖t‖) ≤ ‖z₁ - z₂‖ * N :=
    mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have : ‖m₁ - m₂‖ * (s ^ 2 / 2 * (m₁.im + m₂.im) ^ 2) * N ≤ ‖z₁ - z₂‖ * N := by
    nlinarith [norm_nonneg (m₁ - m₂), norm_nonneg t, norm_nonneg (z₁ - z₂)]
  exact le_of_mul_le_mul_right this hN

/-- Uniqueness of the Dyson root at `z` (`Im z ≥ 0`). -/
theorem dysonRoot_unique [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ}
    (hs : 0 < s) {z m₁ m₂ : ℂ} (hz : 0 ≤ z.im) (h₁ : IsDysonRoot F s z m₁)
    (h₂ : IsDysonRoot F s z m₂) : m₁ = m₂ := by
  have h := dyson_lipschitz hF hs hz hz h₁ h₂
  rw [sub_self, norm_zero] at h
  have hpos : 0 < s ^ 2 / 2 * (m₁.im + m₂.im) ^ 2 := by
    have := h₁.1; have := h₂.1; positivity
  have : ‖m₁ - m₂‖ = 0 :=
    le_antisymm (by nlinarith [norm_nonneg (m₁ - m₂)]) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `IsDysonRoot` in the form of the certificate trace: `m = ⟨(F - z - s m)⁻¹⟩`. -/
theorem isDysonRoot_iff (F : Matrix ι ι ℂ) (s : ℝ) (z m : ℂ) :
    IsDysonRoot F s z m ↔
      0 < m.im ∧ m = BlockBand.Palm.certificateMatrixTrace F (z + (s : ℂ) * m) := by
  unfold IsDysonRoot BlockBand.Palm.certificateMatrixTrace
    BlockBand.Palm.certificateMatrixResolvent
  rw [div_eq_inv_mul]

/-- Dyson roots are invariant under reindexing. -/
theorem isDysonRoot_reindex {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (F : Matrix ι ι ℂ) (s : ℝ) (z m : ℂ) :
    IsDysonRoot (reindex e e F) s z m ↔ IsDysonRoot F s z m := by
  rw [isDysonRoot_iff, isDysonRoot_iff,
    BlockBand.LocalWindow.ProofCertificate.certificateMatrixTrace_reindex]

/-- **`freshDyson` is the Dyson root** whenever a root exists (`Im z ≥ 0`, `s > 0`, Hermitian
`F`, `N > 0`): `CoareaPalm.freshDyson F s z = m` (uniqueness, `dysonRoot_unique`). -/
theorem freshDyson_eq_of_isDysonRoot {N : ℕ} [NeZero N] {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im)
    (h : IsDysonRoot F s z m) :
    BlockBand.Internal.Contracts.CoareaPalm.freshDyson F s z = m := by
  have hex : ∃ m' : ℂ, 0 < m'.im ∧
      m' = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m') • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹.trace := by
    refine ⟨m, h.1, ?_⟩
    have := h.2; rwa [Fintype.card_fin] at this
  unfold BlockBand.Internal.Contracts.CoareaPalm.freshDyson
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hc := Classical.choose_spec hex
  have hroot : IsDysonRoot F s z (Classical.choose hex) := by
    refine ⟨hc.1, ?_⟩
    rw [Fintype.card_fin]; exact hc.2
  exact dysonRoot_unique hF hs hz hroot h

/-- **The pair Dyson root** (`pairDyson`, `m_E(λ)`): for Hermitian `K`
on the pair, `s > 0`, `Im z ≥ 0` and a root `m` of `K` at `z`, `pairDyson p i K s z = m`. -/
theorem pairDyson_eq_of_isDysonRoot (p : BlockBand.Parameters)
    (i : ZMod p.n) {K : BlockBand.Internal.Contracts.CoareaPalm.PairMatrix p i}
    (hK : K.IsHermitian) {s : ℝ} (hs : 0 < s) {z m : ℂ} (hz : 0 ≤ z.im)
    (h : IsDysonRoot K s z m) : BlockBand.LocalWindow.pairDyson p i K s z = m := by
  have : Nonempty (BlockBand.Internal.Contracts.CoareaPalm.PairSite p i) :=
    ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  have : NeZero (Fintype.card (BlockBand.Internal.Contracts.CoareaPalm.PairSite p i)) :=
    ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin (BlockBand.Internal.Contracts.CoareaPalm.PairSite p i)
  have hK' : (reindex e e K).IsHermitian := by
    rw [reindex_apply]; exact hK.submatrix _
  exact freshDyson_eq_of_isDysonRoot hK' hs hz ((isDysonRoot_reindex e K s z m).mpr h)

/-!
## The two centres
-/

/-- `(XᴴX)⁻¹ = X⁻¹ (X⁻¹)ᴴ`. -/
theorem inv_conjTranspose_mul_self (X : Matrix ι ι ℂ) : (Xᴴ * X)⁻¹ = X⁻¹ * (X⁻¹)ᴴ := by
  rw [Matrix.mul_inv_rev, conjTranspose_nonsing_inv]

/-- **`Γ_E(λ)` at a root**: `windowGamma p i K s λ = s M₀M₀*` with
`M₀ = (K - λ - s m)⁻¹`, `m = pairDyson p i K s λ`. -/
theorem windowGamma_eq (p : BlockBand.Parameters) (i : ZMod p.n)
    (K : BlockBand.Internal.Contracts.CoareaPalm.PairMatrix p i) (s lam : ℝ) :
    BlockBand.LocalWindow.windowGamma p i K s lam =
      (s : ℂ) • ((K - ((lam : ℂ) + (s : ℂ) * BlockBand.LocalWindow.pairDyson p i K s lam) •
          (1 : BlockBand.Internal.Contracts.CoareaPalm.PairMatrix p i))⁻¹ *
        ((K - ((lam : ℂ) + (s : ℂ) * BlockBand.LocalWindow.pairDyson p i K s lam) •
          (1 : BlockBand.Internal.Contracts.CoareaPalm.PairMatrix p i))⁻¹)ᴴ) := by
  unfold BlockBand.LocalWindow.windowGamma
  simp only
  rw [inv_conjTranspose_mul_self]

/-- `N⁻¹ Tr (Im M) = Im ⟨M⟩` (as a complex number) for the CEH matrix imaginary part. -/
theorem normalizedTrace_imaginaryPart {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    BlockBand.External.CEH.normalizedTrace (BlockBand.External.CEH.imaginaryPart M) =
      ((BlockBand.External.CEH.normalizedTrace M).im : ℂ) := by
  unfold BlockBand.External.CEH.normalizedTrace BlockBand.External.CEH.imaginaryPart
  rw [trace_smul, trace_sub, trace_conjTranspose, smul_eq_mul]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have h2 : (2 * Complex.I)⁻¹ * (M.trace - star M.trace) = ((M.trace.im : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]
    field_simp
    push_cast; ring
  rw [h2, hNr, Complex.im_ofReal_mul, Complex.ofReal_mul]

/-- **The CEH centre at a root** (the external ETH theorem, `Γ = Im M/⟨Im M⟩`): for
Hermitian `F`, `M = (F - w)⁻¹` with `⟨M⟩ = m`, `Im w ≠ 0`:
`CEH.gammaMatrix M = (Im w/Im m) M M*`. -/
theorem gammaMatrix_eq {N : ℕ} {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {w m : ℂ}
    (hw : w.im ≠ 0)
    (hm : BlockBand.External.CEH.normalizedTrace (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ = m) :
    BlockBand.External.CEH.gammaMatrix (F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ =
      ((w.im / m.im : ℝ) : ℂ) • ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *
        ((F - w • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)ᴴ) := by
  unfold BlockBand.External.CEH.gammaMatrix
  rw [normalizedTrace_imaginaryPart, hm,
    BlockBand.LocalWindow.ProofCertificate.imaginaryPart_resolvent hF hw, smul_smul]
  congr 1
  push_cast
  ring

/-- `|Tr (M M* J)| ≤ frob M` for a contraction `J` (`‖J* v‖ ≤ ‖v‖`). -/
theorem norm_trace_mul_mul_le {J : Matrix ι ι ℂ}
    (hJ : ∀ v : ι → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v) (X Y : Matrix ι ι ℂ) :
    ‖(X * Yᴴ * J).trace‖ ≤ Real.sqrt (frob X) * Real.sqrt (frob Y) := by
  rw [Matrix.mul_assoc]
  refine (norm_trace_mul_le X (Yᴴ * J)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have := frob_mul_right_le hJ Yᴴ
  rw [frob_conjTranspose, one_pow, one_mul] at this
  exact this

/-- **Centre move** (variation of the deterministic centre): let `m` be a
Dyson root of the Hermitian `F` at `z` (`Im z ≥ 0`) and `m₀` a root at the real `x₀`, with
`w = z + s m`, `w₀ = x₀ + s m₀`, `M = (F - w)⁻¹`, `M₀ = (F - w₀)⁻¹`, and `J` a contraction
(`‖J* v‖ ≤ ‖v‖`). Then
`|(Im w/Im m) Tr(MM*J) - s Tr(M₀M₀*J)| ≤ N (Im z/(s Im m) + 2|w - w₀|/(s Im m₀))`. -/
theorem centre_close [Nonempty ι] {F : Matrix ι ι ℂ} (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s)
    {z m m₀ : ℂ} {x₀ : ℝ} (hz : 0 ≤ z.im) (hroot : IsDysonRoot F s z m)
    (hroot₀ : IsDysonRoot F s (x₀ : ℂ) m₀) {J : Matrix ι ι ℂ}
    (hJ : ∀ v : ι → ℂ, sqNorm (Jᴴ *ᵥ v) ≤ 1 ^ 2 * sqNorm v) :
    ‖(((z + (s : ℂ) * m).im / m.im : ℝ) : ℂ) *
        ((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹ *
          ((F - (z + (s : ℂ) * m) • (1 : Matrix ι ι ℂ))⁻¹)ᴴ * J).trace -
      (s : ℂ) * ((F - ((x₀ : ℂ) + (s : ℂ) * m₀) • (1 : Matrix ι ι ℂ))⁻¹ *
          ((F - ((x₀ : ℂ) + (s : ℂ) * m₀) • (1 : Matrix ι ι ℂ))⁻¹)ᴴ * J).trace‖ ≤
      Fintype.card ι * (z.im / (s * m.im) +
        2 * ‖(z + (s : ℂ) * m) - ((x₀ : ℂ) + (s : ℂ) * m₀)‖ / (s * m₀.im)) := by
  set w := z + (s : ℂ) * m
  set w₀ := (x₀ : ℂ) + (s : ℂ) * m₀
  set M := (F - w • (1 : Matrix ι ι ℂ))⁻¹
  set M₀ := (F - w₀ • (1 : Matrix ι ι ℂ))⁻¹
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hm := hroot.1
  have hm₀ := hroot₀.1
  have hz₀ : 0 ≤ ((x₀ : ℂ)).im := by simp
  have hwim : w.im = z.im + s * m.im := by simp [w, Complex.mul_im]
  have hw₀im : w₀.im = s * m₀.im := by simp [w₀, Complex.mul_im]
  have hw : 0 < w.im := dysonRoot_w_im_pos hs hz hm
  have hw₀ : 0 < w₀.im := dysonRoot_w_im_pos hs hz₀ hm₀
  have hf : s * frob M ≤ N := s_frob_le hF hs hz hroot
  have hf₀ : s * frob M₀ ≤ N := s_frob_le hF hs hz₀ hroot₀
  have hfM := frob_nonneg M
  have hfM₀ := frob_nonneg M₀
  -- the coefficient
  have hcoef : w.im / m.im = s + z.im / m.im := by
    rw [hwim, add_div, mul_div_assoc, div_self hm.ne', mul_one, add_comm]
  -- `M - M₀ = (w - w₀) M M₀`
  have hdiff : M - M₀ = (w - w₀) • (M * M₀) := resolvent_sub hF hw.ne' hw₀.ne'
  have hsplit : M * Mᴴ - M₀ * M₀ᴴ = (w - w₀) • (M * M₀ * Mᴴ) +
      (star (w - w₀)) • (M₀ * (M * M₀)ᴴ) := by
    have h1 : M * Mᴴ - M₀ * M₀ᴴ = (M - M₀) * Mᴴ + M₀ * (M - M₀)ᴴ := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, conjTranspose_sub]; abel
    rw [h1, hdiff, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  -- bound of the first difference term
  have hres₀ : ∀ v : ι → ℂ, sqNorm (M₀ᴴ *ᵥ v) ≤ (|w₀.im|⁻¹) ^ 2 * sqNorm v :=
    sqNorm_resolvent_conjTranspose_le hF hw₀.ne'
  have hres₀' : ∀ v : ι → ℂ, sqNorm (M₀ᴴᴴ *ᵥ v) ≤ (|w₀.im|⁻¹) ^ 2 * sqNorm v := by
    intro v; rw [conjTranspose_conjTranspose]; exact sqNorm_resolvent_le hF hw₀.ne' v
  have hMM₀ : frob (M * M₀) ≤ (|w₀.im|⁻¹) ^ 2 * frob M := frob_mul_right_le hres₀ M
  have hM₀M : frob (M₀ * M₀ᴴ) ≤ (|w₀.im|⁻¹) ^ 2 * frob M₀ := frob_mul_right_le hres₀' M₀
  have hinv : |w₀.im|⁻¹ = (s * m₀.im)⁻¹ := by rw [abs_of_pos hw₀, hw₀im]
  have hsm₀ : 0 < s * m₀.im := mul_pos hs hm₀
  -- `√(frob X) ≤ a √(frob Y)` from `frob X ≤ a² frob Y`
  have hsq : ∀ {a x y : ℝ}, 0 ≤ a → 0 ≤ y → x ≤ a ^ 2 * y → Real.sqrt x ≤ a * Real.sqrt y := by
    intro a x y ha hy hxy
    calc Real.sqrt x ≤ Real.sqrt (a ^ 2 * y) := Real.sqrt_le_sqrt hxy
      _ = a * Real.sqrt y := by rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  have hsN : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → s * x ≤ N → s * y ≤ N →
      s * (Real.sqrt x * Real.sqrt y) ≤ N := by
    intro x y hx hy h1 h2
    have e : s * (Real.sqrt x * Real.sqrt y) = Real.sqrt (s * x) * Real.sqrt (s * y) := by
      rw [Real.sqrt_mul hs.le, Real.sqrt_mul hs.le]
      have := Real.mul_self_sqrt hs.le
      linear_combination (-(Real.sqrt x * Real.sqrt y)) * this
    rw [e]
    calc Real.sqrt (s * x) * Real.sqrt (s * y) ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN.le
  have hT1 : s * ‖(M * M₀ * Mᴴ * J).trace‖ ≤ N / (s * m₀.im) := by
    have h := norm_trace_mul_mul_le hJ (M * M₀) M
    have h2 := hsq (inv_nonneg.mpr (abs_nonneg w₀.im)) hfM hMM₀
    rw [hinv] at h2
    have h3 : s * ‖(M * M₀ * Mᴴ * J).trace‖ ≤
        (s * m₀.im)⁻¹ * (s * (Real.sqrt (frob M) * Real.sqrt (frob M))) := by
      have := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right h2
        (Real.sqrt_nonneg _))) hs.le
      linarith
    refine h3.trans ?_
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hsN hfM hfM hf hf) (inv_nonneg.mpr hsm₀.le)
  have hT2 : s * ‖(M₀ * (M * M₀)ᴴ * J).trace‖ ≤ N / (s * m₀.im) := by
    have h := norm_trace_mul_mul_le hJ M₀ (M * M₀)
    have h2 := hsq (inv_nonneg.mpr (abs_nonneg w₀.im)) hfM hMM₀
    rw [hinv] at h2
    have h3 : s * ‖(M₀ * (M * M₀)ᴴ * J).trace‖ ≤
        (s * m₀.im)⁻¹ * (s * (Real.sqrt (frob M₀) * Real.sqrt (frob M))) := by
      have := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left h2
        (Real.sqrt_nonneg _))) hs.le
      linarith
    refine h3.trans ?_
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hsN hfM₀ hfM hf₀ hf) (inv_nonneg.mpr hsm₀.le)
  have hT0 : ‖(M * Mᴴ * J).trace‖ ≤ N / s := by
    have h := norm_trace_mul_mul_le hJ M M
    rw [Real.mul_self_sqrt hfM] at h
    rw [le_div_iff₀ hs]
    calc ‖(M * Mᴴ * J).trace‖ * s ≤ frob M * s := mul_le_mul_of_nonneg_right h hs.le
      _ ≤ N := by linarith
  -- assemble
  have hexp : ((w.im / m.im : ℝ) : ℂ) * (M * Mᴴ * J).trace - (s : ℂ) * (M₀ * M₀ᴴ * J).trace =
      ((z.im / m.im : ℝ) : ℂ) * (M * Mᴴ * J).trace +
        (s : ℂ) * ((w - w₀) * (M * M₀ * Mᴴ * J).trace) +
        (s : ℂ) * (star (w - w₀) * (M₀ * (M * M₀)ᴴ * J).trace) := by
    have ht : (M * Mᴴ * J).trace - (M₀ * M₀ᴴ * J).trace =
        (w - w₀) * (M * M₀ * Mᴴ * J).trace + star (w - w₀) * (M₀ * (M * M₀)ᴴ * J).trace := by
      rw [← trace_sub, ← Matrix.sub_mul, hsplit, Matrix.add_mul, trace_add, Matrix.smul_mul,
        Matrix.smul_mul, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul]
    rw [hcoef]
    push_cast
    linear_combination (s : ℂ) * ht
  rw [hexp]
  have n1 := norm_add_le (((z.im / m.im : ℝ) : ℂ) * (M * Mᴴ * J).trace +
    (s : ℂ) * ((w - w₀) * (M * M₀ * Mᴴ * J).trace))
    ((s : ℂ) * (star (w - w₀) * (M₀ * (M * M₀)ᴴ * J).trace))
  have n2 := norm_add_le (((z.im / m.im : ℝ) : ℂ) * (M * Mᴴ * J).trace)
    ((s : ℂ) * ((w - w₀) * (M * M₀ * Mᴴ * J).trace))
  have e1 : ‖((z.im / m.im : ℝ) : ℂ) * (M * Mᴴ * J).trace‖ ≤ N * (z.im / (s * m.im)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hz hm.le)]
    calc z.im / m.im * ‖(M * Mᴴ * J).trace‖ ≤ z.im / m.im * (N / s) :=
          mul_le_mul_of_nonneg_left hT0 (div_nonneg hz hm.le)
      _ = N * (z.im / (s * m.im)) := by field_simp
  have e2 : ‖(s : ℂ) * ((w - w₀) * (M * M₀ * Mᴴ * J).trace)‖ ≤
      ‖w - w₀‖ * (N / (s * m₀.im)) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have := mul_le_mul_of_nonneg_left hT1 (norm_nonneg (w - w₀))
    linarith
  have e3 : ‖(s : ℂ) * (star (w - w₀) * (M₀ * (M * M₀)ᴴ * J).trace)‖ ≤
      ‖w - w₀‖ * (N / (s * m₀.im)) := by
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have := mul_le_mul_of_nonneg_left hT2 (norm_nonneg (w - w₀))
    linarith
  have e4 : ‖w - w₀‖ * (N / (s * m₀.im)) + ‖w - w₀‖ * (N / (s * m₀.im)) =
      N * (2 * ‖w - w₀‖ / (s * m₀.im)) := by ring
  linarith

end BlockBand.LocalWindow.ProofETH
