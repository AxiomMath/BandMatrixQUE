module

public import BlockBand.Native.CEH.Zig.Bootstrap
public import BlockBand.Native.CEH.Flow.ResolventIto
public import BlockBand.Native.CEH.Phase1.Characteristic

/-!
# CEH local law, assembly: deterministic setup

* Linear observables `X ↦ tr(K X)`: the averaged (`avgK = N⁻¹ · 1`, `obsB = N⁻¹ B`) and
  isotropic (`isoK x y = y x*`) representing matrices; real part `reTr K`, imaginary part
  `reTr (-i K)`.
* Quadratic forms of resolvents: `Im (v* R v) = Im w ‖R v‖²`, hence `|Im v* R v| = |Im w| ‖R v‖²`,
  and the column identity `⟨A B Bᴴ⟩ = N⁻¹ ∑_j (B e_j)* A (B e_j)`.
* Drift bounds `‖⟨R²⟩‖ ≤ |Im⟨R⟩| / |Im w|`, `‖v* R² v‖ ≤ |Im v* R v| / |Im w|`, … and bracket
  bounds for `(1/N) ∑_x (Re tr(K R E_x R))²` (Ward identity).
* Path observables `obsX`, `obsD`, `obsM` (`X = M + ∫ D`) along a matrix path `R : ℝ → Mat`.
* The bracket-integral comparison `∫_{(0,t]} f ≤ (β / c)(1/η_t - 1/η_0)` and the dyadic grid
  lemma `exists_grid`.

Every statement is for both half-planes (only `|Im z|`, `|Im w|` enter). Measure: Lebesgue
measure on `ℝ` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.LocalLaw

open Matrix MeasureTheory Set
open BlockBand.External.CEH BlockBand.Native.CEH.Phase1 BlockBand.Native.CEH.Flow
open BlockBand.Native.CEH.Zig BlockBand.SourceProcess.Stochastic.Dyson
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Representing matrices of the observables
-/

/-- `N⁻¹ B`: `tr(obsB B X) = ⟨X B⟩`. -/
def obsB (B : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ := (N : ℂ)⁻¹ • B

/-- `N⁻¹ · 1`: `tr(avgK X) = ⟨X⟩`. -/
def avgK (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := obsB (1 : Matrix (Fin N) (Fin N) ℂ)

/-- `y x*`: `tr(isoK x y X) = x* X y`. -/
def isoK (x y : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := vecMulVec y (star x)

theorem trace_obsB_mul (B X : Matrix (Fin N) (Fin N) ℂ) :
    trace (obsB B * X) = normalizedTrace (X * B) := by
  rw [obsB, Matrix.smul_mul, trace_smul, smul_eq_mul, trace_mul_comm]; rfl

theorem trace_avgK_mul (X : Matrix (Fin N) (Fin N) ℂ) :
    trace (avgK N * X) = normalizedTrace X := by
  rw [avgK, trace_obsB_mul, Matrix.mul_one]

theorem trace_isoK_mul (x y : Fin N → ℂ) (X : Matrix (Fin N) (Fin N) ℂ) :
    trace (isoK x y * X) = sourceMatrixElement X x y :=
  trace_vecMulVec_mul x y X

theorem reTr_eq_re_trace (K X : Matrix (Fin N) (Fin N) ℂ) : reTr K X = (trace (K * X)).re := rfl

theorem reTr_negI_smul (K X : Matrix (Fin N) (Fin N) ℂ) :
    reTr ((-Complex.I) • K) X = (trace (K * X)).im := by
  rw [reTr, Matrix.smul_mul, trace_smul, smul_eq_mul]
  simp [Complex.mul_re]

/-!
## Quadratic forms
-/

theorem sourceMatrixElement_sub (A B : Matrix (Fin N) (Fin N) ℂ) (x y : Fin N → ℂ) :
    sourceMatrixElement (A - B) x y = sourceMatrixElement A x y - sourceMatrixElement B x y := by
  simp [sourceMatrixElement, sub_mulVec, dotProduct_sub]

theorem sourceMatrixElement_conjTranspose (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    sourceMatrixElement Aᴴ v v = conj (sourceMatrixElement A v v) := by
  rw [sourceMatrixElement_eq_adjoint, conjTranspose_conjTranspose, sourceMatrixElement,
    Matrix.star_dotProduct]
  rfl

/-- `Re (v* (Im A) v) = Im (v* A v)`. -/
theorem re_sourceMatrixElement_imaginaryPart (A : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    (sourceMatrixElement (imaginaryPart A) v v).re = (sourceMatrixElement A v v).im := by
  have h : sourceMatrixElement (imaginaryPart A) v v =
      (2 * Complex.I)⁻¹ * (sourceMatrixElement A v v - conj (sourceMatrixElement A v v)) := by
    rw [External.CEH.imaginaryPart, sourceMatrixElement_smul, sourceMatrixElement_sub,
      sourceMatrixElement_conjTranspose]
  rw [h, Complex.sub_conj]
  have : (2 * Complex.I)⁻¹ * (((2 * (sourceMatrixElement A v v).im : ℝ) : ℂ) * Complex.I) =
      ((sourceMatrixElement A v v).im : ℂ) := by
    push_cast
    field_simp
  rw [this, Complex.ofReal_re]

section Resolvent

variable {H : Matrix (Fin N) (Fin N) ℂ} {w : ℂ}

/-- `Im (v* R v) = Im w ‖R v‖²`. -/
theorem im_sourceMatrixElement_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (v : Fin N → ℂ) :
    (sourceMatrixElement (Phase1.resolvent H w) v v).im =
      w.im * sourceVectorNorm (Phase1.resolvent H w *ᵥ v) ^ 2 := by
  rw [← re_sourceMatrixElement_imaginaryPart, re_sourceMatrixElement_imaginaryPart_resolvent hH hw]

/-- `|Im (v* R v)| = |Im w| ‖R v‖²`. -/
theorem abs_im_sourceMatrixElement_resolvent (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (v : Fin N → ℂ) :
    |(sourceMatrixElement (Phase1.resolvent H w) v v).im| =
      |w.im| * sourceVectorNorm (Phase1.resolvent H w *ᵥ v) ^ 2 := by
  rw [im_sourceMatrixElement_resolvent hH hw, abs_mul, abs_of_nonneg (sq_nonneg (sourceVectorNorm _))]

/-- `‖R v‖² = |Im v* R v| / |Im w|`. -/
theorem sourceVectorNorm_resolvent_sq_eq (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (v : Fin N → ℂ) :
    sourceVectorNorm (Phase1.resolvent H w *ᵥ v) ^ 2 =
      |(sourceMatrixElement (Phase1.resolvent H w) v v).im| / |w.im| := by
  rw [abs_im_sourceMatrixElement_resolvent hH hw]
  field_simp [abs_pos.mpr hw]

/-- `‖Rᴴ v‖² = |Im v* R v| / |Im w|`. -/
theorem sourceVectorNorm_resolvent_conjTranspose_sq_eq (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (v : Fin N → ℂ) :
    sourceVectorNorm ((Phase1.resolvent H w)ᴴ *ᵥ v) ^ 2 =
      |(sourceMatrixElement (Phase1.resolvent H w) v v).im| / |w.im| := by
  rw [sourceVectorNorm_resolvent_conjTranspose_mulVec_sq hH hw,
    re_sourceMatrixElement_imaginaryPart]

/-- A nonzero vector has `‖R v‖ > 0`. -/
theorem sourceVectorNorm_resolvent_pos (hH : H.IsHermitian) (hw : w.im ≠ 0) {v : Fin N → ℂ}
    (hv : v ≠ 0) : 0 < sourceVectorNorm (Phase1.resolvent H w *ᵥ v) := by
  refine lt_of_le_of_ne (sourceVectorNorm_nonneg _) fun h => hv ?_
  have h0 : Phase1.resolvent H w *ᵥ v = 0 := (sourceVectorNorm_eq_zero_iff _).1 h.symm
  have := congrArg (fun u => (H - w • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ u) h0
  simp only [mulVec_mulVec, sub_smul_mul_resolvent hH hw, one_mulVec, mulVec_zero] at this
  exact this

/-- A nonzero vector has `|Im (v* R v)| > 0`. -/
theorem abs_im_sourceMatrixElement_resolvent_pos (hH : H.IsHermitian) (hw : w.im ≠ 0)
    {v : Fin N → ℂ} (hv : v ≠ 0) : 0 < |(sourceMatrixElement (Phase1.resolvent H w) v v).im| := by
  rw [abs_im_sourceMatrixElement_resolvent hH hw]
  have := sourceVectorNorm_resolvent_pos hH hw hv
  have := abs_pos.mpr hw
  positivity

/-- `|Re ⟨Im R⟩| = |Im ⟨R⟩|`. -/
theorem abs_re_normalizedTrace_imaginaryPart (A : Matrix (Fin N) (Fin N) ℂ) :
    |(normalizedTrace (imaginaryPart A)).re| = |(normalizedTrace A).im| := by
  rw [normalizedTrace_imaginaryPart, Complex.ofReal_re]

/-- **Averaged drift factor:** `‖⟨R²⟩‖ ≤ |Im ⟨R⟩| / |Im w|`. -/
theorem norm_normalizedTrace_resolvent_sq_le' (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    ‖normalizedTrace (Phase1.resolvent H w * Phase1.resolvent H w)‖ ≤
      |(normalizedTrace (Phase1.resolvent H w)).im| / |w.im| := by
  rw [← abs_re_normalizedTrace_imaginaryPart]
  exact norm_normalizedTrace_resolvent_sq_le hH hw

/-- **Isotropic drift factor:** `‖x* R² y‖ ≤ √|Im x* R x| √|Im y* R y| / |Im w|`. -/
theorem norm_sourceMatrixElement_resolvent_sq_le (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (x y : Fin N → ℂ) :
    ‖sourceMatrixElement (Phase1.resolvent H w * Phase1.resolvent H w) x y‖ ≤
      Real.sqrt |(sourceMatrixElement (Phase1.resolvent H w) x x).im| *
        Real.sqrt |(sourceMatrixElement (Phase1.resolvent H w) y y).im| / |w.im| := by
  have h := norm_sourceMatrixElement_resolvent_mul_resolvent_le hH hw x y
  rw [re_sourceMatrixElement_imaginaryPart, re_sourceMatrixElement_imaginaryPart] at h
  rw [div_eq_inv_mul, ← mul_assoc]
  exact h

/-- Diagonal case: `‖v* R² v‖ ≤ |Im v* R v| / |Im w|`. -/
theorem norm_sourceMatrixElement_resolvent_sq_self_le (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (v : Fin N → ℂ) :
    ‖sourceMatrixElement (Phase1.resolvent H w * Phase1.resolvent H w) v v‖ ≤
      |(sourceMatrixElement (Phase1.resolvent H w) v v).im| / |w.im| := by
  have h := norm_sourceMatrixElement_resolvent_sq_le hH hw v v
  rwa [Real.mul_self_sqrt (abs_nonneg _)] at h

end Resolvent

/-!
## Columns
-/

/-- The `j`-th column `B e_j`. -/
def col (B : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) : Fin N → ℂ := fun i => B i j

/-- `⟨A B Bᴴ⟩ = N⁻¹ ∑_j (B e_j)* A (B e_j)`. -/
theorem normalizedTrace_mul_mul_conjTranspose (A B : Matrix (Fin N) (Fin N) ℂ) :
    normalizedTrace (A * B * Bᴴ) = (N : ℂ)⁻¹ * ∑ j, sourceMatrixElement A (col B j) (col B j) := by
  rw [normalizedTrace]
  congr 1
  simp only [trace, diag, mul_apply, conjTranspose_apply, sourceMatrixElement, dotProduct,
    mulVec, col, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

section ResolventColumns

variable {H : Matrix (Fin N) (Fin N) ℂ} {w : ℂ}

/-- `|Re ⟨Im R B Bᴴ⟩| = N⁻¹ ∑_j |Im (B e_j)* R (B e_j)|` for a resolvent `R`. -/
theorem abs_re_normalizedTrace_imaginaryPart_resolvent_mul (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    |(normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w) * B * Bᴴ)).re| =
      (N : ℝ)⁻¹ * ∑ j, |(sourceMatrixElement (Phase1.resolvent H w) (col B j) (col B j)).im| := by
  rw [normalizedTrace_mul_mul_conjTranspose, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    Complex.re_ofReal_mul, Complex.re_sum]
  simp only [re_sourceMatrixElement_imaginaryPart, im_sourceMatrixElement_resolvent hH hw]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg N)), ← Finset.mul_sum, abs_mul,
    abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      sq_nonneg (sourceVectorNorm (Phase1.resolvent H w *ᵥ col B j))), Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_mul, abs_of_nonneg (sq_nonneg (sourceVectorNorm (Phase1.resolvent H w *ᵥ col B j)))]

end ResolventColumns

/-!
## Bracket densities
-/

/-- Bracket density `(1/N) ∑_x (Re tr(K R E_x R))²` of `Re tr(K R)` along a path. -/
def brk (K : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) : ℝ :=
  1 / (N : ℝ) * ∑ x, reTr K (R r * hermBasis x * R r) ^ 2

theorem brk_nonneg (K : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    0 ≤ brk K R r :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem brk_obsB_le (B : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    brk (obsB B) R r ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R r * B * R r) * (R r * B * R r)ᴴ)).re := by
  unfold brk obsB
  simp only [reTr_avgRe]
  exact avgRe_bracket_le (R r) B

theorem brk_negI_obsB_le (B : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (r : ℝ) :
    brk ((-Complex.I) • obsB B) R r ≤
      1 / (N : ℝ) ^ 2 * (normalizedTrace ((R r * B * R r) * (R r * B * R r)ᴴ)).re := by
  unfold brk obsB
  rw [smul_smul]
  simp only [reTr_avgIm]
  exact avgIm_bracket_le (R r) B

theorem brk_isoK_le (x y : Fin N → ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    brk (isoK x y) R r ≤ 1 / (N : ℝ) *
      ((star x ⬝ᵥ ((R r * (R r)ᴴ) *ᵥ x)).re * (star y ⬝ᵥ (((R r)ᴴ * R r) *ᵥ y)).re) := by
  unfold brk isoK
  simp only [reTr_isoRe]
  exact isoRe_bracket_le (R r) x y

theorem brk_negI_isoK_le (x y : Fin N → ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (r : ℝ) :
    brk ((-Complex.I) • isoK x y) R r ≤ 1 / (N : ℝ) *
      ((star x ⬝ᵥ ((R r * (R r)ᴴ) *ᵥ x)).re * (star y ⬝ᵥ (((R r)ᴴ * R r) *ᵥ y)).re) := by
  unfold brk isoK
  simp only [reTr_isoIm]
  exact isoIm_bracket_le (R r) x y

section ResolventBrackets

variable {H : Matrix (Fin N) (Fin N) ℂ} {w : ℂ}

/-- Isotropic bracket factor: `Re x* R Rᴴ x · Re y* Rᴴ R y = |Im x* R x| |Im y* R y| / |Im w|²`. -/
theorem iso_bracket_factor_eq (hH : H.IsHermitian) (hw : w.im ≠ 0) (x y : Fin N → ℂ) :
    (star x ⬝ᵥ ((Phase1.resolvent H w * (Phase1.resolvent H w)ᴴ) *ᵥ x)).re *
        (star y ⬝ᵥ (((Phase1.resolvent H w)ᴴ * Phase1.resolvent H w) *ᵥ y)).re =
      |(sourceMatrixElement (Phase1.resolvent H w) x x).im| *
        |(sourceMatrixElement (Phase1.resolvent H w) y y).im| / |w.im| ^ 2 := by
  have h1 := sourceMatrixElement_mul_conjTranspose_self (Phase1.resolvent H w) x
  have h2 := sourceMatrixElement_conjTranspose_mul_self (Phase1.resolvent H w) y
  simp only [sourceMatrixElement] at h1 h2
  rw [h1, h2, Complex.ofReal_re, Complex.ofReal_re,
    sourceVectorNorm_resolvent_conjTranspose_sq_eq hH hw, sourceVectorNorm_resolvent_sq_eq hH hw]
  ring

/-- Averaged (`B = 1`) bracket factor: `Re ⟨R² (R²)ᴴ⟩ ≤ |Im ⟨R⟩| / |Im w|³`. -/
theorem avg_bracket_factor_le (hH : H.IsHermitian) (hw : w.im ≠ 0) :
    (normalizedTrace ((Phase1.resolvent H w * 1 * Phase1.resolvent H w) *
      (Phase1.resolvent H w * 1 * Phase1.resolvent H w)ᴴ)).re ≤
      |(normalizedTrace (Phase1.resolvent H w)).im| / |w.im| ^ 3 := by
  rw [Matrix.mul_one, ← abs_re_normalizedTrace_imaginaryPart]
  exact re_normalizedTrace_resolvent_sq_mul_conjTranspose_le hH hw

/-- General-`B` bracket factor: `Re ⟨(R B R)(R B R)ᴴ⟩ ≤ |Re ⟨Im R B Bᴴ⟩| / |Im w|³`. -/
theorem obsB_bracket_factor_le (hH : H.IsHermitian) (hw : w.im ≠ 0)
    (B : Matrix (Fin N) (Fin N) ℂ) :
    (normalizedTrace ((Phase1.resolvent H w * B * Phase1.resolvent H w) *
      (Phase1.resolvent H w * B * Phase1.resolvent H w)ᴴ)).re ≤
      |(normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w) * B * Bᴴ)).re| / |w.im| ^ 3 := by
  set R := Phase1.resolvent H w with hRdef
  have hpos : 0 < |w.im| := abs_pos.mpr hw
  -- peel the right factor `R`: `tr((X R)(X R)ᴴ) ≤ ‖Rᴴ‖² tr(X Xᴴ)` with `X = R B`
  have hA : ∀ v, sourceVectorNorm (Rᴴ *ᵥ v) ≤ |w.im|⁻¹ * sourceVectorNorm v :=
    sourceVectorNorm_resolvent_conjTranspose_mulVec_le hH hw
  have hpeel := re_trace_conjTranspose_mul_self_mul_le Rᴴ (R * B)ᴴ hA
  have e1 : (Rᴴ * (R * B)ᴴ)ᴴ * (Rᴴ * (R * B)ᴴ) = (R * B * R) * (R * B * R)ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have e2 : ((R * B)ᴴ)ᴴ * (R * B)ᴴ = (R * B) * (R * B)ᴴ := by rw [conjTranspose_conjTranspose]
  rw [e1, e2] at hpeel
  have e3 : normalizedTrace ((R * B) * (R * B)ᴴ) = (w.im : ℂ)⁻¹ *
      normalizedTrace (External.CEH.imaginaryPart R * B * Bᴴ) := by
    rw [normalizedTrace_mul_comm, normalizedTrace_conjTranspose_resolvent_mul_self hH hw]
  have e4 : (normalizedTrace ((R * B) * (R * B)ᴴ)).re =
      |(normalizedTrace (External.CEH.imaginaryPart R * B * Bᴴ)).re| / |w.im| := by
    rw [e3, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    have h0 := re_normalizedTrace_imaginaryPart_resolvent_mul_div_nonneg hH hw B
    rw [← hRdef] at h0
    rw [← abs_div, abs_of_nonneg h0, div_eq_inv_mul]
  have hre : ∀ X : Matrix (Fin N) (Fin N) ℂ, (normalizedTrace X).re = (N : ℝ)⁻¹ * (X.trace).re :=
    re_normalizedTrace
  have hpeel' : (normalizedTrace ((R * B * R) * (R * B * R)ᴴ)).re ≤
      |w.im|⁻¹ ^ 2 * (normalizedTrace ((R * B) * (R * B)ᴴ)).re := by
    rw [hre, hre]
    calc (N : ℝ)⁻¹ * ((R * B * R) * (R * B * R)ᴴ).trace.re
        ≤ (N : ℝ)⁻¹ * (|w.im|⁻¹ ^ 2 * ((R * B) * (R * B)ᴴ).trace.re) :=
          mul_le_mul_of_nonneg_left hpeel (by positivity)
      _ = _ := by ring
  calc _ ≤ |w.im|⁻¹ ^ 2 * (normalizedTrace ((R * B) * (R * B)ᴴ)).re := hpeel'
    _ = _ := by
        rw [e4]
        field_simp

end ResolventBrackets

/-!
## Path observables
-/

/-- `X_K(t) = tr(K (R_t - M))`. -/
def obsX (K Mz : Matrix (Fin N) (Fin N) ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : ℂ :=
  trace (K * (R t - Mz))

/-- Drift `D_K(t) = (⟨R_t⟩ - m) tr(K R_t²)`. -/
def obsD (K : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ) (t : ℝ) : ℂ :=
  (normalizedTrace (R t) - m) * trace (K * (R t * R t))

/-- Martingale part `M_K(t) = X_K(t) - ∫_0^t D_K`. -/
def obsM (K Mz : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) : ℂ :=
  obsX K Mz R t - ∫ r in (0 : ℝ)..t, obsD K m R r

theorem obsX_eq (K Mz : Matrix (Fin N) (Fin N) ℂ) (m : ℂ) (R : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (t : ℝ) : obsX K Mz R t = obsM K Mz m R t + ∫ r in (0 : ℝ)..t, obsD K m R r := by
  rw [obsM, sub_add_cancel]

/-!
## Elementary real facts
-/

/-- `|a + λ b| = |a| + λ |b|` when `a b ≥ 0`, `λ ≥ 0`. -/
theorem abs_add_mul_of_mul_nonneg {a b l : ℝ} (hab : 0 ≤ a * b) (hl : 0 ≤ l) :
    |a + l * b| = |a| + l * |b| := by
  rcases le_total 0 a with ha | ha
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0; simp [abs_mul, abs_of_nonneg hl]
    · have hb : 0 ≤ b := by
        by_contra h; push Not at h; nlinarith
      rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (by positivity)]
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · subst ha0; simp [abs_mul, abs_of_nonneg hl]
    · have hb : b ≤ 0 := by
        by_contra h; push Not at h; nlinarith
      rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonpos (by nlinarith)]
      ring

/-- **Dyadic grid.** If `0 < H`, `h ≤ H` and `H ≤ 2^L h`, some `k ≤ L` has
`H / 2^k ≤ h ≤ 2 (H / 2^k)`. -/
theorem exists_grid {H h : ℝ} {L : ℕ} (hH : 0 < H) (hh : h ≤ H) (hL : H ≤ 2 ^ L * h) :
    ∃ k ≤ L, H / 2 ^ k ≤ h ∧ h ≤ 2 * (H / 2 ^ k) := by
  have hex : ∃ k, H / 2 ^ k ≤ h := ⟨L, by
    rw [div_le_iff₀ (by positivity)]; linarith⟩
  classical
  set k := Nat.find hex with hk
  have hkspec : H / 2 ^ k ≤ h := Nat.find_spec hex
  have hkL : k ≤ L := Nat.find_min' hex (by rw [div_le_iff₀ (by positivity)]; linarith)
  refine ⟨k, hkL, hkspec, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, div_one]; linarith
  · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hjlt : j < k := by omega
    have hnot : ¬ H / 2 ^ j ≤ h := Nat.find_min hex hjlt
    push Not at hnot
    have : 2 * (H / 2 ^ k) = H / 2 ^ j := by
      rw [hj, pow_succ]; field_simp
    linarith

/-!
## Bracket integrals along the height
-/

/-- If `0 ≤ f ≤ β / η_r²` on `(0, t)`, then `∫_{(0,t]} f ≤ (β / c)(1/η_t - 1/η_0)`. -/
theorem setIntegral_Ioc_le_of_le {η c s β t : ℝ} {f : ℝ → ℝ} (hη : 0 < η) (hc : 0 < c)
    (ht : 0 ≤ t) (hts : t ≤ s) (hf0 : ∀ r ∈ Ioo 0 t, 0 ≤ f r)
    (hfg : ∀ r ∈ Ioo 0 t, f r ≤ β / zigHeight η c s r ^ 2) :
    ∫ r in Ioc 0 t, f r ≤ β / c * (1 / zigHeight η c s t - 1 / zigHeight η c s 0) := by
  have hpos : ∀ r ∈ Icc (0 : ℝ) t, zigHeight η c s r ^ 2 ≠ 0 := fun r hr =>
    pow_ne_zero 2 (zigHeight_pos hη hc.le (hr.2.trans hts)).ne'
  have hgc : ContinuousOn (fun r => β / zigHeight η c s r ^ 2) (Icc 0 t) :=
    continuousOn_const.div (continuous_zigHeight.continuousOn.pow 2) hpos
  have hgi : IntegrableOn (fun r => β / zigHeight η c s r ^ 2) (Ioo 0 t) :=
    (hgc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [integral_Ioc_eq_integral_Ioo]
  calc ∫ r in Ioo 0 t, f r ≤ ∫ r in Ioo 0 t, β / zigHeight η c s r ^ 2 :=
        integral_mono_of_nonneg ((ae_restrict_mem measurableSet_Ioo).mono hf0) hgi
          ((ae_restrict_mem measurableSet_Ioo).mono hfg)
    _ = ∫ r in (0 : ℝ)..t, β / zigHeight η c s r ^ 2 := by
        rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
    _ = _ := integral_const_div_zigHeight_sq hη hc β (ht.trans hts) hts

end BlockBand.Native.CEH.LocalLaw
