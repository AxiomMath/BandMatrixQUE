module

public import BlockBand.SourceProcess.CoupledFrames.ProbeInit
public import BlockBand.SourceProcess.CutoffLimit.Pin
public import BlockBand.SourceProcess.RankFree.BirthAlgebra
public import BlockBand.SourceProcess.ModelExist.AmbientTwo

/-!
# Frame algebra for the coupled cutoff frames

* `embK`: the isometric embedding of the canonical mode space (`embK_isometry`);
  `extFrame_mul_lcur`: `[initialFrame | 1] · Lcur = embK · initialFrame` (the hypothesis's `cutFrame`);
  `twoProjection_cutFrame`, `lcur_sig`.

Proved in the sibling module:

* `mul_bornL`: `A L_t = A Lcur + Σ_k 1{θ_k ≤ t} (A pv_k) e_{col_k}ᵀ` (births indexed by `Fin n`).
* `sum_reIm`: `Σ_y Σ_r reIm_r(a_y) F (c_r e_y) = F a` (real decomposition of complex weights).
* `sourceDiffusion_mul`, `sourceDrift_mul`: the source coefficients commute with right
  multiplication by `L` when `L 𝖣 Lᴴ = 𝖣'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.ModelExist BlockBand.SourceProcess.RankFree
open scoped NNReal ComplexConjugate

variable (K R : ℕ) (π : Type*) [Fintype π] [DecidableEq π]

/-- The current columns of the target frame inside the extended columns. -/
def lcur : Matrix (ExtCol K R) (SrcCol K π) ℂ := fun x y => match y with
  | Sum.inl k => if x = Sum.inl k then 1 else 0
  | Sum.inr _ => 0

/-- The embedding of the canonical mode space. -/
def embK : Matrix (Amb K R) (Fin K × Fin 2) ℂ := fun r x => if r = Sum.inl x then 1 else 0

theorem embK_isometry : (embK K R)ᴴ * embK K R = 1 := by
  ext x x'
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [embK, conjTranspose_apply, Sum.inl.injEq, reduceCtorEq, ↓reduceIte, star_zero,
    mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
  by_cases h : x = x' <;> simp [h]

omit [Fintype π] [DecidableEq π] in
theorem extFrame_mul_lcur (t : ℕ → ℝ) (h : ℝ) :
    extFrame K R t h * lcur K R π = embK K R * initialFrame K π t h := by
  ext r y
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases y with k | i
  · rw [Finset.sum_eq_single k (fun b _ hb => by simp [lcur, hb]) (by simp)]
    simp only [lcur, ↓reduceIte, mul_one, reduceCtorEq, mul_zero, Finset.sum_const_zero, add_zero]
    rcases r with x | j
    · rw [Finset.sum_eq_single x (fun b _ hb => by simp [embK, Ne.symm hb]) (by simp)]
      simp [embK, extFrame, curFrame_eq_initialFrame (π := π)]
    · simp [embK, extFrame]
  · simp [lcur, initialFrame]

theorem lcur_sig : lcur K R π * srcSignature K π * (lcur K R π)ᴴ = extSig K R := by
  ext x x'
  have hD : ∀ (A : Matrix (ExtCol K R) (SrcCol K π) ℂ) r y, (A * srcSignature K π) r y =
      A r y * (match y with | Sum.inl (_, σ) => if σ = 0 then (1 : ℂ) else -1 | Sum.inr _ => 0) :=
    fun A r y => by rw [srcSignature, Matrix.mul_diagonal]; rfl
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hD]
  simp only [conjTranspose_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, lcur]
  rcases x with y | r <;> rcases x' with y' | r'
  · rw [Finset.sum_eq_single y (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    by_cases hy : y = y'
    · subst hy; simp [extSig]
    · simp only [extSig, hy, diagonal_apply, Sum.inl.injEq, ↓reduceIte]
      simp only [Ne.symm hy, ↓reduceIte, star_zero, mul_zero]
  · simp [extSig]
  · simp [extSig]
  · simp [extSig, diagonal_apply]

theorem gramProjection_mul {ι c c₂ : Type*} [Fintype c] [Fintype c₂] (P : Matrix ι ι ℂ)
    (Y : Matrix ι c ℂ) (L : Matrix c c₂ ℂ) (D : Matrix c₂ c₂ ℂ) (D' : Matrix c c ℂ)
    (hL : L * D * Lᴴ = D') : gramProjection P (Y * L) D = gramProjection P Y D' := by
  simp only [gramProjection, conjTranspose_mul, ← hL, Matrix.mul_assoc]

theorem twoProjection_cutFrame {t : ℕ → ℝ} (ht : ∀ k, 0 ≤ t k ∧ t k ≤ 1) (h : ℝ) :
    TwoProjection (ambP K R) (srcSignature K π) (embK K R * initialFrame K π t h) := by
  rw [← extFrame_mul_lcur, TwoProjection, gramProjection_mul _ _ _ _ _ (lcur_sig K R π)]
  exact twoProjection_extFrame K R ht h

end BlockBand.SourceProcess.CoupledFrames
