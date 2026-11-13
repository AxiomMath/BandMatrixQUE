module

public import BlockBand.SourceProcess.CoupledFrames.FrameAlg

/-!
# Frame algebra, continued

* `mul_bornL`: `A L_t = A Lcur + Σ_k 1{θ_k ≤ t} birthMat (col_k) (A pv_k)`.
* `sum_reIm`: `Σ_y Σ_r reIm_r(a_y) F (c_r e_y) = F a`, `c_0 = 1`, `c_1 = i`.
* `sourceDiffusion_mul`, `sourceDrift_mul`.
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

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} {Ω : Type*}

omit [Fintype π] in
theorem mul_bornL (A : Matrix (Amb K R) (ExtCol K R) ℂ) (σ : π → Ω → ℝ)
    (pv : π → Ω → ExtCol K R → ℂ) (eπ : π ≃ Fin n) (t : ℝ≥0) (ω : Ω) :
    A * bornL (mθ K σ) (glam K R pv) t ω = A * lcur K R π + ∑ k : Fin n,
      if (σ (eπ.symm k) ω).toNNReal ≤ t then
        birthMat (Sum.inr (eπ.symm k)) (A *ᵥ pv (eπ.symm k) ω) else 0 := by
  ext r y
  rw [Matrix.add_apply, Matrix.sum_apply]
  rcases y with k | i
  · have h1 : ∀ x : Fin n, (if (σ (eπ.symm x) ω).toNNReal ≤ t then
        birthMat (Sum.inr (eπ.symm x)) (A *ᵥ pv (eπ.symm x) ω) else 0) r (Sum.inl k) = 0 := by
      intro x; split_ifs <;> simp [birthMat]
    simp only [h1, Finset.sum_const_zero, add_zero, Matrix.mul_apply, bornL, mθ, glam, zero_le,
      ↓reduceIte, lcur, mul_ite, mul_one, mul_zero, Pi.single_apply]
  · have h0 : (A * lcur K R π) r (Sum.inr i) = 0 := by simp [Matrix.mul_apply, lcur]
    rw [h0, zero_add, Finset.sum_eq_single (eπ i) (fun x _ hx => ?_) (by simp)]
    · simp only [Equiv.symm_apply_apply, Matrix.mul_apply, bornL, mθ, glam]
      split_ifs with h
      · simp [h, birthMat, mulVec, dotProduct, Fintype.sum_sum_type]
      · simp [h]
    · have hne : Sum.inr i ≠ (Sum.inr (eπ.symm x) : SrcCol K π) := fun e => hx (by
        rw [Sum.inr.injEq] at e; rw [e, Equiv.apply_symm_apply])
      split_ifs <;> simp [birthMat, hne]

/-- Real and imaginary parts. -/
def reIm (r : Fin 2) (z : ℂ) : ℝ := if r = 0 then z.re else z.im

/-- `1` and `i`. -/
def cr (r : Fin 2) : ℂ := if r = 0 then 1 else Complex.I

theorem sum_reIm {ι c' : Type*} [Fintype c'] [DecidableEq c'] (F : Matrix ι c' ℂ) (a : c' → ℂ) :
    ∑ y, ∑ r : Fin 2, reIm r (a y) • (F *ᵥ (cr r • Pi.single y 1)) = F *ᵥ a := by
  have ha : a = ∑ y, a y • Pi.single y (1 : ℂ) := by
    funext x; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [ha, mulVec_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.sum_univ_two]
  simp only [reIm, cr, ↓reduceIte, one_smul, one_ne_zero, mulVec_smul]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im (a y)]
  ring

theorem sourceDiffusion_mul {ι c c₂ : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]
    [Fintype c₂] (D0 : ℝ) (P : Matrix ι ι ℂ) (Y : Matrix ι c ℂ) (L : Matrix c c₂ ℂ)
    (D : Matrix c₂ c₂ ℂ) (D' : Matrix c c ℂ) (hL : L * D * Lᴴ = D') (a : SourceNoise ι) :
    sourceDiffusion D0 P D a (Y * L) = sourceDiffusion D0 P D' a Y * L := by
  unfold sourceDiffusion
  rw [gramProjection_mul P Y L D D' hL, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

theorem sourceDrift_mul {ι c c₂ : Type*} [Fintype ι] [Fintype c] (D0 : ℝ) (N : ℕ)
    (P : Matrix ι ι ℂ) (Y : Matrix ι c ℂ) (L : Matrix c c₂ ℂ) :
    sourceDrift D0 N P (Y * L) = sourceDrift D0 N P Y * L := by
  unfold sourceDrift
  rw [Matrix.smul_mul, Matrix.mul_assoc]

end BlockBand.SourceProcess.CoupledFrames
