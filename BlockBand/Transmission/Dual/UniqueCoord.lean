module

public import BlockBand.Transmission.Dual.Generator
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem

/-!
# Flat coordinates for the level-`q` dual

`ofFlat q : ℝ^{q+q} →L DualCoord q` (`w ↦ (w ∘ castAdd, w ∘ natAdd)`), the flat drift
`flatDrift D₀ q = (D₀/2)(β^x, β^y)` and the diagonal diffusion
`flatDiff D₀ q = D₀ diag(x(1+x), y(1−y))`:
* `mpGenerator_flat`: `mpGenerator (flatDrift) (flatDiff) (f ∘ ofFlat) = dualGenerator D₀ f ∘ ofFlat`
  for `C²` `f` (the dual generator is the martingale-problem generator in flat coordinates);
* `flatDiff_symm`, `flatDiff_posDef` (on the chamber, `D₀ > 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ}

/-- `ℝ^{q+q} → DualCoord q`, `w ↦ (w ∘ castAdd, w ∘ natAdd)`. -/
def ofFlat (q : ℕ) : (Fin (q + q) → ℝ) →L[ℝ] DualCoord q :=
  (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd q i)).prod
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd q j))

theorem ofFlat_apply (w : Fin (q + q) → ℝ) :
    ofFlat q w = (fun i => w (Fin.castAdd q i), fun j => w (Fin.natAdd q j)) := rfl

theorem ofFlat_single_castAdd (i : Fin q) :
    ofFlat q (Pi.single (Fin.castAdd q i) 1) = dirX i := by
  ext k
  · simp [ofFlat_apply, dirX, Pi.single_apply]
  · simp [ofFlat_apply, dirX, Pi.single_apply, Fin.ext_iff]; omega

theorem ofFlat_single_natAdd (j : Fin q) :
    ofFlat q (Pi.single (Fin.natAdd q j) 1) = dirY j := by
  ext k
  · simp [ofFlat_apply, dirY, Pi.single_apply, Fin.ext_iff]; omega
  · simp [ofFlat_apply, dirY, Pi.single_apply]

/-- Flat drift `(D₀/2)(β^x, β^y)`. -/
def flatDrift (D0 : ℝ) (q : ℕ) (w : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Fin.append (fun i => D0 / 2 * dualDriftX (ofFlat q w) i)
    (fun j => D0 / 2 * dualDriftY (ofFlat q w) j)

/-- Flat diagonal diffusion `D₀ diag(x(1+x), y(1-y))`. -/
def flatDiffDiag (D0 : ℝ) (q : ℕ) (w : Fin (q + q) → ℝ) : Fin (q + q) → ℝ :=
  Fin.append (fun i => D0 * ((ofFlat q w).1 i * (1 + (ofFlat q w).1 i)))
    (fun j => D0 * ((ofFlat q w).2 j * (1 - (ofFlat q w).2 j)))

def flatDiff (D0 : ℝ) (q : ℕ) (w : Fin (q + q) → ℝ) : Matrix (Fin (q + q)) (Fin (q + q)) ℝ :=
  Matrix.diagonal (flatDiffDiag D0 q w)

theorem fderiv_fderiv_apply_eq {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f) (z v : DualCoord q) :
    fderiv ℝ (fun w => fderiv ℝ f w v) z v = fderiv ℝ (fderiv ℝ f) z v v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- **The flat generator is the dual generator.** -/
theorem mpGenerator_flat (D0 : ℝ) {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    (w : Fin (q + q) → ℝ) :
    mpGenerator (flatDrift D0 q) (flatDiff D0 q) (f ∘ ofFlat q) w =
      dualGenerator D0 f (ofFlat q w) := by
  have h1 : ∀ v, fderiv ℝ (f ∘ ofFlat q) w v = fderiv ℝ f (ofFlat q w) (ofFlat q v) := fun v => by
    rw [fderiv_comp w (hf.differentiable two_ne_zero _) (ofFlat q).differentiableAt,
      ContinuousLinearMap.fderiv]
    rfl
  have h2 : ∀ u v, fderiv ℝ (fderiv ℝ (f ∘ ofFlat q)) w u v =
      fderiv ℝ (fderiv ℝ f) (ofFlat q w) (ofFlat q u) (ofFlat q v) := fun u v => by
    have := ContinuousLinearMap.iteratedFDeriv_comp_right (ofFlat q) hf w (i := 2) le_rfl
    have e := congrArg (fun T => T ![u, v]) this
    simp only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      at e
    simpa using e
  have hcn : ∀ x y : Fin q, Fin.castAdd q x ≠ Fin.natAdd q y := fun x y h => by
    have := congrArg Fin.val h; simp at this; omega
  have hnc : ∀ x y : Fin q, Fin.natAdd q x ≠ Fin.castAdd q y := fun x y h => hcn y x h.symm
  unfold mpGenerator dualGenerator
  simp only [h1, h2, flatDiff, Matrix.diagonal_apply, Fin.sum_univ_add, ofFlat_single_castAdd,
    ofFlat_single_natAdd, flatDrift, flatDiffDiag, Fin.append_left, Fin.append_right,
    fderiv_fderiv_apply_eq hf]
  simp only [Fin.castAdd_inj, Fin.natAdd_inj, hcn, hnc, ite_false, zero_mul,
    Finset.sum_const_zero, add_zero, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  ring_nf
  simp

theorem flatDiff_symm (D0 : ℝ) (w : Fin (q + q) → ℝ) (i j : Fin (q + q)) :
    flatDiff D0 q w i j = flatDiff D0 q w j i := by
  by_cases h : i = j
  · rw [h]
  · simp [flatDiff, h, Ne.symm h]

/-- On the chamber the flat diffusion matrix is positive definite. -/
theorem flatDiff_posDef {D0 : ℝ} (hD0 : 0 < D0) {w : Fin (q + q) → ℝ}
    (hw : ofFlat q w ∈ dualChamber q) : (flatDiff D0 q w).PosDef := by
  refine Matrix.posDef_diagonal_iff.2 fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp only [flatDiffDiag, Fin.append_left]
    have h1 := hw.2.2.1 i
    exact mul_pos hD0 (mul_pos h1 (by linarith))
  · simp only [flatDiffDiag, Fin.append_right]
    have h2 := hw.2.2.2 j
    exact mul_pos hD0 (mul_pos h2.1 (by linarith [h2.2]))

end BlockBand.Transmission.Dual
