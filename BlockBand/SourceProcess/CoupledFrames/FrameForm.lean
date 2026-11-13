module

public import BlockBand.SourceProcess.CoupledFrames.FrameNative
public import BlockBand.SourceProcess.CoupledFrames.BirthProg

/-!
# Closed forms of the born frame and of its coefficients

* `frameN_eq'`: `N_t = Y_t Lc + Σ_k birthMat (col k) ((Y_t − Y_{t∧τ_k}) a_k)`.
* `frameNc_eq'`: `Nc_t = f_t Lc + Σ_k 1{τ_k < t} birthMat (col k) (f_t a_k)`.
* `frameN_add_jump`: where `Y_{τ_k} a_k = w_k`,
  `N_t + J_b(t) = Y_t Lc + Σ_k 1{τ_k ≤ t} birthMat (col k) (Y_t a_k)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.RankFree
open BlockBand.SourceProcess.Stochastic.Semimartingale

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c' c : Type*} [Fintype ι] [Fintype c'] [DecidableEq c'] [Fintype c] [DecidableEq c]
variable {Ω : Type*} {n : ℕ}

omit [Fintype c] in
theorem frameN_eq' (Y : ℝ≥0 → Ω → Matrix ι c' ℂ) (Lc : Matrix c' c ℂ) (τ : Fin n → Ω → ℝ≥0)
    (col : Fin n → c) (a : Fin n → Ω → c' → ℂ) (t : ℝ≥0) (x : Ω) :
    mulRightCLM Lc (Y t x) + ∑ i : Fin n × c' × Fin 2, colCLM (col i.1) (cr i.2.2 • Pi.single i.2.1 1)
      (shiftProc Y (fun x => ((τ i.1 x : ℝ≥0) : WithTop ℝ≥0)) (fun x => reIm i.2.2 (a i.1 x i.2.1)) t x) =
      Y t x * Lc + ∑ k, birthMat (col k)
        ((Y t x - stoppedProcess Y (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x) *ᵥ a k x) := by
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type, ← sum_colCLM]
  rfl

omit [Fintype c] in
theorem frameNc_eq' (f : ℝ≥0 → Ω → Matrix ι c' ℂ) (Lc : Matrix c' c ℂ) (τ : Fin n → Ω → ℝ≥0)
    (col : Fin n → c) (a : Fin n → Ω → c' → ℂ) (t : ℝ≥0) (x : Ω) :
    mulRightCLM Lc (f t x) + ∑ i : Fin n × c' × Fin 2, colCLM (col i.1) (cr i.2.2 • Pi.single i.2.1 1)
      (onAfter (fun x => ((τ i.1 x : ℝ≥0) : WithTop ℝ≥0)) (fun x => reIm i.2.2 (a i.1 x i.2.1)) f t x) =
      f t x * Lc + ∑ k, if τ k x < t then birthMat (col k) (f t x *ᵥ a k x) else 0 := by
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type]
  by_cases h : τ k x < t
  · have h' : ((τ k x : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0) := WithTop.coe_lt_coe.2 h
    rw [ite_eq_left h, ← sum_colCLM]
    simp only [onAfter, h', ↓reduceIte]
  · have h' : ¬ ((τ k x : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0) := fun e =>
      h (WithTop.coe_lt_coe.1 e)
    rw [ite_eq_right h]
    simp only [onAfter, h', ↓reduceIte, map_zero, Finset.sum_const_zero]

omit [DecidableEq c'] [Fintype c] in
theorem frameN_add_jump (Y : ℝ≥0 → Ω → Matrix ι c' ℂ) (Lc : Matrix c' c ℂ) (τ : Fin n → Ω → ℝ≥0)
    (col : Fin n → c) (a : Fin n → Ω → c' → ℂ) (w : Fin n → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω)
    (hw : ∀ k, Y (τ k x) x *ᵥ a k x = w k x) :
    (Y t x * Lc + ∑ k, birthMat (col k)
        ((Y t x - stoppedProcess Y (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x) *ᵥ a k x)) +
      frameBirthJump τ col w t x =
      Y t x * Lc + ∑ k, if τ k x ≤ t then birthMat (col k) (Y t x *ᵥ a k x) else 0 := by
  rw [frameBirthJump_eq, add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : τ k x ≤ t
  · have hs : stoppedProcess Y (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x = Y (τ k x) x := by
      rw [stoppedProcess_eq_stopTime]
      congr 1
      unfold stopTime
      rw [min_eq_right (WithTop.coe_le_coe.2 h)]
      rfl
    rw [ite_eq_left h, ite_eq_left h, hs, sub_mulVec, hw k, ← birthCLM_apply, ← birthCLM_apply,
      ← birthCLM_apply, ← map_add, sub_add_cancel]
  · have hs : stoppedProcess Y (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0)) t x = Y t x :=
      stoppedProcess_eq_of_le (WithTop.coe_le_coe.2 (not_le.1 h).le)
    rw [ite_eq_right h, ite_eq_right h, hs, sub_self, zero_mulVec, add_zero, ← birthCLM_apply,
      map_zero]

end BlockBand.SourceProcess.CoupledFrames
