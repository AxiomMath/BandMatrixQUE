module
public import BlockBand.SourceProcess.Stochastic.RankBarrier.GramMinors
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.DefectLyapunov
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Generator terms along lines, and smoothness of `e_k`

The generator `sdeGenerator b σ φ y = Dφ(y)[b y] + ½ ∑_a D²φ(y)[σ_a y, σ_a y]` of the
finite source equation is computed through the lines `t ↦ y + t h`:

* `fderiv_apply_eq_of_line`: `Dφ(y)[h]` is the derivative at `0` of `t ↦ φ(y + t h)`;
* `fderiv_fderiv_eq_of_quadratic`: if `φ` is `C²` and `φ(y + t h) = a + b t + γ t²` for all
  real `t`, then `D²φ(y)[h,h] = 2γ`.

`contDiff_minorSq_mul`: `W ↦ minorSq k (Q W)` (hence `e_k(B)`, `e_k(M − B)`) is `C^n` for the
Frobenius normed structure used for `GramRankBarrier`.
-/

namespace BlockBand.SourceProcess.Stochastic.RankBarrierProof
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_line (V H : E) (t₀ : ℝ) : HasDerivAt (fun t : ℝ => V + t • H) H t₀ := by
  simpa using ((hasDerivAt_id t₀).smul_const H).const_add V

/-- First derivative along a line. -/
theorem fderiv_apply_eq_of_line {φ : E → ℝ} {V H : E} {β : ℝ} (hφ : DifferentiableAt ℝ φ V)
    (h : HasDerivAt (fun t : ℝ => φ (V + t • H)) β 0) : fderiv ℝ φ V H = β :=
  (hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line V H 0) (by simp)).unique h

/-- Second derivative along a line on which `φ` is a quadratic polynomial. -/
theorem fderiv_fderiv_eq_of_quadratic {φ : E → ℝ} {V H : E} {a b γ : ℝ} (hφ : ContDiff ℝ 2 φ)
    (h : ∀ t : ℝ, φ (V + t • H) = a + b * t + γ * t ^ 2) :
    fderiv ℝ (fderiv ℝ φ) V H H = 2 * γ := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have key : ∀ t₀ : ℝ, fderiv ℝ φ (V + t₀ • H) H = b + 2 * γ * t₀ := by
    intro t₀
    have h1 := (hd (V + t₀ • H)).hasFDerivAt.comp_hasDerivAt t₀ (hasDerivAt_line V H t₀)
    have h2 : HasDerivAt (fun t : ℝ => φ (V + t • H)) (b + 2 * γ * t₀) t₀ := by
      rw [show (fun t : ℝ => φ (V + t • H)) = fun t => a + b * t + γ * t ^ 2 from funext h]
      have := (((hasDerivAt_id' t₀).const_mul b).const_add a).add
        ((hasDerivAt_pow 2 t₀).const_mul γ)
      exact this.congr_deriv (by norm_num; ring)
    exact h1.unique h2
  have h3 : HasDerivAt (fun t : ℝ => fderiv ℝ φ (V + t • H) H)
      (fderiv ℝ (fderiv ℝ φ) V H H) 0 := by
    have h4 := (hdd V).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_line V H 0) (by simp)
    simpa using h4.clm_apply (hasDerivAt_const (0 : ℝ) H)
  have h6 : HasDerivAt (fun t : ℝ => fderiv ℝ φ (V + t • H) H) (2 * γ) 0 := by
    rw [show (fun t : ℝ => fderiv ℝ φ (V + t • H) H) = fun t => b + 2 * γ * t from funext key]
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * γ)).const_add b
  exact h3.unique h6

end Line

section Smooth

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Matrix entries as continuous `ℝ`-linear maps (Frobenius norm). -/
def entryCLM {m n : Type*} [Fintype m] [Fintype n] (i : m) (j : n) : Matrix m n ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W => W i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } 1
    fun W => by
      show ‖W i j‖ ≤ 1 * ‖W‖
      rw [one_mul]; exact SourceAlgebra.frob_entry_le W i j

variable {N : WithTop ℕ∞}

theorem contDiff_entry {m n : Type*} [Fintype m] [Fintype n] (i : m) (j : n) :
    ContDiff ℝ N fun W : Matrix m n ℂ => W i j :=
  (entryCLM i j).contDiff

theorem contDiff_mul_entry {ι c : Type*} [Fintype ι] [Fintype c] (Q : Matrix ι ι ℂ) (l : ι)
    (m : c) : ContDiff ℝ N fun W : Matrix ι c ℂ => (Q * W) l m := by
  simp only [mul_apply]
  exact ContDiff.sum fun n _ => contDiff_const.mul (contDiff_entry n m)

theorem contDiff_det' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type*}
    [Fintype n] [DecidableEq n] {M : E → Matrix n n ℂ} (h : ∀ i j, ContDiff ℝ N fun x => M x i j) :
    ContDiff ℝ N fun x => det (M x) := by
  simp only [det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_minorSq_mul {ι c : Type*} [Fintype ι] [Fintype c] (k : ℕ) (Q : Matrix ι ι ℂ) :
    ContDiff ℝ N fun W : Matrix ι c ℂ => minorSq k (Q * W) := by
  unfold minorSq
  exact ContDiff.sum fun p _ =>
    (contDiff_det' fun i j => contDiff_mul_entry Q (p.1 i) (p.2 j)).norm_sq ℝ

end Smooth

end BlockBand.SourceProcess.Stochastic.RankBarrierProof
