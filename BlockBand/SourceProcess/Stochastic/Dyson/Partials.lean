module

public import BlockBand.Internal.Contracts.Transmission
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Partial derivatives of time-independent functions

The partial derivatives `partialTime`, `partialSpace`, `partialSpace2`, the Itô drift and the Itô
bracket of `(t, y) ↦ g(y)`, in terms of the derivatives of `g`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open Filter Topology
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission

variable {d : ℕ}

/-- `fderiv (fderiv f) y v w = fderiv (y' ↦ fderiv f y' w) y v`. -/
theorem fderiv_fderiv_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ (fderiv ℝ f) y) (v w : E) :
    fderiv ℝ (fderiv ℝ f) y v w = fderiv ℝ (fun y' => fderiv ℝ f y' w) y v := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

theorem fderiv_comp_snd_apply {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : DifferentiableAt ℝ g y) (t : ℝ) (v : ℝ × (Fin d → ℝ)) :
    fderiv ℝ (fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) v = fderiv ℝ g y v.2 := by
  have h := hg.hasFDerivAt.comp (t, y) (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, y)))
  rw [show (fun p : ℝ × (Fin d → ℝ) => g p.2) = g ∘ Prod.snd from rfl, h.fderiv]
  rfl

theorem partialTime_comp_snd {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : DifferentiableAt ℝ g y) (t : ℝ) :
    partialTime (fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) = 0 := by
  unfold partialTime
  rw [fderiv_comp_snd_apply hg]
  simp

theorem partialSpace_comp_snd {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : DifferentiableAt ℝ g y) (t : ℝ) (a : Fin d) :
    partialSpace (fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) a = fderiv ℝ g y (Pi.single a 1) := by
  unfold partialSpace
  rw [fderiv_comp_snd_apply hg]

theorem partialSpace2_comp_snd {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : ContDiffAt ℝ 2 g y) (t : ℝ) (a b : Fin d) :
    partialSpace2 (fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) a b =
      fderiv ℝ (fderiv ℝ g) y (Pi.single a 1) (Pi.single b 1) := by
  unfold partialSpace2
  have hφ : ContDiffAt ℝ 2 (fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) :=
    hg.comp (t, y) contDiffAt_snd
  have hdφ : DifferentiableAt ℝ (fderiv ℝ fun p : ℝ × (Fin d → ℝ) => g p.2) (t, y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_fderiv_apply' hdφ, fderiv_fderiv_apply' hdg]
  have hev : (fun p' : ℝ × (Fin d → ℝ) =>
      fderiv ℝ (fun p : ℝ × (Fin d → ℝ) => g p.2) p' ((0 : ℝ), (Pi.single b 1 : Fin d → ℝ))) =ᶠ[𝓝 (t, y)]
      fun p' => fderiv ℝ g p'.2 (Pi.single b 1) := by
    have hev' : ∀ᶠ p' : ℝ × (Fin d → ℝ) in 𝓝 (t, y), DifferentiableAt ℝ g p'.2 :=
      (continuous_snd.tendsto (t, y)).eventually
        ((hg.eventually (by simp)).mono fun y' hy' => hy'.differentiableAt (by norm_num))
    filter_upwards [hev'] with p' hp'
    obtain ⟨t', y'⟩ := p'
    exact fderiv_comp_snd_apply hp' t' _
  rw [hev.fderiv_eq]
  exact fderiv_comp_snd_apply (g := fun y' => fderiv ℝ g y' (Pi.single b 1))
    (hdg.clm_apply (differentiableAt_const _)) t _

/-- `itoDrift` of a time-independent `C²` function with zero drift and constant diagonal
covariance `c · I`: `(c/2) ∑_a ∂_a² g`. -/
theorem itoDrift_comp_snd {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ} (hg : ContDiffAt ℝ 2 g y)
    (t : ℝ≥0) (c : ℝ) :
    itoDrift (fun p : ℝ × (Fin d → ℝ) => g p.2) y t 0
        (Matrix.of fun a b => if a = b then c else 0) =
      c / 2 * ∑ a, fderiv ℝ (fderiv ℝ g) y (Pi.single a 1) (Pi.single a 1) := by
  unfold itoDrift
  rw [partialTime_comp_snd (hg.differentiableAt (by norm_num))]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add, Matrix.of_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [partialSpace2_comp_snd hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `itoBracket` of time-independent `C¹` functions against `c · I`: `c ∑_a (∂_a g)²`. -/
theorem itoBracket_comp_snd {g : (Fin d → ℝ) → ℝ} {y : Fin d → ℝ}
    (hg : DifferentiableAt ℝ g y) (t : ℝ≥0) (c : ℝ) :
    itoBracket (fun p : ℝ × (Fin d → ℝ) => g p.2) y t
        (Matrix.of fun a b => if a = b then c else 0) =
      c * ∑ a, fderiv ℝ g y (Pi.single a 1) * fderiv ℝ g y (Pi.single a 1) := by
  unfold itoBracket
  simp only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [partialSpace_comp_snd hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end BlockBand.SourceProcess.Stochastic.Dyson
