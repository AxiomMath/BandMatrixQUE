module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Generic chart transfer of SDE coefficients

* `chartSigma φ σ a w = (Dφ w)⁻¹ σ_a(φ w)`,
* `chartDrift φ b σ w = (Dφ w)⁻¹ (b(φ w) − ½ Σ_a D²φ w (σ̃_a w, σ̃_a w))`
satisfy, exactly and without a second-order chain rule,
* `chart_sigma_eq`: `Dφ w (σ̃_a w) = σ_a(φ w)`;
* `chart_drift_eq`: `Dφ w (b̃ w) + ½ Σ_a D²φ w (σ̃_a w) (σ̃_a w) = b(φ w)`,
which are the identities that Itô's formula for `φ` needs to return the flat coefficients
(compare the hand-computed `Exists.toFlat_drift` at `p = 1`). They are `C^∞` on all of `E`
(`contDiff_chartSigma`, `contDiff_chartDrift`), hence locally Lipschitz, as local
well-posedness requires. `exists_equiv_fderiv_of_leftInverse` gives the invertibility from a
differentiable left inverse.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*} [Fintype κ]

/-- `(Dφ w)⁻¹` (totalized `ContinuousLinearMap.inverse`). -/
def chartInv (φ : E → E) (w : E) : E →L[ℝ] E := ContinuousLinearMap.inverse (fderiv ℝ φ w)

/-- Chart noise `σ̃_a(w) = (Dφ w)⁻¹ σ_a(φ w)`. -/
def chartSigma (φ : E → E) (σ : κ → E → E) (a : κ) (w : E) : E := chartInv φ w (σ a (φ w))

/-- Chart drift `b̃(w) = (Dφ w)⁻¹ (b(φ w) − ½ Σ_a D²φ w (σ̃_a, σ̃_a))`. -/
def chartDrift (φ : E → E) (b : E → E) (σ : κ → E → E) (w : E) : E :=
  chartInv φ w (b (φ w) - (1 / 2 : ℝ) •
    ∑ a, fderiv ℝ (fderiv ℝ φ) w (chartSigma φ σ a w) (chartSigma φ σ a w))

theorem fderiv_chartInv_apply {φ : E → E} {w : E} (hinv : ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) =
    fderiv ℝ φ w) (x : E) : fderiv ℝ φ w (chartInv φ w x) = x := by
  obtain ⟨e, he⟩ := hinv
  rw [chartInv, ← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply x

omit [Fintype κ] in
/-- **The chart noise is pushed to the flat noise.** -/
theorem chart_sigma_eq {φ : E → E} (σ : κ → E → E) {w : E}
    (hinv : ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w) (a : κ) :
    fderiv ℝ φ w (chartSigma φ σ a w) = σ a (φ w) :=
  fderiv_chartInv_apply hinv _

/-- **The chart drift satisfies the Itô identity** `Dφ b̃ + ½ Σ D²φ(σ̃, σ̃) = b ∘ φ`. -/
theorem chart_drift_eq {φ : E → E} (b : E → E) (σ : κ → E → E) {w : E}
    (hinv : ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w) :
    fderiv ℝ φ w (chartDrift φ b σ w) + (1 / 2 : ℝ) •
      ∑ a, fderiv ℝ (fderiv ℝ φ) w (chartSigma φ σ a w) (chartSigma φ σ a w) = b (φ w) := by
  rw [chartDrift, fderiv_chartInv_apply hinv, sub_add_cancel]

section Smooth

variable [CompleteSpace E]

theorem contDiff_chartInv {φ : E → E} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hinv : ∀ w, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w) :
    ContDiff ℝ (⊤ : ℕ∞) (chartInv φ) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  obtain ⟨e, he⟩ := hinv w
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) ContinuousLinearMap.inverse (fderiv ℝ φ w) := by
    rw [← he]; exact contDiffAt_map_inverse e
  exact hi.comp w hD.contDiffAt

omit [Fintype κ] in
theorem contDiff_chartSigma {φ : E → E} {σ : κ → E → E} {U : Set E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hinv : ∀ w, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w)
    (hσ : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (σ a) U) (hU : ∀ w, φ w ∈ U) (a : κ) :
    ContDiff ℝ (⊤ : ℕ∞) (chartSigma φ σ a) :=
  (contDiff_chartInv hφ hinv).clm_apply ((hσ a).comp_contDiff hφ hU)

theorem contDiff_chartDrift {φ : E → E} {b : E → E} {σ : κ → E → E} {U : Set E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hinv : ∀ w, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hσ : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (σ a) U)
    (hU : ∀ w, φ w ∈ U) : ContDiff ℝ (⊤ : ℕ∞) (chartDrift φ b σ) := by
  have hD1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hD2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ φ)) := hD1.fderiv_right (by simp)
  have hs : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (chartSigma φ σ a) := contDiff_chartSigma hφ hinv hσ hU
  refine (contDiff_chartInv hφ hinv).clm_apply ((hb.comp_contDiff hφ hU).sub
    (contDiff_const.smul (ContDiff.sum fun a _ => (hD2.clm_apply (hs a)).clm_apply (hs a))))

omit [Fintype κ] in
theorem locallyLipschitz_chartSigma {φ : E → E} {σ : κ → E → E} {U : Set E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hinv : ∀ w, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w)
    (hσ : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (σ a) U) (hU : ∀ w, φ w ∈ U) (a : κ) :
    LocallyLipschitz (chartSigma φ σ a) :=
  ((contDiff_chartSigma hφ hinv hσ hU a).of_le (by simp)).locallyLipschitz

theorem locallyLipschitz_chartDrift {φ : E → E} {b : E → E} {σ : κ → E → E} {U : Set E}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hinv : ∀ w, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hσ : ∀ a, ContDiffOn ℝ (⊤ : ℕ∞) (σ a) U)
    (hU : ∀ w, φ w ∈ U) : LocallyLipschitz (chartDrift φ b σ) :=
  ((contDiff_chartDrift hφ hinv hb hσ hU).of_le (by simp)).locallyLipschitz

end Smooth

/-- An everywhere-differentiable left inverse makes `Dφ w` invertible (finite dimension). -/
theorem exists_equiv_fderiv_of_leftInverse [FiniteDimensional ℝ E] {φ ψ : E → E} {w : E}
    (hφ : DifferentiableAt ℝ φ w) (hψ : DifferentiableAt ℝ ψ (φ w)) (h : ∀ u, ψ (φ u) = u) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ φ w := by
  have hcomp : (fderiv ℝ ψ (φ w)).comp (fderiv ℝ φ w) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp w hψ hφ]
    have : ψ ∘ φ = id := funext h
    rw [this, fderiv_id]
  have hinj : Function.Injective (fderiv ℝ φ w) := fun u v huv => by
    have := congrArg (fderiv ℝ ψ (φ w)) huv
    simpa [← ContinuousLinearMap.comp_apply, hcomp] using this
  refine ⟨(LinearEquiv.ofInjectiveEndo (fderiv ℝ φ w : E →ₗ[ℝ] E) hinj).toContinuousLinearEquiv,
    ?_⟩
  ext x
  rfl

end BlockBand.Transmission.Dual.G
