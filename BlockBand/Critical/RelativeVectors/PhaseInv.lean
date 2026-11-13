module

public import BlockBand.Critical.RelativeVectors.CrossHess
public import BlockBand.Critical.RelativeVectors.PhasePairing

/-!
# Phase invariance of the cross error

The Lean statement puts the phases on the terminal marks only, and the Duhamel integrand is
evaluated at the phase-free array `frameArray`. Phase averaging is legitimate pointwise because
the cross error of a label-phase-invariant function is itself label-phase invariant:

* `phaseCLM u z = (u_i z_i)_i` (label phases with unit `u_i`);
* `fderiv_fderiv_comp_eq`: if `g ∘ L = g` (`L` continuous linear, `g` of class `C²`), then
  `D²g(Lz)(Lx, Ly) = D²g(z)(x, y)`;
* `rotPair_smul`: `D(iA, iB) - D(A, B)` is unchanged under `A ↦ aA`, `B ↦ bB` when `ab = 1`;
* `crossError_phase_eq`: if `g(u z) = g(z)` for all unit `u`, then
  `crossError(D²g(uz))(uz) = crossError(D²g(z))(z)`;
* `ae_norm_phase_eq_one`: the phases of `phaseVectorLaw` are unit a.s.;
* `crossError_eq_phase_average`: `crossError(D²g(z))(z) = ∫ crossError(D²g(θz))(θz) dθ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N r : ℕ}

/-- Label phases `z ↦ (u_i z_i)_i` as a continuous `ℝ`-linear map. -/
def phaseCLM (u : Fin N → ℂ) : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (u i • ContinuousLinearMap.id ℝ (Fin r → ℂ)).comp (ContinuousLinearMap.proj i)

@[simp] theorem phaseCLM_apply (u : Fin N → ℂ) (z : Fin N → Fin r → ℂ) :
    phaseCLM u z = fun i => u i • z i := rfl

theorem phaseCLM_single (u : Fin N → ℂ) (i : Fin N) (v : Fin r → ℂ) :
    phaseCLM u (single i v) = single i (u i • v) := by
  funext k q
  by_cases hk : k = i
  · subst hk; simp [single]
  · simp [single, hk]

theorem phaseCLM_smul (u : Fin N → ℂ) (c : ℂ) (x : Fin N → Fin r → ℂ) :
    phaseCLM u (c • x) = c • phaseCLM u x := by
  funext k q; simp [smul_eq_mul]; ring

/-- `D²g(Lz)(Lx, Ly) = D²g(z)(x, y)` when `g ∘ L = g`. -/
theorem fderiv_fderiv_comp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ 2 g) (L : E →L[ℝ] E) (hL : ∀ z, g (L z) = g z) (z x y : E) :
    fderiv ℝ (fderiv ℝ g) (L z) (L x) (L y) = fderiv ℝ (fderiv ℝ g) z x y := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- first derivatives
  have h1 : fderiv ℝ g = fun w => (fderiv ℝ g (L w)).comp L := by
    funext w
    have : g = g ∘ L := by funext v; exact (hL v).symm
    conv_lhs => rw [this]
    exact ((hd (L w)).hasFDerivAt.comp w L.hasFDerivAt).fderiv
  -- second derivatives
  have h2 : HasFDerivAt (fun w => (fderiv ℝ g (L w)).comp L)
      (((ContinuousLinearMap.compL ℝ E E ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ g) (L z)).comp L))
      z :=
    (((ContinuousLinearMap.compL ℝ E E ℝ).flip L).hasFDerivAt).comp z
      ((hd2 (L z)).hasFDerivAt.comp z L.hasFDerivAt)
  have h3 : fderiv ℝ (fderiv ℝ g) z =
      ((ContinuousLinearMap.compL ℝ E E ℝ).flip L).comp ((fderiv ℝ (fderiv ℝ g) (L z)).comp L) := by
    rw [show fderiv ℝ (fderiv ℝ g) z = fderiv ℝ (fun w => (fderiv ℝ g (L w)).comp L) z by
      rw [← h1]]
    exact h2.fderiv
  rw [h3]
  rfl

/-- `D(iA, iB) - D(A, B)`. -/
def rotPair (D : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) →L[ℝ] ℝ)
    (A B : Fin N → Fin r → ℂ) : ℝ :=
  D (Complex.I • A) (Complex.I • B) - D A B

theorem rotPair_smul (D : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) →L[ℝ] ℝ)
    (A B : Fin N → Fin r → ℂ) {a b : ℂ} (hab : a * b = 1) :
    rotPair D (a • A) (b • B) = rotPair D A B := by
  unfold rotPair
  rw [bilRot_eq D (a • A) (b • B), bilRot_eq D A B]
  congr 2
  refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun q' _ =>
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  calc gam D m q m' q' * (a * A m q * (b * B m' q'))
      = gam D m q m' q' * ((a * b) * (A m q * B m' q')) := by ring
    _ = _ := by rw [hab, one_mul]

theorem single_I (i : Fin N) (v : Fin r → ℂ) :
    single i (Complex.I • v) = Complex.I • single i v := by
  funext k q
  by_cases hk : k = i
  · subst hk; simp [single]
  · simp [single, hk]

theorem crossTerm_eq_rotPair (D : (Fin N → Fin r → ℂ) →L[ℝ] (Fin N → Fin r → ℂ) →L[ℝ] ℝ)
    (z : Fin N → Fin r → ℂ) (i j : Fin N) :
    crossTerm D z i j = rotPair D (single i (z j)) (single j (z i)) +
      rotPair D (single j (z i)) (single i (z j)) := by
  unfold crossTerm rotPair
  rw [single_I, single_I]
  ring

/-- **Phase invariance of the cross error.** -/
theorem crossError_phase_eq {g : (Fin N → Fin r → ℂ) → ℝ} (hg : ContDiff ℝ 2 g)
    {u : Fin N → ℂ} (hu : ∀ i, ‖u i‖ = 1) (hinv : ∀ z, g (phaseCLM u z) = g z)
    (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ) :
    crossError N r lam ℓ (fderiv ℝ (fderiv ℝ g) (phaseCLM u z)) (phaseCLM u z) =
      crossError N r lam ℓ (fderiv ℝ (fderiv ℝ g) z) z := by
  have hcu : ∀ i, starRingEnd ℂ (u i) * u i = 1 := by
    intro i
    rw [Complex.conj_mul', hu i]; simp
  -- `single i (u_j z_j) = L (single i (ū_i u_j z_j))`
  have hs : ∀ i j, single i ((phaseCLM u z) j) =
      phaseCLM u ((starRingEnd ℂ (u i) * u j) • single i (z j)) := by
    intro i j
    rw [phaseCLM_smul, phaseCLM_single, phaseCLM_apply]
    funext k q
    by_cases hk : k = i
    · subst hk
      simp only [single, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
      calc u j * z j q = (starRingEnd ℂ (u k) * u k) * (u j * z j q) := by rw [hcu k, one_mul]
        _ = _ := by ring
    · simp [single, hk]
  have hrot : ∀ i j, rotPair (fderiv ℝ (fderiv ℝ g) (phaseCLM u z))
      (single i ((phaseCLM u z) j)) (single j ((phaseCLM u z) i)) =
      rotPair (fderiv ℝ (fderiv ℝ g) z) (single i (z j)) (single j (z i)) := by
    intro i j
    rw [hs i j, hs j i]
    unfold rotPair
    rw [← phaseCLM_smul, ← phaseCLM_smul, fderiv_fderiv_comp_eq hg _ hinv,
      fderiv_fderiv_comp_eq hg _ hinv]
    have := rotPair_smul (fderiv ℝ (fderiv ℝ g) z) (single i (z j)) (single j (z i))
      (a := starRingEnd ℂ (u i) * u j) (b := starRingEnd ℂ (u j) * u i) (by
        calc starRingEnd ℂ (u i) * u j * (starRingEnd ℂ (u j) * u i)
            = (starRingEnd ℂ (u i) * u i) * (starRingEnd ℂ (u j) * u j) := by ring
          _ = 1 := by rw [hcu i, hcu j, one_mul])
    unfold rotPair at this
    exact this
  unfold crossError
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [crossTerm_eq_rotPair, crossTerm_eq_rotPair, hrot i j, hrot j i]

/-!
## Phase averages
-/

theorem ae_norm_phase_eq_one : ∀ᵐ θ ∂phaseVectorLaw N, ∀ i, ‖θ i‖ = 1 := by
  rw [ae_all_iff]
  intro i
  have hmap : (phaseVectorLaw N).map (fun θ => θ i) = phaseLaw := by
    unfold phaseVectorLaw
    rw [show (fun θ : Fin N → ℂ => θ i) = Function.eval i from rfl, Measure.pi_map_eval]
    simp
  have hS : MeasurableSet {z : ℂ | ‖z‖ = 1} :=
    measurableSet_eq_fun continuous_norm.measurable measurable_const
  have h1 : ∀ᵐ z ∂phaseLaw, ‖z‖ = 1 := by
    rw [phaseLaw_eq_map, ae_map_iff continuous_phaseMap.measurable.aemeasurable hS]
    refine Filter.Eventually.of_forall fun x => ?_
    unfold phaseMap
    rw [Complex.norm_exp]
    simp
  rw [← hmap] at h1
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h1

/-- **Phase averaging is legitimate pointwise**: for label-phase-invariant `g` of class `C²`,
`crossError(D²g(z))(z) = ∫ crossError(D²g(θz))(θz) dθ` (`θ ~ phaseVectorLaw N`). -/
theorem crossError_eq_phase_average {g : (Fin N → Fin r → ℂ) → ℝ} (hg : ContDiff ℝ 2 g)
    (hinv : ∀ u : Fin N → ℂ, (∀ i, ‖u i‖ = 1) → ∀ z, g (phaseCLM u z) = g z)
    (lam : Fin N → ℝ) (ℓ : ℕ) (z : Fin N → Fin r → ℂ) :
    crossError N r lam ℓ (fderiv ℝ (fderiv ℝ g) z) z =
      ∫ θ, crossError N r lam ℓ (fderiv ℝ (fderiv ℝ g) (phaseCLM θ z)) (phaseCLM θ z)
        ∂phaseVectorLaw N := by
  rw [integral_congr_ae (ae_norm_phase_eq_one.mono fun θ hθ =>
    crossError_phase_eq hg hθ (hinv θ hθ) lam ℓ z)]
  simp

end BlockBand.Critical.RelativeVectors
