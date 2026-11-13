module

public import BlockBand.SourceProcess.Stochastic.SourceSDE.GlobalAgree
public import BlockBand.SourceProcess.Stochastic.SDE.NativeLocalUnique
public import BlockBand.SourceProcess.Stochastic.ItoNative.Main

/-!
# The joint SDE `(X, 𝒴)`: triangular coefficients and the frame part

On `E₁ × E₂` the triangular coefficients are `jb b₁ (x, y) = (b₁ x, 0)` and
`jσ σ₁ σ₂ a (x, y) = (σ₁ a x, σ₂ a x)`. They are locally Lipschitz when `b₁, σ₁, σ₂` are.

* `fst_nativeIto`, `snd_nativeIto`: the two components of a strong exit-time solution `Z` of the
  joint equation are Itô processes with the switched coefficients.
* `ae_fst_eq_of_joint`: if `X` is a global solution of `(b₁, σ₁)` from `ξ` (with a continuous
  adapted modification `X'`) and `Z` a strong exit-time solution of radius `R > 0` of the joint
  equation from `(ξ, η)`, then a.s. `exit_R(Z) ≤ exit_R(X')` and `Z_t.1 = X_t` for `t ≤ exit_R(Z)`
  (local uniqueness, `stoppedProcess_ae_eq_local`, as in `ae_eq_strongExit_of_isSDESolution`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexConstruct

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {κ : Type*} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]

/-- Joint drift `(x, y) ↦ (b₁ x, 0)`. -/
def jb (b₁ : E₁ → E₁) : E₁ × E₂ → E₁ × E₂ := fun z => (b₁ z.1, 0)

/-- Joint diffusion `(x, y) ↦ (σ₁ a x, σ₂ a x)`. -/
def jσ (σ₁ : κ → E₁ → E₁) (σ₂ : κ → E₁ → E₂) : κ → E₁ × E₂ → E₁ × E₂ :=
  fun a z => (σ₁ a z.1, σ₂ a z.1)

theorem locallyLipschitz_jb {b₁ : E₁ → E₁} (hb : LocallyLipschitz b₁) :
    LocallyLipschitz (jb (E₂ := E₂) b₁) :=
  (hb.comp LipschitzWith.prod_fst.locallyLipschitz).prodMk (LocallyLipschitz.const _)

theorem locallyLipschitz_jσ {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    (h₁ : ∀ a, LocallyLipschitz (σ₁ a)) (h₂ : ∀ a, LocallyLipschitz (σ₂ a)) (a : κ) :
    LocallyLipschitz (jσ σ₁ σ₂ a) :=
  ((h₁ a).comp LipschitzWith.prod_fst.locallyLipschitz).prodMk
    ((h₂ a).comp LipschitzWith.prod_fst.locallyLipschitz)

variable [NormedSpace ℝ E₁] [NormedSpace ℝ E₂] [Fintype κ] {S : Type*} [MeasurableSpace S]
  {μ : Measure S} [IsProbabilityMeasure μ]
  [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂]

omit [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] in
theorem fst_nativeIto {b₁ : E₁ → E₁} {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    {Z : ℝ≥0 → DriverSample S κ → E₁ × E₂} {e : DriverSample S κ → WithTop ℝ≥0}
    (hZ : IsNativeItoProcess μ Z (switchOff e fun t x => jb b₁ (Z t x))
      (fun a => switchOff e fun t x => jσ σ₁ σ₂ a (Z t x))) :
    IsNativeItoProcess μ (fun t x => (Z t x).1) (switchOff e fun t x => b₁ (Z t x).1)
      (fun a => switchOff e fun t x => σ₁ a (Z t x).1) := by
  have h := hZ.map_clm (ContinuousLinearMap.fst ℝ E₁ E₂)
  have e1 : (fun t x => ContinuousLinearMap.fst ℝ E₁ E₂
      (switchOff e (fun t x => jb b₁ (Z t x)) t x)) = switchOff e fun t x => b₁ (Z t x).1 := by
    funext t x; simp only [switchOff]; split_ifs <;> simp [jb]
  have e2 : (fun a t x => ContinuousLinearMap.fst ℝ E₁ E₂
      (switchOff e (fun t x => jσ σ₁ σ₂ a (Z t x)) t x)) =
      fun a => switchOff e fun t x => σ₁ a (Z t x).1 := by
    funext a t x; simp only [switchOff]; split_ifs <;> simp [jσ]
  rw [e1, e2] at h
  exact h

omit [MeasurableSpace E₁] [BorelSpace E₁] [MeasurableSpace E₂] [BorelSpace E₂] in
theorem snd_nativeIto {b₁ : E₁ → E₁} {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    {Z : ℝ≥0 → DriverSample S κ → E₁ × E₂} {e : DriverSample S κ → WithTop ℝ≥0}
    (hZ : IsNativeItoProcess μ Z (switchOff e fun t x => jb b₁ (Z t x))
      (fun a => switchOff e fun t x => jσ σ₁ σ₂ a (Z t x))) :
    IsNativeItoProcess μ (fun t x => (Z t x).2) (fun _ _ => 0)
      (fun a => switchOff e fun t x => σ₂ a (Z t x).1) := by
  have h := hZ.map_clm (ContinuousLinearMap.snd ℝ E₁ E₂)
  have e1 : (fun t x => ContinuousLinearMap.snd ℝ E₁ E₂
      (switchOff e (fun t x => jb b₁ (Z t x)) t x)) = fun _ _ => (0 : E₂) := by
    funext t x; simp only [switchOff]; split_ifs <;> simp [jb]
  have e2 : (fun a t x => ContinuousLinearMap.snd ℝ E₁ E₂
      (switchOff e (fun t x => jσ σ₁ σ₂ a (Z t x)) t x)) =
      fun a => switchOff e fun t x => σ₂ a (Z t x).1 := by
    funext a t x; simp only [switchOff]; split_ifs <;> simp [jσ]
  rw [e1, e2] at h
  exact h

omit [MeasurableSpace E₂] [BorelSpace E₂] in
/-- **The frame part of a joint exit-time solution is the global solution before the exit.** -/
theorem ae_fst_eq_of_joint {b₁ : E₁ → E₁} {σ₁ : κ → E₁ → E₁} {σ₂ : κ → E₁ → E₂}
    (hb : LocallyLipschitz b₁) (hσ : ∀ a, LocallyLipschitz (σ₁ a)) {ξ : DriverSample S κ → E₁}
    {η : DriverSample S κ → E₂} {X X' : ℝ≥0 → DriverSample S κ → E₁}
    {Z : ℝ≥0 → DriverSample S κ → E₁ × E₂} {R : ℝ} (hR : 0 < R)
    (hX : IsSDESolution μ b₁ σ₁ ξ X)
    (hZ : IsStrongExitSolution μ (jb b₁) (jσ σ₁ σ₂) (fun x => (ξ x, η x)) R Z)
    (hX'a : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X' t))
    (hX'c : ∀ x, Continuous fun t => X' t x)
    (hXX' : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ t, X' t x = X t x) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, exitTime Z R x ≤ exitTimeOf X' R x ∧
      ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ exitTime Z R x → (Z t x).1 = X t x := by
  classical
  obtain ⟨hXi, hX0⟩ := hX
  set e := exitTime Z R with hedef
  set ρ : DriverSample S κ → WithTop ℝ≥0 := fun x => min (exitTimeOf X' R x) (e x) with hρdef
  have hρ : IsStoppingTime (driverAugmented (κ := κ) μ) ρ :=
    (isStoppingTime_exitTimeOf hX'a hX'c R).min hZ.stopping
  set Z₁ : ℝ≥0 → DriverSample S κ → E₁ := fun t x => (Z t x).1 with hZ₁def
  have hZ₁ := fst_nativeIto hZ.sol.1
  have hZ₁c : ∀ x, Continuous fun t => Z₁ t x := fun x => continuous_fst.comp (hZ.continuous x)
  obtain ⟨c, -, hceq⟩ := exists_truncCoeff hb hσ hR
  have hXb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
      ‖X s x‖ ≤ R := by
    filter_upwards [hXX'] with x hx s hs0 hs
    rw [← hx s]
    exact norm_le_of_le_exitTimeOf (hX'c x) hs0 (hs.trans (min_le_left _ _))
  have hZb : ∀ x, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x → ‖Z₁ s x‖ ≤ R :=
    fun x s hs0 hs => (norm_fst_le _).trans
      (norm_le_of_le_exitTimeOf (hZ.continuous x) hs0 (hs.trans (min_le_right _ _)))
  have hbound : ∀ {Y : ℝ≥0 → DriverSample S κ → E₁}
      (hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (Y t))
      (hYc : ∀ᵐ x ∂driverLaw (κ := κ) μ, Continuous fun t => Y t x)
      (hYb : ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ ρ x →
        ‖Y s x‖ ≤ R) (ℓ : E₁ →L[ℝ] ℝ) (T : ℝ≥0),
      NativeIntegrand μ T (stopIntegrand ρ (fun a p => ℓ (σ₁ a (Y p.1.toNNReal p.2)))) :=
    fun hYa hYc hYb ℓ T => nativeIntegrand_stopped_bounded (μ := μ) hYa hYc hρ
      (φ := fun a y => ℓ (σ₁ a y)) (fun a => ℓ.continuous.comp (hσ a).continuous)
      (M := ‖ℓ‖ * c.C) (by
        filter_upwards [hYb] with x hx s hs0 hs a
        rw [← Real.norm_eq_abs, ← ((hceq _ (hx s hs0 hs)).2 a)]
        exact (ℓ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (c.bd_σ a _) (norm_nonneg _))) T
  have hXid : ∀ T, StoppedIdentity μ T ρ X (switchOff (fun _ => ⊤) fun t x => b₁ (X t x))
      (fun a => switchOff (fun _ => ⊤) fun t x => σ₁ a (X t x)) := fun T =>
    IsNativeItoProcess.stoppedIdentity hXi hρ T fun ℓ =>
      NativeIntegrand.congr (hbound hXi.adapted hXi.continuous hXb ℓ T) fun a =>
        Eventually.of_forall fun p => by
          simp only [stopIntegrand, functionalIntegrand, switchOff, le_top, ite_true]
  have hZid : ∀ T, StoppedIdentity μ T ρ Z₁ (switchOff e fun t x => b₁ (Z₁ t x))
      (fun a => switchOff e fun t x => σ₁ a (Z₁ t x)) := fun T =>
    IsNativeItoProcess.stoppedIdentity hZ₁ hρ T fun ℓ =>
      NativeIntegrand.congr (hbound hZ₁.adapted (Eventually.of_forall hZ₁c)
        (Eventually.of_forall hZb) ℓ T) fun a => Eventually.of_forall fun p => by
          simp only [stopIntegrand, functionalIntegrand, switchOff]
          by_cases h1 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ ρ p.2
          · have h2 : ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ exitTime Z R p.2 :=
              h1.trans (min_le_right _ _)
            simp only [h1, h2, ite_true]
          · simp only [h1, ite_false]
  have hst := stoppedProcess_ae_eq_local hb hσ hR hρ hXi.adapted hZ₁.adapted hXi.continuous
    (Eventually.of_forall hZ₁c)
    (by filter_upwards [hX0] with x hx; rw [hx, hZ.init]) hXid hZid ?_ ?_ ?_
  rotate_left
  · filter_upwards [hXb] with x hx s hs0 hs
    left
    have hse : (s : WithTop ℝ≥0) ≤ e x := hs.trans (min_le_right _ _)
    simp only [switchOff, le_top, hse, ↓reduceIte]
    exact ⟨hx s hs0 hs, hZb x s hs0 hs, trivial, rfl, fun a => ⟨trivial, rfl⟩⟩
  · filter_upwards [hXi.continuous] with x hx T
    exact aesm_switchOff_path hb.continuous hx _ T
  · exact Eventually.of_forall fun x T => aesm_switchOff_path hb.continuous (hZ₁c x) _ T
  have hind := indistinguishable_of_continuous
    (hXi.continuous.mono fun x hx => continuous_stoppedProcess hx ρ)
    (Eventually.of_forall fun x => continuous_stoppedProcess (hZ₁c x) ρ) hst
  filter_upwards [hind, hXX'] with x h1 h2
  have key : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ ρ x → X t x = Z₁ t x := fun t ht => by
    have := h1 t
    rwa [stoppedProcess_eq_of_le ht, stoppedProcess_eq_of_le ht] at this
  have hle : e x ≤ exitTimeOf X' R x := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    have hρm : ρ x = m := by rw [hρdef]; exact (min_eq_left hlt.le).trans hm.symm
    have h3 := le_norm_exitTimeOf (hX'c x) hm.symm
    rw [h2 m, key m hρm.ge] at h3
    have h4 : ‖Z m x‖ < R := norm_lt_of_lt_exitTimeOf (X := Z) (by rw [hm]; exact hlt)
    linarith [norm_fst_le (Z m x)]
  refine ⟨hle, fun t ht => (key t ?_).symm⟩
  rw [hρdef]
  exact le_min (ht.trans hle) ht

end BlockBand.SourceProcess.ComplexConstruct
