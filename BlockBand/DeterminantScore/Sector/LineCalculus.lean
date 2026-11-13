module

public import BlockBand.DeterminantScore.Sector.Statement
public import BlockBand.Model.Construction.GaussianWeakIntegrationByParts
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# One-dimensional calculus for cut-off observables

* a cut-off of a continuous observable by an arbitrary predicate is continuous at a zero of
  the observable, and has zero Fréchet derivative at a point where the observable has value
  zero and derivative zero (no regularity of the predicate is assumed);
* a continuous function on `ℝ` that is differentiable off a countable set, with a locally
  integrable derivative, has that derivative as its distributional derivative
  (`Model.Construction.HasRealWeakDerivative`). This is the one-dimensional replacement of the
  cutoff `χ(P/ε)` in Steps 1–3 of the paper's proof: the fundamental theorem of calculus
  with countably many exceptional points (finitely many roots of `P` on a line) leaves no boundary term.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory Filter Set
open scoped Topology ContDiff

/-- A cutoff cannot acquire a jump at a point where its continuous uncut
observable vanishes. The predicate is arbitrary. -/
theorem continuousAt_ite_zero_of_continuousAt_of_eq_zero
    {X F : Type*} [PseudoMetricSpace X]
    [SeminormedAddCommGroup F]
    (p : X → Prop) [DecidablePred p] (f : X → F) {x : X}
    (hf : ContinuousAt f x) (hfx : f x = 0) :
    ContinuousAt (fun y => if p y then f y else 0) x := by
  rw [Metric.continuousAt_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  by_cases hpy : p y
  · simpa [hpy, hfx] using hclose hy
  · simp [hpy, hfx, hε]

/-- Cutting a function with zero value and zero Fréchet derivative at a point by any predicate
preserves its zero derivative there. -/
theorem hasFDerivAt_ite_zero_of_hasFDerivAt_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E → Prop) [DecidablePred p] (f : E → F) {x : E}
    (hf : HasFDerivAt f (0 : E →L[ℝ] F) x) (hfx : f x = 0) :
    HasFDerivAt (fun y => if p y then f y else 0) (0 : E →L[ℝ] F) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf ⊢
  refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)).trans_isLittleO hf
  by_cases hp : p (x + h)
  · by_cases hpx : p x <;> simp [hp, hpx, hfx]
  · by_cases hpx : p x <;> simp [hp, hpx, hfx]

/-- A continuous function on `ℝ`, differentiable off a countable set with a locally integrable
derivative, has that derivative as its distributional derivative. -/
theorem hasRealWeakDerivative_of_hasDerivAt_off_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F g : ℝ → E} (hF : Continuous F) (hg : LocallyIntegrable g volume) {S : Set ℝ}
    (hS : S.Countable) (hd : ∀ s ∉ S, HasDerivAt F (g s) s) :
    BlockBand.Model.Construction.HasRealWeakDerivative F g := by
  refine ⟨hF.locallyIntegrable, hg, fun φ hφ hφs => ?_⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hdφ : Continuous (deriv φ) := hφ1.continuous_deriv le_rfl
  have hdφs : HasCompactSupport (deriv φ) := hφs.deriv
  have hI1 : Integrable (fun s => deriv φ s • F s) :=
    hF.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hdφ hdφs
  have hI2 : Integrable (fun s => φ s • g s) :=
    hg.integrable_smul_left_of_hasCompactSupport hφ.continuous hφs
  obtain ⟨R0, hR0⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR0
  set R := max R0 0
  have hR0' : 0 ≤ R := le_max_right _ _
  have hR : tsupport φ ⊆ Icc (-R) R := hR0.trans
    (Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _))
  have hout : ∀ s, s ∉ Icc (-R) R → φ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hs (hR h)
  have hdout : ∀ s, s ∉ Icc (-R) R → deriv φ s = 0 := fun s hs => by
    by_contra h
    exact hs (hR (support_deriv_subset h))
  set H' : ℝ → E := fun s => deriv φ s • F s + φ s • g s
  have hsupp : Function.support H' ⊆ Ioc (-R - 1) (R + 1) := by
    intro s hs
    by_contra hns
    apply hs
    have hns' : s ∉ Icc (-R) R := fun h => hns ⟨by linarith [h.1], by linarith [h.2]⟩
    simp [H', hout s hns', hdout s hns']
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le (fun s => φ s • F s) H'
    (show -R - 1 ≤ R + 1 by linarith) hS
    ((hφ.continuous.smul hF).continuousOn)
    (fun s hs => by
      have h := (hφ1.differentiable one_ne_zero s).hasDerivAt.smul (hd s hs.2)
      rw [show H' s = φ s • g s + deriv φ s • F s from add_comm _ _]
      exact h)
    ((hI1.add hI2).intervalIntegrable)
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp] at hFTC
  have ha : φ (-R - 1) = 0 := hout _ fun h => by linarith [h.1]
  have hb : φ (R + 1) = 0 := hout _ fun h => by linarith [h.2]
  simp only [ha, hb, zero_smul, sub_zero] at hFTC
  rw [integral_add hI1 hI2] at hFTC
  exact eq_neg_of_add_eq_zero_left hFTC

end BlockBand.DeterminantScore.Sector
