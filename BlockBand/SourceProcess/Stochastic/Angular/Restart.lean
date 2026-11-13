module

public import BlockBand.SourceProcess.Stochastic.Angular.Interface
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionHolds
public import BlockBand.SourceProcess.Stochastic.Dyson.NonCollisionStop

/-!
# Complex angular contract: from simple spectrum to every start time

`complexAngularMartingaleProblem_of_simple : SimpleSpectrumAngular N r →
ComplexAngularMartingaleProblem N r`.
* `s > 0`: clause (b1) (`dysonNonCollision_holds`) gives simple spectrum of `H_{s+v}` for all
  `v ≥ 0` a.s.
* `s = 0`: on `A = {all gaps of H_0 > 1/n}` (an `𝓖_0`-set) keep `F`; off `A` the gap stop is
  `0` and the variable vanishes, and we replace `F` by a fixed matrix `D` with simple spectrum
  and the test by `0`. The new start has simple spectrum, the variables agree for every `ω`,
  and the new test is measurable for the new σ-algebra (`measurable_indicator_of_traceSigma`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

/-!
### Trace σ-algebras
-/

section Trace
variable {Ω : Type*}

/-- Sets whose trace on `A` is `m'`-measurable. -/
abbrev traceSigma (m' : MeasurableSpace Ω) {A : Set Ω} (hA : MeasurableSet[m'] A) :
    MeasurableSpace Ω where
  MeasurableSet' S := MeasurableSet[m'] (S ∩ A)
  measurableSet_empty := by simp
  measurableSet_compl S hS := by
    have : Sᶜ ∩ A = A \ (S ∩ A) := by ext; simp; tauto
    rw [this]; exact hA.diff hS
  measurableSet_iUnion S hS := by
    rw [iUnion_inter]; exact MeasurableSet.iUnion hS

theorem measurable_indicator_of_traceSigma {m m' : MeasurableSpace Ω} {A : Set Ω}
    (hA : MeasurableSet[m'] A) (hm : m ≤ traceSigma m' hA) {g : Ω → ℝ} (hg : Measurable[m] g) :
    Measurable[m'] (A.indicator g) := by
  intro B hB
  rw [indicator_preimage, Set.ite]
  refine MeasurableSet.union (hm _ (hg hB)) (MeasurableSet.diff ?_ hA)
  by_cases h0 : (0 : ℝ) ∈ B
  · convert @MeasurableSet.univ Ω m'; ext; simp [h0]
  · convert @MeasurableSet.empty Ω m'; ext; simp [h0]

end Trace

variable {N r : ℕ}

/-- The gap stop vanishes when the starting gap is at most `1/n`. -/
theorem gapStop_eq_zero {Ω : Type*} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0} {n : ℕ}
    {ω : Ω} {i j : Fin N} (hij : i ≠ j)
    (h : |dysonEigenvalue N (H (s + 0) ω) i - dysonEigenvalue N (H (s + 0) ω) j| ≤ 1 / (n : ℝ)) :
    gapStop N H s n ω = 0 := by
  have : gapStop N H s n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
    unfold gapStop; exact iInf₂_le (0 : ℝ≥0) ⟨i, j, hij, h⟩
  exact le_antisymm (by simpa using this) bot_le

theorem stoppedProcess_zero_stop {Ω E : Type*} (X : ℝ≥0 → Ω → E) {τ : Ω → WithTop ℝ≥0}
    {ω : Ω} (hτ : τ ω = 0) (u : ℝ≥0) : stoppedProcess X τ u ω = X 0 ω := by
  simp only [stoppedProcess, hτ]
  rw [min_eq_right zero_le]
  rfl

theorem complexAngularGenerator_zero (lam : Fin N → ℝ) (Z : AngularArray N r) :
    complexAngularGenerator N r lam (fun _ => 0) Z = 0 := by
  simp [complexAngularGenerator]

/-- **The contract from the simple-spectrum clause.** -/
theorem complexAngularMartingaleProblem_of_simple (h : SimpleSpectrumAngular N r) :
    ComplexAngularMartingaleProblem N r := by
  intro Ω _ Q _ 𝓖 G F hG hF hFh ev hev s V n hn f hf hfp hfm hfb u
  show Integrable (angVar F G ev s V n f u) Q ∧ ∫ ω, angVar F G ev s V n f u ω ∂Q = 0
  have hb1 := dysonNonCollision_holds N Ω Q 𝓖 G F hG hF hFh
  rcases (zero_le : (0 : ℝ≥0) ≤ s).lt_or_eq with hs | hs
  · -- `s > 0`: clause (b1)
    refine h Ω Q 𝓖 G F hG hF hFh ev hev s ?_ V n hn f hf hfp hfm hfb u
    filter_upwards [hb1] with ω hω v
    exact hω _ (add_pos_of_pos_of_nonneg hs zero_le)
  · -- `s = 0`: modify the start off `A`
    subst hs
    obtain ⟨ω₀, hω₀⟩ := hb1.exists
    set D := F ω₀ + G 1 ω₀
    have hDh : D.IsHermitian := (hFh ω₀).add (hG.hermitian 1 ω₀)
    have hDs : HasSimpleSpectrum N D := hω₀ 1 one_pos
    set A : Set Ω := {ω | ∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) <
      |dysonEigenvalue N (F ω + G 0 ω) i - dysonEigenvalue N (F ω + G 0 ω) j|}
    have hlam0 : ∀ i, Measurable[𝓖 0] fun ω => dysonEigenvalue N (F ω + G 0 ω) i := fun i =>
      (measurable_dysonEigenvalue i).comp (measurable_hermBM_add hG hF 0)
    have hA : MeasurableSet[𝓖 0] A := by
      have : A = ⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≠ j → 1 / (n : ℝ) <
          |dysonEigenvalue N (F ω + G 0 ω) i - dysonEigenvalue N (F ω + G 0 ω) j|} := by
        ext ω; simp [A]
      rw [this]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ne_eq, not_false_eq_true, forall_const]
        exact measurableSet_lt measurable_const
          (continuous_abs.measurable.comp ((hlam0 i).sub (hlam0 j)))
    classical
    set F' : Ω → Matrix (Fin N) (Fin N) ℂ := fun ω => if ω ∈ A then F ω else D
    set f' : Ω → AngularArray N r → ℝ := fun ω => if ω ∈ A then f ω else fun _ => 0
    have hF' : Measurable[𝓖 0] F' := Measurable.ite hA hF measurable_const
    have hF'h : ∀ ω, (F' ω).IsHermitian := fun ω => by
      simp only [F']; split_ifs; exacts [hFh ω, hDh]
    have hb1' := dysonNonCollision_holds N Ω Q 𝓖 G F' hG hF' hF'h
    have hsimple : ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, HasSimpleSpectrum N (F' ω + G (0 + v) ω) := by
      filter_upwards [hb1'] with ω hω v
      rcases (zero_le : (0 : ℝ≥0) ≤ v).lt_or_eq with hv | hv
      · exact hω _ (by simpa using hv)
      · subst hv
        simp only [add_zero]
        by_cases hωA : ω ∈ A
        · simp only [F', hωA, ite_true]
          exact hasSimpleSpectrum_of_gap (by positivity) fun i j hij => (hωA i j hij).le
        · simp only [F', hωA, ite_false, hG.zero, add_zero]; exact hDs
    -- the σ-algebras
    have hAm' : MeasurableSet[𝓖 0 ⊔ eigenPathSigma N F' G 0] A := le_sup_left (α := MeasurableSpace Ω) _ hA
    have hle : 𝓖 0 ⊔ eigenPathSigma N F G 0 ≤ traceSigma _ hAm' := by
      refine sup_le (fun S hS => le_sup_left (α := MeasurableSpace Ω) _ ((hS.inter hA))) ?_
      refine iSup_le fun v => ?_
      rintro _ ⟨B, hB, rfl⟩
      change MeasurableSet[𝓖 0 ⊔ eigenPathSigma N F' G 0]
        ((fun ω => dysonEigenvalue N (F ω + G (0 + v) ω)) ⁻¹' B ∩ A)
      have e : (fun ω => dysonEigenvalue N (F ω + G (0 + v) ω)) ⁻¹' B ∩ A =
          (fun ω => dysonEigenvalue N (F' ω + G (0 + v) ω)) ⁻¹' B ∩ A := by
        ext ω
        simp only [mem_inter_iff, mem_preimage]
        constructor
        · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩; simpa [F', h2] using h1
        · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩; simpa [F', h2] using h1
      rw [e]
      refine MeasurableSet.inter ?_ hAm'
      exact le_sup_right (α := MeasurableSpace Ω) _
        ((le_iSup (fun v => MeasurableSpace.comap
          (fun ω => dysonEigenvalue N (F' ω + G (0 + v) ω)) inferInstance) v) _ ⟨B, hB, rfl⟩)
    have hf'm : ∀ Z, Measurable[𝓖 0 ⊔ eigenPathSigma N F' G 0] fun ω => f' ω Z := by
      intro Z
      have e : (fun ω => f' ω Z) = A.indicator fun ω => f ω Z := by
        funext ω; by_cases hω : ω ∈ A <;> simp [f', hω]
      rw [e]
      exact measurable_indicator_of_traceSigma hAm' hle (hfm Z)
    have hf'b : ∀ R : ℝ, ∃ C : ℝ, ∀ ω Z, ‖Z‖ ≤ R →
        |f' ω Z| ≤ C ∧ ‖fderiv ℝ (f' ω) Z‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (f' ω)) Z‖ ≤ C := by
      intro R
      obtain ⟨C, hC⟩ := hfb R
      refine ⟨max C 0, fun ω Z hZ => ?_⟩
      by_cases hω : ω ∈ A
      · simp only [f', hω, ite_true]
        obtain ⟨h1, h2, h3⟩ := hC ω Z hZ
        exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
      · have e : f' ω = fun _ => 0 := by simp [f', hω]
        rw [e]
        simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, abs_zero]
        rw [ContinuousLinearMap.opNorm_zero, ContinuousLinearMap.opNorm_zero]
        exact ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩
    have hf'c : ∀ ω, ContDiff ℝ 2 (f' ω) := fun ω => by
      simp only [f']; split_ifs; exacts [hf ω, contDiff_const]
    have hf'p : ∀ ω, IsPhaseInvariant (f' ω) := fun ω => by
      simp only [f']; split_ifs
      · exact hfp ω
      · intro θ _ Z; rfl
    have key := h Ω Q 𝓖 G F' hG hF' hF'h ev hev 0 hsimple V n hn f' hf'c hf'p hf'm hf'b u
    have heq : angVar F G ev 0 V n f u = angVar F' G ev 0 V n f' u := by
      funext ω
      by_cases hω : ω ∈ A
      · have h1 : F' ω = F ω := by simp [F', hω]
        have h2 : f' ω = f ω := by simp [f', hω]
        simp only [angVar, stoppedProcess, gapStop, h1, h2]
      · have hτ : gapStop N (fun t ω => F ω + G t ω) 0 n ω = 0 := by
          simp only [A, mem_ofPred_eq, not_forall, not_lt] at hω
          obtain ⟨i, j, hij, hle⟩ := hω
          exact gapStop_eq_zero hij (by simpa using hle)
        have h2 : f' ω = fun _ => 0 := by simp [f', hω]
        rw [angVar, angVar, stoppedProcess_zero_stop _ hτ]
        simp only [stoppedProcess, h2, complexAngularGenerator_zero, integral_zero, sub_self]
        simp
    rw [heq]
    exact key

end BlockBand.SourceProcess.Stochastic.ComplexAngular
