module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeGlobal
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Global strong solutions for Lipschitz bounded coefficients

`Ω = DriverSample S κ`, `P = driverLaw μ`, augmented filtration `F_t ∨ N`, coefficients
`c : LipCoeff κ E`, `F_0 ∨ N`-measurable `ξ`.

`GlobalLipSol μ c ξ X`: `X` is `F_t ∨ N`-adapted with everywhere continuous paths, `X_0 = ξ`,
and for **every** horizon `T` and augmented stopping time `ρ` it satisfies the identity
(`StoppedIdentity`) with drift `b(X)` and diffusion `σ(X)`.

`exists_globalLipSol`: such an `X` exists. The horizon-`n` solutions (`exists_strongSolOn`) agree
a.s. on `[0,n]` (`strongSolOn_agree`); on the full-measure set where all of them agree we set
`X_t = X^{⌈t⌉}_t`, and `ξ` elsewhere.
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion
open BlockBand.SourceProcess.Stochastic.Integral

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (μ) in
/-- Global strong solution for Lipschitz bounded coefficients (see the module docstring). -/
def GlobalLipSol (c : LipCoeff κ E) (ξ : DriverSample S κ → E)
    (X : ℝ≥0 → DriverSample S κ → E) : Prop :=
  (∀ t, StronglyMeasurable[driverAugmented (κ := κ) μ t] (X t)) ∧
    (∀ x, Continuous fun t => X t x) ∧ (∀ x, X 0 x = ξ x) ∧
    ∀ (T : ℝ≥0) (ρ : DriverSample S κ → WithTop ℝ≥0),
      IsStoppingTime (driverAugmented (κ := κ) μ) ρ →
        StoppedIdentity μ T ρ X (fun t x => c.b (X t x)) (fun a t x => c.σ a (X t x))

/-- **Global existence** for Lipschitz bounded coefficients and any `F_0 ∨ N`-measurable `ξ`. -/
theorem exists_globalLipSol (c : LipCoeff κ E) {ξ : DriverSample S κ → E}
    (hξ : StronglyMeasurable[driverAugmented (κ := κ) μ 0] ξ) : ∃ X, GlobalLipSol μ c ξ X := by
  classical
  choose Xn hXn using fun n : ℕ => exists_strongSolOn c hξ (N := (n : ℝ≥0))
  have hagree : ∀ᵐ x ∂driverLaw (κ := κ) μ,
      ∀ n m : ℕ, n ≤ m → ∀ t ≤ (n : ℝ≥0), Xn n t x = Xn m t x := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    by_cases hnm : n ≤ m
    · filter_upwards [strongSolOn_agree c (Nat.cast_le.2 hnm) (hXn n) (hXn m)] with x hx _ t ht
      exact hx t ht
    · exact Eventually.of_forall fun x h => absurd h hnm
  obtain ⟨G, hGm, hG0, hGa⟩ := exists_good_set μ hagree
  have hGae : ∀ᵐ x ∂driverLaw (κ := κ) μ, x ∈ G := by
    rw [ae_iff]
    simpa only [compl_def] using hG0
  let X : ℝ≥0 → DriverSample S κ → E := fun t => G.piecewise (Xn ⌈t⌉₊ t) ξ
  have hkey : ∀ x ∈ G, ∀ m : ℕ, ∀ t ≤ (m : ℝ≥0), X t x = Xn m t x := by
    intro x hx m t ht
    simp only [X, Set.piecewise_eq_of_mem _ _ _ hx]
    exact hGa x hx ⌈t⌉₊ m (Nat.ceil_le.2 ht) t (Nat.le_ceil t)
  refine ⟨X, fun t => ?_, fun x => ?_, fun x => ?_, fun T ρ hρ => ?_⟩
  · exact StronglyMeasurable.piecewise (measurableSet_aug_of_full μ hGm hG0 t) ((hXn _).1 t)
      (hξ.mono ((driverAugmented (κ := κ) μ).mono zero_le))
  · by_cases hx : x ∈ G
    · refine continuous_iff_continuousAt.2 fun t₀ => ?_
      set m : ℕ := ⌈t₀⌉₊ + 1
      have hlt : t₀ < (m : ℝ≥0) := (Nat.le_ceil t₀).trans_lt (by simp [m])
      refine ((hXn m).2.1 x).continuousAt.congr ?_
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact (hkey x hx m t (le_of_lt ht)).symm
    · have : (fun t => X t x) = fun _ => ξ x := by
        funext t
        simp only [X, Set.piecewise_eq_of_notMem _ _ _ hx]
      rw [this]
      exact continuous_const
  · by_cases hx : x ∈ G
    · rw [hkey x hx 0 0 (by simp)]
      exact (hXn 0).2.2.1 x
    · simp only [X, Set.piecewise_eq_of_notMem _ _ _ hx]
  · have h := (stoppedIdentity_of_strongSolOn (hXn ⌈T⌉₊) hρ).mono (Nat.le_ceil T)
    refine h.congr ?_
    filter_upwards [hGae] with x hx t ht
    exact hkey x hx _ t (ht.trans (Nat.le_ceil T))

end BlockBand.SourceProcess.Stochastic.NativeSDE
