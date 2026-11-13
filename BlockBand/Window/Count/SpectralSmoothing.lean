module

public import Mathlib
public import BlockBand.Model.Construction.OrderedSpectrum
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Deterministic smoothing of the sharp negative count

* `spectralSum g M = Σ_j g(λ_j(M))` for Hermitian `M` (multiplicity counted); measurable in
  `M` for measurable `g` (`measurable_spectralSum`).
* `windowCount η M = #{j : |λ_j(M)| ≤ η}` (`= N([-η, η])`).
* `stepFn η = f_η`, `f_η(x) = smoothTransition((η - x)/(2η))`: `C^1` (indeed `C^∞`), values in
  `[0,1]`, equal to `1_{(-∞,0)}` off `[-η,η]`, and `|f_η'| ≤ K/η` with one absolute `K`
  (`stepFn_deriv_bound`), `f_η' = 0` off `[-η,η]`.
* `abs_negativeCount_sub_le`: `|N_-(M) - Tr f_η(M)| ≤ N_M([-η,η])`.
* `spectralSum_derivSq_le`: `Tr |f_η'(M)|^2 ≤ (K/η)^2 N_M([-η,η])`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
## Spectral sums
-/

/-- `Tr g(M) = Σ_j g(λ_j(M))` for Hermitian `M` (eigenvalues with multiplicity), `0` otherwise. -/
def spectralSum (g : ℝ → ℝ) (M : Matrix ι ι ℂ) : ℝ := by
  classical
  exact if h : M.IsHermitian then ∑ j, g (h.eigenvalues j) else 0

/-- `N_M([-η, η]) = #{j : |λ_j(M)| ≤ η}` for Hermitian `M`, `0` otherwise. -/
def windowCount (η : ℝ) (M : Matrix ι ι ℂ) : ℕ := by
  classical
  exact if h : M.IsHermitian then (Finset.univ.filter fun j => |h.eigenvalues j| ≤ η).card else 0

/-- Indicator of `[-η, η]`. -/
def windowInd (η : ℝ) (x : ℝ) : ℝ := if |x| ≤ η then 1 else 0

/-- Indicator of `(-∞, 0)`. -/
def negInd (x : ℝ) : ℝ := if x < 0 then 1 else 0

theorem windowCount_cast (η : ℝ) (M : Matrix ι ι ℂ) :
    (windowCount η M : ℝ) = spectralSum (windowInd η) M := by
  classical
  unfold windowCount spectralSum windowInd
  split_ifs with h
  · rw [Finset.card_filter]; push_cast; rfl
  · simp

theorem negativeCount_cast (M : Matrix ι ι ℂ) :
    (negativeCount M : ℝ) = spectralSum negInd M := by
  classical
  unfold negativeCount spectralSum negInd
  split_ifs with h
  · rw [Finset.card_filter]; push_cast; rfl
  · simp

theorem windowCount_le_card (η : ℝ) (M : Matrix ι ι ℂ) : windowCount η M ≤ Fintype.card ι := by
  classical
  unfold windowCount
  split_ifs
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · exact Nat.zero_le _

omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_isHermitian : IsClosed {M : Matrix ι ι ℂ | M.IsHermitian} :=
  isClosed_eq continuous_id.matrix_conjTranspose continuous_id

omit [DecidableEq ι] in
theorem measurableSet_isHermitian : MeasurableSet {M : Matrix ι ι ℂ | M.IsHermitian} :=
  isClosed_isHermitian.measurableSet

/-- Spectral sums of measurable functions are Borel measurable in the matrix. -/
theorem measurable_spectralSum {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (spectralSum g : Matrix ι ι ℂ → ℝ) := by
  classical
  have hsub : Measurable (fun A : {M : Matrix ι ι ℂ // M ∈ {M : Matrix ι ι ℂ | M.IsHermitian}} =>
      ∑ i : Fin (Fintype.card ι),
        g (BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i)) := by
    apply Finset.measurable_sum
    intro i _
    exact hg.comp (BlockBand.Model.Construction.measurable_increasingEigenvalue (ι := ι) i)
  have heq : (spectralSum g : Matrix ι ι ℂ → ℝ) = fun M =>
      if h : M ∈ {M : Matrix ι ι ℂ | M.IsHermitian} then
        (fun A : {M : Matrix ι ι ℂ // M ∈ {M : Matrix ι ι ℂ | M.IsHermitian}} =>
          ∑ i : Fin (Fintype.card ι),
            g (BlockBand.Foundations.Spectral.increasingEigenvalue A.2 i)) ⟨M, h⟩
      else (fun _ : {M : Matrix ι ι ℂ // M ∈ {M : Matrix ι ι ℂ | M.IsHermitian}ᶜ} => (0 : ℝ))
        ⟨M, h⟩ := by
    funext M
    unfold spectralSum
    by_cases h : M.IsHermitian
    · simp only [h, Set.mem_ofPred_eq, ↓reduceDIte]
      rw [← Equiv.sum_comp BlockBand.Foundations.Spectral.increasingIndex]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
    · simp only [h, Set.mem_ofPred_eq, ↓reduceDIte]
  rw [heq]
  exact Measurable.dite hsub measurable_const measurableSet_isHermitian

theorem measurable_windowInd (η : ℝ) : Measurable (windowInd η) := by
  unfold windowInd
  exact Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
    measurable_const measurable_const

theorem measurable_negInd : Measurable negInd := by
  unfold negInd
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem measurable_windowCount (η : ℝ) :
    Measurable (fun M : Matrix ι ι ℂ => windowCount η M) := by
  have h : Measurable (fun M : Matrix ι ι ℂ => (windowCount η M : ℝ)) := by
    simp_rw [windowCount_cast]; exact measurable_spectralSum (measurable_windowInd η)
  have heq : (fun M : Matrix ι ι ℂ => windowCount η M) =
      fun M => Nat.floor ((windowCount η M : ℝ)) := by
    funext M; rw [Nat.floor_natCast]
  rw [heq]; exact h.nat_floor

/-!
## Order and linearity of spectral sums
-/

theorem spectralSum_mono {g₁ g₂ : ℝ → ℝ} (h : ∀ x, g₁ x ≤ g₂ x) (M : Matrix ι ι ℂ) :
    spectralSum g₁ M ≤ spectralSum g₂ M := by
  classical
  unfold spectralSum
  split_ifs
  · exact Finset.sum_le_sum fun j _ => h _
  · exact le_rfl

theorem spectralSum_nonneg {g : ℝ → ℝ} (h : ∀ x, 0 ≤ g x) (M : Matrix ι ι ℂ) :
    0 ≤ spectralSum g M := by
  classical
  unfold spectralSum
  split_ifs
  · exact Finset.sum_nonneg fun j _ => h _
  · exact le_rfl

theorem spectralSum_const_mul (a : ℝ) (g : ℝ → ℝ) (M : Matrix ι ι ℂ) :
    spectralSum (fun x => a * g x) M = a * spectralSum g M := by
  classical
  unfold spectralSum
  split_ifs
  · rw [Finset.mul_sum]
  · simp

theorem abs_spectralSum_sub_le {g₁ g₂ g₃ : ℝ → ℝ} (h : ∀ x, |g₁ x - g₂ x| ≤ g₃ x)
    (M : Matrix ι ι ℂ) : |spectralSum g₁ M - spectralSum g₂ M| ≤ spectralSum g₃ M := by
  classical
  unfold spectralSum
  split_ifs
  · rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => h _)
  · simp

theorem abs_spectralSum_le {g : ℝ → ℝ} {B : ℝ} (h : ∀ x, |g x| ≤ B) (M : Matrix ι ι ℂ) :
    |spectralSum g M| ≤ Fintype.card ι * |B| := by
  classical
  unfold spectralSum
  split_ifs
  · calc _ ≤ ∑ j : ι, |B| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => (h _).trans (le_abs_self B))
      _ = Fintype.card ι * |B| := by simp
  · simp only [abs_zero]; positivity

/-!
## The smooth step `f_η`
-/

/-- `f_η(x) = smoothTransition((η - x)/(2η))`: `1` on `(-∞, -η]`, `0` on `[η, ∞)`. -/
def stepFn (η : ℝ) (x : ℝ) : ℝ := Real.smoothTransition ((η - x) / (2 * η))

theorem stepFn_nonneg (η x : ℝ) : 0 ≤ stepFn η x := Real.smoothTransition.nonneg _

theorem stepFn_le_one (η x : ℝ) : stepFn η x ≤ 1 := Real.smoothTransition.le_one _

theorem stepFn_of_le {η x : ℝ} (hη : 0 < η) (hx : x ≤ -η) : stepFn η x = 1 := by
  unfold stepFn
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem stepFn_of_ge {η x : ℝ} (hη : 0 < η) (hx : η ≤ x) : stepFn η x = 0 := by
  unfold stepFn
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

theorem contDiff_stepFn (η : ℝ) : ContDiff ℝ 1 (stepFn η) := by
  unfold stepFn
  exact (Real.smoothTransition.contDiff (n := 1)).comp
    ((contDiff_const.sub contDiff_id).div_const _)

theorem continuous_stepFn (η : ℝ) : Continuous (stepFn η) := (contDiff_stepFn η).continuous

theorem hasDerivAt_stepFn (η x : ℝ) :
    HasDerivAt (stepFn η)
      (deriv Real.smoothTransition ((η - x) / (2 * η)) * (-1 / (2 * η))) x := by
  have hin : HasDerivAt (fun x : ℝ => (η - x) / (2 * η)) (-1 / (2 * η)) x := by
    simpa using ((hasDerivAt_id x).const_sub η).div_const (2 * η)
  have hout : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((η - x) / (2 * η))) ((η - x) / (2 * η)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  exact hout.comp x hin

theorem deriv_smoothTransition_eq_zero {y : ℝ} (hy : y < 0 ∨ 1 < y) :
    deriv Real.smoothTransition y = 0 := by
  rcases hy with hy | hy
  · have : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hy) fun z hz => Real.smoothTransition.zero_of_nonpos (le_of_lt hz)
    rw [this.deriv_eq, deriv_const]
  · have : Real.smoothTransition =ᶠ[𝓝 y] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hy) fun z hz => Real.smoothTransition.one_of_one_le (le_of_lt hz)
    rw [this.deriv_eq, deriv_const]

theorem exists_deriv_smoothTransition_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |deriv Real.smoothTransition y| ≤ K := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨K, hK0, fun y => ?_⟩
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [Real.norm_eq_abs] using hK y hy
  · have : y < 0 ∨ 1 < y := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy; exact hy
    rw [deriv_smoothTransition_eq_zero this, abs_zero]
    exact hK0

/-- One absolute `K` with `|f_η'| ≤ K/η` for every `η > 0`. -/
theorem stepFn_deriv_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → ∀ x, |deriv (stepFn η) x| ≤ K / η := by
  obtain ⟨K, hK0, hK⟩ := exists_deriv_smoothTransition_bound
  refine ⟨K, hK0, fun η hη x => ?_⟩
  rw [(hasDerivAt_stepFn η x).deriv, abs_mul]
  have h2 : |(-1 / (2 * η))| = 1 / (2 * η) := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
  rw [h2]
  calc |deriv Real.smoothTransition ((η - x) / (2 * η))| * (1 / (2 * η))
      ≤ K * (1 / (2 * η)) := by gcongr; exact hK _
    _ ≤ K / η := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hK0 hη (by linarith)

theorem deriv_stepFn_eq_zero {η x : ℝ} (hη : 0 < η) (hx : η < |x|) :
    deriv (stepFn η) x = 0 := by
  rw [(hasDerivAt_stepFn η x).deriv]
  have : (η - x) / (2 * η) < 0 ∨ 1 < (η - x) / (2 * η) := by
    rcases lt_abs.mp hx with h | h
    · left; apply div_neg_of_neg_of_pos <;> linarith
    · right; rw [lt_div_iff₀ (by positivity)]; linarith
  rw [deriv_smoothTransition_eq_zero this, zero_mul]

/-!
## The two deterministic comparisons
-/

theorem abs_negInd_sub_stepFn_le {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |negInd x - stepFn η x| ≤ windowInd η x := by
  unfold windowInd
  split_ifs with hx
  · have h0 := stepFn_nonneg η x
    have h1 := stepFn_le_one η x
    unfold negInd
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rcases lt_abs.mp (not_le.mp hx) with h | h
    · rw [stepFn_of_ge hη h.le]; simp [negInd, show ¬ x < 0 by linarith]
    · rw [stepFn_of_le hη (by linarith)]; simp [negInd, show x < 0 by linarith]

theorem derivSq_stepFn_le {η K : ℝ} (hη : 0 < η) (hK : ∀ x, |deriv (stepFn η) x| ≤ K / η)
    (x : ℝ) : deriv (stepFn η) x ^ 2 ≤ (K / η) ^ 2 * windowInd η x := by
  unfold windowInd
  split_ifs with hx
  · rw [mul_one, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2
  · rw [deriv_stepFn_eq_zero hη (not_le.mp hx)]; simp

/-- `|N_-(M) - Tr f_η(M)| ≤ N_M([-η,η])`, every matrix `M`, every `η > 0`. -/
theorem abs_negativeCount_sub_le {η : ℝ} (hη : 0 < η) (M : Matrix ι ι ℂ) :
    |(negativeCount M : ℝ) - spectralSum (stepFn η) M| ≤ windowCount η M := by
  rw [negativeCount_cast, windowCount_cast]
  exact abs_spectralSum_sub_le (abs_negInd_sub_stepFn_le hη) M

/-- `Tr |f_η'(M)|^2 ≤ (K/η)^2 N_M([-η,η])`, every matrix `M`, every `η > 0`. -/
theorem spectralSum_derivSq_le {η K : ℝ} (hη : 0 < η) (hK : ∀ x, |deriv (stepFn η) x| ≤ K / η)
    (M : Matrix ι ι ℂ) :
    spectralSum (fun x => deriv (stepFn η) x ^ 2) M ≤ (K / η) ^ 2 * windowCount η M := by
  rw [windowCount_cast, ← spectralSum_const_mul]
  exact spectralSum_mono (derivSq_stepFn_le hη hK) M

end BlockBand.Window.Count
