module

public import BlockBand.SourceProcess.ContractingWords.CutSpec
public import BlockBand.SourceProcess.ContractingWords.PathStep
public import BlockBand.SourceProcess.ContractingWords.Alive
public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# The letters before the trace stop

Bounds on the letters of the trace load before the trace stop, and their dependence on the path.

* `letterMatrix_isHermitian`: `J`, `Q_a` are Hermitian (every path);
* `nuclearNorm_letter_le`: on `{j < σ_K}`, `j ≥ εW`: `Tr|A_ℓ| ≤ K` for every letter (`Q_a ⪰ 0`, so
  `Tr|Q_a| = Tr Q_a`; all terms of the trace load are nonnegative);
* `injCoef_le`: `|c_ℓ| ≤ c₀/W²`, `c₀` a bound of the interval tests;
* `letterMatrix_congr`: letters at length `j` depend only on `pathAt W j`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open Matrix BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.FullSource
open scoped ComplexOrder

variable {W nT nI : ℕ}

theorem nuclearNorm_of_posSemidef {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : nuclearNorm A = A.trace.re := by
  rw [nuclearNorm_eq_sum hA.1, hA.1.trace_eq_sum_eigenvalues, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (hA.eigenvalues_nonneg i)]; simp

theorem sourceLetter_posSemidef (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (a : Fin nT ⊕ Fin nI) :
    (letterMatrix b E k q W j ω (sourceLetter a)).PosSemidef := by
  obtain ⟨s, c, hc, he⟩ := sourceLetter_gram b E k q hq j ω a
  rw [he]
  exact posSemidef_sum s fun i hi =>
    (posSemidef_conjTranspose_mul_self _).smul (by exact_mod_cast hc i hi)

theorem letterMatrix_isHermitian (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) (j : ℕ) (ω : GrowthPath W) (ℓ : TraceLetter nT nI) :
    (letterMatrix b E k q W j ω ℓ).IsHermitian := by
  cases ℓ with
  | current => exact pathCurrent_isHermitian b E j ω
  | tag a => exact (sourceLetter_posSemidef b E k q hq j ω (Sum.inl a)).1
  | interval a => exact (sourceLetter_posSemidef b E k q hq j ω (Sum.inr a)).1

/-- **Letters before the stop.** On `{j < σ_K}` with `εW ≤ j`, every letter has `Tr|A_ℓ| ≤ K`. -/
theorem nuclearNorm_letter_le (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (hq : IsIntervalTests q) {K ε : ℝ} {j : ℕ} (hj : ε * W ≤ j) {ω : GrowthPath W}
    (hω : ω ∈ alive b E k q K ε W j) (ℓ : TraceLetter nT nI) :
    nuclearNorm (letterMatrix b E k q W j ω ℓ) ≤ K := by
  have hL : traceLoad b E k q W j ω ≤ K := by
    rw [alive_eq] at hω
    have := Set.mem_iInter₂.mp hω j (Finset.mem_range.mpr (Nat.lt_succ_self j))
    simp only [Set.mem_ofPred_eq, not_and, not_lt] at this
    exact this hj
  have hS : 0 ≤ ∑ a, sourceTrace b E k q W j ω a :=
    Finset.sum_nonneg fun a _ => sourceTrace_nonneg b E k q hq j ω a
  have hsrc : ∀ a, nuclearNorm (letterMatrix b E k q W j ω (sourceLetter a)) ≤ K := fun a => by
    rw [nuclearNorm_of_posSemidef (sourceLetter_posSemidef b E k q hq j ω a)]
    have h1 := sourceTrace_le_sum b E k q hq j ω a
    have h2 := nuclearNorm_nonneg (pathCurrent b E W j ω)
    simp only [traceLoad] at hL
    change sourceTrace b E k q W j ω a ≤ K
    linarith
  cases ℓ with
  | current =>
    have := nuclearNorm_nonneg (pathCurrent b E W j ω)
    simp only [traceLoad] at hL
    exact (le_add_of_nonneg_left hS).trans hL
  | tag a => exact hsrc (Sum.inl a)
  | interval a => exact hsrc (Sum.inr a)

theorem intervalTests_bounded {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ a x, |q a x| ≤ c₀ := by
  have h : ∀ a, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |q a x| ≤ M := fun a => by
    obtain ⟨s, T, h0, h1, h2⟩ := hq a
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
    refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
    by_cases hx : x ∈ Set.Icc s T
    · have := hM x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    · rw [h1 x hx, abs_zero]; exact le_max_right _ _
  choose M hM0 hM using h
  refine ⟨∑ a, M a, Finset.sum_nonneg fun a _ => hM0 a, fun a x => (hM a x).trans ?_⟩
  exact Finset.single_le_sum (fun a _ => hM0 a) (Finset.mem_univ a)

theorem injCoef_le {q : Fin nI → ℝ → ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (hq : ∀ a x, |q a x| ≤ c₀)
    (j : ℕ) (ℓ : TraceLetter nT nI) : |injCoef (nT := nT) q W j ℓ| ≤ c₀ / (W : ℝ) ^ 2 := by
  cases ℓ with
  | current => simp only [injCoef, abs_zero]; positivity
  | tag a => simp only [injCoef, abs_zero]; positivity
  | interval a =>
    simp only [injCoef, abs_div, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (hq a _) (by positivity)

theorem letterMatrix_congr (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    {ω ω' : GrowthPath W} (h : pathAt W j ω = pathAt W j ω') (ℓ : TraceLetter nT nI) :
    letterMatrix b E k q W j ω ℓ = letterMatrix b E k q W j ω' ℓ := by
  cases ℓ <;> simp only [letterMatrix, pathCurrent, scatteringMatrix, boundaryResolvent,
    fullInverse, fullPathMatrix, tagResponse, boundaryToInterior, intervalSource, h]

end BlockBand.SourceProcess.ContractingWords
