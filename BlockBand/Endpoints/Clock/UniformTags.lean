module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Coarea.ProjectiveHaar
public import Mathlib.Analysis.Matrix.Order

/-!
# The uniform clock-tags corollary, Palm part, from the two-positive-clocks lemma

`UniformClockTagsPalmContract` follows from the Palm part of the two-positive-clocks lemma
(`TwoPositiveClocksPalmContract`), with no other input. With `a_j = q Tr(ΓD_j)/Tr(ΓD)`,
`q⁻¹ Σ_j a_j = 1`, so at most a fraction `1/K` of the tags has `a_j > K`; each such tag costs at
most `2‖Φ‖`; on the others the lemma applies with `C = qD_j`, `Tr(ΓC) ≤ KT`, uniformly. Choose `K`
after `ε`.

Supporting facts: `Tr(ΓD) ≥ 0` for positive semidefinite `Γ, D`; `freshGamma` is positive
semidefinite for `c₀ ≥ 0`; `|Â[φ]| ≤ B` whenever `|φ| ≤ B`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal ComplexOrder Matrix BoundedContinuousFunction

variable {N : ℕ}

/-- `Re Tr(ΓD) ≥ 0` for positive semidefinite `Γ` and `D`. -/
theorem traceAgainst_nonneg {Γ D : Matrix (Fin N) (Fin N) ℂ} (hΓ : Γ.PosSemidef)
    (hD : D.PosSemidef) : 0 ≤ traceAgainst Γ D := by
  classical
  open scoped MatrixOrder in
  obtain ⟨X, hX, -, hXX⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hD.isHermitian (QuasispectrumRestricts.nnreal_of_nonneg hD.nonneg)
  have hXs : Xᴴ = X := hX
  have htr : (Γ * D).trace = (Xᴴ * Γ * X).trace := by
    rw [← hXX, hXs, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  have h0 : 0 ≤ (Xᴴ * Γ * X).trace := (hΓ.conjTranspose_mul_mul_same X).trace_nonneg
  unfold traceAgainst
  rw [htr]
  exact (Complex.nonneg_iff.mp h0).1

/-- `Γ = c₀ |F - E - c₀ m|^{-2}` is positive semidefinite for `c₀ ≥ 0`. -/
theorem freshGamma_posSemidef (F : Matrix (Fin N) (Fin N) ℂ) {c₀ : ℝ} (hc : 0 ≤ c₀) (E : ℝ) :
    (freshGamma F c₀ E).PosSemidef := by
  classical
  unfold freshGamma
  exact (posSemidef_conjTranspose_mul_self _).inv.smul (by exact_mod_cast hc)

/-- The scalar Palm weight is integrable under the traceless law. -/
theorem integrable_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N) :
    Integrable (fun A0 => palmWeight F c₀ E ℓ A0) (freshTracelessLaw N c₀) := by
  refine Integrable.mono' (integrable_const
    (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹)
    (BlockBand.Coarea.FreshPalm.measurable_palmWeight F c₀ E ℓ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun A0 => ?_
  unfold palmWeight
  rw [Real.norm_eq_abs, abs_of_nonneg (BlockBand.Palm.scalarWeight_nonneg _ _ _ _)]
  exact BlockBand.Palm.scalarWeight_le_prefactor _ _ _ _

/-- `|Â[φ]| ≤ B` whenever `|φ| ≤ B` (no measurability of `φ` is needed). -/
theorem abs_palmExpect_le (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (φ : (Fin N → ℂ) → ℝ)
    (B : ℝ) (hB : ∀ v, |φ v| ≤ B) : |palmExpect F c₀ E φ| ≤ B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hw0 : ∀ ℓ A0, 0 ≤ palmWeight F c₀ E ℓ A0 := fun _ _ =>
    BlockBand.Palm.scalarWeight_nonneg _ _ _ _
  have hZ0 : 0 ≤ palmMass F c₀ E :=
    Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 => hw0 ℓ A0
  have hterm : ∀ ℓ : Fin N,
      |∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ) ∂freshTracelessLaw N c₀| ≤
        B * ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀ := by
    intro ℓ
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ((integrable_palmWeight F c₀ E ℓ).const_mul B) (Filter.Eventually.of_forall fun A0 => ?_)
    dsimp only
    rw [abs_mul, abs_of_nonneg (hw0 ℓ A0), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (hw0 ℓ A0)
  have hS : |∑ ℓ : Fin N, ∫ A0, palmWeight F c₀ E ℓ A0 * φ (freshEigenvector (F + A0) ℓ)
      ∂freshTracelessLaw N c₀| ≤ B * palmMass F c₀ E := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold palmMass
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ _ => hterm ℓ
  unfold palmExpect
  rcases hZ0.eq_or_lt with hZ | hZ
  · rw [← hZ, div_zero, abs_zero]; exact hB0
  · rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]; exact hS

/-- `|E_g φ(g)| ≤ B` whenever `|φ| ≤ B`. -/
theorem abs_integral_circular_le (φ : (Fin N → ℂ) → ℝ) (B : ℝ) (hB : ∀ v, |φ v| ≤ B) :
    |∫ g, φ g ∂circularVectorLaw (Fin N)| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := circularVectorLaw (Fin N))
    (f := φ) (C := B) (Filter.Eventually.of_forall fun v => by simpa using hB v)
  simpa [probReal_univ] using h

/-- `Tr(Γ Σ_j D_j) = Σ_j Tr(ΓD_j)`. -/
theorem traceAgainst_sum {q : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ)
    (Dt : Fin q → Matrix (Fin N) (Fin N) ℂ) :
    traceAgainst Γ (∑ j, Dt j) = ∑ j, traceAgainst Γ (Dt j) := by
  unfold traceAgainst
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- `Tr(Γ (q•D)) = q Tr(ΓD)` for real `q`. -/
theorem traceAgainst_smul (Γ D : Matrix (Fin N) (Fin N) ℂ) (q : ℝ) :
    traceAgainst Γ ((q : ℂ) • D) = q * traceAgainst Γ D := by
  unfold traceAgainst
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- Counting: if `a_j ≥ 0` and `Σ_j a_j ≤ q·T`, `T > 0`, `K > 0`, then the number of tags with
`a_j > K T` is at most `q/K`. -/
theorem card_bad_le {q : ℕ} (a : Fin q → ℝ) (ha : ∀ j, 0 ≤ a j) (T K : ℝ) (hT : 0 < T)
    (hK : 0 < K) (hsum : ∑ j, a j ≤ q * T) :
    ((Finset.univ.filter fun j => K * T < a j).card : ℝ) ≤ q / K := by
  classical
  set S := Finset.univ.filter fun j => K * T < a j
  have h1 : (S.card : ℝ) * (K * T) ≤ ∑ j ∈ S, a j := by
    have := Finset.card_nsmul_le_sum S a (K * T) fun j hj => (Finset.mem_filter.mp hj).2.le
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ j ∈ S, a j ≤ ∑ j, a j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => ha j
  rw [le_div_iff₀ hK]
  have : (S.card : ℝ) * K * T ≤ q * T := by nlinarith
  exact le_of_mul_le_mul_right (by linarith) hT

/-- **Uniform clock tags, Palm part** (`UniformClockTagsPalmContract`), from the two-positive-clocks
lemma `TwoPositiveClocksPalmContract`. -/
theorem uniformClockTagsPalm_of_twoPositiveClocks (h : TwoPositiveClocksPalmContract) :
    UniformClockTagsPalmContract := by
  intro A c₀ r₀ s₀ v₀ hc Φ ε hε
  set B := ‖Φ‖ with hBdef
  have hB0 : 0 ≤ B := norm_nonneg _
  set K : ℝ := 4 * B / ε + 1 with hKdef
  have hK : 0 < K := by positivity
  have hKε : 4 * B ≤ ε * K := by
    rw [hKdef, mul_add, mul_div_assoc', mul_comm ε (4 * B), mul_div_assoc, div_self hε.ne',
      mul_one, mul_one]
    linarith
  obtain ⟨N₀, hN₀⟩ := h.ratio A c₀ r₀ s₀ v₀ hc K Φ (ε / 2) (by positivity)
  refine ⟨N₀, fun N hN hNpos F E hF q hq Dt hDt hT M hM d hd => ?_⟩
  classical
  set Γ := freshGamma F c₀ E with hΓdef
  set D := ∑ j, Dt j with hDdef
  set T := traceAgainst Γ D with hTdef
  have hΓ : Γ.PosSemidef := freshGamma_posSemidef F hc.1.le E
  have hD : D.PosSemidef := by
    rw [hDdef]
    exact Finset.sum_induction _ (fun X : Matrix (Fin N) (Fin N) ℂ => X.PosSemidef)
      (fun _ _ h₁ h₂ => h₁.add h₂) PosSemidef.zero fun j _ => hDt j
  -- the per-tag differences
  set P : Fin q → ℝ := fun j =>
    palmExpect F c₀ E (fun v => Φ (ratioHalfLine ((q : ℂ) • Dt j) D d v)) with hPdef
  set G : Fin q → ℝ := fun j =>
    ∫ g, Φ (ratioHalfLine ((q : ℂ) • Dt j) D d (M *ᵥ g)) ∂circularVectorLaw (Fin N) with hGdef
  have hΦB : ∀ x, |Φ x| ≤ B := fun x => by
    simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm x
  have hP : ∀ j, |P j| ≤ B := fun j => abs_palmExpect_le F c₀ E _ B fun v => hΦB _
  have hG : ∀ j, |G j| ≤ B := fun j => abs_integral_circular_le _ B fun v => hΦB _
  -- tag weights `a_j = q Tr(ΓD_j)`
  set a : Fin q → ℝ := fun j => (q : ℝ) * traceAgainst Γ (Dt j) with hadef
  have ha : ∀ j, 0 ≤ a j := fun j => mul_nonneg (Nat.cast_nonneg _)
    (traceAgainst_nonneg hΓ (hDt j))
  have hasum : ∑ j, a j ≤ q * T := by
    rw [hTdef, hDdef, traceAgainst_sum, Finset.mul_sum]
  have hgood : ∀ j, ¬ (K * T < a j) → |P j - G j| ≤ ε / 2 := by
    intro j hj
    have hC : ((q : ℂ) • Dt j).PosSemidef := (hDt j).smul (by exact_mod_cast (Nat.cast_nonneg q))
    have hCT : traceAgainst Γ ((q : ℂ) • Dt j) ≤ K * T := by
      have : ((q : ℝ) : ℂ) = (q : ℂ) := by norm_cast
      rw [← this, traceAgainst_smul]
      exact not_lt.mp hj
    exact hN₀ N hN hNpos F E hF D ((q : ℂ) • Dt j) hD hC hT hCT M hM d hd
  have hbad : ∀ j, |P j - G j| ≤ 2 * B := fun j =>
    (abs_sub _ _).trans (by linarith [hP j, hG j])
  -- split the sum
  have hsplit : ∑ j, |P j - G j| ≤ q * (ε / 2) +
      ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => K * T < a j)]
    have hb : ∑ j ∈ Finset.univ.filter (fun j => K * T < a j), |P j - G j| ≤
        ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter fun j => K * T < a j)
        (fun j => |P j - G j|) (2 * B) fun j _ => hbad j
      simpa [nsmul_eq_mul] using this
    have hg : ∑ j ∈ Finset.univ.filter (fun j => ¬ K * T < a j), |P j - G j| ≤ q * (ε / 2) := by
      have := Finset.sum_le_card_nsmul (Finset.univ.filter fun j => ¬ K * T < a j)
        (fun j => |P j - G j|) (ε / 2) fun j hj => hgood j (Finset.mem_filter.mp hj).2
      have hcard : ((Finset.univ.filter fun j => ¬ K * T < a j).card : ℝ) ≤ q := by
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      simp only [nsmul_eq_mul] at this
      nlinarith
    linarith
  have hcount := card_bad_le a ha T K hT hK hasum
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  -- conclude
  have hdiff : (q : ℝ)⁻¹ * ∑ j, P j - (q : ℝ)⁻¹ * ∑ j, G j =
      (q : ℝ)⁻¹ * ∑ j, (P j - G j) := by
    rw [← mul_sub, Finset.sum_sub_distrib]
  show |(q : ℝ)⁻¹ * ∑ j, P j - (q : ℝ)⁻¹ * ∑ j, G j| ≤ ε
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hqpos)]
  have h3 : |∑ j, (P j - G j)| ≤ ∑ j, |P j - G j| := Finset.abs_sum_le_sum_abs _ _
  have h4 : ((Finset.univ.filter fun j => K * T < a j).card : ℝ) * (2 * B) ≤
      (q / K) * (2 * B) := mul_le_mul_of_nonneg_right hcount (by positivity)
  have h5 : (q / K) * (2 * B) ≤ q * (ε / 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith
  rw [inv_mul_le_iff₀ hqpos]
  linarith

end BlockBand.Endpoints.Clock
