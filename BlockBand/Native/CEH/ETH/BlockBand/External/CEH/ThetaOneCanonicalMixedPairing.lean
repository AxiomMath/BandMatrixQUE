module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneHorizontalBoundaryModulus

/-!
# Canonical-height arithmetic and mixed-pairing transport

This module packages the exact two decay scales forced by the published
exponents: the canonical vertical scale `N^(ξ-1)` and the two-energy source
scale `N^(β-1)`.  It proves the strict CEH perturbation budget eventually and
transports the resulting scalar mixed pairing through the Hermitian spectral
lift and conjugate transpose, with no change of normalized trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set
open scoped Topology Matrix.Norms.L2Operator ComplexConjugate

/-- Explicit upper bound for one canonical CEH height after the density lower
bound `c/(2π)` has been inserted into the exact spacing equation. -/
def canonicalHeightRate (N : ℕ) (ξ c : ℝ) : ℝ :=
  (2 * Real.pi / c) * (N : ℝ) ^ (ξ - 1)

/-- The vertical entry error obtained by inserting `canonicalHeightRate` into
the exact first-exit entry modulus. -/
def canonicalVerticalEntryRate (N : ℕ) (ξ s c : ℝ) : ℝ :=
  let h := canonicalHeightRate N ξ c
  (h + s * (8 * h / (s ^ 2 * c ^ 3))) *
    (s * c / 2)⁻¹ * (s * c)⁻¹

/-- The horizontal boundary-entry error at the exact published source-window
separation `2 N^(β-1)`. -/
def sourceHorizontalEntryRate (N : ℕ) (β s c K : ℝ) : ℝ :=
  (1 + s * K) * (2 * (N : ℝ) ^ (β - 1)) * (s * c)⁻¹ ^ 2

/-- A single common-boundary error budget for both canonical source points. -/
def canonicalMixedEntryRate (N : ℕ) (ξ β s c K : ℝ) : ℝ :=
  canonicalVerticalEntryRate N ξ s c +
    sourceHorizontalEntryRate N β s c K

/-- The exact canonical vertical scale tends to zero for `ξ<1`. -/
theorem tendsto_canonicalHeightRate
    {ξ c : ℝ} (hξ : ξ < 1) :
    Tendsto (fun N : ℕ => canonicalHeightRate N ξ c) atTop (nhds 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (ξ - 1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hξ)).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    · funext N
      congr 1
      ring
  unfold canonicalHeightRate
  simpa using (tendsto_const_nhds.mul hp)

/-- Both exact published decay scales vanish, hence so does their assembled
entry error. -/
theorem tendsto_canonicalMixedEntryRate
    {ξ β s c K : ℝ} (hξ : ξ < 1) (hβ : β < 1) :
    Tendsto (fun N : ℕ => canonicalMixedEntryRate N ξ β s c K)
      atTop (nhds 0) := by
  have hv0 := tendsto_canonicalHeightRate (c := c) hξ
  have hv : Tendsto (fun N : ℕ => canonicalVerticalEntryRate N ξ s c)
      atTop (nhds 0) := by
    let C : ℝ := (1 + s * (8 / (s ^ 2 * c ^ 3))) *
      (s * c / 2)⁻¹ * (s * c)⁻¹
    have hC : Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    convert hC.mul hv0 using 1
    · funext N
      simp only [canonicalVerticalEntryRate]
      simp only [C]
      ring
    · simp
  have hhpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (β - 1))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp
      tendsto_natCast_atTop_atTop
    convert h using 1
    · funext N
      congr 1
      ring
  have hh : Tendsto (fun N : ℕ => sourceHorizontalEntryRate N β s c K)
      atTop (nhds 0) := by
    let C : ℝ := (1 + s * K) * 2 * (s * c)⁻¹ ^ 2
    have hC : Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    convert hC.mul hhpow using 1
    · funext N
      simp only [sourceHorizontalEntryRate]
      simp only [C]
      ring
    · simp
  simpa [canonicalMixedEntryRate] using hv.add hh

/-- Under the exact published exponent restrictions, the explicit assembled
entry rate eventually satisfies the strict theta-one perturbation budget. -/
theorem eventually_canonicalMixedEntryRate_budget
    {ξ β s c K : ℝ} (_hs : 0 < s) (hξβ : ξ < β) (hβ : β ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2 := by
  have hξ : ξ < 1 := lt_of_lt_of_le hξβ (hβ.trans (by norm_num))
  have hβ1 : β < 1 := lt_of_le_of_lt hβ (by norm_num)
  have hd := tendsto_canonicalMixedEntryRate
    (s := s) (c := c) (K := K) hξ hβ1
  have hlin : Tendsto (fun N : ℕ =>
      (2 * (s * c)⁻¹) * canonicalMixedEntryRate N ξ β s c K)
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => 2 * (s * c)⁻¹)
        atTop (nhds (2 * (s * c)⁻¹)) := tendsto_const_nhds
    simpa using hconst.mul hd
  have hsq : Tendsto (fun N : ℕ =>
      canonicalMixedEntryRate N ξ β s c K ^ 2)
      atTop (nhds 0) := by simpa using hd.pow 2
  have hsum := hlin.add hsq
  have hbudget : Tendsto (fun N : ℕ =>
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => s) atTop (nhds s) :=
      tendsto_const_nhds
    simpa [mul_assoc] using hconst.mul hsum
  exact hbudget.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

/-- The exact spacing equation and the first-exit density lower bound give the
promised explicit `O(N^(ξ-1))` canonical-height estimate. -/
theorem canonicalHeight_le_rate_of_boundaryData
    {N : ℕ} (hN : 4 ≤ N) (f : DeformationSpectrum N)
    {s c x ξ : ℝ} (hs : 0 < s) (hc : 0 < c) (hξ₀ : 0 ≤ ξ)
    {m₀ : ℂ} (hm₀sol : IsSolution f s (x : ℂ) m₀)
    (hm₀im : c ≤ m₀.im)
    (hm₀stab : c ≤ ‖stabilityDenominator f s (x : ℂ) m₀‖)
    (hboundary : Tendsto
      (fun η : ℝ => upperBranch (by omega) f hs
        ((x : ℂ) + (η : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds m₀))
    (hlarge : 1 < (N : ℝ) *
      (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi))) :
    (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x ≤
      canonicalHeightRate N ξ c := by
  let η := cehTypicalSpacing N hN f hs x
  have hη : 0 < η := (cehTypicalSpacing_spec N hN f hs x).1
  have hcut : (N : ℝ) ^ ξ * η < quantitativeIFTHeight s c :=
    canonicalHeight_lt_quantitativeIFTHeight_of_boundaryData
      hN f hs hc hξ₀ hm₀sol hm₀im hm₀stab hboundary hlarge
  have hNpow : 0 < (N : ℝ) ^ ξ := by
    positivity
  have hηcut : η ≤ quantitativeIFTHeight s c := by
    have hpow : 1 ≤ (N : ℝ) ^ ξ := by
      exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hξ₀
    nlinarith
  have hclose := upperBranch_close_boundary_below_quantitativeIFTHeight
    (by omega) f hs hc hm₀sol hm₀im hm₀stab hboundary η hη hηcut
  have hdensity := density_upperBranch_ge_of_close_boundary
    (by omega) f hs hc hm₀im hη
    (hclose.trans_le
      (quantitativeIFTRadius_height_spec hs hc).2.2.1)
  have hspacing := (cehTypicalSpacing_spec N hN f hs x).2
  rw [spacingQuantity, ite_eq_left hη] at hspacing
  have hηbound : η ≤ (2 * Real.pi) / ((N : ℝ) * c) := by
    have hmul := mul_le_mul_of_nonneg_left hdensity
      (mul_nonneg (Nat.cast_nonneg N) hη.le)
    rw [hspacing] at hmul
    apply (le_div_iff₀ (by positivity : 0 < (N : ℝ) * c)).2
    have hp : 0 < Real.pi := Real.pi_pos
    field_simp [Real.pi_ne_zero] at hmul ⊢
    nlinarith
  have hNpos : 0 < (N : ℝ) := by positivity
  calc
    (N : ℝ) ^ ξ * η ≤
        (N : ℝ) ^ ξ * ((2 * Real.pi) / ((N : ℝ) * c)) := by
      gcongr
    _ = canonicalHeightRate N ξ c := by
      unfold canonicalHeightRate
      rw [Real.rpow_sub hNpos, Real.rpow_one]
      field_simp [hNpos.ne', hc.ne']

end CEHNative.BlockBand.CEH

namespace CEHNative.BlockBand.External.CEH

open Matrix
open CEHNative.BlockBand
open CEHNative.BlockBand.CEH
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- Conjugate transpose of a Hermitian spectral lift is pointwise star in the
same spectral basis. -/
theorem spectralLift_conjTranspose {N : ℕ} {F : LocalETHMatrix N}
    (hF : F.IsHermitian) (q : Fin N → ℂ) :
    (spectralLift hF q)ᴴ = spectralLift hF (fun i => star (q i)) := by
  unfold spectralLift
  rw [← star_eq_conjTranspose, ← map_star]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij, Ne.symm hij]

/-- Exact normalized-trace transport for the mixed pairing with the second
matrix conjugate-transposed. -/
theorem NTrace_spectralLift_mul_conjTranspose {N : ℕ}
    {F : LocalETHMatrix N} (hF : F.IsHermitian) (q₁ q₂ : Fin N → ℂ) :
    NTrace (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ) =
      average (fun i => q₁ i * star (q₂ i)) := by
  rw [spectralLift_conjTranspose hF q₂]
  change Conventions.normalizedTrace
      (spectralLift hF q₁ * spectralLift hF (fun i => star (q₂ i))) = _
  rw [normalizedTrace_spectralLift_mul]

/-- The eventual scalar entry budget gives the CEH mixed matrix pairing
and fixes the cutoff to one after unitary spectral transport. -/
theorem regularizationCoefficient_spectralLift_eq_one_of_canonicalRate
    {N : ℕ} {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s c δ : ℝ} (hs : 0 < s) (hc : 0 < c)
    (q₀ q₁ q₂ : Fin N → ℂ)
    (hward : scaledPairing s q₀ q₀ = 1)
    (hq₀ : ∀ i, ‖q₀ i‖ ≤ (s * c)⁻¹)
    (hq₁ : ∀ i, ‖q₁ i - q₀ i‖ ≤ δ)
    (hq₂ : ∀ i, ‖q₂ i - q₀ i‖ ≤ δ)
    (hbudget : s * (2 * (s * c)⁻¹ * δ + δ ^ 2) < 1 / 2) :
    1 / 2 < (s * NTrace
        (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re ∧
      regularizationCoefficient (Real.sqrt s : ℂ)
        (spectralLift hF q₁) ((spectralLift hF q₂)ᴴ) = 1 := by
  have hN : 0 < N := by
    by_contra h
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos h
    subst N
    simp [scaledPairing, average] at hward
  have hδ : 0 ≤ δ := by
    let hi : Fin N := ⟨0, hN⟩
    exact (norm_nonneg (q₁ hi - q₀ hi)).trans (hq₁ hi)
  have hpair := scaledPairing_gt_half_of_uniform_close hN hs q₀ q₁ q₂
    (by positivity) hδ hward hq₀ hq₁ hq₂ hbudget
  have htrace : (s * NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re =
      scaledPairing s q₁ q₂ := by
    rw [NTrace_spectralLift_mul_conjTranspose]
    simp [scaledPairing]
  have hmatrix : 1 / 2 < (s * NTrace
      (spectralLift hF q₁ * (spectralLift hF q₂)ᴴ)).re := by
    rwa [htrace]
  refine ⟨hmatrix, ?_⟩
  apply regularizationCoefficient_eq_one_of_scaled_pairing
    (s := s) (lambda := Real.sqrt s)
  · rw [Real.sq_sqrt hs.le]
  · exact hmatrix

end CEHNative.BlockBand.External.CEH
