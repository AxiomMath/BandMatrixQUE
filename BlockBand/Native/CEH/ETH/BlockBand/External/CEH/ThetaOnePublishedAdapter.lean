module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.ThetaOneCanonicalMixedPairing

/-!
# Published CEH theta-one adapter

This file attaches the quantitative canonical-height package directly to the
checked-in `LocalETHRegularBoundaryWindow` data.  It deliberately stops at the
mixed pairing and cutoff coefficient: the published interface contains
no bound for the remaining `sTwoSq` base and stability-quotient terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.CEH

open Filter Set Matrix
open scoped Topology Matrix.Norms.L2Operator ComplexConjugate

/-- At a canonical CEH height, every spectral entry is within the
explicit vertical rate of the identified boundary entry. -/
theorem canonicalEntry_close_boundary_le_rate
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
        (c / (2 * Real.pi))) (i : Fin N) :
    let η := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x
    ‖entry f s ((x : ℂ) + (η : ℂ) * Complex.I)
          (upperBranch (by omega) f hs
            ((x : ℂ) + (η : ℂ) * Complex.I)) i -
        entry f s (x : ℂ) m₀ i‖ ≤
      canonicalVerticalEntryRate N ξ s c := by
  dsimp only
  let η := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x
  have hη : 0 < η := mul_pos (by positivity)
    (cehTypicalSpacing_spec N hN f hs x).1
  have hηcut : η ≤ quantitativeIFTHeight s c :=
    (canonicalHeight_lt_quantitativeIFTHeight_of_boundaryData
      hN f hs hc hξ₀ hm₀sol hm₀im hm₀stab hboundary hlarge).le
  have hbase := norm_upperBranch_entry_sub_boundary_le
    (by omega) f hs hc hm₀sol hm₀im hm₀stab hboundary hη hηcut i
  have hrate : η ≤ canonicalHeightRate N ξ c :=
    canonicalHeight_le_rate_of_boundaryData hN f hs hc hξ₀
      hm₀sol hm₀im hm₀stab hboundary hlarge
  unfold canonicalVerticalEntryRate
  dsimp only
  apply hbase.trans
  have hs0 : 0 ≤ s := hs.le
  have hden1 : 0 ≤ (s * c / 2)⁻¹ := by positivity
  have hden2 : 0 ≤ (s * c)⁻¹ := by positivity
  gcongr

/-- The three scalar side conditions of the published adapter hold
simultaneously for all sufficiently large dimensions under the published exponent restrictions. -/
theorem eventually_regularBoundaryWindow_canonical_conditions
    {s r c K β ξ : ℝ} (hs : 0 < s) (hr : 0 < r) (hc : 0 < c)
    (hξβ : ξ < β) (hβ : β ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (β - 1) < r ∧
      1 < (N : ℝ) *
        (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
          (c / (2 * Real.pi)) ∧
      s * (2 * (s * c)⁻¹ *
          canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2 := by
  have hβ1 : β < 1 := lt_of_le_of_lt hβ (by norm_num)
  have hξ1 : ξ < 1 := lt_trans hξβ hβ1
  have hwindow :
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (β - 1) < r := by
    have hlim := (tendsto_rpow_neg_atTop (sub_pos.mpr hβ1)).comp
      tendsto_natCast_atTop_atTop
    have hlim' : Tendsto (fun N : ℕ => (N : ℝ) ^ (β - 1))
        atTop (nhds 0) := by
      convert hlim using 1
      funext N
      congr 1
      ring
    exact hlim'.eventually (Iio_mem_nhds hr)
  have hheight : 0 < quantitativeIFTHeight s c := by
    simp only [quantitativeIFTHeight, quantitativeIFTRadius]
    positivity
  filter_upwards [hwindow,
    eventually_one_lt_ceh_test_density_scale hξ1 hheight hc,
    eventually_canonicalMixedEntryRate_budget hs hξβ hβ] with N hw hh hb
  exact ⟨hw, hh, hb⟩

/-- Pointwise final adapter on the published source domain.  The three
explicit scalar inequalities are precisely the already-proved eventual facts:
the source window lies inside the regular window, canonical heights lie below
the IFT cutoff, and the perturbation budget is below `1/2`. -/
theorem regularBoundaryWindow_canonicalMixedPairing
    {N : ℕ} (hN : 4 ≤ N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {s E₀ r c K β ξ x y : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hξ₀ : 0 ≤ ξ)
    (hregular : LocalETHRegularBoundaryWindow s
      (hermitianMDEBranch hF hs) E₀ r c K)
    (hx : |x - E₀| ≤ (N : ℝ) ^ (β - 1))
    (hy : |y - E₀| ≤ (N : ℝ) ^ (β - 1))
    (hwindow : (N : ℝ) ^ (β - 1) < r)
    (hlarge : 1 < (N : ℝ) *
      (quantitativeIFTHeight s c / (N : ℝ) ^ ξ) *
        (c / (2 * Real.pi)))
    (hbudget : s * (2 * (s * c)⁻¹ *
        canonicalMixedEntryRate N ξ β s c K +
      canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2) :
    let f := hermitianSpectrum hF
    let ηx := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x
    let ηy := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs y
    let qx := entry f s ((x : ℂ) + (ηx : ℂ) * Complex.I)
      (upperBranch (by omega) f hs ((x : ℂ) + (ηx : ℂ) * Complex.I))
    let qy := entry f s ((y : ℂ) + (ηy : ℂ) * Complex.I)
      (upperBranch (by omega) f hs ((y : ℂ) + (ηy : ℂ) * Complex.I))
    1 / 2 < (s * External.CEH.NTrace
        (spectralLift hF qx * (spectralLift hF qy)ᴴ)).re ∧
      External.CEH.regularizationCoefficient (Real.sqrt s : ℂ)
        (spectralLift hF qx) ((spectralLift hF qy)ᴴ) = 1 := by
  dsimp only
  let f := hermitianSpectrum hF
  let ηx := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs x
  let ηy := (N : ℝ) ^ ξ * cehTypicalSpacing N hN f hs y
  let qx := entry f s ((x : ℂ) + (ηx : ℂ) * Complex.I)
    (upperBranch (by omega) f hs ((x : ℂ) + (ηx : ℂ) * Complex.I))
  let qy := entry f s ((y : ℂ) + (ηy : ℂ) * Complex.I)
    (upperBranch (by omega) f hs ((y : ℂ) + (ηy : ℂ) * Complex.I))
  obtain ⟨Mb, Mb', hdata⟩ := hregular.boundary
  have hxopen : x ∈ Ioo (E₀ - r) (E₀ + r) := by
    rw [mem_Ioo]
    rw [abs_le] at hx
    constructor <;> linarith
  have hyopen : y ∈ Ioo (E₀ - r) (E₀ + r) := by
    rw [mem_Ioo]
    rw [abs_le] at hy
    constructor <;> linarith
  let mx := Conventions.normalizedTrace (Mb x)
  let my := Conventions.normalizedTrace (Mb y)
  have hidx := boundary_matrix_scalar_identification hF (by omega) hs hc
    (hdata x hxopen).1 (hdata x hxopen).2.2.2.1
  have hidy := boundary_matrix_scalar_identification hF (by omega) hs hc
    (hdata y hyopen).1 (hdata y hyopen).2.2.2.1
  have hbx : Tendsto (fun t : ℝ => upperBranch (by omega) f hs
      ((x : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds mx) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp
      (hdata x hxopen).1
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF (by omega) hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF (by omega) hs (by simpa using htpos')]
  have hby : Tendsto (fun t : ℝ => upperBranch (by omega) f hs
      ((y : ℂ) + (t : ℂ) * Complex.I))
      (nhdsWithin 0 (Ioi 0)) (nhds my) := by
    have ht := continuous_normalizedTrace.continuousAt.tendsto.comp
      (hdata y hyopen).1
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t htpos
    simp only [Function.comp_apply]
    have htpos' : 0 < t := htpos
    rw [normalizedTrace_hermitianMDEBranch hF (by omega) hs
      (by simpa using htpos'.ne')]
    rw [hermitianMDEMean_of_im_pos hF (by omega) hs (by simpa using htpos')]
  have hstabx : c ≤ ‖stabilityDenominator f s (x : ℂ) mx‖ := by
    rw [← hidx.2.2]
    exact (hdata x hxopen).2.2.2.2.2
  have hstaby : c ≤ ‖stabilityDenominator f s (y : ℂ) my‖ := by
    rw [← hidy.2.2]
    exact (hdata y hyopen).2.2.2.2.2
  have hvx (i : Fin N) : ‖qx i - entry f s (x : ℂ) mx i‖ ≤
      canonicalVerticalEntryRate N ξ s c := by
    exact canonicalEntry_close_boundary_le_rate hN f hs hc hξ₀ hidx.1
      (hdata x hxopen).2.2.2.1 hstabx hbx hlarge i
  have hvy (i : Fin N) : ‖qy i - entry f s (y : ℂ) my i‖ ≤
      canonicalVerticalEntryRate N ξ s c := by
    exact canonicalEntry_close_boundary_le_rate hN f hs hc hξ₀ hidy.1
      (hdata y hyopen).2.2.2.1 hstaby hby hlarge i
  have hK : 0 ≤ K := (norm_nonneg (Mb' x)).trans (hdata x hxopen).2.2.1
  have hmxy : ‖my - mx‖ ≤ K * |y - x| := by
    rcases le_total x y with hxy | hyx
    · have hseg : Icc x y ⊆ Ioo (E₀-r) (E₀+r) := by
        intro t ht
        exact ⟨hxopen.1.trans_le ht.1, ht.2.trans_lt hyopen.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using
        norm_normalizedTrace_sub_le_of_regularDerivative (by omega)
          hxy hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
    · rw [norm_sub_rev, abs_sub_comm]
      have hseg : Icc y x ⊆ Ioo (E₀-r) (E₀+r) := by
        intro t ht
        exact ⟨hyopen.1.trans_le ht.1, ht.2.trans_lt hxopen.2⟩
      simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using
        norm_normalizedTrace_sub_le_of_regularDerivative (by omega)
          hyx hseg (fun t ht => (hdata t ht).2.1)
          (fun t ht => (hdata t ht).2.2.1)
  have hhoriz (i : Fin N) :
      ‖entry f s (y : ℂ) my i - entry f s (x : ℂ) mx i‖ ≤
        sourceHorizontalEntryRate N β s c K := by
    apply (norm_boundary_entry_sub_le_of_mean_modulus f hs hc hK
      (hdata x hxopen).2.2.2.1 (hdata y hyopen).2.2.2.1 hmxy i).trans
    unfold sourceHorizontalEntryRate
    have hsep := abs_sub_le_two_mul_rpow_of_sourceWindow hx hy
    have hcoef : 0 ≤ 1 + s * K := by positivity
    rw [abs_sub_comm] at hsep
    gcongr
  let q₀ := entry f s (x : ℂ) mx
  have hq₀ (i : Fin N) : ‖q₀ i‖ ≤ (s * c)⁻¹ := by
    have hh : s * c ≤ effectiveHeight s (x : ℂ) mx := by
      simp only [effectiveHeight, Complex.ofReal_im, zero_add]
      exact mul_le_mul_of_nonneg_left (hdata x hxopen).2.2.2.1 hs.le
    exact (norm_entry_le_inv_effectiveHeight f
      (lt_of_lt_of_le (mul_pos hs hc) hh) i).trans
      (inv_anti₀ (by positivity) hh)
  have hqx (i : Fin N) : ‖qx i - q₀ i‖ ≤
      canonicalMixedEntryRate N ξ β s c K := by
    exact (hvx i).trans (le_add_of_nonneg_right (by
      unfold sourceHorizontalEntryRate
      positivity))
  have hqy (i : Fin N) : ‖qy i - q₀ i‖ ≤
      canonicalMixedEntryRate N ξ β s c K := by
    apply (calc
      ‖qy i - q₀ i‖ =
          ‖(qy i - entry f s (y : ℂ) my i) +
            (entry f s (y : ℂ) my i - q₀ i)‖ := by
              congr 1
              ring
      _ ≤ ‖qy i - entry f s (y : ℂ) my i‖ +
          ‖entry f s (y : ℂ) my i - q₀ i‖ := norm_add_le _ _).trans
    exact add_le_add (hvy i) (hhoriz i)
  have hward := scaledPairing_boundary_eq_one (by omega) f hs hidx.1
  exact External.CEH.regularizationCoefficient_spectralLift_eq_one_of_canonicalRate
    hF hs hc q₀ qx qy hward hq₀ hqx hqy hbudget

end CEHNative.BlockBand.CEH
