module

public import BlockBand.Native.CEH.ETH.Statements

/-!
# CEH ETH: extraction from the `θ = 1` law

The regular-window ETH bound `LocalETHRegularWindowBound gue` follows from the two-resolvent
positive-chain law with cutoff `θ = 1`, `TwoResolventPositiveChainLawThetaOne gue`.

## Main results

* `regularizationCoefficient_gridPair_eq_one`: at every pair of points of the rectangular
  extraction grid `cehETHGrid`, under the conversion conditions, the CEH cutoff `θ(z₁, z₂)` of an
  admissible MDE branch equals `1`.
* `gridTail_of_thetaOneLaw`: grid-pair tails from `TwoResolventPositiveChainLawThetaOne` (the law
  is evaluated only at grid pairs).
* `centreComparison_regularWindow`: the regular-window centre comparison.
* `localETHRegularWindowBound_of_thetaOneLaw`: the conclusion `LocalETHRegularWindowBound gue`,
  finished exactly as `localETHRegularWindowBound_of_twoResolventPositiveChainLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set Filter
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH CEHNative.BlockBand.CEH
open scoped Matrix Matrix.Norms.L2Operator ENNReal

/-- **`θ = 1` at grid pairs.** Under the conversion conditions
(`eventually_cehTwoResolventLaw_conversionConditions`, first four clauses), the CEH cutoff
`θ(z₁, z₂) = regularizationCoefficient (√s) (Mf z₁) (Mf z₂)ᴴ` equals `1` at every pair of
points of the rectangular grid `cehETHGrid N E₀ β ξ s c m`, for every admissible MDE branch
`Mf` with a regular boundary window. Deterministic; derived from
`regularWindow_pair_thetaOne_sTwo_density` as in `cehTwoResolventLawBad_of_positiveChainBad`. -/
theorem regularizationCoefficient_gridPair_eq_one
    {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) (F : HermitianMatrix (Fin N))
    {Mf : ℂ → LocalETHMatrix N} (hMf : IsLocalETHMDEBranch s F.1 Mf)
    {E₀ r c K β ξ : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K) {m : ℕ} (hm : 0 < m)
    (hR : (N : ℝ) ^ (β - 1) < r)
    (hHq : canonicalHeightRate N ξ c ≤ quantitativeIFTHeight s c)
    (hconv : canonicalMixedEntryRate N ξ β s c K ≤ 1 ∧
      canonicalMixedEntryRate N ξ β s c K ≤ c / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) < 1 / 2 ∧
      s * (2 * (s * c)⁻¹ * canonicalMixedEntryRate N ξ β s c K +
        canonicalMixedEntryRate N ξ β s c K ^ 2) ≤ c / 2)
    (a b : Fin (m + 1) × Fin (m + 1)) :
    regularizationCoefficient (Real.sqrt s : ℂ) (Mf (cehETHGrid N E₀ β ξ s c m a))
      (Mf (cehETHGrid N E₀ β ξ s c m b))ᴴ = 1 := by
  obtain ⟨hδ1, hδc, hb1, hb2⟩ := hconv
  have hF : F.1.IsHermitian := F.2
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch hF hs hMf hreg
  obtain ⟨Mb, Mb', hdata⟩ := hregC.boundary
  have hK : 0 ≤ K := by
    have hx₀ : E₀ ∈ Ioo (E₀ - r) (E₀ + r) := by constructor <;> linarith
    exact (norm_nonneg _).trans (hdata E₀ hx₀).2.2.1
  set wa := cehETHGrid N E₀ β ξ s c m a
  set wb := cehETHGrid N E₀ β ξ s c m b
  have hma := cehETHGrid_mem (ξ := ξ) hN hs hF hr hc hregC hR hm a
  have hmb := cehETHGrid_mem (ξ := ξ) hN hs hF hr hc hregC hR hm b
  set x₁ := wa.re
  set x₂ := wb.re
  set η₁ := wa.im
  set η₂ := wb.im
  have hwa : wa = (x₁ : ℂ) + (η₁ : ℂ) * Complex.I := (Complex.re_add_im wa).symm
  have hwb : wb = (x₂ : ℂ) + (η₂ : ℂ) * Complex.I := (Complex.re_add_im wb).symm
  have hη₁ : 0 < η₁ := hma.2.2.2.2.trans_le hma.2.2.1
  have hη₂ : 0 < η₂ := hmb.2.2.2.2.trans_le hmb.2.2.1
  set V := canonicalVerticalEntryRate N ξ s c
  have hsrc : 0 ≤ sourceHorizontalEntryRate N β s c K := by
    unfold sourceHorizontalEntryRate; positivity
  have hmix : canonicalMixedEntryRate N ξ β s c K =
      V + sourceHorizontalEntryRate N β s c K := rfl
  have hv₁ := (verticalModulus_le_canonicalVerticalEntryRate (N := N) (ξ := ξ) hs hc
    hma.2.2.2.1).trans (show V ≤ canonicalMixedEntryRate N ξ β s c K by
      rw [hmix]; linarith)
  have hdist : |x₂ - x₁| ≤ 2 * (N : ℝ) ^ (β - 1) := by
    have h1 := hma.1
    have h2 := hmb.1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hv₂ : (η₂ + s * (8 * η₂ / (s ^ 2 * c ^ 3))) * (s * c / 2)⁻¹ * (s * c)⁻¹ +
      (1 + s * K) * |x₂ - x₁| * (s * c)⁻¹ ^ 2 ≤ canonicalMixedEntryRate N ξ β s c K := by
    rw [hmix]
    gcongr
    · exact verticalModulus_le_canonicalVerticalEntryRate hs hc hmb.2.2.2.1
    · unfold sourceHorizontalEntryRate
      gcongr
  obtain ⟨htheta, -⟩ :=
    regularWindow_pair_thetaOne_sTwo_density hN hF hs hc hdata hma.2.1 hmb.2.1
      hη₁ (hma.2.2.2.1.trans hHq) hη₂ (hmb.2.2.2.1.trans hHq) hv₁ hv₂ hδ1 hδc hb1 hb2
      (0 : LocalETHMatrix N) (by simp)
  simp only [← hwa, ← hwb] at htheta
  have hMfa : Mf wa = hermitianMDEBranch hF hs wa :=
    localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf hη₁.ne'
  have hMfb : Mf wb = hermitianMDEBranch hF hs wb :=
    localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf hη₂.ne'
  rw [hMfa, hMfb]
  exact htheta

/-- **Grid-pair tails from the `θ = 1` law.** The statement of
`gridTail_of_twoResolventPositiveChainLaw`, with hypothesis the `θ = 1` law
`TwoResolventPositiveChainLawThetaOne gue`: at every pair of points of the `N^4` rectangular
grid, failure of the order-one positive-chain bound `N^(δ-ξ)` has probability at most
`N^(-(D+20))`, eventually and uniformly. -/
theorem gridTail_of_thetaOneLaw
    (gue : LocalETHGUEFamily) (hlaw : TwoResolventPositiveChainLawThetaOne gue)
    {κ C sLo sHi r c K β ξ δ D : ℝ} (hκ : 0 ≤ κ) (hC : 0 < C)
    (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hc : 0 < c) (hK : 0 < K)
    (hβ : β < 1) (hξ : 0 < ξ) (hξhalf : ξ < 1 / 2) (hξδ : ξ < δ) (hD : 0 < D) :
    ∃ Ng : ℕ, ∀ N : ℕ, Ng ≤ N →
      ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
      ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
      ∀ a b : Fin (N ^ 4 + 1) × Fin (N ^ 4 + 1),
        (gue N (s / N) : Measure (HermitianMatrix (Fin N)))
            {G | CEHFixedPointPositiveChainBad s (δ - ξ) Mf F.1 J
              (cehETHGrid N E₀ β ξ s c (N ^ 4) a)
              (cehETHGrid N E₀ β ξ s c (N ^ 4) b) G} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-(D + 20))) := by
  have hε : 0 < δ - ξ := by linarith
  obtain ⟨Nlaw, hNlaw⟩ := hlaw κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK
    (ξ / 2) (2 * ξ) (by positivity) (by linarith) (by linarith)
    ((δ - ξ) / 2) (D + 20) (by positivity) (by linarith)
  obtain ⟨Ndet, hNdet⟩ := eventually_atTop.1
    (eventually_cehETHGridScalarConditions (δ := δ) (ε := δ - ξ) hsLo hsHi hr hc hK hβ
      hξ hξhalf hε (by linarith))
  obtain ⟨Nconv, hNconv⟩ := eventually_atTop.1
    (eventually_cehTwoResolventLaw_conversionConditions (β := β) (K := K) hsLo hsHi hc
      hK.le hβ hξ (by linarith) hε)
  refine ⟨max Nlaw (max Ndet Nconv), ?_⟩
  intro N hN s hs hsH F hFdef Mf hMf E₀ hreg J hJh hJ a b
  obtain ⟨hN4, hall⟩ := hNdet N (le_of_max_le_left (le_of_max_le_right hN))
  obtain ⟨hcond, hlo, hHup⟩ := hall s hs hsH
  have hconv := hNconv N (le_of_max_le_right (le_of_max_le_right hN)) s hs hsH
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hN0 : 0 < N := by omega
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  have hma := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) a
  have hmb := cehETHGrid_mem (ξ := ξ) hN0 hs0 F.2 hr hc hregC hcond.1
    (by positivity : 0 < N ^ 4) b
  have hHq := (canonicalHeightRate_lt_quantitativeIFTHeight hN0 hc hcond.2.1).le
  have htheta := regularizationCoefficient_gridPair_eq_one hN0 hs0 F hMf hr hc hreg
    (by positivity : 0 < N ^ 4) hcond.1 hHq
    ⟨hconv.1, hconv.2.1, hconv.2.2.1, hconv.2.2.2.1⟩ a b
  have hlit := hNlaw N (le_of_max_le_left hN) s hs hsH F hFdef Mf hMf E₀ hreg
    _ _ hma.2.1 hmb.2.1 (hlo.trans hma.2.2.1) (hma.2.2.2.1.trans hHup)
    (hlo.trans hmb.2.2.1) (hmb.2.2.2.1.trans hHup) htheta J hJh hJ
  refine (measure_mono fun G hG => ?_).trans hlit
  exact cehTwoResolventLawBad_of_positiveChainBad hN0 hs0 F hMf hr hc hreg J hJ
    (by positivity : 0 < N ^ 4) hcond.1 hHq hconv a b G hG

/-- **The regular-window centre comparison.** Fix `sLo > 0`, regular-window data
`r, c, K > 0`, `β < 1`, height exponents `0 ≤ ξ, ξ' < 1/2`, and loss exponents `δ' < δ`, `δ > 0`.
There is one cutoff `N₀ ≥ 4`, depending only on these data, such that for every `N ≥ N₀`,
`s ≥ sLo`, Hermitian deformation `F`, admissible MDE branch `Mf`, typical-spacing function
`etaF`, regular boundary window `E₀` and `‖J‖ ≤ 1`, and every energy `x` with
`|x - E₀| ≤ N^(β-1)`:
* the centres `⟨Γ(x + i N^ξ η_f(x)) J⟩` and `⟨Γ(x + i N^ξ' η_f(x)) J⟩` differ by at most
  `(2/c + 2K/c²)` times the sum of the two vertical rates `canonicalVerticalEntryRate`
  (each `O(N^(ξ-1))`, resp. `O(N^(ξ'-1))`, uniformly in `s ≥ sLo`), through the boundary
  centre `⟨Γ(M_b(x)) J⟩`;
* that discrepancy plus `N^δ' N^(-1/2)` is at most `N^δ N^(-1/2)`. -/
theorem centreComparison_regularWindow
    {sLo r c K β ξ ξ' δ δ' : ℝ} (hsLo : 0 < sLo) (hr : 0 < r) (hc : 0 < c)
    (hK : 0 < K) (hβ : β < 1) (hξ₀ : 0 ≤ ξ) (hξ : ξ < 1 / 2)
    (hξ'₀ : 0 ≤ ξ') (hξ' : ξ' < 1 / 2) (hδ : 0 < δ) (hδ' : δ' < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ s : ℝ, sLo ≤ s →
      ∀ F : HermitianMatrix (Fin N),
      ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
      ∀ etaF : ℝ → ℝ, (∀ x, IsLocalETHTypicalSpacing Mf x (etaF x)) →
      ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
      ∀ J : LocalETHMatrix N, ‖J‖ ≤ 1 →
      ∀ x : ℝ, |x - E₀| ≤ (N : ℝ) ^ (β - 1) →
        ‖localETHCenter Mf etaF ξ x J - localETHCenter Mf etaF ξ' x J‖ ≤
            (2 / c + 2 * K / c ^ 2) *
              (canonicalVerticalEntryRate N ξ s c + canonicalVerticalEntryRate N ξ' s c) ∧
          (N : ℝ) ^ δ' * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
              (2 / c + 2 * K / c ^ 2) *
                (canonicalVerticalEntryRate N ξ s c + canonicalVerticalEntryRate N ξ' s c) ≤
            (N : ℝ) ^ δ * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (eventually_auxiliaryLoss_scalarConditions (K := K) hsLo hr hc hK hβ
      hξ hξ' hδ hδ')
  refine ⟨max N₀ 4, le_max_right _ _, ?_⟩
  intro N hN s hs F Mf hMf etaF hetaF E₀ hreg J hJ x hx
  obtain ⟨hN4, hwin, hsc⟩ := hN₀ N (le_of_max_le_left hN)
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  obtain ⟨hlg, hlg', hrt, hrt', hbudget⟩ := hsc s hs
  have hregC := localETHRegularBoundaryWindow_canonical_of_branch F.2 hs0 hMf hreg
  refine ⟨?_, hbudget⟩
  rw [localETHCenter_eq_canonicalSpacing hN4 F.2 hs0 hMf hetaF ξ x J,
    localETHCenter_eq_canonicalSpacing hN4 F.2 hs0 hMf hetaF ξ' x J]
  exact regularWindow_canonicalCenter_sub_le hN4 F.2 hs0 hc hξ₀ hξ'₀ hregC hx
    hwin hlg hlg' hrt hrt' J hJ

/-- **The regular-window ETH bound from the `θ = 1` law.** For an arbitrary family `gue`,
`TwoResolventPositiveChainLawThetaOne gue` implies `LocalETHRegularWindowBound gue`, with its
exact quantifier order and uniformities: auxiliary height `ξ' = min(ξ, δ/4)`, auxiliary loss
`δ/2`, centre comparison (`centreComparison_regularWindow`), grid snapping
(`measure_localETHWindowBad_le_of_gridTail`) and the grid tail `gridTail_of_thetaOneLaw`. -/
theorem localETHRegularWindowBound_of_thetaOneLaw
    (gue : LocalETHGUEFamily) (hlaw : TwoResolventPositiveChainLawThetaOne gue) :
    LocalETHRegularWindowBound gue := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK β hβ hβ2 ξ hξ hξβ δ D hδ hD
  set ξ' : ℝ := min ξ (δ / 4) with hξ'def
  have hξ'pos : 0 < ξ' := lt_min hξ (by positivity)
  have hξ'ξ : ξ' ≤ ξ := min_le_left _ _
  have hξ'δ : ξ' ≤ δ / 4 := min_le_right _ _
  have hβ1 : β < 1 := lt_of_le_of_lt hβ2 (by norm_num)
  exact CEH.localETHWindowBad_polynomialTail_of_auxiliaryLoss gue
    (ξ' := ξ') (δ' := δ / 2) hsLo hr hc hK hξ hξβ hβ2 hξ'pos.le hξ'ξ hδ (by linarith)
    (measure_localETHWindowBad_le_of_gridTail gue hsLo hsHi hr hc hK hβ1 hξ'pos
      (by linarith) (by linarith)
      (gridTail_of_thetaOneLaw gue hlaw hκ hC hsLo hsHi hr hc hK hβ1
        hξ'pos (by linarith) (by linarith) hD))

end BlockBand.Native.CEH.ETH
