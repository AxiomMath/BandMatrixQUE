module

public import BlockBand.LocalWindow.ProofPartTwoPoint
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.ETHPairSpacing

/-!
# The pair ETH with the real-axis centre at one grid point (GUE inputs)

`gue_not_pairWindowGood_le`: under `G ~ GUE_{2W}(s/2W)`,
`P(¬ PairWindowGood K sel s E₀ β ε J G) ≤ (2W)^{-D}`.

The statements are those of `BlockBand.LocalWindow.ProofPartTwoPoint`, with `NativeInputs` replaced
by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of `External.CEH.SourceContract`) as
needed, and without `GUEWignerFamilyAdapter`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo.GUEInputs

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped ENNReal NNReal Matrix.Norms.L2Operator

section

variable {p : Parameters} {i : ZMod p.n}

/-- **The pair ETH with the real-axis centre at one grid point** (the external ETH via
`gue_not_pairETHGood_le`). Fixed `A, C`, `[sLo, sHi] ⊂ (0,∞)`,
the rectangle radius `r > 0` and lower bound `v₀ > 0` first; then `β₀ ∈ (0, 1/2]`; then
`0 < β < β₀`, `ε, D > 0`; then `N₀`. Uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`,
Hermitian pair deformations `K` with `s^{-1/2}‖K‖ ≤ C (2W)^A`, `E₀` with
`PairRootRectangle K s E₀ r v₀`, eigenpair selections and Hermitian pair contractions `J`:
under `G ~ GUE_{2W}(s/2W)`, `P(¬ PairWindowGood K sel s E₀ β ε J G) ≤ (2W)^{-D}`. -/
theorem gue_not_pairWindowGood_le (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
    (hMDE : MDEBranchIdentification) (hETH : ExternalETH) (hBridge : PairGUELawBridgeStatement)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W → ∀ s ∈ Icc sLo sHi,
        ∀ (K : PairMatrix p i) (hK : K.IsHermitian),
          (Real.sqrt s)⁻¹ * ‖K‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A →
        ∀ E₀ : ℝ, PairRootRectangle K s E₀ r v₀ →
        ∀ (sel : CEH.EigenpairSelection (2 * p.W)) (J : PairMatrix p i), J.IsHermitian →
          ‖J‖ ≤ 1 →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ¬ PairWindowGood K hK sel s E₀ β ε J G} ≤
            ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  have hKr : 0 < regK sLo v₀ :=
    lt_of_lt_of_le (inv_pos.mpr (mul_pos hsLo hv₀)) ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨β₁, hβ₁, hE⟩ := gue_not_pairETHGood_le hETH hBridge A C sLo sHi r (regK sLo v₀) hsLo
    hsHi hr hKr
  refine ⟨min β₁ (1 / 2), lt_min hβ₁ (by norm_num), min_le_right _ _,
    fun β hβ hββ ε D hε hD => ?_⟩
  set ξ := β / 2 with hξ
  have hξ0 : 0 < ξ := half_pos hβ
  have hξβ : ξ < β := half_lt_self hβ
  have hβ12 : β < 1 / 2 := hββ.trans_le (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hE β ξ hξ0 hξβ (hββ.trans_le (min_le_left _ _)) ε D hε hD
  set Lc := (3 + 1 / (sLo * v₀ ^ 2)) / (sLo * v₀) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  -- the eventual size conditions on `N = 2W`
  have e3 : ∀ᶠ n : ℕ in atTop, Real.pi < ((n : ℕ) : ℝ) * v₀ :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hv₀).eventually_gt_atTop Real.pi
  have e4 : ∀ᶠ n : ℕ in atTop, ((n : ℕ) : ℝ) ^ (-1 + β) ≤ r := by
    filter_upwards [eventually_const_mul_rpow_le (1 / r) (-1 + β) (by linarith)] with n hn
    rwa [div_mul_eq_mul_div, one_mul, div_le_one hr] at hn
  have e5 := eventually_const_mul_rpow_le (Real.pi / v₀) (ξ - 1) (by linarith)
  have e6 := eventually_const_mul_rpow_le (Lc * (Real.pi / v₀)) (ξ - 1 / 2 - ε) (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop N₁).and
    ((eventually_ge_atTop 4).and (e3.and (e4.and (e5.and e6)))))
  refine ⟨N₀, fun p i hN s hsI K hK hKn E₀ hrect sel J hJ hJn => ?_⟩
  obtain ⟨h1, h4, hpi, hhr, hη1, hcen⟩ := hN₀ (2 * p.W) hN
  have hs : 0 < s := hsLo.trans_le hsI.1
  have hNpos : 0 < 2 * p.W := Nat.mul_pos two_pos p.W_pos
  have : NeZero (2 * p.W) := ⟨hNpos.ne'⟩
  set N : ℝ := ((2 * p.W : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := Nat.cast_pos.mpr hNpos
  obtain ⟨M⟩ := (hMDE (2 * p.W) hNpos s hs (toSourceHermitian K hK)).1
  have hR : RootRectangle (toSourceHermitian K hK).1 s E₀ r v₀ :=
    rootRectangle_reindex (pairEquiv p i) hrect
  have hreg : RegularWindow M E₀ r (regK sLo v₀) :=
    regularWindow_of_rootRectangle hMDE hs hv₀ hR (regK_anti hsLo hsI.1 hv₀) M
  obtain ⟨spacing, hsp⟩ := BlockBand.LocalWindow.ProofETH.GUEInputs.exists_small_spacing hSp hMDE hs hK M h4 hv₀
    (fun x hx η hη hη1 => hrect x hx η hη.le hη1) hpi
  have hbad := hN₁ p i h1 s hsI K hK hKn M E₀ hreg spacing sel J hJ hJn
  set B := N ^ ε * N ^ (-(1 : ℝ) / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the centre move is at most `B`
  have hmove : ∀ μ : ℝ, |μ - E₀| ≤ r →
      ‖ethCentre M spacing ξ J μ - pairCentre J K s μ‖ ≤ B := by
    intro μ hμ
    set η := N ^ ξ * spacing.eta μ with hη
    have hηle : η ≤ (Real.pi / v₀) * N ^ (ξ - 1) := by
      rw [hη, Real.rpow_sub_one hN0.ne']
      have := hsp μ hμ
      calc N ^ ξ * spacing.eta μ ≤ N ^ ξ * (Real.pi / (N * v₀)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Real.pi / v₀ * (N ^ ξ / N) := by field_simp
    have hη0 : 0 ≤ η := mul_nonneg (by positivity) (spacing.positive μ).le
    obtain ⟨m, hm, hmv⟩ := hrect μ hμ η hη0 (hηle.trans hη1)
    have hm' : IsDysonRoot K s (CEH.inflatedSpectralPoint spacing ξ μ) m := by
      unfold CEH.inflatedSpectralPoint; exact hm
    obtain ⟨m₀, hm₀, hm₀v⟩ := hrect μ hμ 0 le_rfl zero_le_one
    have hm₀' : IsDysonRoot K s (μ : ℂ) m₀ := by simpa using hm₀
    have hcc := ethCentre_sub_pairCentre_le hMDE hs hK M spacing ξ hJn hv₀ hm' hmv hm₀' hm₀v
    rw [inflatedSpectralPoint_im] at hcc
    have hconst : (3 + 1 / (s * v₀ ^ 2)) / (s * v₀) ≤ Lc := by
      have h1' : 1 / (s * v₀ ^ 2) ≤ 1 / (sLo * v₀ ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg v₀, hsI.1])
      exact div_le_div₀ (by positivity) (by linarith) (by positivity)
        (by nlinarith [hsI.1])
    have hexp : N ^ (ξ - 1) = N ^ (ξ - 1 / 2 - ε) * N ^ (ε + -(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hBexp : B = N ^ (ε + -(1 : ℝ) / 2) := by rw [hB, ← Real.rpow_add hN0]
    calc _ ≤ η * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := hcc
      _ ≤ ((Real.pi / v₀) * N ^ (ξ - 1)) * Lc :=
          mul_le_mul hηle hconst (by positivity) (by positivity)
      _ = (Lc * (Real.pi / v₀) * N ^ (ξ - 1 / 2 - ε)) * N ^ (ε + -(1 : ℝ) / 2) := by
          rw [hexp]; ring
      _ ≤ 1 * N ^ (ε + -(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcen (by positivity)
      _ = B := by rw [one_mul, hBexp]
  refine le_trans (measure_mono fun G hG => ?_) hbad
  intro hgood
  apply hG
  obtain ⟨hGh, hgood⟩ := hgood
  refine ⟨hGh, fun k l hk hl => ?_⟩
  have hb := hgood k l hk hl
  by_cases hkl : k = l
  · subst hkl
    simp only [↓reduceIte] at hb ⊢
    set μ := pairEigval sel (K + G) (hK.add hGh) k
    have hμ : |μ - E₀| ≤ r := by
      rw [mem_Icc] at hk
      rw [abs_le]; constructor <;> linarith [hk.1, hk.2]
    have hm := hmove μ hμ
    calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (ethCentre M spacing ξ J μ) _
      _ ≤ B + B := add_le_add hb hm
      _ = 2 * B := (two_mul B).symm
  · simp only [hkl, ↓reduceIte] at hb ⊢
    linarith

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
