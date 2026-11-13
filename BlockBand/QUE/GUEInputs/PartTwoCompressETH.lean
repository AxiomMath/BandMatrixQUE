module

public import BlockBand.LocalWindow.ProofPartTwoCompressETH
public import BlockBand.QUE.GUEInputs.Fields
public import BlockBand.QUE.GUEInputs.PartTwoCompressETHNative

/-!
# The compressed window estimate (GUE inputs)

The external ETH in dimension `N` (`gueSource_not_natWindowGood_le`) and the compressed window
estimate at `N = 2W - 1` (`gue_not_compressWindowGood_le`).

The statements are those of `BlockBand.LocalWindow.ProofPartTwoCompressETH`, with `NativeInputs`
replaced by the hypotheses `EigenpairsExist` and `SpacingExists` (fields of
`External.CEH.SourceContract`) as needed, and without `GUEWignerFamilyAdapter`.
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

variable {N : ℕ}

/-- **The external ETH in dimension `N`, recentred at the real-axis centre** (the analogue
of `gue_not_pairWindowGood_le`). Fixed `A, C`, `[sLo, sHi] ⊂ (0,∞)`, the rectangle
radius `r > 0` and lower bound `v₀ > 0` first; then `β₀ ∈ (0, 1/2]`; then `0 < β < β₀`,
`ε, D > 0`; then `N₀`. Uniformly in `N ≥ N₀`, `s ∈ [sLo, sHi]`, Hermitian `F` with
`s^{-1/2}‖F‖ ≤ C N^A`, `E₀` with `RootRectangle F s E₀ r v₀`, eigenpair selections and Hermitian
contractions `J`: under `W ~ gueSourceLaw N`,
`P(¬ NatWindowGood F sel s E₀ β ε J (√s W)) ≤ N^{-D}`. -/
theorem gueSource_not_natWindowGood_le (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
 (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s ∈ Icc sLo sHi, ∀ F : CEH.SourceHermitian N,
        (Real.sqrt s)⁻¹ * ‖F.1‖ ≤ C * (N : ℝ) ^ A →
        ∀ E₀ : ℝ, RootRectangle F.1 s E₀ r v₀ →
        ∀ (sel : CEH.EigenpairSelection N) (J : CEH.SourceMatrix N), J.IsHermitian →
          ‖J‖ ≤ 1 →
          gueSourceLaw N
              {W | ¬ NatWindowGood F sel s E₀ β ε J ((((Real.sqrt s) : ℝ) : ℂ) • W.1)} ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  have hKr : 0 < regK sLo v₀ :=
    lt_of_lt_of_le (inv_pos.mpr (mul_pos hsLo hv₀)) ((le_max_right _ _).trans (le_max_left _ _))
  obtain ⟨β₁, hβ₁, hE⟩ := hETH A C sLo sHi r (regK sLo v₀) hsLo hsHi hr hKr
  refine ⟨min β₁ (1 / 2), lt_min hβ₁ (by norm_num), min_le_right _ _,
    fun β hβ hββ ε D hε hD => ?_⟩
  set ξ := β / 2 with hξ
  have hξ0 : 0 < ξ := half_pos hβ
  have hξβ : ξ < β := half_lt_self hβ
  have hβ12 : β < 1 / 2 := hββ.trans_le (min_le_right _ _)
  obtain ⟨N₁, hN₁⟩ := hE β ξ hξ0 hξβ (hββ.trans_le (min_le_left _ _)) ε D hε hD
  set Lc := (3 + 1 / (sLo * v₀ ^ 2)) / (sLo * v₀) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  have e3 : ∀ᶠ n : ℕ in atTop, Real.pi < ((n : ℕ) : ℝ) * v₀ :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hv₀).eventually_gt_atTop Real.pi
  have e4 : ∀ᶠ n : ℕ in atTop, ((n : ℕ) : ℝ) ^ (-1 + β) ≤ r := by
    filter_upwards [eventually_const_mul_rpow_le (1 / r) (-1 + β) (by linarith)] with n hn
    rwa [div_mul_eq_mul_div, one_mul, div_le_one hr] at hn
  have e5 := eventually_const_mul_rpow_le (Real.pi / v₀) (ξ - 1) (by linarith)
  have e6 := eventually_const_mul_rpow_le (Lc * (Real.pi / v₀)) (ξ - 1 / 2 - ε) (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_ge_atTop N₁).and
    ((eventually_ge_atTop 4).and (e3.and (e4.and (e5.and e6)))))
  refine ⟨N₀, fun N hN s hsI F hKn E₀ hR sel J hJ hJn => ?_⟩
  obtain ⟨h1, h4, hpi, hhr, hη1, hcen⟩ := hN₀ N hN
  have hs : 0 < s := hsLo.trans_le hsI.1
  have hNpos : 0 < N := by omega
  have : NeZero N := ⟨hNpos.ne'⟩
  set Nr : ℝ := (N : ℝ) with hNdef
  have hN0 : 0 < Nr := Nat.cast_pos.mpr hNpos
  obtain ⟨M⟩ := (hMDE N hNpos s hs F).1
  have hreg : RegularWindow M E₀ r (regK sLo v₀) :=
    regularWindow_of_rootRectangle hMDE hs hv₀ hR (regK_anti hsLo hsI.1 hv₀) M
  obtain ⟨spacing, hsp⟩ := BlockBand.LocalWindow.ProofPartTwo.GUEInputs.nat_exists_small_spacing hSp hMDE hs M h4 hv₀
    (fun x hx η hη hη1 => hR x hx η hη.le hη1) hpi
  have hbad := hN₁ N h1 s hsI F hKn M E₀ hreg spacing sel J hJ hJn
  set B := Nr ^ ε * Nr ^ (-(1 : ℝ) / 2) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the centre move is at most `B`
  have hmove : ∀ μ : ℝ, |μ - E₀| ≤ r →
      ‖natEthCentre M spacing ξ J μ - nativeCentre J F.1 s μ‖ ≤ B := by
    intro μ hμ
    set η := Nr ^ ξ * spacing.eta μ with hη
    have hηle : η ≤ (Real.pi / v₀) * Nr ^ (ξ - 1) := by
      rw [hη, Real.rpow_sub_one hN0.ne']
      have := hsp μ hμ
      calc Nr ^ ξ * spacing.eta μ ≤ Nr ^ ξ * (Real.pi / (Nr * v₀)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = Real.pi / v₀ * (Nr ^ ξ / Nr) := by field_simp
    have hη0 : 0 ≤ η := mul_nonneg (by positivity) (spacing.positive μ).le
    obtain ⟨m, hm, hmv⟩ := hR μ hμ η hη0 (hηle.trans hη1)
    have hm' : IsDysonRoot F.1 s (CEH.inflatedSpectralPoint spacing ξ μ) m := by
      unfold CEH.inflatedSpectralPoint; exact hm
    obtain ⟨m₀, hm₀, hm₀v⟩ := hR μ hμ 0 le_rfl zero_le_one
    have hm₀' : IsDysonRoot F.1 s (μ : ℂ) m₀ := by simpa using hm₀
    have hcc := nat_ethCentre_sub_nativeCentre_le hMDE hNpos hs M spacing ξ hJn hv₀ hm' hmv
      hm₀' hm₀v
    rw [nat_inflatedSpectralPoint_im] at hcc
    have hconst : (3 + 1 / (s * v₀ ^ 2)) / (s * v₀) ≤ Lc := by
      have h1' : 1 / (s * v₀ ^ 2) ≤ 1 / (sLo * v₀ ^ 2) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg v₀, hsI.1])
      exact div_le_div₀ (by positivity) (by linarith) (by positivity)
        (by nlinarith [hsI.1])
    have hexp : Nr ^ (ξ - 1) = Nr ^ (ξ - 1 / 2 - ε) * Nr ^ (ε + -(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hBexp : B = Nr ^ (ε + -(1 : ℝ) / 2) := by rw [hB, ← Real.rpow_add hN0]
    calc _ ≤ η * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := hcc
      _ ≤ ((Real.pi / v₀) * Nr ^ (ξ - 1)) * Lc :=
          mul_le_mul hηle hconst (by positivity) (by positivity)
      _ = (Lc * (Real.pi / v₀) * Nr ^ (ξ - 1 / 2 - ε)) * Nr ^ (ε + -(1 : ℝ) / 2) := by
          rw [hexp]; ring
      _ ≤ 1 * Nr ^ (ε + -(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcen (by positivity)
      _ = B := by rw [one_mul, hBexp]
  refine le_trans (measure_mono fun W hW => ?_) hbad
  by_contra hnot
  apply hW
  have hX := isHermitian_sqrt_smul s W
  refine ⟨hX, fun k l hk hl => ?_⟩
  have hb : ‖CEH.sourceMatrixElement J (sel.eigenvector (natDeformed F _ hX) k)
        (sel.eigenvector (natDeformed F _ hX) l) -
      (if k = l then natEthCentre M spacing ξ J (sel.eigenvalue (natDeformed F _ hX) k)
        else 0)‖ ≤ B := by
    by_contra hlt
    push Not at hlt
    exact hnot ⟨k, l, hk, hl, hlt⟩
  by_cases hkl : k = l
  · subst hkl
    simp only [↓reduceIte] at hb ⊢
    set μ := sel.eigenvalue (natDeformed F _ hX) k
    have hμ : |μ - E₀| ≤ r := by
      rw [mem_Icc] at hk
      rw [abs_le]; constructor <;> linarith [hk.1, hk.2]
    have hm := hmove μ hμ
    calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (natEthCentre M spacing ξ J μ) _
      _ ≤ B + B := add_le_add hb hm
      _ = 2 * B := (two_mul B).symm
  · simp only [hkl, ↓reduceIte] at hb ⊢
    linarith

end

section

variable (p : Parameters)

/-- **The compressed window estimate** (the external ETH at `N = 2W - 1`, variance
`s' = s(1 - 1/(2W))`, recentred at the real-axis compressed centre).
Fixed `A, C`, `[sLo, sHi] ⊂ (0,∞)`, `r, v₀ > 0` first; then `β₀ ∈ (0, 1/2]`; then `0 < β < β₀`,
`ε, D > 0`; then `N₀`. Uniformly in `p, i` with `N₀ ≤ 2W - 1`, `s > 0` with `s' ∈ [sLo, sHi]`,
compressed deformations `F` on `Fin (2W - 1)` with `s'^{-1/2}‖F‖ ≤ C (2W-1)^A` and
`RootRectangle F s' E₀ r v₀`, eigenpair selections, Hermitian contractions `J` and isometries `U`:
under `G ~ GUE_{2W}(s/2W)`, `P(¬ NatWindowGood F sel s' E₀ β ε J (U*GU)) ≤ (2W - 1)^{-D}`. -/
theorem gue_not_compressWindowGood_le (hSp : BlockBand.QUE.GUEInputs.SpacingExists)
 (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
    (hComp : CompressedGUELawBridgeStatement)
    (A C sLo sHi r v₀ : ℝ) (hsLo : 0 < sLo) (hsHi : sLo ≤ sHi) (hr : 0 < r) (hv₀ : 0 < v₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ ∀ β : ℝ, 0 < β → β < β₀ → ∀ ε D : ℝ, 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ (p : Parameters) (i : ZMod p.n), N₀ ≤ 2 * p.W - 1 → ∀ s : ℝ, 0 < s →
        compressVar p s ∈ Icc sLo sHi →
        ∀ F : CEH.SourceHermitian (2 * p.W - 1),
          (Real.sqrt (compressVar p s))⁻¹ * ‖F.1‖ ≤ C * ((2 * p.W - 1 : ℕ) : ℝ) ^ A →
        ∀ E₀ : ℝ, RootRectangle F.1 (compressVar p s) E₀ r v₀ →
        ∀ (sel : CEH.EigenpairSelection (2 * p.W - 1)) (J : CEH.SourceMatrix (2 * p.W - 1)),
          J.IsHermitian → ‖J‖ ≤ 1 →
        ∀ U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ, Uᴴ * U = 1 →
          gueMeasure (PairSite p i) (pairTime p s)
              {G | ¬ NatWindowGood F sel (compressVar p s) E₀ β ε J (Uᴴ * G * U)} ≤
            ENNReal.ofReal (((2 * p.W - 1 : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨β₀, hβ₀, hβ₀', h⟩ :=
    BlockBand.LocalWindow.ProofPartTwo.GUEInputs.gueSource_not_natWindowGood_le hSp hMDE hETH A C sLo sHi r v₀ hsLo hsHi hr hv₀
  refine ⟨β₀, hβ₀, hβ₀', fun β hβ hββ ε D hε hD => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h β hβ hββ ε D hε hD
  refine ⟨N₀, fun p i hN s hs hsI F hKn E₀ hR sel J hJ hJn U hU => ?_⟩
  have hT := hN₀ (2 * p.W - 1) hN (compressVar p s) hsI F hKn E₀ hR sel J hJ hJn
  set T := {W : CEH.SourceHermitian (2 * p.W - 1) | ¬ NatWindowGood F sel (compressVar p s) E₀
    β ε J ((((Real.sqrt (compressVar p s)) : ℝ) : ℂ) • W.1)} with hTdef
  have hsub : {G : PairMatrix p i | ¬ NatWindowGood F sel (compressVar p s) E₀ β ε J
      (Uᴴ * G * U)} ⊆
      {G | Uᴴ * G * U ∈ compressSample p s '' T ∪ (range (compressSample p s))ᶜ} := by
    intro G hG
    by_cases hran : Uᴴ * G * U ∈ range (compressSample p s)
    · obtain ⟨W, hW⟩ := hran
      refine Or.inl ⟨W, ?_, hW⟩
      show ¬ NatWindowGood F sel (compressVar p s) E₀ β ε J (compressSample p s W)
      rw [hW]; exact hG
    · exact Or.inr hran
  calc _ ≤ _ := measure_mono hsub
    _ ≤ gueSourceLaw (2 * p.W - 1) T := gue_compress_preimage_union_le p hComp i hs U hU T
    _ ≤ _ := hT

end

end BlockBand.LocalWindow.ProofPartTwo.GUEInputs
