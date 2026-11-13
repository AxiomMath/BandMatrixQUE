module

public import BlockBand.LocalWindow.ProofPartTwoCompressETHNative
public import BlockBand.LocalWindow.ProofPartTwoLargeRho
public import BlockBand.LocalWindow.ProofPartTwoCompressCentre

/-!
# The compressed window estimate, recentred on the real axis

The window estimate for the compression of the fresh pair block to a `(2W - 1)`-dimensional
subspace; this is the `(2W - 1)`-dimensional analogue of
`LocalWindow.ProofPartTwo.gue_not_pairWindowGood_le`. The hypotheses are `NativeInputs`,
`GUEWignerFamilyAdapter`, `MDEBranchIdentification`, `ExternalETH` and
`CompressedGUELawBridgeStatement`; the root rectangle of the compressed deformation is a hypothesis
here, supplied by `compressRootRectangle_family`.

## Main results

* `NatWindowGood F sel s E₀ β ε J X`: `X` Hermitian and, for all labels `k, l` of `F + X` (native
  dimension `N`, eigenpairs selected by `sel`) with eigenvalues in `[E₀ - h, E₀ + h]`,
  `h = N^{-1+β}`: `|u_k* J u_l - δ_{kl} nativeCentre J F s μ_k| ≤ 2 N^ε N^{-1/2}`.
* `gue_compress_preimage_union_le`: `CompressedGUELawBridgeStatement` for the sets
  `√s' T ∪ (√s' · Herm)ᶜ` (the compressed noise is a.s. Hermitian).
* **`gue_not_compressWindowGood_le`**: the compressed window estimate: for an isometry
  `U : ℂ^{2W-1} → ℂ^{pair}`, `G ~ GUE_{2W}(s/2W)`, a compressed deformation `F` on `Fin (2W - 1)`
  with a root rectangle at `s' = s(1 - 1/2W)`: `P(¬ NatWindowGood F sel s' E₀ β ε J (U*GU)) ≤
  (2W - 1)^{-D}`.
* `nativeCentre_eq_compressCentre`, `isHermitian_compress_obs`, `opNorm_compress_le_eth`:
  at `F = U*MU`, `J' = U*JU` the centre is `compressCentre`, `J'` is a Hermitian contraction
  and `‖U*MU‖ ≤ ‖M‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofETH
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
## The window event
-/

section Native

variable {N : ℕ}

/-- The deformed matrix `F + X` as a Hermitian sample. -/
def natDeformed (F : CEH.SourceHermitian N) (X : CEH.SourceMatrix N) (hX : X.IsHermitian) :
    CEH.SourceHermitian N :=
  ⟨F.1 + X, F.2.add hX⟩

/-- **The window bound** (in dimension `N`): `X` is Hermitian and every
pair of selected eigenvectors of `F + X` with eigenvalues in `[E₀ - h, E₀ + h]`, `h = N^{-1+β}`,
has overlap error at most `2 N^ε N^{-1/2}` around the real-axis centre
`δ_{kl} nativeCentre J F s μ_k`. -/
def NatWindowGood (F : CEH.SourceHermitian N) (sel : CEH.EigenpairSelection N)
    (s E₀ β ε : ℝ) (J X : CEH.SourceMatrix N) : Prop :=
  ∃ hX : X.IsHermitian, ∀ k l : Fin N,
    sel.eigenvalue (natDeformed F X hX) k ∈
        Icc (E₀ - (N : ℝ) ^ (-1 + β)) (E₀ + (N : ℝ) ^ (-1 + β)) →
    sel.eigenvalue (natDeformed F X hX) l ∈
        Icc (E₀ - (N : ℝ) ^ (-1 + β)) (E₀ + (N : ℝ) ^ (-1 + β)) →
    ‖CEH.sourceMatrixElement J (sel.eigenvector (natDeformed F X hX) k)
          (sel.eigenvector (natDeformed F X hX) l) -
        (if k = l then nativeCentre J F.1 s (sel.eigenvalue (natDeformed F X hX) k) else 0)‖ ≤
      2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (-(1 : ℝ) / 2))

theorem isHermitian_sqrt_smul (s : ℝ) (W : CEH.SourceHermitian N) :
    ((((Real.sqrt s) : ℝ) : ℂ) • W.1).IsHermitian :=
  W.2.smul (by simp [IsSelfAdjoint])

/-- **The external ETH theorem in dimension `N`, recentred at the real-axis centre**
(the analogue of `LocalWindow.ProofPartTwo.gue_not_pairWindowGood_le`). Fixed `A, C`,
`[sLo, sHi] ⊂ (0,∞)`, the rectangle radius `r > 0` and lower bound `v₀ > 0` first; then
`β₀ ∈ (0, 1/2]`; then `0 < β < β₀`, `ε, D > 0`; then `N₀`. Uniformly in `N ≥ N₀`, `s ∈ [sLo, sHi]`, Hermitian `F` with
`s^{-1/2}‖F‖ ≤ C N^A`, `E₀` with `RootRectangle F s E₀ r v₀`, eigenpair selections and Hermitian
contractions `J`: under `W ~ gueSourceLaw N`,
`P(¬ NatWindowGood F sel s E₀ β ε J (√s W)) ≤ N^{-D}`. -/
theorem gueSource_not_natWindowGood_le (inputs : NativeInputs.{0})
    (hAd : GUEWignerFamilyAdapter) (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
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
  obtain ⟨spacing, hsp⟩ := nat_exists_small_spacing inputs hAd hMDE hs M h4 hv₀
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

end Native

/-!
## The compressed window estimate
-/

section Compressed

variable (p : Parameters)

/-- **The compressed fresh noise, a.s. Hermitian form**
(`CompressedGUELawBridgeStatement`): for an isometry `U : Fin (2W - 1) → PairSite` and every set
`T` of samples, `GUE_{2W}(s/2W){G : U*GU ∈ √s' T ∪ (range √s')ᶜ} ≤ gueSourceLaw (2W-1) T`
(no measurability needed). -/
theorem gue_compress_preimage_union_le (hComp : CompressedGUELawBridgeStatement) (i : ZMod p.n)
    {s : ℝ} (hs : 0 < s) (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ) (hU : Uᴴ * U = 1)
    (T : Set (CEH.SourceHermitian (2 * p.W - 1))) :
    gueMeasure (PairSite p i) (pairTime p s)
        {G | Uᴴ * G * U ∈ compressSample p s '' T ∪ (range (compressSample p s))ᶜ} ≤
      gueSourceLaw (2 * p.W - 1) T := by
  have hf : Measurable fun G : PairMatrix p i => Uᴴ * G * U :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have h := Measure.le_map_apply (μ := gueMeasure (PairSite p i) (pairTime p s)) hf.aemeasurable
    (compressSample p s '' T ∪ (range (compressSample p s))ᶜ)
  rw [hComp p i s hs U hU] at h
  have e : (gueSourceLaw (2 * p.W - 1)).map
      (fun W => (((Real.sqrt (s * (1 - 1 / (2 * (p.W : ℝ))))) : ℝ) : ℂ) • W.1) =
      (gueSourceLaw (2 * p.W - 1)).map (compressSample p s) := rfl
  have hset : compressSample p s ⁻¹' (compressSample p s '' T ∪ (range (compressSample p s))ᶜ) =
      T := by
    rw [preimage_union, (measurableEmbedding_compressSample p hs).injective.preimage_image,
      preimage_compl, preimage_range, compl_univ, union_empty]
  rw [e, (measurableEmbedding_compressSample p hs).map_apply, hset] at h
  exact h

/-- **The compressed window estimate** (the external ETH theorem at `N = 2W - 1`,
variance `s' = s(1 - 1/(2W))`, recentred at the real-axis compressed centre).
Fixed `A, C`, `[sLo, sHi] ⊂ (0,∞)`, `r, v₀ > 0` first; then `β₀ ∈ (0, 1/2]`; then `0 < β < β₀`,
`ε, D > 0`; then `N₀`. Uniformly in `p, i` with `N₀ ≤ 2W - 1`, `s > 0` with `s' ∈ [sLo, sHi]`,
compressed deformations `F` on `Fin (2W - 1)` with `s'^{-1/2}‖F‖ ≤ C (2W-1)^A` and
`RootRectangle F s' E₀ r v₀`, eigenpair selections, Hermitian contractions `J` and isometries `U`:
under `G ~ GUE_{2W}(s/2W)`, `P(¬ NatWindowGood F sel s' E₀ β ε J (U*GU)) ≤ (2W - 1)^{-D}`. -/
theorem gue_not_compressWindowGood_le (inputs : NativeInputs.{0})
    (hAd : GUEWignerFamilyAdapter) (hMDE : MDEBranchIdentification) (hETH : ExternalETH)
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
    gueSource_not_natWindowGood_le inputs hAd hMDE hETH A C sLo sHi r v₀ hsLo hsHi hr hv₀
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

end Compressed

/-!
## The compressed deformation and observable
-/

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- At `N = 2W - 1` the real-axis centre is the compressed centre `compressCentre`. -/
theorem nativeCentre_eq_compressCentre (J' B : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ)
    (s' x : ℝ) : nativeCentre J' B s' x = compressCentre p J' B s' x := rfl

/-- `‖U*XU‖ ≤ ‖X‖` for an isometry `U`. -/
theorem opNorm_compress_le_eth {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) (X : Matrix ι ι ℂ) :
    ‖Uᴴ * X * U‖ ≤ ‖X‖ := by
  calc ‖Uᴴ * X * U‖ ≤ ‖Uᴴ * X‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Uᴴ‖ * ‖X‖) * ‖U‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (compress_opNorm_isometry_adj_le hU)
          (norm_nonneg _)) (compress_opNorm_isometry_le hU) (norm_nonneg _) (by positivity)
    _ = ‖X‖ := by ring

/-- The compressed observable `U*JU` of a Hermitian pair contraction is a Hermitian
contraction. -/
theorem isHermitian_compress_obs {J : PairMatrix p i} (hJ : J.IsHermitian)
    (U : Matrix (PairSite p i) (Fin (2 * p.W - 1)) ℂ) : (Uᴴ * J * U).IsHermitian :=
  isHermitian_compress hJ U

end Pair

end BlockBand.LocalWindow.ProofPartTwo
