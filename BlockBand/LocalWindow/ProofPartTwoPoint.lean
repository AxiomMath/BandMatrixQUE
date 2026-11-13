module

public import BlockBand.LocalWindow.ProofETHPairSpacing

/-!
# The pair ETH at one grid point, with the real-axis centre

The external ETH theorem for the fresh pair block at one grid point, recentred at the real-axis
window centre, for part (ii) of the physical local-window lemma.

## Main results

* `PairRootRectangle`: the root rectangle of `K` on the pair (`Im m ≥ v₀` at every `x + iη`,
  `|x - E₀| ≤ r`, `0 ≤ η ≤ 1`).
* `pairCentre J K s x = d⁻¹ Tr(J Γ_K(x))`, `re_pairCentre` (it is `windowCenter`).
* `PairWindowGood`: `G` Hermitian and, for all labels `k, l` of `K + G` with eigenvalues in
  `[E₀ - h, E₀ + h]`, `h = (2W)^{-1+β}`: `|e_k* J e_l - δ_{kl} pairCentre(μ_k)| ≤ 2 (2W)^ε (2W)^{-1/2}`.
* `eventually_const_mul_rpow_le`: `c n^a ≤ 1` eventually for `a < 0`.
* **`gue_not_pairWindowGood_le`**: fixed `A, C, [sLo, sHi], r, v₀`; then `β₀ ∈ (0, 1/2]`; then
  `0 < β < β₀`, `ε, D > 0`; then `N₀`; uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`,
  Hermitian `K` with `s^{-1/2}‖K‖ ≤ C (2W)^A`, `E₀` with `PairRootRectangle K s E₀ r v₀`, eigenpair
  selections and Hermitian pair contractions `J`:
  `GUE_{2W}(s/2W){¬ PairWindowGood} ≤ (2W)^{-D}`.

Proof: the branch exists (`MDEBranchIdentification`), the root rectangle gives the regular
window (`regularWindow_of_rootRectangle`, constant `regK sLo v₀` by `regK_anti`) and a typical
spacing `η_f ≤ π/(N v₀)` (`exists_small_spacing`); the pair ETH holds with `ξ = β/2`
(`gue_not_pairETHGood_le`), and `ethCentre_close` with `root_lipschitz` moves the centre from
`μ + iN^ξ η_f(μ)` to `μ` at cost `Im z (3 + 1/(s v₀²))/(s v₀) ≤ C N^{ξ-1} ≤ N^{ε-1/2}`.
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

variable {p : Parameters} {i : ZMod p.n}

/-- The root rectangle of a pair deformation `K` (the conclusion of
`ProofETH.rootRectangle_of_poleCertificate`): at every `x + iη`, `|x - E₀| ≤ r`, `0 ≤ η ≤ 1`, a
Dyson root of `K` with `Im m ≥ v₀`. -/
def PairRootRectangle (K : PairMatrix p i) (s E₀ r v₀ : ℝ) : Prop :=
  ∀ x : ℝ, |x - E₀| ≤ r → ∀ η : ℝ, 0 ≤ η → η ≤ 1 →
    ∃ m : ℂ, IsDysonRoot K s ((x : ℂ) + (η : ℂ) * Complex.I) m ∧ v₀ ≤ m.im

/-- The complex real-axis window centre `d⁻¹ Tr(J Γ_K(x))` (`j_B(E, λ)` with
`K = K₀(E)`, `B = J`, `λ = x`, before taking the real part). -/
def pairCentre (J K : PairMatrix p i) (s x : ℝ) : ℂ :=
  (((2 * (p.W : ℝ))⁻¹ : ℝ) : ℂ) * (J * BlockBand.LocalWindow.windowGamma p i K s x).trace

theorem re_pairCentre (J K : PairMatrix p i) (s x : ℝ) :
    (pairCentre J K s x).re = BlockBand.LocalWindow.windowCenter p i J K s x :=
  (windowCenter_eq_re J K s x).symm

/-- **The pair window bound at one grid point**: `G` is Hermitian and every
pair of selected eigenvectors of `K + G` with eigenvalues in `[E₀ - h, E₀ + h]`,
`h = (2W)^{-1+β}`, has overlap error at most `2 (2W)^ε (2W)^{-1/2}` around the real-axis centre
`δ_{kl} pairCentre J K s μ_k`. -/
def PairWindowGood (K : PairMatrix p i) (hK : K.IsHermitian)
    (sel : CEH.EigenpairSelection (2 * p.W)) (s E₀ β ε : ℝ) (J G : PairMatrix p i) : Prop :=
  ∃ hG : G.IsHermitian, ∀ k l : PairSite p i,
    pairEigval sel (K + G) (hK.add hG) k ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) →
    pairEigval sel (K + G) (hK.add hG) l ∈
        Icc (E₀ - ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) (E₀ + ((2 * p.W : ℕ) : ℝ) ^ (-1 + β)) →
    ‖star (pairEigvec sel (K + G) (hK.add hG) k) ⬝ᵥ (J *ᵥ pairEigvec sel (K + G) (hK.add hG) l) -
        (if k = l then pairCentre J K s (pairEigval sel (K + G) (hK.add hG) k) else 0)‖ ≤
      2 * (((2 * p.W : ℕ) : ℝ) ^ ε * ((2 * p.W : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))

/-- `c n^a ≤ 1` for all large `n : ℕ` when `a < 0`. -/
theorem eventually_const_mul_rpow_le (c a : ℝ) (ha : a < 0) :
    ∀ᶠ n : ℕ in atTop, c * ((n : ℕ) : ℝ) ^ a ≤ 1 := by
  have h0 : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ) ^ a) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := -a) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using this
  have h1 : Tendsto (fun n : ℕ => c * ((n : ℕ) : ℝ) ^ a) atTop (𝓝 0) := by
    simpa using h0.const_mul c
  exact (h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le

/-- The centre move of `ethCentre_close` at `x₀ = x` on a root rectangle:
`‖ethCentre - pairCentre‖ ≤ Im z (3 + 1/(s v₀²))/(s v₀)`, `z = x + iN^ξ η_f(x)`. -/
theorem ethCentre_sub_pairCentre_le (hMDE : MDEBranchIdentification) {s : ℝ} (hs : 0 < s)
    {K : PairMatrix p i} (hK : K.IsHermitian)
    (M : CEH.MDEBranch (Real.sqrt s) (toSourceHermitian K hK)) (spacing : CEH.TypicalSpacing M)
    (ξ : ℝ) {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1) {x : ℝ} {m m₀ : ℂ} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hroot : IsDysonRoot K s (CEH.inflatedSpectralPoint spacing ξ x) m) (hm : v₀ ≤ m.im)
    (hroot₀ : IsDysonRoot K s (x : ℂ) m₀) (hm₀ : v₀ ≤ m₀.im) :
    ‖ethCentre M spacing ξ J x - pairCentre J K s x‖ ≤
      (CEH.inflatedSpectralPoint spacing ξ x).im * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := by
  have : Nonempty (PairSite p i) := ⟨⟨(i, ⟨0, p.W_pos⟩), Or.inl rfl⟩⟩
  set z := CEH.inflatedSpectralPoint spacing ξ x with hz
  have hzim : 0 < z.im := inflatedSpectralPoint_im_pos spacing ξ x
  have hc := ethCentre_close hMDE hs hK M spacing ξ hJ hroot hroot₀
  have hzx : z - (x : ℂ) = ((z.im : ℝ) : ℂ) * Complex.I := by
    rw [hz]; unfold CEH.inflatedSpectralPoint; simp
  have hzx' : ‖z - (x : ℂ)‖ = z.im := by
    rw [hzx, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hzim]
  have hlip := root_lipschitz hK hs hzim.le (by simp) hroot hroot₀ hv₀ hm hm₀
  rw [hzx'] at hlip
  have hw : ‖(z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀)‖ ≤ z.im * (1 + s * rootLip s v₀) := by
    have e : (z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀) = (z - (x : ℂ)) + (s : ℂ) * (m - m₀) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [hzx', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    nlinarith
  have hsr : s * rootLip s v₀ = 1 / (2 * (s * v₀ ^ 2)) := by
    unfold rootLip; field_simp
  have hsv : 0 < s * v₀ := mul_pos hs hv₀
  have h1 : z.im / (s * m.im) ≤ z.im / (s * v₀) :=
    div_le_div_of_nonneg_left hzim.le hsv (mul_le_mul_of_nonneg_left hm hs.le)
  have h2 : 2 * ‖(z + (s : ℂ) * m) - ((x : ℂ) + (s : ℂ) * m₀)‖ / (s * m₀.im) ≤
      2 * (z.im * (1 + s * rootLip s v₀)) / (s * v₀) := by
    have hrl := mul_nonneg hs.le (rootLip_nonneg s v₀)
    refine div_le_div₀ (mul_nonneg zero_le_two (mul_nonneg hzim.le (by linarith)))
      (by linarith) hsv
      (mul_le_mul_of_nonneg_left hm₀ hs.le)
  calc _ ≤ _ := hc
    _ ≤ z.im / (s * v₀) + 2 * (z.im * (1 + s * rootLip s v₀)) / (s * v₀) := add_le_add h1 h2
    _ = z.im * ((3 + 1 / (s * v₀ ^ 2)) / (s * v₀)) := by
        rw [hsr]; field_simp; ring

/-- **The pair ETH with the real-axis centre at one grid point** (the external
ETH theorem via `gue_not_pairETHGood_le`). Fixed `A, C`, `[sLo, sHi] ⊂ (0,∞)`,
the rectangle radius `r > 0` and lower bound `v₀ > 0` first; then `β₀ ∈ (0, 1/2]`; then
`0 < β < β₀`, `ε, D > 0`; then `N₀`. Uniformly in `p, i` with `2W ≥ N₀`, `s ∈ [sLo, sHi]`,
Hermitian pair deformations `K` with `s^{-1/2}‖K‖ ≤ C (2W)^A`, `E₀` with
`PairRootRectangle K s E₀ r v₀`, eigenpair selections and Hermitian pair contractions `J`:
under `G ~ GUE_{2W}(s/2W)`, `P(¬ PairWindowGood K sel s E₀ β ε J G) ≤ (2W)^{-D}`. -/
theorem gue_not_pairWindowGood_le (inputs : NativeInputs.{0}) (hAd : GUEWignerFamilyAdapter)
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
  obtain ⟨spacing, hsp⟩ := exists_small_spacing inputs hAd hMDE hs hK M h4 hv₀
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

end BlockBand.LocalWindow.ProofPartTwo
