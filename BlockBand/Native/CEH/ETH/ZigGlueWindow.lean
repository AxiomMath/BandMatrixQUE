module

public import BlockBand.Native.CEH.ETH.ZigGlueFlow

/-!
# CEH ETH: window constants uniform in `s`, and the degenerate observable

Constants for the spectral window that depend only on the window parameters and not on `s`, the
eventual bounds in `N` used by the zig closure, and the case of a vanishing observable.

* `zgl_window_B`: `|ζ₁ - ζ̄₂| ≤ 8/c` (`= 4 s K'` with `K' = 2/(sc)`), from
  `norm_zeta_sub_conj_le_of_theta`.
* `zgl_cehETHRegularizedObservable_eq`, `zgl_reg_of_theta`: under `θ = 1`,
  `A° = regularizedObservable 1 M₁ M₂ᴴ J` and `⟨M₁ A° M₂ᴴ⟩ = 0`.
* `zgl_lemma56_window_uniform`: for every `σ ∈ [0, s]` the five Lemma 5.6 bounds of
  `lemma56_window_bound_hermitian` for `A°` hold with the constant `zgl_C56 sLo c =
  lemma56Const sLo K₀ (c/2) (8/c)`, depending only on `(sLo, c)` (`lemma56Const` is antitone in
  `s`, `zgl_lemma56Const_anti`).
* `zgl_N2_window_uniform`: `ρ₁ρ₂ s₂(s)² ≤ zgl_CN2 sLo sHi c` (`s₂(s) = sTwoAt s`),
  depending only on `(sLo, sHi, c)`.
* `zgl_eventually_density`: `∃ N₀(ε₀, κ_ρ)`, `N ≥ N₀`, `η ≥ N^{ε₀-1}`, `ρ ≥ κ_ρ` ⟹
  `N^{ε₀/2} ≤ N η ρ`; `zgl_eventually_rpow_le`: `N^{ε₁-1} ≤ h` eventually (`ε₁ < 1`, `h > 0`).
* **Degenerate observable.** `zgl_measure_bad_eq_zero_of_eq_zero`: if `A = 0` the bad
  event `{N^ε ≤ ‖cehPositiveChain (F + G ω) z₁ z₂ A‖}` is empty (`N > 0`).
  `zgl_sTwoBase_pos`, `zgl_sTwoAt_pos`: if `A ≠ 0` then `⟨Γ₁AΓ₂Aᴴ⟩ > 0` and `s₂(σ) > 0` for every
  `σ ≥ 0` (MDE solutions at `Im zᵢ > 0`, `N > 0`). `zgl_chain_eq_sTwoAt_zero`:
  `Z₀ = Re⟨Im M₁ A Im M₂ Aᴴ⟩ = π² ρ₁ρ₂ s₂(0)²`, hence `zgl_chain_lt_threshold_zero`:
  `Z₀ < T ρ₁ρ₂ s₂(0)²` whenever `π² < T` and `A ≠ 0`; `zgl_flowResolvent_zero`: `R_{i,0} = Mᵢ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open CEHNative.BlockBand.CEH (quantitativeIFTHeight quantitativeIFTRadius)
open BlockBand.Native.CEH.Flow
open scoped NNReal ENNReal ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
## The constants
-/

/-- `K₀ = 2/(sLo c)`: bound on `‖Mᵢ‖`, `|mᵢ|`, `Im mᵢ` on the window, uniform in `s ≥ sLo`. -/
def zgl_K₀ (sLo c : ℝ) : ℝ := 2 / (sLo * c)

/-- The Lemma 5.6 constant uniform in `s ∈ [sLo, sHi]`. -/
def zgl_C56 (sLo c : ℝ) : ℝ := lemma56Const sLo (zgl_K₀ sLo c) (c / 2) (8 / c)

/-- The constant in the bound on `ρ₁ρ₂ s₂(s)²`, uniform in `s ∈ [sLo, sHi]`. -/
def zgl_CN2 (sLo sHi c : ℝ) : ℝ :=
  (1 + 2 * sHi * zgl_K₀ sLo c ^ 2) ^ 2 *
    (zgl_K₀ sLo c ^ 2 + zgl_K₀ sLo c ^ 4 / (2 * (c / 2) ^ 2)) / Real.pi ^ 2

/-- `lemma56Const` is antitone in `s`. -/
theorem zgl_lemma56Const_anti {s s' K κ B : ℝ} (hs' : 0 < s') (hss : s' ≤ s) (hK : 0 ≤ K)
    (hκ : 0 < κ) (hB : 0 ≤ B) : lemma56Const s K κ B ≤ lemma56Const s' K κ B := by
  have hs : 0 < s := hs'.trans_le hss
  unfold lemma56Const
  gcongr

/-- The IFT height cutoff is monotone in `s`. -/
theorem zgl_quantitativeIFTHeight_mono {s s' c : ℝ} (hs' : 0 < s') (hss : s' ≤ s)
    (hc : 0 < c) : quantitativeIFTHeight s' c ≤ quantitativeIFTHeight s c := by
  unfold quantitativeIFTHeight quantitativeIFTRadius
  have hs : 0 < s := hs'.trans_le hss
  gcongr

theorem zgl_quantitativeIFTHeight_pos {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    0 < quantitativeIFTHeight s c := by
  unfold quantitativeIFTHeight quantitativeIFTRadius
  positivity

/-!
## One window point
-/

/-- **One window point**: for `0 < sLo ≤ s`, `Re z` in the window and
`0 < Im z ≤ quantitativeIFTHeight sLo c`: `c/2 < Im m`, `‖M‖ ≤ K₀`, `|m| ≤ K₀`, `Im m ≤ K₀`,
`c/(2π) ≤ cehDensityOf M`, `c/(2π) ≤ sourceDensity M` (`M = Mf z`, `m = ⟨M⟩`). -/
theorem zgl_window_point (hN : 0 < N) {F : LocalETHMatrix N} (hF : F.IsHermitian)
    {sLo s : ℝ} (hsLo : 0 < sLo) (hss : sLo ≤ s) {Mf : ℂ → LocalETHMatrix N}
    (hMf : IsLocalETHMDEBranch s F Mf) {E₀ r c K : ℝ} (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K) {z : ℂ}
    (hzr : z.re ∈ Ioo (E₀ - r) (E₀ + r)) (hz : 0 < z.im)
    (hzH : z.im ≤ quantitativeIFTHeight sLo c) :
    c / 2 < (NTrace (Mf z)).im ∧ ‖Mf z‖ ≤ zgl_K₀ sLo c ∧ ‖NTrace (Mf z)‖ ≤ zgl_K₀ sLo c ∧
      (NTrace (Mf z)).im ≤ zgl_K₀ sLo c ∧ c / (2 * Real.pi) ≤ cehDensityOf (Mf z) ∧
      c / (2 * Real.pi) ≤ BlockBand.External.CEH.sourceDensity (Mf z) := by
  have hs : 0 < s := hsLo.trans_le hss
  have hzH' : z.im ≤ quantitativeIFTHeight s c :=
    hzH.trans (zgl_quantitativeIFTHeight_mono hsLo hss hc)
  have hregC := CEHNative.BlockBand.CEH.localETHRegularBoundaryWindow_canonical_of_branch hF hs
    hMf hreg
  obtain ⟨Mb, Mb', hdata⟩ := hregC.boundary
  obtain ⟨hb, -, -, hdens, -, hstab⟩ := hdata z.re hzr
  have hhalf := half_lt_im_upperBranch_of_boundary hN hF hs hc hb hdens hstab hz hzH'
  have hnorm := norm_hermitianMDEBranch_le_two_div_of_half_lt hN hF hs hc hhalf hz
  have hzeq : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  rw [hzeq] at hhalf hnorm
  have hMfz : Mf z = CEHNative.BlockBand.CEH.hermitianMDEBranch hF hs z :=
    CEHNative.BlockBand.CEH.localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf hz.ne'
  have htr : NTrace (Mf z) = CEHNative.BlockBand.CEH.upperBranch hN
      (CEHNative.BlockBand.CEH.hermitianSpectrum hF) hs z := by
    rw [hMfz]
    change Conventions.normalizedTrace _ = _
    rw [CEHNative.BlockBand.CEH.normalizedTrace_hermitianMDEBranch hF hN hs hz.ne',
      CEHNative.BlockBand.CEH.hermitianMDEMean_of_im_pos hF hN hs hz]
  have hK₀ : 2 / (s * c) ≤ zgl_K₀ sLo c := by
    unfold zgl_K₀
    gcongr
  have h1 : c / 2 < (NTrace (Mf z)).im := by rw [htr]; exact hhalf
  have h2 : ‖Mf z‖ ≤ zgl_K₀ sLo c := by rw [hMfz]; exact hnorm.trans hK₀
  have h3 : ‖NTrace (Mf z)‖ ≤ zgl_K₀ sLo c := (norm_NTrace_le_l2_opNorm hN _).trans h2
  have h4 : (NTrace (Mf z)).im ≤ zgl_K₀ sLo c := (Complex.im_le_norm _).trans h3
  have hπ := Real.pi_pos
  have h5 : c / (2 * Real.pi) ≤ cehDensityOf (Mf z) := by
    rw [cehDensityOf_eq, div_le_div_iff₀ (by positivity) hπ]
    nlinarith
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  have hpos : 0 ≤ (NTrace (Mf z)).im := by linarith
  rw [BlockBand.External.CEH.sourceDensity, ← NTrace_eq_normalizedTrace, abs_of_nonneg hpos]
  rw [cehDensityOf_eq] at h5
  exact h5

/-!
## Pair facts under `θ = 1`
-/

section Pair

variable {F : LocalETHMatrix N} {s : ℝ} {Mf : ℂ → LocalETHMatrix N} {z₁ z₂ : ℂ}

/-- `θ = 1` gives `Re(s⟨M₁M₂ᴴ⟩) ≥ 1/2`, hence `⟨M₁M₂ᴴ⟩ ≠ 0`. -/
theorem zgl_NTrace_ne_zero_of_theta {M₁ M₂ : LocalETHMatrix N}
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1) :
    NTrace (M₁ * M₂ᴴ) ≠ 0 := by
  have harg : 0 ≤ ((Real.sqrt s : ℂ) ^ 2 * NTrace (M₁ * M₂ᴴ)).re - 1 / 2 := by
    by_contra hneg
    unfold regularizationCoefficient at hθ
    rw [cehTheta_of_neg (not_le.mp hneg)] at hθ
    norm_num at hθ
  intro h0
  rw [h0, mul_zero, Complex.zero_re] at harg
  linarith

/-- Under `θ = 1`, the CEH regularized observable is `regularizedObservable 1 M₁ M₂ᴴ J`. -/
theorem zgl_cehETHRegularizedObservable_eq
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1)
    (J : LocalETHMatrix N) :
    cehETHRegularizedObservable s Mf z₁ z₂ J = regularizedObservable 1 (Mf z₁) (Mf z₂)ᴴ J := by
  rw [cehETHRegularizedObservable, hθ]

/-- Under `θ = 1`, `A°` is `(z₁, z₂)`-regular: `⟨M₁ A° M₂ᴴ⟩ = 0`. -/
theorem zgl_reg_of_theta
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1)
    (J : LocalETHMatrix N) :
    NTrace (Mf z₁ * cehETHRegularizedObservable s Mf z₁ z₂ J * (Mf z₂)ᴴ) = 0 := by
  rw [zgl_cehETHRegularizedObservable_eq hθ]
  exact regularizedObservable_trace_zero _ _ _ (zgl_NTrace_ne_zero_of_theta hθ)

variable {sLo sHi : ℝ} {E₀ r c K : ℝ}

/-- **The `B` bound**: on the window, under `θ = 1`, `|ζ₁ - ζ̄₂| ≤ 8/c`. -/
theorem zgl_window_B (hN : 0 < N) (hF : F.IsHermitian) (hsLo : 0 < sLo) (hss : sLo ≤ s)
    (hMf : IsLocalETHMDEBranch s F Mf) (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hz₁r : z₁.re ∈ Ioo (E₀ - r) (E₀ + r)) (hz₂r : z₂.re ∈ Ioo (E₀ - r) (E₀ + r))
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (hz₁H : z₁.im ≤ quantitativeIFTHeight sLo c)
    (hz₂H : z₂.im ≤ quantitativeIFTHeight sLo c)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1) :
    ‖(z₁ + (s : ℂ) * NTrace (Mf z₁)) - conj (z₂ + (s : ℂ) * NTrace (Mf z₂))‖ ≤ 8 / c := by
  have hs : 0 < s := hsLo.trans_le hss
  have hzeta := norm_zeta_sub_conj_le_of_theta hN hF hs hz₁ hz₂ (hMf z₁ hz₁.ne')
    (hMf z₂ hz₂.ne') hθ
  -- `|mᵢ| ≤ ‖Mᵢ‖ ≤ 2/(sc)`
  have hm (z : ℂ) (hzr : z.re ∈ Ioo (E₀ - r) (E₀ + r)) (hz : 0 < z.im)
      (hzH : z.im ≤ quantitativeIFTHeight sLo c) : ‖NTrace (Mf z)‖ ≤ 2 / (s * c) := by
    have hzH' : z.im ≤ quantitativeIFTHeight s c :=
      hzH.trans (zgl_quantitativeIFTHeight_mono hsLo hss hc)
    have hregC := CEHNative.BlockBand.CEH.localETHRegularBoundaryWindow_canonical_of_branch hF
      hs hMf hreg
    obtain ⟨Mb, Mb', hdata⟩ := hregC.boundary
    obtain ⟨hb, -, -, hdens, -, hstab⟩ := hdata z.re hzr
    have hhalf := half_lt_im_upperBranch_of_boundary hN hF hs hc hb hdens hstab hz hzH'
    have hnorm := norm_hermitianMDEBranch_le_two_div_of_half_lt hN hF hs hc hhalf hz
    rw [Complex.re_add_im z] at hnorm
    rw [CEHNative.BlockBand.CEH.localETHMDEBranch_eq_hermitianMDEBranch_of_im_ne hF hs hMf
      hz.ne']
    exact (norm_NTrace_le_l2_opNorm hN _).trans hnorm
  have h1 := hm z₁ hz₁r hz₁ hz₁H
  have h2 := hm z₂ hz₂r hz₂ hz₂H
  have hsub : ‖NTrace (Mf z₁) - conj (NTrace (Mf z₂))‖ ≤ 2 / (s * c) + 2 / (s * c) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_conj]
    linarith
  refine hzeta.trans ?_
  calc 2 * s * ‖NTrace (Mf z₁) - conj (NTrace (Mf z₂))‖
      ≤ 2 * s * (2 / (s * c) + 2 / (s * c)) := by gcongr
    _ = 8 / c := by field_simp; ring

/-- **Lemma 5.6 with constants uniform in `s ∈ [sLo, sHi]`**: on the window,
under `θ = 1`, for `A° = cehETHRegularizedObservable s Mf z₁ z₂ J` and every `σ ∈ [0, s]`, the
five bounds of `lemma56_window_bound_hermitian` hold with `C = zgl_C56 sLo c`. -/
theorem zgl_lemma56_window_uniform (hN : 0 < N) (hF : F.IsHermitian) (hsLo : 0 < sLo)
    (hss : sLo ≤ s) (hMf : IsLocalETHMDEBranch s F Mf) (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hz₁r : z₁.re ∈ Ioo (E₀ - r) (E₀ + r)) (hz₂r : z₂.re ∈ Ioo (E₀ - r) (E₀ + r))
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (hz₁H : z₁.im ≤ quantitativeIFTHeight sLo c)
    (hz₂H : z₂.im ≤ quantitativeIFTHeight sLo c)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1)
    (J : LocalETHMatrix N) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσs : σ ≤ s) :
    let A := cehETHRegularizedObservable s Mf z₁ z₂ J
    let P := Real.sqrt (NTrace (matrixImaginaryPart (Mf z₁) * A * matrixImaginaryPart (Mf z₂) *
      Aᴴ)).re
    ‖NTrace (twoResApprox σ (Mf z₁) A (Mf z₂))‖ ≤ zgl_C56 sLo c * P ∧
      ‖NTrace (twoResApprox σ (Mf z₁)ᴴ A (Mf z₂)ᴴ)‖ ≤ zgl_C56 sLo c * P ∧
      NTrace (twoResApprox σ (Mf z₁) A (Mf z₂)ᴴ) = 0 ∧
      ‖NTrace (twoResApprox σ (Mf z₁)ᴴ A (Mf z₂))‖ ≤ zgl_C56 sLo c * P ∧
      ‖NTrace (hatApprox σ (Mf z₁) A (Mf z₂))‖ ≤ zgl_C56 sLo c * P := by
  intro A P
  have hs : 0 < s := hsLo.trans_le hss
  obtain ⟨p₁, -, -, k₁, -, -⟩ := zgl_window_point hN hF hsLo hss hMf hc hreg hz₁r hz₁ hz₁H
  obtain ⟨p₂, -, -, k₂, -, -⟩ := zgl_window_point hN hF hsLo hss hMf hc hreg hz₂r hz₂ hz₂H
  have hB := zgl_window_B hN hF hsLo hss hMf hc hreg hz₁r hz₂r hz₁ hz₂ hz₁H hz₂H hθ
  have hκ : (0 : ℝ) < c / 2 := by positivity
  have key := lemma56_window_bound_hermitian hN hF hs hκ hσ0 hσs hz₁ hz₂ (hMf z₁ hz₁.ne')
    (hMf z₂ hz₂.ne') A (zgl_reg_of_theta hθ J) p₁.le p₂.le k₁ k₂ hB
  have hK₀ : 0 ≤ zgl_K₀ sLo c := by unfold zgl_K₀; positivity
  have hC : lemma56Const s (zgl_K₀ sLo c) (c / 2) (8 / c) ≤ zgl_C56 sLo c :=
    zgl_lemma56Const_anti hsLo hss hK₀ hκ (by positivity)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hm := mul_le_mul_of_nonneg_right hC hP
  obtain ⟨a1, a2, a3, a4, a5⟩ := key
  exact ⟨a1.trans hm, a2.trans hm, a3, a4.trans hm, a5.trans hm⟩

/-- **The bound on `ρ₁ρ₂ s₂(s)²`, uniform in `s ∈ [sLo, sHi]`**: on the window, under `θ = 1`,
`ρ₁ρ₂ s₂(s)² ≤ zgl_CN2 sLo sHi c` with `s₂(s) = sTwoAt s` and `A° = cehETHRegularizedObservable`,
`‖J‖ ≤ 1`. -/
theorem zgl_N2_window_uniform (hN : 0 < N) (hF : F.IsHermitian) (hsLo : 0 < sLo)
    (hss : sLo ≤ s) (hsHi : s ≤ sHi) (hMf : IsLocalETHMDEBranch s F Mf) (hc : 0 < c)
    (hreg : LocalETHRegularBoundaryWindow s Mf E₀ r c K)
    (hz₁r : z₁.re ∈ Ioo (E₀ - r) (E₀ + r)) (hz₂r : z₂.re ∈ Ioo (E₀ - r) (E₀ + r))
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (hz₁H : z₁.im ≤ quantitativeIFTHeight sLo c)
    (hz₂H : z₂.im ≤ quantitativeIFTHeight sLo c)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1)
    (J : LocalETHMatrix N) (hJ : ‖J‖ ≤ 1) :
    cehDensityOf (Mf z₁) * cehDensityOf (Mf z₂) *
        sTwoAt s (Mf z₁) (Mf z₂) (cehETHRegularizedObservable s Mf z₁ z₂ J) ^ 2 ≤
      zgl_CN2 sLo sHi c := by
  have hs : 0 < s := hsLo.trans_le hss
  obtain ⟨p₁, n₁, -, -, -, -⟩ := zgl_window_point hN hF hsLo hss hMf hc hreg hz₁r hz₁ hz₁H
  obtain ⟨p₂, n₂, -, -, -, -⟩ := zgl_window_point hN hF hsLo hss hMf hc hreg hz₂r hz₂ hz₂H
  have hκ : (0 : ℝ) < c / 2 := by positivity
  have h₁ := hMf z₁ hz₁.ne'
  have h₂ := hMf z₂ hz₂.ne'
  have hm₁ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₁ (Mf z₁) :=
    ⟨h₁.inv, h₁.pos⟩
  have hm₂ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₂ (Mf z₂) :=
    ⟨h₂.inv, h₂.pos⟩
  have key := density_mul_sTwo_sq_le_mde hN hs hκ hm₁ hm₂ hz₁.ne' hz₂.ne' n₁ n₂ p₁.le p₂.le J
    hJ hθ
  rw [zgl_cehETHRegularizedObservable_eq hθ, sTwoAt_target hs.le]
  refine key.trans ?_
  unfold zgl_CN2
  have hK₀ : 0 ≤ zgl_K₀ sLo c := by unfold zgl_K₀; positivity
  gcongr

end Pair

/-!
## Eventual bounds in `N`
-/

/-- `N^{ε₀/2} ≤ N η ρ` for `N ≥ N₀(ε₀, κ_ρ)`, `η ≥ N^{ε₀-1}`, `ρ ≥ κ_ρ > 0`. -/
theorem zgl_eventually_density {ε₀ κρ : ℝ} (hε₀ : 0 < ε₀) (hκ : 0 < κρ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ η ρ : ℝ, (N : ℝ) ^ (ε₀ - 1) ≤ η → κρ ≤ ρ →
      (N : ℝ) ^ (ε₀ / 2) ≤ N * η * ρ := by
  set t := (κρ⁻¹) ^ (2 / ε₀) with ht
  refine ⟨⌈t⌉₊ + 1, fun N hN η ρ hη hρ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have htN : t ≤ N := by
    have h1 : t ≤ ⌈t⌉₊ := Nat.le_ceil t
    have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ _).trans hN
    linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg (inv_nonneg.2 hκ.le) _
  have hpow : κρ⁻¹ ≤ (N : ℝ) ^ (ε₀ / 2) := by
    have := Real.rpow_le_rpow ht0 htN (by positivity : (0 : ℝ) ≤ ε₀ / 2)
    rwa [ht, ← Real.rpow_mul (inv_nonneg.2 hκ.le), div_mul_div_comm, mul_comm 2 ε₀,
      div_self (by positivity), Real.rpow_one] at this
  have hsplit : (N : ℝ) ^ ε₀ = (N : ℝ) ^ (ε₀ / 2) * (N : ℝ) ^ (ε₀ / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hNη : (N : ℝ) ^ ε₀ ≤ N * η := by
    have e : (N : ℝ) * (N : ℝ) ^ (ε₀ - 1) = (N : ℝ) ^ ε₀ := by
      rw [Real.rpow_sub_one hN0.ne']; field_simp
    rw [← e]
    exact mul_le_mul_of_nonneg_left hη hN0.le
  have hp0 : 0 < (N : ℝ) ^ (ε₀ / 2) := Real.rpow_pos_of_pos hN0 _
  have hηpos : 0 ≤ N * η := le_trans (Real.rpow_nonneg hN0.le _) hNη
  calc (N : ℝ) ^ (ε₀ / 2) = (N : ℝ) ^ (ε₀ / 2) * (κρ⁻¹ * κρ) := by
        rw [inv_mul_cancel₀ hκ.ne', mul_one]
    _ ≤ (N : ℝ) ^ (ε₀ / 2) * ((N : ℝ) ^ (ε₀ / 2) * κρ) := by gcongr
    _ = (N : ℝ) ^ ε₀ * κρ := by rw [hsplit]; ring
    _ ≤ N * η * ρ := mul_le_mul hNη hρ hκ.le hηpos

/-- `N^{ε₁-1} ≤ h` for `N ≥ N₀(ε₁, h)`, `ε₁ < 1`, `h > 0`. -/
theorem zgl_eventually_rpow_le {ε₁ h : ℝ} (hε₁ : ε₁ < 1) (hh : 0 < h) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (N : ℝ) ^ (ε₁ - 1) ≤ h := by
  set t := (h⁻¹) ^ ((1 - ε₁)⁻¹) with ht
  refine ⟨⌈t⌉₊ + 1, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (Nat.le_add_left 1 _) hN
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N := by linarith
  have htN : t ≤ N := by
    have h1 : t ≤ ⌈t⌉₊ := Nat.le_ceil t
    have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (Nat.le_succ _).trans hN
    linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg (inv_nonneg.2 hh.le) _
  have hδ : 0 < 1 - ε₁ := by linarith
  have hpow : h⁻¹ ≤ (N : ℝ) ^ (1 - ε₁) := by
    have := Real.rpow_le_rpow ht0 htN hδ.le
    rwa [ht, ← Real.rpow_mul (inv_nonneg.2 hh.le), inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      at this
  have e : (N : ℝ) ^ (ε₁ - 1) = ((N : ℝ) ^ (1 - ε₁))⁻¹ := by
    rw [← Real.rpow_neg hN0.le, neg_sub]
  rw [e]
  have hp : 0 < (N : ℝ) ^ (1 - ε₁) := Real.rpow_pos_of_pos hN0 _
  rw [inv_le_comm₀ hp hh]
  exact hpow

/-!
## The degenerate observable
-/

/-- `cehPositiveChain H z₁ z₂ 0 = 0`. -/
theorem zgl_cehPositiveChain_zero (H : LocalETHMatrix N) (z₁ z₂ : ℂ) :
    cehPositiveChain H z₁ z₂ 0 = 0 := by
  simp [cehPositiveChain, NTrace, Conventions.normalizedTrace]

/-- **`A° = 0`: the bad event is empty** (`N > 0`), so it has measure `0`. -/
theorem zgl_measure_bad_eq_zero_of_eq_zero {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (hN : 0 < N) (ε : ℝ) (K : Ω → LocalETHMatrix N) (z₁ z₂ : ℂ) {A : LocalETHMatrix N}
    (hA : A = 0) :
    Q {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (K ω) z₁ z₂ A‖} = 0 := by
  have hpos : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hN) ε
  have : {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (K ω) z₁ z₂ A‖} = ∅ := by
    ext ω
    simp only [hA, zgl_cehPositiveChain_zero, norm_zero, Set.mem_ofPred_eq,
      Set.mem_empty_iff_false, iff_false, not_le]
    exact hpos
  rw [this, measure_empty]

section Positivity

variable {F : LocalETHMatrix N} {s : ℝ} {z₁ z₂ : ℂ} {M₁ M₂ : LocalETHMatrix N}

/-- **`A ≠ 0` ⟹ the chain at `σ = 0` is positive**: for MDE solutions at `Im zᵢ > 0`
(`N > 0`, `s ≥ 0`, `F` Hermitian), `0 < Re⟨Im M₁ A Im M₂ Aᴴ⟩`. -/
theorem zgl_chain_pos (hN : 0 < N) (hF : F.IsHermitian) (hs : 0 ≤ s) (hz₁ : 0 < z₁.im)
    (hz₂ : 0 < z₂.im) (h₁ : IsLocalETHMDESolution s F z₁ M₁)
    (h₂ : IsLocalETHMDESolution s F z₂ M₂) {A : LocalETHMatrix N} (hA : A ≠ 0) :
    0 < (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re := by
  have hm₁ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₁ M₁ :=
    ⟨h₁.inv, h₁.pos⟩
  have hm₂ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₂ M₂ :=
    ⟨h₂.inv, h₂.pos⟩
  set ζ₁ := z₁ + (s : ℂ) * BlockBand.External.CEH.normalizedTrace M₁
  set ζ₂ := z₂ + (s : ℂ) * BlockBand.External.CEH.normalizedTrace M₂
  have hR₁ : M₁ = Phase1.resolvent F ζ₁ := Phase1.mde_eq_resolvent hm₁
  have hR₂ : M₂ = Phase1.resolvent F ζ₂ := Phase1.mde_eq_resolvent hm₂
  have hζ₁ : 0 < ζ₁.im := by
    have := Phase1.mde_im_mul_im_spectral_pos hm₁ hz₁.ne' hs
    exact (mul_pos_iff_of_pos_left hz₁).1 this
  have hζ₂ : 0 < ζ₂.im := by
    have := Phase1.mde_im_mul_im_spectral_pos hm₂ hz₂.ne' hs
    exact (mul_pos_iff_of_pos_left hz₂).1 this
  have he : NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ) =
      BlockBand.External.CEH.normalizedTrace (bwImChain A (Phase1.resolvent F ζ₁)
        (Phase1.resolvent F ζ₂)) := by
    rw [zgl_matrixImaginaryPart_eq, zgl_matrixImaginaryPart_eq, ← hR₁, ← hR₂]
    rfl
  rw [he, bw_normalizedTrace_imChain_eq hF hζ₁.ne' hζ₂.ne', Complex.ofReal_re]
  refine mul_pos (mul_pos hζ₁ hζ₂) ?_
  -- `Re⟨YYᴴ⟩ > 0` for `Y = R₁ᴴ A R₂ ≠ 0`
  set Y := (Phase1.resolvent F ζ₁)ᴴ * A * Phase1.resolvent F ζ₂ with hY
  have hY0 : Y ≠ 0 := by
    intro h0
    have hu₁ : IsUnit (Phase1.resolvent F ζ₁)ᴴ := by
      rw [Phase1.resolvent_conjTranspose hF]
      exact Phase1.isUnit_resolvent hF (by simpa using hζ₁.ne')
    have hu₂ : IsUnit (Phase1.resolvent F ζ₂) := Phase1.isUnit_resolvent hF hζ₂.ne'
    rw [hY, hu₂.mul_left_eq_zero, hu₁.mul_right_eq_zero] at h0
    exact hA h0
  have hex : ∃ i j, Y i j ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hY0 (Matrix.ext hno)
  obtain ⟨i₀, j₀, hij⟩ := hex
  rw [bwChainMass, Phase1.normalizedTrace_mul_conjTranspose_self, Complex.ofReal_re]
  have hNr : (0 : ℝ) < (N : ℝ)⁻¹ := by positivity
  refine mul_pos hNr ?_
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
    ⟨i₀, Finset.mem_univ _, Finset.sum_pos' (fun j _ => by positivity)
      ⟨j₀, Finset.mem_univ _, by positivity⟩⟩

/-- **`A ≠ 0` ⟹ `⟨Γ₁AΓ₂Aᴴ⟩ > 0`.** -/
theorem zgl_sTwoBase_pos (hN : 0 < N) (hF : F.IsHermitian) (hs : 0 ≤ s) (hz₁ : 0 < z₁.im)
    (hz₂ : 0 < z₂.im) (h₁ : IsLocalETHMDESolution s F z₁ M₁)
    (h₂ : IsLocalETHMDESolution s F z₂ M₂) (ht₁ : 0 < (NTrace M₁).im)
    (ht₂ : 0 < (NTrace M₂).im) {A : LocalETHMatrix N} (hA : A ≠ 0) :
    0 < sTwoBase M₁ M₂ A := by
  have h := zgl_chain_pos hN hF hs hz₁ hz₂ h₁ h₂ hA
  rw [chain_eq_mul_sTwoBase M₁ M₂ A ht₁.ne' ht₂.ne'] at h
  exact (mul_pos_iff_of_pos_left (mul_pos ht₁ ht₂)).1 h

/-- **`A ≠ 0` ⟹ `s₂(σ) > 0`** for every `σ ≥ 0`. -/
theorem zgl_sTwoAt_pos (hN : 0 < N) (hF : F.IsHermitian) (hs : 0 ≤ s) (hz₁ : 0 < z₁.im)
    (hz₂ : 0 < z₂.im) (h₁ : IsLocalETHMDESolution s F z₁ M₁)
    (h₂ : IsLocalETHMDESolution s F z₂ M₂) (ht₁ : 0 < (NTrace M₁).im)
    (ht₂ : 0 < (NTrace M₂).im) {A : LocalETHMatrix N} (hA : A ≠ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    0 < sTwoAt σ M₁ M₂ A := by
  have hb := zgl_sTwoBase_pos hN hF hs hz₁ hz₂ h₁ h₂ ht₁ ht₂ hA
  have hle := sTwoBase_le_sTwoAt_sq hσ M₁ M₂ A
  have h0 : 0 ≤ sTwoAt σ M₁ M₂ A := Real.sqrt_nonneg _
  rcases h0.lt_or_eq with h | h
  · exact h
  · rw [← h] at hle; norm_num at hle; linarith

/-- **`Z₀ = π² ρ₁ρ₂ s₂(0)²`** (for `Im⟨Mᵢ⟩ > 0` and `⟨Γ₁AΓ₂Aᴴ⟩ ≥ 0`). -/
theorem zgl_chain_eq_sTwoAt_zero (ht₁ : 0 < (NTrace M₁).im) (ht₂ : 0 < (NTrace M₂).im)
    (A : LocalETHMatrix N) (hb : 0 ≤ sTwoBase M₁ M₂ A) :
    (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re =
      Real.pi ^ 2 * cehDensityOf M₁ * cehDensityOf M₂ * sTwoAt 0 M₁ M₂ A ^ 2 := by
  rw [chain_eq_mul_sTwoBase M₁ M₂ A ht₁.ne' ht₂.ne', sTwoAt, sTwoSqHybrid_zero,
    Real.sq_sqrt hb, cehDensityOf_eq, cehDensityOf_eq]
  field_simp

/-- **Strict start for `Z`**: if `A ≠ 0` and `π² < T`, then
`Z₀ < T ρ₁ρ₂ s₂(0)²` (MDE solutions at `Im zᵢ > 0`, `N > 0`, `s ≥ 0`). -/
theorem zgl_chain_lt_threshold_zero (hN : 0 < N) (hF : F.IsHermitian) (hs : 0 ≤ s)
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (h₁ : IsLocalETHMDESolution s F z₁ M₁)
    (h₂ : IsLocalETHMDESolution s F z₂ M₂) (ht₁ : 0 < (NTrace M₁).im)
    (ht₂ : 0 < (NTrace M₂).im) {A : LocalETHMatrix N} (hA : A ≠ 0) {T : ℝ}
    (hT : Real.pi ^ 2 < T) :
    (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re <
      T * cehDensityOf M₁ * cehDensityOf M₂ * sTwoAt 0 M₁ M₂ A ^ 2 := by
  have hb := zgl_sTwoBase_pos hN hF hs hz₁ hz₂ h₁ h₂ ht₁ ht₂ hA
  rw [zgl_chain_eq_sTwoAt_zero ht₁ ht₂ A hb.le]
  have hρ₁ : 0 < cehDensityOf M₁ := by rw [cehDensityOf_eq]; positivity
  have hρ₂ : 0 < cehDensityOf M₂ := by rw [cehDensityOf_eq]; positivity
  have hst := zgl_sTwoAt_pos hN hF hs hz₁ hz₂ h₁ h₂ ht₁ ht₂ hA le_rfl
  have hp : 0 < cehDensityOf M₁ * cehDensityOf M₂ * sTwoAt 0 M₁ M₂ A ^ 2 := by positivity
  nlinarith

end Positivity

/-- **The flow starts at `M`**: for `G 0 ω = 0` and `M` solving the MDE at `(s, F, z)`,
`R_0 = flowResolvent F G z ⟨M⟩ s 0 ω = M`; so `X, Y` start at `0` and `Z₀ = Re⟨Im M₁AIm M₂Aᴴ⟩`. -/
theorem zgl_flowResolvent_zero {Ω : Type*} {F : BlockBand.External.CEH.SourceHermitian N}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {ω : Ω} (hG0 : G 0 ω = 0) {s : ℝ≥0} {z : ℂ}
    {M : Matrix (Fin N) (Fin N) ℂ}
    (h : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE (s : ℝ) F z M) :
    flowResolvent F.1 G z (BlockBand.External.CEH.normalizedTrace M) s 0 ω = M := by
  conv_rhs => rw [Phase1.mde_eq_resolvent h]
  rw [zgl_flowResolvent_eq_resolvent, hG0, add_zero]
  simp [flowSpectral]

end BlockBand.Native.CEH.ETH
