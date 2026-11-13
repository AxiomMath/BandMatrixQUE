module

public import BlockBand.Critical.MatrixClosing.Poles.GoodEventEvents
public import BlockBand.Critical.MatrixClosing.PolesPos
public import BlockBand.Critical.MatrixClosing.Mean

/-!
# The collar good event; matrix closing from the relative mixed vectors theorem

*Law.* `layerLaw W b .common` (end diagonals `A_j ~ GUE_W(c/W)`, bonds `Gin(b/W)`), `c = 1 - 2b`,
along an admissible old sequence (`OldSequence`: `W_n → ∞`, `e_n ∈ bulkInterval κ`, Hermitian
`X_n` with `d(X_n) → 0`, orthonormal `J_n`).

* **`collarGoodEvent_holds (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
  (source : PSSS.SourceContract) (r : ℕ) : CollarGoodEventAt r`** (every rank, in
  particular `r ≥ 1`). Fresh constants: `A = 7` and `(r₀, s₀, v₀)` of the regularity
  certificate at `c = 1 - 2b`, `V = √(4 - (2-κ')²)/2`, `κ' = min κ 1` (independent of `ε`). For
  `ε, η > 0` the bad set is contained in
  `regᶜ ∪ {‖L‖² > R} ∪ ⋃_{ij}{|u_i^*(LL^* - E LL^*)u_j| > ε/(3λ)}` once `W ≥ W₀` and
  `d(X) ≤ d₀` and `λC(d + W⁻²) ≤ ε/3`, with `R = C₄⁴/η + 1` and the trace threshold
  `τ = min(ε_t, πε/C, v₀ min(1, ε/(9λR))/C)`; its probability is at most
  `(4C_w/√c + 2b + C_T)/W² + r²C_f²/(θ²W) + η` (`θ = ε/(3λ)`, `λ = γ⁻¹`).
  - Regularity: `collarRegEvent`, `collarFresh_of_event` (`freshRegular_of_chi`,
    `norm_certificateChi_collarFW`, `normBound_collarFW`, `Palm.certificate_full_uniform`);
    `layerLaw_compl_collarRegEvent_le` (`layerLaw_collarTopBlock_inv_bad_le`,
    `layerLaw_frobenius_bad_le`) with `layerLaw_trace_bad_le`.
  - Density scale: `|ρ(e) - ρ_F| ≤ |m_{F,c}(0) - ā|/π ≤ Cτ/π ≤ ε` (`collarGood_of_bounds`,
    `semicircleDensity_eq_im`).
  - Frame covariance: `Ṽ^*Γ_FṼ = λΨΨ^*`, `Ψ = -J^*L(1 + E)`, `‖E‖ ≤ |m - ā|/v₀`
    (`collarVt_gamma_eq`, `inv_sub_eq_mul`, `collarCov_entry_le`) and `λγ = 1`
    (`collarLambda_mul_gamma`); then `CommonPortMeanContract.mean`, `.fluctuation` (`p = 2`,
    Chebyshev: `layerLaw_entry_bad_le`) and `.moments` (`p = 4`, Markov:
    `layerLaw_commonPortL_sq_bad_le`).
* **`matrixClosing_of_relativeVectors (hRMV : RelativeMixedVectorsStatement) (hP hPD hCM hTM
  source) : MatrixClosingStatement`**, from `matrixClosing_of_goodEvent`,
  `Mean.collarMeanClause_of_inputs` and `BoundaryMean.exactBoundaryMean_of_inputs`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {W r : ℕ}

/-- **The pointwise good event from the regular event and the two `L`-cutoffs.** -/
theorem collarGood_of_reg {b e c V εt r₀ s₀ v₀ Cc ε τ R : ℝ} (hcdef : c = 1 - 2 * b)
    (hb : b < 1 / 2) (he : |e| < 2) (hW2 : (2 : ℝ) ≤ W)
    (H : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ μ : ℂ,
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖BlockBand.Palm.certificateChi F c 0 μ‖ ≤ εt →
          FreshRegular F c 0 r₀ s₀ v₀ ∧
            ‖freshDyson F c ((0 : ℝ) : ℂ) - μ‖ ≤ Cc * ‖BlockBand.Palm.certificateChi F c 0 μ‖)
    (hVμ : V ≤ (star (matchedA e)).im) (hK : FreshConstants c r₀ s₀ v₀) (hτ : τ ≤ εt)
    (hCc : 0 < Cc) (hτε : Cc * τ ≤ Real.pi * ε)
    (hcov : collarLambda W b e * ((2 * (Cc * τ / v₀) + (Cc * τ / v₀) ^ 2) * R) ≤ ε / 3)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1) {ω₁ : LayerSample W .common}
    (hreg : ω₁ ∈ collarRegEvent W b e τ X) (hL : ‖commonPortL b e X ω₁‖ ^ 2 ≤ R)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hf : ∀ i j : Fin r, collarLambda W b e *
      ‖star (fun x => J x i) ⬝ᵥ ((commonPortLL b e X ω₁ - M) *ᵥ fun x => J x j)‖ ≤ ε / 3)
    (hM : collarLambda W b e * ‖M - ((commonPortGamma b : ℝ) : ℂ) •
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ ε / 3) :
    CollarGood b e X J 7 r₀ s₀ v₀ ε ω₁ := by
  have hW : 0 < W := by
    have : (0 : ℝ) < W := by linarith
    exact_mod_cast this
  obtain ⟨hA, hD, hDinv, hB, hχ⟩ := hreg
  obtain ⟨hFC, hm⟩ := collarFresh_of_event hcdef hb he hW2 H hVμ hX hA hD hDinv hB (hχ.trans hτ)
  subst hcdef
  have hk : ‖freshDyson (collarF e X ω₁) (1 - 2 * b) ((0 : ℝ) : ℂ) - star (matchedA e)‖ ≤
      Cc * τ := hm.trans (mul_le_mul_of_nonneg_left hχ hCc.le)
  exact collarGood_of_bounds hb he hW hX hJ hA hD hFC hK.2.2.2.1 hK.2.2.1 hK.2.2.2.2.2 hk hτε hL
    hcov M hf hM

theorem sum_sum_ofReal_const (r : ℕ) {a : ℝ} :
    ∑ _i : Fin r, ∑ _j : Fin r, ENNReal.ofReal a = ENNReal.ofReal ((r : ℝ) * ((r : ℝ) * a)) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast]

/-- The scalar budget of the covariance step. -/
theorem cov_budget {Λ ε R t₀ k : ℝ} (hΛ : 0 < Λ) (hR : 0 < R) (hk0 : 0 ≤ k) (hkt : k ≤ t₀)
    (ht1 : t₀ ≤ 1) (ht2 : t₀ ≤ ε / (9 * Λ * R)) : Λ * ((2 * k + k ^ 2) * R) ≤ ε / 3 := by
  have h3 : 2 * k + k ^ 2 ≤ 3 * t₀ := by nlinarith only [hk0, hkt, ht1]
  have h5 : t₀ * (9 * Λ * R) ≤ ε := by rwa [le_div_iff₀ (by positivity)] at ht2
  have h6 : Λ * ((2 * k + k ^ 2) * R) ≤ Λ * ((3 * t₀) * R) := by gcongr
  nlinarith only [h5, h6]

/-- **The probability of the bad set at one width**, from the three exceptional events. -/
theorem layerLaw_notCollarGood_le {b e c V εt r₀ s₀ v₀ Cc ε τ R θ a₁ a₃ η : ℝ}
    (hcdef : c = 1 - 2 * b) (hb : b < 1 / 2) (he : |e| < 2) (hW2 : (2 : ℝ) ≤ W)
    (H : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ μ : ℂ,
        V ≤ μ.im → ‖μ‖ ≤ 1 → ‖BlockBand.Palm.certificateChi F c 0 μ‖ ≤ εt →
          FreshRegular F c 0 r₀ s₀ v₀ ∧
            ‖freshDyson F c ((0 : ℝ) : ℂ) - μ‖ ≤ Cc * ‖BlockBand.Palm.certificateChi F c 0 μ‖)
    (hVμ : V ≤ (star (matchedA e)).im) (hK : FreshConstants c r₀ s₀ v₀) (hτ : τ ≤ εt)
    (hCc : 0 < Cc) (hτε : Cc * τ ≤ Real.pi * ε)
    (hcov : collarLambda W b e * ((2 * (Cc * τ / v₀) + (Cc * τ / v₀) ^ 2) * R) ≤ ε / 3)
    (hθε : collarLambda W b e * θ ≤ ε / 3)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    {J : Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hJ : Jᴴ * J = 1)
    (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (hM : collarLambda W b e * ‖M - ((commonPortGamma b : ℝ) : ℂ) •
      (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)‖ ≤ ε / 3)
    (ha₁ : 0 ≤ a₁) (ha₃ : 0 ≤ a₃) (hη : 0 ≤ η)
    (h1 : layerLaw W b .common (collarRegEvent W b e τ X)ᶜ ≤ ENNReal.ofReal a₁)
    (h2 : layerLaw W b .common {ω | R < ‖commonPortL b e X ω‖ ^ 2} ≤ ENNReal.ofReal η)
    (h3 : ∀ i j : Fin r, layerLaw W b .common
      {ω | θ < ‖star (fun x => J x i) ⬝ᵥ ((commonPortLL b e X ω - M) *ᵥ fun x => J x j)‖} ≤
        ENNReal.ofReal a₃) :
    layerLaw W b .common {ω₁ | ¬ CollarGood b e X J 7 r₀ s₀ v₀ ε ω₁} ≤
      ENNReal.ofReal (a₁ + (r : ℝ) * ((r : ℝ) * a₃) + η) := by
  set μ := layerLaw W b .common
  set Bf : Fin r → Fin r → Set (LayerSample W .common) := fun i j =>
    {ω | θ < ‖star (fun x => J x i) ⬝ᵥ ((commonPortLL b e X ω - M) *ᵥ fun x => J x j)‖}
    with hBf
  have hsub : {ω₁ | ¬ CollarGood b e X J 7 r₀ s₀ v₀ ε ω₁} ⊆
      (collarRegEvent W b e τ X)ᶜ ∪ {ω | R < ‖commonPortL b e X ω‖ ^ 2} ∪ ⋃ i, ⋃ j, Bf i j := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hc'
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, not_or, not_not, not_exists,
      Set.mem_ofPred_eq, not_lt, hBf] at hc'
    obtain ⟨⟨hreg, hL⟩, hfij⟩ := hc'
    have hl0 := collarLambda_nonneg W (e := e) hb
    refine hω (collarGood_of_reg hcdef hb he hW2 H hVμ hK hτ hCc hτε hcov hX hJ hreg hL M
      (fun i j => (mul_le_mul_of_nonneg_left (hfij i j) hl0).trans hθε) hM)
  have hm3 : μ (⋃ i, ⋃ j, Bf i j) ≤ ENNReal.ofReal ((r : ℝ) * ((r : ℝ) * a₃)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => measure_iUnion_fintype_le _ _).trans ?_
    rw [← sum_sum_ofReal_const r]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h3 i j
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) hm3).trans
    (le_of_eq ?_)
  rw [← ENNReal.ofReal_add ha₁ hη, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- **`CollarGoodEventAt r`** (the frame covariance, the density scale and the regularity of `F`),
from `CommonPortMeanContract`, `TraceMatrixContract` and `PSSS.SourceContract`. -/
theorem collarGoodEvent_holds (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (r : ℕ) : CollarGoodEventAt r := by
  intro b hb0 hb κ hκ S
  set κ' := min κ 1 with hκ'def
  have hκ' : 0 < κ' := lt_min hκ one_pos
  have hκ'2 : κ' < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have heS : ∀ N, S.e N ∈ bulkInterval κ' := fun N =>
    ⟨by linarith [(S.e_mem N).1, min_le_left κ 1], by linarith [(S.e_mem N).2, min_le_left κ 1]⟩
  have hc : 0 < 1 - 2 * b := by linarith
  have hc1 : 1 - 2 * b < 1 := by linarith
  have hm4 : 0 < 4 - (2 - κ') ^ 2 := BlockBand.Layers.four_sub_sq_pos hκ' (by linarith)
  set V : ℝ := Real.sqrt (4 - (2 - κ') ^ 2) / 2 with hVdef
  have hV : 0 < V := by have := Real.sqrt_pos.2 hm4; positivity
  obtain ⟨εt, r₀, s₀, v₀, Cc, hεt, hK, hCc, H⟩ := certificate_regular_uniform hc hc1 hV
  refine ⟨7, r₀, s₀, v₀, hK, fun ε hε => ?_⟩
  obtain ⟨δ₀, Cm, Wm, hδ₀, hmean⟩ := hCM.mean b hb0 hb κ' hκ'
  obtain ⟨C4, W4, hC4, hL4⟩ := layerLaw_commonPortL_sq_bad_le hCM hb0 hb hκ'
  obtain ⟨Cf, Wf, hCf, hfl⟩ := layerLaw_entry_bad_le hCM hb0 hb hκ'
  obtain ⟨Cw, hCw, hregb⟩ := layerLaw_compl_collarRegEvent_le source
  have hv₀ : 0 < v₀ := hK.2.2.2.2.2
  set γ := commonPortGamma b with hγdef
  have hγ : 0 < γ := div_pos (by linarith) hc
  set Λ := γ⁻¹ with hΛdef
  have hΛ : 0 < Λ := inv_pos.2 hγ
  have he2 : ∀ N, |S.e N| < 2 := fun N =>
    BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ' (heS N)
  have hlamN : ∀ N, collarLambda (S.W N) b (S.e N) = Λ := fun N =>
    eq_inv_of_mul_eq_one_left (collarLambda_mul_gamma (S.W_pos N) hb (he2 N))
  have hVμ : ∀ N, V ≤ (star (matchedA (S.e N))).im := fun N => by
    have := BlockBand.Layers.matchedA_im_le_of_mem_bulkInterval (heS N)
    rw [Complex.star_def, Complex.conj_im]; linarith
  set Cm' := max Cm 0 with hCm'def
  have hCm' : 0 ≤ Cm' := le_max_right _ _
  have hWt : Tendsto (fun N => (S.W N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp S.tendsto_W
  refine tendsto_zero_of_slack fun η hη => ?_
  set R : ℝ := C4 ^ 4 / η + 1 with hRdef
  have hR0 : 0 ≤ C4 ^ 4 / η := by positivity
  have hR1 : 1 ≤ R := by linarith
  have hR : 0 < R := by linarith
  set t₀ : ℝ := min 1 (ε / (9 * Λ * R)) with ht₀def
  have ht₀ : 0 < t₀ := lt_min one_pos (by positivity)
  set τ : ℝ := min εt (min (Real.pi * ε / Cc) (v₀ * t₀ / Cc)) with hτdef
  have hτ : 0 < τ := lt_min hεt (lt_min (by positivity) (by positivity))
  obtain ⟨dT, CT, WT, hdT, hCT, htr⟩ :=
    Collar.Density.layerLaw_trace_bad_le hTM source hb0 hb hκ' hκ'2 hτ
  set θ : ℝ := ε / (3 * Λ) with hθdef
  have hθ : 0 < θ := by positivity
  set Cbad : ℝ := 4 * Cw / Real.sqrt (1 - 2 * b) + 2 * b + CT with hCbad
  have hCbad0 : 0 ≤ Cbad := by
    have : 0 ≤ 4 * Cw / Real.sqrt (1 - 2 * b) := by positivity
    linarith
  -- scalar budgets (independent of `N`)
  have hτε : Cc * τ ≤ Real.pi * ε := by
    have : τ ≤ Real.pi * ε / Cc := (min_le_right _ _).trans (min_le_left _ _)
    rwa [le_div_iff₀ hCc, mul_comm] at this
  have hcov : Λ * ((2 * (Cc * τ / v₀) + (Cc * τ / v₀) ^ 2) * R) ≤ ε / 3 := by
    have hkv : Cc * τ / v₀ ≤ t₀ := by
      have : τ ≤ v₀ * t₀ / Cc := (min_le_right _ _).trans (min_le_right _ _)
      rw [div_le_iff₀ hv₀]
      rw [le_div_iff₀ hCc] at this
      linarith
    exact cov_budget hΛ hR (by positivity) hkv (min_le_left _ _) (min_le_right _ _)
  have hθε : Λ * θ ≤ ε / 3 := le_of_eq (by rw [hθdef]; field_simp)
  have hCη : C4 ^ 4 / R ^ 2 ≤ η := by
    have hR2 : R ≤ R ^ 2 := by nlinarith only [hR1]
    rw [div_le_iff₀ (by positivity)]
    have h1 : C4 ^ 4 ≤ η * R := by
      have := (div_le_iff₀ hη).1 (show C4 ^ 4 / η ≤ R by linarith)
      linarith
    nlinarith only [h1, hR2, hη]
  refine ⟨fun N => Cbad / (S.W N : ℝ) ^ 2 + (r : ℝ) * ((r : ℝ) * (Cf ^ 2 / (θ ^ 2 * S.W N))),
    ?_, ?_⟩
  · have h1 : Tendsto (fun N => Cbad / (S.W N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hWt)
    have h2 : Tendsto (fun N => Cf ^ 2 / (θ ^ 2 * S.W N)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (hWt.const_mul_atTop (by positivity))
    have h3 := (h2.const_mul (r : ℝ)).const_mul (r : ℝ)
    simp only [mul_zero] at h3
    simpa using h1.add h3
  -- eventual conditions
  have hev1 := S.tendsto_W.eventually_ge_atTop (max (max Wm W4) (max (max Wf WT) 2))
  have hev2 : ∀ᶠ N in atTop, matchedDistance b (S.e N) (S.X N) ≤ min δ₀ dT :=
    S.tendsto_d.eventually (Iic_mem_nhds (lt_min hδ₀ hdT))
  have hev3 : ∀ᶠ N in atTop, Λ * (Cm' * (matchedDistance b (S.e N) (S.X N) +
      1 / (S.W N : ℝ) ^ 2)) ≤ ε / 3 := by
    have h1 : Tendsto (fun N => 1 / (S.W N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hWt)
    have h2 := ((S.tendsto_d.add h1).const_mul Cm').const_mul Λ
    simp only [add_zero, mul_zero] at h2
    exact h2.eventually (Iic_mem_nhds (by positivity))
  filter_upwards [hev1, hev2, hev3] with N hWN hdN hmN
  have hW : 0 < S.W N := S.W_pos N
  have hWm : Wm ≤ S.W N := (le_max_left _ _).trans ((le_max_left _ _).trans hWN)
  have hW4 : W4 ≤ S.W N := (le_max_right _ _).trans ((le_max_left _ _).trans hWN)
  have hWf : Wf ≤ S.W N :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hWN))
  have hWT : WT ≤ S.W N :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hWN))
  have hW2 : (2 : ℝ) ≤ S.W N := by
    have : 2 ≤ S.W N := (le_max_right _ _).trans ((le_max_right _ _).trans hWN)
    exact_mod_cast this
  have hX := S.X_herm N
  have hMb := (hmean (S.W N) hW hWm (S.X N) hX (S.e N) (heS N) (hdN.trans (min_le_left _ _))).2
  have hM : collarLambda (S.W N) b (S.e N) * ‖matrixExpect (layerLaw (S.W N) b .common)
      (commonPortLL b (S.e N) (S.X N)) - ((commonPortGamma b : ℝ) : ℂ) • 1‖ ≤ ε / 3 := by
    rw [hlamN N]
    refine (mul_le_mul_of_nonneg_left (hMb.trans ?_) hΛ.le).trans hmN
    have hd0 : 0 ≤ matchedDistance b (S.e N) (S.X N) + 1 / (S.W N : ℝ) ^ 2 := by
      have : 0 ≤ matchedDistance b (S.e N) (S.X N) := le_max_of_le_left (norm_nonneg _)
      positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hd0
  refine layerLaw_notCollarGood_le rfl hb (he2 N) hW2 H (hVμ N) hK (min_le_left _ _) hCc hτε
    (by rw [hlamN N]; exact hcov) (by rw [hlamN N]; exact hθε) hX (S.J_frame N) _ hM
    (by positivity) (by positivity) hη.le
    (hregb (S.W N) hW b hb0 hb (S.e N) (S.X N) hX τ CT hCT
      (htr (S.W N) hW hWT (S.X N) hX (S.e N) (heS N) (hdN.trans (min_le_right _ _))))
    ((hL4 (S.W N) hW hW4 (S.X N) hX (S.e N) (heS N) R hR).trans (ENNReal.ofReal_le_ofReal hCη))
    (fun i j => hfl (S.W N) hW hWf (S.X N) hX (S.e N) (heS N) _ _
      (l2Norm_frame_col (S.J_frame N) i) (l2Norm_frame_col (S.J_frame N) j) θ hθ)

/-- **Hypothesis 1 at every positive rank** (`CollarPolesAt r`), from
`RelativeMixedVectorsStatement`, `CommonPortMeanContract`, `TraceMatrixContract` and
`PSSS.SourceContract`.
-/
theorem collarPolesAt_of_relativeVectors (hRMV : RelativeMixedVectorsStatement)
    (hCM : CommonPortMeanContract) (hTM : TraceMatrixContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {r : ℕ} (hr : 0 < r) :
    CollarPolesAt r :=
  collarPolesAt_of_goodEvent hRMV hr (collarGoodEvent_holds hCM hTM source r)

/-- **`MatrixClosingStatement` from `RelativeMixedVectorsStatement`**, `FreshPalmContract`,
`PointDensityContract`, `CommonPortMeanContract`, `TraceMatrixContract` and `PSSS.SourceContract`.
-/
theorem matrixClosing_of_relativeVectors (hRMV : RelativeMixedVectorsStatement)
    (hP : FreshPalmContract) (hPD : PointDensityContract) (hCM : CommonPortMeanContract)
    (hTM : TraceMatrixContract) (source : BlockBand.External.PSSS.SourceContract.{0}) :
    MatrixClosingStatement :=
  matrixClosing_of_goodEvent hRMV (fun r _ => collarGoodEvent_holds hCM hTM source r)
    (Mean.collarMeanClause_of_inputs hP hPD hCM hTM source)
    (BlockBand.Critical.BoundaryMean.exactBoundaryMean_of_inputs hP hPD hCM hTM source)

end BlockBand.Critical.MatrixClosing.Poles
