module

public import BlockBand.Endpoints.Poisson.SingleCollarDilation

/-!
# Single-collar log error: the conditional unitary comparison

We prove the conditional unitary comparison and the scalar bookkeeping of the single-collar
log-error bound.

* `scLift`: the unitary dilation `𝒱(S)` of a matrix `S` on `F ⊕ β` reindexed to `F ⊕ β'`
  (`β' = β ⊕ (F ⊕ β)`), the index shape of `unitary_log_comparison`; `sc_lift_unitary`,
  `sc_lift_toBlocks11` (the collar block is that of `S`), `sc_schattenFrac_lift_sub`
  (`σ` is unchanged), `sc_det_one_sub_collarHat` (`det(I - ÛV) = det(I - U V₁₁)`).
* `sc_conditional_comparison`: Fubini over the fresh collar, independent of the old network:
  a bound on `E_U |log|det(I - ÛV₁)| - log|det(I - ÛV₀)||` for each deterministic old
  configuration in a good set `G` (the conclusion of `unitary_log_comparison`) integrates to
  the bound on `E[1_G |…|]`.
* `sc_good_bad_split`: on the good event the comparison bound `C_p E[(1 + g₀ + σ)σ]` and
  Cauchy–Schwarz with `E g₀² ≤ C`, and off it Hölder with an `L^r` log moment:
  `E|D| ≤ C_p (A + √(C_g A)) + M P(Gᶜ)^{1-1/r}`.
* `sc_collar_comparison`: the unitary log-comparison lemma applied to the dilated scattering
  matrices.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Endpoints.PhaseFractional (schattenFrac)
open scoped ENNReal ComplexOrder

/-!
## 1. The dilation in the index shape of `unitary_log_comparison`
-/

section Lift

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `𝒱(S)` reindexed from `(α ⊕ β) ⊕ (α ⊕ β)` to `α ⊕ (β ⊕ (α ⊕ β))`. -/
def scLift (S : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    Matrix (α ⊕ (β ⊕ (α ⊕ β))) (α ⊕ (β ⊕ (α ⊕ β))) ℂ :=
  reindex (Equiv.sumAssoc α β (α ⊕ β)) (Equiv.sumAssoc α β (α ⊕ β)) (scDilation S)

theorem sc_reindex_conjTranspose_mul {γ δ : Type*} [Fintype γ] [DecidableEq γ] [Fintype δ]
    [DecidableEq δ] (e : γ ≃ δ) (M N : Matrix γ γ ℂ) :
    (reindex e e M)ᴴ * reindex e e N = reindex e e (Mᴴ * N) := by
  simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]

theorem sc_lift_unitary {S : Matrix (α ⊕ β) (α ⊕ β) ℂ} (h : (1 - Sᴴ * S).PosSemidef) :
    (scLift S)ᴴ * scLift S = 1 := by
  rw [scLift, sc_reindex_conjTranspose_mul, sc_dilation_unitary h, reindex_apply,
    submatrix_one_equiv]

theorem sc_lift_toBlocks11 (S : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (scLift S).toBlocks₁₁ = S.toBlocks₁₁ := by
  ext i j
  simp [scLift, scDilation, toBlocks₁₁, reindex_apply]

theorem sc_schattenFrac_lift_sub (S₁ S₀ : Matrix (α ⊕ β) (α ⊕ β) ℂ) (p : ℝ) :
    schattenFrac p (scLift S₁ - scLift S₀) = schattenFrac p (scDilation S₁ - scDilation S₀) := by
  have hsub : reindex (Equiv.sumAssoc α β (α ⊕ β)) (Equiv.sumAssoc α β (α ⊕ β)) (scDilation S₁) -
      reindex (Equiv.sumAssoc α β (α ⊕ β)) (Equiv.sumAssoc α β (α ⊕ β)) (scDilation S₀) =
      reindex (Equiv.sumAssoc α β (α ⊕ β)) (Equiv.sumAssoc α β (α ⊕ β))
        (scDilation S₁ - scDilation S₀) := by
    ext i j; simp [reindex_apply]
  unfold schattenFrac scLift
  rw [hsub, sc_reindex_conjTranspose_mul, fracTrace_reindex]

omit [Fintype β] [DecidableEq β] in
/-- `det(I - Û V) = det(I - U V₁₁)` for `Û = U ⊕ 0`. -/
theorem sc_det_one_sub_collarHat [Fintype β] [DecidableEq β] (U : Matrix α α ℂ)
    (V : Matrix (α ⊕ β) (α ⊕ β) ℂ) :
    (1 - fromBlocks U 0 0 0 * V).det = (1 - U * V.toBlocks₁₁).det := by
  conv_lhs => rw [← fromBlocks_toBlocks V]
  rw [fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp only [Matrix.zero_mul, add_zero, neg_zero]
  rw [det_fromBlocks_zero₂₁, ← sub_eq_add_neg, det_one, mul_one]

end Lift

/-!
## 2. Fubini over the independent fresh collar
-/

/-- **Conditional comparison.** Let the fresh collar `Uc` (law `ν`) be independent of the old
configuration `O`, and let `V₀, V₁` be measurable functions of the old configuration. If for
every old configuration `o` in a measurable good set `G` the collar expectation
`E_U |log|det(I - Φ̂(U)V₁(o))| - log|det(I - Φ̂(U)V₀(o))||` is at most `B(o)`, then
`E[1_{O ∈ G} |…|] ≤ E B(O)`. -/
theorem sc_conditional_comparison {Ω Ω' C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] {μ : Measure Ω} [IsProbabilityMeasure μ] {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {Uc : Ω → C} {O : Ω → Ω'} (hU : Measurable Uc)
    (hO : Measurable O) (hind : IndepFun Uc O μ) {ν : Measure C} (hlaw : μ.map Uc = ν)
    {Φ : C → Matrix α α ℂ} (hΦ : Measurable Φ) {V₀ V₁ : Ω' → Matrix (α ⊕ β) (α ⊕ β) ℂ}
    (hV₀ : Measurable V₀) (hV₁ : Measurable V₁) {G : Set Ω'} (hG : MeasurableSet G)
    {B : Ω' → ℝ} (hB : Measurable B)
    (hcomp : ∀ o ∈ G, ∫⁻ u, ENNReal.ofReal
        |Real.log ‖(1 - fromBlocks (Φ u) 0 0 0 * V₁ o).det‖ -
          Real.log ‖(1 - fromBlocks (Φ u) 0 0 0 * V₀ o).det‖| ∂ν ≤ ENNReal.ofReal (B o)) :
    ∫⁻ ω in O ⁻¹' G, ENNReal.ofReal
        |Real.log ‖(1 - fromBlocks (Φ (Uc ω)) 0 0 0 * V₁ (O ω)).det‖ -
          Real.log ‖(1 - fromBlocks (Φ (Uc ω)) 0 0 0 * V₀ (O ω)).det‖| ∂μ ≤
      ∫⁻ ω, ENNReal.ofReal (B (O ω)) ∂μ := by
  have hL : ∀ V : Ω' → Matrix (α ⊕ β) (α ⊕ β) ℂ, Measurable V →
      Measurable (fun q : C × Ω' => Real.log ‖(1 - fromBlocks (Φ q.1) 0 0 0 * V q.2).det‖) := by
    intro V hV
    refine Real.measurable_log.comp (measurable_norm.comp
      ((continuous_id.matrix_det).measurable.comp (PhaseFractional.measurable_matrix_sub measurable_const ?_)))
    exact PhaseFractional.measurable_matrix_mul
      (PhaseFractional.measurable_collarHat (β := β) (hΦ.comp measurable_fst))
      (hV.comp measurable_snd)
  set F : C × Ω' → ℝ≥0∞ := fun q => G.indicator (fun o => ENNReal.ofReal
      |Real.log ‖(1 - fromBlocks (Φ q.1) 0 0 0 * V₁ o).det‖ -
        Real.log ‖(1 - fromBlocks (Φ q.1) 0 0 0 * V₀ o).det‖|) q.2 with hF
  have hFm : Measurable F := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp ((hL V₁ hV₁).sub (hL V₀ hV₀)).abs)
      (hG.preimage measurable_snd)
  have hpair : Measurable fun ω => (Uc ω, O ω) := hU.prodMk hO
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hO.aemeasurable).1 hind
  have hνf : IsFiniteMeasure ν := by rw [← hlaw]; infer_instance
  calc ∫⁻ ω in O ⁻¹' G, _ ∂μ = ∫⁻ ω, F (Uc ω, O ω) ∂μ := by
        rw [← lintegral_indicator (hG.preimage hO)]
        rfl
    _ = ∫⁻ q, F q ∂(ν.prod (μ.map O)) := by
        rw [← lintegral_map hFm hpair, hprod, hlaw]
    _ = ∫⁻ o, ∫⁻ u, F (u, o) ∂ν ∂(μ.map O) := lintegral_prod_symm _ hFm.aemeasurable
    _ ≤ ∫⁻ o, ENNReal.ofReal (B o) ∂(μ.map O) := by
        refine lintegral_mono fun o => ?_
        by_cases ho : o ∈ G
        · simp only [hF, Set.indicator_of_mem ho]; exact hcomp o ho
        · simp [hF, Set.indicator_of_notMem ho]
    _ = ∫⁻ ω, ENNReal.ofReal (B (O ω)) ∂μ :=
        lintegral_map (ENNReal.measurable_ofReal.comp hB) hO

/-!
## 3. The bookkeeping of the good and bad events
-/

/-- **Good and bad events**. On a probability space let `D` be the log
difference, `g, σ ≥ 0`, `G` a measurable good event with
* `E[1_G |D|] ≤ C_p E[(1 + g + σ)σ]` (the conditional unitary log comparison),
* `E g² ≤ C_g` (the defect moment), `E(σ + σ²) ≤ A` (fractional moments of the dilation),
* `‖D‖_{L^r} ≤ M` for some `r > 1` (the log moments of the exceptional-set removal),
* `P(Gᶜ) ≤ ε₀`.
Then `E|D| ≤ C_p (A + √C_g √A) + M ε₀^{1-1/r}`. -/
theorem sc_good_bad_split {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {D g σ : Ω → ℝ} (hD : AEStronglyMeasurable D μ)
    (hg : AEMeasurable g μ) (hσ : AEMeasurable σ μ) (hg0 : ∀ ω, 0 ≤ g ω) (hσ0 : ∀ ω, 0 ≤ σ ω)
    {G : Set Ω}
    (hG : MeasurableSet G) {Cp Cg A M ε₀ r : ℝ} (hCg : 0 ≤ Cg) (hA : 0 ≤ A) (hr : 1 < r)
    (hgood : ∫⁻ ω in G, ENNReal.ofReal |D ω| ∂μ ≤
      ENNReal.ofReal Cp * ∫⁻ ω, ENNReal.ofReal ((1 + g ω + σ ω) * σ ω) ∂μ)
    (hg2 : ∫⁻ ω, ENNReal.ofReal (g ω ^ 2) ∂μ ≤ ENNReal.ofReal Cg)
    (hσ2 : ∫⁻ ω, ENNReal.ofReal (σ ω + σ ω ^ 2) ∂μ ≤ ENNReal.ofReal A)
    (hDr : eLpNorm D (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M)
    (hbad : μ Gᶜ ≤ ENNReal.ofReal ε₀) :
    ∫⁻ ω, ENNReal.ofReal |D ω| ∂μ ≤
      ENNReal.ofReal Cp * (ENNReal.ofReal A + ENNReal.ofReal (Real.sqrt Cg * Real.sqrt A)) +
        ENNReal.ofReal M * ENNReal.ofReal ε₀ ^ (1 - 1 / r) := by
  rw [← lintegral_add_compl _ hG]
  have hE : ∫⁻ ω, ENNReal.ofReal ((1 + g ω + σ ω) * σ ω) ∂μ ≤
      ENNReal.ofReal A + ENNReal.ofReal (Real.sqrt Cg * Real.sqrt A) := by
    -- the good event: `E[(1+g+σ)σ] ≤ E(σ+σ²) + (E g²)^{1/2} (E σ²)^{1/2}`
    have hsplit : ∀ ω, ENNReal.ofReal ((1 + g ω + σ ω) * σ ω) =
        ENNReal.ofReal (σ ω + σ ω ^ 2) + ENNReal.ofReal (g ω) * ENNReal.ofReal (σ ω) := by
      intro ω
      rw [← ENNReal.ofReal_mul (hg0 ω), ← ENNReal.ofReal_add (by nlinarith [hσ0 ω])
        (mul_nonneg (hg0 ω) (hσ0 ω))]
      congr 1; ring
    simp_rw [hsplit]
    rw [lintegral_add_left' (f := fun ω => ENNReal.ofReal (σ ω + σ ω ^ 2))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hσ.add (hσ.pow_const 2)))]
    refine add_le_add hσ2 ?_
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (ENNReal.measurable_ofReal.comp_aemeasurable hg)
      (ENNReal.measurable_ofReal.comp_aemeasurable hσ)
    have hpow : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
      intro x hx
      rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.rpow_two]
    have h1 : ∫⁻ ω, ENNReal.ofReal (g ω) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal Cg := by
      simp_rw [Function.comp_apply] at hH
      refine le_of_eq_of_le (lintegral_congr fun ω => hpow _ (hg0 ω)) hg2
    have h2 : ∫⁻ ω, ENNReal.ofReal (σ ω) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal A := by
      refine le_of_eq_of_le (lintegral_congr fun ω => hpow _ (hσ0 ω)) (le_trans ?_ hσ2)
      exact lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (by linarith [hσ0 ω])
    have hsq : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ^ (1 / (2 : ℝ)) = ENNReal.ofReal (Real.sqrt x) := by
      intro x hx
      rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), Real.sqrt_eq_rpow]
    calc ∫⁻ ω, ENNReal.ofReal (g ω) * ENNReal.ofReal (σ ω) ∂μ
        ≤ (∫⁻ ω, ENNReal.ofReal (g ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫⁻ ω, ENNReal.ofReal (σ ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hH
      _ ≤ ENNReal.ofReal Cg ^ (1 / (2 : ℝ)) * ENNReal.ofReal A ^ (1 / (2 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal (Real.sqrt Cg * Real.sqrt A) := by
          rw [hsq _ hCg, hsq _ hA, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have hB : ∫⁻ ω in Gᶜ, ENNReal.ofReal |D ω| ∂μ ≤
      ENNReal.ofReal M * ENNReal.ofReal ε₀ ^ (1 - 1 / r) := by
    -- the bad event: Hölder with the `L^r` moment
    have hr0 : (0 : ℝ) ≤ 1 - 1 / r := by
      rw [sub_nonneg]; exact (div_le_one (by linarith)).2 hr.le
    have h1 : ∫⁻ ω in Gᶜ, ENNReal.ofReal |D ω| ∂μ = eLpNorm D 1 (μ.restrict Gᶜ) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      · simp_rw [Real.enorm_eq_ofReal_abs]
      · exact hD.restrict
    have h1r : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict Gᶜ) h1r hD.restrict
    rw [Measure.restrict_apply_univ, ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith),
      div_one] at h2
    rw [h1]
    refine h2.trans (mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hDr)
      (ENNReal.rpow_le_rpow hbad hr0))
  exact add_le_add (hgood.trans (by gcongr)) hB

/-!
## 4. The unitary log-comparison lemma for the dilated scattering matrices
-/

open BlockBand.Internal.Contracts.Critical (CollarKernelContract collarLaw collarScattering
  conductance)
open BlockBand.Internal.Contracts.Layers (bulkInterval)
open BlockBand.Endpoints.PhaseFractional (scatteringDistance unitary_log_comparison)

/-- **`unitary_log_comparison` applied to `V₀ = 𝒱(S₀)`, `V₁ = 𝒱(S_κ)`.** For a unitary `S₀` and a contraction `S₁` on
`(Fin 2 × Fin W) ⊕ β` (the complete scattering matrices of the old network without and with the absorber; the
collar block is the compressed response `r`), with the certificate `d(r₀) ≤ d₂` and
`σ = Tr |𝒱(S₁) - 𝒱(S₀)|^p ≤ c_* W`, over the fresh collar `U ~ collarLaw W b` (matched lead parameter,
`s = ν = 0`): `E_U |log|det(I - U r₁)| - log|det(I - U r₀)|| ≤ C_p (1 + g₀ + σ) σ`, `g₀ = Tr(I - r₀*r₀)`. Only
`CollarKernelContract` is used, through `unitary_log_comparison`. -/
theorem sc_collar_comparison (hK : CollarKernelContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κI : ℝ} (hκI : 0 < κI) :
    ∃ (d₂ cstar : ℝ) (W₀ : ℕ), 0 < d₂ ∧ 0 < cstar ∧ ∀ p : ℝ, 0 < p → p < 1 → ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κI, ∀ (β : Type) [Fintype β]
        [DecidableEq β] (S₀ S₁ : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ),
        S₀ᴴ * S₀ = 1 → (1 - S₁ᴴ * S₁).PosSemidef →
        scatteringDistance b e S₀.toBlocks₁₁ ≤ d₂ →
        schattenFrac p (scDilation S₁ - scDilation S₀) ≤ cstar * W →
        ∫⁻ u, ENNReal.ofReal
            |Real.log ‖(1 - collarScattering b e 0 0 u * S₁.toBlocks₁₁).det‖ -
              Real.log ‖(1 - collarScattering b e 0 0 u * S₀.toBlocks₁₁).det‖| ∂collarLaw W b ≤
          ENNReal.ofReal (Cp * (1 + conductance S₀.toBlocks₁₁ +
            schattenFrac p (scDilation S₁ - scDilation S₀)) *
              schattenFrac p (scDilation S₁ - scDilation S₀)) := by
  obtain ⟨d₂, cstar, s₀, ν₀, τ, W₀, hd₂, hc, hs₀, hν₀, -, -, hUL⟩ :=
    unitary_log_comparison.{0} hK hb0 hb1 hκI
  refine ⟨d₂, cstar, W₀, hd₂, hc, fun p hp0 hp1 => ?_⟩
  obtain ⟨Cp, hCp, hmain⟩ := hUL p hp0 hp1
  refine ⟨Cp, hCp, fun W hW hW₀ e he β _ _ S₀ S₁ hS₀ hS₁ hd hσ => ?_⟩
  have hS₀' : (1 - S₀ᴴ * S₀).PosSemidef := by rw [hS₀, sub_self]; exact PosSemidef.zero
  have key := (hmain W hW hW₀ e he 0 ⟨by linarith, by linarith⟩ 0 ⟨le_rfl, hν₀.le⟩
    (β ⊕ ((Fin 2 × Fin W) ⊕ β)) (scLift S₀) (scLift S₁) (sc_lift_unitary hS₀')
    (sc_lift_unitary hS₁) (by rwa [sc_lift_toBlocks11])
    (by rwa [sc_schattenFrac_lift_sub])).2
  simp only [sc_det_one_sub_collarHat, sc_lift_toBlocks11, sc_schattenFrac_lift_sub] at key
  exact key

end BlockBand.Endpoints
