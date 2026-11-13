module

public import BlockBand.Endpoints.Poisson.SingleCollarStageLog

/-!
# The single-collar log-error bound at one configuration: the collar log difference

Setting: a probability space `(Ω, μ)`, the fresh collar `Uc` (law `Critical.collarLaw W b`)
independent of the old configuration `O`; complete scattering matrices `S₀` (unitary) and `S₁`
(contraction) of the old network as measurable functions of `O`; a measurable majorant `σ̄` of
`σ = Tr |𝒱(S₁) - 𝒱(S₀)|^p` (in the application, the right side of the unitary dilation of the
source). Hypotheses (moments under `μ`): `E (g₀ ∨ 0)² ≤ C_g`,
`E(σ̄ + σ̄²) ≤ A`, `‖D‖_{L^r} ≤ M` (`r > 1`), `P(d(r₀) > d₂) ≤ ε₁`. Conclusion:
`E|D| ≤ C_p (A + √C_g √A) + M (ε₁ + A/(c_* W))^{1-1/r}` for the collar log difference
`D = log|det(I - U r₁)| - log|det(I - U r₀)|`, `r_i = (S_i)₁₁`.

* `scsSigma`, `scsCollarLogDiff`: `σ` and `D`.
* `scs_collar_log_bound`: the bound above.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace)
open BlockBand.Endpoints.PhaseFractional (schattenFrac scatteringDistance)
open BlockBand.Internal.Contracts.Critical (CollarKernelContract collarScattering
  conductance)
open BlockBand.Internal.Contracts.Layers (bulkInterval)
open scoped ENNReal ComplexOrder

variable {W : ℕ} {β : Type} [Fintype β] [DecidableEq β]

/-- `σ = Tr |𝒱(S₁) - 𝒱(S₀)|^p`, with `𝒱` the unitary dilation. -/
def scsSigma (p : ℝ) (S₀ S₁ : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ) : ℝ :=
  schattenFrac p (scDilation S₁ - scDilation S₀)

/-- `D = log|det(I - U r₁)| - log|det(I - U r₀)|`, `U = collarScattering b e 0 0 u`,
`r_i = (S_i)₁₁`. -/
def scsCollarLogDiff (b e : ℝ) (u : BlockBand.Internal.Contracts.Critical.CollarSample W)
    (S₀ S₁ : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ) : ℝ :=
  Real.log ‖(1 - collarScattering b e 0 0 u * S₁.toBlocks₁₁).det‖ -
    Real.log ‖(1 - collarScattering b e 0 0 u * S₀.toBlocks₁₁).det‖

theorem scs_continuous_conductance {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun r : Matrix ι ι ℂ => conductance r) := by
  unfold conductance
  refine Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag]
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_apply_apply i i).comp ?_
  exact continuous_const.sub (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)

omit [Fintype β] [DecidableEq β] in
theorem scs_measurable_toBlocks11 [Fintype β] [DecidableEq β] :
    Measurable (fun S : Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ => S.toBlocks₁₁) :=
  Measurable.of_eval_matrix _ fun _ _ => by
    simp only [toBlocks₁₁, of_apply]; exact Matrix.measurable_apply

theorem scs_measurable_logDet {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {Φ : γ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hΦ : Measurable Φ) {Uc : α → γ}
    (hU : Measurable Uc) {r : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hr : Measurable r) :
    Measurable (fun ω => Real.log ‖(1 - Φ (Uc ω) * r ω).det‖) :=
  Real.measurable_log.comp (measurable_norm.comp ((continuous_id.matrix_det).measurable.comp
    (measurable_mat_sub measurable_const (measurable_mat_mul (hΦ.comp hU) hr))))

/-- **The collar log-difference bound at one configuration.** From `CollarKernelContract`:
constants `d₂, c_* > 0`, `W₀`, and for each `0 < p < 1` a `C_p`, such that in the setting of the
module docstring `E|D| ≤ C_p (A + √C_g √A) + M (ε₁ + A/(c_* W))^{1-1/r}`.
-/
theorem scs_collar_log_bound (hK : CollarKernelContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    {κI : ℝ} (hκI : 0 < κI) :
    ∃ (d₂ cstar : ℝ) (W₀ : ℕ), 0 < d₂ ∧ 0 < cstar ∧ ∀ p : ℝ, 0 < p → p < 1 → ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ (W : ℕ), 0 < W → W₀ ≤ W → ∀ e ∈ bulkInterval κI,
      ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
        [IsProbabilityMeasure μ] (β : Type) [Fintype β] [DecidableEq β]
        (Uc : Ω → BlockBand.Internal.Contracts.Critical.CollarSample W) (O : Ω → Ω'), Measurable Uc → Measurable O →
        IndepFun Uc O μ → μ.map Uc = BlockBand.Internal.Contracts.Critical.collarLaw W b →
      ∀ (S₀ S₁ : Ω' → Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ) (σb : Ω' → ℝ),
        Measurable S₀ → Measurable S₁ → Measurable σb →
        (∀ o, (S₀ o)ᴴ * S₀ o = 1) → (∀ o, (1 - (S₁ o)ᴴ * S₁ o).PosSemidef) →
        (∀ o, scsSigma p (S₀ o) (S₁ o) ≤ σb o) →
        Measurable (fun o => scatteringDistance b e (S₀ o).toBlocks₁₁) →
      ∀ {Cg A M ε₁ r : ℝ}, 0 ≤ Cg → 0 ≤ A → 0 ≤ ε₁ → 1 < r →
        ∫⁻ ω, ENNReal.ofReal (max 0 (conductance (S₀ (O ω)).toBlocks₁₁) ^ 2) ∂μ ≤
          ENNReal.ofReal Cg →
        ∫⁻ ω, ENNReal.ofReal (σb (O ω) + σb (O ω) ^ 2) ∂μ ≤ ENNReal.ofReal A →
        eLpNorm (fun ω => scsCollarLogDiff b e (Uc ω) (S₀ (O ω)) (S₁ (O ω)))
          (ENNReal.ofReal r) μ ≤ ENNReal.ofReal M →
        μ {ω | d₂ < scatteringDistance b e (S₀ (O ω)).toBlocks₁₁} ≤ ENNReal.ofReal ε₁ →
        ∫⁻ ω, ENNReal.ofReal |scsCollarLogDiff b e (Uc ω) (S₀ (O ω)) (S₁ (O ω))| ∂μ ≤
          ENNReal.ofReal Cp * (ENNReal.ofReal A + ENNReal.ofReal (Real.sqrt Cg * Real.sqrt A)) +
            ENNReal.ofReal M * ENNReal.ofReal (ε₁ + A / (cstar * W)) ^ (1 - 1 / r) := by
  obtain ⟨d₂, cstar, W₀, hd₂, hc, hUL⟩ := sc_collar_comparison hK hb0 hb1 hκI
  refine ⟨d₂, cstar, W₀, hd₂, hc, fun p hp0 hp1 => ?_⟩
  obtain ⟨Cp, hCp, hmain⟩ := hUL p hp0 hp1
  refine ⟨Cp, hCp, ?_⟩
  intro W hW hW₀ e he Ω Ω' _ _ μ _ β _ _ Uc O hU hO hind hlaw S₀ S₁ σb hS₀m hS₁m hσm hS₀ hS₁
    hσle hdm Cg A M ε₁ r hCg hA hε₁ hr hg2 hσ2 hDr hcert
  have hσ0 : ∀ o, 0 ≤ σb o := fun o => (fracTrace_nonneg _ _).trans (hσle o)
  have hcW : 0 < cstar * W := mul_pos hc (by exact_mod_cast hW)
  -- the good set of old configurations
  set G' : Set Ω' := {o | scatteringDistance b e (S₀ o).toBlocks₁₁ ≤ d₂ ∧ σb o ≤ cstar * W}
  have hG'm : MeasurableSet G' :=
    (measurableSet_le hdm measurable_const).inter (measurableSet_le hσm measurable_const)
  have hΦ := PhaseFractional.measurable_collarScattering b e 0 0 W
  have hr11 : ∀ {S : Ω' → Matrix ((Fin 2 × Fin W) ⊕ β) ((Fin 2 × Fin W) ⊕ β) ℂ}, Measurable S →
      Measurable fun ω => (S (O ω)).toBlocks₁₁ := fun hS => (scs_measurable_toBlocks11.comp hS).comp hO
  have hDm : Measurable fun ω => scsCollarLogDiff b e (Uc ω) (S₀ (O ω)) (S₁ (O ω)) :=
    (scs_measurable_logDet hΦ hU (hr11 hS₁m)).sub (scs_measurable_logDet hΦ hU (hr11 hS₀m))
  have hgm : Measurable fun o => max 0 (conductance (S₀ o).toBlocks₁₁) :=
    measurable_const.max (scs_continuous_conductance.measurable.comp
      (scs_measurable_toBlocks11.comp hS₀m))
  -- the good event: conditional comparison over the fresh collar
  set B : Ω' → ℝ := fun o => Cp * ((1 + max 0 (conductance (S₀ o).toBlocks₁₁) + σb o) * σb o)
  have hBm : Measurable B :=
    measurable_const.mul (((measurable_const.add hgm).add hσm).mul hσm)
  have hcomp : ∀ o ∈ G', ∫⁻ u, ENNReal.ofReal
      |Real.log ‖(1 - fromBlocks (collarScattering b e 0 0 u) 0 0 0 * S₁ o).det‖ -
        Real.log ‖(1 - fromBlocks (collarScattering b e 0 0 u) 0 0 0 * S₀ o).det‖|
        ∂BlockBand.Internal.Contracts.Critical.collarLaw W b ≤ ENNReal.ofReal (B o) := by
    intro o ho
    simp_rw [sc_det_one_sub_collarHat]
    have hσc : schattenFrac p (scDilation (S₁ o) - scDilation (S₀ o)) ≤ cstar * W :=
      (hσle o).trans ho.2
    refine (hmain W hW hW₀ e he β (S₀ o) (S₁ o) (hS₀ o) (hS₁ o) ho.1 hσc).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have h1 := hσle o
    have h2 : 0 ≤ schattenFrac p (scDilation (S₁ o) - scDilation (S₀ o)) := fracTrace_nonneg _ _
    have h3 : conductance (S₀ o).toBlocks₁₁ ≤ max 0 (conductance (S₀ o).toBlocks₁₁) :=
      le_max_right _ _
    have h4 : 0 ≤ max 0 (conductance (S₀ o).toBlocks₁₁) := le_max_left _ _
    unfold scsSigma at h1
    simp only [B, ← mul_assoc]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCp) h1 h2
      (mul_nonneg hCp (by linarith))
  have hcc := sc_conditional_comparison hU hO hind hlaw hΦ hS₀m hS₁m hG'm hBm hcomp
  simp_rw [sc_det_one_sub_collarHat] at hcc
  have hgood : ∫⁻ ω in O ⁻¹' G', ENNReal.ofReal
      |scsCollarLogDiff b e (Uc ω) (S₀ (O ω)) (S₁ (O ω))| ∂μ ≤
      ENNReal.ofReal Cp * ∫⁻ ω, ENNReal.ofReal
        ((1 + max 0 (conductance (S₀ (O ω)).toBlocks₁₁) + σb (O ω)) * σb (O ω)) ∂μ := by
    refine hcc.trans (le_of_eq ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    simp only [B]
    rw [ENNReal.ofReal_mul hCp]
  -- the bad event: certificate and Markov on `σ̄`
  have hmark : μ {ω | cstar * W ≤ σb (O ω)} ≤ ENNReal.ofReal (A / (cstar * W)) := by
    have hm := meas_ge_le_lintegral_div (μ := μ)
      (ENNReal.measurable_ofReal.comp (hσm.comp hO)).aemeasurable
      (ε := ENNReal.ofReal (cstar * W)) (by simp [hcW]) ENNReal.ofReal_ne_top
    have hset : {ω | cstar * W ≤ σb (O ω)} =
        {ω | ENNReal.ofReal (cstar * W) ≤ ENNReal.ofReal (σb (O ω))} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      exact (ENNReal.ofReal_le_ofReal_iff (hσ0 _)).symm
    rw [hset]
    refine hm.trans ?_
    rw [ENNReal.ofReal_div_of_pos hcW]
    gcongr
    refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) hσ2
    simp only [Function.comp_apply]; nlinarith [hσ0 (O ω)]
  have hbad : μ (O ⁻¹' G')ᶜ ≤ ENNReal.ofReal (ε₁ + A / (cstar * W)) := by
    have hsub : (O ⁻¹' G')ᶜ ⊆ {ω | d₂ < scatteringDistance b e (S₀ (O ω)).toBlocks₁₁} ∪
        {ω | cstar * W ≤ σb (O ω)} := by
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, G', not_and_or,
        not_le] at hω
      rcases hω with h | h
      · exact Or.inl h
      · exact Or.inr h.le
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [ENNReal.ofReal_add hε₁ (div_nonneg hA hcW.le)]
    exact add_le_add hcert hmark
  exact sc_good_bad_split hDm.aestronglyMeasurable (hgm.comp hO).aemeasurable
    (hσm.comp hO).aemeasurable (fun ω => le_max_left _ _) (fun ω => hσ0 (O ω))
    (hG'm.preimage hO) hCg hA hr hgood hg2 hσ2 hDr hbad

end BlockBand.Endpoints
