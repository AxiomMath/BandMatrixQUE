module

public import BlockBand.Endpoints.Normalization.PalmBridge
public import BlockBand.Coarea.FreshPalmDensity
public import BlockBand.Wegner.ProjectedWegnerGUECount
public import BlockBand.Palm.MomentFlow.LocalScaling
public import BlockBand.External.NativeInputs

/-!
# Upper bound on the unranked Palm mass

We prove that the unranked Palm mass is at most `C_b 𝒩`, for the pair and for one block.

**Measures, domain, constants.** `A⁰ ~ freshTracelessLaw N c₀` (traceless part of
`GUE_N(c₀/N)`), `G ~ gueMeasure (Fin N) (c₀/N)`, Lebesgue `dE`. Every `N ≥ 1`, `c₀ > 0`, every
Hermitian `F` (no norm bound), every real `E`. With `C > 0` the PSSS constant (absolute):
* `palmMass_le`: `palmMass F c₀ E ≤ C/√c₀ · N`;
* pair (`N = 2W`, `c₀ = s = min(b, 1-2b)`): `Z(e) ≤ C_b · 2W`, `C_b = C/√(min(b,1-2b))`, for every
  `p` with `p.b = b`, pair, measurable frame, Hermitian exterior and real `e`;
* block (`N = W`, `c₀ = c = 1-2b`): `Z₀(e) ≤ C/√(1-2b) · W`, every Hermitian `H_R`, every `C`.
`C_b` depends only on `b` (not on `W`, `n`, the exterior, the frame or `e`).

## Proof

1. *Integrated identity* (`lintegral_eigenvalue_test_eq`): for measurable `h ≥ 0`,
   `∫ h(λ_ℓ(F+G)) dGUE_N(c₀/N) = ∫ h(E) E[w_{ℓ,E}] dE` (scalar split + scalar Gaussian kernel;
   `λ_ℓ(F + A⁰ + ζ) = λ_ℓ(F + A⁰) + ζ`). Summed over `ℓ`: `∫ Σ_ℓ h(λ_ℓ) = ∫ h(E) palmMass(E) dE`.
2. *Wegner/PSSS* (`lintegral_count_le`): with `h = 1_{[a,b]}`, the left side is the mean
   eigenvalue count of `F + G` in `[a,b]`, at most `C/√c₀ · N · (b-a)` (PSSS, `r = 1`, after the
   rescaling `G = √c₀ G_std` inside `gueCoordinate_count_le`).
3. *Continuity* (`continuous_palmMass`): `E ↦ palmMass F c₀ E` is continuous (dominated
   convergence; the Palm weight is bounded by the Gaussian prefactor).
4. *Pointwise* (`le_of_setLIntegral_Icc_le`): a continuous `m` with
   `∫_{[a,b]} m ≤ K (b-a)` for all `a ≤ b` satisfies `m ≤ K` everywhere.
5. `Z(e) = ofReal(palmMass)` (`pairNormalizer_eq_palmMass`, `blockNormalizer_eq_palmMass`) and
   `palmMass ≥ 0` conclude.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

/-!
## 1. The integrated Palm identity for eigenvalue tests
-/

section Integrated

variable {N : ℕ}

/-- **Integrated Palm identity for eigenvalue tests.** For `N ≥ 1`, Hermitian `F`, `c₀ > 0`,
rank `ℓ` and measurable `h ≥ 0` on `ℝ`:
`∫ h(λ_ℓ(F+G)) dGUE_N(c₀/N)(G) = ∫ h(E) · E_{A⁰}[w_{ℓ,E}] dE`.
Exact identity in `[0,∞]`. Uses the scalar split `GUE_N(t) = law(A⁰ + ζI)`
(`scalarShiftLaw_fin_eq_gueMeasure`) and the scalar Gaussian kernel. -/
theorem lintegral_eigenvalue_test_eq (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) (ℓ : Fin N) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ G, h (freshEigenvalue (F + G) ℓ) ∂gueMeasure (Fin N) (Real.toNNReal (c₀ / N)) =
      ∫⁻ E, h E * ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) := by
  set t : ℝ≥0 := Real.toNNReal (c₀ / N)
  set c₀' : ℝ≥0 := Real.toNNReal c₀
  set σ : ℝ≥0 := BlockBand.Palm.scalarVariance c₀' N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc₀' : c₀' ≠ 0 := (Real.toNNReal_pos.2 hc₀).ne'
  have hσ : (σ : ℝ) = (t : ℝ) / N := by
    rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc₀.le,
      Real.coe_toNNReal _ (div_pos hc₀ hNr).le]
    field_simp
  have hadd : ∀ {α : Type} [MeasurableSpace α] {k : α → Matrix (Fin N) (Fin N) ℂ},
      Measurable k → Measurable fun x => F + k x := fun hk =>
    FixedOmega.measurable_matrix_add measurable_const hk
  set g : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞ := fun G => h (freshEigenvalue (F + G) ℓ)
  have hg : Measurable g :=
    hh.comp ((FreshPalm.measurable_freshEigenvalue ℓ).comp (hadd measurable_id))
  set μ0 := freshTracelessLaw N c₀
  have hμ0 : μ0 = (gueMeasure (Fin N) t).map tracelessPart := rfl
  set ν : Matrix (Fin N) (Fin N) ℂ → ℝ := fun A0 => freshEigenvalue (F + A0) ℓ
  have hν : Measurable ν := (FreshPalm.measurable_freshEigenvalue ℓ).comp (hadd measurable_id)
  set Φ : Matrix (Fin N) (Fin N) ℂ × ℝ → ℝ≥0∞ := fun q => h q.2
  have hΦ : Measurable Φ := hh.comp measurable_snd
  change ∫⁻ G, g G ∂gueMeasure (Fin N) t = _
  rw [← FreshPalm.scalarShiftLaw_fin_eq_gueMeasure hN t σ hσ]
  unfold PoleExclusion.scalarShiftLaw
  rw [lintegral_map hg PoleExclusion.measurable_scalarAdd, ← hμ0]
  have hcongr : (fun y : Matrix (Fin N) (Fin N) ℂ × ℝ => g (y.1 + (y.2 : ℂ) • 1)) =ᵐ[μ0.prod
      (gaussianReal 0 σ)] fun y => Φ (y.1, ν y.1 + y.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ0)
      (ν := gaussianReal 0 σ)).ae (FreshPalm.ae_freshTracelessLaw hN c₀)] with y hy
    simp only [g, Φ, ν]
    rw [← add_assoc, FreshPalm.freshEigenvalue_add_smul_one (hF.add hy.1)]
  rw [lintegral_congr_ae hcongr,
    BlockBand.Palm.lintegral_dependentScalarShift_eq_kernel μ0 hc₀' hN.ne' hν hΦ]
  refine lintegral_congr fun E => ?_
  have hm : Measurable fun A0 : Matrix (Fin N) (Fin N) ℂ =>
      ENNReal.ofReal (palmWeight F c₀ E ℓ A0) :=
    ENNReal.measurable_ofReal.comp (measurable_palmWeight' F c₀ E ℓ)
  have h1 := lintegral_palmWeight_eq_ofReal F c₀ E ℓ
  simp only [mul_one] at h1
  rw [← h1, ← lintegral_const_mul _ hm]
  rfl

/-- `E ↦ E_{A⁰}[w_{ℓ,E}]` is continuous (dominated convergence; `w ≤ (2π c₀/N²)^{-1/2}`). -/
theorem continuous_integral_palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) (ℓ : Fin N) :
    Continuous fun E => ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀ := by
  refine continuous_of_dominated (bound := fun _ =>
      (Real.sqrt (2 * Real.pi * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))⁻¹)
    (fun E => (measurable_palmWeight' F c₀ E ℓ).aestronglyMeasurable)
    (fun E => ae_of_all _ fun A0 => ?_) (integrable_const _)
    (ae_of_all _ fun A0 => FreshPalm.continuous_palmWeight_E F c₀ ℓ A0)
  rw [Real.norm_eq_abs, abs_of_nonneg (palmWeight_nonneg' F c₀ E ℓ A0)]
  exact palmWeight_le_prefactor F c₀ E ℓ A0

/-- `E ↦ palmMass F c₀ E` is continuous. -/
theorem continuous_palmMass (F : Matrix (Fin N) (Fin N) ℂ) (c₀ : ℝ) :
    Continuous fun E => palmMass F c₀ E := by
  unfold palmMass
  exact continuous_finsetSum _ fun ℓ _ => continuous_integral_palmWeight F c₀ ℓ

/-- **Summed integrated identity.** `∫ Σ_ℓ h(λ_ℓ(F+G)) dGUE_N(c₀/N) = ∫ h(E) palmMass(F,c₀,E) dE`
(same hypotheses as `lintegral_eigenvalue_test_eq`). -/
theorem lintegral_sum_eigenvalue_test_eq (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {c₀ : ℝ} (hc₀ : 0 < c₀) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ G, ∑ ℓ : Fin N, h (freshEigenvalue (F + G) ℓ)
        ∂gueMeasure (Fin N) (Real.toNNReal (c₀ / N)) =
      ∫⁻ E, h E * ENNReal.ofReal (palmMass F c₀ E) := by
  have hadd : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => F + G :=
    FixedOmega.measurable_matrix_add measurable_const measurable_id
  rw [lintegral_finsetSum (f := fun ℓ G => h (freshEigenvalue (F + G) ℓ)) _ (fun ℓ _ =>
    hh.comp ((FreshPalm.measurable_freshEigenvalue ℓ).comp hadd))]
  simp_rw [lintegral_eigenvalue_test_eq hN hF hc₀ _ hh]
  have hmE : ∀ ℓ : Fin N, Measurable fun E =>
      h E * ENNReal.ofReal (∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀) := fun ℓ =>
    hh.mul (ENNReal.measurable_ofReal.comp (continuous_integral_palmWeight F c₀ ℓ).measurable)
  rw [← lintegral_finsetSum _ (fun ℓ _ => hmE ℓ)]
  refine lintegral_congr fun E => ?_
  rw [palmMass, ENNReal.ofReal_sum_of_nonneg (fun ℓ _ =>
    integral_nonneg fun A0 => palmWeight_nonneg' _ c₀ E ℓ A0), Finset.mul_sum]

end Integrated

/-!
## 2. PSSS (`r = 1`): mean eigenvalue count of `F + GUE_N(c₀/N)`
-/

section Count

variable {N : ℕ}

/-- The sum of the interval indicators over the ranks is the PSSS multiplicity count
(`PSSS.eigenCount`), for every Hermitian `K` and every set `I`. Deterministic. -/
theorem sum_indicator_freshEigenvalue_eq_eigenCount {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : K.IsHermitian) (I : Set ℝ) :
    (∑ ℓ : Fin N, I.indicator (fun _ => (1 : ℝ≥0∞)) (freshEigenvalue K ℓ)) =
      (BlockBand.External.PSSS.eigenCount ⟨K, hK⟩ I : ℝ≥0∞) := by
  classical
  unfold BlockBand.External.PSSS.eigenCount
  rw [Finset.card_filter]
  push_cast
  refine Fintype.sum_equiv (finCongr (Fintype.card_fin N).symm) _ _ fun ℓ => ?_
  simp only [finCongr_apply, Set.indicator_apply]
  unfold freshEigenvalue
  rw [rawIncreasingEigenvalue_eq _ _ hK]

/-- **Wegner bound from PSSS at `r = 1`.** One constant `C > 0` (the PSSS constant) before all
`N ≥ 1`, `c₀ > 0`, Hermitian `F` and `a ≤ b`:
`E_{G ~ GUE_N(c₀/N)} #{ℓ : λ_ℓ(F+G) ∈ [a,b]} ≤ C/√c₀ · N · (b-a)`.
Uses only `PSSS.SourceContract` (through `Wegner.gueCoordinate_count_le`). -/
theorem lintegral_count_le (source : BlockBand.External.PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (c₀ : ℝ), 0 < c₀ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ (a b : ℝ), a ≤ b →
        ∫⁻ G, ∑ ℓ : Fin N, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞))
            (freshEigenvalue (F + G) ℓ) ∂gueMeasure (Fin N) (Real.toNNReal (c₀ / N)) ≤
          ENNReal.ofReal (C / Real.sqrt c₀ * N * (b - a)) := by
  obtain ⟨C, hC, hcount⟩ := BlockBand.Wegner.gueCoordinate_count_le source
  refine ⟨C, hC, fun N hN c₀ hc₀ F hF a b hab => ?_⟩
  have hadd : Measurable fun G : Matrix (Fin N) (Fin N) ℂ => F + G :=
    FixedOmega.measurable_matrix_add measurable_const measurable_id
  have hmeas : Measurable fun G : Matrix (Fin N) (Fin N) ℂ =>
      ∑ ℓ : Fin N, (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) (freshEigenvalue (F + G) ℓ) :=
    Finset.measurable_sum _ fun ℓ _ =>
      (measurable_const.indicator measurableSet_Icc).comp
        ((FreshPalm.measurable_freshEigenvalue ℓ).comp hadd)
  have hraw : Measurable (BlockBand.External.Johansson.gaussianMatrixRaw (N := N)) :=
    measurable_subtype_coe.comp BlockBand.External.Johansson.measurable_gaussianMatrix
  rw [← BlockBand.Palm.MomentFlow.map_gaussianMatrixRaw, lintegral_map hmeas hraw]
  refine le_trans (le_of_eq (lintegral_congr fun z => ?_)) (hcount N hN c₀ hc₀ F hF a b hab)
  exact sum_indicator_freshEigenvalue_eq_eigenCount
    (hF.add (BlockBand.External.Johansson.gaussianMatrix z).2) _

end Count

/-!
## 3. From interval bounds to a pointwise bound
-/

/-- A continuous `m : ℝ → ℝ` with `∫_{[a,b]} m ≤ K (b - a)` for all `a ≤ b` (and `K ≥ 0`)
satisfies `m ≤ K` everywhere. Deterministic. -/
theorem le_of_setLIntegral_Icc_le {m : ℝ → ℝ} (hm : Continuous m) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ a b : ℝ, a ≤ b →
      ∫⁻ E in Set.Icc a b, ENNReal.ofReal (m E) ≤ ENNReal.ofReal (K * (b - a)))
    (E₀ : ℝ) : m E₀ ≤ K := by
  by_contra hlt
  push Not at hlt
  set K' := (m E₀ + K) / 2 with hK'
  have hK1 : K < K' := by linarith
  have hK2 : K' < m E₀ := by linarith
  have hev : ∀ᶠ E in 𝓝 E₀, K' < m E := hm.continuousAt.eventually (lt_mem_nhds hK2)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set δ := ε / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hsub : ∀ E ∈ Set.Icc E₀ (E₀ + δ), K' < m E := fun E hE => hball (by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hE.1, hE.2])
  have hlow : ENNReal.ofReal (K' * δ) ≤ ∫⁻ E in Set.Icc E₀ (E₀ + δ), ENNReal.ofReal (m E) := by
    calc ENNReal.ofReal (K' * δ) = ∫⁻ _ in Set.Icc E₀ (E₀ + δ), ENNReal.ofReal K' := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
          congr 1
          ring
      _ ≤ _ := setLIntegral_mono (ENNReal.measurable_ofReal.comp hm.measurable)
          (fun E hE => ENNReal.ofReal_le_ofReal (hsub E hE).le)
  have hup := h E₀ (E₀ + δ) (by linarith)
  have hle := hlow.trans hup
  rw [ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at hle
  have : K' * δ ≤ K * δ := by
    have e : E₀ + δ - E₀ = δ := by ring
    rwa [e] at hle
  nlinarith

/-!
## 4. The deformed-GUE one-point density bound
-/

/-- **Palm mass bound (deformed-GUE one-point density).** One constant `C > 0` (the PSSS
constant) before all `N ≥ 1`, `c₀ > 0`, Hermitian `F` and real `E`:
`palmMass F c₀ E = Σ_ℓ E_{A⁰}[w_{ℓ,E}] ≤ C/√c₀ · N`. Uses only `PSSS.SourceContract`. -/
theorem palmMass_le (source : BlockBand.External.PSSS.SourceContract.{0}) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (c₀ : ℝ), 0 < c₀ →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian → ∀ E : ℝ,
        palmMass F c₀ E ≤ C / Real.sqrt c₀ * N := by
  obtain ⟨C, hC, hcount⟩ := lintegral_count_le source
  refine ⟨C, hC, fun N hN c₀ hc₀ F hF => ?_⟩
  refine le_of_setLIntegral_Icc_le (continuous_palmMass F c₀) (by positivity) fun a b hab => ?_
  have hid := lintegral_sum_eigenvalue_test_eq hN hF hc₀
    (h := (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator measurableSet_Icc)
  rw [← lintegral_indicator measurableSet_Icc]
  have hfun : (Set.Icc a b).indicator (fun E => ENNReal.ofReal (palmMass F c₀ E)) =
      fun E => (Set.Icc a b).indicator (fun _ => (1 : ℝ≥0∞)) E *
        ENNReal.ofReal (palmMass F c₀ E) := by
    funext E
    by_cases hE : E ∈ Set.Icc a b <;> simp [hE]
  rw [hfun, ← hid]
  exact hcount N hN c₀ hc₀ F hF a b hab

/-!
## 5. The upper bound for the pair and for one block
-/

theorem reindex_isHermitian {ι κ : Type*} {F : Matrix ι ι ℂ} (hF : F.IsHermitian)
    (σ : ι ≃ κ) : (Matrix.reindex σ σ F).IsHermitian := by
  rw [Matrix.reindex_apply]
  exact hF.submatrix _

/-- **, pair**.
The exact type of `ExactPalmContract.upper`.
With `C` the PSSS constant,
`C_b = C/√(min(b, 1-2b))`; for every `p` with `p.b = b`, pair `i`, measurable frame `U`,
Hermitian exterior `ω` and real `e`:
`Z(e) = pairNormalizer ≤ C_b · 2W`.
Consumes `FreshEigenpairDensityContract` (`hD`, via `pairNormalizer_eq_palmMass`) and
`NativeInputs.psss`.
-/
theorem exactPalm_upper_of (inputs : BlockBand.External.NativeInputs.{0})
    (hD : FreshEigenpairDensityContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (i : ZMod p.n) (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
    IsPairFrame p i U → ∀ ω : SplitState p i, IsHermitianExterior p i ω → ∀ e : ℝ,
      pairNormalizer p i U ω e ≤ ENNReal.ofReal (C * (2 * p.W)) := by
  obtain ⟨C, -, hZ⟩ := palmMass_le inputs.psss
  intro b _ _
  refine ⟨C / Real.sqrt (min b (1 - 2 * b)), ?_⟩
  intro p hpb i U hU ω hω e
  rw [pairNormalizer_eq_palmMass p i hD (FixedOmega.pairEquiv p i) U hU ω hω e]
  apply ENNReal.ofReal_le_ofReal
  have hF := reindex_isHermitian (physicalCoareaF_isHermitian' ω.1 ω.2.1 ω.2.2 hω.1 hω.2 e)
    (FixedOmega.pairEquiv p i)
  have hle := hZ (2 * p.W) (two_W_pos p) (pairS p) (pairS_pos p) _ hF e
  have hs : pairS p = min b (1 - 2 * b) := by subst hpb; rfl
  rw [hs] at hle ⊢
  refine hle.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The upper bound of the one-block normalizer** (`Z₀/W ≤ C/√c`, one-block PSSS with `r = 1`),
in the exact type of `OneBlockPalmContract.upper`.
With `C` the PSSS constant, the constant is
`C/√(1-2b)`; for every `p` with `p.b = b`, block `k`, measurable block frame `U`, exterior
`ω = (H_R, C)` with Hermitian `H_R` (every `C`) and real `e`:
`Z₀(e) ≤ C/√(1-2b) · W`.
Consumes `FreshEigenpairDensityContract` (`hD`, via `blockNormalizer_eq_palmMass`) and
`NativeInputs.psss`.
-/
theorem oneBlockPalm_upper_of (inputs : BlockBand.External.NativeInputs.{0})
    (hD : FreshEigenpairDensityContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ (p : Parameters), p.b = b →
    ∀ (k : ZMod p.n) (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ),
    IsBlockFrame p k U → ∀ ω : BlockState p k, ω.1.IsHermitian → ∀ e : ℝ,
      blockNormalizer p k U ω e ≤ ENNReal.ofReal (C * p.W) := by
  obtain ⟨C, -, hZ⟩ := palmMass_le inputs.psss
  intro b _ _
  refine ⟨C / Real.sqrt (1 - 2 * b), ?_⟩
  intro p hpb k U hU ω hω e
  rw [blockNormalizer_eq_palmMass p k hD (blockEquiv p k) U hU ω hω e]
  apply ENNReal.ofReal_le_ofReal
  have hF := reindex_isHermitian (blockF_isHermitian p k ω hω e) (blockEquiv p k)
  have hle := hZ p.W p.W_pos p.c p.c_pos _ hF e
  have hs : p.c = 1 - 2 * b := by subst hpb; rfl
  rw [hs] at hle ⊢
  exact hle

/-- Type check: `exactPalm_upper_of` has exactly the type of the field `ExactPalmContract.upper`. -/
example (inputs : BlockBand.External.NativeInputs.{0}) (hD : FreshEigenpairDensityContract)
    (h : ExactPalmContract) : ExactPalmContract :=
  { h with upper := exactPalm_upper_of inputs hD }

/-- Type check: `oneBlockPalm_upper_of` has exactly the type of `OneBlockPalmContract.upper`. -/
example (inputs : BlockBand.External.NativeInputs.{0}) (hD : FreshEigenpairDensityContract)
    (h : OneBlockPalmContract) : OneBlockPalmContract :=
  { h with upper := oneBlockPalm_upper_of inputs hD }

end BlockBand.Endpoints.Normalization
