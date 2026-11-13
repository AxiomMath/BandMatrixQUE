module

public import BlockBand.Layers.OnePortMeanAlgebra
public import BlockBand.Layers.OnePortMoments
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# One-port passive mean (`OnePortPassiveMeanContract`): assembly

The passive mean `E_j LL* ⪯ (1 + Cδ₀ + CW⁻²) I` of the one-port layer, a consequence of the
passive mean identity, the exact identity `(η - Im Ω)(1 - k_hA_M) = bhη + k_h y_M` and the
passive-bounds lemma.

Main results:
* `onePortPassiveMean_of (hinv) (hmom) (hsd) : OnePortPassiveMeanContract`, from the passive
  inverse moments `OppPassiveInverseMoments`, the operator moments
  `OnePortOperatorMomentsContract` and the passive Schwinger–Dyson system
  `OppPassiveMeanEquations` (the remaining estimate, stated in `OnePortMeanInputs` and proved in `OnePortSD`);
* `onePortPassiveMean_holds_of_meanEquations (hcount) (hsd)`: the same with the first two inputs
  discharged by `opm_passive_inverse_moments` and
  `onePortOperatorMoments_holds`.

Proof. Large `δ₀ > d₁ = bη₀/2`: `‖E LL*‖ ≤ E‖L‖² ≤ C₂²` (operator moments at `p = 2`), so
`E LL* ⪯ C₂² I ⪯ (1 + (C₂²/d₁)δ₀) I`. Small `δ₀ ≤ d₁`: `opp_core_bound` (deterministic reduction,
`OnePortMeanAlgebra`) applied to the layer means, with `‖E𝒢₁₁‖, |ḡ₂| ≤ E‖𝒢‖ ≤ C₀` (inverse moments
at `p = 1`) and the relations of `OppPassiveMeanEquations` at error `ρ = C/W² ≤ ρ₀`. In both cases
`E LL*` is Hermitian, so `‖E LL*‖ ≤ λ` gives `E LL* ⪯ λ I` (C*-order of matrices).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.LayersOnePort
open BlockBand.Internal.Contracts.Inputs (ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Loewner bound from the operator norm; Hermitian expectations
-/

open scoped MatrixOrder in
/-- A Hermitian `H` with `‖H‖ ≤ r` satisfies `H ⪯ r I`. -/
theorem opp_posSemidef_of_norm_le {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {r : ℝ} (hr : ‖H‖ ≤ r) :
    (((r : ℂ)) • (1 : Matrix n n ℂ) - H).PosSemidef := by
  have h1 := IsSelfAdjoint.le_algebraMap_norm_self H (Matrix.isHermitian_iff_isSelfAdjoint.mp hH)
  rw [Matrix.le_iff, Algebra.algebraMap_eq_smul_one] at h1
  have h2 : (((r - ‖H‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
    refine Matrix.PosSemidef.smul Matrix.PosSemidef.one ?_
    exact Complex.nonneg_iff.mpr ⟨by simp; linarith, by simp⟩
  have := h2.add h1
  convert this using 1
  rw [Complex.ofReal_sub, sub_smul]
  ext i j
  simp [Matrix.smul_apply]

/-- The entrywise expectation of a Hermitian-valued random matrix is Hermitian. -/
theorem opp_matrixExpect_isHermitian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : Type*} {F : Ω → Matrix n n ℂ} (hF : ∀ ω, (F ω).IsHermitian) :
    (matrixExpect μ F).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
  rw [show star (∫ ω, F ω j i ∂μ) = conj (∫ ω, F ω j i ∂μ) from rfl, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have := congrFun (congrFun (hF ω) i) j
  rw [conjTranspose_apply] at this
  exact this

/-- `‖E F‖ ≤ E‖F‖` for an integrable random matrix. -/
theorem opp_norm_matrixExpect_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {W : ℕ}
    {F : Ω → Matrix (Fin W) (Fin W) ℂ} (hF : Integrable F μ) :
    ‖matrixExpect μ F‖ ≤ ∫ ω, ‖F ω‖ ∂μ := by
  rw [meq_matrixExpect_eq hF]
  exact norm_integral_le_integral_norm _

/-!
## 2. Moments
-/

/-- First moment from an `L¹` bound: `E f ≤ max C 0`. -/
theorem opp_integral_le_of_eLpNorm_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hnn : ∀ ω, 0 ≤ f ω) {C : ℝ}
    (h : eLpNorm f (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ max C 0 := by
  rw [ENNReal.ofReal_one] at h
  have hmem : MemLp f 1 μ := memLp_iff.mpr (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  have hint : Integrable f μ := memLp_one_iff_integrable.mp hmem
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hf]
  refine ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) ?_
  rw [eLpNorm_one_eq_lintegral_enorm hf] at h
  refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  exact lintegral_congr fun ω => by rw [Real.enorm_eq_ofReal (hnn ω)]

/-- Second moment from an `L²` bound: `E f² ≤ (max C 0)²`. -/
theorem opp_integral_sq_le_of_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hnn : ∀ ω, 0 ≤ f ω) {C : ℝ}
    (h : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal C) :
    Integrable (fun ω => f ω ^ 2) μ ∧ ∫ ω, f ω ^ 2 ∂μ ≤ (max C 0) ^ 2 := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have hC : eLpNorm f (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal (max C 0) :=
    h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hmem : MemLp f 2 μ := memLp_iff.mpr (by rw [← h2]; exact lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  refine ⟨hmem.integrable_sq, ?_⟩
  have hl := opm_lintegral_le_of_eLpNorm hf (by norm_num : (0 : ℝ) < 2) hC
  have hsq : ∀ ω, 0 ≤ f ω ^ 2 := fun ω => sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hsq) (hf.pow 2)]
  refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) ?_
  have e1 : ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ = ∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hnn ω), ENNReal.ofReal_rpow_of_nonneg (hnn ω) (by norm_num),
      Real.rpow_two]
  rw [e1]
  refine hl.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) (by norm_num), Real.rpow_two]

/-!
## 3. The objects of the one-port layer
-/

section Layer

variable {W : ℕ}

theorem opp_oppG11_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    oppG11 b E X ω = (onePortResolvent b E X ω).submatrix (fun x => Sum.inl ((0 : Fin 1), x))
      (fun y => Sum.inl ((0 : Fin 1), y)) := rfl

theorem opp_oppG22_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    oppG22 b E X ω = (onePortResolvent b E X ω).submatrix (fun x => Sum.inr ((0 : Fin 1), x))
      (fun y => Sum.inr ((0 : Fin 1), y)) := rfl

theorem opp_measurable_resolvent (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (onePortResolvent b E X) :=
  measurable_layerResolvent _ _ _ _

/-- Integrability and the bound `‖E Bₘ‖ ≤ max C 0` for a corner block `Bₘ` of `𝒢`, from
`‖ ‖𝒢‖ ‖_{L¹} ≤ C`. -/
theorem opp_block_mean_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (h : eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal 1)
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C)
    {f g : Fin W → LayerSite W .oneBlockOnePort} (hf : Function.Injective f)
    (hg : Function.Injective g) :
    ‖matrixExpect (layerLaw W b .oneBlockOnePort)
        (fun ω => (onePortResolvent b E X ω).submatrix f g)‖ ≤ max C 0 := by
  have hGm := (opp_measurable_resolvent b E X).aestronglyMeasurable
    (μ := layerLaw W b .oneBlockOnePort)
  obtain ⟨hint, hI⟩ := opp_integral_le_of_eLpNorm_one hGm.norm (fun _ => norm_nonneg _) h
  have hBm : AEStronglyMeasurable (fun ω => (onePortResolvent b E X ω).submatrix f g)
      (layerLaw W b .oneBlockOnePort) :=
    (continuous_id.matrix_submatrix f g).comp_aestronglyMeasurable hGm
  have hbd : ∀ ω, ‖(onePortResolvent b E X ω).submatrix f g‖ ≤ ‖onePortResolvent b E X ω‖ :=
    fun ω => wl_norm_submatrix_le _ hf hg
  have hBi : Integrable (fun ω => (onePortResolvent b E X ω).submatrix f g)
      (layerLaw W b .oneBlockOnePort) :=
    hint.mono' hBm (ae_of_all _ hbd)
  refine (opp_norm_matrixExpect_le hBi).trans ?_
  refine le_trans ?_ hI
  exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hint (ae_of_all _ hbd)

/-- `‖E𝒢₁₁‖ ≤ max C 0`. -/
theorem opp_norm_meanTop_le {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (h : eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal 1)
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C) :
    ‖oppMeanTop b E X‖ ≤ max C 0 :=
  opp_block_mean_le h (fun x y hxy => by simpa using hxy) (fun x y hxy => by simpa using hxy)

/-- `|ḡ₂| ≤ max C 0`. -/
theorem opp_norm_G2_le (hW : 0 < W) {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} {C : ℝ}
    (h : eLpNorm (fun ω => ‖onePortResolvent b E X ω‖) (ENNReal.ofReal 1)
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C) :
    ‖oppG2 b E X‖ ≤ max C 0 :=
  (opp_norm_ntrace_le hW _).trans
    (opp_block_mean_le h (fun x y hxy => by simpa using hxy) (fun x y hxy => by simpa using hxy))

/-- `t₁ ≥ 0`. -/
theorem opp_T1_nonneg (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ oppT1 b E X :=
  integral_nonneg fun ω => mul_nonneg (by positivity) (opp_trace_self_nonneg _)

/-- From `‖ ‖L‖ ‖_{L²} ≤ C`: the entries of `LL*` are integrable, `E LL*` is Hermitian and
`‖E LL*‖ ≤ (max C 0)²`. -/
theorem opp_LL_facts {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hLm : Measurable (onePortL b E X))
    {C : ℝ} (h : eLpNorm (fun ω => ‖onePortL b E X ω‖) (ENNReal.ofReal 2)
      (layerLaw W b .oneBlockOnePort) ≤ ENNReal.ofReal C) :
    (∀ x y, Integrable (fun ω => (onePortL b E X ω * (onePortL b E X ω)ᴴ) x y)
        (layerLaw W b .oneBlockOnePort)) ∧
      (matrixExpect (layerLaw W b .oneBlockOnePort)
        (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ)).IsHermitian ∧
      ‖matrixExpect (layerLaw W b .oneBlockOnePort)
        (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ)‖ ≤ (max C 0) ^ 2 := by
  set μ := layerLaw W b .oneBlockOnePort
  have hLa : AEStronglyMeasurable (onePortL b E X) μ := hLm.aestronglyMeasurable
  obtain ⟨hsq, hI⟩ := opp_integral_sq_le_of_eLpNorm_two hLa.norm (fun _ => norm_nonneg _) h
  have hUm : AEStronglyMeasurable (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ) μ :=
    (continuous_id.matrix_mul continuous_id.matrix_conjTranspose).comp_aestronglyMeasurable hLa
  have hbd : ∀ ω, ‖onePortL b E X ω * (onePortL b E X ω)ᴴ‖ ≤ ‖onePortL b E X ω‖ ^ 2 :=
    fun ω => opp_norm_mul_conjTranspose_le _
  have hUi : Integrable (fun ω => onePortL b E X ω * (onePortL b E X ω)ᴴ) μ :=
    hsq.mono' hUm (ae_of_all _ hbd)
  refine ⟨fun x y => ?_, opp_matrixExpect_isHermitian fun ω => isHermitian_mul_conjTranspose_self _,
    ?_⟩
  · exact (LinearMap.toContinuousLinearMap
      (Matrix.entryLinearMap ℂ ℂ x y : Matrix (Fin W) (Fin W) ℂ →ₗ[ℂ] ℂ)).integrable_comp hUi
  · refine (opp_norm_matrixExpect_le hUi).trans (le_trans ?_ hI)
    exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hsq (ae_of_all _ hbd)

end Layer

/-!
## 4. The contract
-/

/-- **One-port passive mean** (`OnePortPassiveMeanContract`), from three named inputs.

* **Law.** The fresh one-block one-port layer `layerLaw W b .oneBlockOnePort`
  (`A ~ GUE_W(c/W)`, `c = 1 - 2b`, `B ~ Gin(b/W)`) at `z = z_∂(E)`; expectations over the fresh
  layer only, conditional on the deterministic (independent) passive `X`; `𝒢 = onePortResolvent`,
  `K = z - X`, `L = K𝒢₁₂`, `δ₀ = onePortDistance b E X = |W⁻¹ Tr(z - X)⁻¹ - a|`.
* **Domain / quantifiers.** `b ∈ (0,1/2)`, `κ > 0`; then `C ≥ 0`, `W₀`; then uniformly in
  `W ≥ W₀`, every passive `X` (`-Im X ⪰ 0`, no bound on `‖X‖` or `‖Im X‖`, no jet-domain or
  scalar-domain restriction) and `E ∈ bulkInterval κ`.
* **Norms.** Euclidean operator norm on `W × W` matrices; Loewner order `M ⪯ λI` as
  `(λI - M).PosSemidef`; expectations entrywise (`matrixExpect`).
* **Conclusion.** The entries of `LL*` are integrable and `E LL* ⪯ (1 + Cδ₀ + CW⁻²) I`.
* **Inputs (named, not hypotheses of the contract).**
  - `hinv : OppPassiveInverseMoments` — `‖ ‖𝒢‖ ‖_{L^p} ≤ C_p` uniformly in passive `X`
    (the passive-bounds lemma); discharged by `opm_passive_inverse_moments hcount`
    (`opp_inverseMoments_of_opm`). Used at `p = 1`.
  - `hmom : OnePortOperatorMomentsContract` — `‖ ‖L‖ ‖_{L^p} ≤ C_p`; discharged by
    `onePortOperatorMoments_holds hcount`. Used at `p = 2`.
  - `hsd : OppPassiveMeanEquations` — the passive one-port Schwinger–Dyson system with
    `O(W⁻²)` errors at the layer means (in the paper: the mean equations, the bottom-source
    trace equations and the first form of the passive mean identity), uniformly in passive `X`.
* **Proof.** With `η₀` the bulk lower bound of `Im z_∂` and `d₁ = bη₀/2`:
  - `δ₀ > d₁`: `‖E LL*‖ ≤ E‖L‖² ≤ C₂²` (`hmom`, `p = 2`) and `C₂² ≤ (C₂²/d₁)δ₀`.
  - `δ₀ ≤ d₁`: `opp_core_bound` (deterministic; `OnePortMeanAlgebra`) at `Ḡ = E𝒢₁₁`, `ḡ₂`,
    `t₁ ≥ 0`, `t₂`, `U = E LL*`, with `‖Ḡ‖, |ḡ₂| ≤ C₀` from `hinv` and the five relations of `hsd`
    at `ρ = C/W² ≤ ρ₀` (`W ≥ W₀`): `‖E LL*‖ ≤ 1 + C₁(δ₀ + C/W²)`. Only `δ₀` small is used; `Y`
    enters through `W⁻¹Tr M̄*YM̄ ≥ 0` and `W⁻¹Tr R*YR ≥ 0` only (Ward identities with the right
    sign), so the bound is uniform in an unbounded absorber.
  - `E LL*` is Hermitian, so `‖E LL*‖ ≤ λ` gives `E LL* ⪯ λI` (`opp_posSemidef_of_norm_le`).
* **Constants.** `C = max(C₁, C₁C_eq, C₂²/d₁)` and `W₀`, depending only on `b, κ` (through
  `η₀`, `C₀`, `C₂`, `C_eq`). -/
theorem onePortPassiveMean_of (hinv : OppPassiveInverseMoments)
    (hmom : OnePortOperatorMomentsContract) (hsd : OppPassiveMeanEquations) :
    OnePortPassiveMeanContract := by
  intro b hb0 hb1 κ hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := wl_bulk hb0 hb1 hκ
  obtain ⟨Ci, Wi, hi⟩ := hinv b hb0 hb1 κ hκ 1 le_rfl
  obtain ⟨Cm, Wm, hm⟩ := hmom.moments b hb0 hb1 κ hκ 2 (by norm_num)
  obtain ⟨Ce, We, he⟩ := hsd b hb0 hb1 κ hκ
  set C₀ : ℝ := max (max Ci 0) 1 with hC₀
  have hC₀1 : 1 ≤ C₀ := le_max_right _ _
  have hCiC₀ : max Ci 0 ≤ C₀ := le_max_left _ _
  obtain ⟨-, -, hρ₀0, -, -, -, -, -, -, hC₁0⟩ := opp_constants_pos hb0 hb1 hη₀ hC₀1
  set ρ₀ := oppRho0 b η₀ C₀ with hρ₀
  set C₁ := oppC1 b η₀ C₀ with hC₁
  set Cp : ℝ := max Ce 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  set d₁ : ℝ := b * η₀ / 2 with hd₁
  have hd₁0 : 0 < d₁ := by positivity
  set C₂ : ℝ := max Cm 0 with hC₂
  set C : ℝ := max (max C₁ (C₁ * Cp)) (C₂ ^ 2 / d₁) with hC
  have hCC₁ : C₁ ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCC₁p : C₁ * Cp ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCC₂ : C₂ ^ 2 / d₁ ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := hC₁0.trans hCC₁
  refine ⟨C, max (max Wi Wm) (max We (⌈Cp / ρ₀⌉₊ + 1)), hC0, ?_⟩
  intro W hW hWW X hX E hE μ U
  have hWi : Wi ≤ W := (le_max_left _ _).trans ((le_max_left _ _).trans hWW)
  have hWm : Wm ≤ W := (le_max_right _ _).trans ((le_max_left _ _).trans hWW)
  have hWe : We ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hWW)
  have hWc : ⌈Cp / ρ₀⌉₊ + 1 ≤ W := (le_max_right _ _).trans ((le_max_right _ _).trans hWW)
  obtain ⟨hηE, hnz, hE2⟩ := hbulk E hE
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  -- moments of `L`: integrability, Hermitian mean, crude bound
  obtain ⟨hint, hherm, hcrude⟩ := opp_LL_facts (hmom.measurable W b E X) (hm W hW hWm X hX E hE)
  refine ⟨hint, ?_⟩
  set δ := onePortDistance b E X with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hW2 : (0 : ℝ) ≤ C / (W : ℝ) ^ 2 := by positivity
  refine opp_posSemidef_of_norm_le hherm ?_
  by_cases hsmall : δ ≤ d₁
  · -- small `δ₀`: the deterministic reduction
    have hiW := hi W hW hWi X hX E hE
    have hG : ‖oppMeanTop b E X‖ ≤ C₀ := (opp_norm_meanTop_le hiW).trans hCiC₀
    have hg₂ : ‖oppG2 b E X‖ ≤ C₀ := (opp_norm_G2_le hW hiW).trans hCiC₀
    obtain ⟨e1, e2, e3, e4, e5⟩ := he W hW hWe X hX E hE
    set ρ : ℝ := Cp / (W : ℝ) ^ 2 with hρdef
    have hρ0 : 0 ≤ ρ := by positivity
    have hCeρ : Ce / (W : ℝ) ^ 2 ≤ ρ :=
      div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    have hρρ₀ : ρ ≤ ρ₀ := by
      have h1 : Cp / ρ₀ ≤ (W : ℝ) := by
        have := Nat.le_ceil (Cp / ρ₀)
        have h2 : ((⌈Cp / ρ₀⌉₊ : ℕ) : ℝ) ≤ (W : ℝ) := by exact_mod_cast (Nat.le_succ _).trans hWc
        linarith
      have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
      have h3 : Cp ≤ ρ₀ * W := by rwa [div_le_iff₀ hρ₀0, mul_comm] at h1
      have h4 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
      rw [hρdef, div_le_iff₀ (by positivity)]
      nlinarith
    have hcore := opp_core_bound hb0 hb1 hη₀ hC₀1 hW hE2 hηE hX hsmall hρ0 hρρ₀ hG hg₂
      (opp_T1_nonneg b E X) (e1.trans hCeρ) (e2.trans hCeρ) (e3.trans hCeρ) (e4.trans hCeρ)
      (e5.trans hCeρ)
    refine hcore.trans ?_
    have i1 : C₁ * δ ≤ C * δ := mul_le_mul_of_nonneg_right hCC₁ hδ0
    have i2 : C₁ * ρ ≤ C / (W : ℝ) ^ 2 := by
      rw [hρdef, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hCC₁p (by positivity)
    nlinarith only [i1, i2]
  · -- large `δ₀`: the crude bound from the operator moments
    push Not at hsmall
    have h1 : C₂ ^ 2 ≤ C * δ := by
      have : C₂ ^ 2 = C₂ ^ 2 / d₁ * d₁ := by field_simp
      rw [this]
      exact mul_le_mul hCC₂ hsmall.le hd₁0.le hC0
    have : ‖matrixExpect μ U‖ ≤ C₂ ^ 2 := hcrude
    linarith

/-- The passive inverse moments, from `opm_passive_inverse_moments`
(which also gives a.s. invertibility and the `𝒢₁₁` moments). -/
theorem opp_inverseMoments_of_opm (hcount : ConditionalBlockGUECount) :
    OppPassiveInverseMoments := by
  intro b hb0 hb1 κ hκ p hp
  obtain ⟨C, W₀, -, h⟩ := opm_passive_inverse_moments hcount b hb0 hb1 κ hκ p hp
  exact ⟨C, W₀, fun W hW hWW X hX E hE => (h W hW hWW X hX E hE).2.1⟩

/-- **`OnePortPassiveMeanContract` from `ConditionalBlockGUECount` and the passive
Schwinger–Dyson system** `OppPassiveMeanEquations` (see `onePortPassiveMean_of`). The inverse and
operator moments are supplied by `opm_passive_inverse_moments` and
`onePortOperatorMoments_holds`. Conditional on `hsd`. -/
theorem onePortPassiveMean_holds_of_meanEquations (hcount : ConditionalBlockGUECount)
    (hsd : OppPassiveMeanEquations) : OnePortPassiveMeanContract :=
  onePortPassiveMean_of (opp_inverseMoments_of_opm hcount) (onePortOperatorMoments_holds hcount) hsd

end BlockBand.Layers
