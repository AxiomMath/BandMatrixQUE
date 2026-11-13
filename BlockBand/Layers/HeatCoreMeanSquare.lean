module

public import BlockBand.Layers.HeatAbsorption

/-!
# The mean-square trace errors along the heat interpolation: generic form and the cores

The input `ChtCoreMeanSquare` of `CompensatedCore` ("The constant mean is `a` and the finite core
stability was proved in the matched-traces theorem"), and the generic argument behind
`ChtMeanSquare`: the mean equations along the interpolation have the constant comparison value
`a`, and the same stable-branch comparison as in the layer-contraction lemma gives trace errors
`O_{L²}(d + W⁻¹)` uniformly in `t`.

Setting (generic, §1–3): a finite Gaussian vector `x ~ gaussianProduct v`, the affine heat path
`ℋ_t(x) = C₀ + t C₁ + √t Λx` (`chtPath`, `Λ` Hermitian-valued) on the layer sites, block traces
`g_β = W⁻¹ Tr P_β ℋ_t⁻¹` (`coreTr`), a block-constant contraction `S(G) = D(g(G))` with weights
`|w_βγ| ≤ 1` (`hmsD`), `C₁ = D(a)` and the reference inverse `Π = C₀⁻¹` (so `Π⁻¹ = C₀ + tC₁ - tD(a)`
for every `t`: the comparison value is `a` for every `t`). Norms: `ℓ²` operator norm, modulus.

* §1 `hmsTr`, `hmsD`, `hmsS`: normalized traces against deterministic matrices; block-constant
  self-energies.
* §2 **`hms_linear`** (abstract law): from `C₀ E[G] - 1 = t E[D(g - a) G]`, `E‖G‖² ≤ M` and the
  trace fluctuations `‖W⁻¹Tr(DG) - E‖₂ ≤ V‖D‖`, the mean errors `ε̄ = E g - a` solve the
  linearized equations `ε̄_β = (tr_β Π - a) + t Σ_γ tr_β(Π P_γ Π) s_γ(ε̄) + r_β` with
  `|r_β| ≤ K_r(e + V²)`, `e = E Σ_β |g_β - a|²` (Cauchy–Schwarz on covariances; the quadratic
  term through `‖E G - Π‖ ≤ C√e`).
* §3 the Gaussian path: `hms_path_sd` (`core_limit_identity`), `hms_path_fl` (`core_fluctuation`,
  `V = 4√2 Cg Γ C_A²/W`), `hms_path_quad` (`e(t) ≤ K₁(d² + V²) + K₁ e(t)²` under the
  deterministic stability `HmsStable`), `hms_err_continuousOn` (dominated convergence),
  `hms_boot` (continuity from `e(0) ≤ 2d²`), **`hms_meanSquare_gen`**:
  `e(t) ≤ 2K₁(d² + V²)` for all `t ∈ [0, 1)`.
* §4 the cores (`Π = a`, `d = 0`): weights `coreW1`, `coreW2`, stability
  (`hms_core1_stable`: margin `2b(1-b)`; `hms_core2_stable`: margin `b(1-b)`), and
  **`chtCoreMeanSquare_holds (hcount) (hgrad) : ChtCoreMeanSquare`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Complex
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. Normalized traces and block-constant self-energies
-/

section Traces

variable {W : ℕ} {σ : LayerShape}

/-- The normalized trace `W⁻¹ Tr(D M)`. -/
def hmsTr (D M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) : ℂ := (W : ℂ)⁻¹ * (D * M).trace

/-- `M ↦ W⁻¹ Tr(D M)` as a continuous linear map. -/
def hmsTrCLM (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Matrix (LayerSite W σ) (LayerSite W σ) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := hmsTr D
      map_add' := fun M N => by simp [hmsTr, Matrix.trace_add, mul_add]
      map_smul' := fun c M => by
        simp only [hmsTr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]; ring }

theorem hmsTrCLM_apply (D M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    hmsTrCLM D M = hmsTr D M := rfl

theorem hms_continuous_tr (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    Continuous (fun M => hmsTr D M) := (hmsTrCLM D).continuous

theorem hms_norm_tr_le (hW : 0 < W) (D M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ‖hmsTr D M‖ ≤ 4 * (‖D‖ * ‖M‖) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [hmsTr, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := tfl_trace_le (D * M)
  have h2 := tfl_card_layerSite_le (W := W) (σ := σ)
  have h3 : ‖D * M‖ ≤ ‖D‖ * ‖M‖ := norm_mul_le _ _
  calc (W : ℝ)⁻¹ * ‖(D * M).trace‖ ≤ (W : ℝ)⁻¹ * (4 * W * (‖D‖ * ‖M‖)) := by
        gcongr
        exact h1.trans (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
    _ = 4 * (‖D‖ * ‖M‖) := by field_simp

theorem hms_coreTr_eq (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : coreTr M β = hmsTr (coreProj β) M :=
  core_tr_eq_trace M β

theorem hms_tr_add_left (D D' M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    hmsTr (D + D') M = hmsTr D M + hmsTr D' M := by
  simp [hmsTr, Matrix.add_mul, Matrix.trace_add, mul_add]

theorem hms_tr_smul_left (c : ℂ) (D M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    hmsTr (c • D) M = c * hmsTr D M := by
  simp only [hmsTr, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]; ring

theorem hms_tr_sum_left {ι : Type*} (s : Finset ι) (D : ι → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    hmsTr (∑ i ∈ s, D i) M = ∑ i ∈ s, hmsTr (D i) M := by
  simp [hmsTr, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum]

/-- The entries of the block projections. -/
theorem hms_proj_apply (γ : Fin σ.blocks ⊕ Fin σ.ports) (x y : LayerSite W σ) :
    (coreProj γ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) x y =
      if x = y then (if coreBlk x = γ then 1 else 0) else 0 := by
  rcases γ with a | j <;> rcases x with ⟨k, α⟩ | ⟨k, α⟩ <;>
    simp [coreProj, meqPhysProj, meqPortProj, diagonal_apply, coreBlk]

/-- A block-constant diagonal is `Σ_γ f_γ P_γ`. -/
theorem hms_diag_eq_sum (f : Fin σ.blocks ⊕ Fin σ.ports → ℂ) :
    diagonal (fun x : LayerSite W σ => f (coreBlk x)) = ∑ γ, f γ • coreProj γ := by
  ext x y
  simp only [diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, hms_proj_apply, smul_eq_mul]
  split_ifs with h
  · simp
  · simp

/-- The shift coefficients `s_γ(τ) = Σ_δ w_γδ τ_δ`. -/
def hmsS (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) (γ : Fin σ.blocks ⊕ Fin σ.ports) : ℂ :=
  ∑ δ, wt γ δ * τ δ

/-- The block-constant self-energy `diag(s(τ))`. -/
def hmsD (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
  diagonal (fun x => hmsS wt τ (coreBlk x))

theorem hmsD_eq_sum (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) :
    (hmsD wt τ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) = ∑ γ, hmsS wt τ γ • coreProj γ :=
  hms_diag_eq_sum _

theorem hms_tr_D_mul (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) (D M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    hmsTr D (hmsD wt τ * M) = ∑ γ, hmsS wt τ γ * hmsTr (D * coreProj γ) M := by
  rw [hmsD_eq_sum]
  simp only [hmsTr, Finset.sum_mul, Matrix.trace_sum, Finset.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  exact Finset.sum_congr rfl fun γ _ => by ring

theorem hms_norm_S_le {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1) (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) (γ) :
    ‖hmsS wt τ γ‖ ≤ ∑ δ, ‖τ δ‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun δ _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hwt γ δ)

theorem hms_norm_D_le {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1) (τ : Fin σ.blocks ⊕ Fin σ.ports → ℂ) :
    ‖(hmsD wt τ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤
      (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) * ∑ δ, ‖τ δ‖ := by
  rw [hmsD_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ γ, ‖hmsS wt τ γ • (coreProj γ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖
      ≤ ∑ _γ : Fin σ.blocks ⊕ Fin σ.ports, ∑ δ, ‖τ δ‖ := Finset.sum_le_sum fun γ _ => by
        rw [norm_smul]
        exact (mul_le_mul (hms_norm_S_le hwt τ γ) (core_norm_proj_le γ) (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans (le_of_eq (mul_one _))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem hms_norm_proj_sum_le {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1) (γ : Fin σ.blocks ⊕ Fin σ.ports) :
    ‖∑ δ, wt γ δ • (coreProj δ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤
      (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ δ, ‖wt γ δ • (coreProj δ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖
      ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, (1 : ℝ) := Finset.sum_le_sum fun δ _ => by
        rw [norm_smul]
        exact (mul_le_mul (hwt γ δ) (core_norm_proj_le δ) (norm_nonneg _) zero_le_one).trans
          (le_of_eq (one_mul 1))
    _ = _ := by simp

end Traces

/-!
## 2. The linearization of the mean block traces
-/

section Linear

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : ℕ} {σ : LayerShape}

/-- Jensen: `‖∫ f‖² ≤ ∫ ‖f‖²`. -/
theorem hms_norm_integral_sq_le {f : Ω → ℂ} (hf : MemLp f 2 μ) :
    ‖∫ ω, f ω ∂μ‖ ^ 2 ≤ ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  have h1 : ‖∫ ω, f ω ∂μ‖ ≤ ∫ ω, ‖f ω‖ ∂μ := norm_integral_le_integral_norm _
  have hv := variance_nonneg (fun ω => ‖f ω‖) μ
  rw [variance_eq_sub hf.norm] at hv
  have e : (∫ ω, ((fun ω => ‖f ω‖) ^ 2) ω ∂μ) = ∫ ω, ‖f ω‖ ^ 2 ∂μ := rfl
  rw [e] at hv
  have h0 : 0 ≤ ‖∫ ω, f ω ∂μ‖ := norm_nonneg _
  nlinarith

/-- **The trace form of a Schwinger–Dyson identity.** If `C₀ E[G] - 1 = t E[D(ε(G)) G]` and
`R0 C₀ = 1`, then for every deterministic `D`:
`E[W⁻¹Tr(D G)] - W⁻¹Tr(D R0) = t E[Σ_γ s_γ(ε(G)) W⁻¹Tr(D R0 P_γ G)]`. -/
theorem hms_trace_identity {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGi : Integrable G μ)
    (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ) (a : ℂ)
    {C0 R0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hR0 : R0 * C0 = 1) (t : ℝ)
    (hDi : Integrable (fun ω => hmsD wt (fun γ => coreTr (G ω) γ - a) * G ω) μ)
    (hSD : C0 * ∫ ω, G ω ∂μ - 1 =
      (t : ℂ) • ∫ ω, hmsD wt (fun γ => coreTr (G ω) γ - a) * G ω ∂μ)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (∫ ω, hmsTr D (G ω) ∂μ) - hmsTr D R0 =
      (t : ℂ) * ∫ ω, ∑ γ, hmsS wt (fun δ => coreTr (G ω) δ - a) γ *
        hmsTr (D * R0 * coreProj γ) (G ω) ∂μ := by
  have h := congrArg (hmsTrCLM (D * R0)) hSD
  rw [map_sub, map_smul, ← (hmsTrCLM (D * R0)).integral_comp_comm hDi] at h
  simp only [hmsTrCLM_apply] at h
  have e1 : hmsTr (D * R0) (C0 * ∫ ω, G ω ∂μ) = ∫ ω, hmsTr D (G ω) ∂μ := by
    have : hmsTr (D * R0) (C0 * ∫ ω, G ω ∂μ) = hmsTr D (∫ ω, G ω ∂μ) := by
      simp only [hmsTr, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R0 C0, hR0, Matrix.one_mul]
    rw [this, ← hmsTrCLM_apply, ← (hmsTrCLM D).integral_comp_comm hGi]
    rfl
  have e2 : hmsTr (D * R0) 1 = hmsTr D R0 := by simp [hmsTr]
  rw [e1, e2, smul_eq_mul] at h
  rw [h]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun ω => hms_tr_D_mul _ _ _ _)

/-- Bounded measurable traces are in `L²`. -/
theorem hms_memLp_tr (hW : 0 < W) {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G μ) {K₀ : ℝ} (hGb : ∀ ω, ‖G ω‖ ≤ K₀)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    MemLp (fun ω => hmsTr D (G ω)) 2 μ :=
  MemLp.of_bound ((hms_continuous_tr D).comp_aestronglyMeasurable hGm) (4 * (‖D‖ * K₀))
    (ae_of_all _ fun ω => (hms_norm_tr_le hW D (G ω)).trans
      (by gcongr; exact hGb ω))

/-- The block trace errors in `L²`. -/
theorem hms_memLp_err (hW : 0 < W) {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G μ) {K₀ : ℝ} (hGb : ∀ ω, ‖G ω‖ ≤ K₀) (a : ℂ)
    (δ : Fin σ.blocks ⊕ Fin σ.ports) :
    MemLp (fun ω => coreTr (G ω) δ - a) 2 μ := by
  have e : (fun ω => coreTr (G ω) δ - a) = fun ω => hmsTr (coreProj δ) (G ω) - a :=
    funext fun ω => by rw [hms_coreTr_eq]
  rw [e]
  exact (hms_memLp_tr hW hGm hGb (coreProj δ)).sub (memLp_const a)

/-- **The linearization of the mean block traces** ("the same stable-branch
comparison as in the layer-contraction lemma"). Let `G` be a bounded random matrix on the layer sites
with the Schwinger–Dyson identity `C₀ E[G] - 1 = t E[D(ε(G)) G]` (`ε_γ(G) = g_γ - a`, block
weights `|w_γδ| ≤ 1`), `Π C₀ = 1`, `E‖G‖² ≤ M` and the trace fluctuations
`‖W⁻¹Tr(D G) - E‖₂ ≤ V ‖D‖`. Then the mean errors `ε̄ = E g - a` satisfy
`ε̄_β = (tr_β Π - a) + t Σ_γ Q_βγ s_γ(ε̄) + r_β`, `Q_βγ = tr_β(Π P_γ Π)`, with
`|r_β| ≤ K_r (e + V²)`, `e = E Σ_δ |g_δ - a|²`, `K_r = 2 n³ ‖Π‖² (M + 1) + n² ‖Π‖`
(`n` the number of blocks). -/
theorem hms_linear (hW : 0 < W) {G : Ω → Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hGm : AEStronglyMeasurable G μ) {K₀ : ℝ} (hGb : ∀ ω, ‖G ω‖ ≤ K₀)
    {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1) (a : ℂ)
    {C0 R0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ} (hR0 : R0 * C0 = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hSD : C0 * ∫ ω, G ω ∂μ - 1 =
      (t : ℂ) • ∫ ω, hmsD wt (fun γ => coreTr (G ω) γ - a) * G ω ∂μ)
    {M : ℝ} (hM : ∫ ω, ‖G ω‖ ^ 2 ∂μ ≤ M) {V : ℝ} (hV0 : 0 ≤ V)
    (hfl : ∀ D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      eLpNorm (fun ω => hmsTr D (G ω) - ∫ ω', hmsTr D (G ω') ∂μ) 2 μ ≤ ENNReal.ofReal (V * ‖D‖))
    (β : Fin σ.blocks ⊕ Fin σ.ports) :
    ‖(∫ ω, coreTr (G ω) β ∂μ - a) - (coreTr R0 β - a) -
        (t : ℂ) * ∑ γ, coreTr (R0 * coreProj γ * R0) β *
          hmsS wt (fun δ => ∫ ω, coreTr (G ω) δ ∂μ - a) γ‖ ≤
      (2 * (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) ^ 3 * ‖R0‖ ^ 2 * (M + 1) +
        (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) ^ 2 * ‖R0‖) *
        ((∫ ω, ∑ δ, ‖coreTr (G ω) δ - a‖ ^ 2 ∂μ) + V ^ 2) := by
  set nB : ℝ := (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) with hnB
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  set ε : Ω → Fin σ.blocks ⊕ Fin σ.ports → ℂ := fun ω δ => coreTr (G ω) δ - a with hε
  set εb : Fin σ.blocks ⊕ Fin σ.ports → ℂ := fun δ => ∫ ω, coreTr (G ω) δ ∂μ - a with hεb
  set e : ℝ := ∫ ω, ∑ δ, ‖coreTr (G ω) δ - a‖ ^ 2 ∂μ with he
  set S : Ω → ℝ := fun ω => ∑ δ, ‖ε ω δ‖ with hS
  set Sb : ℝ := ∑ δ, ‖εb δ‖ with hSb
  have hK₀ : 0 ≤ K₀ := by
    obtain ⟨ω⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    exact (norm_nonneg _).trans (hGb ω)
  have hGi : Integrable G μ := Integrable.of_bound hGm K₀ (ae_of_all _ hGb)
  have hεm : ∀ δ, MemLp (fun ω => ε ω δ) 2 μ := hms_memLp_err hW hGm hGb a
  have hεi : ∀ δ, Integrable (fun ω => ε ω δ) μ := fun δ => (hεm δ).integrable one_le_two
  have hτi : ∀ δ, Integrable (fun ω => coreTr (G ω) δ) μ := fun δ => by
    have e : (fun ω => coreTr (G ω) δ) = fun ω => hmsTr (coreProj δ) (G ω) :=
      funext fun ω => hms_coreTr_eq _ _
    rw [e]; exact (hms_memLp_tr hW hGm hGb _).integrable one_le_two
  have hεint : ∀ δ, ∫ ω, ε ω δ ∂μ = εb δ := fun δ => by
    simp only [hε, hεb]
    rw [integral_sub (hτi δ) (integrable_const a), integral_const, probReal_univ, one_smul]
  have hSm : AEStronglyMeasurable S μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun δ _ => (hεm δ).aestronglyMeasurable.norm
  have hεb_le : ∀ ω δ, ‖ε ω δ‖ ≤ K₀ + ‖a‖ := fun ω δ => by
    simp only [hε]
    exact (norm_sub_le _ _).trans (by gcongr; exact (core_norm_tr_le _ _).trans (hGb ω))
  -- integrability of the self-energy term
  have hDm : AEStronglyMeasurable (fun ω => hmsD wt (fun γ => coreTr (G ω) γ - a) * G ω) μ := by
    have hc : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
        hmsD wt (fun γ => coreTr M γ - a) * M) := by
      refine Continuous.mul ?_ continuous_id
      refine continuous_pi fun x => continuous_pi fun y => ?_
      simp only [hmsD, diagonal_apply]
      split_ifs
      · exact continuous_finsetSum _ fun δ _ => continuous_const.mul
          ((core_continuous_tr δ).sub continuous_const)
      · exact continuous_const
    exact hc.comp_aestronglyMeasurable hGm
  have hDi : Integrable (fun ω => hmsD wt (fun γ => coreTr (G ω) γ - a) * G ω) μ := by
    refine Integrable.of_bound hDm (nB * (nB * (K₀ + ‖a‖)) * K₀) (ae_of_all _ fun ω => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ((hms_norm_D_le hwt _).trans ?_) (hGb ω)
      (norm_nonneg _) (by positivity))
    gcongr
    calc ∑ δ, ‖coreTr (G ω) δ - a‖ ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, (K₀ + ‖a‖) :=
          Finset.sum_le_sum fun δ _ => hεb_le ω δ
      _ = nB * (K₀ + ‖a‖) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hid := hms_trace_identity hGi wt a hR0 t hDi hSD
  -- notation for the pieces
  set h : Fin σ.blocks ⊕ Fin σ.ports → Ω → ℂ := fun γ ω =>
    hmsTr (coreProj β * R0 * coreProj γ) (G ω) with hh
  set f : Fin σ.blocks ⊕ Fin σ.ports → Ω → ℂ := fun γ ω => hmsS wt (ε ω) γ with hf
  have hfm : ∀ γ, MemLp (f γ) 2 μ := fun γ => by
    simp only [hf, hmsS]
    exact memLp_finsetSum _ fun δ _ => (hεm δ).const_mul _
  have hhm : ∀ γ, MemLp (h γ) 2 μ := fun γ => hms_memLp_tr hW hGm hGb _
  have hfi : ∀ γ, Integrable (fun ω => f γ ω * h γ ω) μ := fun γ => (hfm γ).integrable_mul (hhm γ)
  have hfint : ∀ γ, ∫ ω, f γ ω ∂μ = hmsS wt εb γ := fun γ => by
    simp only [hf, hmsS]
    rw [integral_finsetSum _ fun δ _ => (hεi δ).const_mul _]
    exact Finset.sum_congr rfl fun δ _ => by rw [integral_const_mul, hεint]
  -- the main identity for `D = P_β`
  have h1 := hid (coreProj β)
  have hlhs : (∫ ω, hmsTr (coreProj β) (G ω) ∂μ) - hmsTr (coreProj β) R0 =
      (∫ ω, coreTr (G ω) β ∂μ - a) - (coreTr R0 β - a) := by
    simp only [← hms_coreTr_eq]; ring
  rw [hlhs] at h1
  rw [h1, integral_finsetSum _ fun γ _ => hfi γ]
  -- covariance bounds
  have hcov : ∀ γ, ‖(∫ ω, f γ ω * h γ ω ∂μ) - (∫ ω, f γ ω ∂μ) * ∫ ω, h γ ω ∂μ‖ ≤
      (V * nB) * (V * ‖R0‖) := by
    intro γ
    refine core_cov_le (hfm γ) (hhm γ) (by positivity) (by positivity) ?_ ?_
    · set Dγ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ := ∑ δ, wt γ δ • coreProj δ
      have hfD : ∀ ω, f γ ω = hmsTr Dγ (G ω) - ∑ δ, wt γ δ * a := fun ω => by
        simp only [hf, hmsS, hε, Dγ, hms_tr_sum_left, hms_tr_smul_left, ← hms_coreTr_eq,
          mul_sub, Finset.sum_sub_distrib]
      have hfD' : (fun ω => f γ ω - ∫ ω', f γ ω' ∂μ) =
          fun ω => hmsTr Dγ (G ω) - ∫ ω', hmsTr Dγ (G ω') ∂μ := by
        funext ω
        simp only [hfD]
        rw [integral_sub ((hms_memLp_tr hW hGm hGb Dγ).integrable one_le_two)
          (integrable_const _), integral_const, probReal_univ, one_smul]
        ring
      rw [hfD']
      refine (hfl Dγ).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hms_norm_proj_sum_le hwt γ) hV0
    · refine (hfl _).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hV0))
      calc ‖coreProj β * R0 * coreProj γ‖ ≤ ‖coreProj β * R0‖ * ‖coreProj γ‖ := norm_mul_le _ _
        _ ≤ (1 * ‖R0‖) * 1 := by
            gcongr
            · exact (norm_mul_le _ _).trans (by gcongr; exact core_norm_proj_le β)
            · exact core_norm_proj_le γ
        _ = ‖R0‖ := by ring
  -- bounded integrands
  have hSb_le : ∀ ω, S ω ≤ nB * (K₀ + ‖a‖) := fun ω => by
    calc S ω ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, (K₀ + ‖a‖) :=
          Finset.sum_le_sum fun δ _ => hεb_le ω δ
      _ = nB * (K₀ + ‖a‖) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hSGi : Integrable (fun ω => S ω * ‖G ω‖) μ :=
    Integrable.of_bound (hSm.mul hGm.norm) (nB * (K₀ + ‖a‖) * K₀) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (mul_nonneg (hS0 ω) (norm_nonneg _))]
      exact mul_le_mul (hSb_le ω) (hGb ω) (norm_nonneg _) (by positivity))
  have hG2i : Integrable (fun ω => ‖G ω‖ ^ 2) μ :=
    Integrable.of_bound (hGm.norm.pow 2) (K₀ ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hGb ω) 2)
  have hS2i : Integrable (fun ω => S ω ^ 2) μ :=
    Integrable.of_bound (hSm.pow 2) ((nB * (K₀ + ‖a‖)) ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hS0 ω) (hSb_le ω) 2)
  have hε2i : ∀ δ, Integrable (fun ω => ‖ε ω δ‖ ^ 2) μ := fun δ =>
    (hεm δ).integrable_norm_pow two_ne_zero
  -- the residual of the means of `h`
  have hres : ∀ γ, ‖(∫ ω, h γ ω ∂μ) - coreTr (R0 * coreProj γ * R0) β‖ ≤
      4 * nB * ‖R0‖ ^ 2 * ∫ ω, S ω * ‖G ω‖ ∂μ := by
    intro γ
    have hQ : coreTr (R0 * coreProj γ * R0) β = hmsTr (coreProj β * R0 * coreProj γ) R0 := by
      rw [hms_coreTr_eq]; simp only [hmsTr, Matrix.mul_assoc]
    rw [hQ, hid (coreProj β * R0 * coreProj γ), norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht0]
    refine (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ?_
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
      (hSGi.const_mul _) (ae_of_all _ fun ω => ?_)
    refine (norm_sum_le _ _).trans ?_
    have hPn : ∀ δ, ‖coreProj β * R0 * coreProj γ * R0 * coreProj δ‖ ≤ ‖R0‖ ^ 2 := fun δ => by
      have h1 := core_norm_proj_le (W := W) (σ := σ) β
      have h2 := core_norm_proj_le (W := W) (σ := σ) γ
      have h3 := core_norm_proj_le (W := W) (σ := σ) δ
      calc ‖coreProj β * R0 * coreProj γ * R0 * coreProj δ‖
          ≤ ‖coreProj β‖ * ‖R0‖ * ‖coreProj γ‖ * ‖R0‖ * ‖coreProj δ‖ := by
            refine (norm_mul_le _ _).trans ?_
            gcongr
            refine (norm_mul_le _ _).trans ?_
            gcongr
            refine (norm_mul_le _ _).trans ?_
            gcongr
            exact norm_mul_le _ _
        _ ≤ 1 * ‖R0‖ * 1 * ‖R0‖ * 1 := by gcongr
        _ = ‖R0‖ ^ 2 := by ring
    calc ∑ δ, ‖hmsS wt (fun δ => coreTr (G ω) δ - a) δ *
          hmsTr (coreProj β * R0 * coreProj γ * R0 * coreProj δ) (G ω)‖
        ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, S ω * (4 * (‖R0‖ ^ 2 * ‖G ω‖)) :=
          Finset.sum_le_sum fun δ _ => by
            rw [norm_mul]
            exact mul_le_mul (hms_norm_S_le hwt _ δ) ((hms_norm_tr_le hW _ _).trans
              (by gcongr; exact hPn δ)) (norm_nonneg _) (hS0 ω)
      _ = 4 * nB * ‖R0‖ ^ 2 * (S ω * ‖G ω‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- Jensen and Cauchy–Schwarz on the errors
  have he_eq : e = ∑ δ, ∫ ω, ‖ε ω δ‖ ^ 2 ∂μ := by
    rw [he, integral_finsetSum _ fun δ _ => hε2i δ]
  have hSb2 : Sb ^ 2 ≤ nB * e := by
    have h1 : Sb ^ 2 ≤ nB * ∑ δ, ‖εb δ‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun δ => ‖εb δ‖)
      simpa [hSb, hnB] using this
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hnB0)
    rw [he_eq]
    refine Finset.sum_le_sum fun δ _ => ?_
    rw [← hεint δ]
    exact hms_norm_integral_sq_le (hεm δ)
  have hS2 : ∫ ω, S ω ^ 2 ∂μ ≤ nB * e := by
    rw [he, ← integral_const_mul]
    refine integral_mono hS2i ((integrable_finsetSum _ fun δ _ => hε2i δ).const_mul _)
      fun ω => ?_
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun δ => ‖ε ω δ‖)
    simpa [hS, hnB] using this
  have hSbT : Sb * ∫ ω, S ω * ‖G ω‖ ∂μ ≤ (nB * e * M + nB * e) / 2 := by
    rw [← integral_const_mul]
    have hpt : ∀ ω, Sb * (S ω * ‖G ω‖) ≤ (Sb ^ 2 * ‖G ω‖ ^ 2 + S ω ^ 2) / 2 := fun ω => by
      nlinarith [sq_nonneg (Sb * ‖G ω‖ - S ω)]
    refine (integral_mono (hSGi.const_mul _) (((hG2i.const_mul (Sb ^ 2)).add hS2i).div_const 2)
      hpt).trans ?_
    rw [integral_div]
    simp only [Pi.add_apply]
    rw [integral_add (hG2i.const_mul _) hS2i, integral_const_mul]
    have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans hM
    have hSb0 : 0 ≤ Sb ^ 2 := sq_nonneg _
    have : Sb ^ 2 * ∫ ω, ‖G ω‖ ^ 2 ∂μ ≤ nB * e * M :=
      mul_le_mul hSb2 hM (integral_nonneg fun ω => sq_nonneg _) (by
        have : 0 ≤ e := integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
        positivity)
    linarith
  -- assembly
  have he0 : 0 ≤ e := integral_nonneg fun ω => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT0 : 0 ≤ ∫ ω, S ω * ‖G ω‖ ∂μ :=
    integral_nonneg fun ω => mul_nonneg (hS0 ω) (norm_nonneg _)
  have hM0 : 0 ≤ M := (integral_nonneg fun ω => sq_nonneg _).trans hM
  have hterm : ∀ γ, ‖(∫ ω, f γ ω * h γ ω ∂μ) - coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ‖ ≤
      V ^ 2 * nB * ‖R0‖ + Sb * (4 * nB * ‖R0‖ ^ 2 * ∫ ω, S ω * ‖G ω‖ ∂μ) := by
    intro γ
    have e1 : (∫ ω, f γ ω * h γ ω ∂μ) - coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ =
        ((∫ ω, f γ ω * h γ ω ∂μ) - (∫ ω, f γ ω ∂μ) * ∫ ω, h γ ω ∂μ) +
          hmsS wt εb γ * ((∫ ω, h γ ω ∂μ) - coreTr (R0 * coreProj γ * R0) β) := by
      rw [hfint]; ring
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ((hcov γ).trans (le_of_eq (by ring))) ?_)
    rw [norm_mul]
    exact mul_le_mul (hms_norm_S_le hwt εb γ) (hres γ) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hsum : ‖(t : ℂ) * ∑ γ, ∫ ω, f γ ω * h γ ω ∂μ -
      (t : ℂ) * ∑ γ, coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ‖ ≤
      nB * (V ^ 2 * nB * ‖R0‖ + Sb * (4 * nB * ‖R0‖ ^ 2 * ∫ ω, S ω * ‖G ω‖ ∂μ)) := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, ← Finset.sum_sub_distrib]
    refine (mul_le_of_le_one_left (norm_nonneg _) ht1).trans ((norm_sum_le _ _).trans ?_)
    calc ∑ γ, ‖(∫ ω, f γ ω * h γ ω ∂μ) - coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ‖
        ≤ ∑ _γ : Fin σ.blocks ⊕ Fin σ.ports,
            (V ^ 2 * nB * ‖R0‖ + Sb * (4 * nB * ‖R0‖ ^ 2 * ∫ ω, S ω * ‖G ω‖ ∂μ)) :=
          Finset.sum_le_sum fun γ _ => hterm γ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine hsum.trans ?_
  have hR2 : 0 ≤ ‖R0‖ ^ 2 := sq_nonneg _
  have key : nB * (Sb * (4 * nB * ‖R0‖ ^ 2 * ∫ ω, S ω * ‖G ω‖ ∂μ)) ≤
      2 * nB ^ 3 * ‖R0‖ ^ 2 * (M + 1) * e := by
    have := mul_le_mul_of_nonneg_left hSbT (by positivity : 0 ≤ 4 * nB ^ 2 * ‖R0‖ ^ 2)
    nlinarith
  have hV2 : 0 ≤ V ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hnB0 3) hR2) (add_nonneg hM0 zero_le_one),
    mul_nonneg (pow_nonneg hnB0 2) (norm_nonneg R0)]

end Linear

/-!
## 3. The Gaussian heat path
-/

section Path

variable {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
variable {W : ℕ} {σ : LayerShape}

theorem hmsD_sub (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (τ τ' : Fin σ.blocks ⊕ Fin σ.ports → ℂ) :
    (hmsD wt τ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) - hmsD wt τ' = hmsD wt (τ - τ') := by
  ext x y
  simp only [hmsD, hmsS, Matrix.sub_apply, diagonal_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  split_ifs <;> simp

/-- The regularity of the affine path at a coercive time. -/
theorem hms_path_reg {C0 C1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian) {t δ : ℝ} (hδ : 0 < δ) (hc : cplCoercive δ (C0 + t • C1)) :
    CoreReg (C0 + t • C1) (Real.sqrt t • Lin) := by
  intro κ hκ x
  have hcx : cplCoercive κ (corePsi (C0 + t • C1) (Real.sqrt t • Lin) κ x) := by
    intro w
    have e : corePsi (C0 + t • C1) (Real.sqrt t • Lin) κ x =
        (C0 + t • C1) + ((κ : ℂ) * Complex.I) • 1 + Real.sqrt t • Lin x := rfl
    rw [e, cpl_form_add, cpl_form_add, cpl_form_smul, cpl_form_herm (hL x), mul_zero, add_zero]
    have h1 := hc w
    have h2 := (cpl_coercive_scalar (w := (κ : ℂ) * Complex.I) (p := LayerSite W σ)) w
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one] at h2
    have := cpl_sq_nonneg w
    nlinarith
  exact ⟨cpl_coercive_isUnit hκ hcx, cht_norm_inv_le hκ hcx⟩

/-- **The Schwinger–Dyson identity along the path** (`core_limit_identity` at `C₀ + tC₁`,
`√t Λ`): with `S(G) = D(g(G))` and `C₁ = D(a)`, `C₀ E[G] - 1 = t E[D(g(G) - a) G]`. -/
theorem hms_path_sd {C0 C1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian)
    {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1)
    (hS : ∀ G, coreS v Lin G = hmsD wt (coreTr G)) {a : ℂ} (hC1 : C1 = hmsD wt (fun _ => a))
    {t δ : ℝ} (ht0 : 0 ≤ t) (hδ : 0 < δ) (hc : cplCoercive δ (C0 + t • C1)) :
    C0 * ∫ x, (chtPath C0 C1 Lin t x)⁻¹ ∂gaussianProduct v - 1 =
      (t : ℂ) • ∫ x, hmsD wt (fun γ => coreTr (chtPath C0 C1 Lin t x)⁻¹ γ - a) *
        (chtPath C0 C1 Lin t x)⁻¹ ∂gaussianProduct v := by
  set μ := gaussianProduct v
  have hreg := hms_path_reg hL hδ hc
  have hP : ∀ x, (C0 + t • C1) + (Real.sqrt t • Lin) x = chtPath C0 C1 Lin t x := fun x => rfl
  have hcP : ∀ x, cplCoercive δ (chtPath C0 C1 Lin t x) := cht_path_coercive hL hc
  have hinv : ∀ᵐ x ∂μ, IsUnit ((C0 + t • C1) + (Real.sqrt t • Lin) x).det :=
    ae_of_all _ fun x => (cpl_coercive_inv hδ (hcP x)).1
  have hPc : Continuous (fun x => chtPath C0 C1 Lin t x) := by unfold chtPath; fun_prop
  set G : (ι → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun x => (chtPath C0 C1 Lin t x)⁻¹
    with hG
  have hGm : Measurable G := measurable_matrix_inv.comp hPc.measurable
  have hGb : ∀ x, ‖G x‖ ≤ δ⁻¹ := fun x => (cpl_coercive_inv hδ (hcP x)).2
  have hG2 : Integrable (fun x => ‖((C0 + t • C1) + (Real.sqrt t • Lin) x)⁻¹‖ ^ 2) μ :=
    Integrable.of_bound (hGm.norm.pow_const 2).aestronglyMeasurable (δ⁻¹ ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2)
  have key := core_limit_identity v hreg hinv hG2
  simp only [hP] at key
  have hSt : ∀ M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      coreS v (Real.sqrt t • Lin) M = (t : ℂ) • hmsD wt (coreTr M) := fun M => by
    rw [cht_coreS_smul, Real.sq_sqrt ht0, hS, ← Complex.coe_smul]
  simp only [hSt] at key
  have hGi : Integrable G μ := Integrable.of_bound hGm.aestronglyMeasurable δ⁻¹ (ae_of_all _ hGb)
  -- integrability of `D(g(G)) G`
  have hcD : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      hmsD wt (coreTr M) * M) := by
    refine Continuous.mul ?_ continuous_id
    refine continuous_pi fun x => continuous_pi fun y => ?_
    simp only [hmsD, hmsS, diagonal_apply]
    split_ifs
    · exact continuous_finsetSum _ fun δ _ => continuous_const.mul (core_continuous_tr δ)
    · exact continuous_const
  set nB : ℝ := (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ)
  have hDi : Integrable (fun x => hmsD wt (coreTr (G x)) * G x) μ := by
    refine Integrable.of_bound (hcD.comp_aestronglyMeasurable hGm.aestronglyMeasurable)
      (nB * (nB * δ⁻¹) * δ⁻¹) (ae_of_all _ fun x => ?_)
    refine (norm_mul_le _ _).trans (mul_le_mul ((hms_norm_D_le hwt _).trans ?_) (hGb x)
      (norm_nonneg _) (by positivity))
    gcongr
    calc ∑ δ', ‖coreTr (G x) δ'‖ ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, δ⁻¹ :=
          Finset.sum_le_sum fun δ' _ => (core_norm_tr_le _ _).trans (hGb x)
      _ = nB * δ⁻¹ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hCi : ∫ x, hmsD wt (fun _ => a) * G x ∂μ = hmsD wt (fun _ => a) * ∫ x, G x ∂μ :=
    (ContinuousLinearMap.mul ℝ (Matrix (LayerSite W σ) (LayerSite W σ) ℂ) _).integral_comp_comm hGi
  have e1 : ∫ x, hmsD wt (fun γ => coreTr (G x) γ - a) * G x ∂μ =
      (∫ x, hmsD wt (coreTr (G x)) * G x ∂μ) - hmsD wt (fun _ => a) * ∫ x, G x ∂μ := by
    rw [← hCi, ← integral_sub hDi (hGi.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Matrix.sub_mul, hmsD_sub]
    rfl
  have e2 : ∫ x, ((t : ℂ) • hmsD wt (coreTr (G x))) * G x ∂μ =
      (t : ℂ) • ∫ x, hmsD wt (coreTr (G x)) * G x ∂μ := by
    simp only [Matrix.smul_mul]
    exact integral_smul _ _
  rw [e2, Matrix.add_mul, Matrix.smul_mul, ← Complex.coe_smul] at key
  have key' : C0 * ∫ x, G x ∂μ + (t : ℂ) • (C1 * ∫ x, G x ∂μ) -
      (t : ℂ) • ∫ x, hmsD wt (coreTr (G x)) * G x ∂μ = 1 := key
  have e3 : C1 * ∫ x, G x ∂μ = hmsD wt (fun _ => a) * ∫ x, G x ∂μ := by rw [hC1]
  rw [e3] at key'
  rw [e1, smul_sub, ← key']
  abel

/-- **Trace fluctuations along the path** (`core_fluctuation` at `p = 2`): with the gradient
constant `Cg`, the coordinate-trace bound `Γ` and `‖‖G‖‖₄ ≤ C_A`,
`‖W⁻¹Tr(D G) - E‖₂ ≤ (4√2 Cg Γ C_A² / W) ‖D‖`. -/
theorem hms_path_fl (hW : 0 < W) {C0 C1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian) {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 < δ)
    (hc : cplCoercive δ (C0 + t • C1)) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hgw : ∀ K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∑ i, (v i : ℝ) * ‖(K * Lin (Pi.single i 1)).trace‖ ^ 2 ≤ Γ ^ 2 * ‖K‖ ^ 2)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hmom : eLpNorm (fun x => ‖(chtPath C0 C1 Lin t x)⁻¹‖) 4 (gaussianProduct v) ≤
      ENNReal.ofReal CA)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    eLpNorm (fun x => hmsTr D (chtPath C0 C1 Lin t x)⁻¹ -
        ∫ y, hmsTr D (chtPath C0 C1 Lin t y)⁻¹ ∂gaussianProduct v) 2 (gaussianProduct v) ≤
      ENNReal.ofReal (4 * Real.sqrt 2 * Cg * Γ * CA ^ 2 / W * ‖D‖) := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hreg := hms_path_reg hL hδ hc
  have hgw' : ∀ K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∑ i, (v i : ℝ) * ‖(K * (Real.sqrt t • Lin) (Pi.single i 1)).trace‖ ^ 2 ≤ Γ ^ 2 * ‖K‖ ^ 2 := by
    intro K
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hgw K)
    rw [_root_.smul_apply, Matrix.mul_smul, Matrix.trace_smul, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht0]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) ht1) (v i).2
  have hcP : ∀ x, cplCoercive δ (chtPath C0 C1 Lin t x) := cht_path_coercive hL hc
  have hinv : ∀ᵐ x ∂gaussianProduct v, IsUnit ((C0 + t • C1) + (Real.sqrt t • Lin) x).det :=
    ae_of_all _ fun x => (cpl_coercive_inv hδ (hcP x)).1
  have hmom' : eLpNorm (fun x => ‖((C0 + t • C1) + (Real.sqrt t • Lin) x)⁻¹‖)
      (ENNReal.ofReal (2 * 2)) (gaussianProduct v) ≤ ENNReal.ofReal CA := by
    rw [show (2 : ℝ) * 2 = 4 by norm_num, ENNReal.ofReal_ofNat]; exact hmom
  have h := core_fluctuation v hCg hgr hreg hΓ hgw' (W : ℝ)⁻¹ D one_le_two hCA hinv hmom'
  rw [ENNReal.ofReal_ofNat] at h
  have hc' : ∀ M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      (((W : ℝ)⁻¹ : ℝ) : ℂ) * (D * M).trace = hmsTr D M := fun M => by
    rw [hmsTr]; push_cast; rfl
  simp only [hc'] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [abs_of_pos (inv_pos.mpr hW')]
  field_simp

/-- `∫ ‖f‖² ≤ A²` from `‖f‖₂ ≤ A`. -/
theorem hms_sq_int_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {E : Type*}
    [NormedAddCommGroup E] {f : Ω → E}
    (hf : MemLp f 2 μ) {A : ℝ} (hA : 0 ≤ A) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal A) :
    ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ A ^ 2 := by
  have e := hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
  simp only [ENNReal.toReal_ofNat] at e
  rw [e] at h
  have h1 := (ENNReal.ofReal_le_ofReal_iff hA).mp h
  have hI : 0 ≤ ∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun _ => by positivity
  have h2 : ∫ ω, ‖f ω‖ ^ (2 : ℝ) ∂μ ≤ A ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hI, show (2⁻¹ : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num,
      Real.rpow_one] at this
  simpa [Real.rpow_two] using h2

/-- The residual constant `K_r = 2 n³ ρ² (C_A² + 1) + n² ρ`. -/
def hmsKr (nB ρ CA : ℝ) : ℝ := 2 * nB ^ 3 * ρ ^ 2 * (CA ^ 2 + 1) + nB ^ 2 * ρ

/-- The fluctuation scale `V = 4√2 Cg Γ C_A² / W`. -/
def hmsV (Cg Γ CA : ℝ) (W : ℕ) : ℝ := 4 * Real.sqrt 2 * Cg * Γ * CA ^ 2 / W

/-- The quadratic constant `K₁ = 2n + 6n C_st² (1 + n² K_r²) + 1`. -/
def hmsK1 (nB Cst Kr : ℝ) : ℝ := 2 * nB + 6 * nB * Cst ^ 2 * (1 + nB ^ 2 * Kr ^ 2) + 1

/-- The mean-square error `e(t) = E Σ_β |g_β - a|²` along the path. -/
def hmsErr (C0 C1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (a : ℂ) (t : ℝ) : ℝ :=
  ∫ x, ∑ δ, ‖coreTr (chtPath C0 C1 Lin t x)⁻¹ δ - a‖ ^ 2 ∂gaussianProduct v

/-- The pathwise stability hypothesis: every approximate solution of the linearized mean
equations at time `t` with residual `r` is `C_st (d + Σ|r|)`-small. -/
def HmsStable (R0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ) (a : ℂ) (t d Cst : ℝ) :
    Prop :=
  ∀ εb r : Fin σ.blocks ⊕ Fin σ.ports → ℂ,
    (∀ β, εb β = (coreTr R0 β - a) +
      (t : ℂ) * ∑ γ, coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ + r β) →
    ∀ β, ‖εb β‖ ≤ Cst * (d + ∑ γ, ‖r γ‖)

/-- **The quadratic a-priori inequality at a fixed time**: under the
Schwinger–Dyson structure, the moment bound `C_A`, the fluctuation constants and the
deterministic stability `HmsStable`, `e(t) ≤ K₁ (d² + V²) + K₁ e(t)²` (`V ≤ 1`). -/
theorem hms_path_quad (hW : 0 < W) {C0 C1 R0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian)
    {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1)
    (hS : ∀ G, coreS v Lin G = hmsD wt (coreTr G)) {a : ℂ} (hC1 : C1 = hmsD wt (fun _ => a))
    (hR0 : R0 * C0 = 1) {ρ : ℝ} (hR0b : ‖R0‖ ≤ ρ)
    {t δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 < δ) (hc : cplCoercive δ (C0 + t • C1))
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hgw : ∀ K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∑ i, (v i : ℝ) * ‖(K * Lin (Pi.single i 1)).trace‖ ^ 2 ≤ Γ ^ 2 * ‖K‖ ^ 2)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hmom : eLpNorm (fun x => ‖(chtPath C0 C1 Lin t x)⁻¹‖) 4 (gaussianProduct v) ≤
      ENNReal.ofReal CA)
    {d Cst : ℝ} (hd : 0 ≤ d) (hCst : 0 ≤ Cst) (hstab : HmsStable R0 wt a t d Cst)
    (hV1 : hmsV Cg Γ CA W ≤ 1) :
    hmsErr v C0 C1 Lin a t ≤
      hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
          (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) *
        (d ^ 2 + hmsV Cg Γ CA W ^ 2) +
      hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
          (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) *
        hmsErr v C0 C1 Lin a t ^ 2 := by
  set μ := gaussianProduct v
  set nB : ℝ := (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ) with hnB
  have hnB0 : 0 ≤ nB := Nat.cast_nonneg _
  set V := hmsV Cg Γ CA W with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef, hmsV]; positivity
  set Kr := hmsKr nB ρ CA with hKr
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hR0b
  have hKr0 : 0 ≤ Kr := by rw [hKr, hmsKr]; positivity
  set G : (ι → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ := fun x => (chtPath C0 C1 Lin t x)⁻¹
    with hG
  have hcP : ∀ x, cplCoercive δ (chtPath C0 C1 Lin t x) := cht_path_coercive hL hc
  have hPc : Continuous (fun x => chtPath C0 C1 Lin t x) := by unfold chtPath; fun_prop
  have hGm : AEStronglyMeasurable G μ :=
    (measurable_matrix_inv.comp hPc.measurable).aestronglyMeasurable
  have hGb : ∀ x, ‖G x‖ ≤ δ⁻¹ := fun x => (cpl_coercive_inv hδ (hcP x)).2
  have hSD := hms_path_sd v hL hwt hS hC1 ht0 hδ hc
  have hM : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ CA ^ 2 := by
    have hm2 : MemLp (fun x => ‖G x‖) 2 μ :=
      MemLp.of_bound hGm.norm δ⁻¹ (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hGb x)
    have h2 : eLpNorm (fun x => ‖G x‖) 2 μ ≤ ENNReal.ofReal CA :=
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans hmom
    have := hms_sq_int_le hm2 hCA h2
    simpa using this
  have hfl := hms_path_fl v hW hL ht0 ht1 hδ hc hCg hgr hΓ hgw hCA hmom
  have hlin := hms_linear hW hGm hGb hwt a hR0 ht0 ht1 hSD hM hV0 hfl
  set e := hmsErr v C0 C1 Lin a t with he
  have he0 : 0 ≤ e := integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set εb : Fin σ.blocks ⊕ Fin σ.ports → ℂ := fun δ => ∫ x, coreTr (G x) δ ∂μ - a with hεb
  set r : Fin σ.blocks ⊕ Fin σ.ports → ℂ := fun β => εb β - (coreTr R0 β - a) -
    (t : ℂ) * ∑ γ, coreTr (R0 * coreProj γ * R0) β * hmsS wt εb γ with hr
  have hKr' : 2 * nB ^ 3 * ‖R0‖ ^ 2 * (CA ^ 2 + 1) + nB ^ 2 * ‖R0‖ ≤ Kr := by
    rw [hKr, hmsKr]
    have h1 : ‖R0‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR0b 2
    gcongr
  have hrb : ∀ β, ‖r β‖ ≤ Kr * (e + V ^ 2) := fun β =>
    (hlin β).trans (mul_le_mul_of_nonneg_right hKr' (by positivity))
  have hεb_le : ∀ β, ‖εb β‖ ≤ Cst * (d + nB * (Kr * (e + V ^ 2))) := by
    intro β
    have := hstab εb r (fun β => by simp only [hr]; ring) β
    refine this.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl d) ?_) hCst)
    calc ∑ γ, ‖r γ‖ ≤ ∑ _γ : Fin σ.blocks ⊕ Fin σ.ports, Kr * (e + V ^ 2) :=
          Finset.sum_le_sum fun γ _ => hrb γ
      _ = nB * (Kr * (e + V ^ 2)) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- `e ≤ 2 n V² + 2 Σ |ε̄|²`
  have hvar : ∀ δ', ∫ x, ‖coreTr (G x) δ' - ∫ y, coreTr (G y) δ' ∂μ‖ ^ 2 ∂μ ≤ V ^ 2 := by
    intro δ'
    have h1 := hfl (coreProj δ')
    have e1 : (fun x => hmsTr (coreProj δ') (G x) - ∫ y, hmsTr (coreProj δ') (G y) ∂μ) =
        fun x => coreTr (G x) δ' - ∫ y, coreTr (G y) δ' ∂μ := by
      funext x; simp only [← hms_coreTr_eq]
    rw [e1] at h1
    refine hms_sq_int_le (hms_memLp_err hW hGm hGb _ δ') hV0 (h1.trans
      (ENNReal.ofReal_le_ofReal ?_))
    exact mul_le_of_le_one_right hV0 (core_norm_proj_le δ')
  have hsplit : ∀ δ', ∫ x, ‖coreTr (G x) δ' - a‖ ^ 2 ∂μ ≤ 2 * V ^ 2 + 2 * ‖εb δ'‖ ^ 2 := by
    intro δ'
    set c := ∫ y, coreTr (G y) δ' ∂μ
    have hi1 : Integrable (fun x => ‖coreTr (G x) δ' - c‖ ^ 2) μ :=
      (hms_memLp_err hW hGm hGb c δ').integrable_norm_pow two_ne_zero
    have hpt : ∀ x, ‖coreTr (G x) δ' - a‖ ^ 2 ≤ 2 * ‖coreTr (G x) δ' - c‖ ^ 2 + 2 * ‖εb δ'‖ ^ 2 :=
      fun x => by
        have e : coreTr (G x) δ' - a = (coreTr (G x) δ' - c) + εb δ' := by simp only [hεb, c]; ring
        rw [e]
        have := norm_add_le (coreTr (G x) δ' - c) (εb δ')
        nlinarith [sq_nonneg (‖coreTr (G x) δ' - c‖ - ‖εb δ'‖), norm_nonneg (coreTr (G x) δ' - c),
          norm_nonneg (εb δ'), norm_nonneg (coreTr (G x) δ' - c + εb δ')]
    calc ∫ x, ‖coreTr (G x) δ' - a‖ ^ 2 ∂μ ≤ ∫ x, (2 * ‖coreTr (G x) δ' - c‖ ^ 2 +
          2 * ‖εb δ'‖ ^ 2) ∂μ :=
          integral_mono ((hms_memLp_err hW hGm hGb a δ').integrable_norm_pow two_ne_zero)
            ((hi1.const_mul 2).add (integrable_const _)) hpt
      _ = 2 * ∫ x, ‖coreTr (G x) δ' - c‖ ^ 2 ∂μ + 2 * ‖εb δ'‖ ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const, probReal_univ, one_smul]
      _ ≤ 2 * V ^ 2 + 2 * ‖εb δ'‖ ^ 2 := by linarith [hvar δ']
  have he_le : e ≤ 2 * nB * V ^ 2 + 2 * ∑ δ', ‖εb δ'‖ ^ 2 := by
    have e1 : e = ∑ δ', ∫ x, ‖coreTr (G x) δ' - a‖ ^ 2 ∂μ := by
      rw [he, hmsErr, integral_finsetSum _ fun δ' _ =>
        (hms_memLp_err hW hGm hGb a δ').integrable_norm_pow two_ne_zero]
    rw [e1]
    calc ∑ δ', ∫ x, ‖coreTr (G x) δ' - a‖ ^ 2 ∂μ ≤ ∑ δ', (2 * V ^ 2 + 2 * ‖εb δ'‖ ^ 2) :=
          Finset.sum_le_sum fun δ' _ => hsplit δ'
      _ = 2 * nB * V ^ 2 + 2 * ∑ δ', ‖εb δ'‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum]; ring
  set A := Cst * (d + nB * (Kr * (e + V ^ 2))) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsum : ∑ δ', ‖εb δ'‖ ^ 2 ≤ nB * A ^ 2 := by
    calc ∑ δ', ‖εb δ'‖ ^ 2 ≤ ∑ _δ' : Fin σ.blocks ⊕ Fin σ.ports, A ^ 2 :=
          Finset.sum_le_sum fun δ' _ => pow_le_pow_left₀ (norm_nonneg _) (hεb_le δ') 2
      _ = nB * A ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA2 : A ^ 2 ≤ 3 * Cst ^ 2 * (d ^ 2 + nB ^ 2 * Kr ^ 2 * e ^ 2 + nB ^ 2 * Kr ^ 2 * V ^ 2) := by
    have hV4 : V ^ 4 ≤ V ^ 2 := by nlinarith [sq_nonneg V, mul_le_mul hV1 hV1 hV0 zero_le_one]
    have h3 : (d + nB * Kr * e + nB * Kr * V ^ 2) ^ 2 ≤
        3 * (d ^ 2 + (nB * Kr * e) ^ 2 + (nB * Kr * V ^ 2) ^ 2) := by
      nlinarith [sq_nonneg (d - nB * Kr * e), sq_nonneg (d - nB * Kr * V ^ 2),
        sq_nonneg (nB * Kr * e - nB * Kr * V ^ 2)]
    have e2 : A = Cst * (d + nB * Kr * e + nB * Kr * V ^ 2) := by rw [hA]; ring
    rw [e2, mul_pow]
    have h4 : (nB * Kr * V ^ 2) ^ 2 ≤ nB ^ 2 * Kr ^ 2 * V ^ 2 := by
      have e4 : (nB * Kr * V ^ 2) ^ 2 = nB ^ 2 * Kr ^ 2 * V ^ 4 := by ring
      rw [e4]
      exact mul_le_mul_of_nonneg_left hV4 (by positivity)
    have h5 : (nB * Kr * e) ^ 2 = nB ^ 2 * Kr ^ 2 * e ^ 2 := by ring
    have hC2 : 0 ≤ Cst ^ 2 := sq_nonneg _
    calc Cst ^ 2 * (d + nB * Kr * e + nB * Kr * V ^ 2) ^ 2
        ≤ Cst ^ 2 * (3 * (d ^ 2 + (nB * Kr * e) ^ 2 + (nB * Kr * V ^ 2) ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 hC2
      _ ≤ Cst ^ 2 * (3 * (d ^ 2 + nB ^ 2 * Kr ^ 2 * e ^ 2 + nB ^ 2 * Kr ^ 2 * V ^ 2)) := by
          rw [h5]; gcongr
      _ = 3 * Cst ^ 2 * (d ^ 2 + nB ^ 2 * Kr ^ 2 * e ^ 2 + nB ^ 2 * Kr ^ 2 * V ^ 2) := by ring
  set X := nB ^ 2 * Kr ^ 2 with hX
  set P := nB * Cst ^ 2 with hP
  have hX0 : 0 ≤ X := by positivity
  have hP0 : 0 ≤ P := by positivity
  have h6 : e ≤ 2 * nB * V ^ 2 + 6 * P * (d ^ 2 + X * e ^ 2 + X * V ^ 2) := by
    have h7 : 2 * ∑ δ', ‖εb δ'‖ ^ 2 ≤ 2 * (nB * (3 * Cst ^ 2 * (d ^ 2 + X * e ^ 2 + X * V ^ 2))) :=
      mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hA2 hnB0)) zero_le_two
    have e7 : 2 * (nB * (3 * Cst ^ 2 * (d ^ 2 + X * e ^ 2 + X * V ^ 2))) =
        6 * P * (d ^ 2 + X * e ^ 2 + X * V ^ 2) := by rw [hP]; ring
    linarith
  have key : hmsK1 nB Cst Kr * (d ^ 2 + V ^ 2) + hmsK1 nB Cst Kr * e ^ 2 -
      (2 * nB * V ^ 2 + 6 * P * (d ^ 2 + X * e ^ 2 + X * V ^ 2)) =
      d ^ 2 * (2 * nB + 6 * P * X + 1) + V ^ 2 * (6 * P + 1) + e ^ 2 * (2 * nB + 6 * P + 1) := by
    rw [hmsK1, hP, hX]; ring
  have hpos : 0 ≤ d ^ 2 * (2 * nB + 6 * P * X + 1) + V ^ 2 * (6 * P + 1) +
      e ^ 2 * (2 * nB + 6 * P + 1) := by positivity
  linarith

/-- **Continuity of the mean-square error in `t`** on `[0, t₁]` under a uniform height `δ₁`
(dominated convergence with the bound `n (δ₁⁻¹ + |a|)²`). -/
theorem hms_err_continuousOn {C0 C1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian) (a : ℂ) {t₁ δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hco : ∀ t ∈ Set.Icc (0 : ℝ) t₁, cplCoercive δ₁ (C0 + t • C1)) :
    ContinuousOn (hmsErr v C0 C1 Lin a) (Set.Icc 0 t₁) := by
  set nB : ℝ := (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports) : ℝ)
  have hcP : ∀ t ∈ Set.Icc (0 : ℝ) t₁, ∀ x, cplCoercive δ₁ (chtPath C0 C1 Lin t x) :=
    fun t ht => cht_path_coercive hL (hco t ht)
  have hf : Continuous (fun M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ =>
      ∑ δ, ‖coreTr M δ - a‖ ^ 2) :=
    continuous_finsetSum _ fun δ _ => (((core_continuous_tr δ).sub continuous_const).norm).pow 2
  refine continuousOn_of_dominated (bound := fun _ => nB * (δ₁⁻¹ + ‖a‖) ^ 2) ?_ ?_
    (integrable_const _) ?_
  · intro t _
    have hPc : Continuous (fun x => chtPath C0 C1 Lin t x) := by unfold chtPath; fun_prop
    exact (hf.measurable.comp (measurable_matrix_inv.comp hPc.measurable)).aestronglyMeasurable
  · intro t ht
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    have hG := (cpl_coercive_inv hδ₁ (hcP t ht x)).2
    calc ∑ δ, ‖coreTr (chtPath C0 C1 Lin t x)⁻¹ δ - a‖ ^ 2
        ≤ ∑ _δ : Fin σ.blocks ⊕ Fin σ.ports, (δ₁⁻¹ + ‖a‖) ^ 2 := Finset.sum_le_sum fun δ _ =>
          pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
            (by gcongr; exact (core_norm_tr_le _ _).trans hG)) 2
      _ = nB * (δ₁⁻¹ + ‖a‖) ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · refine ae_of_all _ fun x => ?_
    refine hf.comp_continuousOn ?_
    intro t ht
    have hU : IsUnit (chtPath C0 C1 Lin t x) := cpl_coercive_isUnit hδ₁ (hcP t ht x)
    have hc := NormedRing.inverse_continuousAt hU.unit
    rw [IsUnit.unit_spec] at hc
    have e : (fun t => (chtPath C0 C1 Lin t x)⁻¹) = fun t => Ring.inverse (chtPath C0 C1 Lin t x) :=
      funext fun t => Matrix.nonsing_inv_eq_ringInverse _
    rw [e]
    exact ContinuousAt.comp_continuousWithinAt (g := Ring.inverse)
      (f := fun t => chtPath C0 C1 Lin t x) hc (cht_continuous_path x).continuousWithinAt

/-- **Continuity (bootstrap) step.** If `f(t) ≤ s + K f(t)²` on `[0, 1)`, `f` is continuous on
every `[0, t]`, `f(0) ≤ 2s` and `4Ks < 1`, then `f ≤ 2s` on `[0, 1)`. -/
theorem hms_boot {f : ℝ → ℝ} {s K : ℝ} (hK : 0 < K) (hs : 0 ≤ s) (hsmall : 4 * K * s < 1)
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) 1, f t ≤ s + K * f t ^ 2)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) 1, ContinuousOn f (Set.Icc 0 t)) (h0 : f 0 ≤ 2 * s) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, f t ≤ 2 * s := by
  have hA : ∀ u ∈ Set.Ico (0 : ℝ) 1, f u ≤ 1 / (2 * K) → f u ≤ 2 * s := by
    intro u hu h
    rcases le_or_gt (f u) 0 with h' | h'
    · linarith
    have h1 := hf u hu
    have h2 : K * f u ^ 2 ≤ f u / 2 := by
      have : K * f u ≤ 1 / 2 := by
        rw [le_div_iff₀ (by positivity)] at h
        nlinarith
      nlinarith
    linarith
  have hlt : 2 * s < 1 / (2 * K) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  intro t ht
  by_contra hcon
  rw [not_le] at hcon
  have hbig : 1 / (2 * K) < f t := by
    by_contra h'
    rw [not_lt] at h'
    exact absurd (hA t ht h') (not_le.mpr hcon)
  have hivt := intermediate_value_Icc ht.1 (hcont t ht)
  obtain ⟨u, hu, hfu⟩ := hivt ⟨by linarith, hbig.le⟩
  have hu' : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
  have := hA u hu' hfu.le
  linarith

theorem hmsK1_ge_one {nB Cst Kr : ℝ} (hnB : 0 ≤ nB) : 1 ≤ hmsK1 nB Cst Kr := by
  rw [hmsK1]
  have : 0 ≤ 6 * nB * Cst ^ 2 * (1 + nB ^ 2 * Kr ^ 2) := by positivity
  linarith

/-- **The mean-square trace bound along the path, generic form.** All hypotheses of
`hms_path_quad` uniformly in `t ∈ [0, 1)` (moments `C_A`, stability `C_st`), local uniform heights,
`Σ_β |tr_β Π - a|² ≤ 2d²` at `t = 0`, `V ≤ 1` and the smallness `4K₁²(d² + V²) < 1`. Then
`e(t) ≤ 2K₁(d² + V²)` for every `t ∈ [0, 1)`. -/
theorem hms_meanSquare_gen (hW : 0 < W) {C0 C1 R0 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    {Lin : (ι → ℝ) →L[ℝ] Matrix (LayerSite W σ) (LayerSite W σ) ℂ}
    (hL : ∀ x, (Lin x).IsHermitian)
    {wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ}
    (hwt : ∀ β γ, ‖wt β γ‖ ≤ 1)
    (hS : ∀ G, coreS v Lin G = hmsD wt (coreTr G)) {a : ℂ} (hC1 : C1 = hmsD wt (fun _ => a))
    (hR0 : R0 * C0 = 1) {ρ : ℝ} (hR0b : ‖R0‖ ≤ ρ)
    (hcoer : ∀ t₁ ∈ Set.Ico (0 : ℝ) 1, ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t₁, cplCoercive δ₁ (C0 + t • C1))
    {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {Γ : ℝ} (hΓ : 0 ≤ Γ)
    (hgw : ∀ K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ,
      ∑ i, (v i : ℝ) * ‖(K * Lin (Pi.single i 1)).trace‖ ^ 2 ≤ Γ ^ 2 * ‖K‖ ^ 2)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hmom : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      eLpNorm (fun x => ‖(chtPath C0 C1 Lin t x)⁻¹‖) 4 (gaussianProduct v) ≤ ENNReal.ofReal CA)
    {d Cst : ℝ} (hd : 0 ≤ d) (hCst : 0 ≤ Cst)
    (hstab : ∀ t ∈ Set.Ico (0 : ℝ) 1, HmsStable R0 wt a t d Cst)
    (h0 : ∑ δ, ‖coreTr R0 δ - a‖ ^ 2 ≤ 2 * d ^ 2) (hV1 : hmsV Cg Γ CA W ≤ 1)
    (hsmall : 4 * hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
        (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) *
      (hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
        (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) *
          (d ^ 2 + hmsV Cg Γ CA W ^ 2)) < 1) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, hmsErr v C0 C1 Lin a t ≤
      2 * (hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
        (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) *
          (d ^ 2 + hmsV Cg Γ CA W ^ 2)) := by
  set K1 := hmsK1 (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) Cst
    (hmsKr (Fintype.card (Fin σ.blocks ⊕ Fin σ.ports)) ρ CA) with hK1def
  have hK1 : 1 ≤ K1 := hmsK1_ge_one (Nat.cast_nonneg _)
  have hs0 : 0 ≤ K1 * (d ^ 2 + hmsV Cg Γ CA W ^ 2) := by positivity
  refine hms_boot (by linarith) hs0 hsmall ?_ ?_ ?_
  · intro t ht
    obtain ⟨δ₁, hδ₁, hco⟩ := hcoer t ht
    have := hms_path_quad v hW hL hwt hS hC1 hR0 hR0b ht.1 ht.2.le hδ₁ (hco t ⟨ht.1, le_rfl⟩)
      hCg hgr hΓ hgw hCA (hmom t ht) hd hCst (hstab t ht) hV1
    rw [← hK1def] at this
    linarith
  · intro t ht
    obtain ⟨δ₁, hδ₁, hco⟩ := hcoer t ht
    exact hms_err_continuousOn v hL a hδ₁ hco
  · have hP0 : ∀ x, chtPath C0 C1 Lin 0 x = C0 := fun x => by
      rw [chtPath, Real.sqrt_zero, zero_smul, zero_smul, add_zero, add_zero]
    have hinv : C0⁻¹ = R0 := Matrix.inv_eq_left_inv hR0
    have e0 : hmsErr v C0 C1 Lin a 0 = ∑ δ, ‖coreTr R0 δ - a‖ ^ 2 := by
      rw [hmsErr]
      simp only [hP0, hinv]
      rw [integral_const, probReal_univ, one_smul]
    rw [e0]
    have : 2 * d ^ 2 ≤ 2 * (K1 * (d ^ 2 + hmsV Cg Γ CA W ^ 2)) := by
      have h1 : d ^ 2 ≤ K1 * d ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hK1
      have h2 : 0 ≤ K1 * hmsV Cg Γ CA W ^ 2 := by positivity
      nlinarith
    linarith

end Path

/-!
## 4. The cores
-/

section Common

variable {W : ℕ} {σ : LayerShape}

/-- Uniform heights on `[0, t₁]` from heights at every `t ∈ [0, 1)` (the form is affine). -/
theorem hms_coer_unif {n : Type} [Fintype n] {C0 C1 : Matrix n n ℂ}
    (h : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ cplCoercive δ (C0 + t • C1)) :
    ∀ t₁ ∈ Set.Ico (0 : ℝ) 1, ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ t ∈ Set.Icc (0 : ℝ) t₁, cplCoercive δ₁ (C0 + t • C1) := by
  intro t₁ ht₁
  obtain ⟨δ₀, hδ₀, h0⟩ := h 0 ⟨le_rfl, one_pos⟩
  obtain ⟨δ', hδ', h1⟩ := h t₁ ht₁
  exact ⟨min δ₀ δ', lt_min hδ₀ hδ', fun t ht => cht_coercive_between h0 h1 ht.1 ht.2⟩

/-- Block traces of the block projections: `tr_β P_γ = [β = γ]`. -/
theorem hms_tr_proj (hW : 0 < W) (β γ : Fin σ.blocks ⊕ Fin σ.ports) :
    coreTr (coreProj γ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) β = if γ = β then 1 else 0 := by
  have e : (coreProj γ : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) =
      diagonal (fun x => (fun δ => if γ = δ then (1 : ℂ) else 0) (coreBlk x)) * 1 := by
    rw [Matrix.mul_one]
    ext x y
    rw [hms_proj_apply, diagonal_apply]
    split_ifs <;> simp_all [eq_comm]
  rw [e]
  exact (core_tr_diag_mul (fun δ => if γ = δ then (1 : ℂ) else 0) 1 β).trans
    (by rw [core_tr_one hW, mul_one])

/-- The weighted coordinate traces of a fresh layer: `Σᵢ vᵢ |Tr(K Λᵢ)|² ≤ 4² ‖K‖²`. -/
theorem hms_layer_weighted_le (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (K : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    ∑ i, (tflVar W b σ i : ℝ) * ‖(K * meqLc W b σ (Pi.single i 1)).trace‖ ^ 2 ≤ 4 ^ 2 * ‖K‖ ^ 2 := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  refine (tfl_weighted_trace_le W b σ K).trans ?_
  have h2 := tfl_hs_le K
  have h3 := tfl_card_layerSite_le W σ
  have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
    have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
    rw [this]; linarith
  calc (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * ∑ x, ∑ y, ‖K x y‖ ^ 2
      ≤ (4 / W) * (4 * W * ‖K‖ ^ 2) := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
    _ = 4 ^ 2 * ‖K‖ ^ 2 := by field_simp

end Common

section Cores

variable {W : ℕ}

theorem hms_coreW1_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β γ : Fin 1 ⊕ Fin 2) :
    ‖coreW1 b β γ‖ ≤ 1 :=
  (Finset.single_le_sum (f := fun γ => ‖coreW1 b β γ‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ γ)).trans (coreW1_rowsum hb0 hb1 β)

theorem hms_coreW2_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (β γ : Fin 2 ⊕ Fin 2) :
    ‖coreW2 b β γ‖ ≤ 1 :=
  (Finset.single_le_sum (f := fun γ => ‖coreW2 b β γ‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ γ)).trans (coreW2_rowsum hb0 hb1 β)

theorem hms_core1_S (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .oneBlockTwoPorts) (LayerSite W .oneBlockTwoPorts) ℂ) :
    coreS (tflVar W b .oneBlockTwoPorts) (meqLc W b .oneBlockTwoPorts) G =
      hmsD (coreW1 b) (coreTr G) := by
  change meqS W b .oneBlockTwoPorts G = _
  rw [meqS_eq hW, meq_coefA hW hb1, meq_coefB hW hb0, core_shift_one]
  rfl

theorem hms_core2_S (hW : 0 < W) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2)
    (G : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) :
    coreS (coreVar W b) (coreLin W b) G = hmsD (coreW2 b) (coreTr G) := by
  rw [coreS_eq hW hb0 hb1, core_shift_two]
  rfl

theorem hms_core1_C1 (b E : ℝ) :
    (chtC1 (W := W) .oneBlockTwoPorts 0 E b) = hmsD (coreW1 b) (fun _ => matchedA E) := by
  ext x y
  rcases x with ⟨i, α⟩ | ⟨i, α⟩ <;> rcases y with ⟨j, γ⟩ | ⟨j, γ⟩ <;>
    simp [chtC1, hmsD, hmsS, coreW1, coreBlk, diagonal_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two]
  all_goals (try split_ifs) <;> ring

theorem hms_core2_C1 (b E : ℝ) :
    (chtC1 (W := W) .separate 0 E b) = hmsD (coreW2 b) (fun _ => matchedA E) := by
  ext x y
  rcases x with ⟨i, α⟩ | ⟨i, α⟩ <;> rcases y with ⟨j, γ⟩ | ⟨j, γ⟩ <;>
    (try fin_cases i) <;> (try fin_cases j) <;>
    simp [chtC1, hmsD, hmsS, coreW2, coreBlk, diagonal_apply, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    (try split_ifs) <;> (try simp_all) <;> ring

theorem hms_tr_smul_right {σ : LayerShape} (c : ℂ) (M : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (β : Fin σ.blocks ⊕ Fin σ.ports) : coreTr (c • M) β = c * coreTr M β := by
  rw [hms_coreTr_eq, hms_coreTr_eq]
  simp only [hmsTr, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring

/-- The linearized equations of a core (`Π = a`): `ε̄_β = t a² s_β(ε̄) + r_β`. -/
theorem hms_core_eq (hW : 0 < W) {σ : LayerShape} (a : ℂ)
    (wt : Fin σ.blocks ⊕ Fin σ.ports → Fin σ.blocks ⊕ Fin σ.ports → ℂ) (t : ℝ)
    (εb r : Fin σ.blocks ⊕ Fin σ.ports → ℂ)
    (h : ∀ β, εb β = (coreTr (a • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) β - a) +
      (t : ℂ) * ∑ γ, coreTr ((a • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * coreProj γ *
        (a • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ))) β * hmsS wt εb γ + r β)
    (β : Fin σ.blocks ⊕ Fin σ.ports) :
    εb β = (t : ℂ) * (a ^ 2 * hmsS wt εb β) + r β := by
  rw [h β, hms_tr_smul_right, core_tr_one hW, mul_one, sub_self, zero_add]
  congr 2
  have e : ∀ γ, coreTr ((a • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * coreProj γ *
      (a • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ))) β = a ^ 2 * if γ = β then 1 else 0 := by
    intro γ
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      hms_tr_smul_right, hms_tr_proj hW, sq]
  simp only [e, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `‖t a² s + r‖ ≤ ‖s‖ + ‖r‖` for `|a| = 1`, `t ∈ [0, 1]`. -/
theorem hms_norm_ta2 {a s r : ℂ} (ha : ‖a‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(t : ℂ) * (a ^ 2 * s) + r‖ ≤ ‖s‖ + ‖r‖ := by
  refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
  rw [norm_mul, norm_mul, norm_pow, ha, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg ht0]
  exact mul_le_of_le_one_left (norm_nonneg _) ht1

/-- The stability constant of the one-block core. -/
def hmsCst1 (b : ℝ) : ℝ := (2 * b + 1) / (2 * b * (1 - b)) + 1

/-- **Stability of the one-block core** (`S₃`, `Π = a`): `|ε̄_β| ≤ C_st Σ|r|`. -/
theorem hms_core1_stable (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (ha : ‖matchedA E‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HmsStable (matchedA E • (1 : Matrix (LayerSite W .oneBlockTwoPorts)
      (LayerSite W .oneBlockTwoPorts) ℂ)) (coreW1 b) (matchedA E) t 0 (hmsCst1 b) := by
  intro εb r h β
  have heq := hms_core_eq hW (σ := .oneBlockTwoPorts) (matchedA E) (coreW1 b) t εb r h
  set R := ∑ γ, ‖r γ‖ with hR
  have hr : ∀ γ, ‖r γ‖ ≤ R := fun γ =>
    Finset.single_le_sum (f := fun γ => ‖r γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb' : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hc' : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set x := ‖εb (Sum.inl 0)‖
  have hy : ∀ j : Fin 2, ‖εb (Sum.inr j)‖ ≤ b * x + R := by
    intro j
    rw [heq (Sum.inr j)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add ?_ (hr _))
    simp only [hmsS, coreW1, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two, zero_mul,
      add_zero]
    rw [norm_mul, hb']
  have hx : x ≤ (1 - 2 * b) * x + (b * ‖εb (Sum.inr 0)‖ + b * ‖εb (Sum.inr 1)‖) + R := by
    change ‖εb (Sum.inl 0)‖ ≤ _
    rw [heq (Sum.inl 0)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add ?_ (hr _))
    simp only [hmsS, coreW1, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_two]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) ((norm_add_le _ _).trans
      (le_of_eq ?_)))
    · rw [norm_mul, hc']
    · rw [norm_mul, norm_mul, hb']
  have h0 := hy 0
  have h1 := hy 1
  have hx' : 2 * b * (1 - b) * x ≤ (2 * b + 1) * R := by nlinarith
  have hpos : 0 < 2 * b * (1 - b) := by have : 0 < 1 - b := by linarith
                                        positivity
  have hxR : x ≤ (2 * b + 1) / (2 * b * (1 - b)) * R := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; linarith
  have hq0 : 0 ≤ (2 * b + 1) / (2 * b * (1 - b)) := by positivity
  rw [zero_add, hmsCst1]
  rcases β with i | j
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    nlinarith
  · have h2 := hy j
    set q := (2 * b + 1) / (2 * b * (1 - b))
    have h3 : b * x ≤ q * R := (mul_le_mul_of_nonneg_left hxR hb0.le).trans (by
      have := mul_nonneg hq0 hR0
      nlinarith)
    linarith

/-- The stability constant of the two-block core. -/
def hmsCst2 (b : ℝ) : ℝ := 2 * (b + 1) / (b * (1 - b)) + 1

/-- **Stability of the two-block core** (`S₄`, `Π = a`): `|ε̄_β| ≤ C_st Σ|r|`. -/
theorem hms_core2_stable (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (ha : ‖matchedA E‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    HmsStable (matchedA E • (1 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ))
      (coreW2 b) (matchedA E) t 0 (hmsCst2 b) := by
  intro εb r h β
  have heq := hms_core_eq hW (σ := .separate) (matchedA E) (coreW2 b) t εb r h
  set R := ∑ γ, ‖r γ‖ with hR
  have hr : ∀ γ, ‖r γ‖ ≤ R := fun γ =>
    Finset.single_le_sum (f := fun γ => ‖r γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb' : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hc' : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set x0 := ‖εb (Sum.inl 0)‖
  set x1 := ‖εb (Sum.inl 1)‖
  have hy0 : ‖εb (Sum.inr 0)‖ ≤ b * x0 + R := by
    rw [heq (Sum.inr 0)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add (le_of_eq ?_) (hr _))
    simp [hmsS, coreW2, Fintype.sum_sum_type, x0, hb0.le]
  have hy1 : ‖εb (Sum.inr 1)‖ ≤ b * x1 + R := by
    rw [heq (Sum.inr 1)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add (le_of_eq ?_) (hr _))
    simp [hmsS, coreW2, Fintype.sum_sum_type, x1, hb0.le]
  have htri : ∀ p q u : ℂ, ‖((1 - 2 * b : ℝ) : ℂ) * p + (b : ℂ) * q + (b : ℂ) * u‖ ≤
      (1 - 2 * b) * ‖p‖ + b * ‖q‖ + b * ‖u‖ := fun p q u => by
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (le_of_eq ?_))
      (le_of_eq ?_))
    · rw [norm_mul, norm_mul, hc', hb']
    · rw [norm_mul, hb']
  have hx0 : x0 ≤ (1 - 2 * b) * x0 + b * x1 + b * ‖εb (Sum.inr 0)‖ + R := by
    change ‖εb (Sum.inl 0)‖ ≤ _
    rw [heq (Sum.inl 0)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add ?_ (hr _))
    have e : hmsS (coreW2 b) εb (Sum.inl 0) = ((1 - 2 * b : ℝ) : ℂ) * εb (Sum.inl 0) +
        (b : ℂ) * εb (Sum.inl 1) + (b : ℂ) * εb (Sum.inr 0) := by
      simp [hmsS, coreW2, Fintype.sum_sum_type, Fin.sum_univ_two]
    rw [e]; exact htri _ _ _
  have hx1 : x1 ≤ (1 - 2 * b) * x1 + b * x0 + b * ‖εb (Sum.inr 1)‖ + R := by
    change ‖εb (Sum.inl 1)‖ ≤ _
    rw [heq (Sum.inl 1)]
    refine (hms_norm_ta2 ha ht0 ht1).trans (add_le_add ?_ (hr _))
    have e : hmsS (coreW2 b) εb (Sum.inl 1) = ((1 - 2 * b : ℝ) : ℂ) * εb (Sum.inl 1) +
        (b : ℂ) * εb (Sum.inl 0) + (b : ℂ) * εb (Sum.inr 1) := by
      simp [hmsS, coreW2, Fintype.sum_sum_type, Fin.sum_univ_two]; ring
    rw [e]; exact htri _ _ _
  have hX : b * (1 - b) * (x0 + x1) ≤ 2 * (b + 1) * R := by nlinarith
  have hpos : 0 < b * (1 - b) := by have : 0 < 1 - b := by linarith
                                    positivity
  set q := 2 * (b + 1) / (b * (1 - b))
  have hq0 : 0 ≤ q := by positivity
  have hXR : x0 + x1 ≤ q * R := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; linarith
  have hx0' : 0 ≤ x0 := norm_nonneg _
  have hx1' : 0 ≤ x1 := norm_nonneg _
  have hqR := mul_nonneg hq0 hR0
  rw [zero_add, hmsCst2]
  rcases β with i | j
  · fin_cases i
    · change x0 ≤ _; nlinarith
    · change x1 ≤ _; nlinarith
  · fin_cases j
    · have : b * x0 ≤ q * R := by nlinarith
      change ‖εb (Sum.inr 0)‖ ≤ _; nlinarith
    · have : b * x1 ≤ q * R := by nlinarith
      change ‖εb (Sum.inr 1)‖ ≤ _; nlinarith

/-- `chtErr` in the block-trace notation. -/
theorem hms_chtErr_eq {σ : LayerShape} (E : ℝ) (G : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    chtErr σ E G = ∑ δ, ‖coreTr G δ - matchedA E‖ ^ 2 := by
  rw [chtErr, Fintype.sum_sum_type]; rfl

/-- The core reference inverse: `(a⁻¹)⁻¹ = a`, with `‖a‖ ≤ α₀⁻¹`-type bound from the heights. -/
theorem hms_core_R0 {σ : LayerShape} {E α₀ : ℝ} (hα₀ : 0 < α₀) (hE2 : |E| < 2)
    (ha1 : ‖matchedA E‖ = 1) (haim : (matchedA E).im ≤ -α₀) :
    (matchedA E • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * chtKC0 σ E = 1 ∧
      ‖matchedA E • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤ α₀⁻¹ := by
  have ha0 : matchedA E ≠ 0 := fun h => by rw [h, norm_zero] at ha1; exact zero_ne_one ha1
  have h1 : (matchedA E • (1 : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)) * chtKC0 σ E = 1 := by
    rw [chtKC0, smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ ha0, one_smul]
  refine ⟨h1, ?_⟩
  obtain ⟨hinv, -, hα, -⟩ := hms_a_facts hE2 ha1 haim
  have hco : cplCoercive α₀ (chtKC0 (W := W) σ E) :=
    cpl_coercive_mono (by rw [hinv]; exact hα) cpl_coercive_scalar
  rw [← Matrix.inv_eq_left_inv h1]
  exact (cpl_coercive_inv hα₀ hco).2

/-- **`ChtCoreMeanSquare`** (compensated-phase lemma, cores): the core trace errors along the
interpolation are `O_{L²}(W⁻¹)` uniformly in `t ∈ (0, 1)`. Law: `layerLaw W b .oneBlockTwoPorts`
(one-block core, heat matrix `chtCoreHeat1`) and `coreLaw2 W b` (two-block core with its internal
bond, `chtCoreHeat2`). Domain: `b ∈ (0, 1/2)`, `E ∈ bulkInterval κ`, `t ∈ (0, 1)`, `W ≥ W₀`.
Norm: complex modulus of the normalized block traces (`chtErr`). Quantifier order: `b, κ` first,
then `C, W₀`, then `W, E, t`; `E Σ_β |g_β - a|² ≤ C/W²`. Uniformity: in `W ≥ W₀`, `E`, `t`;
constants depend on `b, κ` and the constants of the two inputs only. No limits are taken. Inputs:
`ConditionalBlockGUECount` (inverse moments `hms_core1_moments`, `hms_core2_moments`) and
`GaussianLpGradient` (fluctuations). -/
theorem chtCoreMeanSquare_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : ChtCoreMeanSquare := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  constructor
  · intro b hb0 hb1 κ hκ
    obtain ⟨CA, W₁, hCA, hmom⟩ := hms_core1_moments hcount hb0 hb1 hκ
    obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
    set nB : ℝ := (Fintype.card (Fin LayerShape.oneBlockTwoPorts.blocks ⊕
      Fin LayerShape.oneBlockTwoPorts.ports) : ℝ)
    set K1 := hmsK1 nB (hmsCst1 b) (hmsKr nB α₀⁻¹ CA) with hK1def
    have hK1 : 1 ≤ K1 := hmsK1_ge_one (Nat.cast_nonneg _)
    set Kf := 4 * Real.sqrt 2 * Cg * 4 * CA ^ 2 with hKf
    have hKf0 : 0 ≤ Kf := by positivity
    refine ⟨2 * K1 * Kf ^ 2, max W₁ (⌈2 * K1 * Kf⌉₊ + 1), fun W hW hW₀ E hE t ht => ?_⟩
    obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have hWK : 2 * K1 * Kf < W := by
      have h1 := Nat.le_ceil (2 * K1 * Kf)
      have h2 : ((⌈2 * K1 * Kf⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
      push_cast at h2; linarith
    have hV : hmsV Cg 4 CA W = Kf / W := by rw [hmsV, hKf]
    have hVs : Kf / W * (2 * K1) < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hW']; linarith
    have hV1 : hmsV Cg 4 CA W ≤ 1 := by
      rw [hV]
      have : Kf / W * 1 ≤ Kf / W * (2 * K1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hKf0 hW'.le)
      linarith
    obtain ⟨hR0, hR0b⟩ := hms_core_R0 (W := W) (σ := .oneBlockTwoPorts) hα₀ hE2 ha1 haim
    have hsmall : 4 * K1 * (K1 * (0 ^ 2 + hmsV Cg 4 CA W ^ 2)) < 1 := by
      rw [hV]
      have h0 : 0 ≤ Kf / W := div_nonneg hKf0 hW'.le
      have : (Kf / W * (2 * K1)) ^ 2 < 1 := by
        have := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 2 * K1)
        nlinarith
      nlinarith
    have hCst0 : 0 ≤ hmsCst1 b := by
      have : 0 < 1 - b := by linarith
      rw [hmsCst1]; positivity
    have key := hms_meanSquare_gen (tflVar W b .oneBlockTwoPorts) (σ := .oneBlockTwoPorts) hW
      (cht_lin_isHermitian .oneBlockTwoPorts b) (hms_coreW1_le hb0.le hb1.le)
      (hms_core1_S hW hb0.le hb1.le) (hms_core1_C1 b E) hR0 hR0b
      (hms_coer_unif (cht_core_coercive hb0.le hb1 hE2)) hCg.le hgr (by norm_num : (0 : ℝ) ≤ 4)
      (hms_layer_weighted_le hW hb0 hb1) hCA.le (fun t ht => hmom W hW (le_max_left _ _ |>.trans hW₀)
        E hE t ht) le_rfl hCst0
      (fun t ht => hms_core1_stable hW hb0 hb1 ha1 ht.1 ht.2.le) ?_ hV1 hsmall t
      ⟨ht.1.le, ht.2⟩
    · -- transfer to the layer law
      have hlaw := tfl_layerLaw_eq_map W b .oneBlockTwoPorts
      have hΦ := tfl_measurable_embed W b .oneBlockTwoPorts
      have hm : Measurable (fun ω : LayerSample W .oneBlockTwoPorts =>
          chtErr .oneBlockTwoPorts E (chtCoreHeat1 b E t ω)⁻¹) := by
        refine (cht_continuous_err E).measurable.comp (measurable_matrix_inv.comp ?_)
        unfold chtCoreHeat1
        exact measurable_const.add ((continuous_const_smul (Real.sqrt t)).measurable.comp
          (cht_measurable_linS _))
      rw [hlaw, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
      have e : ∫ x, chtErr .oneBlockTwoPorts E (chtCoreHeat1 b E t (tflEmbed W b _ x))⁻¹
          ∂gaussianProduct (tflVar W b .oneBlockTwoPorts) =
          hmsErr (tflVar W b .oneBlockTwoPorts) (chtKC0 .oneBlockTwoPorts E)
            (chtC1 .oneBlockTwoPorts 0 E b) (meqLc W b .oneBlockTwoPorts) (matchedA E) t := by
        rw [hmsErr]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        rw [hms_chtErr_eq, chtCoreHeat1, chtPath, cht_linS_embed]
      rw [e]
      refine key.trans (le_of_eq ?_)
      rw [hV, ← hK1def]
      field_simp
      ring
    · have h1 : ∀ δ, coreTr (matchedA E • (1 : Matrix (LayerSite W .oneBlockTwoPorts)
          (LayerSite W .oneBlockTwoPorts) ℂ)) δ = matchedA E := fun δ => by
        rw [hms_tr_smul_right, core_tr_one hW, mul_one]
      simp [h1]
  · intro b hb0 hb1 κ hκ
    obtain ⟨CA, W₁, hCA, hmom⟩ := hms_core2_moments hcount hb0 hb1 hκ
    obtain ⟨α₀, hα₀, -, hbulk⟩ := cmp_bulk_setup hκ
    set nB : ℝ := (Fintype.card (Fin LayerShape.separate.blocks ⊕
      Fin LayerShape.separate.ports) : ℝ)
    set K1 := hmsK1 nB (hmsCst2 b) (hmsKr nB α₀⁻¹ CA) with hK1def
    have hK1 : 1 ≤ K1 := hmsK1_ge_one (Nat.cast_nonneg _)
    set Kf := 4 * Real.sqrt 2 * Cg * 5 * CA ^ 2 with hKf
    have hKf0 : 0 ≤ Kf := by positivity
    refine ⟨2 * K1 * Kf ^ 2, max W₁ (⌈2 * K1 * Kf⌉₊ + 1), fun W hW hW₀ E hE t ht => ?_⟩
    obtain ⟨hE2, ha1, haim⟩ := hbulk E hE
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW
    have hWK : 2 * K1 * Kf < W := by
      have h1 := Nat.le_ceil (2 * K1 * Kf)
      have h2 : ((⌈2 * K1 * Kf⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast (le_max_right _ _).trans hW₀
      push_cast at h2; linarith
    have hV : hmsV Cg 5 CA W = Kf / W := by rw [hmsV, hKf]
    have hVs : Kf / W * (2 * K1) < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hW']; linarith
    have hV1 : hmsV Cg 5 CA W ≤ 1 := by
      rw [hV]
      have : Kf / W * 1 ≤ Kf / W * (2 * K1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hKf0 hW'.le)
      linarith
    obtain ⟨hR0, hR0b⟩ := hms_core_R0 (W := W) (σ := .separate) hα₀ hE2 ha1 haim
    have hsmall : 4 * K1 * (K1 * (0 ^ 2 + hmsV Cg 5 CA W ^ 2)) < 1 := by
      rw [hV]
      have h0 : 0 ≤ Kf / W := div_nonneg hKf0 hW'.le
      have : (Kf / W * (2 * K1)) ^ 2 < 1 := by
        have := mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 2 * K1)
        nlinarith
      nlinarith
    have hCst0 : 0 ≤ hmsCst2 b := by
      have : 0 < 1 - b := by linarith
      rw [hmsCst2]; positivity
    have key := hms_meanSquare_gen (coreVar W b) (σ := .separate) hW
      (cht_coreLin_isHermitian b) (hms_coreW2_le hb0.le hb1.le)
      (hms_core2_S hW hb0.le hb1.le) (hms_core2_C1 b E) hR0 hR0b
      (hms_coer_unif (cht_core_coercive hb0.le hb1 hE2)) hCg.le hgr (by norm_num : (0 : ℝ) ≤ 5)
      (core_weighted_le hW hb0 hb1) hCA.le
      (fun t ht => hmom W hW (le_max_left _ _ |>.trans hW₀) E hE t ht) le_rfl hCst0
      (fun t ht => hms_core2_stable hW hb0 hb1 ha1 ht.1 ht.2.le) ?_ hV1 hsmall t
      ⟨ht.1.le, ht.2⟩
    · -- transfer to the law of the two-block core
      have hlaw : coreLaw2 W b = (gaussianProduct (coreVar W b)).map (coreEmbed W b) := by
        rw [coreLaw2, core_law_eq_map]
      have hΦ := core_measurable_embed W b
      have hm : Measurable (fun q : Matrix (Fin W) (Fin W) ℂ × LayerSample W .separate =>
          chtErr .separate E (chtCoreHeat2 b E t q)⁻¹) := by
        refine (cht_continuous_err E).measurable.comp (measurable_matrix_inv.comp ?_)
        unfold chtCoreHeat2
        exact measurable_const.add ((continuous_const_smul (Real.sqrt t)).measurable.comp
          (((cht_measurable_linS _).comp measurable_snd).add
            (cht_measurable_coreLb.comp measurable_fst)))
      rw [hlaw, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
      have e : ∫ x, chtErr .separate E (chtCoreHeat2 b E t (coreEmbed W b x))⁻¹
          ∂gaussianProduct (coreVar W b) =
          hmsErr (coreVar W b) (chtKC0 .separate E) (chtC1 .separate 0 E b) (coreLin W b)
            (matchedA E) t := by
        rw [hmsErr]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        have hM : chtCoreHeat2 b E t (coreEmbed W b x) =
            chtPath (chtKC0 .separate E) (chtC1 .separate 0 E b) (coreLin W b) t x := by
          rw [chtCoreHeat2, chtPath, coreLin_apply]
          rw [show chtLinS .separate (coreEmbed W b x).2 + coreLb (coreEmbed W b x).1 =
            coreLb (ginibreAssemble fun c => x (Sum.inl c)) +
              tflLin W b .separate (fun c => x (Sum.inr c)) from by
            rw [coreEmbed, cht_linS_embed, meqLc_apply, add_comm]]
        rw [hms_chtErr_eq, hM]
      rw [e]
      refine key.trans (le_of_eq ?_)
      rw [hV, ← hK1def]
      field_simp
      ring
    · have h1 : ∀ δ, coreTr (matchedA E • (1 : Matrix (LayerSite W .separate)
          (LayerSite W .separate) ℂ)) δ = matchedA E := fun δ => by
        rw [hms_tr_smul_right, core_tr_one hW, mul_one]
      simp [h1]

end Cores

end BlockBand.Layers
