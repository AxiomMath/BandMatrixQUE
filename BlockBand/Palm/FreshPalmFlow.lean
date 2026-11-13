module

public import BlockBand.Palm.FreshPalmShift
public import BlockBand.Palm.ScalarLocalization
public import BlockBand.Coarea.FreshPalmDensityLaw

/-!
# Flow representation of the fresh traceless law

Ingredients of the proof of the fresh Palm theorem that express the fresh traceless law through
the matrix flow.

* `integral_freshTracelessLaw_eq_flow`: `E_{A⁰}[Φ(A⁰)] = E_flow[Φ(tracelessPart(H_{c₀} - F))]`
  (via `map_flowMatrix_sub`).
* `flow_identification`, `ae_flow_identification`: on the Hermitian locus,
  `F + A⁰ = H_{c₀} - g I` with `g = (∑_k λ_k(c₀) - Re Tr F)/N` (`traceShift`), so the scalar Palm
  weight is `flowWeight` (a function of the terminal eigenvalues only, hence `𝓛`-measurable) and
  `palmOverlap = flowOverlap` (scalar-shift invariance of the selected eigenvector).
* `map_scalarPart_flow`: the scalar part `Re Tr(H_{c₀} - F)/N` has law exactly `N(0, c₀/N²)`
  (scalar split `scalarShiftLaw_fin_eq_gueMeasure`).
* `flowLaw_traceShift_tail`: `P(|g| ≥ δ) ≤ 2 exp(-δ²/(2c₀/N²))`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.FreshPalmAssembly

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Model.Construction
  BlockBand.Palm.MomentFlow BlockBand.Coarea.PoleExclusion BlockBand.Coarea.FreshPalm
open scoped ENNReal NNReal ComplexConjugate

variable {N : ℕ}

theorem measurable_flowIncrement (F : Matrix (Fin N) (Fin N) ℂ) (a σ : ℝ) :
    Measurable (fun ω : FlowSample N => flowMatrix F a ω σ - F) :=
  measurable_matrix_sub.comp ((measurable_flowMatrix F a σ).prodMk measurable_const)

theorem ae_isHermitian_flow {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a σ : ℝ}
    (ha : 0 ≤ a) (haσ : a ≤ σ) :
    ∀ᵐ ω ∂flowLaw N a, (flowMatrix F a ω σ - F).IsHermitian ∧ (flowMatrix F a ω σ).IsHermitian := by
  have h : ∀ᵐ G ∂((flowLaw N a).map (fun ω => flowMatrix F a ω σ - F)), G.IsHermitian := by
    rw [map_flowMatrix_sub F ha haσ]
    exact BlockBand.Coarea.GUELaw.ae_isHermitian_gueMeasure _
  filter_upwards [ae_of_ae_map (measurable_flowIncrement F a σ).aemeasurable h] with ω hω
  refine ⟨hω, ?_⟩
  have : flowMatrix F a ω σ = F + (flowMatrix F a ω σ - F) := by abel
  rw [this]
  exact hF.add hω

/-- Expectations over the traceless law are expectations over the matrix flow at
terminal variance `c₀`, for every start `0 ≤ a ≤ c₀`. -/
theorem integral_freshTracelessLaw_eq_flow (F : Matrix (Fin N) (Fin N) ℂ) {a c₀ : ℝ}
    (ha : 0 ≤ a) (hac : a ≤ c₀) {Φ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hΦ : Measurable Φ) :
    ∫ A0, Φ A0 ∂freshTracelessLaw N c₀ =
      ∫ ω, Φ (tracelessPart (flowMatrix F a ω c₀ - F)) ∂flowLaw N a := by
  unfold freshTracelessLaw
  rw [integral_map measurable_tracelessPart.aemeasurable hΦ.aestronglyMeasurable,
    ← map_flowMatrix_sub F ha hac]
  exact integral_map (measurable_flowIncrement F a c₀).aemeasurable
    (f := fun x => Φ (tracelessPart x)) (hΦ.comp measurable_tracelessPart).aestronglyMeasurable

/-- `g = (∑_k λ_k(c₀) - Re Tr F)/N`, a function of the terminal eigenvalues. -/
def traceShift (F : Matrix (Fin N) (Fin N) ℂ) (a c₀ : ℝ) (ω : FlowSample N) : ℝ :=
  ((∑ k, flowEigenvalue F a ω c₀ k) - F.trace.re) / N

/-- The scalar Palm weight written through the terminal eigenvalue path:
`φ_{√c₀/N}(E - (λ_ℓ(c₀) - g))`. -/
def flowWeight (F : Matrix (Fin N) (Fin N) ℂ) (a c₀ E : ℝ) (ℓ : Fin N) (ω : FlowSample N) : ℝ :=
  BlockBand.Palm.scalarWeight (Real.toNNReal c₀) N E
    (flowEigenvalue F a ω c₀ ℓ - traceShift F a c₀ ω)

/-- The scalar part `Re(Tr A / N)` of a matrix. -/
def scalarPart (G : Matrix (Fin N) (Fin N) ℂ) : ℝ := (((N : ℂ))⁻¹ * G.trace).re

theorem measurable_scalarPart : Measurable (scalarPart (N := N)) :=
  Complex.continuous_re.measurable.comp
    (measurable_const.mul (continuous_id.matrix_trace).measurable)

/-- Pointwise flow identification on the Hermitian locus: `F + A⁰ = H_{c₀} - g I`, the Palm
weight is `flowWeight` and `palmOverlap = flowOverlap`. -/
theorem flow_identification {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {a c₀ : ℝ} (E : ℝ) (q : Fin N → ℂ) (ℓ : Fin N) {ω : FlowSample N}
    (hA : (flowMatrix F a ω c₀ - F).IsHermitian) (hK : (flowMatrix F a ω c₀).IsHermitian) :
    palmWeight F c₀ E ℓ (tracelessPart (flowMatrix F a ω c₀ - F)) = flowWeight F a c₀ E ℓ ω ∧
      palmOverlap F q ℓ (tracelessPart (flowMatrix F a ω c₀ - F)) = flowOverlap F a q c₀ ℓ ω ∧
      scalarPart (flowMatrix F a ω c₀ - F) = traceShift F a c₀ ω := by
  set K := flowMatrix F a ω c₀ with hKdef
  set g := scalarPart (K - F) with hgdef
  have hsplit : F + tracelessPart (K - F) = K + ((-g : ℝ) : ℂ) • 1 := by
    rw [add_tracelessPart_eq F hA]
    change F + (K - F) - (g : ℂ) • 1 = _
    push_cast
    rw [neg_smul]
    abel
  have hg : g = traceShift F a c₀ ω := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [hgdef]
    unfold scalarPart traceShift
    rw [trace_sub, show ((N : ℂ))⁻¹ = (((N : ℝ))⁻¹ : ℝ) by push_cast; rfl, Complex.re_ofReal_mul,
      Complex.sub_re, re_trace_eq_sum_freshEigenvalue hK]
    simp only [flowEigenvalue, ← hKdef]
    field_simp
  refine ⟨?_, ?_, hg⟩
  · unfold palmWeight flowWeight
    rw [hsplit, freshEigenvalue_add_smul_one hK, ← hg]
    simp only [flowEigenvalue, ← hKdef]
    ring_nf
  · unfold palmOverlap flowOverlap
    rw [hsplit, freshEigenvector_add_smul_one hK]

theorem ae_flow_identification {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c₀ : ℝ} (ha : 0 ≤ a) (hac : a ≤ c₀) (E : ℝ) (q : Fin N → ℂ) (ℓ : Fin N) :
    ∀ᵐ ω ∂flowLaw N a,
      palmWeight F c₀ E ℓ (tracelessPart (flowMatrix F a ω c₀ - F)) = flowWeight F a c₀ E ℓ ω ∧
      palmOverlap F q ℓ (tracelessPart (flowMatrix F a ω c₀ - F)) = flowOverlap F a q c₀ ℓ ω ∧
      scalarPart (flowMatrix F a ω c₀ - F) = traceShift F a c₀ ω := by
  filter_upwards [ae_isHermitian_flow hF ha hac] with ω hω
  exact flow_identification hN E q ℓ hω.1 hω.2

/-- The scalar part of `GUE_N(c₀/N)` under the flow is exactly `N(0, c₀/N²)`. -/
theorem map_scalarPart_flow (F : Matrix (Fin N) (Fin N) ℂ) (hN : 0 < N) {a c₀ : ℝ}
    (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hac : a ≤ c₀) :
    (flowLaw N a).map (fun ω => scalarPart (flowMatrix F a ω c₀ - F)) =
      gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N) := by
  have hv : ((BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N : ℝ≥0) : ℝ) =
      ((Real.toNNReal (c₀ / N) : ℝ≥0) : ℝ) / N := by
    rw [BlockBand.Palm.coe_scalarVariance, Real.coe_toNNReal _ hc₀,
      Real.coe_toNNReal _ (div_nonneg hc₀ (Nat.cast_nonneg N))]
    ring
  rw [show (fun ω => scalarPart (flowMatrix F a ω c₀ - F)) =
      scalarPart ∘ (fun ω => flowMatrix F a ω c₀ - F) from rfl,
    ← Measure.map_map measurable_scalarPart (measurable_flowIncrement F a c₀),
    map_flowMatrix_sub F ha hac, ← scalarShiftLaw_fin_eq_gueMeasure hN _ _ hv]
  unfold scalarShiftLaw
  rw [Measure.map_map measurable_scalarPart measurable_scalarAdd]
  have hae : ∀ᵐ y ∂(((gueMeasure (Fin N) (Real.toNNReal (c₀ / N))).map tracelessPart).prod
      (gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N))),
      (scalarPart ∘ fun y : Matrix (Fin N) (Fin N) ℂ × ℝ => y.1 + (y.2 : ℂ) • 1) y = y.2 := by
    have h0 := ae_freshTracelessLaw (N := N) hN c₀
    unfold freshTracelessLaw at h0
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h0] with y hy
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Function.comp_apply, scalarPart, trace_add, hy.2, trace_smul, trace_one,
      Fintype.card_fin, smul_eq_mul, zero_add]
    rw [show ((N : ℂ))⁻¹ * (((y.2 : ℝ) : ℂ) * (N : ℂ)) = (y.2 : ℂ) by field_simp]
    simp
  rw [Measure.map_congr hae, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Gaussian tail of the scalar part**: `P(|g| ≥ δ) ≤ 2 exp(-δ²/(2 c₀/N²))`. -/
theorem flowLaw_traceShift_tail {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c₀ : ℝ} (hc₀ : 0 ≤ c₀) (ha : 0 ≤ a) (hac : a ≤ c₀) {δ : ℝ} (hδ : 0 ≤ δ) :
    (flowLaw N a).real {ω | δ ≤ |traceShift F a c₀ ω|} ≤
      2 * Real.exp (-δ ^ 2 / (2 * BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N)) := by
  have hset : {ω | δ ≤ |traceShift F a c₀ ω|} =ᵐ[flowLaw N a]
      (fun ω => scalarPart (flowMatrix F a ω c₀ - F)) ⁻¹' {x : ℝ | δ ≤ |x|} := by
    filter_upwards [ae_flow_identification hF hN ha hac 0 0 ⟨0, hN⟩] with ω hω
    change (δ ≤ |traceShift F a c₀ ω|) = (δ ≤ |scalarPart (flowMatrix F a ω c₀ - F)|)
    rw [hω.2.2]
  have hms : MeasurableSet {x : ℝ | δ ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  rw [measureReal_congr hset, show (fun ω => scalarPart (flowMatrix F a ω c₀ - F)) ⁻¹' {x : ℝ | δ ≤ |x|} =
      (scalarPart ∘ (fun ω => flowMatrix F a ω c₀ - F)) ⁻¹' {x : ℝ | δ ≤ |x|} from rfl,
    ← map_measureReal_apply
    (measurable_scalarPart.comp (measurable_flowIncrement F a c₀)) hms]
  have hmap : (flowLaw N a).map (scalarPart ∘ fun ω => flowMatrix F a ω c₀ - F) =
      gaussianReal 0 (BlockBand.Palm.scalarVariance (Real.toNNReal c₀) N) :=
    map_scalarPart_flow F hN hc₀ ha hac
  rw [hmap]
  exact BlockBand.Palm.scalarGaussian_abs_tail _ N hδ

end BlockBand.Palm.FreshPalmAssembly
