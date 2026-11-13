module

public import BlockBand.Critical.MatrixClosing.Mean.Shift
public import BlockBand.Critical.Collar.Density.CondSchurCollarMeas
public import BlockBand.Layers.LayerMeanBounds

/-!
# Matrix closing, mean clause: the spectral identity of the middle-shifted density

*Law.* `collarLaw W b = layerLaw W b .common ⊗ GUE_W(c/W)` (middle block `G` on the port index),
`c = 1 - 2b`; deterministic Hermitian `X`, any `u`.

* `meanDensity W b e X u s = E_{A,B} (T*u)*Σ_F(s)(T*u)` (extended reals), `F`, `T` the
  `Collar.Density.collarFW`, `collarTW` at `(e, X)`.
* `spectralSum k e X u ω = Σ_ℓ k(λ_ℓ(Q))|(T*u)*u_ℓ(Q)|²`, `Q = portSchurFin e X ω = F + G`
  (`portSchurFin_eq`).
* **`lintegral_spectralSum_eq`**: `E_collar spectralSum k = ∫ k(s) meanDensity(s) ds` for every
  measurable `k ≥ 0` (eigenpair kernel identity `lintegral_sigmaKernel_eq` in `G`, then Tonelli).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Mean

open MeasureTheory Matrix ProbabilityTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.WeightedDensity
open BlockBand.Coarea.FreshPalm
open scoped ENNReal NNReal ComplexOrder

variable {W : ℕ}

attribute [local instance] Collar.Density.matrix_secondCountableTopology_gen

theorem measurable_freshEigenvector_fin {N : ℕ} (ℓ : Fin N) :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ => freshEigenvector K ℓ :=
  measurable_pi_iff.2 fun x =>
    BlockBand.Model.Construction.measurable_rawOrderedColumnSelection _ x

theorem measurable_collarFW (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : LayerSample W .common => Collar.Density.collarFW e X ω := by
  have h := (Collar.Density.measurable_collarFW_energy e X).comp
    (measurable_const.prodMk measurable_id : Measurable fun ω : LayerSample W .common =>
      ((0 : ℝ), ω))
  simpa [Function.comp_def] using h

theorem measurable_collarTW_conj (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) :
    Measurable fun ω : LayerSample W .common => (Collar.Density.collarTW e X ω)ᴴ *ᵥ u := by
  have h := (Collar.Density.measurable_collarTW_conj_mulVec e X u).comp
    (measurable_const.prodMk measurable_id : Measurable fun ω : LayerSample W .common =>
      ((0 : ℝ), ω))
  simpa [Function.comp_def] using h

/-- The middle-shifted conditional mean density
`ρ_u(s) = E_{A,B} u*TΣ_F(s)T*u` (extended reals; `F`, `T` at the unshifted `(e, X)`). -/
def meanDensity (W : ℕ) (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (quadForm (sigma (Collar.Density.collarFW e X ω) (1 - 2 * b) s)
    ((Collar.Density.collarTW e X ω)ᴴ *ᵥ u)) ∂layerLaw W b .common

/-- The spectral sum `Σ_ℓ k(λ_ℓ(Q)) |y*u_ℓ(Q)|²`, `y = T*u`, of the middle Schur complement `Q`. -/
def spectralSum (k : ℝ → ℝ) (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (u : Fin 2 × Fin W → ℂ) (ω : CollarSample W) : ℝ≥0∞ :=
  ∑ ℓ, ENNReal.ofReal (k (freshEigenvalue (portSchurFin e X ω) ℓ) *
    ‖star ((Collar.Density.collarTW e X ω.1)ᴴ *ᵥ u) ⬝ᵥ
      freshEigenvector (portSchurFin e X ω) ℓ‖ ^ 2)

theorem measurable_spectralSum {k : ℝ → ℝ} (hk : Measurable k) (e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (u : Fin 2 × Fin W → ℂ) :
    Measurable (spectralSum k e X u) := by
  have h1 : Measurable fun ω : CollarSample W => (Collar.Density.collarTW e X ω.1)ᴴ *ᵥ u :=
    (measurable_collarTW_conj e X u).comp measurable_fst
  have hterm : ∀ ℓ : Fin W, Measurable fun ω : CollarSample W =>
      ENNReal.ofReal (k (freshEigenvalue (portSchurFin e X ω) ℓ) *
        ‖star ((Collar.Density.collarTW e X ω.1)ᴴ *ᵥ u) ⬝ᵥ
          freshEigenvector (portSchurFin e X ω) ℓ‖ ^ 2) := by
    intro ℓ
    have h2 : Measurable fun ω : CollarSample W => freshEigenvector (portSchurFin e X ω) ℓ :=
      (measurable_freshEigenvector_fin ℓ).comp (measurable_portSchurFin e X)
    have h3 : Measurable fun ω : CollarSample W =>
        star ((Collar.Density.collarTW e X ω.1)ᴴ *ᵥ u) ⬝ᵥ
          freshEigenvector (portSchurFin e X ω) ℓ :=
by
      simp only [dotProduct, Pi.star_apply]
      exact Finset.measurable_sum _ fun i _ =>
        (Complex.continuous_conj.measurable.comp ((measurable_pi_apply i).comp h1)).mul
          ((measurable_pi_apply i).comp h2)
    have h4 : Measurable fun ω : CollarSample W => k (freshEigenvalue (portSchurFin e X ω) ℓ) :=
      hk.comp ((measurable_freshEigenvalue ℓ).comp (measurable_portSchurFin e X))
    exact ENNReal.measurable_ofReal.comp (h4.mul (h3.norm.pow_const 2))
  exact Finset.measurable_sum _ fun ℓ _ => hterm ℓ

theorem portSchurFin_eq (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω₁ : LayerSample W .common) (G : Matrix (PortSite W .common) (PortSite W .common) ℂ) :
    portSchurFin e X (ω₁, G) =
      Collar.Density.collarFW e X ω₁ + Matrix.reindex (portEquiv W) (portEquiv W) G := by
  have h : portSchur e X (ω₁, G) = G + Collar.Density.collarF e X ω₁ := by
    simp only [portSchur, Collar.Density.collarF, topBlock, Collar.Density.collarTopBlock]
    abel
  rw [portSchurFin, h, add_comm]
  rfl

theorem measurable_dotProduct_comp {α : Type*} [MeasurableSpace α] {N : ℕ}
    {y z : α → Fin N → ℂ} (hy : Measurable y) (hz : Measurable z) :
    Measurable fun a => star (y a) ⬝ᵥ z a := by
  simp only [dotProduct, Pi.star_apply]
  exact Finset.measurable_sum _ fun i _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply i).comp hy)).mul
      ((measurable_pi_apply i).comp hz)

/-- Joint measurability of `(a, s) ↦ y(a)*Σ_{F(a)}(s)y(a)` (extended reals). -/
theorem measurable_ofReal_quadForm_sigma {α : Type*} [MeasurableSpace α] {N : ℕ}
    {F : α → Matrix (Fin N) (Fin N) ℂ} (hF : Measurable F) {y : α → Fin N → ℂ}
    (hy : Measurable y) (c : ℝ) :
    Measurable fun p : α × ℝ => ENNReal.ofReal (quadForm (sigma (F p.1) c p.2) (y p.1)) := by
  simp_rw [ofReal_quadForm_sigma]
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  refine Measurable.lintegral_prod_right' (f := fun q : (α × ℝ) × Matrix (Fin N) (Fin N) ℂ =>
    ENNReal.ofReal (palmWeight (F q.1.1) c q.1.2 ℓ q.2 *
      ‖star (y q.1.1) ⬝ᵥ freshEigenvector (F q.1.1 + q.2) ℓ‖ ^ 2)) ?_
  have hK : Measurable fun q : (α × ℝ) × Matrix (Fin N) (Fin N) ℂ => F q.1.1 + q.2 :=
    (continuous_add.measurable).comp ((hF.comp (measurable_fst.comp measurable_fst)).prodMk
      measurable_snd)
  have hw : Measurable fun q : (α × ℝ) × Matrix (Fin N) (Fin N) ℂ =>
      palmWeight (F q.1.1) c q.1.2 ℓ q.2 := by
    unfold palmWeight BlockBand.Palm.scalarWeight
    exact (measurable_gaussianPDFReal _ _).comp ((measurable_snd.comp measurable_fst).sub
      ((measurable_freshEigenvalue ℓ).comp hK))
  have hd := measurable_dotProduct_comp (hy.comp (measurable_fst.comp measurable_fst))
    ((measurable_freshEigenvector_fin ℓ).comp hK)
  exact ENNReal.measurable_ofReal.comp (hw.mul (hd.norm.pow_const 2))

theorem measurable_reindex_port :
    Measurable (Matrix.reindex (portEquiv W) (portEquiv W) :
      Matrix (PortSite W .common) (PortSite W .common) ℂ → Matrix (Fin W) (Fin W) ℂ) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply

/-- The `G`-integral of the spectral sum for fixed end blocks and bonds (`A` Hermitian):
`E_G Σ_ℓ k(λ_ℓ(Q))|y*u_ℓ(Q)|² = ∫ k(s) y*Σ_F(s)y ds` (eigenpair kernel identity). -/
theorem lintegral_gue_spectralSum_eq (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (u : Fin 2 × Fin W → ℂ) {k : ℝ → ℝ} (hk : Measurable k) (hk0 : ∀ x, 0 ≤ k x)
    (ω₁ : LayerSample W .common) (hA : ∀ j, (ω₁.1 j).IsHermitian) :
    ∫⁻ G, spectralSum k e X u (ω₁, G)
        ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)) =
      ∫⁻ s, ENNReal.ofReal (k s) * ENNReal.ofReal (quadForm
        (sigma (Collar.Density.collarFW e X ω₁) (1 - 2 * b) s)
          ((Collar.Density.collarTW e X ω₁)ᴴ *ᵥ u)) := by
  have hc : 0 < 1 - 2 * b := by linarith
  set F := Collar.Density.collarFW e X ω₁
  have hF : F.IsHermitian := Collar.Density.collarFW_isHermitian e hX hA
  set y := (Collar.Density.collarTW e X ω₁)ᴴ *ᵥ u
  set Ψ : ℝ × (Fin W → ℂ) → ℝ≥0∞ := fun p => ENNReal.ofReal (k p.1 * ‖star y ⬝ᵥ p.2‖ ^ 2)
    with hΨdef
  have hΨ : Measurable Ψ := by
    have hd := measurable_dotProduct_comp (α := ℝ × (Fin W → ℂ)) (measurable_const (a := y))
      measurable_snd
    exact ENNReal.measurable_ofReal.comp ((hk.comp measurable_fst).mul (hd.norm.pow_const 2))
  have hK := lintegral_sigmaKernel_eq hW hF hc hΨ
  have hmG : Measurable fun G : Matrix (Fin W) (Fin W) ℂ =>
      ∑ ℓ, Ψ (freshEigenvalue (F + G) ℓ, freshEigenvector (F + G) ℓ) := by
    refine Finset.measurable_sum _ fun ℓ _ => hΨ.comp ?_
    have hadd : Measurable fun G : Matrix (Fin W) (Fin W) ℂ => F + G :=
      (continuous_const.add continuous_id).measurable
    exact ((measurable_freshEigenvalue ℓ).comp hadd).prodMk
      ((measurable_freshEigenvector_fin ℓ).comp hadd)
  have h1 : ∫⁻ G, spectralSum k e X u (ω₁, G)
      ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W)) =
      ∫⁻ G, ∑ ℓ, Ψ (freshEigenvalue (F + G) ℓ, freshEigenvector (F + G) ℓ)
        ∂freshGUE W (1 - 2 * b) := by
    rw [freshGUE, ← BlockBand.Coarea.GUELaw.gueMeasure_map_reindex (portEquiv W),
      lintegral_map hmG measurable_reindex_port]
    refine lintegral_congr fun G => ?_
    simp only [spectralSum, hΨdef]
    simp_rw [portSchurFin_eq e X ω₁ G]
    rfl
  rw [h1, ← hK]
  refine lintegral_congr fun s => ?_
  rw [ofReal_quadForm_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun A0 => ?_
  rw [← ENNReal.ofReal_mul (hk0 s), ← ENNReal.ofReal_mul (palmWeight_nonneg _ _ _ _ _)]
  congr 1
  ring

/-- **The spectral identity of the middle-shifted collar density.** For a measurable `k ≥ 0`,
`E_collar Σ_ℓ k(λ_ℓ(Q))|(T*u)*u_ℓ(Q)|² = ∫ k(s) ρ_u(s) ds`, `ρ_u = meanDensity`
(`G`-integral by the eigenpair kernel identity `lintegral_sigmaKernel_eq`, then Tonelli). -/
theorem lintegral_spectralSum_eq (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (u : Fin 2 × Fin W → ℂ) {k : ℝ → ℝ} (hk : Measurable k) (hk0 : ∀ x, 0 ≤ k x) :
    ∫⁻ ω, spectralSum k e X u ω ∂collarLaw W b =
      ∫⁻ s, ENNReal.ofReal (k s) * meanDensity W b e X u s := by
  have hP : IsProbabilityMeasure (layerLaw W b .common) := by unfold layerLaw; infer_instance
  have hmeas := measurable_spectralSum hk e X u
  have hy := measurable_collarTW_conj (W := W) e X u
  have hjoint := measurable_ofReal_quadForm_sigma (measurable_collarFW (W := W) e X) hy (1 - 2 * b)
  have hjoint' : Measurable fun p : LayerSample W .common × ℝ =>
      ENNReal.ofReal (k p.2) * ENNReal.ofReal (quadForm
        (sigma (Collar.Density.collarFW e X p.1) (1 - 2 * b) p.2)
          ((Collar.Density.collarTW e X p.1)ᴴ *ᵥ u)) :=
    (ENNReal.measurable_ofReal.comp (hk.comp measurable_snd)).mul hjoint
  have h1 : ∫⁻ ω, spectralSum k e X u ω ∂collarLaw W b =
      ∫⁻ ω₁, ∫⁻ G, spectralSum k e X u (ω₁, G)
        ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W))
        ∂layerLaw W b .common := by
    unfold collarLaw
    exact lintegral_prod _ hmeas.aemeasurable
  have h2 : ∫⁻ ω₁, ∫⁻ G, spectralSum k e X u (ω₁, G)
        ∂gueMeasure (PortSite W .common) (Real.toNNReal ((1 - 2 * b) / W))
        ∂layerLaw W b .common =
      ∫⁻ ω₁, (∫⁻ s, ENNReal.ofReal (k s) * ENNReal.ofReal (quadForm
        (sigma (Collar.Density.collarFW e X ω₁) (1 - 2 * b) s)
          ((Collar.Density.collarTW e X ω₁)ᴴ *ᵥ u))) ∂layerLaw W b .common :=
    lintegral_congr_ae ((BlockBand.Layers.lct_ae_blocks_isHermitian W b .common).mono
      fun ω₁ h => lintegral_gue_spectralSum_eq hW hb e hX u hk hk0 ω₁ h)
  have h3 := lintegral_lintegral_swap (μ := layerLaw W b .common) (ν := (volume : Measure ℝ))
    (f := fun (ω₁ : LayerSample W .common) (s : ℝ) => ENNReal.ofReal (k s) * ENNReal.ofReal
      (quadForm (sigma (Collar.Density.collarFW e X ω₁) (1 - 2 * b) s)
        ((Collar.Density.collarTW e X ω₁)ᴴ *ᵥ u))) hjoint'.aemeasurable
  rw [h1, h2, h3]
  refine lintegral_congr fun s => ?_
  have hs : Measurable fun ω₁ : LayerSample W .common => ENNReal.ofReal (quadForm
      (sigma (Collar.Density.collarFW e X ω₁) (1 - 2 * b) s)
        ((Collar.Density.collarTW e X ω₁)ᴴ *ᵥ u)) := by
    have := hjoint.comp (measurable_id.prodMk (measurable_const (a := s)))
    exact this
  rw [meanDensity]
  exact lintegral_const_mul _ hs

end BlockBand.Critical.MatrixClosing.Mean
