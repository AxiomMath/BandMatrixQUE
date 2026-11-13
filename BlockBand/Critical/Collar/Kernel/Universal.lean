module

public import BlockBand.Critical.Collar.Kernel.Dilation
public import BlockBand.Critical.Collar.Kernel.Radial
public import BlockBand.Layers.ScalarRecursion
public import BlockBand.Critical.WeightedDensity.Global

/-!
# The universal collar kernel bound `E_collar 𝒫(Ur) ⪯ C √W I`

The universal clauses of the collar kernel theorem, at zero height and every real shift `s`.

*Law.* `collarLaw W b`, `0 < b < 1/2`, `W ≥ 1`; the old response `X` is deterministic.
*Domain.* Every real `e` with `η = Im z_b > 0`, every real shift `s`, `ν = 0`; `Y = -Im X ≻ 0`
(strict) or `Y ⪰ 0` with the radial regulator `t < 1` (boundary). No norm bound on `X`.
*Constant.* `C = η⁻¹ C_{b,w}`, `w = conj(z_b + e + s)`, `C_{b,w} = collarRowConst b w`.
No hypothesis is used.

## Proof

1. `collar_poissonKernel_quad`: `q*𝒫(Ur)q = -η⁻¹ Im⟨ρ*q, 𝓡 ρ*q⟩`, `𝓡 = ℋ_X⁻¹` (a.s.: `D` is
   invertible, `ae_isUnit_det_middleBlock`).
2. `-Im⟨y, 𝓡 y⟩ = lim_{ε↓0} -Im⟨y, (ℋ_X + iε)⁻¹ y⟩` (`tendsto_inv_add_smul_I`), and for `ε > 0`
   the dilation identity `-Im⟨y, (ℋ_X + iε)⁻¹ y⟩ = E_t Im⟨y, (ℋ_{X_h + tY} - iε)⁻¹ y⟩`
   (`neg_im_collarResolvent_eq_integral`).
3. Fatou in `ε`, Tonelli in `(t, ω)`, and the fresh-row bound
   `E_collar Im⟨ρ*q, (ℋ_{X'} - iε)⁻¹ ρ*q⟩ ≤ C_{b,w} √W ‖q‖²` for every Hermitian `X'`
   (`Density.lintegral_im_resolvent_collarRow_le_sqrt`).
4. Polarization gives integrability of the entries; the quadratic-form bound gives the Loewner bound.
5. Boundary clause: `E𝒫(tUr) = E𝒫(U r(X'))` with `-Im X' ≻ 0` (the radial Cayley inverse `radialOld`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.CoareaPalm (gueMeasure)
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open scoped ComplexOrder ENNReal NNReal

variable {W : ℕ}

/-!
## Almost-sure invertibility of the middle block
-/

/-- `G - E` is invertible `GUE`-a.s. on the port index (`t ≠ 0`). -/
theorem gueMeasure_port_det_null {t : ℝ≥0} (ht : t ≠ 0)
    (N : Matrix (PortSite W .common) (PortSite W .common) ℂ) :
    gueMeasure (PortSite W .common) t {G | (G + N).det = 0} = 0 := by
  set eqv : Fin 1 × Fin W ≃ Fin W := Equiv.uniqueProd (Fin W) (Fin 1)
  have hR : Measurable (Matrix.reindex eqv.symm eqv.symm :
      Matrix (Fin W) (Fin W) ℂ → Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hS : MeasurableSet {G : Matrix (PortSite W .common) (PortSite W .common) ℂ |
      (G + N).det = 0} :=
    measurableSet_eq_fun ((continuous_id.add continuous_const).matrix_det.measurable)
      measurable_const
  rw [← BlockBand.Coarea.GUELaw.gueMeasure_map_reindex eqv.symm t, Measure.map_apply hR hS]
  have hpi := measurePreserving_eval (fun _ : Fin 1 => gueMeasure (Fin W) t) 0
  have hS' : MeasurableSet ((Matrix.reindex eqv.symm eqv.symm) ⁻¹'
      {G : Matrix (PortSite W .common) (PortSite W .common) ℂ | (G + N).det = 0}) := hR hS
  rw [← hpi.measure_preimage hS'.nullMeasurableSet]
  have hset : (fun A : Fin 1 → Matrix (Fin W) (Fin W) ℂ => A 0) ⁻¹'
      ((Matrix.reindex eqv.symm eqv.symm) ⁻¹'
        {G : Matrix (PortSite W .common) (PortSite W .common) ℂ | (G + N).det = 0}) =
      {A | (Layers.blockDiag A + N).det = 0} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have : Matrix.reindex eqv.symm eqv.symm (A 0) = Layers.blockDiag A := by
      ext ⟨j, a⟩ ⟨j', c⟩
      have hj : j = 0 := Subsingleton.elim _ _
      have hj' : j' = 0 := Subsingleton.elim _ _
      subst hj hj'
      simp [Layers.blockDiag, eqv]
    rw [this]
  rw [hset]
  exact BlockBand.Layers.srec_pi_gue_det_null W 1 ht N

/-- **`D = G - (e + s)` is invertible `collarLaw`-a.s.** (`b < 1/2`). -/
theorem ae_isUnit_det_middleBlock {b : ℝ} (hb : b < 1 / 2) (e s : ℝ) :
    ∀ᵐ ω ∂Critical.collarLaw W b, IsUnit (middleBlock e s ω).det := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · exact Filter.Eventually.of_forall fun ω => by rw [Matrix.det_isEmpty]; exact isUnit_one
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : t ≠ 0 :=
    (Real.toNNReal_pos.2 (div_pos (by linarith) (by exact_mod_cast hW))).ne'
  have hG : ∀ᵐ G ∂gueMeasure (PortSite W .common) t,
      IsUnit (G - ((e + s : ℝ) : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).det := by
    rw [ae_iff]
    simp only [isUnit_iff_ne_zero, not_not, sub_eq_add_neg]
    exact gueMeasure_port_det_null ht _
  exact (Measure.quasiMeasurePreserving_snd (μ := layerLaw W b .common)
    (ν := gueMeasure (PortSite W .common) t)).ae hG

/-!
## Continuity of the inverse along `M + iε`
-/

theorem tendsto_inv_add_smul_I {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (hM : IsUnit M.det) {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => (M + ((u n : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹) atTop (𝓝 M⁻¹) := by
  set f : ℝ → Matrix ι ι ℂ := fun x => M + ((x : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = M := by simp [f]
  have hcont : ContinuousAt (fun x => (f x)⁻¹) 0 := by
    have hinv : (fun x => (f x)⁻¹) = fun x => (f x).det⁻¹ • (f x).adjugate := by
      funext x
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hinv]
    refine ContinuousAt.smul (f := fun x => (f x).det⁻¹) ?_ hf.matrix_adjugate.continuousAt
    refine ContinuousAt.inv₀ hf.matrix_det.continuousAt ?_
    rw [hf0]; exact hM.ne_zero
  have := hcont.tendsto.comp hu
  rw [hf0] at this
  exact this

/-!
## Measurability
-/

theorem measurable_ofReal_neg_im_form {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] {M : Ω → Matrix ι ι ℂ} {v : Ω → ι → ℂ} (hM : Measurable M)
    (hv : Measurable v) :
    Measurable fun ω => ENNReal.ofReal (-(star (v ω) ⬝ᵥ ((M ω)⁻¹ *ᵥ v ω)).im) := by
  have hinv := (BlockBand.Wegner.measurable_matrix_inv (n := ι)).comp hM
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℂ) => -(star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    (Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))).neg
  exact (hcont.measurable.comp (hinv.prodMk hv)).ennreal_ofReal

/-!
## The expected quadratic form
-/

/-- The coefficient `w = conj(z_b + e + s)` of the fresh row vector. -/
abbrev rowCoeff (b e s : ℝ) : ℂ := star (boundaryZ b e + ((e + s : ℝ) : ℂ))

/-- **Universal quadratic-form bound** (setting of the module): for `Y = -Im X ≻ 0` and every
deterministic `q`, `E_collar Re q*𝒫(Ur)q ≤ η⁻¹ C_{b,w} √W ‖q‖²` (lintegral form). -/
theorem lintegral_collarKernel_quad_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (e s : ℝ) (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosDef) (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s 0 ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b ≤
      ENNReal.ofReal ((boundaryZ b e).im⁻¹ *
        (collarRowConst b (rowCoeff b e s) * Real.sqrt W * ∑ x, ‖q x‖ ^ 2)) := by
  set η := (boundaryZ b e).im
  set e' := e + s
  set w := rowCoeff b e s
  set rv := collarRowVec w q
  set B := collarRowConst b w * Real.sqrt W * ∑ x, ‖q x‖ ^ 2
  set Y := -Critical.imPart X
  set Xh := rePart X
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : ∀ n, 0 < εn n := fun n => by positivity
  have hεt : Tendsto εn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set N : Critical.CollarSample W → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (-(star (rv ω) ⬝ᵥ ((collarMatrix e' X ω)⁻¹ *ᵥ rv ω)).im)
  set Nn : ℕ → Critical.CollarSample W → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (-(star (rv ω) ⬝ᵥ ((collarMatrix e' X ω +
      ((εn n : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv ω)).im)
  set G : ℕ → ℝ × Critical.CollarSample W → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal ((star (rv p.2) ⬝ᵥ ((collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 -
      ((εn n : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv p.2)).im)
  have hrv : Measurable rv := Density.measurable_collarRowVec w q
  have hMc := Density.measurable_collarMatrix e' X (W := W)
  have hNn : ∀ n, Measurable (Nn n) := fun n =>
    measurable_ofReal_neg_im_form (Measurable.of_eval_matrix _ fun i j =>
      ((Matrix.measurable_apply).comp hMc).add measurable_const) hrv
  have hG : ∀ n, Measurable (G n) := by
    intro n
    have hM : Measurable fun p : ℝ × Critical.CollarSample W =>
        collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((εn n : ℂ) * Complex.I) • 1 := by
      have heq : (fun p : ℝ × Critical.CollarSample W =>
          collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((εn n : ℂ) * Complex.I) • 1) =
          fun p => collarMatrix e' Xh p.2 - (p.1 : ℂ) • topLift Y -
            ((εn n : ℂ) * Complex.I) • 1 := by
        funext p; rw [collarMatrix_add_right, topLift_smul]
      rw [heq]
      refine Measurable.of_eval_matrix _ fun i j => ?_
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine (((Matrix.measurable_apply).comp ((Density.measurable_collarMatrix e' Xh).comp
        measurable_snd)).sub ?_).sub measurable_const
      exact (Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const
    exact Density.measurable_ofReal_im_form hM (hrv.comp measurable_snd)
  -- a.s. facts
  have hHerm := Density.ae_collarMatrix_isHermitian b e' (rePart_isHermitian X) (W := W)
  have hDinv := ae_isUnit_det_middleBlock hb e s (W := W)
  -- step 1: the kernel through the resolvent
  have h1 : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel
      (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) *ᵥ q)).re =
      ENNReal.ofReal η⁻¹ * N ω := by
    filter_upwards [hHerm, hDinv] with ω hω hD
    rw [collar_poissonKernel_quad b e s hη hω.2.1 hω.2.2 hD hY q,
      collarRow_conjTranspose_mulVec b e s hω.2.1 q, Complex.ofReal_re,
      ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]
  -- step 2: the limit `ε ↓ 0`
  have h2 : ∀ᵐ ω ∂Critical.collarLaw W b, N ω = liminf (fun n => Nn n ω) atTop := by
    filter_upwards [hHerm, hDinv] with ω hω hD
    have hH := isUnit_det_collarMatrix b e s hω.2.1 hω.2.2 hD hY
    have ht := tendsto_inv_add_smul_I _ hH hεt
    have hc : Continuous fun M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
        ENNReal.ofReal (-(star (rv ω) ⬝ᵥ (M *ᵥ rv ω)).im) :=
      ENNReal.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const))).neg
    exact ((hc.tendsto _).comp ht).liminf_eq.symm
  -- the bound at each `ε` (step 3)
  have h4 : ∀ n, ∫⁻ ω, Nn n ω ∂Critical.collarLaw W b ≤ ENNReal.ofReal B := by
    intro n
    have hpt : ∀ᵐ ω ∂Critical.collarLaw W b, Nn n ω = ∫⁻ t, G n (t, ω) ∂stdCauchy := by
      filter_upwards [hHerm] with ω hω
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2
        hY.posSemidef (hεn n) (rv ω)
      simp only [Nn, G]
      rw [← heq, ofReal_integral_eq_lintegral_ofReal hint]
      refine Filter.Eventually.of_forall fun t => ?_
      have hHt := collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)
      exact Density.im_dotProduct_inv_mulVec_nonneg' hHt (by simp [hεn n]) _
    have hsw : AEMeasurable (Function.uncurry fun (ω : Critical.CollarSample W) (t : ℝ) =>
        G n (t, ω)) ((Critical.collarLaw W b).prod stdCauchy) :=
      ((hG n).comp measurable_swap).aemeasurable
    rw [lintegral_congr_ae hpt, lintegral_lintegral_swap hsw]
    calc ∫⁻ t, ∫⁻ ω, G n (t, ω) ∂Critical.collarLaw W b ∂stdCauchy
        ≤ ∫⁻ _ : ℝ, ENNReal.ofReal B ∂stdCauchy := by
          refine lintegral_mono fun t => ?_
          exact Density.lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e'
            (dilatedOld_isHermitian X t) (by simp [hεn n]) w q
      _ = ENNReal.ofReal B := by simp
  -- assemble
  calc ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s 0 ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b
      = ENNReal.ofReal η⁻¹ * ∫⁻ ω, N ω ∂Critical.collarLaw W b := by
        rw [lintegral_congr_ae h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal η⁻¹ * ∫⁻ ω, liminf (fun n => Nn n ω) atTop ∂Critical.collarLaw W b := by
        rw [lintegral_congr_ae h2]
    _ ≤ ENNReal.ofReal η⁻¹ * liminf (fun n => ∫⁻ ω, Nn n ω ∂Critical.collarLaw W b) atTop := by
        gcongr
        exact lintegral_liminf_le hNn
    _ ≤ ENNReal.ofReal η⁻¹ * ENNReal.ofReal B := by
        gcongr
        exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall h4)
    _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]

/-!
## From quadratic-form bounds to entrywise integrability and a Loewner bound
-/

section Expect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]

omit [DecidableEq ι] in
/-- Polarization: `⟨u, M v⟩ = ¼ [Q(u+v) - Q(u-v) - i (Q(u+iv) - Q(u-iv))]`, `Q(x) = ⟨x, M x⟩`. -/
theorem dotProduct_polarization (M : Matrix ι ι ℂ) (u v : ι → ℂ) :
    star u ⬝ᵥ (M *ᵥ v) = (1 / 4 : ℂ) * ((star (u + v) ⬝ᵥ (M *ᵥ (u + v)) -
      star (u - v) ⬝ᵥ (M *ᵥ (u - v))) - Complex.I * (star (u + Complex.I • v) ⬝ᵥ
        (M *ᵥ (u + Complex.I • v)) - star (u - Complex.I • v) ⬝ᵥ (M *ᵥ (u - Complex.I • v)))) := by
  simp only [star_add, star_sub, star_smul, mulVec_add, mulVec_sub, mulVec_smul, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `⟨eᵢ, M eⱼ⟩ = Mᵢⱼ`. -/
theorem dotProduct_single_mulVec_single (M : Matrix ι ι ℂ) (i j : ι) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [dotProduct, mulVec, Pi.single_apply]

/-- **Quadratic-form bounds give an expected Loewner bound.** Law: a probability measure `μ`.
If `P` is measurable, `μ`-a.s. positive semidefinite, and `E Re q*Pq ≤ K ‖q‖²` for every
deterministic `q` (`K ≥ 0`), then every entry of `P` is integrable and `E P ⪯ K I`. -/
theorem integrable_and_posSemidef_of_quad_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {P : Ω → Matrix ι ι ℂ} (hP : Measurable P) (hpsd : ∀ᵐ ω ∂μ, (P ω).PosSemidef) {K : ℝ}
    (hK : 0 ≤ K)
    (hq : ∀ q : ι → ℂ, ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (P ω *ᵥ q)).re ∂μ ≤
      ENNReal.ofReal (K * ∑ a, ‖q a‖ ^ 2)) :
    (∀ i j, Integrable (fun ω => P ω i j) μ) ∧
      (((K : ℂ)) • (1 : Matrix ι ι ℂ) - BlockBand.Internal.Contracts.Layers.matrixExpect μ P).PosSemidef := by
  have hQm : ∀ q : ι → ℂ, Measurable fun ω => star q ⬝ᵥ (P ω *ᵥ q) := by
    intro q
    have hc : Continuous fun M : Matrix ι ι ℂ => star q ⬝ᵥ (M *ᵥ q) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact hc.measurable.comp hP
  have hreal : ∀ q : ι → ℂ, ∀ᵐ ω ∂μ, star q ⬝ᵥ (P ω *ᵥ q) =
      (((star q ⬝ᵥ (P ω *ᵥ q)).re : ℝ) : ℂ) := by
    intro q
    filter_upwards [hpsd] with ω hω
    have h0 := hω.dotProduct_mulVec_nonneg q
    rw [Complex.nonneg_iff] at h0
    exact Complex.ext rfl (by simp [← h0.2])
  have hnn : ∀ q : ι → ℂ, ∀ᵐ ω ∂μ, 0 ≤ (star q ⬝ᵥ (P ω *ᵥ q)).re := by
    intro q
    filter_upwards [hpsd] with ω hω
    exact (Complex.nonneg_iff.1 (hω.dotProduct_mulVec_nonneg q)).1
  have hQi : ∀ q : ι → ℂ, Integrable (fun ω => star q ⬝ᵥ (P ω *ᵥ q)) μ := by
    intro q
    have hre : Integrable (fun ω => (star q ⬝ᵥ (P ω *ᵥ q)).re) μ := by
      refine ⟨(Complex.measurable_re.comp (hQm q)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (hnn q)]
      exact (hq q).trans_lt ENNReal.ofReal_lt_top
    exact (hre.ofReal (𝕜 := ℂ)).congr (by filter_upwards [hreal q] with ω h using h.symm)
  have hent : ∀ i j, Integrable (fun ω => P ω i j) μ := by
    intro i j
    set u : ι → ℂ := Pi.single i 1
    set v : ι → ℂ := Pi.single j 1
    have h := (((hQi (u + v)).sub (hQi (u - v))).sub (((hQi (u + Complex.I • v)).sub
      (hQi (u - Complex.I • v))).const_mul Complex.I)).const_mul (1 / 4 : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    rw [← dotProduct_polarization, dotProduct_single_mulVec_single]
  refine ⟨hent, ?_⟩
  -- the quadratic form of the expectation
  have hEq : ∀ q : ι → ℂ, star q ⬝ᵥ (BlockBand.Internal.Contracts.Layers.matrixExpect μ P *ᵥ q) =
      ∫ ω, star q ⬝ᵥ (P ω *ᵥ q) ∂μ := by
    intro q
    simp only [dotProduct, mulVec, BlockBand.Internal.Contracts.Layers.matrixExpect,
      Matrix.of_apply]
    rw [integral_finsetSum _ fun i _ => ((integrable_finsetSum _ fun j _ =>
      (hent i j).mul_const (q j)).const_mul (star q i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hent i j).mul_const (q j)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  have hHerm : (BlockBand.Internal.Contracts.Layers.matrixExpect μ P).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, BlockBand.Internal.Contracts.Layers.matrixExpect,
      Matrix.of_apply]
    rw [Complex.star_def, ← integral_conj]
    refine integral_congr_ae ?_
    filter_upwards [hpsd] with ω hω
    exact hω.isHermitian.apply i j
  have hone : ((K : ℂ) • (1 : Matrix ι ι ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  refine BlockBand.Critical.WeightedDensity.posSemidef_of_quadForm_nonneg (hone.sub hHerm)
    fun q => ?_
  rw [BlockBand.Critical.WeightedDensity.quadForm_sub,
    BlockBand.Critical.WeightedDensity.quadForm_real_smul,
    BlockBand.Critical.WeightedDensity.quadForm_one]
  have hE : BlockBand.Internal.Contracts.CoareaPalm.quadForm
      (BlockBand.Internal.Contracts.Layers.matrixExpect μ P) q =
      ∫ ω, (star q ⬝ᵥ (P ω *ᵥ q)).re ∂μ := by
    rw [BlockBand.Internal.Contracts.CoareaPalm.quadForm, hEq]
    exact (integral_re (hQi q)).symm
  rw [hE, integral_eq_lintegral_of_nonneg_ae (hnn q)
    (Complex.measurable_re.comp (hQm q)).aestronglyMeasurable]
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) (hq q)
  linarith

end Expect

/-!
## Measurability of the collar kernel
-/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_matrix_mul' {l m n : Type*} [Fintype m] {f : Ω → Matrix l m ℂ}
    {g : Ω → Matrix m n ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x * g x := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.mul_apply]
  fun_prop

theorem measurable_matrix_add' {m n : Type*} {f g : Ω → Matrix m n ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => f x + g x := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.add_apply]
  fun_prop

theorem measurable_matrix_sub' {m n : Type*} {f g : Ω → Matrix m n ℂ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun x => f x - g x := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.sub_apply]
  fun_prop

theorem measurable_matrix_smul' {m n : Type*} (c : ℂ) {f : Ω → Matrix m n ℂ}
    (hf : Measurable f) : Measurable fun x => c • f x := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem measurable_matrix_conjTranspose' {m n : Type*} {f : Ω → Matrix m n ℂ}
    (hf : Measurable f) : Measurable fun x => (f x)ᴴ := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [conjTranspose_apply]
  exact Complex.continuous_conj.measurable.comp (by fun_prop)

theorem measurable_matrix_inv' {m : Type} [Fintype m] [DecidableEq m] {f : Ω → Matrix m m ℂ}
    (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  (BlockBand.Wegner.measurable_matrix_inv (n := m)).comp hf

theorem measurable_blockDiag_collar :
    Measurable fun ω : Critical.CollarSample W => Layers.blockDiag ω.1.1 := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [Layers.blockDiag]
  split_ifs
  · exact (Matrix.measurable_apply).comp ((measurable_pi_apply _).comp
      (measurable_fst.comp measurable_fst))
  · exact measurable_const

theorem measurable_bondMatrix_collar :
    Measurable fun ω : Critical.CollarSample W => bondMatrix .common ω.1.2 := by
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [bondMatrix]
  split_ifs
  · exact (Matrix.measurable_apply).comp ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      (measurable_snd.comp measurable_fst)))
  · exact measurable_const

theorem measurable_collarReaction (b e s ν : ℝ) :
    Measurable fun ω : Critical.CollarSample W => Critical.collarReaction b e s ν ω := by
  unfold Critical.collarReaction
  refine measurable_matrix_sub' (measurable_matrix_sub' measurable_blockDiag_collar
    measurable_const) (measurable_matrix_mul' (measurable_matrix_mul' measurable_bondMatrix_collar
      (measurable_matrix_inv' (measurable_matrix_sub' measurable_snd measurable_const)))
      (measurable_matrix_conjTranspose' measurable_bondMatrix_collar))

/-- `ω ↦ 𝒫(t U r)` is measurable (every `t, s, ν` and `X`). -/
theorem measurable_collarPoisson (b e s ν t : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : Critical.CollarSample W => Critical.poissonKernel ((t : ℂ) •
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X)) := by
  have hU : Measurable fun ω : Critical.CollarSample W => Critical.collarScattering b e s ν ω := by
    unfold Critical.collarScattering
    exact measurable_matrix_sub' measurable_const (measurable_matrix_smul' _
      (measurable_matrix_inv' (measurable_matrix_add' (measurable_collarReaction b e s ν)
        measurable_const)))
  have hV : Measurable fun ω : Critical.CollarSample W => (t : ℂ) •
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X) :=
    measurable_matrix_smul' _ (measurable_matrix_mul' hU measurable_const)
  unfold Critical.poissonKernel
  exact measurable_matrix_sub' (measurable_matrix_add' (measurable_matrix_inv'
    (measurable_matrix_sub' measurable_const hV)) (measurable_matrix_inv'
      (measurable_matrix_sub' measurable_const (measurable_matrix_conjTranspose' hV))))
    measurable_const

end Meas

/-!
## The universal bounds
-/

/-- `𝒫(Ur)` is positive semidefinite almost surely (`Y ≻ 0`, zero height). -/
theorem ae_collarPoisson_posSemidef {b : ℝ} (e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosDef) :
    ∀ᵐ ω ∂Critical.collarLaw W b, (Critical.poissonKernel
      (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X)).PosSemidef := by
  filter_upwards [Density.ae_collarMatrix_isHermitian b e (rePart_isHermitian X) (W := W)]
    with ω hω
  rw [collar_poissonKernel_eq_row b e s hη hω.2.1 hω.2.2 hY]
  exact (hY.posSemidef.mul_mul_conjTranspose_same _).smul
    (Complex.zero_le_real.2 (inv_nonneg.2 hη.le))

/-- **Universal collar kernel bound, strict clause** (from the global collar density bound
alone). Law `collarLaw W b`,
`0 < b < 1/2`, `W ≥ 1`, every real `e` with `η = Im z_b > 0`, every real shift `s`, zero height,
every `X` with `Y = -Im X ≻ 0` (no norm bound): the entries of `𝒫(Ur)` are integrable and
`E_collar 𝒫(Ur) ⪯ η⁻¹ C_{b,w} √W I`, `w = conj(z_b + e + s)`. -/
theorem collarKernel_universal_strict {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (e s : ℝ) (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosDef) :
    Critical.CollarKernelIntegrable b e s 0 1 X ∧
      ((((boundaryZ b e).im⁻¹ * collarRowConst b (rowCoeff b e s) * Real.sqrt W : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          Critical.expectedCollarKernel b e s 0 1 X).PosSemidef := by
  have hone : ∀ V : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, ((1 : ℝ) : ℂ) • V = V := by
    intro V; simp
  have hK : 0 ≤ (boundaryZ b e).im⁻¹ * collarRowConst b (rowCoeff b e s) * Real.sqrt W :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hη.le) (Density.collarRowConst_nonneg hb0.le _))
      (Real.sqrt_nonneg _)
  have h := integrable_and_posSemidef_of_quad_le (μ := Critical.collarLaw W b)
    (P := fun ω => Critical.poissonKernel
      (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X))
    (by simpa [hone] using measurable_collarPoisson b e s 0 1 X (W := W))
    (ae_collarPoisson_posSemidef e s hη hY) hK fun q => by
      refine (lintegral_collarKernel_quad_le hb0 hb hW e s hη hY q).trans (le_of_eq ?_)
      congr 1; ring
  refine ⟨fun x y => by simpa [hone] using h.1 x y, ?_⟩
  simpa [Critical.expectedCollarKernel, hone] using h.2

/-- **Universal collar kernel bound, radial (boundary) clause** (semidefinite `Y`, by radial
contraction). Setting of
`collarKernel_universal_strict`, but `Y = -Im X ⪰ 0`: for every radial regulator `0 ≤ t < 1`,
the entries of `𝒫(tUr)` are integrable and `E_collar 𝒫(tUr) ⪯ η⁻¹ C_{b,w} √W I` (the same
constant; no limit in `t` is needed for this clause). Proof: `E𝒫(tUr) = E𝒫(U r(X'))` with
`X' = z_b - 2iη(I - tr)⁻¹`, `-Im X' ≻ 0` (`radialOld`), then the strict clause at `X'`. -/
theorem collarKernel_universal_radial {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (e s : ℝ) (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosSemidef) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Critical.CollarKernelIntegrable b e s 0 t X ∧
      ((((boundaryZ b e).im⁻¹ * collarRowConst b (rowCoeff b e s) * Real.sqrt W : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          Critical.expectedCollarKernel b e s 0 t X).PosSemidef := by
  obtain ⟨h1, h2⟩ := collarKernel_universal_strict hb0 hb hW e s hη
    (posDef_neg_imPart_radialOld b e hη hY ht0 ht1)
  exact ⟨(collarKernelIntegrable_radial b e s 0 hη hY ht0 ht1).2 h1,
    by rw [expectedCollarKernel_radial b e s 0 hη hY ht0 ht1]; exact h2⟩

/-- Raising the scalar in a Loewner bound `M ⪯ K I`. -/
theorem posSemidef_smul_one_sub_mono {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    {K K' : ℝ} (h : (((K : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - M).PosSemidef) (hKK : K ≤ K') :
    (((K' : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - M).PosSemidef := by
  have hd : ((((K' - K : ℝ)) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    PosSemidef.one.smul (Complex.zero_le_real.2 (by linarith))
  have := hd.add h
  convert this using 1
  push_cast
  rw [sub_smul]
  abel

/-- **Universal clauses of the collar kernel bound with uniform constants** (zero height).
`b ∈ (0, 1/2)`, `κ > 0` and a shift range `s₀` first; then one constant `C ≥ 0`; uniformly in
`W ≥ 1`, `e ∈ bulkInterval κ`, `|s| ≤ s₀` and every old response `X` (no norm bound):
* `Y = -Im X ≻ 0`: entries of `𝒫(Ur)` integrable, `E_collar 𝒫(Ur) ⪯ C √W I`;
* `Y ⪰ 0`, every radial regulator `0 ≤ t < 1`: entries of `𝒫(tUr)` integrable,
  `E_collar 𝒫(tUr) ⪯ C √W I`.
`C = η_min⁻¹ C_{b, 5 + |s₀|}` with `η_min = (1-b)√(4-(2-κ)²)/2` (`|z_b| ≤ 3`, `|e| ≤ 2`). -/
theorem collarKernel_universal_uniform {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) (s₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        ((-Critical.imPart X).PosDef → Critical.CollarKernelIntegrable b e s 0 1 X ∧
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            Critical.expectedCollarKernel b e s 0 1 X).PosSemidef) ∧
        ((-Critical.imPart X).PosSemidef → ∀ t : ℝ, 0 ≤ t → t < 1 →
          Critical.CollarKernelIntegrable b e s 0 t X ∧
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            Critical.expectedCollarKernel b e s 0 t X).PosSemidef) := by
  set ηmin := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2
  set w' : ℂ := ((5 + |s₀| : ℝ) : ℂ)
  refine ⟨ηmin⁻¹ * collarRowConst b w', ?_, ?_⟩
  · by_cases hκ2 : κ ≤ 2
    · have hs : 0 ≤ ηmin := by
        have : 0 ≤ 1 - b := by linarith
        positivity
      exact mul_nonneg (inv_nonneg.2 hs) (Density.collarRowConst_nonneg hb0.le _)
    · -- empty bulk: any nonnegative constant; `ηmin` is still `≥ 0` since `√· ≥ 0`
      have : 0 ≤ ηmin := by
        have : 0 ≤ 1 - b := by linarith
        positivity
      exact mul_nonneg (inv_nonneg.2 this) (Density.collarRowConst_nonneg hb0.le _)
  intro W hW e he s hs X
  obtain ⟨hηmin, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
    (by linarith) hκ he
  have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hz3 := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) he2
  have hw : ‖rowCoeff b e s‖ ≤ ‖w'‖ := by
    have hs' : |s| ≤ |s₀| :=
      abs_le.2 ⟨by linarith [hs.1, le_abs_self s₀], by linarith [hs.2, le_abs_self s₀]⟩
    rw [rowCoeff, norm_star]
    calc ‖boundaryZ b e + ((e + s : ℝ) : ℂ)‖ ≤ ‖boundaryZ b e‖ + ‖((e + s : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 3 + (2 + |s₀|) := by
          gcongr
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (abs_add_le e s).trans (by linarith)
      _ = ‖w'‖ := by
          have h5 : (0 : ℝ) ≤ 5 + |s₀| := by positivity
          simp only [w']
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h5]; ring
  have hKK : (boundaryZ b e).im⁻¹ * collarRowConst b (rowCoeff b e s) * Real.sqrt W ≤
      ηmin⁻¹ * collarRowConst b w' * Real.sqrt W := by
    gcongr
    · exact Density.collarRowConst_nonneg hb0.le _
    · exact Density.collarRowConst_mono b hw
  refine ⟨fun hY => ?_, fun hY t ht0 ht1 => ?_⟩
  · obtain ⟨h1, h2⟩ := collarKernel_universal_strict hb0 hb hW e s hη hY
    exact ⟨h1, posSemidef_smul_one_sub_mono h2 hKK⟩
  · obtain ⟨h1, h2⟩ := collarKernel_universal_radial hb0 hb hW e s hη hY ht0 ht1
    exact ⟨h1, posSemidef_smul_one_sub_mono h2 hKK⟩

end BlockBand.Critical.Collar.Kernel
