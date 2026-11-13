module

public import BlockBand.Critical.Collar.Density.CollarBlocks
public import BlockBand.Coarea.FreshPalmDensityLaw

/-!
# The common Gaussian scalar shift of the three collar diagonals

*Result* (`collarLaw_commonShift`). For `W ≥ 1`, `b < 1/2` there is a probability measure `μ'` on
collar samples with
`collarLaw W b = (μ' ⊗ N(0, t/(3W))).map (ω', θ) ↦ shiftSample θ ω'`, where `shiftSample θ` adds
`θ I` to the three diagonal blocks. Hence `ℋ_X(shiftSample θ ω') = ℋ_X(ω') + θ I`
(`collarMatrix_shiftSample`): the three-block collar matrix carries an independent Gaussian
common scalar shift of variance `c/(3W²)`.

*Proof.* Each diagonal block splits as traceless part plus an independent `N(0, t/W)` scalar
(adopted `scalarShiftLaw_fin_eq_gueMeasure`, reindexed). The three scalars `(ζ₁, ζ₂, ζ₃)` are
i.i.d. `N(0, v)`; their decomposition `ζ = (ζ - ζ̄ 1) + ζ̄ 1` with `ζ̄ ~ N(0, v/3)` independent of
the residual is read off the scalar split of `GUE_3(v)` restricted to its diagonal
(`pi_gaussian_eq_map_residual`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Coarea.GUELaw BlockBand.Coarea.PoleExclusion
  BlockBand.Coarea.FreshPalm
open CoareaNative.BlockBand (HermitianCoordinate)
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexConjugate

/-!
## Equality of measures from lintegrals
-/

theorem measure_eq_of_lintegral_eq {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    (h : ∀ F : α → ℝ≥0∞, Measurable F → ∫⁻ a, F a ∂μ = ∫⁻ a, F a ∂ν) : μ = ν := by
  ext s hs
  have := h (s.indicator 1) (measurable_one.indicator hs)
  rwa [lintegral_indicator_one hs, lintegral_indicator_one hs] at this

/-!
## Three i.i.d. Gaussians: mean and residual are independent
-/

/-- Real parts of the diagonal entries. -/
def diagRe {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : Fin d → ℝ := fun i => (M i i).re

/-- `ζ - ζ̄ 1`, `ζ̄ = d⁻¹ Σ ζ_j`. -/
def residual {d : ℕ} (ζ : Fin d → ℝ) : Fin d → ℝ := fun i => ζ i - (∑ j, ζ j) / d

theorem measurable_diagRe {d : ℕ} : Measurable (diagRe (d := d)) :=
  measurable_pi_iff.2 fun i => Complex.measurable_re.comp (Matrix.measurable_apply (i := i) (j := i))

theorem measurable_residual {d : ℕ} : Measurable (residual (d := d)) :=
  measurable_pi_iff.2 fun i => (measurable_pi_apply i).sub
    ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).div_const _)

theorem diagRe_tracelessPart {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) :
    diagRe (tracelessPart G) = residual (diagRe G) := by
  funext i
  simp only [diagRe, residual, tracelessPart, Matrix.sub_apply, Matrix.smul_apply, one_apply_eq,
    smul_eq_mul, mul_one, Complex.sub_re, Fintype.card_fin, Matrix.trace, Matrix.diag]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum]
  ring

theorem diagRe_add_smul_one {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (ζ : ℝ) :
    diagRe (G + (ζ : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) = diagRe G + fun _ => ζ := by
  funext i
  simp [diagRe]

/-- The diagonal of `GUE_d(t)` is i.i.d. `N(0, t)`. -/
theorem gueMeasure_map_diagRe (d : ℕ) (t : ℝ≥0) :
    (gueMeasure (Fin d) t).map diagRe = Measure.pi fun _ : Fin d => gaussianReal 0 t := by
  rw [gueMeasure_eq_map_hermitianMatrixOfCoordinates,
    Measure.map_map measurable_diagRe (measurable_hermitianMatrixOfCoordinates d)]
  have hf : diagRe ∘ CoareaNative.BlockBand.hermitianMatrixOfCoordinates =
      Prod.fst ∘ (MeasurableEquiv.sumPiEquivProdPi (fun _ : HermitianCoordinate d => ℝ)) := by
    funext x
    funext i
    simp [diagRe, CoareaNative.BlockBand.hermitianMatrixOfCoordinates,
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  unfold hermCoordGaussian
  rw [hf, ← Measure.map_map measurable_fst (MeasurableEquiv.measurable _),
    (measurePreserving_sumPiEquivProdPi (fun k : HermitianCoordinate d =>
      gaussianReal 0 (hermCoordVariance t k))).map_eq, Measure.map_fst_prod]
  simp only [measure_univ, one_smul]
  rfl

/-- **Three-Gaussian decomposition.** For i.i.d. `ζ_i ~ N(0, v)`, `i < 3`:
`Law(ζ) = Law(r + θ 1)`, `r ~ Law(ζ - ζ̄ 1)`, `θ ~ N(0, v/3)` independent. -/
theorem pi_gaussian_eq_map_residual (v : ℝ≥0) :
    Measure.pi (fun _ : Fin 3 => gaussianReal 0 v) =
      (((Measure.pi fun _ : Fin 3 => gaussianReal 0 v).map residual).prod
        (gaussianReal 0 (v / 3))).map (fun p => p.1 + fun _ => p.2) := by
  have hv : ((v / 3 : ℝ≥0) : ℝ) = (v : ℝ) / (3 : ℕ) := by push_cast; ring
  have hssl := scalarShiftLaw_fin_eq_gueMeasure (by norm_num : 0 < 3) v (v / 3) hv
  have hadd : Measurable fun p : (Fin 3 → ℝ) × ℝ => p.1 + fun _ => p.2 :=
    measurable_fst.add (measurable_pi_iff.2 fun _ => measurable_snd)
  have hfun : diagRe ∘ (fun y : Matrix (Fin 3) (Fin 3) ℂ × ℝ => y.1 + (y.2 : ℂ) • 1) =
      (fun p : (Fin 3 → ℝ) × ℝ => p.1 + fun _ => p.2) ∘ Prod.map diagRe id := by
    funext y
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
    exact diagRe_add_smul_one y.1 y.2
  have key : (gueMeasure (Fin 3) v).map diagRe =
      ((((gueMeasure (Fin 3) v).map diagRe).map residual).prod (gaussianReal 0 (v / 3))).map
        (fun p => p.1 + fun _ => p.2) := by
    conv_lhs => rw [← hssl, scalarShiftLaw, Measure.map_map measurable_diagRe measurable_scalarAdd,
      hfun, ← Measure.map_map hadd (measurable_diagRe.prodMap measurable_id),
      ← Measure.map_prod_map _ _ measurable_diagRe measurable_id, Measure.map_id,
      Measure.map_map measurable_diagRe measurable_tracelessPart]
    rw [Measure.map_map measurable_residual measurable_diagRe]
    congr 3
    funext G
    exact diagRe_tracelessPart G
  rw [gueMeasure_map_diagRe] at key
  exact key

/-!
## Scalar split of one GUE block on a general index type
-/

theorem measurable_add_smul_one {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    {f : α → Matrix ι ι ℂ} {g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a + (g a : ℂ) • (1 : Matrix ι ι ℂ) := by
  have := (measurable_scalarAdd (ι := ι)).comp (hf.prodMk hg)
  exact this

theorem tracelessPart_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (G : Matrix ι ι ℂ) :
    tracelessPart (Matrix.reindex e e G) = Matrix.reindex e e (tracelessPart G) := by
  unfold tracelessPart
  have htr : (Matrix.reindex e e G).trace = G.trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e.symm (fun i => G i i)
  rw [htr, Fintype.card_congr e]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply, e.symm.injective.eq_iff]

/-- `GUE_ι(t) = Law(G⁰ + ζ I)`, `G⁰ ~ GUE_ι(t).map tracelessPart`, `ζ ~ N(0, t/|ι|)`. -/
theorem gueMeasure_eq_scalarShiftLaw (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (t v : ℝ≥0) (hv : (v : ℝ) = t / Fintype.card ι) :
    gueMeasure ι t = scalarShiftLaw ι t v := by
  set d := Fintype.card ι
  set e : ι ≃ Fin d := Fintype.equivFin ι
  have hR : Measurable (Matrix.reindex e.symm e.symm : Matrix (Fin d) (Fin d) ℂ → Matrix ι ι ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hR' : Measurable (Matrix.reindex e e : Matrix ι ι ℂ → Matrix (Fin d) (Fin d) ℂ) :=
    Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply
  have hg : gueMeasure ι t = (gueMeasure (Fin d) t).map (Matrix.reindex e.symm e.symm) :=
    (gueMeasure_map_reindex e.symm t).symm
  have hg' : gueMeasure (Fin d) t = (gueMeasure ι t).map (Matrix.reindex e e) :=
    (gueMeasure_map_reindex e t).symm
  rw [hg, ← scalarShiftLaw_fin_eq_gueMeasure hι t v hv, scalarShiftLaw, scalarShiftLaw,
    Measure.map_map hR measurable_scalarAdd]
  have hfun : (Matrix.reindex e.symm e.symm) ∘
      (fun y : Matrix (Fin d) (Fin d) ℂ × ℝ => y.1 + (y.2 : ℂ) • 1) =
      (fun y : Matrix ι ι ℂ × ℝ => y.1 + (y.2 : ℂ) • 1) ∘ Prod.map (Matrix.reindex e.symm e.symm) id := by
    funext y
    ext i j
    simp [Matrix.one_apply]
  rw [hfun, ← Measure.map_map measurable_scalarAdd (hR.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hR measurable_id, Measure.map_id,
    Measure.map_map hR measurable_tracelessPart, hg',
    Measure.map_map (hR.comp measurable_tracelessPart) hR']
  have hcomp : ((Matrix.reindex e.symm e.symm) ∘ tracelessPart) ∘ (Matrix.reindex e e) =
      (tracelessPart : Matrix ι ι ℂ → Matrix ι ι ℂ) := by
    funext G
    simp only [Function.comp_apply]
    rw [tracelessPart_reindex, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix]
    simp
  rw [hcomp]

/-- Lintegral form of the scalar split of one block. -/
theorem lintegral_gue_scalarSplit (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (t v : ℝ≥0) (hv : (v : ℝ) = t / Fintype.card ι)
    {h : Matrix ι ι ℂ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ G, h G ∂gueMeasure ι t = ∫⁻ G, ∫⁻ ζ, h (tracelessPart G + (ζ : ℂ) • 1)
      ∂gaussianReal 0 v ∂gueMeasure ι t := by
  have hm : Measurable fun a : Matrix ι ι ℂ × ℝ => h (a.1 + (a.2 : ℂ) • 1) :=
    hh.comp measurable_scalarAdd
  conv_lhs => rw [gueMeasure_eq_scalarShiftLaw ι hι t v hv, scalarShiftLaw,
    lintegral_map hh measurable_scalarAdd,
    lintegral_prod (fun a : Matrix ι ι ℂ × ℝ => h (a.1 + (a.2 : ℂ) • 1)) hm.aemeasurable,
    lintegral_map hm.lintegral_prod_right' measurable_tracelessPart]

/-- Lintegral form of the scalar split of `k` i.i.d. blocks. -/
theorem lintegral_pi_gue_scalarSplit (k W : ℕ) (hW : 0 < W) (t v : ℝ≥0) (hv : (v : ℝ) = t / W)
    {h : (Fin k → Matrix (Fin W) (Fin W) ℂ) → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ A, h A ∂Measure.pi (fun _ : Fin k => gueMeasure (Fin W) t) =
      ∫⁻ A, ∫⁻ ζ, h (fun j => tracelessPart (A j) + (ζ j : ℂ) • 1)
        ∂Measure.pi (fun _ : Fin k => gaussianReal 0 v)
        ∂Measure.pi (fun _ : Fin k => gueMeasure (Fin W) t) := by
  have hv' : (v : ℝ) = t / Fintype.card (Fin W) := by rw [Fintype.card_fin]; exact hv
  have hssl := gueMeasure_eq_scalarShiftLaw (Fin W) (by rw [Fintype.card_fin]; exact hW) t v hv'
  set μ0 := (gueMeasure (Fin W) t).map tracelessPart
  have hpi : Measure.pi (fun _ : Fin k => gueMeasure (Fin W) t) =
      ((Measure.pi fun _ : Fin k => μ0).prod (Measure.pi fun _ : Fin k => gaussianReal 0 v)).map
        (fun p j => p.1 j + (p.2 j : ℂ) • 1) := by
    have h1 : Measure.pi (fun _ : Fin k => gueMeasure (Fin W) t) =
        (Measure.pi fun _ : Fin k => μ0.prod (gaussianReal 0 v)).map
          (fun x j => (x j).1 + ((x j).2 : ℂ) • 1) := by
      rw [Measure.pi_map_pi (fun _ => measurable_scalarAdd.aemeasurable)]
      congr 1
      funext j
      rw [hssl, scalarShiftLaw]
    have h2 := (measurePreserving_arrowProdEquivProdArrow (Matrix (Fin W) (Fin W) ℂ) ℝ (Fin k)
      (fun _ => μ0) (fun _ => gaussianReal 0 v)).symm
    rw [h1, ← h2.map_eq, Measure.map_map]
    · rfl
    · exact measurable_pi_iff.2 fun j => measurable_scalarAdd.comp (measurable_pi_apply j)
    · exact (MeasurableEquiv.arrowProdEquivProdArrow _ _ _).symm.measurable
  have hadd : Measurable fun p : (Fin k → Matrix (Fin W) (Fin W) ℂ) × (Fin k → ℝ) =>
      fun j => p.1 j + (p.2 j : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) :=
    measurable_pi_iff.2 fun j => measurable_add_smul_one
      ((measurable_pi_apply j).comp measurable_fst) ((measurable_pi_apply j).comp measurable_snd)
  have hpi0 : Measure.pi (fun _ : Fin k => μ0) =
      (Measure.pi fun _ : Fin k => gueMeasure (Fin W) t).map (fun A j => tracelessPart (A j)) :=
    (Measure.pi_map_pi (fun _ => measurable_tracelessPart.aemeasurable)).symm
  have htl : Measurable fun A : Fin k → Matrix (Fin W) (Fin W) ℂ => fun j => tracelessPart (A j) :=
    measurable_pi_iff.2 fun j => measurable_tracelessPart.comp (measurable_pi_apply j)
  have hm : Measurable fun a : (Fin k → Matrix (Fin W) (Fin W) ℂ) × (Fin k → ℝ) =>
      h fun j => a.1 j + (a.2 j : ℂ) • 1 := hh.comp hadd
  conv_lhs => rw [hpi, lintegral_map hh hadd, lintegral_prod _ hm.aemeasurable,
    hpi0, lintegral_map hm.lintegral_prod_right' htl]

/-!
## Generic Tonelli bookkeeping
-/

section Tonelli

variable {β γ δ ε : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  [MeasurableSpace ε] {μb : Measure β} {μg : Measure γ} {ν : Measure δ} {ρ : Measure ε}
  [SFinite μb] [SFinite μg] [SFinite ν] [SFinite ρ]

theorem measurable_lintegral_three {α : Type*} [MeasurableSpace α]
    {k : α × β × γ × δ → ℝ≥0∞} (hk : Measurable k) :
    Measurable fun a => ∫⁻ x, ∫⁻ y, ∫⁻ z, k (a, x, y, z) ∂ν ∂μg ∂μb := by
  have h1 : Measurable fun p : (α × β × γ) × δ => k (p.1.1, p.1.2.1, p.1.2.2, p.2) :=
    hk.comp ((measurable_fst.comp measurable_fst).prodMk ((measurable_fst.comp
      (measurable_snd.comp measurable_fst)).prodMk ((measurable_snd.comp
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)))
  have h2 : Measurable fun p : (α × β) × γ => ∫⁻ z, k (p.1.1, p.1.2, p.2, z) ∂ν :=
    (h1.lintegral_prod_right').comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h3 : Measurable fun p : α × β => ∫⁻ y, ∫⁻ z, k (p.1, p.2, y, z) ∂ν ∂μg :=
    h2.lintegral_prod_right'
  exact h3.lintegral_prod_right'

/-- Move the outermost integral (over `ε`) innermost past three others. -/
theorem lintegral_reorder_four {Φ : β × γ × δ × ε → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ w, ∫⁻ x, ∫⁻ y, ∫⁻ z, Φ (x, y, z, w) ∂ν ∂μg ∂μb ∂ρ =
      ∫⁻ x, ∫⁻ y, ∫⁻ z, ∫⁻ w, Φ (x, y, z, w) ∂ρ ∂ν ∂μg ∂μb := by
  -- swap `w` and `x`
  have s1 : Measurable (Function.uncurry fun (w : ε) (x : β) =>
      ∫⁻ y, ∫⁻ z, Φ (x, y, z, w) ∂ν ∂μg) := by
    have := measurable_lintegral_three (μb := μg) (μg := ν) (ν := (Measure.dirac (0 : ℝ≥0)))
      (k := fun p : (ε × β) × γ × δ × ℝ≥0 => Φ (p.1.2, p.2.1, p.2.2.1, p.1.1))
      (hΦ.comp ((measurable_snd.comp measurable_fst).prodMk ((measurable_fst.comp
        measurable_snd).prodMk ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_fst.comp measurable_fst)))))
    simp only [lintegral_dirac] at this
    exact this
  rw [lintegral_lintegral_swap s1.aemeasurable]
  refine lintegral_congr fun x => ?_
  -- swap `w` and `y`
  have s2 : Measurable (Function.uncurry fun (w : ε) (y : γ) => ∫⁻ z, Φ (x, y, z, w) ∂ν) := by
    have h : Measurable fun p : (ε × γ) × δ => Φ (x, p.1.2, p.2, p.1.1) :=
      hΦ.comp (measurable_const.prodMk ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst))))
    exact h.lintegral_prod_right'
  rw [lintegral_lintegral_swap s2.aemeasurable]
  refine lintegral_congr fun y => ?_
  have s3 : Measurable (Function.uncurry fun (w : ε) (z : δ) => Φ (x, y, z, w)) :=
    hΦ.comp (measurable_const.prodMk (measurable_const.prodMk
      (measurable_snd.prodMk measurable_fst)))
  rw [lintegral_lintegral_swap s3.aemeasurable]

end Tonelli

/-!
## The collar
-/

variable {W : ℕ}

/-- Add `ζ₂ I` to the middle block and `ζ_A(j) I` to the end blocks. -/
def scalarSample (ζ : ℝ × (Fin 2 → ℝ)) (ω : CollarSample W) : CollarSample W :=
  ((fun j => ω.1.1 j + (ζ.2 j : ℂ) • 1, ω.1.2), ω.2 + (ζ.1 : ℂ) • 1)

/-- Add the common shift `θ I` to the three diagonal blocks. -/
def shiftSample (θ : ℝ) (ω : CollarSample W) : CollarSample W :=
  ((fun j => ω.1.1 j + (θ : ℂ) • 1, ω.1.2), ω.2 + (θ : ℂ) • 1)

/-- Traceless parts of the three diagonal blocks. -/
def tlSample (ω : CollarSample W) : CollarSample W :=
  ((fun j => tracelessPart (ω.1.1 j), ω.1.2), tracelessPart ω.2)

theorem measurable_scalarSample :
    Measurable fun p : CollarSample W × (ℝ × (Fin 2 → ℝ)) => scalarSample p.2 p.1 := by
  unfold scalarSample
  refine Measurable.prodMk (Measurable.prodMk ?_ (measurable_snd.comp (measurable_fst.comp
    measurable_fst))) ?_
  · exact measurable_pi_iff.2 fun j => measurable_add_smul_one
      ((measurable_pi_apply j).comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  · exact measurable_add_smul_one (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_snd)

theorem measurable_shiftSample :
    Measurable fun p : CollarSample W × ℝ => shiftSample p.2 p.1 := by
  unfold shiftSample
  refine Measurable.prodMk (Measurable.prodMk ?_ (measurable_snd.comp (measurable_fst.comp
    measurable_fst))) ?_
  · exact measurable_pi_iff.2 fun j => measurable_add_smul_one
      ((measurable_pi_apply j).comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      measurable_snd
  · exact measurable_add_smul_one (measurable_snd.comp measurable_fst) measurable_snd

theorem measurable_tlSample : Measurable (tlSample (W := W)) := by
  unfold tlSample
  refine Measurable.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_fst)) ?_
  · exact measurable_pi_iff.2 fun j => measurable_tracelessPart.comp
      ((measurable_pi_apply j).comp (measurable_fst.comp measurable_fst))
  · exact measurable_tracelessPart.comp measurable_snd

theorem scalarSample_add (r : ℝ × (Fin 2 → ℝ)) (θ : ℝ) (ω : CollarSample W) :
    scalarSample (r + (θ, fun _ => θ)) ω = shiftSample θ (scalarSample r ω) := by
  simp only [scalarSample, shiftSample, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    Complex.ofReal_add, add_smul, add_assoc]

theorem card_portSite_common : Fintype.card (PortSite W .common) = W := by
  simp [PortSite, LayerShape.ports]

/-- The per-block scalar variance `t/W`, `t = (1-2b)/W`. -/
def blockScalarVar (W : ℕ) (b : ℝ) : ℝ≥0 := Real.toNNReal ((1 - 2 * b) / W) / (W : ℝ≥0)

/-- The common scalar variance `t/(3W) = c/(3W²)`. -/
def commonShiftVar (W : ℕ) (b : ℝ) : ℝ≥0 := blockScalarVar W b / 3

/-- Step 1: the three per-block scalar parts, `Z = N(0,v) ⊗ N(0,v)^{⊗2}`. -/
theorem lintegral_collarLaw_scalarSplit (hW : 0 < W) (b : ℝ) {F : CollarSample W → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F ω ∂collarLaw W b = ∫⁻ ω, ∫⁻ ζ, F (scalarSample ζ (tlSample ω))
      ∂((gaussianReal 0 (blockScalarVar W b)).prod
        (Measure.pi fun _ : Fin 2 => gaussianReal 0 (blockScalarVar W b))) ∂collarLaw W b := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  set v := blockScalarVar W b
  have hv : (v : ℝ) = t / W := by
    simp only [v, blockScalarVar, NNReal.coe_div, NNReal.coe_natCast, t]
  have hvP : (v : ℝ) = t / Fintype.card (PortSite W .common) := by rw [card_portSite_common]; exact hv
  have hP : 0 < Fintype.card (PortSite W .common) := by rw [card_portSite_common]; exact hW
  set μA := Measure.pi (fun _ : Fin 2 => gueMeasure (Fin W) t)
  set μB := Measure.pi fun _ : Fin 2 => Measure.pi fun _ : Fin 1 =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  set μG := gueMeasure (PortSite W .common) t
  set N := gaussianReal 0 v
  set NA := Measure.pi fun _ : Fin 2 => gaussianReal 0 v
  have hlaw : collarLaw W b = (μA.prod μB).prod μG := rfl
  rw [hlaw]
  have hΦm : Measurable fun p : (Fin 2 → Matrix (Fin W) (Fin W) ℂ) ×
      (Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) × Matrix (PortSite W .common)
        (PortSite W .common) ℂ × ℝ × (Fin 2 → ℝ) =>
      F ((fun j => tracelessPart (p.1 j) + (p.2.2.2.2 j : ℂ) • 1, p.2.1),
        tracelessPart p.2.2.1 + (p.2.2.2.1 : ℂ) • 1) := by
    refine hF.comp (Measurable.prodMk (Measurable.prodMk ?_ (measurable_fst.comp measurable_snd)) ?_)
    · exact measurable_pi_iff.2 fun j => measurable_add_smul_one
        (measurable_tracelessPart.comp ((measurable_pi_apply j).comp measurable_fst))
        ((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd))))
    · exact measurable_add_smul_one (measurable_tracelessPart.comp (measurable_fst.comp
        (measurable_snd.comp measurable_snd))) (measurable_fst.comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))
  have hF' : ∀ x, Measurable fun G => F (x, G) := fun x => hF.comp measurable_prodMk_left
  -- left side
  have hL : ∫⁻ ω, F ω ∂(μA.prod μB).prod μG = ∫⁻ A, ∫⁻ zA, ∫⁻ B, ∫⁻ G, ∫⁻ z,
      F ((fun j => tracelessPart (A j) + (zA j : ℂ) • 1, B), tracelessPart G + (z : ℂ) • 1)
        ∂N ∂μG ∂μB ∂NA ∂μA := by
    rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hF.lintegral_prod_right'.aemeasurable]
    have hstep : ∀ (A : Fin 2 → Matrix (Fin W) (Fin W) ℂ)
        (B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ),
        ∫⁻ G, F ((A, B), G) ∂μG = ∫⁻ G, ∫⁻ z, F ((A, B), tracelessPart G + (z : ℂ) • 1) ∂N ∂μG :=
      fun A B => lintegral_gue_scalarSplit (PortSite W .common) hP t v hvP (hF' (A, B))
    rw [lintegral_congr fun A => lintegral_congr fun B => hstep A B]
    have hmeas : Measurable fun A : Fin 2 → Matrix (Fin W) (Fin W) ℂ => ∫⁻ B, ∫⁻ G, ∫⁻ z,
        F ((A, B), tracelessPart G + (z : ℂ) • 1) ∂N ∂μG ∂μB := by
      have h4 : Measurable fun p : (Fin 2 → Matrix (Fin W) (Fin W) ℂ) ×
          (Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) × Matrix (PortSite W .common)
            (PortSite W .common) ℂ × ℝ =>
          F ((p.1, p.2.1), tracelessPart p.2.2.1 + (p.2.2.2 : ℂ) • 1) :=
        hF.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_add_smul_one (measurable_tracelessPart.comp (measurable_fst.comp
            (measurable_snd.comp measurable_snd))) (measurable_snd.comp (measurable_snd.comp
              measurable_snd))))
      exact measurable_lintegral_three (μb := μB) (μg := μG) (ν := N) h4
    exact lintegral_pi_gue_scalarSplit 2 W hW t v hv (h := fun A => ∫⁻ B, ∫⁻ G, ∫⁻ z,
        F ((A, B), tracelessPart G + (z : ℂ) • 1) ∂N ∂μG ∂μB) hmeas
  have hT : Measurable fun q : CollarSample W × (ℝ × (Fin 2 → ℝ)) =>
      F (scalarSample q.2 (tlSample q.1)) :=
    hF.comp (Measurable.comp (g := fun p : CollarSample W × (ℝ × (Fin 2 → ℝ)) =>
      scalarSample p.2 p.1) measurable_scalarSample (measurable_tlSample.prodMap measurable_id))
  have hm1 : Measurable fun ω : CollarSample W =>
      ∫⁻ ζ, F (scalarSample ζ (tlSample ω)) ∂(N.prod NA) := hT.lintegral_prod_right'
  rw [hL, lintegral_prod _ hm1.aemeasurable, lintegral_prod _ hm1.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun A => ?_
  have hζ : ∀ (B : Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ)
      (G : Matrix (PortSite W .common) (PortSite W .common) ℂ),
      ∫⁻ ζ, F (scalarSample ζ (tlSample ((A, B), G))) ∂(N.prod NA) =
        ∫⁻ z, ∫⁻ zA, F ((fun j => tracelessPart (A j) + (zA j : ℂ) • 1, B),
          tracelessPart G + (z : ℂ) • 1) ∂NA ∂N := by
    intro B G
    exact lintegral_prod _ (hT.comp (Measurable.prodMk (measurable_const (a := ((A, B), G)))
      measurable_id)).aemeasurable
  simp_rw [hζ]
  have hΦ : Measurable fun p : (Fin 2 → Fin 1 → Matrix (Fin W) (Fin W) ℂ) ×
      Matrix (PortSite W .common) (PortSite W .common) ℂ × ℝ × (Fin 2 → ℝ) =>
      F ((fun j => tracelessPart (A j) + (p.2.2.2 j : ℂ) • 1, p.1),
        tracelessPart p.2.1 + (p.2.2.1 : ℂ) • 1) := by
    refine hF.comp (Measurable.prodMk (Measurable.prodMk ?_ measurable_fst) ?_)
    · exact measurable_pi_iff.2 fun j => measurable_add_smul_one measurable_const
        ((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    · exact measurable_add_smul_one (measurable_tracelessPart.comp (measurable_fst.comp
        measurable_snd)) (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact lintegral_reorder_four (μb := μB) (μg := μG) (ν := N) (ρ := NA) hΦ

/-- `ℝ × (Fin 2 → ℝ)`-form of the three-Gaussian decomposition: `N(0,v) ⊗ N(0,v)^{⊗2}` is the law of
`r + (θ, θ, θ)` with `θ ~ N(0, v/3)` independent of `r ~ ρ`. -/
theorem exists_scalarTriple_decomp (v : ℝ≥0) :
    ∃ ρ : Measure (ℝ × (Fin 2 → ℝ)), IsProbabilityMeasure ρ ∧
      (gaussianReal 0 v).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 v) =
        (ρ.prod (gaussianReal 0 (v / 3))).map (fun p => p.1 + (p.2, fun _ => p.2)) := by
  set P3 := Measure.pi fun _ : Fin 3 => gaussianReal 0 v
  set σ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have hσ := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 v) (Fin.last 2)).map_eq
  have hadd3 : Measurable fun p : (Fin 3 → ℝ) × ℝ => p.1 + fun _ => p.2 :=
    measurable_fst.add (measurable_pi_iff.2 fun _ => measurable_snd)
  have haddZ : Measurable fun p : (ℝ × (Fin 2 → ℝ)) × ℝ => p.1 + (p.2, fun _ => p.2) :=
    measurable_fst.add (measurable_snd.prodMk (measurable_pi_iff.2 fun _ => measurable_snd))
  refine ⟨(P3.map residual).map σ, ?_, ?_⟩
  · have : IsProbabilityMeasure (P3.map residual) :=
      (Measure.isProbabilityMeasure_map_iff measurable_residual.aemeasurable).2 inferInstance
    exact (Measure.isProbabilityMeasure_map_iff σ.measurable.aemeasurable).2 inferInstance
  have hfun : σ ∘ (fun p : (Fin 3 → ℝ) × ℝ => p.1 + fun _ => p.2) =
      (fun p : (ℝ × (Fin 2 → ℝ)) × ℝ => p.1 + (p.2, fun _ => p.2)) ∘ Prod.map σ id := by
    funext p
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, σ,
      MeasurableEquiv.piFinSuccAbove_apply]
    ext <;> simp [Fin.removeNth]
  rw [← hσ, pi_gaussian_eq_map_residual v, Measure.map_map σ.measurable hadd3, hfun,
    ← Measure.map_map haddZ (σ.measurable.prodMap measurable_id),
    ← Measure.map_prod_map _ _ σ.measurable measurable_id, Measure.map_id]

/-- **Common Gaussian scalar shift of the collar** (`PLAN.md` §2.1). For `W ≥ 1`: there is a
probability measure `μ'` with `collarLaw W b = (μ' ⊗ N(0, commonShiftVar W b)).map shiftSample`. -/
theorem collarLaw_commonShift (hW : 0 < W) (b : ℝ) :
    ∃ μ' : Measure (CollarSample W), IsProbabilityMeasure μ' ∧
      collarLaw W b = (μ'.prod (gaussianReal 0 (commonShiftVar W b))).map
        (fun p => shiftSample p.2 p.1) := by
  obtain ⟨ρ, hρ, hZ⟩ := exists_scalarTriple_decomp (blockScalarVar W b)
  set Nθ := gaussianReal 0 (commonShiftVar W b)
  have hS : Measurable fun p : CollarSample W × (ℝ × (Fin 2 → ℝ)) => scalarSample p.2 (tlSample p.1) :=
    Measurable.comp (g := fun p : CollarSample W × (ℝ × (Fin 2 → ℝ)) => scalarSample p.2 p.1)
      measurable_scalarSample (measurable_tlSample.prodMap measurable_id)
  refine ⟨((collarLaw W b).prod ρ).map fun p => scalarSample p.2 (tlSample p.1),
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).2 inferInstance, ?_⟩
  refine measure_eq_of_lintegral_eq fun F hF => ?_
  have hFs : Measurable fun p : CollarSample W × ℝ => F (shiftSample p.2 p.1) :=
    hF.comp measurable_shiftSample
  have haddZ : Measurable fun p : (ℝ × (Fin 2 → ℝ)) × ℝ => p.1 + (p.2, fun _ => p.2) :=
    measurable_fst.add (measurable_snd.prodMk (measurable_pi_iff.2 fun _ => measurable_snd))
  have hI : Measurable fun ω' : CollarSample W => ∫⁻ θ, F (shiftSample θ ω') ∂Nθ :=
    hFs.lintegral_prod_right'
  have hI2 : Measurable fun a : CollarSample W × (ℝ × (Fin 2 → ℝ)) =>
      ∫⁻ θ, F (shiftSample θ (scalarSample a.2 (tlSample a.1))) ∂Nθ :=
    Measurable.comp (g := fun ω' : CollarSample W => ∫⁻ θ, F (shiftSample θ ω') ∂Nθ) hI hS
  rw [lintegral_map hF measurable_shiftSample, lintegral_prod _ hFs.aemeasurable]
  dsimp only
  rw [lintegral_map (f := fun ω' : CollarSample W => ∫⁻ θ, F (shiftSample θ ω') ∂Nθ) hI hS,
    lintegral_prod (fun a : CollarSample W × (ℝ × (Fin 2 → ℝ)) =>
      ∫⁻ θ, F (shiftSample θ (scalarSample a.2 (tlSample a.1))) ∂Nθ) hI2.aemeasurable,
    lintegral_collarLaw_scalarSplit hW b hF]
  refine lintegral_congr fun ω => ?_
  have hg : Measurable fun ζ : ℝ × (Fin 2 → ℝ) => F (scalarSample ζ (tlSample ω)) :=
    hF.comp (Measurable.comp (g := fun p : CollarSample W × (ℝ × (Fin 2 → ℝ)) =>
      scalarSample p.2 p.1) measurable_scalarSample (measurable_const.prodMk measurable_id))
  have hvar : blockScalarVar W b / 3 = commonShiftVar W b := rfl
  have hg2 : Measurable fun a : (ℝ × (Fin 2 → ℝ)) × ℝ =>
      F (scalarSample (a.1 + (a.2, fun _ => a.2)) (tlSample ω)) :=
    Measurable.comp (g := fun ζ : ℝ × (Fin 2 → ℝ) => F (scalarSample ζ (tlSample ω))) hg haddZ
  rw [hZ, hvar, lintegral_map hg haddZ]
  dsimp only
  rw [lintegral_prod (fun a : (ℝ × (Fin 2 → ℝ)) × ℝ =>
      F (scalarSample (a.1 + (a.2, fun _ => a.2)) (tlSample ω))) hg2.aemeasurable]
  refine lintegral_congr fun r => lintegral_congr fun θ => ?_
  rw [scalarSample_add]

theorem blockDiag_add_smul_one {k : ℕ} (A : Fin k → Matrix (Fin W) (Fin W) ℂ) (θ : ℂ) :
    blockDiag (fun j => A j + θ • (1 : Matrix (Fin W) (Fin W) ℂ)) =
      blockDiag A + θ • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) := by
  ext x y
  simp only [BlockBand.Internal.Contracts.Layers.blockDiag, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply]
  by_cases h1 : x.1 = y.1
  · by_cases h2 : x.2 = y.2
    · have : x = y := Prod.ext h1 h2
      simp [this]
    · have : x ≠ y := fun h => h2 (congrArg Prod.snd h)
      simp [h1, h2, this]
  · have : x ≠ y := fun h => h1 (congrArg Prod.fst h)
    simp [h1, this]

/-- `ℋ_X(shiftSample θ ω) = ℋ_X(ω) + θ I`. -/
theorem collarMatrix_shiftSample (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (θ : ℝ)
    (ω : CollarSample W) :
    collarMatrix e X (shiftSample θ ω) =
      collarMatrix e X ω + (θ : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) := by
  unfold collarMatrix shiftSample
  rw [blockDiag_add_smul_one, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
    Matrix.fromBlocks_add]
  congr 1
  · abel
  · simp
  · simp
  · exact add_sub_right_comm _ _ _

end BlockBand.Critical.Collar.Density
