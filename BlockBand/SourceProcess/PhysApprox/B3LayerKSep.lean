module

public import BlockBand.SourceProcess.PhysApprox.B3LayerKSepAlg
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm

/-!
# `B3PadGrowth` from `B3PadInvertible`

**`b3PadGrowth_of_inv : B3PadInvertible → B3PadGrowth`**: almost surely, at every
no-birth step `j` (in fact at every `j ≥ n_s`, on and off the alive set), the chain state
`𝕐_j = b3ChainXX … j` satisfies `𝕐_{j+1} = freshTwoPortSchur E 𝕐_j F_j`.

The proof: along the path `𝕊_n = 𝕊(𝕏_n)` with `𝕏_n = pathSchur` (`scatteringMatrix_eq`) and
`𝕏_{j+1} = Φ_{F_j}(𝕏_j)` (`ae_pathSchur_succ_eq_freshTwoPortSchur`), so `𝕐_n` is
`Cay(𝕊_pad(𝕊(𝕏_n)))` and the deterministic commutation `cay_padScat_freshTwoPortSchur`
applies. Its hypotheses hold a.s.:
* `ζ - 𝕏_j`, `ζ - 𝕏_{j+1}` invertible (`𝕏_n` Hermitian, `Im ζ > 0`);
* the open pivot `A_F - E - (𝕏_j)₀₀` invertible: it is the Schur complement of the grown pencil
  (`isUnit_freshPivot_path`);
* the padded pivot `A_F - E - (𝕐_j)₀₀` invertible: `𝕐_j` is a measurable function
  of the past at `j` and the fresh block is GUE, independent of the past
  (`ae_isUnit_freshPivot`, from `closedLaw_map_past_fresh` and `ae_det_gue_add_ne_zero`);
* `1 - zN_n`, `1 - 𝕊_pad(n)` invertible at `n = j, j + 1`: `B3PadInvertible`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.Transmission BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops

variable {W np : ℕ}

/-- **The open fresh pivot is invertible** when the pencils at `j` and `j + 1` are: it is the
Schur complement of the grown pencil. -/
theorem isUnit_freshPivot_path (E : ℝ) {j : ℕ} (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1))
    (hF' : IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1)) :
    IsUnit (freshPivot E (pathSchur E (pathAt W j ω)) (freshSample W j ω)) := by
  set F := pathMatrix (pathAt W j ω) - (E : ℂ) • 1
  set Cn := nearCol W j ω
  have hblk := pathMatrix_succ_submatrix E j ω
  have hM : IsUnit (Matrix.fromBlocks (ω.1 j - (E : ℂ) • 1) Cnᴴ Cn F) := by
    rw [← hblk, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
      ← Matrix.isUnit_iff_isUnit_det]
    exact hF'
  have h00 : portBlock (pathSchur E (pathAt W j ω)) 0 0 = Cnᴴ * F⁻¹ * Cn :=
    portBlock_pathSchur E j ω 0 0
  have := hF.invertible
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv] at hM
  rw [Matrix.isUnit_iff_isUnit_det]
  have e : freshPivot E (pathSchur E (pathAt W j ω)) (freshSample W j ω) =
      ω.1 j - (E : ℂ) • 1 - Cnᴴ * F⁻¹ * Cn := by
    rw [freshPivot, h00]; rfl
  rw [e]
  exact isUnit_of_mul_isUnit_right hM

/-- **The fresh pivot of a past-determined two-port is a.s. invertible** (GUE block independent of
the past). -/
theorem ae_isUnit_freshPivot {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) (j : ℕ)
    {Z : ProbedPath W np × ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hZ : Measurable Z)
    (hZinv : ∀ y, Z (b3Ext W j y) = Z y) :
    ∀ᵐ y ∂closedLaw b W np, IsUnit (freshPivot E (Z y) (freshSample W j y.1.1)) := by
  set g : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) × LayerSample W .oneBlockOnePort → ℂ :=
    fun p => (freshPivot E (Z (b3Rebuild W j p.1)) p.2).det with hgdef
  have hP : Measurable fun p : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
      LayerSample W .oneBlockOnePort => freshPivot E (Z (b3Rebuild W j p.1)) p.2 := by
    refine Measurable.of_eval_matrix _ fun x x' => ?_
    have h1 : Measurable fun p : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
        LayerSample W .oneBlockOnePort => p.2.1 0 :=
      (measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable fun p : (PastSample W j × ((Fin np → Fin W → ℂ) × ℝ)) ×
        LayerSample W .oneBlockOnePort => Z (b3Rebuild W j p.1) :=
      hZ.comp ((measurable_b3Rebuild W j).comp measurable_fst)
    simp only [freshPivot, Matrix.sub_apply, portBlock, Matrix.of_apply]
    exact (h1.eval_matrix.sub measurable_const).sub h2.eval_matrix
  have hg : Measurable g := measurable_det_comp hP
  set Sset := {p | g p = 0}
  have hS : MeasurableSet Sset := hg (measurableSet_singleton 0)
  have hslice : ∀ x, freshLaw W b (Prod.mk x ⁻¹' Sset) = 0 := by
    intro x
    have hA := ae_det_gue_add_ne_zero W (gueVariance_ne_zero hb hW)
      (-((E : ℂ) • 1) - portBlock (Z (b3Rebuild W j x)) 0 0)
    rw [← freshLaw_map_block W b] at hA
    have hA' := ae_of_ae_map ((measurable_pi_apply 0).comp measurable_fst).aemeasurable hA
    rw [ae_iff] at hA'
    refine measure_mono_null (fun f hf => ?_) hA'
    change g (x, f) = 0 at hf
    intro hne
    apply hne
    show (f.1 0 + (-((E : ℂ) • 1) - portBlock (Z (b3Rebuild W j x)) 0 0)).det = 0
    rw [show f.1 0 + (-((E : ℂ) • 1) - portBlock (Z (b3Rebuild W j x)) 0 0) =
      freshPivot E (Z (b3Rebuild W j x)) f by simp only [freshPivot]; abel]
    exact hf
  have h0 : (((pastLaw W j b).prod (probePhaseLaw W np)).prod (freshLaw W b)) Sset = 0 :=
    (Measure.measure_prod_null hS).2 (Eventually.of_forall hslice)
  have hT : Measurable fun y : ProbedPath W np × ℝ => (b3Past W j y, freshSample W j y.1.1) :=
    (measurable_b3Past W j).prodMk
      ((measurable_freshSample W j).comp (measurable_fst.comp measurable_fst))
  rw [← closedLaw_map_past_fresh b W np j, Measure.map_apply hT hS] at h0
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h0
  change g (b3Past W j y, freshSample W j y.1.1) = 0
  simp only [hgdef, b3Rebuild_b3Past, hZinv]
  by_contra hd
  exact hy ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd))

/-- The path growth `𝕏_{j+1} = Φ_{F_j}(𝕏_j)` under the closed law. -/
theorem ae_closed_pathSchur_succ {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) :
    ∀ᵐ y ∂closedLaw b W np, ∀ j : ℕ, 1 ≤ j →
      pathSchur E (pathAt W (j + 1) y.1.1) =
        freshTwoPortSchur E (pathSchur E (pathAt W j y.1.1)) (freshSample W j y.1.1) := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  exact hq.ae (ae_pathSchur_succ_eq_freshTwoPortSchur hb hW E)

/-- `b3ChainXX` in Cayley form over the path two-port. -/
theorem b3ChainXX_eq_cay (b E s h : ℝ) (W n : ℕ) (y : ProbedPath W np × ℝ)
    (hF : IsUnit (pathMatrix (pathAt W n y.1.1) - (E : ℂ) • 1)) :
    b3ChainXX b E s h W n y =
      boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          (1 - B3LayerMean.padScat (twoPortScattering b E (pathSchur E (pathAt W n y.1.1)))
            (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
            (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)) (phase y.2))⁻¹ := by
  rw [b3ChainXX, B3LayerMean.b3PadScatter_eq, scatteringMatrix_eq b E n y.1.1 hF]

/-- **`B3PadGrowth` from `B3PadInvertible`.** -/
theorem b3PadGrowth_of_inv (hI : B3LayerMean.B3PadInvertible) : B3LayerMean.B3PadGrowth := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, -⟩ := B3LayerMean.frameDomain_facts hF
  have hb0 : 0 < b := hF.1.1
  have hηim : 0 < (boundaryZ b E).im := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [hI b E np τ m T s h K Vs hF, eventually_ge_atTop 1,
    B3Cur.eventually_one_le_closeLen hF.2.1] with W hIW hW hs1 j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hj1 : 1 ≤ j := hs1.trans hjc
  have hZm := B3LayerMean.measurable_b3ChainXX (np := np) (W := W) b E s h j
  have hZinv : ∀ y : ProbedPath W np × ℝ, b3ChainXX b E s h W j (b3Ext W j y) =
      b3ChainXX b E s h W j y := fun y => B3LayerMean.b3ChainXX_b3Ext hjc le_rfl y
  filter_upwards [hIW j hjc, hIW (j + 1) (hjc.trans (Nat.le_succ j)),
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW, ae_closed_pathSchur_succ (np := np) hb hW E,
    ae_isUnit_freshPivot hb hW E j hZm hZinv] with y h0 h1 hP hsucc hGp _hyA
  obtain ⟨hA, hFp, -, -⟩ := hP
  set Y := pathSchur E (pathAt W j y.1.1) with hYdef
  have hsj := hsucc j hj1
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y) :=
    portPencil_isUnit _ (pathSchur_isHermitian E j y.1.1 hA) hηim
  have hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y (freshSample W j y.1.1)) := by
    rw [← hsj]
    exact portPencil_isUnit _ (pathSchur_isHermitian E (j + 1) y.1.1 hA) hηim
  have hG := isUnit_freshPivot_path E y.1.1 (hFp j) (hFp (j + 1))
  have e0 := b3ChainXX_eq_cay b E s h W j y (hFp j)
  have e1 := b3ChainXX_eq_cay b E s h W (j + 1) y (hFp (j + 1))
  rw [hsj] at e1
  have hU := h0.1
  have hUg := h1.1
  have hV := h0.2
  have hVg := h1.2
  rw [scatteringMatrix_eq b E j y.1.1 (hFp j)] at hU
  rw [scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj] at hUg
  rw [B3LayerMean.b3PadScatter_eq, scatteringMatrix_eq b E j y.1.1 (hFp j)] at hV
  rw [B3LayerMean.b3PadScatter_eq, scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)),
    hsj] at hVg
  rw [e0] at hGp
  rw [e1, e0]
  exact cay_padScat_freshTwoPortSchur b E hη (omittedProj_mul_self b E h _ _)
    (omittedProj_mul_closingPairing b E h _ _) (phase y.2) Y (freshSample W j y.1.1) hK hKg hG
    hU hUg hV hVg hGp

end BlockBand.SourceProcess.PhysApprox.B3
