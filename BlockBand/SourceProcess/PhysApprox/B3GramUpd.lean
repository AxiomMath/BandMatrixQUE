module

public import BlockBand.SourceProcess.PhysApprox.B3GramUpdRep
public import BlockBand.SourceProcess.PhysApprox.B3ClosedForm
public import BlockBand.SourceProcess.PhysApprox.B3LayerKAlg
public import BlockBand.SourceProcess.PhysApprox.B3BirthMCross

/-!
# The closed Gram update `ClosedGramUpdate`

The proof is the Gram analogue of `closedK_step`:
1. Every column of the open frame that is not newborn at `j` is `x = 𝒰_jᴴg`, `x' = 𝒰_{j+1}ᴴg'`
   with `g'` the old-block embedding of `g` (`gramCol_rep`; current columns through the
   injectivity of `𝒰_j`, `j ≥ 2`, and the transport bridge `N_jᴴ𝒰_jᴴg = 𝒰_{j+1}ᴴg'`).
2. The closed interior Ward identity `𝒰CCᴴ𝒰ᴴ = c(Gcl − Gclᴴ)` turns `M = (Cᴴx)ᴴ(Cᴴx)` into
   `c(g*Gcl g − (g*Gcl g)^*)`; the grown closed inverse `Gcl' |old = Gcl + U'ΔV'` (the closed Schur
   step) gives `dM = c u*Δv + (c u*Δv)^*`.
3. The old rows of the grown closed near column are `U'L`, so `ιC'ᴴx' = Lᴴu` and
   `dB = u*(LLᴴ − 1)u = u*(U − 1)u`.

* `eventually_two_le_closeLen`, `ae_bridge_closed` (the transport bridge under `closedLaw`);
* **`closedGramUpdate_holds : ClosedGramUpdate`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

variable {W np K : ℕ}

namespace GramUpd

theorem eventually_two_le_closeLen {s : ℝ} (hs : 0 < s) :
    ∀ᶠ W : ℕ in atTop, 2 ≤ closeLen s W := by
  filter_upwards [(tendsto_natCast_atTop_atTop.atTop_mul_const hs).eventually_ge_atTop 2]
    with W hW
  exact Nat.le_floor (by simpa using hW)

/-- **The transport bridge under `closedLaw`.** -/
theorem ae_bridge_closed {b E : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ y ∂closedLaw b W np, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j y.1.1) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) y.1.1) - (E : ℂ) • 1) →
      (boundaryToInterior b E W (j + 1) y.1.1).submatrix (headEquiv j W) id =
        Matrix.fromRows (nearSel W * boundaryResolvent b E W j y.1.1 * transportN b E W j y.1.1)
          (boundaryToInterior b E W j y.1.1 * transportN b E W j y.1.1) := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  have h0 : ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1) →
      IsUnit (pathMatrix (pathAt W (j + 1) ω) - (E : ℂ) • 1) →
      (boundaryToInterior b E W (j + 1) ω).submatrix (headEquiv j W) id =
        Matrix.fromRows (nearSel W * boundaryResolvent b E W j ω * transportN b E W j ω)
          (boundaryToInterior b E W j ω * transportN b E W j ω) := by
    filter_upwards [ae_boundaryToInterior_succ hb0 hb1 hE1 hE2 hW] with ω hω j hj hF hF'
    exact (hω j hj hF hF').1
  exact hq.ae h0

theorem closedFrame_col_gram (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (d : SrcCol K (Fin np))
    (y : ProbedPath W np × ℝ) :
    (fun a => b3ClosedFrameAt b E s h τ m W n Vs y a d) =
      (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ *ᵥ gramCol b E s τ m W n Vs d y.1 := by
  funext a
  simp [b3ClosedFrameAt, Matrix.mul_apply, mulVec, dotProduct, gramCol]

theorem dot_nearPortProj (a c : Fin 2 × Fin W → ℂ) :
    star a ⬝ᵥ (nearPortProj W *ᵥ c) = star (nearSel W *ᵥ a) ⬝ᵥ (nearSel W *ᵥ c) := by
  have e := dot_gram (nearSel W)ᴴ a c
  rw [conjTranspose_conjTranspose] at e
  rw [nearPortProj_eq_nearSel, e]

end GramUpd

open GramUpd in
/-- **`ClosedGramUpdate` holds**: eventually, at every step `n_s ≤ j < ⌊WT⌋`, `X_cl` is a.e.
passive and every Gram step with no newborn column is a.e. `gramForm` at
`(gramNearU, gramNearV, X_cl, F_j)`. -/
theorem closedGramUpdate_holds : ClosedGramUpdate := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD.1
  have hh : h ^ 2 < 1 := by nlinarith [hD.2.2.2.1, hD.2.2.2.2.1]
  have hb1 : b < 1 := by linarith
  have hη := boundaryZ_im_pos (b := b) hb1 hE1 hE2
  filter_upwards [eventually_ge_atTop 1, eventually_two_le_closeLen hD.2.1] with W hW hs2 j hj
  have hsj : closeLen s W ≤ j := (Finset.mem_Ico.1 hj).1
  have hj2 : 2 ≤ j := hs2.trans hsj
  refine ⟨ae_passive_b3ClosedX hb0 hb hE1 hE2 s h hh τ m hW j, fun e he => ?_⟩
  filter_upwards [ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    ae_bridge_closed (np := np) hb0 hb1 hE1 hE2 hW]
    with y hP hQ hT
  obtain ⟨hA, hF, hB, hS⟩ := hP
  obtain ⟨hU, hU', hY, h4⟩ := hQ
  have hR := h4.resolve_left (isUnit_closedR0 b E h s j y.1.1 hA hη (hF j)).ne_zero
  have hX := passive_closedNearX b E s h hh j y.1.1 y.2 hη (hS j) (isUnit_iff_ne_zero.2 hU)
    (isUnit_iff_ne_zero.2 hR)
  have hTj := hT j (by omega) (hF j) (hF (j + 1))
  obtain ⟨σ, k, l⟩ := e
  have hk : ¬ IsNewCol τ W j k := fun h' => he (Or.inl h')
  have hl : ¬ IsNewCol τ W j l := fun h' => he (Or.inr h')
  obtain ⟨gk, gk', hgk, hxk, hxk'⟩ :=
    gramCol_rep b E s τ m hsj hj2 (Vs W) y.1 hA hη (hF j) (hB 0) (hB j) hTj k hk
  obtain ⟨gl, gl', hgl, hxl, hxl'⟩ :=
    gramCol_rep b E s τ m hsj hj2 (Vs W) y.1 hA hη (hF j) (hB 0) (hB j) hTj l hl
  obtain ⟨hM, hBs⟩ := closedGram_step_vec b E s h hh (by omega : 1 ≤ j) y.1.1
    (phase_mul_star y.2) hA hη (hF j) (hF (j + 1)) (hB (j + 1)) hS (isUnit_iff_ne_zero.2 hU)
    (isUnit_iff_ne_zero.2 hU') (isUnit_iff_ne_zero.2 hY) (isUnit_iff_ne_zero.2 hR) hX hgk hgl
  have hu : ∀ (d : SrcCol K (Fin np)) (g : Fin j × Fin W → ℂ),
      gramCol b E s τ m W j (Vs W) d y.1 = (boundaryToInterior b E W j y.1.1)ᴴ *ᵥ g →
      gramNearU b E s h τ m W j (Vs W) d y = (nearU b E s h W j y.1.1 (phase y.2))ᴴ *ᵥ g := by
    intro d g hg
    rw [gramNearU, hg, nearU_conj_mulVec]
  have hv : ∀ (d : SrcCol K (Fin np)) (g : Fin j × Fin W → ℂ),
      gramCol b E s τ m W j (Vs W) d y.1 = (boundaryToInterior b E W j y.1.1)ᴴ *ᵥ g →
      gramNearV b E s h τ m W j (Vs W) d y = nearV b E s h W j y.1.1 (phase y.2) *ᵥ g := by
    intro d g hg
    rw [gramNearV, hg, nearV_mulVec]
  simp only [b3dX, b3X, cEntry, b3ClosedGramAt]
  rw [BirthM.gramEntry_gramPair, BirthM.gramEntry_gramPair, closedFrame_col_gram,
    closedFrame_col_gram, closedFrame_col_gram, closedFrame_col_gram, hxk, hxk', hxl, hxl']
  by_cases hσ : σ = 0
  · subst hσ
    simp only [gramForm, BirthM.gramQ, ↓reduceIte, one_mulVec]
    rw [hu k gk hxk, hu l gl hxl, hv k gk hxk, hv l gl hxl]
    exact hM
  · simp only [gramForm, BirthM.gramQ, hσ, ↓reduceIte, dot_nearPortProj]
    rw [hu k gk hxk, hu l gl hxl]
    simp only [nearU_conj_mulVec] at hBs ⊢
    exact hBs

end BlockBand.SourceProcess.PhysApprox.B3
