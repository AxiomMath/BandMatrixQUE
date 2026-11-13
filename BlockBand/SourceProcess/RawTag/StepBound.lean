module

public import BlockBand.SourceProcess.RawTag.AbstractStep
public import BlockBand.SourceProcess.RawTag.FrameMoments

/-!
# One step of the raw-moment transport on `GrowthPath W × Γ`

`step_bound`: if a.s. the raw form is updated at step `l` by `nearL*Δ nearR` and the centred
fresh bilinear forms of `Δ` are bounded in `L^{4m}` by `C_f(W^{-1/2} + δ₀)‖u‖‖v‖`, then the
`4m`-th moment of the raw form at length `l + 1` is at most `(1 + K/W)` times that of the
mean-updated form plus `K W^{2m-1}` times the `4m`-th power of the fluctuation bound (by
`abstract_step` on the product of the past and the fresh layer).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open BlockBand.SourceProcess.FullSource
open scoped Matrix ENNReal ComplexOrder

variable {W : ℕ}

theorem measurable_bilinear_jt {α n : Type*} [MeasurableSpace α] [Fintype n] {u v : α → n → ℂ}
    {M : α → Matrix n n ℂ} (hu : Measurable u) (hM : Measurable M) (hv : Measurable v) :
    Measurable fun a => bilinear (u a) (M a) (v a) := by
  simp only [bilinear, dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply x).comp hu)).mul
      (Finset.measurable_sum _ fun y _ => hM.eval_matrix.mul ((measurable_pi_apply y).comp hv))

theorem passiveY_pathX_extendPast {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {l : ℕ}
    {q : PastSample W l} (hq : q ∈ hermPast W l) :
    (passiveY (pathX b E W l (extendPast q))).PosSemidef := by
  have h := passiveY_pastX (b := b) (E := E) hb hE1 hE2 (fun _ => le_rfl) hq
  have e := pathNearSchur_eq_past b E (fun _ => 0) l (extendPast q)
  rw [pastCoords_extendPast] at e
  have e' : pathX b E W l (extendPast q) = pastX b E (fun _ => 0) W l q := e
  rw [e']; exact h

/-- **One step** on `GrowthPath W × Γ`. -/
theorem step_bound {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) {l β₁ β₂ : ℕ}
    {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    {g₁ g₂ : Γ → Fin W → ℂ} (hg₁ : Measurable g₁) (hg₂ : Measurable g₂) {m : ℕ} (hm : 1 ≤ m)
    (hW : (1 : ℝ) ≤ W) {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hupd : ∀ᵐ ω ∂growthPathLaw W b, ∀ g h : Fin W → ℂ,
      rawForm b E W (l + 1) β₁ β₂ ω g h = rawForm b E W l β₁ β₂ ω g h +
        bilinear (nearL b E W l β₁ ω g) (stepDelta b E W l ω) (nearR b E W l β₂ ω h))
    (hI : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ x y, Integrable (fun f => freshDelta b E X f x y) (freshLaw W b))
    (hF : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
      eLpNorm (fun f => bilinear u (freshDelta b E X f -
          matrixExpect (freshLaw W b) (freshDelta b E X)) v) (ENNReal.ofReal (4 * m))
          (freshLaw W b) ≤
        ENNReal.ofReal (Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E X) * vecNorm u * vecNorm v)) :
    ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W (l + 1) β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m))
        ∂((growthPathLaw W b).prod ν) ≤
      ∫⁻ w, (ENNReal.ofReal ((1 + stepK (2 * m) / W) *
          (‖rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2) +
            bilinear (nearL b E W l β₁ w.1 (g₁ w.2))
              (matrixExpect (freshLaw W b) (freshDelta b E (pathX b E W l w.1)))
              (nearR b E W l β₂ w.1 (g₂ w.2))‖ ^ 2) ^ (2 * m)) +
        ENNReal.ofReal (stepK (2 * m) * (W : ℝ) ^ (2 * m - 1)) *
          ENNReal.ofReal ((Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E (pathX b E W l w.1)) *
            vecNorm (nearL b E W l β₁ w.1 (g₁ w.2)) *
            vecNorm (nearR b E W l β₂ w.1 (g₂ w.2))) ^ (4 * m))) ∂((growthPathLaw W b).prod ν) := by
  set μΩ := (growthPathLaw W b).prod ν
  set μP := (pastLaw W l b).prod ν
  set π : GrowthPath W × Γ → PastSample W l × Γ := fun w => (pastCoords W l w.1, w.2)
  set φ : GrowthPath W × Γ → LayerSample W .oneBlockOnePort := fun w => freshSample W l w.1
  have hπ : Measurable π := ((measurable_pastCoords W l).comp measurable_fst).prodMk measurable_snd
  have hφ : Measurable φ := (measurable_freshSample W l).comp measurable_fst
  have hmap : μΩ.map (fun w => (π w, φ w)) = μP.prod (freshLaw W b) := map_past_tag_fresh W l b ν
  have hmapπ : μΩ.map π = μP := by
    have := congrArg (fun μ => μ.map Prod.fst) hmap
    rw [Measure.map_map measurable_fst (hπ.prodMk hφ), Measure.map_fst_prod, measure_univ,
      one_smul] at this
    exact this
  have hext := measurable_extendPast (W := W) l
  set Xp : PastSample W l × Γ → Matrix (Fin W) (Fin W) ℂ := fun p => pathX b E W l (extendPast p.1)
  set xp : PastSample W l × Γ → ℂ :=
    fun p => rawForm b E W l β₁ β₂ (extendPast p.1) (g₁ p.2) (g₂ p.2)
  set ap : PastSample W l × Γ → Fin W → ℂ := fun p => nearL b E W l β₁ (extendPast p.1) (g₁ p.2)
  set cp : PastSample W l × Γ → Fin W → ℂ := fun p => nearR b E W l β₂ (extendPast p.1) (g₂ p.2)
  set D : PastSample W l × Γ → LayerSample W .oneBlockOnePort → Matrix (Fin W) (Fin W) ℂ :=
    fun p f => freshDelta b E (Xp p) f
  have hXp : Measurable Xp :=
    (BlockBand.Transmission.PathJet.measurable_pathX b E l).comp (hext.comp measurable_fst)
  have hxp : Measurable xp := measurable_rawForm b E l β₁ β₂ (hext.comp measurable_fst)
    (hg₁.comp measurable_snd) (hg₂.comp measurable_snd)
  have hap : Measurable ap := measurable_nearL b E l β₁ (hext.comp measurable_fst)
    (hg₁.comp measurable_snd)
  have hcp : Measurable cp := measurable_nearR b E l β₂ (hext.comp measurable_fst)
    (hg₂.comp measurable_snd)
  have hDm : Measurable fun z : (PastSample W l × Γ) × LayerSample W .oneBlockOnePort =>
      D z.1 z.2 := measurable_freshDelta_comp b E (hXp.comp measurable_fst) measurable_snd
  -- the past functions agree with the length-`l` objects
  have ex : ∀ w, xp (π w) = rawForm b E W l β₁ β₂ w.1 (g₁ w.2) (g₂ w.2) := fun w =>
    rawForm_extendPast b E l β₁ β₂ w.1 _ _
  have ea : ∀ w, ap (π w) = nearL b E W l β₁ w.1 (g₁ w.2) := fun w =>
    nearL_extendPast b E l β₁ w.1 _
  have ec : ∀ w, cp (π w) = nearR b E W l β₂ w.1 (g₂ w.2) := fun w =>
    nearR_extendPast b E l β₂ w.1 _
  have eX : ∀ w, Xp (π w) = pathX b E W l w.1 := fun w => pathX_extendPast b E l w.1
  -- the passive pasts
  have hpas : ∀ᵐ p ∂μP, (passiveY (Xp p)).PosSemidef := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := pastLaw W l b) (ν := ν)).ae
      (ae_pastLaw_hermitian W l b)
    filter_upwards [h] with p hp
    exact passiveY_pathX_extendPast hb hE1 hE2 hp
  -- the update on the product space
  have hupd' : ∀ᵐ w ∂μΩ, rawForm b E W (l + 1) β₁ β₂ w.1 (g₁ w.2) (g₂ w.2) =
      xp (π w) + bilinear (ap (π w)) (D (π w) (φ w)) (cp (π w)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b) (ν := ν)).ae
      hupd] with w hw
    rw [hw, ex, ea, ec]
    simp only [D, eX, stepDelta, φ]
  set G : (PastSample W l × Γ) × LayerSample W .oneBlockOnePort → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((‖xp z.1 + bilinear (ap z.1) (D z.1 z.2) (cp z.1)‖ ^ 2) ^ (2 * m))
  have hGm : Measurable G := by
    have := measurable_bilinear_jt (hap.comp measurable_fst) hDm (hcp.comp measurable_fst)
    have h2 := (hxp.comp measurable_fst).add this
    exact ((h2.norm.pow_const 2).pow_const _).ennreal_ofReal
  have hstep := abstract_step μP (freshLaw W b) xp ap cp D hm hW hGm.aemeasurable
    (hpas.mono fun p hp => hI _ hp)
    (fun p => Cf * ((Real.sqrt W)⁻¹ + jetDistance0 b E (Xp p)) * vecNorm (ap p) * vecNorm (cp p))
    (fun p => by have := vecNorm_nonneg (ap p); have := vecNorm_nonneg (cp p)
                 have : 0 ≤ jetDistance0 b E (Xp p) := norm_nonneg _
                 positivity)
    (hpas.mono fun p hp => hF _ hp (ap p) (cp p))
  calc ∫⁻ w, ENNReal.ofReal ((‖rawForm b E W (l + 1) β₁ β₂ w.1 (g₁ w.2) (g₂ w.2)‖ ^ 2) ^ (2 * m))
        ∂μΩ = ∫⁻ w, G (π w, φ w) ∂μΩ :=
          lintegral_congr_ae (hupd'.mono fun w hw => by dsimp only; rw [hw])
    _ = ∫⁻ z, G z ∂(μP.prod (freshLaw W b)) := by rw [← hmap, lintegral_map hGm (hπ.prodMk hφ)]
    _ ≤ _ := hstep
    _ ≤ _ := by
        rw [← hmapπ]
        refine (lintegral_map_le _ hπ.aemeasurable).trans (le_of_eq ?_)
        refine lintegral_congr fun w => ?_
        simp only [ex, ea, ec, eX, D]

end BlockBand.SourceProcess.RawTag
