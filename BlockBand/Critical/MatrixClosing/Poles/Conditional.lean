module

public import BlockBand.Critical.MatrixClosing.Poles.Identify
public import BlockBand.Critical.MatrixClosing.Poles.SmallMark

/-!
# Matrix closing, poles clause: the conditional Laplace comparison for the marked atoms

*Law.* `G ~ GUE_N(c/N)` on `Fin N`, independent uniform phases (`phaseVectorLaw`), as in
`RelativeMixedVectorsDecorated`.

* `measurable_markRes`, `measurable_exp_atomSum_markAtoms`, `ae_norm_phase_eq_one`.
* `markedIntegrand_bounds`: on simple spectrum,
  `0 ≤ exp(-atomSum φ) - M(canonTest φ) ≤ 1 - M(ψ)` after the phase average.
* `exists_radius_bound`: support radius and bound of `φ ∈ C_c(ℝ × Matrix)`.
* **`conditional_laplace`** (`DecoratedContinuousClause`, `r ≥ 1`): uniformly over `N ≥ N₀`, `F`
  in the fresh class, frames with `|(V^*ΓV - I)_{ij}| ≤ ε` and `|ρ - ρ_F| ≤ ε`,
  `|E_G exp(-atomSum φ(markAtoms ρ E V (F + G))) - decoratedSineLaplace r (canonTest φ)| ≤ δ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.Herglotz BlockBand.Critical.WeightedDensity

variable {N r : ℕ}

/-!
## Measurability of the marked atoms
-/

theorem markVec_eq_relativeMark (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (ℓ : Fin N) : markVec V K ℓ = relativeMark V K (fun _ => 1) ℓ := by
  rw [relativeMark_eq_smul, one_smul]

theorem measurable_markRes (V : Matrix (Fin N) (Fin r) ℂ) (ℓ : Fin N) :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ => markRes V K ℓ := by
  have h : Measurable fun K : Matrix (Fin N) (Fin N) ℂ => markVec V K ℓ := by
    simp_rw [markVec_eq_relativeMark]
    have e : (fun K : Matrix (Fin N) (Fin N) ℂ => relativeMark V K (fun _ => 1) ℓ) =
        (fun p : Matrix (Fin N) (Fin N) ℂ × (Fin N → ℂ) => relativeMark V p.1 p.2 ℓ) ∘
          fun K => (K, fun _ => (1 : ℂ)) := rfl
    rw [e]
    exact (measurable_relativeMark V ℓ).comp (measurable_id.prodMk measurable_const)
  exact continuous_canonicalResidue.measurable.comp h

theorem measurable_exp_atomSum_markAtoms (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    Measurable fun K : Matrix (Fin N) (Fin N) ℂ =>
      Real.exp (-(markAtoms ρ E V K).atomSum φ) := by
  have hp : ∀ ℓ, Measurable fun K : Matrix (Fin N) (Fin N) ℂ => markPts ρ E K ℓ := fun ℓ =>
    measurable_const.mul
      ((BlockBand.Coarea.FreshPalm.measurable_freshEigenvalue ℓ).sub measurable_const)
  have hr : ∀ ℓ, Measurable fun K : Matrix (Fin N) (Fin N) ℂ => markRes V K ℓ :=
    measurable_markRes V
  have heq : (fun K : Matrix (Fin N) (Fin N) ℂ => (markAtoms ρ E V K).atomSum φ) =
      fun K => ∑ ℓ, (fiberCard (markPts ρ E K) ℓ)⁻¹ *
        (if fiberRes (markPts ρ E K) (markRes V K) ℓ = 0 then 0 else
          φ (markPts ρ E K ℓ, fiberRes (markPts ρ E K) (markRes V K) ℓ)) := by
    funext K
    exact atomSum_ofAtoms _ _ _ _ _ φ
  refine Real.measurable_exp.comp (Measurable.neg ?_)
  rw [heq]
  refine Finset.measurable_sum _ fun ℓ _ => ?_
  refine (measurable_fiberCard hp ℓ).inv.mul ?_
  exact Measurable.ite (measurableSet_matrix_eq_zero (measurable_fiberRes hp hr ℓ))
    measurable_const (φ.continuous.measurable.comp ((hp ℓ).prodMk (measurable_fiberRes hp hr ℓ)))

/-!
## Phases are unimodular
-/

theorem ae_norm_phase_eq_one : ∀ᵐ θ ∂phaseVectorLaw N, ∀ ℓ, ‖θ ℓ‖ = 1 := by
  rw [ae_all_iff]
  intro ℓ
  have h1 : ∀ᵐ z ∂phaseLaw, ‖z‖ = 1 := by
    have hm : Measurable fun θ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) :=
      (Complex.continuous_exp.comp (by fun_prop)).measurable
    rw [phaseLaw, ae_map_iff hm.aemeasurable (measurableSet_eq_fun measurable_norm
      measurable_const)]
    refine Eventually.of_forall fun θ => ?_
    have : 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hmp : MeasurePreserving (fun θ : Fin N → ℂ => θ ℓ) (phaseVectorLaw N) phaseLaw :=
    measurePreserving_eval (fun _ : Fin N => phaseLaw) ℓ
  exact hmp.quasiMeasurePreserving.ae h1

/-!
## The pointwise comparison after the phase average
-/

/-- On simple spectrum: `0 ≤ exp(-atomSum φ) - M(canonTest φ) ≤ 1 - M(ψ)`, `M` the
phase-averaged marked integrand, for every nonnegative continuous `ψ` with `φ(x,0) ≤ ψ(x,0)`. -/
theorem markedIntegrand_bounds {ρ E : ℝ} {V : Matrix (Fin N) (Fin r) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K) (hN : 0 < N) (hρ : ρ ≠ 0)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) (hφ : ∀ p, 0 ≤ φ p)
    {ψ : ℝ × (Fin r → ℂ) → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ p, 0 ≤ ψ p)
    (hψ : ∀ x, φ (x, 0) ≤ ψ (x, 0)) :
    0 ≤ Real.exp (-(markAtoms ρ E V K).atomSum φ) - markedIntegrand ρ E V (canonTest φ) K ∧
      Real.exp (-(markAtoms ρ E V K).atomSum φ) - markedIntegrand ρ E V (canonTest φ) K ≤
        1 - markedIntegrand ρ E V ψ K := by
  set a := Real.exp (-(markAtoms ρ E V K).atomSum φ)
  set g1 : (Fin N → ℂ) → ℝ := fun θ => Real.exp (-∑ ℓ : Fin N,
    canonTest φ ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E), relativeMark V K θ ℓ))
  set g2 : (Fin N → ℂ) → ℝ := fun θ => Real.exp (-∑ ℓ : Fin N,
    ψ ((N : ℝ) * ρ * (freshEigenvalue K ℓ - E), relativeMark V K θ ℓ))
  have hb : ∀ (g : (Fin N → ℂ) → ℝ), Measurable g → (∀ θ, 0 ≤ g θ ∧ g θ ≤ 1) →
      Integrable g (phaseVectorLaw N) := fun g hg hb =>
    Integrable.of_bound hg.aestronglyMeasurable 1 (Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb θ).1]; exact (hb θ).2)
  have hexp : ∀ s : ℝ, 0 ≤ s → 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 := fun s hs =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (neg_nonpos.2 hs)⟩
  have hi1 : Integrable g1 (phaseVectorLaw N) :=
    hb g1 (measurable_markedIntegrand_inner (canonTest φ).continuous ρ E V K) fun θ =>
      hexp _ (Finset.sum_nonneg fun ℓ _ => hφ _)
  have hi2 : Integrable g2 (phaseVectorLaw N) :=
    hb g2 (measurable_markedIntegrand_inner hψc ρ E V K) fun θ =>
      hexp _ (Finset.sum_nonneg fun ℓ _ => hψ0 _)
  have e1 : a - markedIntegrand ρ E V (canonTest φ) K = ∫ θ, (a - g1 θ) ∂phaseVectorLaw N := by
    rw [integral_sub (integrable_const a) hi1, integral_const, probReal_univ, one_smul]; rfl
  have e2 : 1 - markedIntegrand ρ E V ψ K = ∫ θ, (1 - g2 θ) ∂phaseVectorLaw N := by
    rw [integral_sub (integrable_const 1) hi2, integral_const, probReal_univ, one_smul]; rfl
  have hpt : ∀ᵐ θ ∂phaseVectorLaw N, 0 ≤ a - g1 θ ∧ a - g1 θ ≤ 1 - g2 θ := by
    filter_upwards [ae_norm_phase_eq_one] with θ hθ
    exact exp_atomSum_sub_bound hK hN hρ hθ φ hφ ψ hψ0 hψ
  rw [e1, e2]
  exact ⟨integral_nonneg_of_ae (hpt.mono fun θ h => h.1),
    integral_mono_ae ((integrable_const a).sub hi1) ((integrable_const 1).sub hi2)
      (hpt.mono fun θ h => h.2)⟩

/-!
## Support radius and bound of a test
-/

theorem exists_radius_bound (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    ∃ R t : ℝ, 0 ≤ R ∧ 0 ≤ t ∧ (∀ x M, R < |x| → φ (x, M) = 0) ∧ ∀ p, φ p ≤ t := by
  obtain ⟨R0, hR0⟩ := ((φ.hasCompactSupport.isCompact.image
    (continuous_abs.comp continuous_fst))).bddAbove
  obtain ⟨t0, ht0⟩ := (φ.continuous.bddAbove_range_of_hasCompactSupport φ.hasCompactSupport)
  refine ⟨max R0 0, max t0 0, le_max_right _ _, le_max_right _ _, fun x M hx => ?_,
    fun p => (ht0 ⟨p, rfl⟩).trans (le_max_left _ _)⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR0 ⟨(x, M), hmem, rfl⟩
  simp only [Function.comp_apply] at this
  linarith [le_max_left R0 0]

/-!
## The conditional Laplace comparison
-/

/-- **The conditional Laplace comparison, conditional on the deformation.** From the enlarged
decorated clause (`DecoratedContinuousClause`, which follows from `RelativeMixedVectorsDecorated`): for
fixed constants `A, c, r₀, s₀, v₀`, a positive rank `r`, a nonnegative test
`φ ∈ C_c(ℝ × Matrix)` and `δ > 0`, there are `ε > 0`, `N₀` such that for `N ≥ N₀`, `F` in the
fresh class at `(c, E)`, every frame `V` with `|(V^*ΓV - I)_{ij}| ≤ ε` and every scale
`ρ` with `|ρ - ρ_F| ≤ ε`, the `GUE_N(c/N)`-average of `exp(-atomSum φ)` of the marked atoms of
`F + G` (poles `Nρ(λ_ℓ - E)`, residues `π⁻¹z_ℓz_ℓ^*` with zero residues dropped) is within `δ`
of `decoratedSineLaplace r (canonTest φ)`. The atoms with zero residue are paid by the
small-mark count test. -/
theorem conditional_laplace (hDC : DecoratedContinuousClause) {A c r₀ s₀ v₀ : ℝ}
    (hFC : FreshConstants c r₀ s₀ v₀) (hr : 0 < r)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) (hφ : ∀ p, 0 ≤ φ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      ∀ V : Matrix (Fin N) (Fin r) ℂ,
        (∀ i j : Fin r, ‖(Vᴴ * freshGamma F c E * V - (1 : Matrix (Fin r) (Fin r) ℂ)) i j‖ ≤ ε) →
      ∀ ρ : ℝ, |ρ - unfoldingDensity F c E| ≤ ε →
        |∫ G, Real.exp (-(markAtoms ρ E V (F + G)).atomSum φ)
            ∂gueMeasure (Fin N) (Real.toNNReal (c / N)) -
          decoratedSineLaplace r (canonTest φ)| ≤ δ := by
  obtain ⟨R, t, hR0, ht0, hφR, hφt⟩ := exists_radius_bound φ
  obtain ⟨n, hn⟩ := exists_smallMarkTest hr R ht0 (η := δ / 4) (by linarith)
  set ψ := smallMarkTest (r := r) R t n
  have hψ0 : ∀ p, 0 ≤ ψ p := smallMarkTest_nonneg R ht0 n
  have hψ : ∀ x, φ (x, 0) ≤ ψ (x, 0) := by
    intro x
    rw [smallMarkTest_zero]
    by_cases hx : |x| ≤ R
    · rw [cutBump_eq_one hx, mul_one]; exact hφt _
    · rw [hφR x 0 (lt_of_not_ge hx)]; exact mul_nonneg ht0 (cutBump_nonneg R x)
  obtain ⟨ε₁, hε₁, N₁, h₁⟩ := hDC A c r₀ s₀ v₀ hFC r (canonTest φ) (fun p => hφ _) (δ / 4)
    (by linarith)
  obtain ⟨ε₂, hε₂, N₂, h₂⟩ := hDC A c r₀ s₀ v₀ hFC r ψ hψ0 (δ / 4) (by linarith)
  have hc : 0 < c := hFC.1
  have hv₀ : 0 < v₀ := hFC.2.2.2.2.2
  set ε := min (min ε₁ ε₂) (v₀ / (2 * Real.pi))
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (div_pos hv₀ (by positivity))
  refine ⟨ε, hε, max (max N₁ N₂) 1, fun N hN F E hF V hV ρ hρ => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hε1 : ε ≤ ε₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρF := unfoldingDensity_ge hFC hF
  have hρpos : 0 < ρ := by
    have h1 : ε ≤ v₀ / (2 * Real.pi) := min_le_right _ _
    have h2 : v₀ / Real.pi = 2 * (v₀ / (2 * Real.pi)) := by field_simp
    have h3 : 0 < v₀ / (2 * Real.pi) := div_pos hv₀ (by positivity)
    linarith [(abs_le.1 hρ).1]
  have hA1 := h₁ N hN1 F E hF V (fun i j => (hV i j).trans hε1) ρ (hρ.trans hε1)
  have hA2 := h₂ N hN2 F E hF V (fun i j => (hV i j).trans hε2) ρ (hρ.trans hε2)
  set ν := gueMeasure (Fin N) (Real.toNNReal (c / N))
  have htpos : 0 < Real.toNNReal (c / N) :=
    Real.toNNReal_pos.2 (div_pos hc (by exact_mod_cast hNpos))
  have hsimple := ae_simpleSpectrum_add_gue hF.1 htpos
  set a : Matrix (Fin N) (Fin N) ℂ → ℝ :=
    fun G => Real.exp (-(markAtoms ρ E V (F + G)).atomSum φ)
  set m1 : Matrix (Fin N) (Fin N) ℂ → ℝ := fun G => markedIntegrand ρ E V (canonTest φ) (F + G)
  set m2 : Matrix (Fin N) (Fin N) ℂ → ℝ := fun G => markedIntegrand ρ E V ψ (F + G)
  have hia : Integrable a ν := by
    refine Integrable.of_bound
      ((measurable_exp_atomSum_markAtoms ρ E V φ).comp (measurable_const_add F)).aestronglyMeasurable
      1 (Eventually.of_forall fun G => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (atomSum_nonneg _ hφ))
  have hi1 : Integrable m1 ν :=
    integrable_markedIntegrand (canonTest φ).continuous (fun p => hφ _) ρ E V F ν
  have hi2 : Integrable m2 ν := integrable_markedIntegrand ψ.continuous hψ0 ρ E V F ν
  have hpt : ∀ᵐ G ∂ν, 0 ≤ a G - m1 G ∧ a G - m1 G ≤ 1 - m2 G := by
    filter_upwards [hsimple] with G hG
    exact markedIntegrand_bounds hG hNpos hρpos.ne' φ hφ ψ.continuous hψ0 hψ
  have hlo : 0 ≤ ∫ G, a G ∂ν - ∫ G, m1 G ∂ν := by
    rw [← integral_sub hia hi1]
    exact integral_nonneg_of_ae (hpt.mono fun G h => h.1)
  have hhi : ∫ G, a G ∂ν - ∫ G, m1 G ∂ν ≤ 1 - ∫ G, m2 G ∂ν := by
    rw [← integral_sub hia hi1]
    have : 1 - ∫ G, m2 G ∂ν = ∫ G, (1 - m2 G) ∂ν := by
      rw [integral_sub (integrable_const 1) hi2, integral_const, probReal_univ, one_smul]
    rw [this]
    exact integral_mono_ae (hia.sub hi1) ((integrable_const 1).sub hi2) (hpt.mono fun G h => h.2)
  change |∫ G, a G ∂ν - decoratedSineLaplace r (canonTest φ)| ≤ δ
  have hA1' : |∫ G, m1 G ∂ν - decoratedSineLaplace r (canonTest φ)| ≤ δ / 4 := hA1
  have hA2' : |∫ G, m2 G ∂ν - decoratedSineLaplace r ψ| ≤ δ / 4 := hA2
  have hn' : 1 - decoratedSineLaplace r ψ ≤ δ / 4 := hn
  rw [abs_le] at hA1' hA2' ⊢
  constructor <;> linarith [hA1'.1, hA1'.2, hA2'.1, hA2'.2]

end BlockBand.Critical.MatrixClosing.Poles
