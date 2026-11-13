module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyPalm
public import BlockBand.Endpoints.Normalization.Normalizer

/-!
# The physical lead-profile theorem: removal of the exterior weight

**Main result** (`physicalOneMark_window_comparison`). Fixed first: `b ∈ (0,1/2)`, a
bulk `E`, `T`, a window `w` (`IsWindow`: continuous, compactly supported, `w ≥ 0`, `∫ w = 1`),
`Φ ∈ C_b(𝒫(𝕋))`, a bound `M > 0` and `ε > 0`. There is `W₀` such that for every admissible `p`
with this `b`, `W ≥ W₀`, `n ≤ TW`, every `FiniteRealization R`, every one-block splitting law
`Pω` of block `0`, every measurable block frame `U` and **every** jointly measurable
`A : ℝ → BlockState → ℝ` with `|A| ≤ M` which represents the normalized angular average, i.e.
`Pω`-a.s. for all `e`,
`Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[Ψ(p(v,e))] = Z₀(e) · A(e, ω)`, `Ψ(q) = n⁻¹ Σ_s Φ(ℛ_{s/n} ν(q))`,
one has
`|E Σ_α w(u_α)Φ(ν_α) - ∫ w(u) ∫ A(e(u), ω) dPω du| ≤ M ε`.

The representing `A` is the fresh-Palm average `palmExpect` of `Ψ ∘ p(·,e)`
(`blockSector_ratio_eq_palmExpect`); its identification, joint measurability and the bound
`|A| ≤ ‖Φ‖` are hypotheses of this lemma, not additional model hypotheses (they are statements
about an explicit function).

**Proof.** The exact block-0 Palm formula (`physicalOneMark_eq_oneBlockPalm`); the window factor `w(u(e))` is pulled
out of the angular measure (`blockSectorFiberReal_const_mul`); the representation turns the
integrand into `n w(u(e)) Z₀(e) A(e, ω)`; by Fubini (dominated by `nMCW w(u(e))`, using
`OneBlockPalm.upper` on Hermitian exteriors) and `withDensity` this is `∫ A d𝔪⁰_W`; then
`OneBlockNormalizerContract.tv` applied to `F = A(e(u), ω)/M`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Layers
open scoped BoundedContinuousFunction ENNReal

variable (p : Parameters)

/-- The profile observable `Ψ(q) = n⁻¹ Σ_s Φ(ℛ_{s/n} ν(q))` read on reconstructed masses. -/
def leadReconObservable (Φ : MassProfile →ᵇ ℝ) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ)
    (v : BlockSite p k → ℂ) : ℝ :=
  leadProfileRotationAverage p Φ (massVectorProfile p (blockReconMass p k ω e v))

/-- Constants come out of the one-block angular measure. -/
theorem blockSectorFiberReal_const_mul (k : ZMod p.n)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) (c : ℝ) (g : (BlockSite p k → ℂ) → ℝ) :
    blockSectorFiberReal p k U ω e ℓ (fun v => c * g v) =
      c * blockSectorFiberReal p k U ω e ℓ g := by
  classical
  unfold blockSectorFiberReal
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [← integral_const_mul]
  congr 1
  funext G'
  ring

theorem microEnergy_microCoord {E : ℝ} (h1 : -2 < E) (h2 : E < 2) (e : ℝ) :
    microEnergy p E (microCoord p E e) = e := by
  have hρ := semicircleDensity_pos h1 h2
  have hN : (0 : ℝ) < p.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.N)
  unfold microEnergy microCoord
  field_simp
  ring

theorem integrable_window_microCoord {E : ℝ} (h1 : -2 < E) (h2 : E < 2) {w : ℝ → ℝ}
    (hw : IsWindow w) : Integrable (fun e => w (microCoord p E e)) volume := by
  have hρ := semicircleDensity_pos h1 h2
  have hN : (0 : ℝ) < p.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.N)
  have hint : Integrable w volume := hw.1.integrable_of_hasCompactSupport hw.2.1
  have := (hint.comp_mul_left' (R := (p.N : ℝ) * Parameters.semicircleDensity E)
    (by positivity)).comp_sub_right E
  simpa only [microCoord] using this

/-- **Assembly step 1b of the physical lead-profile theorem**, from `OneBlockPalmContract` and
`OneBlockNormalizerContract`. See the module docstring.
-/
theorem physicalOneMark_window_comparison (hPalm : OneBlockPalmContract)
    (hNorm : OneBlockNormalizerContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (h1 : -2 < E) (h2 : E < 2) (T : ℝ) (w : ℝ → ℝ) (hw : IsWindow w) (Φ : MassProfile →ᵇ ℝ)
    (M : ℝ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ (p : Parameters), p.b = b → W₀ ≤ p.W → (p.n : ℝ) ≤ T * p.W →
      ∀ (R : FiniteRealization p) (Pω : Measure (BlockState p 0)),
      IsBlockSplitting p 0 R.model Pω →
      ∀ (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ),
      IsBlockFrame p 0 U →
      ∀ A : ℝ → BlockState p 0 → ℝ, Measurable (Function.uncurry A) → (∀ e ω, |A e ω| ≤ M) →
      (∀ᵐ ω ∂Pω, ∀ e, ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p 0 U ω e ℓ (leadReconObservable p Φ 0 ω e) =
        (blockNormalizer p 0 U ω e).toReal * A e ω) →
        |physicalOneMark R E w Φ -
            ∫ x, A (microEnergy p E x.1) x.2 ∂priorWindowMeasure Pω w| ≤ M * ε := by
  obtain ⟨W₀, hW₀⟩ := hNorm.tv b hb hb' E h1 h2 T w hw ε hε
  obtain ⟨C, hC⟩ := hPalm.upper b hb hb'
  refine ⟨W₀, fun p hpb hW hn R Pω hsplit U hU A hAm hAb hAeq => ?_⟩
  have hprob := isProbabilityMeasure_blockSplitting p R.model 0 hsplit
  have hZB : ∀ᵐ ω ∂Pω, ∀ e, blockNormalizer p 0 U ω e ≤ ENNReal.ofReal (C * p.W) := by
    filter_upwards [ae_blockSplit_isHermitian p R.model 0 hsplit] with ω hω
    exact hC p hpb 0 U hU ω hω
  have hw0 : ∀ u, 0 ≤ w u := hw.2.2.1
  -- the density of the exterior window measure
  set dens : ℝ × BlockState p 0 → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) * blockNormalizer p 0 U x.2 x.1
  have hdens_meas : Measurable dens :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (hw.1.measurable.comp ((measurable_microCoord (p := p) E).comp measurable_fst)))).mul
      (measurable_blockNormalizer_joint p 0 U hU.1)
  have hZBprod : ∀ᵐ x ∂(volume.prod Pω), ∀ e,
      blockNormalizer p 0 U x.2 e ≤ ENNReal.ofReal (C * p.W) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := Pω)).ae
      (p := fun ω => ∀ e, blockNormalizer p 0 U ω e ≤ ENNReal.ofReal (C * p.W)) hZB
  have hdens_fin : ∀ᵐ x ∂(volume.prod Pω), dens x < ∞ := by
    filter_upwards [hZBprod] with x hx
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt (hx x.1) ENNReal.ofReal_lt_top)
  have hdens_toReal : ∀ x, (dens x).toReal =
      (p.n : ℝ) * w (microCoord p E x.1) * (blockNormalizer p 0 U x.2 x.1).toReal := by
    intro x
    simp only [dens, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (hw0 _))]
  -- the exact Palm formula and the representation
  have h1a := physicalOneMark_eq_oneBlockPalm p hPalm h1 h2 hw.1 hw.2.1 Φ R Pω hsplit U hU
  have hrep : physicalOneMark R E w Φ =
      ∫ ω, ∫ e : ℝ, (dens (e, ω)).toReal * A e ω ∂volume ∂Pω := by
    rw [h1a, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hAeq] with ω hω
    rw [← integral_const_mul]
    congr 1
    funext e
    have hpull : ∑ ℓ ∈ Finset.range p.W, blockSectorFiberReal p 0 U ω e ℓ
        (fun v => leadPalmObservable p E w Φ e (blockReconMass p 0 ω e v)) =
        w (microCoord p E e) * ∑ ℓ ∈ Finset.range p.W,
          blockSectorFiberReal p 0 U ω e ℓ (leadReconObservable p Φ 0 ω e) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      exact blockSectorFiberReal_const_mul p 0 U ω e ℓ _ _
    rw [hpull, hω e, hdens_toReal]
    ring
  -- integrability on the product
  have hint : Integrable (fun x : ℝ × BlockState p 0 => (dens x).toReal * A x.1 x.2)
      (volume.prod Pω) := by
    have hg : Integrable (fun x : ℝ × BlockState p 0 =>
        (p.n : ℝ) * (max C 0 * p.W) * M * w (microCoord p E x.1)) (volume.prod Pω) :=
      ((integrable_window_microCoord p h1 h2 hw).const_mul _).comp_fst Pω
    refine hg.mono' ((ENNReal.measurable_toReal.comp hdens_meas).mul hAm).aestronglyMeasurable ?_
    filter_upwards [hZBprod] with x hx
    rw [Real.norm_eq_abs, abs_mul, hdens_toReal, abs_of_nonneg (by
      have := hw0 (microCoord p E x.1); positivity)]
    have hZ : (blockNormalizer p 0 U x.2 x.1).toReal ≤ max C 0 * p.W := by
      have hWp : (0 : ℝ) ≤ p.W := by positivity
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((hx x.1).trans
        (ENNReal.ofReal_le_ofReal ?_))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hWp
    have hwx := hw0 (microCoord p E x.1)
    have hAx := hAb x.1 x.2
    calc (p.n : ℝ) * w (microCoord p E x.1) * (blockNormalizer p 0 U x.2 x.1).toReal *
          |A x.1 x.2| ≤ (p.n : ℝ) * w (microCoord p E x.1) * (max C 0 * p.W) * M := by
          gcongr
      _ = _ := by ring
  have hwin : ∫ x, A x.1 x.2 ∂blockWindowMeasure p 0 U Pω E w =
      physicalOneMark R E w Φ := by
    rw [hrep]
    unfold blockWindowMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas hdens_fin]
    simp only [smul_eq_mul]
    exact integral_prod_symm _ hint
  -- the normalizer comparison for `F = A(e(u), ω)/M`
  have hF : Measurable (fun x : ℝ × BlockState p 0 => A (microEnergy p E x.1) x.2 / M) := by
    have : Measurable (fun x : ℝ × BlockState p 0 => (microEnergy p E x.1, x.2)) := by
      refine Measurable.prodMk ?_ measurable_snd
      unfold microEnergy
      exact measurable_const.add (measurable_fst.div_const _)
    exact (hAm.comp this).div_const M
  have hF1 : ∀ x : ℝ × BlockState p 0, |A (microEnergy p E x.1) x.2 / M| ≤ 1 := by
    intro x
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact hAb _ _
  have htv := hW₀ p hpb hW hn R.model 0 Pω hsplit U hU _ hF hF1
  simp only [microEnergy_microCoord p h1 h2] at htv
  rw [integral_div, integral_div, hwin, ← sub_div, abs_div, abs_of_pos hM,
    div_le_iff₀ hM] at htv
  linarith

end BlockBand.Endpoints.Normalization
