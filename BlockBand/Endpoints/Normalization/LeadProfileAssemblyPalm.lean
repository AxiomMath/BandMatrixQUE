module

public import BlockBand.Endpoints.Normalization.LeadProfileRotation

/-!
# The physical lead-profile theorem: the exact block-0 Palm formula

**Main result (an exact identity, with no error term).** Fix an admissible `p`, a bulk
energy `E` (`-2 < E < 2`), a continuous compactly supported (signed) weight `w`, and
`Φ ∈ C_b(𝒫(𝕋))`. For every `FiniteRealization R`, every one-block splitting law `Pω` of block
`0` and every measurable block frame `U`:

`E Σ_α w(u_α) Φ(ν_α) = n ∫ dPω(ω) ∫ de Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[ f(e, p(v,e)) ]`,

`f(e, q) = w(Nρ(E)(e - E)) · n⁻¹ Σ_{s ∈ ℤ/n} Φ(ℛ_{s/n} ν(q))`, `ν(q) = massVectorProfile q`,
`p(v,e) = blockReconMass` (`physicalOneMark_eq_oneBlockPalm`). Measures: the exact physical law
on the left; `Pω`, Lebesgue `de` and the one-block angular measure on the right.

**Proof.** `physicalOneMark_eq_blockZeroPalm_massVector` followed by `OneBlockPalmContract.massReal` at `k = 0` for `f`, which is jointly measurable,
bounded by `sup|w| · ‖Φ‖` and vanishes for `|e| > |E| + R_w/(Nρ(E))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.Layers
open scoped BoundedContinuousFunction

variable (p : Parameters)

/-- The one-block Palm observable `f(e, q) = w(Nρ(E)(e - E)) · n⁻¹ Σ_s Φ(ℛ_{s/n} ν(q))`. -/
def leadPalmObservable (E : ℝ) (w : ℝ → ℝ) (Φ : MassProfile →ᵇ ℝ) (e : ℝ)
    (q : ZMod p.n → ℝ) : ℝ :=
  w (microCoord p E e) * leadProfileRotationAverage p Φ (massVectorProfile p q)

theorem semicircleDensity_pos {E : ℝ} (h1 : -2 < E) (h2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have : 0 < 4 - E ^ 2 := by nlinarith
  positivity

theorem measurable_leadPalmObservable (E : ℝ) {w : ℝ → ℝ} (hw : Measurable w)
    (Φ : MassProfile →ᵇ ℝ) : Measurable (Function.uncurry (leadPalmObservable p E w Φ)) := by
  unfold leadPalmObservable
  exact (hw.comp ((measurable_microCoord (p := p) E).comp measurable_fst)).mul
    ((measurable_leadProfileRotationAverage p Φ).comp
      ((measurable_massVectorProfile p).comp measurable_snd))

/-- A continuous compactly supported function is bounded and vanishes outside a ball. -/
theorem exists_bound_support_of_compact {w : ℝ → ℝ} (hc : Continuous w)
    (hs : HasCompactSupport w) :
    ∃ M R : ℝ, 0 ≤ M ∧ (∀ u, |w u| ≤ M) ∧ ∀ u, R < |u| → w u = 0 := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max M 0, R, le_max_right _ _, fun u => (by
    have := hM u; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)), ?_⟩
  intro u hu
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith

theorem isBoundedCompactEnergy_leadPalmObservable {E : ℝ} (h1 : -2 < E) (h2 : E < 2)
    {w : ℝ → ℝ} (hc : Continuous w) (hs : HasCompactSupport w) (Φ : MassProfile →ᵇ ℝ) :
    IsBoundedCompactEnergy (leadPalmObservable p E w Φ) := by
  obtain ⟨M, R, hM0, hM, hR⟩ := exists_bound_support_of_compact hc hs
  have hρ := semicircleDensity_pos h1 h2
  have hN : (0 : ℝ) < p.N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.N)
  have hκ : 0 < (p.N : ℝ) * Parameters.semicircleDensity E := mul_pos hN hρ
  refine ⟨⟨M * ‖Φ‖, fun e q => ?_⟩, ⟨|E| + |R| / ((p.N : ℝ) * Parameters.semicircleDensity E),
    fun e q he => ?_⟩⟩
  · unfold leadPalmObservable
    rw [abs_mul]
    exact mul_le_mul (hM _) (abs_leadProfileRotationAverage_le p Φ _) (abs_nonneg _) hM0
  · unfold leadPalmObservable
    rw [hR, zero_mul]
    unfold microCoord
    rw [abs_mul, abs_of_pos hκ]
    have hd : |R| / ((p.N : ℝ) * Parameters.semicircleDensity E) < |e - E| := by
      have := abs_sub_abs_le_abs_sub e E
      linarith
    have := (div_lt_iff₀' hκ).mp hd
    linarith [le_abs_self R]

/-- **Assembly step 1a of the physical lead-profile theorem.** Exact block-0 one-block Palm formula
for the physical one-mark statistic, from `OneBlockPalmContract.massReal`.
-/
theorem physicalOneMark_eq_oneBlockPalm (hPalm : OneBlockPalmContract) {E : ℝ} (h1 : -2 < E)
    (h2 : E < 2) {w : ℝ → ℝ} (hc : Continuous w) (hs : HasCompactSupport w)
    (Φ : MassProfile →ᵇ ℝ) (R : FiniteRealization p) (Pω : Measure (BlockState p 0))
    (hsplit : IsBlockSplitting p 0 R.model Pω)
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p 0 U) :
    physicalOneMark R E w Φ =
      (p.n : ℝ) * ∫ ω, ∫ e : ℝ, ∑ ℓ ∈ Finset.range p.W,
        blockSectorFiberReal p 0 U ω e ℓ
          (fun v => leadPalmObservable p E w Φ e (blockReconMass p 0 ω e v)) ∂volume ∂Pω := by
  obtain ⟨M, -, -, hM, -⟩ := exists_bound_support_of_compact hc hs
  rw [physicalOneMark_eq_blockZeroPalm_massVector p R E w hc.measurable M hM Φ]
  congr 1
  exact hPalm.massReal p R.model 0 Pω hsplit U hU (leadPalmObservable p E w Φ)
    (measurable_leadPalmObservable p E hc.measurable Φ)
    (isBoundedCompactEnergy_leadPalmObservable p h1 h2 hc hs Φ)

end BlockBand.Endpoints.Normalization
