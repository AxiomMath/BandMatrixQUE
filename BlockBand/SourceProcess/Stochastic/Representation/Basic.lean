module
public import BlockBand.SourceProcess.Stochastic.Levy.Main
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Representation of martingale-problem solutions: basic tools

Setting: an arbitrary measurable space `(Ω, m₀)` with a finite measure `Q` and a raw filtration
`𝓖 : Filtration ℝ≥0 m₀` (no usual conditions).

* `measurable_iic_embed_pred`, `isStronglyProgressive_of_predictable`: raw predictable functions
  of `(s, ω)` are strongly progressive processes (Lévy's characterization needs a progressive
  process; the predictable version of an adapted process is one).
* `predVersion_congr`: `predVersion Y (s, ω)` only depends on the values of `Y` at the dyadic
  left points of `s`; `predVersion_zero`: it vanishes at `s = 0`.
* `martingale_glue`: martingales `Y n` that are consistent a.s. at times `t ≤ n` glue to the
  martingale `t ↦ Y ⌈t⌉₊ t` (horizon gluing).
* `martingale_ae_eq_of_terminal`: two martingales with a.s. equal values at `T` agree a.s. at
  every `t ≤ T`.
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.Stochastic.Integral (leftPoint)
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The embedding `Iic t × Ω → ℝ × Ω` is measurable from `B(Iic t) ⊗ 𝓖_t` into the raw
predictable σ-algebra. -/
theorem measurable_iic_embed_pred (𝓖 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    Measurable[Subtype.instMeasurableSpace.prod (𝓖 t), predictableSpace (toCF 𝓖)]
      fun p : Set.Iic t × Ω => (((p.1 : ℝ≥0) : ℝ), p.2) := by
  let _ : MeasurableSpace (Set.Iic t × Ω) := Subtype.instMeasurableSpace.prod (𝓖 t)
  have hc : Measurable fun r : Set.Iic t => ((r : ℝ≥0) : ℝ) :=
    measurable_subtype_coe.coe_nnreal_real
  refine measurable_generateFrom ?_
  rintro S (⟨A, hA, rfl⟩ | ⟨s, u, A, hA, rfl⟩)
  · have he : (fun p : Set.Iic t × Ω => (((p.1 : ℝ≥0) : ℝ), p.2)) ⁻¹' (({0} : Set ℝ) ×ˢ A) =
        ((fun r : Set.Iic t => ((r : ℝ≥0) : ℝ)) ⁻¹' {0}) ×ˢ A := by
      ext p; simp
    rw [he]
    exact (hc (measurableSet_singleton 0)).prod (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) _ hA)
  · by_cases hst : s ≤ t
    · have he : (fun p : Set.Iic t × Ω => (((p.1 : ℝ≥0) : ℝ), p.2)) ⁻¹' (Ioc (s : ℝ) u ×ˢ A) =
          ((fun r : Set.Iic t => ((r : ℝ≥0) : ℝ)) ⁻¹' Ioc (s : ℝ) u) ×ˢ A := by
        ext p; simp
      rw [he]
      exact (hc measurableSet_Ioc).prod (𝓖.mono hst _ hA)
    · have he : (fun p : Set.Iic t × Ω => (((p.1 : ℝ≥0) : ℝ), p.2)) ⁻¹' (Ioc (s : ℝ) u ×ˢ A) =
          ∅ := by
        ext p
        simp only [mem_preimage, mem_prod, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
        intro h1 _
        have hp : ((p.1 : ℝ≥0) : ℝ) ≤ t := NNReal.coe_le_coe.2 p.1.2
        have : (t : ℝ) < s := NNReal.coe_lt_coe.2 (lt_of_not_ge hst)
        linarith
      rw [he]
      exact MeasurableSet.empty

/-- **Raw predictable functions are strongly progressive processes.** -/
theorem isStronglyProgressive_of_predictable {E : Type*} [TopologicalSpace E]
    (𝓖 : Filtration ℝ≥0 mΩ) {f : ℝ × Ω → E}
    (hf : StronglyMeasurable[predictableSpace (toCF 𝓖)] f) :
    IsStronglyProgressive 𝓖 fun t ω => f ((t : ℝ), ω) := fun t =>
  hf.comp_measurable (measurable_iic_embed_pred 𝓖 t)

variable {d : ℕ}

omit mΩ in
/-- `predVersion Y (s, ω)` depends only on `Y` at the dyadic left points of `s`. -/
theorem predVersion_congr {Y Y' : ℝ≥0 → Ω → Fin d → ℝ} {p : ℝ × Ω}
    (h : ∀ n, Y (leftPoint n p.1) p.2 = Y' (leftPoint n p.1) p.2) :
    predVersion Y p = predVersion Y' p := by
  funext i
  simp only [predVersion, compositeVersion]
  congr 1
  funext n
  simp only [leftSample, preComposite, Set.indicator, h n]

omit mΩ in
theorem predVersion_zero (Y : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    predVersion Y ((0 : ℝ), ω) = 0 := by
  funext i
  exact compositeVersion_of_nonpos _ _ _ (le_refl (0 : ℝ))

omit mΩ in
/-- Dyadic left points are dyadic: `leftPoint n s = k 2⁻ⁿ`. -/
theorem leftPoint_eq_mul (n : ℕ) (s : ℝ) :
    ∃ k : ℕ, leftPoint n s = (k : ℝ≥0) * BlockBand.SourceProcess.Stochastic.Integral.dyadicStep n :=
  ⟨_, rfl⟩

/-- The predictable version of an adapted process is a strongly progressive process. -/
theorem isStronglyProgressive_predVersion (𝓖 : Filtration ℝ≥0 mΩ) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) :
    IsStronglyProgressive 𝓖 fun t ω => predVersion Y ((t : ℝ), ω) :=
  isStronglyProgressive_of_predictable 𝓖 (stronglyMeasurable_predVersion 𝓖 hY)

variable {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- Two martingales with a.s. equal values at `T` agree a.s. at every `t ≤ T`. -/
theorem martingale_ae_eq_of_terminal {M M' : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 Q)
    (hM' : Martingale M' 𝓖 Q) {t T : ℝ≥0} (ht : t ≤ T) (hT : M T =ᵐ[Q] M' T) :
    M t =ᵐ[Q] M' t :=
  (hM.2 t T ht).symm.trans ((condExp_congr_ae hT).trans (hM'.2 t T ht))

/-- **Horizon gluing of martingales.** -/
theorem martingale_glue {Y : ℕ → ℝ≥0 → Ω → ℝ} (hY : ∀ n, Martingale (Y n) 𝓖 Q)
    (hcons : ∀ n n' : ℕ, n ≤ n' → ∀ t : ℝ≥0, t ≤ n → Y n' t =ᵐ[Q] Y n t) :
    Martingale (fun t => Y ⌈t⌉₊ t) 𝓖 Q := by
  refine ⟨fun t => (hY _).1 t, fun s t hst => ?_⟩
  have h1 := (hY ⌈t⌉₊).2 s t hst
  have h2 := hcons ⌈s⌉₊ ⌈t⌉₊ (Nat.ceil_mono hst) s (Nat.le_ceil s)
  exact h1.trans h2

theorem glue_ae_eq {Y : ℕ → ℝ≥0 → Ω → ℝ}
    (hcons : ∀ n n' : ℕ, n ≤ n' → ∀ t : ℝ≥0, t ≤ n → Y n' t =ᵐ[Q] Y n t) (n : ℕ) {t : ℝ≥0}
    (ht : t ≤ n) : Y ⌈t⌉₊ t =ᵐ[Q] Y n t :=
  (hcons ⌈t⌉₊ n (Nat.ceil_le.2 ht) t (Nat.le_ceil t)).symm

end BlockBand.SourceProcess.Stochastic.Representation
