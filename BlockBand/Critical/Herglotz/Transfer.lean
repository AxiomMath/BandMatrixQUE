module

public import BlockBand.Critical.Herglotz.Existence
public import BlockBand.Critical.Herglotz.Main

/-!
# Transfer of the Herglotz tail lemma to every realization of `𝖢_r(0)`

* Cited from the sibling module: `IsCanonicalCauchy.atZero`, a realization `C` gives the
  `IsCanonicalCauchyAtZero` realization `C₀ = C · 0`.
* `ae_eq_of_isCanonicalCauchyAtZero`: if `IsCanonicalCauchy r P Ξ C` and
  `IsCanonicalCauchyAtZero r P Ξ C₀` (same `P`, same `Ξ`), then `C₀ = C · 0` `P`-a.e.
  (uniqueness of limits in probability; the two cutoff families coincide by
  `cauchyTruncation_zero`). No uniqueness in law is needed.
* `exists_isCanonicalCauchy_ae_eq`: every `C₀` extends to a realization `C` of the whole
  function on the same space with `C₀ = C · 0` a.e. (with `exists_isCanonicalCauchy`).

Forms used by the matrix closing theorem (which needs `F_W(0) ⇒ 𝖢_r(0)`, jointly over finitely
many real middle shifts):

* `herglotzTail_of_atZero`: for every `C₀` with `IsCanonicalCauchyAtZero`, hypotheses 1–3 give a
  full realization `C` on the same space, `C₀ = C · 0` a.e., and the full joint conclusion
  `HerglotzTailConclusion` for `C` (real points and compact subsets of `{Im z > 0}`).
* `herglotzTail_eval_zero`: `F_N(0) ⇒ C₀` for every `IsCanonicalCauchyAtZero` realization.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire

variable {r : ℕ}

/-- **Same-space identification of `𝖢_r(0)`.** Law: one probability space `(Ω, P)` and one
decorated sine process `Ξ` (`IsDecoratedSineProcess`).
If `C` realizes `𝖢_r` and `C₀`
realizes the `𝖢_r(0)` from the same `Ξ`, then `C₀ = C · 0` `P`-almost everywhere: both are
limits in probability of the same symmetric cutoffs (`cauchyTruncation_zero`).
-/
theorem ae_eq_of_isCanonicalCauchyAtZero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ}
    {C₀ : Ω → Matrix (Fin r) (Fin r) ℂ} (hC : IsCanonicalCauchy r P Ξ C)
    (hC₀ : IsCanonicalCauchyAtZero r P Ξ C₀) : C₀ =ᵐ[P] fun ω => C ω 0 := by
  have hent (i j : Fin r) : (fun ω => C₀ ω i j) =ᵐ[P] fun ω => C ω 0 i j :=
    tendstoInMeasure_ae_unique (hC₀.limit i j) (hC.atZero.limit i j)
  have hall : ∀ᵐ ω ∂P, ∀ i j : Fin r, C₀ ω i j = C ω 0 i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact hent i
  filter_upwards [hall] with ω hω
  funext i j
  exact hω i j

/-- **Every realization of `𝖢_r(0)` extends.** For every `C₀` with
`IsCanonicalCauchyAtZero r P Ξ C₀` there is `C` on the same probability space with
`IsCanonicalCauchy r P Ξ C` and `C₀ = C · 0` `P`-a.e. -/
theorem exists_isCanonicalCauchy_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C₀ : Ω → Matrix (Fin r) (Fin r) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero r P Ξ C₀) :
    ∃ C : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ, IsCanonicalCauchy r P Ξ C ∧
      C₀ =ᵐ[P] fun ω => C ω 0 := by
  obtain ⟨C, hC⟩ := exists_isCanonicalCauchy hC₀.decorated
  exact ⟨C, hC, ae_eq_of_isCanonicalCauchyAtZero hC hC₀⟩

/-- Convergence in law is insensitive to changing the limit on a null set. -/
theorem tendstoInDistribution_congr_limit {ι E Ω' : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {X : ∀ i, Ω i → E} {l : Filter ι}
    {Z Z' : Ω' → E} (h : TendstoInDistribution X l Z μ μ') (hZ : Z =ᵐ[μ'] Z') :
    TendstoInDistribution X l Z' μ μ' where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := h.aemeasurable_limit.congr hZ
  tendsto := by
    have heq : (⟨μ'.map Z', inferInstance⟩ : ProbabilityMeasure E) =
        ⟨μ'.map Z, inferInstance⟩ := by
      congr 1
      exact (Measure.map_congr hZ).symm
    rw [heq]
    exact h.tendsto

/-- **The Herglotz tail lemma for a realization of `𝖢_r(0)`.** For `C₀` with
`IsCanonicalCauchyAtZero`, the lemma applies to an extension `C` on the same space whose value at
`0` is `C₀` almost surely, and whose values at the real middle shifts `x_a` are the joint limits. -/
theorem herglotzTail_of_atZero {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C₀ : Ω' → Matrix (Fin r) (Fin r) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero r P' Ξ C₀) (h : HerglotzTailHypotheses r P F P' Ξ) :
    ∃ C : Ω' → ℂ → Matrix (Fin r) (Fin r) ℂ, IsCanonicalCauchy r P' Ξ C ∧
      (C₀ =ᵐ[P'] fun ω => C ω 0) ∧ HerglotzTailConclusion r P F P' C := by
  obtain ⟨C, hC, hae⟩ := exists_isCanonicalCauchy_ae_eq hC₀
  exact ⟨C, hC, hae, herglotzTail r Ω P F Ω' P' Ξ C hC h⟩

/-- **`F_N(0) ⇒ 𝖢_r(0)` for every realization of the `𝖢_r(0)`.** Law as in
`herglotzTail_of_atZero`; for every `C₀` with `IsCanonicalCauchyAtZero r P' Ξ C₀`, hypotheses
1–3 give `F_N(0) ⇒ C₀` in law (matrix product topology).
-/
theorem herglotzTail_eval_zero {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))} {C₀ : Ω' → Matrix (Fin r) (Fin r) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero r P' Ξ C₀) (h : HerglotzTailHypotheses r P F P' Ξ) :
    TendstoInDistribution (fun N ω => (F N ω).eval 0) atTop C₀ P P' := by
  obtain ⟨C, hC, hae⟩ := exists_isCanonicalCauchy_ae_eq hC₀
  have hT := herglotzTail r Ω P F Ω' P' Ξ C hC h 1 (fun _ => (0 : ℝ)) ∅ isCompact_empty
    (empty_subset _)
  have hg : Continuous fun p : JointValues r 1 ∅ => p.1 0 :=
    (continuous_apply (0 : Fin 1)).comp (continuous_fst (X := Fin 1 → Matrix (Fin r) (Fin r) ℂ)
      (Y := C((∅ : Set ℂ), Matrix (Fin r) (Fin r) ℂ)))
  have h0 := hT.continuous_comp hg
  have hfun : (fun N => (fun p : JointValues r 1 ∅ => p.1 0) ∘
      fun ω => jointValues (F N ω).eval (fun _ => (0 : ℝ)) ∅) = fun N ω => (F N ω).eval 0 := by
    funext N ω
    show (F N ω).eval ((0 : ℝ) : ℂ) = _
    rw [Complex.ofReal_zero]
  have hlim : ((fun p : JointValues r 1 ∅ => p.1 0) ∘
      fun ω => jointValues (C ω) (fun _ => (0 : ℝ)) ∅) = fun ω => C ω 0 := by
    funext ω
    show C ω ((0 : ℝ) : ℂ) = _
    rw [Complex.ofReal_zero]
  rw [hfun, hlim] at h0
  exact tendstoInDistribution_congr_limit h0 hae.symm

end BlockBand.Critical.Herglotz
