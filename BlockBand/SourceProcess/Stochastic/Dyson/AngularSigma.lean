module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularFourier

/-!
# From cylinder sets to the σ-algebra `𝓕_0 ⊔ σ(W)` (π–λ theorem)

`Hyp.orth_sigma`: `E[1_S (Ms_u - Ms_0)] = 0` for every `S` measurable for
`𝓕_0 ⊔ ⨆_t σ(W_t)` (`W = λ - ∫ b(λ)`). The sets `A ∩ {W_J ∈ C}` (`A ∈ 𝓕_0`, `J` finite, `C`
Borel) form a π-system generating a σ-algebra containing `𝓕_0 ⊔ σ(W)`; the class of sets
with `E[1_S D] = 0` is a Dynkin system (`Hyp.orth_cyl` with `A = Ω`, `J = ∅` gives `E[D] = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

variable {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ} {s : ℝ≥0}
  {f : (Fin N → ℝ) → ℝ} {n : ℕ}

/-- The σ-algebra `𝓕_0 ⊔ σ(W_t : t ≥ 0)`. -/
abbrev sigB (m0 : MeasurableSpace Ω) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) : MeasurableSpace Ω :=
  m0 ⊔ ⨆ t, MeasurableSpace.comap (Wp Y t) inferInstance

/-- Cylinder sets `A ∩ {W_J ∈ C}`. -/
def cylSets (m0 : MeasurableSpace Ω) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) : Set (Set Ω) :=
  {S | ∃ A, MeasurableSet[m0] A ∧ ∃ (J : Finset ℝ≥0) (C : Set (J → Fin N → ℝ)),
    MeasurableSet C ∧ S = A ∩ WJ Y J ⁻¹' C}

/-- Restriction of a vector indexed by `J'` to `J ⊆ J'`. -/
def resJ {J J' : Finset ℝ≥0} (h : J ⊆ J') (x : J' → Fin N → ℝ) : J → Fin N → ℝ :=
  fun j => x ⟨j, h j.2⟩

theorem measurable_resJ {J J' : Finset ℝ≥0} (h : J ⊆ J') :
    Measurable (resJ (N := N) h) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

omit [MeasurableSpace Ω] in
theorem isPiSystem_cylSets (m0 : MeasurableSpace Ω) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) :
    IsPiSystem (cylSets m0 Y) := by
  rintro S₁ ⟨A₁, hA₁, J₁, C₁, hC₁, rfl⟩ S₂ ⟨A₂, hA₂, J₂, C₂, hC₂, rfl⟩ -
  have h1 : J₁ ⊆ J₁ ∪ J₂ := Finset.subset_union_left
  have h2 : J₂ ⊆ J₁ ∪ J₂ := Finset.subset_union_right
  refine ⟨A₁ ∩ A₂, hA₁.inter hA₂, J₁ ∪ J₂, resJ h1 ⁻¹' C₁ ∩ resJ h2 ⁻¹' C₂,
    (measurable_resJ h1 hC₁).inter (measurable_resJ h2 hC₂), ?_⟩
  ext ω
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨a1, c1⟩, a2, c2⟩; exact ⟨⟨a1, a2⟩, c1, c2⟩
  · rintro ⟨⟨a1, a2⟩, c1, c2⟩; exact ⟨⟨a1, c1⟩, a2, c2⟩

omit [MeasurableSpace Ω] in
theorem sigB_le_generateFrom (m0 : MeasurableSpace Ω) (Y : ℝ≥0 → Ω → Fin (N + N) → ℝ) :
    sigB m0 Y ≤ MeasurableSpace.generateFrom (cylSets m0 Y) := by
  refine sup_le (fun A hA => MeasurableSpace.measurableSet_generateFrom
    ⟨A, hA, ∅, univ, MeasurableSet.univ, by simp⟩) (iSup_le fun t => ?_)
  rintro S ⟨B, hB, rfl⟩
  refine MeasurableSpace.measurableSet_generateFrom ⟨univ, MeasurableSet.univ, {t},
    {x | x ⟨t, Finset.mem_singleton_self t⟩ ∈ B}, measurable_pi_apply _ hB, ?_⟩
  ext ω; simp [WJ]

/-- **The stopped angular increment is orthogonal to `𝓕_0 ⊔ σ(W)`.** -/
theorem Hyp.orth_sigma (H : Hyp Q 𝓖 N G F s f n) (q : Fin N → ℂ) (u : ℝ≥0) {S : Set Ω}
    (hS : MeasurableSet[sigB (shiftFiltration 𝓖 s 0) (Yst N q G F s)] S) :
    ∫ ω in S, Dp f (Yst N q G F s) (sig N G F s n) u ω ∂Q = 0 := by
  set Y := Yst N q G F s
  have hgen : MeasurableSpace.generateFrom (cylSets (shiftFiltration 𝓖 s 0) Y) ≤ (inferInstance : MeasurableSpace Ω) := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨A, hA, J, C, hC, rfl⟩
    exact ((shiftFiltration 𝓖 s).le 0 A hA).inter (H.measurable_WJ q J hC)
  have hD := H.integrable_D (f := f) q u
  have htot : ∫ ω, Dp f Y (sig N G F s n) u ω ∂Q = 0 := by
    have := H.orth_cyl (f := f) q (A := univ) MeasurableSet.univ ∅ (C := univ)
      MeasurableSet.univ u
    simpa using this
  refine @MeasurableSpace.induction_on_inter Ω (MeasurableSpace.generateFrom (cylSets (shiftFiltration 𝓖 s 0) Y))
    (fun S _ => ∫ ω in S, Dp f Y (sig N G F s n) u ω ∂Q = 0) (cylSets (shiftFiltration 𝓖 s 0) Y) rfl
    (isPiSystem_cylSets (shiftFiltration 𝓖 s 0) Y) (by simp) ?_ ?_ ?_ S (sigB_le_generateFrom (shiftFiltration 𝓖 s 0) Y S hS)
  · rintro _ ⟨A, hA, J, C, hC, rfl⟩
    exact H.orth_cyl q hA J hC u
  · intro T hT h
    rw [setIntegral_compl (hgen T hT) hD, htot, h, sub_zero]
  · intro g hdisj hgm hg
    have hg' : ∀ i, ∫ ω in g i, Dp f Y (sig N G F s n) u ω ∂Q = 0 := hg
    rw [integral_iUnion (fun i => hgen _ (hgm i)) hdisj hD.integrableOn]
    exact (tsum_congr hg').trans tsum_zero

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
