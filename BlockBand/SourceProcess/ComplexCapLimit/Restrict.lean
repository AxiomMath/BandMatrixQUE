module

public import BlockBand.SourceProcess.ComplexCapLimit.Cond

/-!
# Restricting the `𝒦` extension to the first `K` modes

For `K ≤ K'`, the restriction of the `𝒦` extension of a cap-`K'` model, on an event where the modes
`k ≥ K` vanish, is a `𝒦` extension for the restricted state under the conditioned measure
(`isComplexSourceExtension_restrict`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCapLimit

open MeasureTheory ProbabilityTheory Function Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {K K' : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

omit [DecidableEq π] in
theorem gramC0_gRestrict (hK : K ≤ K') {D : Matrix (SrcCol K' π) (SrcCol K' π) ℂ}
    (hD : Sep (capEmb hK π) D) {X : GramState (SrcCol K' π)} (hX : Supp (capEmb hK π) X.1)
    (a c : SrcCol K π) :
    gramC0 (gRestrict (capEmb hK π) X).1 (gRestrict (capEmb hK π) X).2
        (D.submatrix (capEmb hK π) (capEmb hK π)) a c =
      gramC0 X.1 X.2 D (capEmb hK π a) (capEmb hK π c) := by
  rw [show (gRestrict (capEmb hK π) X).1 = X.1.submatrix (capEmb hK π) (capEmb hK π) from rfl,
    show (gRestrict (capEmb hK π) X).2 = X.2.submatrix (capEmb hK π) (capEmb hK π) from rfl,
    gramC0_submatrix (capEmb_injective hK π) hX hD]
  rfl

omit [DecidableEq π] in
theorem gramC1_conj_gRestrict (hK : K ≤ K') {D : Matrix (SrcCol K' π) (SrcCol K' π) ℂ}
    (hD : Sep (capEmb hK π) D) {X : GramState (SrcCol K' π)} (hX : Supp (capEmb hK π) X.1)
    (a c : SrcCol K π) :
    (gramC1 (gRestrict (capEmb hK π) X).1 (gRestrict (capEmb hK π) X).2
        (D.submatrix (capEmb hK π) (capEmb hK π)))ᴴ a c =
      (gramC1 X.1 X.2 D)ᴴ (capEmb hK π a) (capEmb hK π c) := by
  rw [show (gRestrict (capEmb hK π) X).1 = X.1.submatrix (capEmb hK π) (capEmb hK π) from rfl,
    show (gRestrict (capEmb hK π) X).2 = X.2.submatrix (capEmb hK π) (capEmb hK π) from rfl,
    gramC1_submatrix (capEmb_injective hK π) hX hD]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {b E : ℝ}
  {D : Matrix (SrcCol K' π) (SrcCol K' π) ℂ}
  {J G : ℝ≥0 → Ω → GramState (SrcCol K' π)} {JK Kc : ℝ≥0 → Ω → Matrix π π ℂ}

/-- **The restriction of the `𝒦` extension on `A` is a `𝒦` extension under `Q[|A]`.** The
`𝒦` coordinates are indexed by the probes and are carried unchanged; the brackets read only
probe entries of `B` and `gramC0`, `gramC1` at a probe column, which the restriction keeps. -/
theorem isComplexSourceExtension_restrict (hK : K ≤ K') (hD : Sep (capEmb hK π) D)
    (hC : IsComplexSourceExtension Q 𝓖 b E D J G JK Kc) {A : Set Ω} (hA : MeasurableSet[𝓖 0] A)
    (hA0 : Q A ≠ 0) (hZ : ∀ᵐ ω ∂Q, ω ∈ A → ∀ t, GSupp (capEmb hK π) (G t ω)) :
    IsComplexSourceExtension (Q[|A]) 𝓖 b E (D.submatrix (capEmb hK π) (capEmb hK π))
      (pRestrict (capEmb hK π) J) (pRestrict (capEmb hK π) G) JK Kc := by
  have hr := capEmb_injective hK π
  have hA' : MeasurableSet A := 𝓖.le 0 _ hA
  exact {
    adapted := hC.adapted
    jump := hC.jump
    continuous := ae_cond_of_ae hC.continuous A
    martingale := fun L i j => by
      obtain ⟨N, hN, hNX⟩ := hC.martingale L i j
      refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on hA' ?_⟩
      filter_upwards [hNX t, hZ] with ω hω hz hωA
      rw [hω]
      simp only [stoppedProcess, gramTraceStop_pRestrict hr (hz hωA)]
    holomorphic := fun L i j k l => by
      obtain ⟨N, hN, hNX⟩ := hC.holomorphic L i j k l
      refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on hA' ?_⟩
      filter_upwards [hNX t, hZ] with ω hω hz hωA
      rw [hω]
      simp only [stoppedProcess, gramTraceStop_pRestrict hr (hz hωA)]
    antiholomorphic := fun L i j k l => by
      obtain ⟨N, hN, hNX⟩ := hC.antiholomorphic L i j k l
      refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on hA' ?_⟩
      filter_upwards [hNX t, hZ] with ω hω hz hωA
      rw [hω]
      simp only [stoppedProcess, gramTraceStop_pRestrict hr (hz hωA), pRestrict,
        gramC0_gRestrict hK hD (hz hωA _).1]
      rfl
    crossM := fun L i j k l => by
      obtain ⟨N, hN, hNX⟩ := hC.crossM L i j (capEmb hK π k) (capEmb hK π l)
      refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on hA' ?_⟩
      filter_upwards [hNX t, hZ] with ω hω hz hωA
      rw [hω]
      simp only [stoppedProcess, gramTraceStop_pRestrict hr (hz hωA),
        bornCompensated_pRestrict hr hD (hz hωA)]
      simp only [pRestrict, gramC0_gRestrict hK hD (hz hωA _).1]
      rfl
    crossB := fun L i j k l => by
      obtain ⟨N, hN, hNX⟩ := hC.crossB L i j (capEmb hK π k) (capEmb hK π l)
      refine ⟨N, martingale_cond hN hA hA0, fun t => ae_cond_of_ae_on hA' ?_⟩
      filter_upwards [hNX t, hZ] with ω hω hz hωA
      rw [hω]
      simp only [stoppedProcess, gramTraceStop_pRestrict hr (hz hωA),
        bornCompensated_pRestrict hr hD (hz hωA)]
      simp only [pRestrict, gramC1_conj_gRestrict hK hD (hz hωA _).1]
      rfl }

end BlockBand.SourceProcess.ComplexCapLimit
