module

public import BlockBand.SourceProcess.ComplexCapLimit.Restrict

/-!
# A cap-`K'` complex model restricts to a cap-`K` complex model on `{t_K ≤ h²}`

On `{t_K ≤ h²}` the modes `k ≥ K` of a cap-`K'` complex model stay zero, so conditioning on this
event and restricting to the first `K` modes gives a cap-`K` complex model (`ccapRestrict`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCapLimit

open MeasureTheory ProbabilityTheory Function Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {b E s : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {h : ℝ} {K K' : ℕ}
  {entrance : Measure (Measure unitInterval)} {Ω : Type*} [MeasurableSpace Ω]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Q : Measure Ω}
  {tseq : Ω → ℕ → ℝ} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

/-- On `A = {t_K ≤ h²}`, the modes `k ≥ K` of a cap-`K'` complex model stay zero. -/
theorem cae_gsupp_capEmb (hK : K ≤ K') {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin np))}
    (hM : IsFiniteComplexSourceModel b E s τ m h K' entrance 𝓖 Q tseq G Kc) :
    ∀ᵐ ω ∂Q, ω ∈ entEvent tseq (capSet K h) → ∀ t, GSupp (capEmb hK (Fin np)) (G t ω) := by
  have := hM.prob
  have hA := cmeasurableSet_entEvent hM (measurableSet_capSet K h)
  have hdiag : ∀ y : {y // y ∉ Set.range (capEmb hK (Fin np))},
      ∀ᵐ ω ∂Q, ω ∈ entEvent tseq (capSet K h) → ∀ t, (G t ω).1 y y = 0 := by
    rintro ⟨y, hy⟩
    obtain ⟨k, σ, rfl, hk⟩ := notMem_range_capEmb hy
    refine ae_diag_eq_zero_on hM.solution (fun t ω => birthJump_inl_diag _ _ _ _)
      (fun ω => ⟨_, fun t => re_trace_birthJump_le _ _ _⟩) hA ?_
    filter_upwards [hM.initial, hM.entrance_sequence] with ω hi hseq hωA
    rw [hi.1]
    refine initialGram_diag_eq_zero k σ ((hseq.1 hk).trans ?_)
    have h1 : seqExtract (seqTraceMeasure (tseq ω)) K ≤ h ^ 2 := hωA
    rwa [seqExtract_seqTraceMeasure hseq] at h1
  filter_upwards [ae_all_iff.2 hdiag, hM.solution.feasible] with ω hω hf hωA t
  exact gsupp_of_feasible (hf t) fun y hy => by rw [hω ⟨y, hy⟩ hωA t, Complex.zero_re]

/-- **Complex cap restriction**: the cap-`K'` complex model, conditioned on `{t_K ≤ h²}` and
restricted to the first `K` modes and all probes (with `𝒦` unchanged), is a cap-`K` complex
model with the conditioned entrance. -/
theorem ccapRestrict (hK : K ≤ K') {G : ℝ≥0 → Ω → GramState (SrcCol K' (Fin np))}
    (hM : IsFiniteComplexSourceModel b E s τ m h K' entrance 𝓖 Q tseq G Kc)
    (hS0 : entrance (capSet K h) ≠ 0) :
    IsFiniteComplexSourceModel b E s τ m h K (entrance[|capSet K h]) 𝓖
      (Q[|entEvent tseq (capSet K h)]) tseq (pRestrict (capEmb hK (Fin np)) G) Kc := by
  have := hM.prob
  have hS := measurableSet_capSet K h
  have hA := cmeasurableSet_entEvent hM hS
  have hQA : Q (entEvent tseq (capSet K h)) ≠ 0 := by rwa [cmeasure_entEvent hM hS]
  have hZ := cae_gsupp_capEmb hK hM
  have hsol := isBornGramSolution_restrict (capEmb_injective hK _) sep_srcSignature hM.solution
    hA hQA hZ
  have hcx := isComplexSourceExtension_restrict hK sep_srcSignature hM.complex hA hQA hZ
  rw [srcSignature_submatrix] at hsol hcx
  have hJ : pRestrict (capEmb hK (Fin np)) (fun (t : ℝ≥0) (_ : Ω) => birthJump (K := K')
      (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) =
      fun (t : ℝ≥0) (_ : Ω) => birthJump (K := K) (fun j => τ j - s)
        (fun j => dStar b * m j) (t : ℝ) := by
    funext t ω
    exact gRestrict_birthJump _ _ _
  rw [hJ] at hsol hcx
  refine cmodel_cond_of hM hS hS0 ?_ hsol hcx
  filter_upwards [hM.initial] with ω hi
  exact ⟨by simp only [pRestrict, hi.1, gRestrict_initialGram], hi.2⟩

/-- The source data of the restricted state are those of the full state (on `GSupp`). -/
theorem modelSourceData_gRestrict (hK : K ≤ K') (Kc : Matrix (Fin np) (Fin np) ℂ)
    {X : GramState (SrcCol K' (Fin np))} (hX : GSupp (capEmb hK (Fin np)) X) :
    modelSourceData (srcSignature K (Fin np)) Kc (gRestrict (capEmb hK (Fin np)) X) =
      modelSourceData (srcSignature K' (Fin np)) Kc X := by
  have hr := capEmb_injective hK (Fin np)
  have e : (X.1 * srcSignature K' (Fin np) * X.1).submatrix (capEmb hK _) (capEmb hK _) =
      (gRestrict (capEmb hK _) X).1 * srcSignature K (Fin np) *
        (gRestrict (capEmb hK _) X).1 := by
    rw [submatrix_mul_of_sep hr (hX.1.mul_left sep_srcSignature).sep,
      submatrix_mul_of_sep hr hX.1.sep, srcSignature_submatrix]
    rfl
  unfold modelSourceData
  rw [← e]
  rfl

end BlockBand.SourceProcess.ComplexCapLimit
