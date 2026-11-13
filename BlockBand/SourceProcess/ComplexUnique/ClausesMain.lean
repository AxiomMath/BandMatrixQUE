module

public import BlockBand.SourceProcess.ComplexUnique.Clauses

/-!
# The joint clauses form a localized complex martingale problem

`isCLocSol_of_joint`: a born Gram solution with deterministic Hermitian jumps and a complex source
extension with deterministic jumps give a localized complex martingale problem (`IsCLocSol`) for
the joint coordinates `jvec (G - J) (𝒦 - J_𝒦)`, with coefficients `jβ`, `jΓ`, `jΓ'`. The
`𝒦`–Gram cross clause is put in `kgCov` form by `cross_clause`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexUnique

open Matrix MeasureTheory ProbabilityTheory Filter Topology Set ComplexConjugate
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal

variable {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {Ω : Type*} [MeasurableSpace Ω]
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {b E : ℝ}
  {D : Matrix (SrcCol K π) (SrcCol K π) ℂ} {J : ℝ≥0 → GramState (SrcCol K π)}
  {JK : ℝ≥0 → Matrix π π ℂ} {G : ℝ≥0 → Ω → GramState (SrcCol K π)}
  {Kc : ℝ≥0 → Ω → Matrix π π ℂ}

omit [DecidableEq π] in
theorem kgCov_jvec_zero (D0 η : ℝ) (G' : GramState (SrcCol K π)) (Kc' : Matrix π π ℂ)
    (q : π × π) (k l : SrcCol K π) :
    kgCov D0 η D (jvec G' Kc') q (0, k, l) =
      -(Complex.I * ((η * D0 : ℝ) : ℂ)) * G'.2 (Sum.inr q.1) l * gramC0 G'.1 G'.2 D k (Sum.inr q.2) := by
  simp [kgCov, gramOf_jvec]

omit [DecidableEq π] in
theorem kgCov_jvec_one (D0 η : ℝ) (G' : GramState (SrcCol K π)) (Kc' : Matrix π π ℂ)
    (q : π × π) (k l : SrcCol K π) :
    kgCov D0 η D (jvec G' Kc') q (1, k, l) = -(Complex.I * ((η * D0 : ℝ) : ℂ)) *
      G'.2 (Sum.inr q.1) l * (gramC1 G'.1 G'.2 D)ᴴ k (Sum.inr q.2) := by
  simp [kgCov, gramOf_jvec]

/-- The `𝒦–Gram` cross clause in `kgCov` form. -/
theorem cross_clause
    (hK : IsComplexSourceExtension Q 𝓖 b E D (fun t _ => J t) G (fun t _ => JK t) Kc)
    (L : ℝ) (q : π × π) (e : Fin 2 × SrcCol K π × SrcCol K π) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t, N t =ᵐ[Q] stoppedProcess (fun t ω =>
      kCompensated Kc (fun t _ => JK t) q.1 q.2 t ω *
        bornCompensated (transportD0 b E) D G (fun t _ => J t) e t ω -
      ∫ s in Ioc (0 : ℝ) t, kgCov (transportD0 b E) (etaZ b E) D
        (jvec (G s.toNNReal ω) (Kc s.toNNReal ω)) q e) (gramTraceStop G L) t := by
  rcases e with ⟨r, k, l⟩
  fin_cases r
  · simp only [Fin.zero_eta, kgCov_jvec_zero]; exact hK.crossM L q.1 q.2 k l
  · simp only [Fin.mk_one, kgCov_jvec_one]; exact hK.crossB L q.1 q.2 k l

variable (b E) in

/-- **The joint clauses as a localized complex martingale problem.** -/
theorem isCLocSol_of_joint (hD : Dᴴ = D) (hJ : ∀ t, (J t).1ᴴ = (J t).1 ∧ (J t).2ᴴ = (J t).2)
    {CJ : ℝ} (hCJ : ∀ t, ‖jc J JK t‖ ≤ CJ)
    (hG : IsBornGramSolution Q 𝓖 (transportD0 b E) D (fun t _ => J t) G)
    (hK : IsComplexSourceExtension Q 𝓖 b E D (fun t _ => J t) G (fun t _ => JK t) Kc) :
    IsCLocSol Q 𝓖 (jβ (transportD0 b E) D) (jΓ (transportD0 b E) (etaZ b E) D)
      (jΓ' (transportD0 b E) (etaZ b E) D) (jc J JK) (jX G J Kc JK)
      (fun L => gramTraceStop G L) := by
  have hcont : ∀ᵐ ω ∂Q, Continuous fun t => jX G J Kc JK t ω := by
    filter_upwards [hG.continuous, hK.continuous] with ω h1 h2
    exact continuous_jvec.comp (h1.prodMk h2)
  have hherm : ∀ᵐ ω ∂Q, ∀ s, (G s ω).1ᴴ = (G s ω).1 ∧ (G s ω).2ᴴ = (G s ω).2 := by
    filter_upwards [hG.feasible] with ω h s using herm_of_feasible (h s)
  refine ⟨fun t => continuous_jvec.comp_stronglyMeasurable
      (((hG.adapted t).sub stronglyMeasurable_const).prodMk
        ((hK.adapted t).sub stronglyMeasurable_const)), hcont,
    fun k => ⟨_, by filter_upwards [hcont] with ω hx using rawHit_le_gramTraceStop hCJ k hx⟩,
    fun L p => ?_, fun L p p' => ?_, fun L p p' => ?_⟩
  · rcases p with e | q
    · rw [lComp_inl]; exact hG.drift L e
    · rw [lComp_inr]; exact hK.martingale L q.1 q.2
  · rcases p with e | q <;> rcases p' with e' | q'
    · have h : lBr (jβ (transportD0 b E) D) (jΓ (transportD0 b E) (etaZ b E) D) (jc J JK)
          (jX G J Kc JK) (Sum.inl e) (Sum.inl e') = fun t ω =>
            bornCompensated (transportD0 b E) D G (fun t _ => J t) e t ω *
              bornCompensated (transportD0 b E) D G (fun t _ => J t) e' t ω -
            ∫ s in Ioc (0 : ℝ) t, gramCovEntry (transportD0 b E) D e e' (G s.toNNReal ω) := by
        funext t ω; unfold lBr; rw [lComp_inl, lComp_inl]
        simp only [jX_add_jc, jΓ, Sum.elim_inl, gramOf_jvec]
      rw [h]; exact hG.bracket L e e'
    · obtain ⟨N, hN, hNX⟩ := cross_clause hK L q' e
      refine ⟨N, hN, fun t => ?_⟩
      filter_upwards [hNX t] with ω h
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr; rw [lComp_inl, lComp_inr]
      simp only [jX_add_jc, jΓ, Sum.elim_inl, Sum.elim_inr, mul_comm]
    · obtain ⟨N, hN, hNX⟩ := cross_clause hK L q e'
      refine ⟨N, hN, fun t => ?_⟩
      filter_upwards [hNX t] with ω h
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr; rw [lComp_inl, lComp_inr]
      simp only [jX_add_jc, jΓ, Sum.elim_inl, Sum.elim_inr]
    · have h : lBr (jβ (transportD0 b E) D) (jΓ (transportD0 b E) (etaZ b E) D) (jc J JK)
          (jX G J Kc JK) (Sum.inr q) (Sum.inr q') = fun t ω =>
            kCompensated Kc (fun t _ => JK t) q.1 q.2 t ω *
              kCompensated Kc (fun t _ => JK t) q'.1 q'.2 t ω := by
        funext t ω; unfold lBr; rw [lComp_inr, lComp_inr]
        simp only [jΓ, Sum.elim_inr, integral_zero, sub_zero]
      rw [h]; exact hK.holomorphic L q.1 q.2 q'.1 q'.2
  · rcases p with e | q <;> rcases p' with e' | q'
    · obtain ⟨N, hN, hNX⟩ := hG.bracket L e (gramSwap e')
      refine ⟨N, hN, fun t => ?_⟩
      filter_upwards [hNX t, hherm] with ω h hf
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr'; rw [lComp_inl, lComp_inl, star_bornCompensated hD hJ hf]
      simp only [jX_add_jc, jΓ', Sum.elim_inl, gramOf_jvec]
    · obtain ⟨N, hN, hNX⟩ := cross_clause hK L q' (gramSwap e)
      refine ⟨fun t ω => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (N t ω),
        martingale_clm hN _, fun t => ?_⟩
      filter_upwards [hNX t, hherm] with ω h hf
      simp only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply]
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr'; rw [lComp_inl, lComp_inr]
      simp only [jX_add_jc, jΓ', Sum.elim_inl, Sum.elim_inr, ← Complex.star_def, star_sub,
        star_mul', star_bornCompensated hD hJ hf]
      rw [Complex.star_def, ← integral_conj, mul_comm]
      rfl
    · obtain ⟨N, hN, hNX⟩ := cross_clause hK L q (gramSwap e')
      refine ⟨N, hN, fun t => ?_⟩
      filter_upwards [hNX t, hherm] with ω h hf
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr'; rw [lComp_inl, lComp_inr, star_bornCompensated hD hJ hf]
      simp only [jX_add_jc, jΓ', Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨N, hN, hNX⟩ := hK.antiholomorphic L q.1 q.2 q'.1 q'.2
      refine ⟨N, hN, fun t => ?_⟩
      filter_upwards [hNX t] with ω h
      rw [h, stoppedProcess_eq_stopTime, stoppedProcess_eq_stopTime]
      unfold lBr'; rw [lComp_inr, lComp_inr]
      simp only [jX_add_jc, jΓ', Sum.elim_inr, kkCov, gramOf_jvec]
      rfl

end BlockBand.SourceProcess.ComplexUnique
