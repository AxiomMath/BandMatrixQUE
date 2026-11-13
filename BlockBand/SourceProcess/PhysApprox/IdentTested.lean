module

public import BlockBand.SourceProcess.PhysApprox.Assembly
public import BlockBand.SourceProcess.ClosedLimit.Model
public import BlockBand.SourceProcess.ComplexUnique.Coeffs
public import BlockBand.SourceProcess.FullSourceStops.CoefficientMoments

/-!
# Tested complex models are complex finite models

This file proves `TargetT8` and `TargetT8Stopped`.

* `measurable_complexObs`, `stronglyMeasurable_G_pastC`, `stronglyMeasurable_Kc_pastC`,
  `measurable_tseq_pastC`: the observables and their past measurability.
* `exists_stopped_mart_of_tested` (unstopped clause, optional stopping) and
  `exists_stopped_mart_of_stoppedTested` (stopped clause; Mathlib's
  `StronglyAdapted.stoppedProcess`, no optional stopping): one clause, adapted and continuous
  for every `ω`, gives a stopped martingale modification.
* `IsTestedComplexModel.isFiniteComplexSourceModel` and
  `IsStoppedTestedComplexModel.isFiniteComplexSourceModel`: for `b < 1` and `m ≥ 0`, a tested
  (resp. stopped-tested) complex model with its raw natural filtration is an
  `IsFiniteComplexSourceModel`.
* `targetT8_holds : TargetT8`, `targetT8Stopped_holds : TargetT8Stopped`.

Measure: the tested model's `Q`; domain `ComplexSourceLawDomain` (only `b < 1` and `m ≥ 0` are used).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.ComplexSourceLaw
open Matrix
open scoped NNReal ComplexConjugate

variable {Ω : Type*} {K np : ℕ} {tseq : Ω → ℕ → ℝ}
  {G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ}

/-!
## The observables `complexObs`
-/

theorem measurable_complexObs [MeasurableSpace Ω] (htm : Measurable tseq)
    (hG : ∀ u, StronglyMeasurable (G u)) (hK : ∀ u, StronglyMeasurable (Kc u)) :
    ∀ i u, Measurable (complexObs tseq G Kc i u)
  | Sum.inl e, u => ((continuous_gramEntry e).comp_stronglyMeasurable (hG u)).measurable
  | Sum.inr (Sum.inl k), _ => Complex.measurable_ofReal.comp (measurable_pi_iff.1 htm k)
  | Sum.inr (Sum.inr ij), u =>
      ((continuous_id.matrix_elem ij.1 ij.2).comp_stronglyMeasurable (hK u)).measurable

theorem stronglyMeasurable_G_pastC (u : ℝ≥0) :
    StronglyMeasurable[pastSigma (complexObs tseq G Kc) u] (G u) := by
  set m := pastSigma (complexObs tseq G Kc) u
  have hv : Measurable[m] fun ω =>
      fun e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np) => gramEntry e (G u ω) := by
    let _ := m
    exact Measurable.of_eval fun e =>
      measurable_obs_past (complexObs tseq G Kc) (Sum.inl e) le_rfl
  have h := continuous_gramOfEntries.comp_stronglyMeasurable hv.stronglyMeasurable
  have e : (fun ω => gramOfEntries fun e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np) =>
      gramEntry e (G u ω)) = G u :=
    funext fun ω => gramOfEntries_gramEntry _
  rwa [e] at h

theorem stronglyMeasurable_Kc_pastC (u : ℝ≥0) :
    StronglyMeasurable[pastSigma (complexObs tseq G Kc) u] (Kc u) := by
  set m := pastSigma (complexObs tseq G Kc) u
  have hv : Measurable[m] fun ω => fun ij : Fin np × Fin np => Kc u ω ij.1 ij.2 := by
    let _ := m
    exact Measurable.of_eval fun ij =>
      measurable_obs_past (complexObs tseq G Kc) (Sum.inr (Sum.inr ij)) le_rfl
  have hc : Continuous fun v : Fin np × Fin np → ℂ => (Matrix.of fun i j => v (i, j)) :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  have h := hc.comp_stronglyMeasurable hv.stronglyMeasurable
  have e : (fun ω => Matrix.of fun i j => (fun ij : Fin np × Fin np => Kc u ω ij.1 ij.2) (i, j))
      = Kc u :=
    funext fun ω => Matrix.ext fun i j => rfl
  rwa [e] at h

theorem measurable_tseq_pastC :
    Measurable[pastSigma (complexObs tseq G Kc) 0] tseq := by
  let _ := pastSigma (complexObs tseq G Kc) 0
  refine Measurable.of_eval fun k => ?_
  have e : (fun ω => tseq ω k) = fun ω => (complexObs tseq G Kc (Sum.inr (Sum.inl k)) 0 ω).re :=
    funext fun ω => by simp [complexObs]
  rw [e]
  exact Complex.measurable_re.comp
    (measurable_obs_past (complexObs tseq G Kc) (Sum.inr (Sum.inl k)) le_rfl)

/-!
## One clause: the unstopped and the stopped tested forms
-/

/-- **Unstopped form.** A process with tested increments, adapted to the raw natural filtration
and continuous for every `ω`, stopped at a time a.s. equal to a stopping time, has a martingale
modification. -/
theorem exists_stopped_mart_of_tested [MeasurableSpace Ω] {I : Type*}
    {obs : I → ℝ≥0 → Ω → ℂ} (hobs : ∀ i u, Measurable (obs i u)) {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℂ} (hX : IsTestedMart Q obs X)
    (had : ∀ t, StronglyMeasurable[pastSigma obs t] (X t))
    (hcont : ∀ ω, Continuous fun t => X t ω) {ρ ρ' : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (pastFiltration obs hobs) ρ) (hρe : ∀ᵐ ω ∂Q, ρ ω = ρ' ω) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (pastFiltration obs hobs) Q ∧
      ∀ t, N t =ᵐ[Q] stoppedProcess X ρ' t := by
  obtain ⟨M', hM', hM'e⟩ := exists_martingale_stopped_C (martingale_of_tested hobs hX had)
    (fun _ => EventuallyEq.rfl) (ae_of_all _ hcont) hρ
  exact ⟨M', hM', fun t => (hM'e t).trans (stoppedProcess_ae_eq _ hρe t)⟩

/-- Tested increments pass to a.e.-equal versions. -/
theorem isTestedMart_of_ae_eq [MeasurableSpace Ω] {I : Type*} {obs : I → ℝ≥0 → Ω → ℂ}
    {Q : Measure Ω} {X Y : ℝ≥0 → Ω → ℂ} (hX : IsTestedMart Q obs X)
    (h : ∀ t, Y t =ᵐ[Q] X t) : IsTestedMart Q obs Y := by
  refine ⟨fun t => (hX.1 t).congr (h t).symm, fun s t hst m i u hu φ => ?_⟩
  rw [← hX.2 s t hst m i u hu φ]
  refine integral_congr_ae ?_
  filter_upwards [h s, h t] with ω h1 h2
  rw [h1, h2]

/-- **Stopped form.** If the process stopped at `ρ'` has tested increments, `X` is adapted to
the raw natural filtration and continuous for every `ω`, and `ρ'` is a.s. a stopping time `ρ`,
then the stopped process has a martingale modification (`X^ρ`, adapted by Mathlib's
`StronglyAdapted.stoppedProcess`). No optional stopping is used. -/
theorem exists_stopped_mart_of_stoppedTested [MeasurableSpace Ω] {I : Type*}
    {obs : I → ℝ≥0 → Ω → ℂ} (hobs : ∀ i u, Measurable (obs i u)) {Q : Measure Ω}
    [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℂ}
    (had : ∀ t, StronglyMeasurable[pastSigma obs t] (X t))
    (hcont : ∀ ω, Continuous fun t => X t ω) {ρ ρ' : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (pastFiltration obs hobs) ρ) (hρe : ∀ᵐ ω ∂Q, ρ ω = ρ' ω)
    (hX : IsTestedMart Q obs (stoppedProcess X ρ')) :
    ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (pastFiltration obs hobs) Q ∧
      ∀ t, N t =ᵐ[Q] stoppedProcess X ρ' t := by
  have hXρ : IsTestedMart Q obs (stoppedProcess X ρ) :=
    isTestedMart_of_ae_eq hX fun t => stoppedProcess_ae_eq X hρe t
  have hadρ : StronglyAdapted (pastFiltration obs hobs) (stoppedProcess X ρ) :=
    StronglyAdapted.stoppedProcess (f := pastFiltration obs hobs) had hcont hρ
  exact ⟨_, martingale_of_tested hobs hXρ hadρ, fun t => stoppedProcess_ae_eq X hρe t⟩

/-!
## The `𝒦` coordinates
-/

theorem stronglyMeasurable_kComp_pastC (E s : ℝ) (τ m : Fin np → ℝ) (i j : Fin np)
    (t : ℝ≥0) : StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
      (kCompensated Kc (fun t _ => kJ E s τ m t) i j t) := by
  have h1 : StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
      fun ω => (Kc t ω - kJ E s τ m t) i j :=
    (continuous_id.matrix_elem i j).comp_stronglyMeasurable
      ((stronglyMeasurable_Kc_pastC t).sub stronglyMeasurable_const)
  have h0 : StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
      fun ω => (Kc 0 ω - kJ E s τ m 0) i j :=
    (continuous_id.matrix_elem i j).comp_stronglyMeasurable
      (((stronglyMeasurable_Kc_pastC 0).mono (pastSigma_mono (complexObs tseq G Kc) zero_le)).sub
        stronglyMeasurable_const)
  exact h1.sub h0

/-- **The `𝒦` extension from five clauses.** For any notion `P X L` of "tested clause at trace
level `L`" that, for adapted processes continuous for every `ω`, yields a stopped martingale
modification (`htool`), the five `𝒦` clauses in `P`-form give
`IsComplexSourceExtension` for the raw natural filtration of `complexObs`.
-/
theorem isComplexSourceExtension_of_clauses [MeasurableSpace Ω] {b E s : ℝ} {τ m : Fin np → ℝ}
    {Q : Measure Ω} (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω)
    (hkc : ∀ ω, Continuous fun u => Kc u ω - kJ E s τ m u)
    (P : (ℝ≥0 → Ω → ℂ) → ℝ → Prop)
    (htool : ∀ (X : ℝ≥0 → Ω → ℂ) (L : ℝ),
      (∀ t, StronglyMeasurable[pastSigma (complexObs tseq G Kc) t] (X t)) →
      (∀ ω, Continuous fun t => X t ω) → P X L →
      ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (pastFiltration (complexObs tseq G Kc) hobs) Q ∧
        ∀ t, N t =ᵐ[Q] stoppedProcess X (gramTraceStop G L) t)
    (hmart : ∀ (L : ℝ) (i j : Fin np), P (kCompensated Kc (fun t _ => kJ E s τ m t) i j) L)
    (hholo : ∀ (L : ℝ) (i j k l : Fin np), P (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) L)
    (hanti : ∀ (L : ℝ) (i j k l : Fin np), P (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        conj (kCompensated Kc (fun t _ => kJ E s τ m t) k l t ω) -
        ∫ u in Set.Ioc (0 : ℝ) t, ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) *
          (G u.toNNReal ω).2 (Sum.inr i) (Sum.inr k) *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np))
            (Sum.inr l) (Sum.inr j)) L)
    (hcrossM : ∀ (L : ℝ) (i j : Fin np) (k l : SrcCol K (Fin np)), P (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (0, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          gramC0 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)) k
            (Sum.inr j)) L)
    (hcrossB : ∀ (L : ℝ) (i j : Fin np) (k l : SrcCol K (Fin np)), P (fun t ω =>
      kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω *
        bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) (1, k, l) t ω -
        ∫ u in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G u.toNNReal ω).2 (Sum.inr i) l *
          (gramC1 (G u.toNNReal ω).1 (G u.toNNReal ω).2 (srcSignature K (Fin np)))ᴴ k
            (Sum.inr j)) L) :
    IsComplexSourceExtension Q (pastFiltration (complexObs tseq G Kc) hobs) b E
      (srcSignature K (Fin np)) (fun t _ => gramJ b s τ m t) G (fun t _ => kJ E s τ m t) Kc := by
  have hG : ∀ u, StronglyMeasurable[pastSigma (complexObs tseq G Kc) u] (G u) :=
    stronglyMeasurable_G_pastC
  have hβ : ∀ i : Fin np, Measurable[pastSigma (complexObs tseq G Kc) 0]
      (fun _ : Ω => τ i - s) := fun _ => measurable_const
  have hkad := stronglyMeasurable_kComp_pastC (tseq := tseq) (G := G) (Kc := Kc) E s τ m
  have hkcc : ∀ (i j : Fin np) (ω : Ω),
      Continuous fun t => kCompensated Kc (fun t _ => kJ E s τ m t) i j t ω :=
    fun i j ω => ((hkc ω).matrix_elem i j).sub continuous_const
  have hbad : ∀ (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (t : ℝ≥0),
      StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
        (bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t) := fun e t =>
    stronglyMeasurable_bornCompensated (D0 := transportD0 b E) (D := srcSignature K (Fin np))
      hG hβ hc e t
  have hbc : ∀ (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (ω : Ω),
      Continuous fun t => bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t ω := fun e ω =>
    continuous_bornCompensated (D0 := transportD0 b E) (D := srcSignature K (Fin np)) hc e ω
  have hC0 : ∀ x y : SrcCol K (Fin np), Continuous fun g : GramState (SrcCol K (Fin np)) =>
      gramC0 g.1 g.2 (srcSignature K (Fin np)) x y := fun x y =>
    ComplexUnique.continuous_gramC0_entry (srcSignature K (Fin np)) x y
  have hC1 : ∀ x y : SrcCol K (Fin np), Continuous fun g : GramState (SrcCol K (Fin np)) =>
      (gramC1 g.1 g.2 (srcSignature K (Fin np)))ᴴ x y := fun x y =>
    ComplexUnique.continuous_gramC1H_entry (srcSignature K (Fin np)) x y
  have hB : ∀ x y : SrcCol K (Fin np), Continuous fun g : GramState (SrcCol K (Fin np)) =>
      g.2 x y := fun x y => continuous_snd.matrix_elem x y
  refine ⟨stronglyMeasurable_Kc_pastC, fun _ => stronglyMeasurable_const, ae_of_all _ hkc,
    fun L i j => htool _ L (hkad i j) (hkcc i j) (hmart L i j),
    fun L i j k l => htool _ L (fun t => (hkad i j t).mul (hkad k l t))
      (fun ω => (hkcc i j ω).mul (hkcc k l ω)) (hholo L i j k l), ?_, ?_, ?_⟩
  · intro L i j k l
    have hf : Continuous fun g : GramState (SrcCol K (Fin np)) =>
        ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) * g.2 (Sum.inr i) (Sum.inr k) *
          gramC0 g.1 g.2 (srcSignature K (Fin np)) (Sum.inr l) (Sum.inr j) :=
      (continuous_const.mul (hB _ _)).mul (hC0 _ _)
    exact htool _ L
      (fun t => ((hkad i j t).mul (Complex.continuous_conj.comp_stronglyMeasurable
        (hkad k l t))).sub (stronglyMeasurable_integral_past hf t hG hβ hc))
      (fun ω => ((hkcc i j ω).mul (Complex.continuous_conj.comp (hkcc k l ω))).sub
        (continuous_integral_born hf hc ω)) (hanti L i j k l)
  · intro L i j k l
    have hf : Continuous fun g : GramState (SrcCol K (Fin np)) =>
        -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) * g.2 (Sum.inr i) l *
          gramC0 g.1 g.2 (srcSignature K (Fin np)) k (Sum.inr j) :=
      (continuous_const.mul (hB _ _)).mul (hC0 _ _)
    exact htool _ L
      (fun t => ((hkad i j t).mul (hbad (0, k, l) t)).sub
        (stronglyMeasurable_integral_past hf t hG hβ hc))
      (fun ω => ((hkcc i j ω).mul (hbc (0, k, l) ω)).sub (continuous_integral_born hf hc ω))
      (hcrossM L i j k l)
  · intro L i j k l
    have hf : Continuous fun g : GramState (SrcCol K (Fin np)) =>
        -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) * g.2 (Sum.inr i) l *
          (gramC1 g.1 g.2 (srcSignature K (Fin np)))ᴴ k (Sum.inr j) :=
      (continuous_const.mul (hB _ _)).mul (hC1 _ _)
    exact htool _ L
      (fun t => ((hkad i j t).mul (hbad (1, k, l) t)).sub
        (stronglyMeasurable_integral_past hf t hG hβ hc))
      (fun ω => ((hkcc i j ω).mul (hbc (1, k, l) ω)).sub (continuous_integral_born hf hc ω))
      (hcrossB L i j k l)

/-- The Gram trace stops are a.s. stopping times of the raw natural filtration of `complexObs`
(`exists_stop_ae_eq_traceStop`), for `b < 1` and `m ≥ 0`. -/
theorem exists_stop_complexObs [MeasurableSpace Ω] {b s : ℝ} {τ m : Fin np → ℝ}
    {Q : Measure Ω} (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u) (hb : b < 1) (hm : ∀ j, 0 ≤ m j)
    (L : ℝ) : ∃ ρ : Ω → WithTop ℝ≥0,
      IsStoppingTime (pastFiltration (complexObs tseq G Kc) hobs) ρ ∧
        ∀ᵐ ω ∂Q, ρ ω = gramTraceStop G L ω := by
  have hj : ∀ i : Fin np,
      0 ≤ (((probeJump (K := K) fun i : Fin np => dStar b * m i) i).1.trace).re :=
    fun i => by
      rw [re_trace_probeJump]
      exact mul_nonneg (FullSourceStops.dStar_pos hb).le (hm i)
  exact exists_stop_ae_eq_traceStop (𝓖 := pastFiltration (complexObs tseq G Kc) hobs) (Q := Q)
    (stronglyMeasurable_G_pastC (Kc := Kc)) hj
    (β := fun i _ => τ i - s) (fun _ => measurable_const) (ae_of_all _ hc) L

/-!
## A tested complex model is a complex finite model
-/

/-- **A tested complex model is a complex finite model** (raw natural filtration of
`complexObs`), for `b < 1` and nonnegative tag masses. The Gram half is
`isBornGramSolution_of_tested`. -/
theorem IsTestedComplexModel.isFiniteComplexSourceModel [MeasurableSpace Ω] {b E s : ℝ}
    {τ m : Fin np → ℝ} {h : ℝ} {entrance : Measure (Measure unitInterval)} {Q : Measure Ω}
    (hT : IsTestedComplexModel b E s τ m h K entrance Q tseq G Kc) (hb : b < 1)
    (hm : ∀ j, 0 ≤ m j) :
    IsFiniteComplexSourceModel b E s τ m h K entrance
      (pastFiltration (complexObs tseq G Kc)
        (measurable_complexObs hT.entrance_measurable hT.gram_measurable hT.k_measurable))
      Q tseq G Kc := by
  have := hT.prob
  have hobs := measurable_complexObs hT.entrance_measurable hT.gram_measurable hT.k_measurable
  have hj : ∀ i : Fin np,
      0 ≤ (((probeJump (K := K) fun i : Fin np => dStar b * m i) i).1.trace).re :=
    fun i => by
      rw [re_trace_probeJump]
      exact mul_nonneg (FullSourceStops.dStar_pos hb).le (hm i)
  have hsol := isBornGramSolution_of_tested (Q := Q) hobs hj
    (stronglyMeasurable_G_pastC (Kc := Kc))
    (β := fun i _ => τ i - s) (fun _ => measurable_const) hT.continuous hT.feasible hT.drift
    hT.bracket
  refine ⟨inferInstance, measurable_tseq_pastC, hT.entrance_sequence, hT.entrance_law,
    hT.initial, hsol, ?_⟩
  refine isComplexSourceExtension_of_clauses hobs hT.continuous hT.k_continuous
    (fun X _ => IsTestedMart Q (complexObs tseq G Kc) X) (fun X L had hcont hX => ?_)
    (fun _ => hT.martingale) (fun _ => hT.holomorphic) (fun _ => hT.antiholomorphic)
    (fun _ => hT.crossM) (fun _ => hT.crossB)
  obtain ⟨ρ, hρ, hρe⟩ := exists_stop_complexObs (Q := Q) hobs hT.continuous hb hm L
  exact exists_stopped_mart_of_tested hobs hX had hcont hρ hρe

/-- **`TargetT8`**: `ComplexClosedLimitLaw` gives
`ComplexClosedLimitIdentification` (each tested model, with the raw natural filtration of
`complexObs`, is a complex finite model). -/
theorem complexClosedLimitIdentification_of_law (hL : ComplexClosedLimitLaw) :
    ComplexClosedLimitIdentification := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  have hb : b < 1 / 2 := hD.2.1
  have hm : ∀ j, 0 ≤ m j := hD.2.2.2.2.2.2.1
  refine (hL b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).mono fun h hK => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', m', Q, tseq, G, Kc, hT, hval⟩ := hKL φ hφ L hφL
  exact ⟨Ω', m', _, Q, tseq, G, Kc, hT.isFiniteComplexSourceModel (by linarith) hm, hval⟩

/-- **`TargetT8` holds.** -/
theorem targetT8_holds : TargetT8 :=
  complexClosedLimitIdentification_of_law

/-!
## The stopped form `TargetT8Stopped`
-/

/-- **A stopped-tested complex model is a complex finite model** (raw natural filtration of
`complexObs`), for `b < 1` and nonnegative tag masses. No moment of an unstopped process and no
optional stopping is used; each clause is stopped at an a.s. version of the trace stop. -/
theorem IsStoppedTestedComplexModel.isFiniteComplexSourceModel [MeasurableSpace Ω] {b E s : ℝ}
    {τ m : Fin np → ℝ} {h : ℝ} {entrance : Measure (Measure unitInterval)} {Q : Measure Ω}
    (hT : IsStoppedTestedComplexModel b E s τ m h K entrance Q tseq G Kc) (hb : b < 1)
    (hm : ∀ j, 0 ≤ m j) :
    IsFiniteComplexSourceModel b E s τ m h K entrance
      (pastFiltration (complexObs tseq G Kc)
        (measurable_complexObs hT.entrance_measurable hT.gram_measurable hT.k_measurable))
      Q tseq G Kc := by
  have := hT.prob
  have hobs := measurable_complexObs hT.entrance_measurable hT.gram_measurable hT.k_measurable
  have hG : ∀ u, StronglyMeasurable[pastSigma (complexObs tseq G Kc) u] (G u) :=
    stronglyMeasurable_G_pastC
  have hβ : ∀ i : Fin np, Measurable[pastSigma (complexObs tseq G Kc) 0]
      (fun _ : Ω => τ i - s) := fun _ => measurable_const
  have hc : ∀ ω, Continuous fun u => G u ω -
      bornJ (probeJump (K := K) fun i : Fin np => dStar b * m i) (fun i _ => τ i - s) u ω :=
    hT.continuous
  have htool : ∀ (X : ℝ≥0 → Ω → ℂ) (L : ℝ),
      (∀ t, StronglyMeasurable[pastSigma (complexObs tseq G Kc) t] (X t)) →
      (∀ ω, Continuous fun t => X t ω) →
      IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess X (gramTraceStop G L)) →
      ∃ N : ℝ≥0 → Ω → ℂ, Martingale N (pastFiltration (complexObs tseq G Kc) hobs) Q ∧
        ∀ t, N t =ᵐ[Q] stoppedProcess X (gramTraceStop G L) t := by
    intro X L had hcont hX
    obtain ⟨ρ, hρ, hρe⟩ := exists_stop_complexObs (Q := Q) hobs hT.continuous hb hm L
    exact exists_stopped_mart_of_stoppedTested hobs had hcont hρ hρe hX
  have hbad : ∀ (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (t : ℝ≥0),
      StronglyMeasurable[pastSigma (complexObs tseq G Kc) t]
        (bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t) := fun e t =>
    stronglyMeasurable_bornCompensated (D0 := transportD0 b E) (D := srcSignature K (Fin np))
      hG hβ hc e t
  have hbc : ∀ (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (ω : Ω),
      Continuous fun t => bornCompensated (transportD0 b E) (srcSignature K (Fin np)) G
          (fun t _ => gramJ b s τ m t) e t ω := fun e ω =>
    continuous_bornCompensated (D0 := transportD0 b E) (D := srcSignature K (Fin np)) hc e ω
  have hsol : IsBornGramSolution Q (pastFiltration (complexObs tseq G Kc) hobs)
      (transportD0 b E) (srcSignature K (Fin np)) (fun t _ => gramJ b s τ m t) G := by
    refine ⟨hG, fun _ => stronglyMeasurable_const, ae_of_all _ hT.continuous, hT.feasible,
      fun L e => htool _ L (hbad e) (hbc e) (hT.drift L e), fun L e e' => ?_⟩
    have hf := continuous_gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e'
    exact htool _ L
      (fun t => ((hbad e t).mul (hbad e' t)).sub (stronglyMeasurable_integral_past hf t hG hβ hc))
      (fun ω => ((hbc e ω).mul (hbc e' ω)).sub (continuous_integral_born hf hc ω))
      (hT.bracket L e e')
  exact ⟨inferInstance, measurable_tseq_pastC, hT.entrance_sequence, hT.entrance_law,
    hT.initial, hsol, isComplexSourceExtension_of_clauses hobs hT.continuous hT.k_continuous
      (fun X L => IsTestedMart Q (complexObs tseq G Kc) (stoppedProcess X (gramTraceStop G L)))
      htool hT.martingale hT.holomorphic hT.antiholomorphic hT.crossM hT.crossB⟩

/-- **`TargetT8Stopped`**: `ComplexClosedLimitLawStopped` gives
`ComplexClosedLimitIdentification`. -/
theorem complexClosedLimitIdentification_of_lawStopped (hL : ComplexClosedLimitLawStopped) :
    ComplexClosedLimitIdentification := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ
  have hb : b < 1 / 2 := hD.2.1
  have hm : ∀ j, 0 ≤ m j := hD.2.2.2.2.2.2.1
  refine (hL b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ).mono fun h hK => hK.mono fun K hKL => ?_
  intro φ hφ L hφL
  obtain ⟨Ω', m', Q, tseq, G, Kc, hT, hval⟩ := hKL φ hφ L hφL
  exact ⟨Ω', m', _, Q, tseq, G, Kc, hT.isFiniteComplexSourceModel (by linarith) hm, hval⟩

/-- **`TargetT8Stopped` holds.** -/
theorem targetT8Stopped_holds : TargetT8Stopped :=
  complexClosedLimitIdentification_of_lawStopped

end BlockBand.SourceProcess.PhysApprox
