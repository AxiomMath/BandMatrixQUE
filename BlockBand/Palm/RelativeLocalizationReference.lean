module

public import BlockBand.Palm.RelativeLocalizationShortFields

/-!
# Relative localization: the field `reference_finite_speed`

* data `refData = 1_A 1_{J^c}` (`J` from the time-`a` count `k₀ = #{λ_l(a) ≤ E}`, `A` the
  far event at the start `s`, measurable at `s`), weight `rlPhi ν 0 d R_c` centred at `E`
  (`ν = N^{19/10000} = 1/d`, `R_c = r₀/128`), truncated reference generator `truncRefGen`;
* `ref_pointwise` : on the good event, for every `s ∈ [a,c]` and every backward propagator `P`,
  the integrand `Σ_{j∉J} P(s)_{kj}` is `≤ e^{ν C_w/N}` times the weighted mass of the
  adapted forward solution from `s` (by pairing with the backward propagator and the terminal
  weight);
* joint `(s, ω)`-measurability through the parametric adapted mass (`coeffP`, `dataP`,
  `measurable_genMassP`), Tonelli (`lintegral_lintegral_swap`), the per-start bound
  `gen_expectation_avoid`, Markov (`markov_limit_lint`) and `tendsto_gapEvent`;
* `ref_scales`, `rowKappa_le_gen`, `ref_final` : the arithmetic of the scales.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix Real
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {N : ℕ}

/-- `1_{J^c}(j)` from the time-`a` eigenvalues. -/
def refJc (N : ℕ) (E : ℝ) (w : ℕ) (lam0 : Fin N → ℝ) (j : Fin N) : ℝ :=
  if Int.natAbs ((j : ℤ) - ((Finset.univ.filter fun l : Fin N => lam0 l ≤ E).card : ℤ)) ≤ w
  then 0 else 1

theorem measurable_refJc (N : ℕ) (E : ℝ) (w : ℕ) (j : Fin N) :
    Measurable fun lam0 : Fin N → ℝ => refJc N E w lam0 j := by
  classical
  set code : (Fin N → ℝ) → (Fin N → Bool) := fun lam l => decide (lam l ≤ E)
  have hcode : Measurable code := by
    refine measurable_pi_iff.mpr fun l => measurable_to_bool ?_
    have : (fun lam : Fin N → ℝ => decide (lam l ≤ E)) ⁻¹' {true} = {lam | lam l ≤ E} := by
      ext lam; simp
    rw [this]; exact measurableSet_le (measurable_pi_apply l) measurable_const
  have hfun : (fun lam0 : Fin N → ℝ => refJc N E w lam0 j) =
      (fun b : Fin N → Bool => if Int.natAbs ((j : ℤ) -
        ((Finset.univ.filter fun l : Fin N => b l = true).card : ℤ)) ≤ w then (0 : ℝ) else 1) ∘
        code := by
    funext lam0; simp [refJc, code]
  rw [hfun]
  exact (measurable_of_finite _).comp hcode

theorem refJc_mem (N : ℕ) (E : ℝ) (w : ℕ) (lam0 : Fin N → ℝ) (j : Fin N) :
    0 ≤ refJc N E w lam0 j ∧ refJc N E w lam0 j ≤ 1 := by
  unfold refJc; split_ifs <;> norm_num

/-- The far-window event at start `s'`. -/
def refA (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ : ℝ) (s' : ℝ≥0) :
    Set (FlowSample N) :=
  {ω | ∀ j : Fin N, refJc N E w (flowLam F 0 ω) j = 1 → δ ≤ |flowLam F s' ω j - E|}

/-- Reference data `1_A 1_{J^c}`. -/
def refData (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ : ℝ) (s' : ℝ≥0)
    (ω : FlowSample N) : Fin N → ℝ :=
  fun j => (refA F E w δ s').indicator (fun _ => (1 : ℝ)) ω * refJc N E w (flowLam F 0 ω) j

theorem refData_mem (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ : ℝ) (s' : ℝ≥0)
    (ω : FlowSample N) (j : Fin N) :
    0 ≤ refData F E w δ s' ω j ∧ refData F E w δ s' ω j ≤ 1 := by
  have h := refJc_mem N E w (flowLam F 0 ω) j
  unfold refData
  by_cases hω : ω ∈ refA F E w δ s'
  · simp [hω, h.1, h.2]
  · simp [hω]

/-- Measurability of the data at its start. -/
theorem refA_measurableSet (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ : ℝ) (s' : ℝ≥0) :
    MeasurableSet[flowFiltration N s'] (refA F E w δ s') := by
  have h0 : Measurable[flowFiltration N s'] (flowLam F 0) :=
    (flowLam_adapted F 0).mono ((flowFiltration N).mono (zero_le (a := s'))) le_rfl
  have hs : Measurable[flowFiltration N s'] (flowLam F s') := flowLam_adapted F s'
  have : refA F E w δ s' = ⋂ j : Fin N, ({ω | refJc N E w (flowLam F 0 ω) j = 1}ᶜ ∪
      {ω | δ ≤ |flowLam F s' ω j - E|}) := by
    ext ω; simp only [refA, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    exact forall_congr' fun j => imp_iff_not_or
  rw [this]
  refine MeasurableSet.iInter fun j => MeasurableSet.union ?_ ?_
  · exact (((measurable_refJc N E w j).comp h0) (measurableSet_singleton 1)).compl
  · exact ((continuous_abs.measurable.comp (((measurable_pi_apply j).comp hs).sub
      measurable_const))) measurableSet_Ici

theorem refData_measurable (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ : ℝ) (s' : ℝ≥0) :
    Measurable[flowFiltration N s'] (refData F E w δ s') := by
  have h0 : Measurable[flowFiltration N s'] (flowLam F 0) :=
    (flowLam_adapted F 0).mono ((flowFiltration N).mono (zero_le (a := s'))) le_rfl
  refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ) (flowFiltration N s') _ _ |>.mpr
    fun j => ?_
  exact (measurable_const.indicator (refA_measurableSet F E w δ s')).mul
    ((measurable_refJc N E w j).comp h0)

theorem measurable_flowLam_joint {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) :
    Measurable (fun p : ℝ≥0 × FlowSample N => flowLam F p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun t ω => flowLam F t ω)
    (fun ω => flowLam_continuous hF ω)
    (fun t => (flowLam_adapted F t).mono ((flowFiltration N).le t) le_rfl)

/-- The constant filtration. -/
def constFiltration (P : Type*) [m : MeasurableSpace P] : Filtration ℝ≥0 m :=
  ⟨fun _ => m, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- Parametric coefficients `p = (s, ω) ↦ Gen(λ((s-a)₊ + u))`. -/
def coeffP (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (u : ℝ≥0) (p : ℝ × FlowSample N) : Fin N → Fin N → ℝ :=
  Gen (flowLam F (Real.toNNReal (p.1 - a) + u) p.2)

/-- Parametric data. -/
def dataP (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (w : ℕ) (δ a : ℝ) (p : ℝ × FlowSample N) :
    Fin N → ℝ :=
  refData F E w δ (Real.toNNReal (p.1 - a)) p.2

theorem genMass_eq_P (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (E : ℝ) (w : ℕ) (δ a : ℝ) (r : ℝ) (s : ℝ) (ω : FlowSample N) :
    adaptedMass (coeffP Gen F a) (dataP F E w δ a) r (s, ω) =
      adaptedMass (genCoeff Gen F (Real.toNNReal (s - a)))
        (refData F E w δ (Real.toNNReal (s - a))) r ω := by
  have h : realCoeff (coeffP Gen F a) (s, ω) = realCoeff (genCoeff Gen F (Real.toNNReal (s - a))) ω :=
    funext fun _ => rfl
  simp only [adaptedMass, adaptedIter, dataP, h]

theorem measurable_coeffP {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (u : ℝ≥0) :
    Measurable (coeffP Gen F a u) := by
  have h0 : Measurable (fun x : ℝ => Real.toNNReal (x - a) + u) :=
    (by fun_prop : Continuous fun x : ℝ => Real.toNNReal (x - a) + u).measurable
  have h1 : Measurable (fun p : ℝ × FlowSample N => Real.toNNReal (p.1 - a) + u) :=
    h0.comp measurable_fst
  have h2 : Measurable (fun p : ℝ × FlowSample N => (Real.toNNReal (p.1 - a) + u, p.2)) :=
    h1.prodMk measurable_snd
  have h3 := (measurable_flowLam_joint hF).comp h2
  exact hG.measurable.comp h3

theorem measurable_dataP {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (E : ℝ) (w : ℕ)
    (δ a : ℝ) : Measurable (dataP F E w δ a) := by
  have h0 : Measurable (fun p : ℝ × FlowSample N => flowLam F 0 p.2) :=
    ((flowLam_adapted F 0).mono ((flowFiltration N).le 0) le_rfl).comp measurable_snd
  have hf1 : Measurable (fun x : ℝ => Real.toNNReal (x - a)) :=
    (by fun_prop : Continuous fun x : ℝ => Real.toNNReal (x - a)).measurable
  have hs2 : Measurable (fun p : ℝ × FlowSample N => (Real.toNNReal (p.1 - a), p.2)) :=
    (hf1.comp measurable_fst).prodMk measurable_snd
  have hs := (measurable_flowLam_joint hF).comp hs2
  have hA : MeasurableSet {p : ℝ × FlowSample N | ∀ j : Fin N,
      refJc N E w (flowLam F 0 p.2) j = 1 →
        δ ≤ |flowLam F (Real.toNNReal (p.1 - a)) p.2 j - E|} := by
    have : {p : ℝ × FlowSample N | ∀ j : Fin N, refJc N E w (flowLam F 0 p.2) j = 1 →
        δ ≤ |flowLam F (Real.toNNReal (p.1 - a)) p.2 j - E|} =
        ⋂ j : Fin N, ({p : ℝ × FlowSample N | refJc N E w (flowLam F 0 p.2) j = 1}ᶜ ∪
          {p | δ ≤ |flowLam F (Real.toNNReal (p.1 - a)) p.2 j - E|}) := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
      exact forall_congr' fun j => imp_iff_not_or
    rw [this]
    refine MeasurableSet.iInter fun j => MeasurableSet.union ?_ ?_
    · exact (((measurable_refJc N E w j).comp h0) (measurableSet_singleton 1)).compl
    · exact measurableSet_le measurable_const
        ((continuous_abs.measurable.comp (((measurable_pi_apply j).comp hs).sub measurable_const)))
  refine measurable_pi_iff.mpr fun j => ?_
  have : (fun p : ℝ × FlowSample N => dataP F E w δ a p j) = fun p =>
      ({p : ℝ × FlowSample N | ∀ j : Fin N, refJc N E w (flowLam F 0 p.2) j = 1 →
        δ ≤ |flowLam F (Real.toNNReal (p.1 - a)) p.2 j - E|}).indicator (fun _ => (1 : ℝ)) p *
        refJc N E w (flowLam F 0 p.2) j := by
    funext p
    simp only [dataP, refData, refA, Set.indicator, Set.mem_ofPred_eq]
    congr 1
    by_cases hc : ∀ (j : Fin N), refJc N E w (flowLam F 0 p.2) j = 1 →
        δ ≤ |flowLam F (Real.toNNReal (p.1 - a)) p.2 j - E|
    · exact (ite_eq_left hc).trans (ite_eq_left hc).symm
    · exact (ite_eq_right hc).trans (ite_eq_right hc).symm
  rw [this]
  exact (measurable_const.indicator hA).mul ((measurable_refJc N E w j).comp h0)

theorem measurable_adaptedP_fix {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (E : ℝ) (w : ℕ) (δ a : ℝ) (u : ℝ≥0) :
    Measurable (fun p : ℝ × FlowSample N =>
      adaptedMass (coeffP Gen F a) (dataP F E w δ a) (u : ℝ) p) := by
  have hc : ∀ p : ℝ × FlowSample N, Continuous fun u => coeffP Gen F a u p := fun p =>
    hG.comp ((flowLam_continuous hF p.2).comp (continuous_const.add continuous_id))
  have := adaptedMass_measurable (constFiltration (ℝ × FlowSample N)) (Lc := coeffP Gen F a)
    (fun t => measurable_coeffP hG hF a t) hc (v₀ := dataP F E w δ a)
    (measurable_dataP hF E w δ a) u
  exact this

theorem measurable_genMassP {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (E : ℝ) (w : ℕ) (δ a : ℝ)
    {T : ℝ × FlowSample N → ℝ≥0} (hT : Measurable T) :
    Measurable (fun p : ℝ × FlowSample N =>
      adaptedMass (coeffP Gen F a) (dataP F E w δ a) ((T p : ℝ≥0) : ℝ) p) := by
  have hc : ∀ p : ℝ × FlowSample N, Continuous fun u => coeffP Gen F a u p := fun p =>
    hG.comp ((flowLam_continuous hF p.2).comp (continuous_const.add continuous_id))
  have hcont : ∀ p : ℝ × FlowSample N, Continuous fun u : ℝ≥0 =>
      adaptedMass (coeffP Gen F a) (dataP F E w δ a) (u : ℝ) p :=
    fun p => adaptedMass_continuous hc _ p
  have hjoint := measurable_uncurry_of_continuous_of_measurable
    (u := fun (u : ℝ≥0) (p : ℝ × FlowSample N) =>
      adaptedMass (coeffP Gen F a) (dataP F E w δ a) (u : ℝ) p) hcont
    (fun u => measurable_adaptedP_fix hG hF E w δ a u)
  have h2 := hjoint.comp (hT.prodMk measurable_id')
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h2

theorem markov_limit_lint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bad B₁ Nul : Set Ω)
    (G : ℕ → Set Ω) (Z : ℕ → Ω → ℝ≥0∞) {ε e : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ⊤)
    (hNul : μ Nul = 0) (hG : Tendsto (fun n => μ (G n)) atTop (𝓝 0))
    (hZm : ∀ n, AEMeasurable (Z n) μ) (hZe : ∀ n, ∫⁻ ω, Z n ω ∂μ ≤ e)
    (hsub : ∀ n, Bad ⊆ B₁ ∪ Nul ∪ G n ∪ {ω | ε < Z n ω}) :
    μ Bad ≤ μ B₁ + e / ε := by
  have hstep : ∀ n, μ Bad ≤ μ B₁ + μ (G n) + e / ε := by
    intro n
    have h1 := measure_union_le (μ := μ) (B₁ ∪ Nul ∪ G n) {ω | ε < Z n ω}
    have h2 := measure_union_le (μ := μ) (B₁ ∪ Nul) (G n)
    have h3 := measure_union_le (μ := μ) B₁ Nul
    have hM : μ {ω | ε < Z n ω} ≤ e / ε :=
      (measure_mono fun ω (hω : ε < Z n ω) => hω.le).trans
        ((meas_ge_le_lintegral_div (hZm n) hε hε').trans (ENNReal.div_le_div_right (hZe n) _))
    calc μ Bad ≤ μ (B₁ ∪ Nul ∪ G n ∪ {ω | ε < Z n ω}) := measure_mono (hsub n)
      _ ≤ μ (B₁ ∪ Nul ∪ G n) + μ {ω | ε < Z n ω} := h1
      _ ≤ μ (B₁ ∪ Nul) + μ (G n) + μ {ω | ε < Z n ω} := by gcongr
      _ ≤ μ B₁ + μ Nul + μ (G n) + μ {ω | ε < Z n ω} := by gcongr
      _ ≤ μ B₁ + μ (G n) + e / ε := by rw [hNul, add_zero]; gcongr
  have hlim : Tendsto (fun n => μ B₁ + μ (G n) + e / ε) atTop (𝓝 (μ B₁ + 0 + e / ε)) :=
    (tendsto_const_nhds.add hG).add tendsto_const_nhds
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim hstep

theorem forwardMass_unshift {L : ℝ → Fin N → Fin N → ℝ} {T s : ℝ} {v₀ : Fin N → ℝ}
    {w : ℝ → Fin N → ℝ} (hw : ForwardMassSolution L 0 T v₀ w) :
    ForwardMassSolution (fun σ => L (σ - s)) s (s + T) v₀ (fun σ => w (σ - s)) := by
  obtain ⟨h0, hc, hd⟩ := hw
  refine ⟨by simp [h0], ?_, fun x hx => ?_⟩
  · refine hc.comp (continuous_id.sub continuous_const).continuousOn fun x hx => ⟨?_, ?_⟩
    · show 0 ≤ x - s; linarith [hx.1]
    · show x - s ≤ T; linarith [hx.2]
  · have := hd (x - s) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact HasDerivAt.comp_sub_const x s this

theorem refJc_eq {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} {ω : FlowSample N} (hH : ω.1.IsHermitian)
    (E : ℝ) (w : ℕ) (j : Fin N) :
    refJc N E w (flowLam F 0 ω) j =
      if Int.natAbs ((j : ℤ) -
        ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
      then 0 else 1 := by
  have h0 : flowLam F 0 ω = flowEigenvalue F a ω a := by
    rw [flowLam_eq_flowEigenvalue F a hH]; funext k; simp
  rw [h0]; rfl

/-- **Pointwise bound** of the integrand `Σ_{j∉J} P(s)_{kj}` on the good event. -/
theorem ref_pointwise {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c s : ℝ}
    (has : a ≤ s) (hsc : s ≤ c) {ω : FlowSample N} (hH : ω.1.IsHermitian) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {b₀ g : ℝ} (hg : 0 < g)
    (hgaps : ∀ r : ℝ≥0, r ≤ Real.toNNReal (c - a) → ∀ i j : Fin N, i ≠ j →
      g ≤ |flowLam F r ω i - flowLam F r ω j|)
    {E δ : ℝ} {w : ℕ} (hA : ω ∈ refA F E w δ (Real.toNNReal (s - a)))
    {ν d Rc Cw : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hRc : 0 < Rc) {k : Fin N}
    (hk : |flowEigenvalue F a ω c k - E| ≤ Cw / N) {P : ℝ → Fin N → Fin N → ℝ}
    (hP : BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c P) :
    ∑ j : Fin N, (if Int.natAbs ((j : ℤ) -
        ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
        then 0 else 1) * P s k j ≤
      Real.exp (ν * (Cw / N)) *
        goodMass (fun lam => truncRefGen N lam ℓ b₀ g) F (Real.toNNReal (s - a))
          (refData F E w δ (Real.toNNReal (s - a))) (fun _ => E) (rlPhi ν 0 d Rc)
          (Real.toNNReal (c - s)) ω := by
  set s' := Real.toNNReal (s - a) with hs'
  set T := Real.toNNReal (c - s) with hT
  have hTr : (T : ℝ) = c - s := Real.coe_toNNReal _ (by linarith)
  set Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ := fun lam => truncRefGen N lam ℓ b₀ g with hGen
  have hGc : Continuous Gen := continuous_truncRefGen ℓ b₀ hg
  set v₀ := refData F E w δ s' with hv₀
  have hdata : v₀ ω = fun j : Fin N => if Int.natAbs ((j : ℤ) -
      ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
      then (0 : ℝ) else 1 := by
    funext j
    simp only [hv₀, refData, Set.indicator_of_mem hA, one_mul]
    exact refJc_eq hH E w j
  -- the forward solution from `s`
  have hc := genCoeff_continuous hGc hF s'
  have hsol := adaptedMass_solution hc v₀ ω (T := c - s) (by linarith)
  have hsh := forwardMass_unshift (s := s) hsol
  rw [show s + (c - s) = c by ring] at hsh
  have hfw := forwardMass_congr hsh (L' := referenceGenerator F a b₀ ω ℓ) (fun σ hσ => by
    have hσa : a ≤ σ := has.trans hσ.1.le
    simp only [realCoeff, genCoeff, hGen]
    rw [referenceGenerator_eq_trunc hσa hH hℓ hg.le (fun i j hij => hgaps _ (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]
      linarith [hσ.2]) i j hij)]
    congr 2
    rw [hs', ← Real.toNNReal_add (by linarith) (by linarith [hσ.1])]
    congr 1; ring)
  have hpair := backward_forward_pairing hP has hsc hfw k
  rw [hdata] at hpair
  rw [Finset.sum_congr rfl fun j _ => mul_comm _ (P s k j), hpair]
  -- terminal weight
  have hvnn : ∀ j, 0 ≤ genMass Gen F s' v₀ T ω j := fun j =>
    (genMass_mem_unit hGc (truncRefGen_isSubGenField ℓ b₀ g) hF s' (refData_mem F E w δ s') T
      ω j).1
  have hterm := terminal_le (ν := ν) (E := 0) (d := d) (R := Rc) hν hd hRc
    (fun j => flowLam F (s' + T) ω j - E) (genMass Gen F s' v₀ T ω) hvnn k
  have hlamc : flowLam F (s' + T) ω = flowEigenvalue F a ω c := by
    rw [flowLam_shift_eq F has hH T, hTr]; congr 1; ring
  have hgm : genMass Gen F s' v₀ T ω k = adaptedMass (genCoeff Gen F s') v₀ (c - s) ω k := by
    simp only [genMass, hTr]
  rw [hgm] at hterm
  refine hterm.trans ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hν)) ?_
  · rw [hlamc, sub_zero]; exact hk
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (rlPhi_pos _).le (hvnn j)

/-- The jointly measurable weighted mass `Y(s, ω)` (avoidance on the whole window). -/
def refY (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (a c E : ℝ)
    (w : ℕ) (δ : ℝ) (Kh : Set (ℝ × (Fin N → ℝ))) (φ : ℝ → ℝ) (p : ℝ × FlowSample N) : ℝ :=
  (avoidSet F 0 (fun _ => E) Kh (Real.toNNReal (c - a))).indicator (fun _ => (1 : ℝ)) p.2 *
    ∑ k, φ (flowLam F (Real.toNNReal (p.1 - a) + Real.toNNReal (c - p.1)) p.2 k - E) *
      adaptedMass (coeffP Gen F a) (dataP F E w δ a) ((Real.toNNReal (c - p.1) : ℝ≥0) : ℝ) p k

theorem measurable_refY {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a c E : ℝ) (w : ℕ) (δ : ℝ)
    {Kh : Set (ℝ × (Fin N → ℝ))} (hKh : IsClosed Kh) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Measurable (refY Gen F a c E w δ Kh φ) := by
  have hAv := measurableSet_avoidSet hF 0 (c₀ := fun _ => E) (@measurable_const _ _ _ _ E) hKh
    (Real.toNNReal (c - a))
  have hT : Measurable (fun p : ℝ × FlowSample N => Real.toNNReal (c - p.1)) :=
    ((by fun_prop : Continuous fun x : ℝ => Real.toNNReal (c - x)).measurable).comp measurable_fst
  have hM := measurable_genMassP hG hF E w δ a hT
  have hf1 : Measurable (fun p : ℝ × FlowSample N =>
      (Real.toNNReal (p.1 - a) + Real.toNNReal (c - p.1), p.2)) :=
    (((by fun_prop : Continuous fun x : ℝ => Real.toNNReal (x - a) + Real.toNNReal (c - x)).measurable).comp
      measurable_fst).prodMk measurable_snd
  have hL := (measurable_flowLam_joint hF).comp hf1
  refine ((measurable_const.indicator hAv).comp measurable_snd).mul ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (hφ.measurable.comp (((measurable_pi_apply k).comp hL).sub measurable_const)).mul
    ((measurable_pi_apply k).comp hM)

theorem refY_eq (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ)
    (a c E : ℝ) (w : ℕ) (δ : ℝ) (Kh : Set (ℝ × (Fin N → ℝ))) (φ : ℝ → ℝ) (s : ℝ)
    (ω : FlowSample N) :
    refY Gen F a c E w δ Kh φ (s, ω) =
      (avoidSet F 0 (fun _ => E) Kh (Real.toNNReal (c - a))).indicator
        (goodMass Gen F (Real.toNNReal (s - a)) (refData F E w δ (Real.toNNReal (s - a)))
          (fun _ => E) φ (Real.toNNReal (c - s))) ω := by
  simp only [refY]
  simp only [genMass_eq_P]
  by_cases hω : ω ∈ avoidSet F 0 (fun _ => E) Kh (Real.toNNReal (c - a))
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul]
    simp only [goodMass, genMass]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]

theorem avoidSet_zero_subset (F : Matrix (Fin N) (Fin N) ℂ) {a c s : ℝ} (has : a ≤ s)
    (hsc : s ≤ c) (E : ℝ) (Kh : Set (ℝ × (Fin N → ℝ))) :
    avoidSet F 0 (fun _ => E) Kh (Real.toNNReal (c - a)) ⊆
      avoidSet F (Real.toNNReal (s - a)) (fun _ => E) Kh (Real.toNNReal (c - s)) := by
  intro ω hω u hu
  have h := hω (Real.toNNReal (s - a) + u) (by
    rw [← NNReal.coe_le_coe]; push_cast
    rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]
    have : (u : ℝ) ≤ c - s := by
      have := NNReal.coe_le_coe.mpr hu; rwa [Real.coe_toNNReal _ (by linarith)] at this
    linarith)
  simpa [cenLam] using h

/-- **Reference core.** -/
theorem ref_core (hIto : SemimartingaleItoFormula (N + N)) (hStop : StoppedSemimartingale 1)
    (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) {E r₀ : ℝ} (_hr₀ : 0 < r₀) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {c₁ C₁ C b₀ h D₀ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hC : 0 < C) (b₀' : ℝ) (w : ℕ)
    (Cw : ℝ) {ν d Rc K thr : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hRc : 0 < Rc)
    (hρ : d + 2 * Rc ≤ r₀ / 32) (hK0 : 0 ≤ K) (hK : rowKappa N ℓ ν d Rc c₁ C₁ ≤ K)
    (hthr : 0 < thr) :
    flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
        ∃ P, BackwardPropagator (referenceGenerator F a b₀' ω ℓ) a c P ∧
          ENNReal.ofReal thr <
            ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∑ j : Fin N,
              (if Int.natAbs ((j : ℤ) -
                  ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                then 0 else 1) * P s k j)} ≤
      flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a c, goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ} +
      ENNReal.ofReal ((c - a) * (Real.exp (ν * (Cw / N)) * (Real.exp (K * (c - a)) *
        (N * Real.exp (-(ν * min ((((w : ℝ) + 1) / (C * N) - h - D₀) - d) Rc)))))) /
        ENNReal.ofReal thr := by
  classical
  set μ := flowLaw N a
  set δ : ℝ := ((w : ℝ) + 1) / (C * N) - h - D₀ with hδ
  set T' := Real.toNNReal (c - a) with hT'
  set IM : ℝ := (N : ℝ) * Real.exp (-(ν * min (δ - d) Rc)) with hIM
  set e : ℝ := Real.exp (ν * (Cw / N)) with he
  set φ := rlPhi ν 0 d Rc with hφ
  set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hgdef
  have hgpos : ∀ n, 0 < g n := fun n => by simp only [hgdef]; positivity
  set Gen : ℕ → (Fin N → ℝ) → Fin N → Fin N → ℝ := fun n lam => truncRefGen N lam ℓ b₀' (g n)
  set Kh : ℕ → Set (ℝ × (Fin N → ℝ)) := fun n => centreSet N ℓ E r₀ c₁ C₁ (g n)
  have hGc : ∀ n, Continuous (Gen n) := fun n => continuous_truncRefGen ℓ b₀' (hgpos n)
  have hGs : ∀ n, IsSubGenField (Gen n) := fun n => truncRefGen_isSubGenField ℓ b₀' (g n)
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  have hφ1 : ∀ z, φ z ≤ 1 := rlPhi_le_one hν hRc
  have hφc : Continuous φ := (rlPhi_contDiff hd hRc).continuous
  set Y : ℕ → ℝ × FlowSample N → ℝ := fun n => refY (Gen n) F a c E w δ (Kh n) φ with hYdef
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    measurable_refY (hGc n) hF a c E w δ (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n)) hφc
  have hbdd : ∀ n (s : ℝ) u' ω, 0 ≤ goodMass (Gen n) F (Real.toNNReal (s - a))
      (refData F E w δ (Real.toNNReal (s - a))) (fun _ => E) φ u' ω ∧
      goodMass (Gen n) F (Real.toNNReal (s - a)) (refData F E w δ (Real.toNNReal (s - a)))
        (fun _ => E) φ u' ω ≤ 1 * N := fun n s =>
    goodMass_le (hGc n) (hGs n) hF _ (refData_mem F E w δ _) _ hφ0 hφ1
  have hY0 : ∀ n p, 0 ≤ Y n p := fun n p => by
    rw [hYdef]; simp only []
    rw [show p = (p.1, p.2) from rfl, refY_eq]
    simp only [Set.indicator]; split_ifs
    · exact (hbdd n _ _ _).1
    · exact le_rfl
  set Z : ℕ → FlowSample N → ℝ≥0∞ := fun n ω =>
    ∫⁻ s in Set.Icc a c, ENNReal.ofReal (e * Y n (s, ω)) with hZdef
  -- per-start expectation
  have hper : ∀ n, ∀ s ∈ Set.Icc a c, ∫⁻ ω, ENNReal.ofReal (e * Y n (s, ω)) ∂μ ≤
      ENNReal.ofReal (e * (Real.exp (K * (c - a)) * IM)) := by
    intro n s hs
    set s' := Real.toNNReal (s - a)
    set T := Real.toNNReal (c - s)
    have hTr : (T : ℝ) = c - s := Real.coe_toNNReal _ (by linarith [hs.2])
    have hv₀m := refData_measurable F E w δ s'
    have hcm : Measurable[flowFiltration N s'] (fun _ : FlowSample N => E) := measurable_const
    have hexp := gen_expectation_avoid hIto hStop hDBM hF a s' (hGc n) (hGs n) hv₀m
      (refData_mem F E w δ s') hcm (rlPhi_hasDerivAt hd hRc) (rlPhi1_hasDerivAt hd hRc)
      (rlPhi_contDiff hd hRc) hφ0 hφ1 (abs_rlPhi1_le_abs hd hRc)
      (mul_nonneg (abs_nonneg _) weightConst_pos.le) (abs_rlPhi2_le_abs hd hRc)
      (add_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (div_nonneg weightConst_pos.le hRc.le)
        (div_nonneg weightConst_pos.le hd.le))) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Real.exp_pos _).le
      (fun x z hxz => (rlPhi_le_exp_mul_abs hd hRc x z).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hxz (mul_nonneg (abs_nonneg _) weightConst_pos.le)))
          (rlPhi_pos x).le))
      (half_pos hc₁) hK0 hK (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n))
      (fun c' lam hcl => hcond_centreSet (Gen := Gen n)
        (fun lam hgap v hv k => truncRefGen_dom hℓ (hgpos n).le lam hgap v hv k) hRc hρ c' lam hcl) T
    have hint : ∀ u, Integrable (goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ u) μ :=
      fun u => Integrable.of_bound (goodMass_measurable (hGc n) hF s' hv₀m hcm hφc u).aestronglyMeasurable
        (1 * N) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hbdd n s u ω).1]; exact (hbdd n s u ω).2)
    have hinit : ∫ ω, goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ 0 ω ∂μ ≤ IM := by
      have hpt : ∀ ω, goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ 0 ω ≤ IM := by
        intro ω
        have h0 : genMass (Gen n) F s' (refData F E w δ s') 0 ω = refData F E w δ s' ω :=
          (adaptedMass_solution (genCoeff_continuous (hGc n) hF s') _ ω le_rfl).1
        simp only [goodMass, h0, add_zero]
        by_cases hωA : ω ∈ refA F E w δ s'
        · have := initial_mass_le (ν := ν) (E := 0) (d := d) (R := Rc) (δ := δ) hν hRc
            (fun j => flowLam F s' ω j - E) (fun j => refJc N E w (flowLam F 0 ω) j = 1)
            (fun j hj => by simpa using hωA j hj)
          refine le_trans (le_of_eq ?_) this
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [refData, Set.indicator_of_mem hωA, one_mul]
          congr 1
          unfold refJc; split_ifs <;> simp_all
        · simp only [refData, Set.indicator_of_notMem hωA, zero_mul, mul_zero,
            Finset.sum_const_zero]
          positivity
      calc _ ≤ ∫ _ω, IM ∂μ := integral_mono_of_nonneg
            (Eventually.of_forall fun ω => (hbdd n s 0 ω).1) (integrable_const _)
            (Eventually.of_forall hpt)
        _ = IM := by simp
    -- avoid on the whole window implies avoid from `s`
    have hsub := avoidSet_zero_subset F hs.1 hs.2 E (Kh n)
    have hAvm := measurableSet_avoidSet hF 0 (c₀ := fun _ => E) (@measurable_const _ _ _ _ E)
      (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n)) T'
    have hAvsm := measurableSet_avoidSet hF s' hcm (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n)) T
    have hYs : ∀ ω, Y n (s, ω) = (avoidSet F 0 (fun _ => E) (Kh n) T').indicator
        (goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ T) ω := fun ω =>
      refY_eq (Gen n) F a c E w δ (Kh n) φ s ω
    have hYle : ∫ ω, Y n (s, ω) ∂μ ≤
        ∫ ω, (avoidSet F s' (fun _ => E) (Kh n) T).indicator
          (goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ T) ω ∂μ := by
      simp only [hYs]
      refine integral_mono ((hint T).indicator hAvm) ((hint T).indicator hAvsm) fun ω => ?_
      simp only [Set.indicator]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (hsub h1) h2
      · exact (hbdd n s T ω).1
      · exact le_rfl
    have hYint : Integrable (fun ω => e * Y n (s, ω)) μ := by
      refine ((hint T).indicator hAvm).const_mul e |>.congr (Eventually.of_forall fun ω => ?_)
      simp only [hYs]
      rfl
    have hexpT : Real.exp (K * T) ≤ Real.exp (K * (c - a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by rw [hTr]; linarith [hs.1]) hK0)
    have hmain : ∫ ω, Y n (s, ω) ∂μ ≤ Real.exp (K * (c - a)) * IM := by
      have he1 : Real.exp (-(K * T)) * Real.exp (K * T) = 1 := by rw [← Real.exp_add]; simp
      have hI := hexp
      calc ∫ ω, Y n (s, ω) ∂μ ≤ _ := hYle
        _ = Real.exp (K * T) * (Real.exp (-(K * T)) * ∫ ω, (avoidSet F s' (fun _ => E) (Kh n) T).indicator
            (goodMass (Gen n) F s' (refData F E w δ s') (fun _ => E) φ T) ω ∂μ) := by
            rw [← mul_assoc, mul_comm (Real.exp (K * T)), he1, one_mul]
        _ ≤ Real.exp (K * T) * IM :=
            mul_le_mul_of_nonneg_left (hI.trans hinit) (Real.exp_pos _).le
        _ ≤ Real.exp (K * (c - a)) * IM := mul_le_mul_of_nonneg_right hexpT (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hYint
      (Eventually.of_forall fun ω => mul_nonneg (Real.exp_pos _).le (hY0 n _))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
  -- the expectation of `Z`
  have hGm : ∀ n, Measurable (fun q : FlowSample N × ℝ => ENNReal.ofReal (e * Y n (q.2, q.1))) :=
    fun n => ENNReal.measurable_ofReal.comp (measurable_const.mul ((hYm n).comp measurable_swap))
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    (hGm n).lintegral_prod_right' (ν := volume.restrict (Set.Icc a c))
  have hZe : ∀ n, ∫⁻ ω, Z n ω ∂μ ≤
      ENNReal.ofReal ((c - a) * (e * (Real.exp (K * (c - a)) * IM))) := by
    intro n
    simp only [hZdef]
    rw [lintegral_lintegral_swap ((hGm n).aemeasurable)]
    calc ∫⁻ s in Set.Icc a c, ∫⁻ ω, ENNReal.ofReal (e * Y n (s, ω)) ∂μ
        ≤ ∫⁻ _s in Set.Icc a c, ENNReal.ofReal (e * (Real.exp (K * (c - a)) * IM)) :=
          setLIntegral_mono' measurableSet_Icc fun s hs => hper n s hs
      _ = ENNReal.ofReal (e * (Real.exp (K * (c - a)) * IM)) * ENNReal.ofReal (c - a) := by
          rw [setLIntegral_const, Real.volume_Icc]
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
  -- the inclusion
  set Nul : Set (FlowSample N) := {ω | ¬ ω.1.IsHermitian}
  have hNul : μ Nul = 0 := ae_iff.mp (ae_fst_isHermitian (N := N) a)
  refine markov_limit_lint μ _ _ Nul (fun n => gapEvent F T' (g n)) Z
    (by simp [hthr]) ENNReal.ofReal_ne_top hNul (tendsto_gapEvent hDBM hF ha T')
    (fun n => (hZm n).aemeasurable) hZe (fun n ω hω => ?_)
  obtain ⟨k, hk, P, hP, hlt⟩ := hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, Nul] at hcon
  obtain ⟨⟨⟨hgood, hH⟩, hgap⟩, hZle⟩ := hcon
  have hN : 0 < N := Fin.pos k
  have hgaps : ∀ r : ℝ≥0, r ≤ T' → ∀ i j : Fin N, i ≠ j →
      g n < |flowLam F r ω i - flowLam F r ω j| := by
    intro r hr i j hij
    by_contra hlt'; push Not at hlt'
    exact hgap ⟨r, hr, i, j, hij, hlt'⟩
  have hga : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ a := hgood a ⟨le_rfl, hac⟩
  -- avoidance on the whole window
  have hav : ω ∈ avoidSet F 0 (fun _ => E) (Kh n) T' := by
    intro r hr hK'
    simp only [cenLam, Kh, centreSet, Set.mem_ofPred_eq, Set.mem_union] at hK'
    have hlr := flowLam_shift_eq F (le_refl a) hH r
    simp only [sub_self, Real.toNNReal_zero, zero_add] at hlr
    have hrc : (a + r : ℝ) ≤ c := by
      have := NNReal.coe_le_coe.mpr hr; rw [hT', Real.coe_toNNReal _ (by linarith)] at this
      linarith
    rcases hK' with (hf | hgp) | hcE
    · rw [zero_add, hlr] at hf
      exact clauses_not_fail hℓ hc₁ hC₁ hN (hgood (a + r) ⟨by
        have := NNReal.coe_nonneg r; linarith, hrc⟩) hf
    · obtain ⟨i, j, hij, hle⟩ := hgp
      rw [zero_add] at hle
      have := hgaps r hr i j hij
      linarith
    · simp at hcE; linarith
  -- pointwise domination of the integrand
  have hpt : ∀ s ∈ Set.Icc a c, ENNReal.ofReal (∑ j : Fin N,
      (if Int.natAbs ((j : ℤ) -
          ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
        then 0 else 1) * P s k j) ≤ ENNReal.ofReal (e * Y n (s, ω)) := by
    intro s hs
    refine ENNReal.ofReal_le_ofReal ?_
    have hgs : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ s := hgood s hs
    have hA : ω ∈ refA F E w δ (Real.toNNReal (s - a)) := by
      intro j hj
      have hlam0 : flowLam F 0 ω = flowEigenvalue F a ω a := by
        have := flowLam_shift_eq F (le_refl a) hH 0; simpa using this
      have hlams : flowLam F (Real.toNNReal (s - a)) ω = flowEigenvalue F a ω s := by
        have := flowLam_shift_eq F hs.1 hH 0; simpa using this
      rw [hlams]
      have hjw : w < Int.natAbs ((j : ℤ) -
          ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) := by
        rw [refJc, hlam0] at hj
        by_contra hle; push Not at hle; simp [hle] at hj
      exact far_of_not_window_flow (flowMatrix_isHermitian hF a hH a)
        (flowMatrix_isHermitian hF a hH s) E w hC hga.2.2.1 hgs.2.2.2.2.2 j hjw
    have := ref_pointwise hF hs.1 hs.2 hH hℓ (hgpos n) (fun r hr i j hij => (hgaps r hr i j hij).le)
      hA hν hd hRc hk hP (b₀ := b₀')
    rw [show Y n (s, ω) = _ from refY_eq (Gen n) F a c E w δ (Kh n) φ s ω,
      Set.indicator_of_mem hav]
    exact this
  have hle := setLIntegral_mono' (μ := volume) measurableSet_Icc hpt
  exact absurd (lt_of_lt_of_le hlt hle) (not_lt.mpr hZle)

/-- The constant of `rowKappa_le_gen`. -/
def kappaConst' (Rc c₁ C₁ : ℝ) : ℝ :=
  2 * Real.exp (2 * weightConst * C₁) * (weightConst / Rc + weightConst + weightConst ^ 2) +
    4 * weightConst / c₁ + (weightConst / Rc + weightConst + weightConst ^ 2)

theorem kappaConst'_pos {Rc c₁ C₁ : ℝ} (hRc : 0 < Rc) (hc₁ : 0 < c₁) :
    0 < kappaConst' Rc c₁ C₁ := by
  have := weightConst_pos; unfold kappaConst'; positivity

/-- `κ ≤ X (ν²ℓ/N + ν(1 + log N) + ν²/N)` at `νd = 1`, `νℓ/N ≤ 1`, `ν ≥ 1`. -/
theorem rowKappa_le_gen {N ℓ : ℕ} {ν d Rc c₁ C₁ : ℝ} (hN : (1 : ℝ) ≤ N) (hRc : 0 < Rc)
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hν1 : 1 ≤ ν) (hνd : ν * d = 1)
    (hνl : ν * (ℓ / N) ≤ 1) (_hℓ0 : (0 : ℝ) ≤ ℓ) :
    rowKappa N ℓ ν d Rc c₁ C₁ ≤
      kappaConst' Rc c₁ C₁ * (ν ^ 2 * (ℓ / N) + ν * (1 + Real.log N) + ν ^ 2 / N) := by
  have hC0 := weightConst_pos
  have hν0 : 0 < ν := lt_of_lt_of_le one_pos hν1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hd : d = 1 / ν := by field_simp; linarith
  set X := weightConst / Rc + weightConst + weightConst ^ 2 with hX
  have hX0 : 0 < X := by positivity
  set e := Real.exp (2 * weightConst * C₁) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hexp : Real.exp (|ν| * weightConst * (2 * C₁ * ℓ / N)) ≤ e := by
    rw [he, Real.exp_le_exp, abs_of_pos hν0]
    have : ν * weightConst * (2 * C₁ * ℓ / N) = 2 * weightConst * C₁ * (ν * (ℓ / N)) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hνl
  have hB : |ν| * (weightConst / Rc + weightConst / d) + ν ^ 2 * weightConst ^ 2 =
      ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2) := by
    rw [abs_of_pos hν0, hd]; field_simp; ring
  have hBle : ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2) ≤ X * ν ^ 2 := by
    have : ν ≤ ν ^ 2 := by nlinarith
    rw [hX]; nlinarith [div_pos hC0 hRc]
  have hB0 : 0 ≤ ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2) := by positivity
  unfold rowKappa
  rw [hB, abs_of_pos hν0]
  have hT1 : 2 * ℓ * (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) *
      Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N ≤ 2 * e * X * (ν ^ 2 * (ℓ / N)) := by
    have hexp' : Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ≤ e := by
      have := hexp; rwa [abs_of_pos hν0] at this
    calc _ = 2 * ((ℓ : ℝ) / N) * (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) *
          Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) := by field_simp
      _ ≤ 2 * ((ℓ : ℝ) / N) * (X * ν ^ 2) * e := by
          have h1 : 0 ≤ 2 * ((ℓ : ℝ) / N) := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hBle h1) hexp' (Real.exp_pos _).le
            (mul_nonneg h1 (by positivity))
      _ = 2 * e * X * (ν ^ 2 * (ℓ / N)) := by ring
  have hT2 : 2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) =
      4 * weightConst / c₁ * (ν * (1 + Real.log N)) := by field_simp; ring
  have hT3 : (ν * (weightConst / Rc) + ν ^ 2 * (weightConst + weightConst ^ 2)) / (2 * N) ≤
      X * (ν ^ 2 / N) := by
    calc _ ≤ X * ν ^ 2 / (2 * N) := div_le_div_of_nonneg_right hBle (by positivity)
      _ ≤ X * ν ^ 2 / N := div_le_div_of_nonneg_left (by positivity) hNpos (by linarith)
      _ = _ := by ring
  rw [hT2]
  have hsum : 0 ≤ ν ^ 2 * (ℓ / N) := by positivity
  have hsum2 : 0 ≤ ν * (1 + Real.log N) := by positivity
  have hsum3 : 0 ≤ ν ^ 2 / N := by positivity
  calc _ ≤ 2 * e * X * (ν ^ 2 * (ℓ / N)) + 4 * weightConst / c₁ * (ν * (1 + Real.log N)) +
        X * (ν ^ 2 / N) := by linarith
    _ ≤ _ := by
        unfold kappaConst'
        rw [← hX, ← he]
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * e * X) hsum2,
          mul_nonneg (by positivity : (0:ℝ) ≤ 2 * e * X) hsum3,
          mul_nonneg (by positivity : (0:ℝ) ≤ 4 * weightConst / c₁) hsum,
          mul_nonneg (by positivity : (0:ℝ) ≤ 4 * weightConst / c₁) hsum3,
          mul_nonneg hX0.le hsum, mul_nonneg hX0.le hsum2]

/-- **The scales** of the reference finite-speed estimate. -/
theorem ref_scales {r₀ c C c₁ C₁ Cw : ℝ} (hr₀ : 0 < r₀) (hc : 0 < c) (hC : 0 < C)
    (hc₁ : 0 < c₁) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ ∧
      (N : ℝ) ^ (-(19 / 10000 : ℝ)) + 2 * (r₀ / 128) ≤ r₀ / 32 ∧
      0 < c - (N : ℝ) ^ (-(1 / 500 : ℝ)) ∧
      kappaConst' (r₀ / 128) c₁ C₁ * (((N : ℝ) ^ (19 / 10000 : ℝ)) ^ 2 *
          (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ / N) +
        (N : ℝ) ^ (19 / 10000 : ℝ) * (1 + Real.log N) +
        ((N : ℝ) ^ (19 / 10000 : ℝ)) ^ 2 / N) * (N : ℝ) ^ (-(1 / 500 : ℝ)) ≤ 1 ∧
      (N : ℝ) ^ (19 / 10000 : ℝ) * (Cw / N) ≤ 1 ∧
      1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ) ≤ (N : ℝ) ^ (19 / 10000 : ℝ) *
        min ((((⌈(N : ℝ) * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ))) *
            (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) + 1) / (C * N) -
          (N : ℝ) ^ (-(1 / 100 : ℝ)) - C * Real.sqrt ((N : ℝ) ^ (-(1 / 500 : ℝ)))) -
          (N : ℝ) ^ (-(19 / 10000 : ℝ))) (r₀ / 128) ∧
      2 * Real.exp 2 * ((N : ℝ) ^ (2 * D + 1) *
        Real.exp (-(1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ)))) ≤ 1 ∧
      (2 : ℝ) ≤ N ∧
      (N : ℝ) ^ (19 / 10000 : ℝ) * (⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊ / N) ≤ 1 ∧
      1 ≤ (N : ℝ) ^ (19 / 10000 : ℝ) ∧
      (N : ℝ) ^ (19 / 10000 : ℝ) * (N : ℝ) ^ (-(19 / 10000 : ℝ)) = 1 ∧
      (N : ℝ) ^ (-(1 / 500 : ℝ)) ≤ 1 := by
  set X := kappaConst' (r₀ / 128) c₁ C₁ with hXdef
  have hX : 0 < X := kappaConst'_pos (by positivity) hc₁
  filter_upwards [ev_rpow_ge (p := (1 - 13 / 5000 : ℝ)) (by norm_num) 2,
    ev_rpow_neg_le (p := (19 / 10000 : ℝ)) (by norm_num) (by positivity : 0 < r₀ / 64),
    ev_rpow_neg_le (p := (1 / 500 : ℝ)) (by norm_num) (by positivity : 0 < c / 2),
    ev_rpow_neg_le (p := (8 / 10000 : ℝ)) (by norm_num) (by positivity : 0 < 1 / (3 * X)),
    ev_log_le (r := 1 / 10000) (by norm_num) (3 * X),
    ev_rpow_neg_le (p := (9982 / 10000 : ℝ)) (by norm_num) (by positivity : 0 < 1 / (3 * X)),
    ev_rpow_neg_le (p := (9981 / 10000 : ℝ)) (by norm_num) (by positivity : 0 < 1 / (|Cw| + 1)),
    ev_rpow_neg_le (p := (81 / 10000 : ℝ)) (by norm_num) (by norm_num : (0 : ℝ) < 1),
    ev_rpow_ge (p := (2 / 10000 : ℝ)) (by norm_num) (4 * C ^ 2),
    ev_rpow_ge (p := (11 / 10000 : ℝ)) (by norm_num) (8 * C),
    ev_rpow_ge (p := (8 / 10000 : ℝ)) (by norm_num) (1 / (2 * C) / (r₀ / 128)),
    ev_poly_exp_le (2 * D + 1) (by positivity : 0 < 1 / (2 * C)) (by norm_num : (0 : ℝ) < 11 / 10000)
      (by positivity : (0 : ℝ) < 1 / (2 * Real.exp 2)),
    ev_natCast_ge 2] with N e1 e2 e3 e4a e4b e4c e5 e6a e6b e6c e6d e7 e8
  set x : ℝ := (N : ℝ) with hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have rp : ∀ p q : ℝ, x ^ p * x ^ q = x ^ (p + q) := fun p q => (Real.rpow_add hx0 p q).symm
  have rpos : ∀ p : ℝ, 0 < x ^ p := fun p => Real.rpow_pos_of_pos hx0 p
  set P := x ^ (1 - 13 / 5000 : ℝ) with hPdef
  set ℓ := ⌊P⌋₊ with hℓdef
  have hP0 : 0 ≤ P := (rpos _).le
  have hℓP : (ℓ : ℝ) ≤ P := Nat.floor_le hP0
  have hℓP2 : P / 2 ≤ ℓ := floor_ge_half e1
  have hℓ1 : (1 : ℝ) ≤ ℓ := by linarith
  have hPx : P = x * x ^ (-(26 / 10000 : ℝ)) := by
    rw [hPdef, show (1 - 13 / 5000 : ℝ) = 1 + -(26 / 10000) by norm_num, Real.rpow_add hx0,
      Real.rpow_one]
  have hℓx : (ℓ : ℝ) / x ≤ x ^ (-(26 / 10000 : ℝ)) := by
    rw [div_le_iff₀ hx0]; nlinarith [hℓP, hPx]
  set ν := x ^ (19 / 10000 : ℝ) with hν
  have hν1 : 1 ≤ ν := Real.one_le_rpow hx1 (by norm_num)
  have hν2 : ν ^ 2 = x ^ (38 / 10000 : ℝ) := by rw [sq, hν, rp]; norm_num
  have hνd : ν * x ^ (-(19 / 10000 : ℝ)) = 1 := by rw [hν, rp]; simp
  have ht1 : x ^ (-(1 / 500 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  have hνl : ν * ((ℓ : ℝ) / x) ≤ 1 := by
    calc ν * ((ℓ : ℝ) / x) ≤ ν * x ^ (-(26 / 10000 : ℝ)) :=
          mul_le_mul_of_nonneg_left hℓx (rpos _).le
      _ = x ^ (-(7 / 10000 : ℝ)) := by rw [hν, rp]; norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
  refine ⟨hℓ1, by linarith, by linarith, ?_, ?_, ?_, ?_, e8, hνl, hν1, hνd, ht1⟩
  · -- the tilt over the window
    have h1 : ν ^ 2 * ((ℓ : ℝ) / x) * x ^ (-(1 / 500 : ℝ)) ≤ x ^ (-(8 / 10000 : ℝ)) := by
      calc ν ^ 2 * ((ℓ : ℝ) / x) * x ^ (-(1 / 500 : ℝ))
          ≤ x ^ (38 / 10000 : ℝ) * x ^ (-(26 / 10000 : ℝ)) * x ^ (-(1 / 500 : ℝ)) := by
            rw [hν2]; gcongr
        _ = x ^ (-(8 / 10000 : ℝ)) := by rw [rp, rp]; norm_num
    have h2 : ν * (1 + Real.log x) * x ^ (-(1 / 500 : ℝ)) =
        (1 + Real.log x) * x ^ (-(1 / 10000 : ℝ)) := by
      rw [hν, mul_comm _ (1 + Real.log x), mul_assoc, rp]; norm_num
    have h3 : ν ^ 2 / x * x ^ (-(1 / 500 : ℝ)) = x ^ (-(9982 / 10000 : ℝ)) := by
      rw [hν2, div_eq_mul_inv, ← Real.rpow_neg_one, rp, rp]; norm_num
    have h2' : X * ((1 + Real.log x) * x ^ (-(1 / 10000 : ℝ))) ≤ 1 / 3 := by
      have hlog0 : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg hx1; linarith
      have hinv : x ^ (1 / 10000 : ℝ) * x ^ (-(1 / 10000 : ℝ)) = 1 := by rw [rp]; simp
      calc X * ((1 + Real.log x) * x ^ (-(1 / 10000 : ℝ)))
          = (3 * X * (1 + Real.log x)) * x ^ (-(1 / 10000 : ℝ)) / 3 := by ring
        _ ≤ x ^ (1 / 10000 : ℝ) * x ^ (-(1 / 10000 : ℝ)) / 3 := by
            gcongr
        _ = 1 / 3 := by rw [hinv]
    calc X * (ν ^ 2 * ((ℓ : ℝ) / x) + ν * (1 + Real.log x) + ν ^ 2 / x) * x ^ (-(1 / 500 : ℝ))
        = X * (ν ^ 2 * ((ℓ : ℝ) / x) * x ^ (-(1 / 500 : ℝ))) +
          X * (ν * (1 + Real.log x) * x ^ (-(1 / 500 : ℝ))) +
          X * (ν ^ 2 / x * x ^ (-(1 / 500 : ℝ))) := by ring
      _ ≤ X * (1 / (3 * X)) + 1 / 3 + X * (1 / (3 * X)) := by
          rw [h2, h3]
          gcongr
          · exact h1.trans e4a
      _ = 1 := by field_simp; ring
  · -- terminal factor
    have hb : ν * (Cw / x) ≤ ν * (|Cw| / x) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (le_abs_self Cw) hx0.le) (rpos _).le
    refine hb.trans ?_
    have : ν * (|Cw| / x) = |Cw| * x ^ (-(9981 / 10000 : ℝ)) := by
      have h1 : ν * (|Cw| / x) = |Cw| * (ν * x⁻¹) := by ring
      have h2 : ν * x⁻¹ = x ^ (-(9981 / 10000 : ℝ)) := by
        rw [hν, ← Real.rpow_neg_one, rp]; norm_num
      rw [h1, h2]
    rw [this]
    calc |Cw| * x ^ (-(9981 / 10000 : ℝ)) ≤ |Cw| * (1 / (|Cw| + 1)) :=
          mul_le_mul_of_nonneg_left e5 (abs_nonneg _)
      _ ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith
  · -- the initial weight exponent
    have hst : Real.sqrt (x ^ (-(1 / 500 : ℝ))) = x ^ (-(1 / 1000 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
    rw [hst]
    set W := (⌈x * x ^ (-(1 / 1000 : ℝ)) * x ^ (2 * (1 / 10000 : ℝ))⌉₊ : ℝ) with hW
    have hW1 : x ^ (1 - 8 / 10000 : ℝ) ≤ W := by
      have : x * x ^ (-(1 / 1000 : ℝ)) * x ^ (2 * (1 / 10000 : ℝ)) = x ^ (1 - 8 / 10000 : ℝ) := by
        rw [show x * x ^ (-(1 / 1000 : ℝ)) = x ^ (1 : ℝ) * x ^ (-(1 / 1000 : ℝ)) by
          rw [Real.rpow_one], rp, rp]; norm_num
      rw [← this]; exact Nat.le_ceil _
    have hA : x ^ (11 / 10000 : ℝ) / C ≤ ν * ((W + 1) / (C * x)) := by
      have key : ν * x ^ (1 - 8 / 10000 : ℝ) = x ^ (11 / 10000 : ℝ) * x := by
        rw [hν, rp, show (19 / 10000 : ℝ) + (1 - 8 / 10000) = 11 / 10000 + 1 by norm_num,
          Real.rpow_add hx0, Real.rpow_one]
      have h1 : x ^ (11 / 10000 : ℝ) / C = ν * (x ^ (1 - 8 / 10000 : ℝ) / (C * x)) := by
        rw [← mul_div_assoc, key]; field_simp
      rw [h1]
      gcongr
      linarith
    have hB1 : ν * x ^ (-(1 / 100 : ℝ)) ≤ 1 := by
      rw [hν, rp]; exact (show (19 / 10000 : ℝ) + -(1 / 100) = -(81 / 10000) by norm_num) ▸ e6a
    have hB2 : ν * (C * x ^ (-(1 / 1000 : ℝ))) ≤ x ^ (11 / 10000 : ℝ) / (4 * C) := by
      have : ν * (C * x ^ (-(1 / 1000 : ℝ))) = C * x ^ (9 / 10000 : ℝ) := by
        rw [hν, mul_left_comm, rp]; norm_num
      rw [this, le_div_iff₀ (by positivity)]
      have h11 : x ^ (11 / 10000 : ℝ) = x ^ (2 / 10000 : ℝ) * x ^ (9 / 10000 : ℝ) := by
        rw [rp]; norm_num
      rw [h11]
      have h9 := rpos (9 / 10000 : ℝ)
      calc C * x ^ (9 / 10000 : ℝ) * (4 * C) = 4 * C ^ 2 * x ^ (9 / 10000 : ℝ) := by ring
        _ ≤ x ^ (2 / 10000 : ℝ) * x ^ (9 / 10000 : ℝ) := mul_le_mul_of_nonneg_right e6b h9.le
    have hB3 : 2 ≤ x ^ (11 / 10000 : ℝ) / (4 * C) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hRc : x ^ (11 / 10000 : ℝ) / (2 * C) ≤ ν * (r₀ / 128) := by
      have hν' : ν = x ^ (8 / 10000 : ℝ) * x ^ (11 / 10000 : ℝ) := by rw [hν, rp]; norm_num
      have h8 : 1 / (2 * C) ≤ x ^ (8 / 10000 : ℝ) * (r₀ / 128) := by
        have := e6d; rwa [div_le_iff₀ (by positivity)] at this
      have h11 := rpos (11 / 10000 : ℝ)
      calc x ^ (11 / 10000 : ℝ) / (2 * C) = x ^ (11 / 10000 : ℝ) * (1 / (2 * C)) := by ring
        _ ≤ x ^ (11 / 10000 : ℝ) * (x ^ (8 / 10000 : ℝ) * (r₀ / 128)) :=
            mul_le_mul_of_nonneg_left h8 h11.le
        _ = ν * (r₀ / 128) := by rw [hν']; ring
    rw [mul_min_of_nonneg _ _ (rpos _).le, le_min_iff]
    constructor
    · have hexp : ν * ((W + 1) / (C * x) - x ^ (-(1 / 100 : ℝ)) - C * x ^ (-(1 / 1000 : ℝ)) -
          x ^ (-(19 / 10000 : ℝ))) = ν * ((W + 1) / (C * x)) - ν * x ^ (-(1 / 100 : ℝ)) -
          ν * (C * x ^ (-(1 / 1000 : ℝ))) - 1 := by rw [← hνd]; ring
      rw [hexp]
      have : 1 / (2 * C) * x ^ (11 / 10000 : ℝ) = x ^ (11 / 10000 : ℝ) / C -
          2 * (x ^ (11 / 10000 : ℝ) / (4 * C)) := by field_simp; ring
      rw [this]
      linarith
    · calc 1 / (2 * C) * x ^ (11 / 10000 : ℝ) = x ^ (11 / 10000 : ℝ) / (2 * C) := by ring
        _ ≤ _ := hRc
  · have := mul_le_mul_of_nonneg_left e7 (by positivity : (0 : ℝ) ≤ 2 * Real.exp 2)
    calc _ ≤ 2 * Real.exp 2 * (1 / (2 * Real.exp 2)) := this
      _ = 1 := by field_simp

theorem ref_final {N : ℕ} {D y X : ℝ} (hN0 : (0 : ℝ) < N)
    (h : 2 * Real.exp 2 * ((N : ℝ) ^ (2 * D + 1) * Real.exp (-y)) ≤ 1)
    (hX : X ≤ Real.exp 2 * (N * Real.exp (-y))) : X / (N : ℝ) ^ (-D) ≤ (N : ℝ) ^ (-D) / 2 := by
  have hpos : 0 < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hid : (N : ℝ) / (N : ℝ) ^ (-D) = (N : ℝ) ^ (2 * D + 1) * (N : ℝ) ^ (-D) := by
    rw [div_eq_iff hpos.ne', mul_assoc, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    rw [show 2 * D + 1 + (-D + -D) = 1 by ring, Real.rpow_one]
  calc X / (N : ℝ) ^ (-D) ≤ Real.exp 2 * (N * Real.exp (-y)) / (N : ℝ) ^ (-D) :=
        div_le_div_of_nonneg_right hX hpos.le
    _ = Real.exp 2 * Real.exp (-y) * ((N : ℝ) / (N : ℝ) ^ (-D)) := by ring
    _ = 2 * Real.exp 2 * ((N : ℝ) ^ (2 * D + 1) * Real.exp (-y)) * ((N : ℝ) ^ (-D) / 2) := by
        rw [hid]; ring
    _ ≤ 1 * ((N : ℝ) ^ (-D) / 2) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := one_mul _

/-- **The `reference_finite_speed` field.** -/
theorem referenceFiniteSpeed_holds (hIto : ∀ N, SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : ∀ N, DysonBrownianMotion N)
    (hR : SpectralGoodEventContract) :
    ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ b₀ : ℝ, 0 < b₀ → ∀ Cw D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let w : ℕ := ⌈(N : ℝ) * Real.sqrt t * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
      flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
          ∃ P, BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c P ∧
            ENNReal.ofReal ((N : ℝ) ^ (-D)) <
              ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∑ j : Fin N,
                (if Int.natAbs ((j : ℤ) -
                    ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                  then 0 else 1) * P s k j)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
  intro A c r₀ s₀ v₀ hK b₀ _hb₀ Cw D
  have hc0 : 0 < c := hK.1
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨c₁, C₁, C, b₀R, hc₁, hC₁, hC, hb₀R, hD⟩ := hR A c r₀ s₀ v₀ hK
  obtain ⟨N₁, hN₁⟩ := hD (D + 1)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (ref_scales (C₁ := C₁) (Cw := Cw) hr₀ hc0 hC hc₁ D)
  refine ⟨max N₁ N₂, fun N hN F E hFC => ?_⟩
  intro t a ℓ w
  obtain ⟨hℓ1, hρ, ha0, hκ, hCw, hmin, hfin, hN2, hνl, hν1, hνd, ht1⟩ :=
    hN₂ N (le_of_max_le_right hN)
  have hℓ1 : (1 : ℝ) ≤ ℓ := hℓ1
  have hνl : (N : ℝ) ^ (19 / 10000 : ℝ) * ((ℓ : ℝ) / N) ≤ 1 := hνl
  have ha0 : 0 < a := ha0
  have hF : F.IsHermitian := hFC.1
  have hN0 : (0 : ℝ) < N := by linarith
  have hℓ1' : 1 ≤ ℓ := by exact_mod_cast hℓ1
  set ν : ℝ := (N : ℝ) ^ (19 / 10000 : ℝ) with hν
  set d : ℝ := (N : ℝ) ^ (-(19 / 10000 : ℝ)) with hd
  have hd0 : 0 < d := Real.rpow_pos_of_pos hN0 _
  set K := rowKappa N ℓ ν d (r₀ / 128) c₁ C₁ with hKdef
  have hKle := rowKappa_le_gen (by linarith : (1 : ℝ) ≤ N) (by positivity : (0 : ℝ) < r₀ / 128)
    hc₁ hC₁ hν1 hνd hνl (by positivity) (ℓ := ℓ)
  have hK0 : 0 ≤ K := by
    have := weightConst_pos
    simp only [hKdef, rowKappa, abs_of_pos (lt_of_lt_of_le one_pos hν1)]
    have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N)
    positivity
  have hca : c - a = t := by simp only [a]; ring
  have hKt : K * (c - a) ≤ 1 := by
    rw [hca]
    calc K * t ≤ kappaConst' (r₀ / 128) c₁ C₁ * (ν ^ 2 * ((ℓ : ℝ) / N) + ν * (1 + Real.log N) +
          ν ^ 2 / N) * t := mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hN0.le _)
      _ ≤ 1 := hκ
  have hcore := ref_core (hIto N) hStop (hDBM N) hF (a := a) (c := c) (E := E) ha0
    (by simp only [a]; linarith [Real.rpow_nonneg hN0.le (-(1 / 500 : ℝ))]) hr₀ hℓ1'
    (c₁ := c₁) (C₁ := C₁) (C := C) (b₀ := b₀R) (h := (N : ℝ) ^ (-(1 / 100 : ℝ)))
    (D₀ := C * Real.sqrt t) hc₁ hC₁ hC b₀ w Cw (ν := ν) (d := d) (Rc := r₀ / 128) (K := K)
    (thr := (N : ℝ) ^ (-D)) (by positivity) hd0 (by positivity) hρ hK0 le_rfl
    (Real.rpow_pos_of_pos hN0 _)
  refine hcore.trans ?_
  have hB₁ : flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a c,
      goodClauses F a ω E r₀ c₁ C₁ C b₀R ℓ ((N : ℝ) ^ (-(1 / 100 : ℝ))) (C * Real.sqrt t) σ} ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) := hN₁ N (le_of_max_le_left hN) F E hFC
  have hX : (c - a) * (Real.exp (ν * (Cw / N)) * (Real.exp (K * (c - a)) *
      (N * Real.exp (-(ν * min ((((w : ℝ) + 1) / (C * N) - (N : ℝ) ^ (-(1 / 100 : ℝ)) -
        C * Real.sqrt t) - d) (r₀ / 128)))))) ≤
      Real.exp 2 * (N * Real.exp (-(1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ)))) := by
    have h1 : c - a ≤ 1 := by rw [hca]; exact ht1
    have h2 : Real.exp (ν * (Cw / N)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hCw
    have h3 : Real.exp (K * (c - a)) ≤ Real.exp 1 := Real.exp_le_exp.mpr hKt
    have h4 : Real.exp (-(ν * min ((((w : ℝ) + 1) / (C * N) - (N : ℝ) ^ (-(1 / 100 : ℝ)) -
        C * Real.sqrt t) - d) (r₀ / 128))) ≤
        Real.exp (-(1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ))) :=
      Real.exp_le_exp.mpr (neg_le_neg hmin)
    have hca0 : 0 ≤ c - a := by rw [hca]; exact Real.rpow_nonneg hN0.le _
    calc _ ≤ 1 * (Real.exp 1 * (Real.exp 1 *
          (N * Real.exp (-(1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ)))))) := by
          gcongr
      _ = Real.exp 2 * (N * Real.exp (-(1 / (2 * C) * (N : ℝ) ^ (11 / 10000 : ℝ)))) := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
  have hfin' := ref_final hN0 hfin hX
  rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN0 _)]
  calc _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + _ := by gcongr
    _ ≤ _ := ennreal_final hN2 hfin'

end BlockBand.Palm.RelativeLocalization
