module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2KStopLim

/-!
# Proof of `CapIdentKStop`

Measure: the candidate's `Q` (premises `CapIdentPremise`). Inputs: `TransmissionLawContract`,
`ComplexClosedSummed`, `ComplexClosedLindeberg` (through `modulusS`),
`ComplexKStoppedMomentMax`.

* `integral_fGrid_le`: `∫ fGrid(obs) dQ ≤ (2 + 2C_J² + N·#cols·θ + 2C)/(p/2)` for a non-birth
  grid, `δ`-dense from the left, with the modulus at window `δ` below `θ`.
* `kComp`, `goodQ`, `aliveQ`, `termQ`: the dominating function
  `g = sup_q 1{q good, A_q} |𝒦(q) − 𝒦(0)|²` (births removed), `A_q` = trace below `L` at every
  rational time `≤ q`.
* `ofReal_le_gE`: `|𝒦(v) − 𝒦(0)|² ≤ g` for `v ≤ t ∧ σ_L` (left limits along good rationals).

These give `∫⁻ min(g_n, N) ≤ 2(2 + 2C_J² + 2C)/p + ε` for every `ε > 0` (each finite set of
rationals refined into a grid fine enough for `modulusS`; `min_gn_le`), and then
`kStop_dominated` and `capIdentKStop_holds : CapIdentKStop`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

variable {K np : ℕ} {b E s h : ℝ} {τ m : Fin np → ℝ}
  {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
  {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
  {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}

theorem gTime_coe {α : Type} {r : α → ℚ} (hrn : ∀ a, 0 ≤ (r a : ℝ)) (l : GLab K np α) :
    (gTime r l : ℝ) = r (Sum.elim Prod.fst id l) := by
  rcases l with p | a
  · exact Real.coe_toNNReal _ (hrn p.1)
  · exact Real.coe_toNNReal _ (hrn a)

/-- **The limit bound of the grid functional.** -/
theorem integral_fGrid_le {α : Type} [Fintype α] [Nonempty α] [IsProbabilityMeasure Q]
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc)
    (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hb : b < 1) (hm : ∀ i, 0 ≤ m i) (hs0 : 0 ≤ s)
    (hτ : ∀ j, s < τ j) {L R T δ θ N C CJ p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hp : 0 < p) (hR : L + ∑ i, dStar b * m i + 2 ≤ R) {r : α → ℚ} {a₀ : α} (hr0 : r a₀ = 0)
    (hrn : ∀ a, 0 ≤ (r a : ℝ)) (hrT : ∀ a, s + (r a : ℝ) ≤ T) (hnb : ∀ a j, s + (r a : ℝ) ≠ τ j)
    (hδ : 0 ≤ δ) (hdense : ∀ x : ℝ, 0 ≤ x → (∃ a, x < r a) → ∃ c, (r c : ℝ) ≤ x ∧ x - δ ≤ r c)
    {κ : α → ℂ} (hκ : ∀ a, ‖κ a‖ ≤ CJ) (ij : Fin np × Fin np)
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0 ∧
      p / 2 ≤ (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal)
    (hmod : ∀ᶠ n in atTop, ∀ col, closedLaw b (φ n) np (modEvent b E s h τ m T δ
      (1 / (Fintype.card (SrcCol K (Fin np)) : ℝ)) (φ n) (Vs (φ n)) col) ≤ ENNReal.ofReal θ)
    (hZ : ∀ᶠ n in atTop, ∫⁻ y, kMaxZ b E s h τ m R T (φ n) (Vs (φ n)) ij y
      ∂closedLaw b (φ n) np ≤ ENNReal.ofReal C) :
    Integrable (fun ω => fGrid L r N κ a₀
      (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω)) Q ∧
    ∫ ω, fGrid L r N κ a₀ (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω) ∂Q ≤
      (2 + 2 * CJ ^ 2 + N * (Fintype.card (SrcCol K (Fin np)) : ℝ) * θ + 2 * C) / (p / 2) := by
  have hu : ∀ (l : GLab K np α) j, s + (gTime r l : ℝ) ≠ τ j := fun l j => by
    rw [gTime_coe hrn]; exact hnb _ j
  exact integral_le_of_fddAll hF hobs (gIdx ij) (gTime r) hu (fGrid L r N κ a₀)
    (psiGrid L r N hN κ a₀) (fun k x => psiFun_nonneg hN k x) (fun k x => psiFun_le_fGrid hN k x)
    (fGrid_le hN) (fun x => tendsto_psiFun x)
    (fun k => eventually_condObs_psiGrid_le hb hm hs0 hτ hN hC hθ hp hR hr0 hrn hrT hδ hdense hκ ij
      hcap hmod hZ k)

/-!
## The dominating function
-/

/-- The births-removed `𝒦_ij(v) − 𝒦_ij(0)`. -/
def kComp (E s : ℝ) (τ m : Fin np → ℝ) (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ)
    (ij : Fin np × Fin np) (v : ℝ≥0) (ω : Ω') : ℂ :=
  kCompensated Kc (fun t _ => kJ E s τ m t) ij.1 ij.2 v ω

/-- Good rationals: non-birth times in `[0, t]`. -/
def goodQ (s t : ℝ) (τ : Fin np → ℝ) (q : ℚ) : Prop :=
  0 ≤ q ∧ (q : ℝ) ≤ t ∧ ∀ j, s + (q : ℝ) ≠ τ j

/-- The trace is below `L` at every rational time `≤ q`. -/
def aliveQ (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))) (L : ℝ) (q : ℚ) : Set Ω' :=
  {ω | ∀ r' : ℚ, 0 ≤ r' → r' ≤ q → ((G ((r' : ℝ)).toNNReal ω).1.trace).re < L}

open scoped Classical in
/-- The terms of the dominating function. -/
def termQ (E s t L : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) (ij : Fin np × Fin np) (q : ℚ) (ω : Ω') :
    ℝ≥0∞ :=
  if goodQ s t τ q then (aliveQ G L q).indicator
    (fun ω => ENNReal.ofReal (‖kComp E s τ m Kc ij ((q : ℝ)).toNNReal ω‖ ^ 2)) ω else 0

/-- An enumeration of `ℚ`. -/
def enumQ : ℕ → ℚ := Classical.choose (exists_surjective_nat ℚ)

theorem enumQ_surjective : Function.Surjective enumQ :=
  Classical.choose_spec (exists_surjective_nat ℚ)

/-- The dominating function. -/
def gE (E s t L : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) (ij : Fin np × Fin np) (ω : Ω') : ℝ≥0∞ :=
  ⨆ k : ℕ, termQ E s t L τ m G Kc ij (enumQ k) ω

/-- Its finite approximations. -/
def gn (E s t L : ℝ) (τ m : Fin np → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ) (ij : Fin np × Fin np) (n : ℕ) (ω : Ω') :
    ℝ≥0∞ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => termQ E s t L τ m G Kc ij (enumQ k) ω

theorem measurable_kComp (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (E s : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) (v : ℝ≥0) :
    Measurable (kComp E s τ m Kc ij v) := by
  have h1 : Measurable fun ω => Kc v ω ij.1 ij.2 := hobs (Sum.inr (Sum.inr ij)) v
  have h0 : Measurable fun ω => Kc 0 ω ij.1 ij.2 := hobs (Sum.inr (Sum.inr ij)) 0
  have e : kComp E s τ m Kc ij v = fun ω =>
      (Kc v ω ij.1 ij.2 - kJ E s τ m v ij.1 ij.2) - (Kc 0 ω ij.1 ij.2 - kJ E s τ m 0 ij.1 ij.2) :=
    by funext ω; simp [kComp, kCompensated, Matrix.sub_apply]
  rw [e]
  exact (h1.sub_const _).sub (h0.sub_const _)

theorem measurableSet_aliveQ (hGm : ∀ u, StronglyMeasurable (G u)) (L : ℝ) (q : ℚ) :
    MeasurableSet (aliveQ G L q) := by
  have e : aliveQ G L q = ⋂ r' : ℚ, {ω | 0 ≤ r' → r' ≤ q →
      ((G ((r' : ℝ)).toNNReal ω).1.trace).re < L} := by
    ext ω; simp [aliveQ]
  rw [e]
  refine MeasurableSet.iInter fun r' => ?_
  by_cases h1 : 0 ≤ r' ∧ r' ≤ q
  · have hf : Measurable fun ω => ((G ((r' : ℝ)).toNNReal ω).1.trace).re :=
      ((Complex.continuous_re.comp continuous_fst.matrix_trace).comp_stronglyMeasurable
        (hGm _)).measurable
    have e2 : {ω | 0 ≤ r' → r' ≤ q → ((G ((r' : ℝ)).toNNReal ω).1.trace).re < L} =
        {ω | ((G ((r' : ℝ)).toNNReal ω).1.trace).re < L} := by
      ext ω; simp [h1.1, h1.2]
    rw [e2]
    exact measurableSet_lt hf measurable_const
  · have e2 : {ω | 0 ≤ r' → r' ≤ q → ((G ((r' : ℝ)).toNNReal ω).1.trace).re < L} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro ha hb'
      exact absurd ⟨ha, hb'⟩ h1
    rw [e2]
    exact MeasurableSet.univ

theorem measurable_termQ (hobs : ∀ i u, Measurable (complexObs tseq G Kc i u))
    (hGm : ∀ u, StronglyMeasurable (G u)) (E s t L : ℝ) (τ m : Fin np → ℝ)
    (ij : Fin np × Fin np) (q : ℚ) : Measurable (termQ E s t L τ m G Kc ij q) := by
  unfold termQ
  split_ifs
  · exact (ENNReal.measurable_ofReal.comp ((measurable_kComp hobs E s τ m ij _).norm.pow_const
      2)).indicator (measurableSet_aliveQ hGm L q)
  · exact measurable_const

omit [MeasurableSpace Ω'] in
theorem kComp_zero (E s : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) (ω : Ω') :
    kComp E s τ m Kc ij 0 ω = 0 := by
  simp [kComp, kCompensated]

omit [MeasurableSpace Ω'] in
/-- **The domination before the trace stop.** -/
theorem ofReal_le_gE (E s : ℝ) (τ m : Fin np → ℝ) (L : ℝ) (t : ℝ≥0)
    (ij : Fin np × Fin np) (ω : Ω') (hkc : Continuous fun u => Kc u ω - kJ E s τ m u)
    (v : ℝ≥0) (hvt : v ≤ t) (hvσ : (v : WithTop ℝ≥0) ≤ gramTraceStop G L ω) :
    ENNReal.ofReal (‖kComp E s τ m Kc ij v ω‖ ^ 2) ≤ gE E s t L τ m G Kc ij ω := by
  rcases eq_zero_or_pos v with hv0 | hv0
  · rw [hv0, kComp_zero, norm_zero]; simp
  have hv0' : (0 : ℝ) < v := hv0
  have hq : ∀ k : ℕ, ∃ q : ℚ, max 0 ((v : ℝ) - 1 / ((k : ℝ) + 1)) < q ∧ (q : ℝ) < v ∧
      ∀ j, s + (q : ℝ) ≠ τ j := fun k =>
    exists_nonbirth_btwn s τ (max_lt hv0' (sub_lt_self _ (by positivity)))
  choose q hq1 hq2 hq3 using hq
  have hqpos : ∀ k, (0 : ℝ) < q k := fun k => lt_of_le_of_lt (le_max_left _ _) (hq1 k)
  have hlimR : Tendsto (fun k => (q k : ℝ)) atTop (𝓝 (v : ℝ)) := by
    have hlo : Tendsto (fun k : ℕ => (v : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 (v : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (v : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun k => (le_max_right _ _).trans (hq1 k).le) fun k => (hq2 k).le
  have hlim : Tendsto (fun k => ((q k : ℝ)).toNNReal) atTop (𝓝 v) := by
    have := (continuous_real_toNNReal.tendsto _).comp hlimR
    rwa [Real.toNNReal_coe] at this
  have hcont : Continuous fun u => ENNReal.ofReal (‖kComp E s τ m Kc ij u ω‖ ^ 2) := by
    have : Continuous fun u => kComp E s τ m Kc ij u ω := by
      simp only [kComp, kCompensated]
      exact (hkc.matrix_elem ij.1 ij.2).sub continuous_const
    exact ENNReal.continuous_ofReal.comp (this.norm.pow 2)
  refine le_of_tendsto' ((hcont.tendsto v).comp hlim) fun k => ?_
  have hgood : goodQ s t τ (q k) := ⟨by exact_mod_cast (hqpos k).le,
    (hq2 k).le.trans (by exact_mod_cast hvt), hq3 k⟩
  have halive : ω ∈ aliveQ G L (q k) := by
    intro r' hr0 hrq
    refine ModelExist.re_trace_lt_of_lt_pathStop (G := fun u => G u ω) ?_
    refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hvσ
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (by exact_mod_cast hr0)]
    exact lt_of_le_of_lt (by exact_mod_cast hrq) (hq2 k)
  obtain ⟨k', hk'⟩ := enumQ_surjective (q k)
  refine le_iSup_of_le k' ?_
  rw [hk']
  simp only [termQ, hgood, ↓reduceIte, Set.indicator_of_mem halive, Function.comp_apply]
  exact le_rfl

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
