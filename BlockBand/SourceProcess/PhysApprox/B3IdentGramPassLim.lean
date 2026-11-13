module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassAug

/-!
# The fixed-time passage of a generator process

Abstract in the measures: probability measures `μ n` on `Ω n` and `Q` on `Ω'`. Off-birth times
`B = birthTimes s τ`.

* `eventually_gramJ_eq_nhds`: the limit jumps `gramJ` are locally constant off `B`.
* **`tendsto_genProc_test`**: if observables `X n` read Gram processes `Gn n`, `Y` reads `G`,
  the fdd converge off `B` (`AddFun.FddConvOff`), all paths are a.s. feasible, `G − gramJ` is
  continuous for every `ω` and everything is jointly measurable, then for every off-birth `t`,
  every cylinder test `φ` at off-birth times and `sel ∈ {re, im}`,
  `E_{μ n}[φ · sel(genProc(Gn n)_t)] → E_Q[φ · sel(genProc(G)_t)]`. Proof: `fddConvOff_augProc`
  twice (first `A^χ`, then `∫ Λ`, both clamped: `Pass.a1`, `Pass.a2`), on the observables with
  the time-`0` Gram observables held fixed (`fddConvOff_freeze`); the test is a bounded
  continuous function of the augmented vector equal to `φ · sel(genProc_t)` along every feasible
  path (`zOf_X2_eq`, `X2_A_eq`, the bounds `exists_lamA_bound`, `exists_lam_bound`,
  `exists_uniform_bound`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-- **Off the birth times the limit jumps are locally constant.** -/
theorem eventually_gramJ_eq_nhds {b s : ℝ} {τ m : Fin np → ℝ} {r : ℝ≥0}
    (hr : r ∉ birthTimes s τ) :
    ∀ᶠ v in 𝓝 r, gramJ (K := K) b s τ m v = gramJ b s τ m r := by
  have hiff : ∀ᶠ v : ℝ≥0 in 𝓝 r, ∀ j, (τ j - s ≤ (v : ℝ) ↔ τ j - s ≤ (r : ℝ)) := by
    rw [eventually_all]
    intro j
    have hne : τ j - s ≠ (r : ℝ) := fun h => hr ⟨j, by linarith⟩
    rcases lt_or_gt_of_ne hne with hj | hj
    · have h : ∀ᶠ v : ℝ≥0 in 𝓝 r, τ j - s < (v : ℝ) :=
        (NNReal.continuous_coe.tendsto r).eventually (lt_mem_nhds hj)
      filter_upwards [h] with v hv
      exact ⟨fun _ => hj.le, fun _ => hv.le⟩
    · have h : ∀ᶠ v : ℝ≥0 in 𝓝 r, (v : ℝ) < τ j - s :=
        (NNReal.continuous_coe.tendsto r).eventually (gt_mem_nhds hj)
      filter_upwards [h] with v hv
      exact ⟨fun h' => absurd h' (not_le.2 hv), fun h' => absurd h' (not_le.2 hj)⟩
  exact hiff.mono fun v hv => by simp only [gramJ, birthJump, hv]

/-- The state read off the second-layer inputs, with the jump at `r` as a variable. -/
def zOfJ (b s : ℝ) (τ m : Fin np → ℝ) (J : GSt K np)
    (x : GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) : ZSt K np :=
  (gramOfEntries (fun e => x (Sum.inl e)) - J,
    fun e => gramEntry e (gramOfEntries (fun e => x (Sum.inl e)) - J) -
      gramEntry e (gramOfEntries (fun e => x (Sum.inr (Sum.inl e))) - gramJ b s τ m 0) -
        x (Sum.inr (Sum.inr e)),
    gramOfEntries (fun e => x (Sum.inr (Sum.inl e))) - gramJ b s τ m 0)

theorem continuous_zOfJ (b s : ℝ) (τ m : Fin np → ℝ) :
    Continuous fun p : GSt K np × (GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) =>
      zOfJ b s τ m p.1 p.2 := by
  have hG : Continuous fun p : GSt K np × (GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) =>
      gramOfEntries (fun e => p.2 (Sum.inl e)) :=
    continuous_gramOfEntries.comp (continuous_pi fun e => (continuous_apply _).comp continuous_snd)
  have h0 : Continuous fun p : GSt K np × (GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) =>
      gramOfEntries (fun e => p.2 (Sum.inr (Sum.inl e))) :=
    continuous_gramOfEntries.comp (continuous_pi fun e => (continuous_apply _).comp continuous_snd)
  refine (hG.sub continuous_fst).prodMk ((continuous_pi fun e => ?_).prodMk
    (h0.sub continuous_const))
  exact (((ClosedLimit.continuous_gramEntry e).comp (hG.sub continuous_fst)).sub
    ((ClosedLimit.continuous_gramEntry e).comp (h0.sub continuous_const))).sub
    ((continuous_apply _).comp continuous_snd)

theorem norm_genA_le {Ω : Type*} {b E s : ℝ} {τ m : Fin np → ℝ} {χ : ℝ → ℝ}
    {G : ℝ≥0 → Ω → GSt K np} {ω : Ω} (hfe : ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    {LA : ℝ} (hLA0 : 0 ≤ LA)
    (hLA : ∀ (e : GIdx K np) (t : ℝ≥0) (H : GSt K np), GramFeasible (srcSignature K (Fin np)) H →
      ‖lamA χ b E e (gramJ b s τ m t, H - gramJ b s τ m t)‖ ≤ LA)
    (e : GIdx K np) {r t : ℝ≥0} (hrt : r ≤ t) : ‖genA χ b E s τ m G e r ω‖ ≤ t * LA := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) r)
    (f := fun w => lamA χ b E e (gramJ b s τ m w.toNNReal, gY b s τ m G w.toNNReal ω))
    (C := LA) measure_Ioc_lt_top fun w _ => by
      simpa only [gY] using hLA e w.toNNReal (G w.toNNReal ω) (hfe _)
  rw [Real.volume_real_Ioc, sub_zero, max_eq_left (NNReal.coe_nonneg r)] at h
  have h2 : LA * (r : ℝ) ≤ t * LA := by
    have : (r : ℝ) ≤ t := NNReal.coe_le_coe.2 hrt
    nlinarith
  exact (show ‖genA χ b E s τ m G e r ω‖ ≤ LA * r from h).trans h2

/-- **The fixed-time passage of a generator process.** -/
theorem tendsto_genProc_test {b E s : ℝ} {τ m : Fin np → ℝ}
    (h0 : (0 : ℝ≥0) ∉ birthTimes s τ)
    {Ω : ℕ → Type} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {X : (n : ℕ) → LIdx K np → ℝ≥0 → Ω n → ℂ} {Gn : (n : ℕ) → ℝ≥0 → Ω n → GSt K np}
    (hXG : ∀ n e u ω, X n (Sum.inl e) u ω = gramEntry e (Gn n u ω))
    (hXm : ∀ n i, Measurable (Function.uncurry (X n i)))
    (hfeN : ∀ n, ∀ᵐ ω ∂μ n, ∀ u, GramFeasible (srcSignature K (Fin np)) (Gn n u ω))
    {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {Y : LIdx K np → ℝ≥0 → Ω' → ℂ} {G : ℝ≥0 → Ω' → GSt K np}
    (hYG : ∀ e u ω, Y (Sum.inl e) u ω = gramEntry e (G u ω))
    (hYm : ∀ i, Measurable (Function.uncurry (Y i)))
    (hfe : ∀ᵐ ω ∂Q, ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
    (hc : ∀ ω, Continuous fun u => G u ω - gramJ b s τ m u)
    (hF : AddFun.FddConvOff (birthTimes s τ) μ X Q Y)
    {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ : ℝ}
    (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} (hFc : Continuous F) (hΛc : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    (hΛv : ∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ)
    {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0) (hub : ∀ l, u l ∉ birthTimes s τ)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) {t : ℝ≥0} (ht : t ∉ birthTimes s τ)
    {sel : ℂ → ℝ} (hsel : Continuous sel) (hselb : ∀ w, |sel w| ≤ ‖w‖) :
    Tendsto (fun n => ∫ ω, φ (fun l => X n (i l) (u l) ω) *
        sel (genProc χ b E s τ m (Gn n) F Λ t ω) ∂μ n) atTop
      (𝓝 (∫ ω, φ (fun l => Y (i l) (u l) ω) * sel (genProc χ b E s τ m G F Λ t ω) ∂Q)) := by
  have hB := birthTimes_finite s τ
  obtain ⟨LA, hLA0, hLA⟩ := exists_lamA_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχ hR
  obtain ⟨LL, hLL0, hLL⟩ := exists_lam_bound (b := b) (s := s) (τ := τ) (m := m) hΛc hΛv
    (t * LA)
  obtain ⟨LM, hLM0, hLM⟩ := exists_uniform_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχ hR hFc hΛc hFv hΛv t
  
  -- layer 0: the time-`0` Gram observables, held fixed
  have hF1 := fddConvOff_freeze (I := LIdx K np) (J := GIdx K np) h0 (fun e => Sum.inl e) hF
  have hX1 : ∀ n q, Measurable (Function.uncurry (freeze (fun e => Sum.inl e) (X n) q)) :=
    fun n => measurable_uncurry_freeze _ (hXm n)
  have hY1 : ∀ q, Measurable (Function.uncurry (freeze (I := LIdx K np) (J := GIdx K np)
      (fun e => Sum.inl e) Y q)) := measurable_uncurry_freeze _ hYm
  -- layer 1: `A^χ`
  have ham1 : ∀ e : GIdx K np,
      Measurable (Function.uncurry (a1 (K := K) (np := np) χ b E s τ m LA e)) := fun e => by
    have hcont : Continuous fun p : GSt K np × (GIdx K np → ℂ) =>
        clampC LA (lamA χ b E e (p.1, gramOfEntries p.2 - p.1)) :=
      (continuous_clampC LA).comp ((continuous_lamA (b := b) (E := E) hχ e).comp
        (continuous_fst.prodMk ((continuous_gramOfEntries.comp continuous_snd).sub
          continuous_fst)))
    have h := (hcont.comp_stronglyMeasurable (((sm_gramJ (K := K) b s τ m).comp_measurable
      measurable_fst).prodMk (measurable_snd (α := ℝ≥0)
        (β := GIdx K np → ℂ)).stronglyMeasurable)).measurable
    exact h
  have hab1 : ∀ e : GIdx K np, ∃ L : ℝ, ∀ r x, ‖a1 (K := K) (np := np) χ b E s τ m LA e r x‖ ≤ L :=
    fun e => ⟨2 * LA, fun r x => norm_clampC_le hLA0 _⟩
  have hac1 : ∀ (e : GIdx K np) (r : ℝ≥0), r ∉ birthTimes s τ →
      Continuous (a1 (K := K) (np := np) χ b E s τ m LA e r) :=
    fun e r _ => (continuous_clampC LA).comp ((continuous_lamA (b := b) (E := E) hχ e).comp
      (continuous_const.prodMk (continuous_gramOfEntries.sub continuous_const)))
  have hYc1 : ∀ (e : GIdx K np) (r : ℝ≥0), r ∉ birthTimes s τ → ∀ᵐ ω ∂Q, ContinuousAt (fun v =>
      a1 (K := K) (np := np) χ b E s τ m LA e v
        (fun c => freeze (fun e => Sum.inl e) Y (j1 c) v ω)) r :=
    fun e r hr => ae_of_all _ fun ω => by
      have hg : Continuous fun v => clampC LA (lamA χ b E e (gramJ b s τ m r,
          G v ω - gramJ b s τ m v)) :=
        (continuous_clampC LA).comp ((continuous_lamA (b := b) (E := E) hχ e).comp
          (continuous_const.prodMk (hc ω)))
      refine hg.continuousAt.congr ?_
      filter_upwards [eventually_gramJ_eq_nhds (K := K) (b := b) (m := m) hr] with v hv
      simp only [a1, j1, freeze, gramOfEntries_read hYG, hv]
  have hF2 := AddFun.fddConvOff_augProc hB (Eventually.of_forall hμ) hX1 hY1 ham1 hab1 hac1
    hYc1 hF1
  -- layer 2: `∫ Λ`
  have hX2 : ∀ n q, Measurable (Function.uncurry (X2 χ b E s τ m LA (X n) q)) :=
    fun n => AddFun.measurable_uncurry_augProc ham1 hab1 (hX1 n)
  have hY2 : ∀ q, Measurable (Function.uncurry (X2 χ b E s τ m LA Y q)) :=
    AddFun.measurable_uncurry_augProc ham1 hab1 hY1
  have ham2 : ∀ k, Measurable (Function.uncurry (a2 Λ b s τ m LL k)) := fun k => by
    have hcont : Continuous fun p : GSt K np × (GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) =>
        clampC LL (Λ (p.1, zOfJ b s τ m p.1 p.2)) :=
      (continuous_clampC LL).comp (hΛc.comp (continuous_fst.prodMk (continuous_zOfJ b s τ m)))
    have h := (hcont.comp_stronglyMeasurable (((sm_gramJ (K := K) b s τ m).comp_measurable
      measurable_fst).prodMk (measurable_snd (α := ℝ≥0)
        (β := GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ)).stronglyMeasurable)).measurable
    exact h
  have hab2 : ∀ k, ∃ L : ℝ, ∀ r x, ‖a2 Λ b s τ m LL k r x‖ ≤ L :=
    fun k => ⟨2 * LL, fun r x => norm_clampC_le hLL0 _⟩
  have hac2 : ∀ k r, r ∉ birthTimes s τ → Continuous (a2 Λ b s τ m LL k r) :=
    fun k r _ => (continuous_clampC LL).comp (hΛc.comp (continuous_const.prodMk
      (continuous_zOf b s τ m r)))
  have hAc : ∀ (e : GIdx K np) (ω : Ω'), Continuous fun v => X2 χ b E s τ m LA Y (Sum.inr e) v ω :=
    fun e ω => AddFun.continuous_addFun (ham1 e) hY1 (fun r x => norm_clampC_le hLA0 _) ω
  have hYc2 : ∀ k r, r ∉ birthTimes s τ → ∀ᵐ ω ∂Q, ContinuousAt (fun v =>
      a2 Λ b s τ m LL k v (fun c => X2 χ b E s τ m LA Y (j2 c) v ω)) r :=
    fun k r hr => ae_of_all _ fun ω => by
      have hg : Continuous fun v => clampC LL (Λ (gramJ b s τ m r,
          (G v ω - gramJ b s τ m v, fun e => gramEntry e (G v ω - gramJ b s τ m v) -
            gramEntry e (G 0 ω - gramJ b s τ m 0) - X2 χ b E s τ m LA Y (Sum.inr e) v ω,
            G 0 ω - gramJ b s τ m 0))) := by
        refine (continuous_clampC LL).comp (hΛc.comp (continuous_const.prodMk
          ((hc ω).prodMk ((continuous_pi fun e => ?_).prodMk continuous_const))))
        exact (((ClosedLimit.continuous_gramEntry e).comp (hc ω)).sub continuous_const).sub
          (hAc e ω)
      refine hg.continuousAt.congr ?_
      filter_upwards [eventually_gramJ_eq_nhds (K := K) (b := b) (m := m) hr] with v hv
      simp only [a2, zOf, j2, X2, AddFun.augProc, freeze, gramOfEntries_read hYG, hv]
  have hF3 := AddFun.fddConvOff_augProc hB (Eventually.of_forall hμ) hX2 hY2 ham2 hab2 hac2
    hYc2 hF2
  -- the test
  let ι := Fin r ⊕ ((GIdx K np ⊕ GIdx K np ⊕ GIdx K np) ⊕ Unit)
  let idx : ι → ((LIdx K np ⊕ GIdx K np) ⊕ GIdx K np) ⊕ Unit := fun q => match q with
    | Sum.inl l => Sum.inl (Sum.inl (Sum.inl (i l)))
    | Sum.inr (Sum.inl k) => Sum.inl (j2 k)
    | Sum.inr (Sum.inr _) => Sum.inr ()
  let tm : ι → ℝ≥0 := fun q => match q with
    | Sum.inl l => u l
    | Sum.inr _ => t
  have htm : ∀ q, tm q ∉ birthTimes s τ := fun q => by
    rcases q with l | _
    · exact hub l
    · exact ht
  let ψf : (ι → ℂ) → ℝ := fun v => φ (fun l => v (Sum.inl l)) *
    sel (clampC LM (F (zOf b s τ m t (fun k => v (Sum.inr (Sum.inl k)))) -
      v (Sum.inr (Sum.inr ()))))
  have hψc : Continuous ψf := by
    refine (φ.continuous.comp (continuous_pi fun l => continuous_apply _)).mul
      (hsel.comp ((continuous_clampC LM).comp ((hFc.comp ((continuous_zOf b s τ m t).comp
        (continuous_pi fun k => continuous_apply _))).sub (continuous_apply _))))
  have hψb : ∀ v, ‖ψf v‖ ≤ ‖φ‖ * (2 * LM) := fun v => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (φ.norm_coe_le_norm _) ((hselb _).trans (norm_clampC_le hLM0 _))
      (abs_nonneg _) (norm_nonneg _)
  let ψ : BoundedContinuousFunction (ι → ℂ) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup ψf hψc _ hψb
  have hlim := hF3 ι idx tm htm ψ
  -- identification along feasible paths
  have key : ∀ {Ω₀ : Type} (Z : LIdx K np → ℝ≥0 → Ω₀ → ℂ) (H : ℝ≥0 → Ω₀ → GSt K np),
      (∀ e u ω, Z (Sum.inl e) u ω = gramEntry e (H u ω)) → ∀ ω₀ : Ω₀,
      (∀ u, GramFeasible (srcSignature K (Fin np)) (H u ω₀)) →
      ψ (fun q => X3 χ b E s τ m LA Λ LL Z (idx q) (tm q) ω₀) =
        φ (fun l => Z (i l) (u l) ω₀) * sel (genProc χ b E s τ m H F Λ t ω₀) := by
    intro Ω₀ Z H hZH ω₀ hf
    have hzt := zOf_X2_eq (χ := χ) (E := E) (LA := LA) hZH hf hLA t
    have hint : X3 χ b E s τ m LA Λ LL Z (Sum.inr ()) t ω₀ =
        ∫ v in Ioc (0 : ℝ) t, Λ (gramJ b s τ m v.toNNReal, stZ χ b E s τ m H v.toNNReal ω₀) := by
      simp only [X3, AddFun.augProc, AddFun.addFun]
      refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
      simp only [a2]
      rw [zOf_X2_eq (χ := χ) (E := E) (LA := LA) hZH hf hLA]
      refine clampC_eq (hLL _ _ _ _ (hf _) (hf 0) fun e => ?_)
      exact norm_genA_le hf hLA0 hLA e (Real.toNNReal_le_iff_le_coe.2 hv.2)
    show φ (fun l => Z (i l) (u l) ω₀) * sel (clampC LM (F (zOf b s τ m t
      (fun k => X3 χ b E s τ m LA Λ LL Z (Sum.inl (j2 k)) t ω₀)) -
        X3 χ b E s τ m LA Λ LL Z (Sum.inr ()) t ω₀)) = _
    have e3 : (fun k => X3 χ b E s τ m LA Λ LL Z (Sum.inl (j2 k)) t ω₀) =
        fun k => X2 χ b E s τ m LA Z (j2 k) t ω₀ := rfl
    rw [e3, hzt, hint]
    exact congrArg (fun w => φ (fun l => Z (i l) (u l) ω₀) * sel w)
      (clampC_eq (hLM Ω₀ H ω₀ hf t le_rfl))
  have e : (∫ ω, ψ (fun q => X3 χ b E s τ m LA Λ LL Y (idx q) (tm q) ω) ∂Q) =
      ∫ ω, φ (fun l => Y (i l) (u l) ω) * sel (genProc χ b E s τ m G F Λ t ω) ∂Q :=
    integral_congr_ae (hfe.mono fun ω hω => key Y G hYG ω hω)
  rw [← e]
  refine hlim.congr' (Eventually.of_forall fun n => ?_)
  exact integral_congr_ae ((hfeN n).mono fun ω hω => key (X n) (Gn n) (hXG n) ω hω)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
