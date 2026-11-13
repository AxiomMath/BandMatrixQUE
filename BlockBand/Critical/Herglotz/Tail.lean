module

public import BlockBand.Critical.Herglotz.NearConv
public import BlockBand.Critical.Herglotz.SmoothCutoff

/-!
# Escaped mass vanishes

* `TendstoInDistribution.lintegral_le_liminf`: Fatou in law (portmanteau, open sets) for
  continuous nonnegative functionals.
* `massTest L M`: the `C_c` test `χ_L(y) ψ_M(ρ) Re tr ρ / (1 + y²)` on `ℝ × Matrix`;
  `tailMass_add_atomSum_le` (`tailMass ≤ poleMass - atomSum(massTest)`).
* `iSup_lintegral_massTest_canon`: canonical mean of the test increases to
  `r ∫ χ_L P_1` as `M → ∞` (`P_1 = poissonKernel 1`; the decorated sine intensity via `productTest_lintegral`).
* `HerglotzTailHypotheses.eventually_measure_tailMass_le`: for `s, η > 0`, eventually
  in `n`, eventually in `N`, `P_N*(tailMass(F_N, n) ≥ s) ≤ η`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexOrder

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-- **Fatou in law.** If `Y N ⇒ Z` (`N → ∞`) in a space with closed sets approximable from
outside, then for every continuous `f ≥ 0`, `E ofReal f(Z) ≤ liminf_N E ofReal f(Y N)`. -/
theorem TendstoInDistribution.lintegral_le_liminf {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E] {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : ∀ N, Ω N → E} {Z : Ω' → E} (h : TendstoInDistribution Y atTop Z P P') {f : E → ℝ}
    (hf : Continuous f) (hf0 : 0 ≤ f) :
    ∫⁻ ω, ENNReal.ofReal (f (Z ω)) ∂P' ≤
      atTop.liminf fun N => ∫⁻ ω, ENNReal.ofReal (f (Y N ω)) ∂P N := by
  have hmain := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := P'.map Z) (μs := fun N => (P N).map (Y N)) hf hf0
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto h.tendsto hG)
  have hm : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf.measurable
  rw [lintegral_map' hm.aemeasurable h.aemeasurable_limit] at hmain
  simp_rw [lintegral_map' hm.aemeasurable (h.forall_aemeasurable _)] at hmain
  exact hmain

/-- The escaped (tail) pole mass outside the window `χ_L`. -/
def tailMass (F : AtomicHerglotz r) (L : ℝ) : ℝ :=
  ∑ x ∈ F.residue.support, (1 - smoothCutoff L x) * ((Matrix.trace (F.residue x)).re / (1 + x ^ 2))

theorem tailMass_nonneg (F : AtomicHerglotz r) (L : ℝ) : 0 ≤ tailMass F L :=
  Finset.sum_nonneg fun x _ => mul_nonneg (by linarith [smoothCutoff_le_one L x])
    (div_nonneg (trace_re_nonneg (F.residue_posSemidef x)) (by positivity))

theorem continuous_trace_re : Continuous fun ρ : Matrix (Fin r) (Fin r) ℂ =>
    (Matrix.trace ρ).re := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Complex.re_sum]
  exact continuous_finsetSum _ fun i _ => Complex.continuous_re.comp (continuous_matrix_apply i i)

theorem matCutoff_mono {M M' : ℝ} (h : M ≤ M') (ρ : Matrix (Fin r) (Fin r) ℂ) :
    matCutoff M ρ ≤ matCutoff M' ρ := by
  unfold matCutoff
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

/-- `Re tr ρ / (1 + y²)`. -/
def massWeight (p : ℝ × Matrix (Fin r) (Fin r) ℂ) : ℝ := (Matrix.trace p.2).re / (1 + p.1 ^ 2)

theorem continuous_massWeight : Continuous (massWeight (r := r)) := by
  have h1 : Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => (Matrix.trace p.2).re :=
    continuous_trace_re.comp continuous_snd
  have h2 : Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => 1 + p.1 ^ 2 :=
    continuous_const.add ((continuous_pow 2).comp continuous_fst)
  exact h1.div h2 fun p => (by positivity : (0 : ℝ) < 1 + p.1 ^ 2).ne'

/-- The window mass test `χ_L(y) ψ_M(ρ) Re tr ρ / (1 + y²)`. -/
def massTest (L M : ℝ) : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ where
  toFun p := smoothCutoff L p.1 * matCutoff M p.2 * massWeight p
  continuous_toFun := (continuous_cutoffs L M).mul continuous_massWeight
  hasCompactSupport' := (hasCompactSupport_cutoffs L M).mul_right

theorem massTest_apply (L M : ℝ) (p : ℝ × Matrix (Fin r) (Fin r) ℂ) :
    massTest L M p =
      smoothCutoff L p.1 * matCutoff M p.2 * ((Matrix.trace p.2).re / (1 + p.1 ^ 2)) := rfl

theorem atomSum_massTest_nonneg (F : AtomicHerglotz r) (L M : ℝ) :
    0 ≤ F.atomSum (massTest L M) :=
  Finset.sum_nonneg fun x _ => mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _)
    (matCutoff_nonneg _ _)) (div_nonneg (trace_re_nonneg (F.residue_posSemidef x))
      (by positivity))

/-- `tailMass F L + atomSum (massTest L M) ≤ poleMass F`. -/
theorem tailMass_add_atomSum_le (F : AtomicHerglotz r) (L M : ℝ) :
    tailMass F L + F.atomSum (massTest L M) ≤ poleMass F := by
  unfold tailMass AtomicHerglotz.atomSum poleMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [massTest_apply]
  have ha := div_nonneg (trace_re_nonneg (F.residue_posSemidef x)) (by positivity :
    (0 : ℝ) < 1 + x ^ 2).le
  have hχ := smoothCutoff_nonneg L x
  have hψ := matCutoff_le_one M (F.residue x)
  have hψ0 := matCutoff_nonneg M (F.residue x)
  simp only
  nlinarith [mul_le_mul_of_nonneg_left hψ hχ]

/-- **Canonical window mass.** For the decorated sine process, the means
`E ∫⁻ massTest L M (x, π⁻¹gg^*) dΞ` increase to `ofReal (r ∫ χ_L P_1)` as `M → ∞` (`M : ℕ`).
Stated as: their supremum is `ofReal ((∫ χ_L P_1) r)`. -/
theorem iSup_lintegral_massTest_canon {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) (L : ℝ) :
    ⨆ M : ℕ, ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (massTest L M (p.1, canonicalResidue p.2))
      ∂(Ξ ω).measure ∂P =
      ENNReal.ofReal ((∫ x, smoothCutoff L x * poissonKernel 1 x) * r) := by
  have hu : Continuous fun x => smoothCutoff L x * poissonKernel 1 x :=
    (continuous_smoothCutoff L).mul (continuous_poissonKernel one_pos)
  obtain ⟨hmeas, hE, -⟩ := productTest_lintegral h hu
    (hasCompactSupport_smoothCutoff L).mul_right
    (fun x => mul_nonneg (smoothCutoff_nonneg _ _) (poissonKernel_nonneg one_pos x))
    continuous_euclidMark euclidMark_nonneg integrable_euclidMark_sq
  rw [integral_euclidMark] at hE
  rw [← hE]
  -- the test against the canonical residues
  have htr : ∀ g : Fin r → ℂ, (Matrix.trace (canonicalResidue g)).re = euclidMark g / Real.pi := by
    intro g
    rw [Matrix.trace, Complex.re_sum]
    unfold euclidMark
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, canonicalResidue_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_inv]
    norm_cast
    ring
  have hval : ∀ (M : ℝ) (p : ℝ × (Fin r → ℂ)), massTest L M (p.1, canonicalResidue p.2) =
      matCutoff M (canonicalResidue p.2) *
        (smoothCutoff L p.1 * poissonKernel 1 p.1 * euclidMark p.2) := by
    intro M p
    rw [massTest_apply, htr]
    simp only [poissonKernel]
    field_simp
    ring
  have hfm : ∀ M : ℕ, Measurable fun p : ℝ × (Fin r → ℂ) =>
      ENNReal.ofReal (massTest L M (p.1, canonicalResidue p.2)) := fun M =>
    ENNReal.measurable_ofReal.comp ((massTest L M).continuous.comp continuous_canonMap).measurable
  have hmono : ∀ p : ℝ × (Fin r → ℂ), Monotone fun M : ℕ =>
      ENNReal.ofReal (massTest L M (p.1, canonicalResidue p.2)) := by
    intro p M M' hMM'
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hval, hval]
    refine mul_le_mul_of_nonneg_right (matCutoff_mono (by exact_mod_cast hMM') _) ?_
    exact mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _) (poissonKernel_nonneg one_pos _))
      (euclidMark_nonneg _)
  have hsup : ∀ p : ℝ × (Fin r → ℂ), ⨆ M : ℕ,
      ENNReal.ofReal (massTest L M (p.1, canonicalResidue p.2)) =
        ENNReal.ofReal (smoothCutoff L p.1 * poissonKernel 1 p.1 * euclidMark p.2) := by
    intro p
    refine le_antisymm (iSup_le fun M => ENNReal.ofReal_le_ofReal ?_) ?_
    · rw [hval]
      exact mul_le_of_le_one_left (mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _)
        (poissonKernel_nonneg one_pos _)) (euclidMark_nonneg _)) (matCutoff_le_one _ _)
    · obtain ⟨M, hM⟩ := exists_nat_ge (matNorm (canonicalResidue p.2))
      refine le_iSup_of_le M (le_of_eq ?_)
      rw [hval, matCutoff_eq_one hM, one_mul]
  -- inner monotone convergence, then outer
  have hinner : ∀ ω, ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * poissonKernel 1 p.1 *
      euclidMark p.2) ∂(Ξ ω).measure = ⨆ M : ℕ, ∫⁻ p, ENNReal.ofReal
        (massTest L M (p.1, canonicalResidue p.2)) ∂(Ξ ω).measure := by
    intro ω
    rw [← lintegral_iSup hfm fun M M' hMM' p => hmono p hMM']
    exact lintegral_congr fun p => (hsup p).symm
  simp_rw [hinner]
  have hωm : ∀ M : ℕ, Measurable fun ω => ∫⁻ p, ENNReal.ofReal
      (massTest L M (p.1, canonicalResidue p.2)) ∂(Ξ ω).measure := by
    intro M
    have hf : Continuous fun p : ℝ × (Fin r → ℂ) => massTest L M (p.1, canonicalResidue p.2) :=
      (massTest L M).continuous.comp continuous_canonMap
    have hnn : ∀ p : ℝ × (Fin r → ℂ), 0 ≤ massTest L M (p.1, canonicalResidue p.2) := by
      intro p
      rw [massTest_apply]
      exact mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _) (matCutoff_nonneg _ _))
        (div_nonneg (trace_re_nonneg (canonicalResidue_posSemidef _)) (by positivity))
    refine (lintegral_lintegral_ofReal_of_decoratedSine h hf hnn
      (isCompact_closedBall (0 : ℝ) (L + 1)) ?_).1
    intro x g hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    rw [massTest_apply, smoothCutoff_eq_zero hx.le]
    simp
  rw [lintegral_iSup hωm fun M M' hMM' ω => lintegral_mono fun p => hmono p hMM']

section Hyp

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

/-- **The escaped pole mass vanishes.** Law: hypotheses of the Herglotz tail lemma for
`F N` on `(Ω N, P N)`, `Ξ` decorated sine. For `s, η > 0`: eventually in `n : ℕ`, eventually in
`N`, `P_N*(tailMass(F_N, n) ≥ s) ≤ η` (outer measure; window `χ_n = smoothCutoff n`). Order of
limits: `N → ∞` first, then `n → ∞`. -/
theorem HerglotzTailHypotheses.eventually_measure_tailMass_le
    (h : HerglotzTailHypotheses r P F P' Ξ) (hΞ : IsDecoratedSineProcess r P' Ξ) {s η : ℝ}
    (hs : 0 < s) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N in atTop,
      P N {ω | s ≤ tailMass (F N ω) n} ≤ ENNReal.ofReal η := by
  set ε₀ : ℝ := η * s / 4 with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  -- the window captures almost all of the canonical mass
  have hwin : ∀ᶠ n : ℕ in atTop, (r : ℝ) - ε₀ < (∫ x, smoothCutoff n x * poissonKernel 1 x) * r := by
    have := ((tendsto_integral_smoothCutoff_mul_poissonKernel one_pos).comp
      tendsto_natCast_atTop_atTop).mul_const (r : ℝ)
    rw [one_mul] at this
    exact this.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hwin] with n hn
  set I : ℝ := (∫ x, smoothCutoff n x * poissonKernel 1 x) * r with hI
  -- integrability of the window test, dominated by the pole mass
  have hintM : ∀ M : ℕ, ∀ᶠ N in atTop,
      Integrable (fun ω => (F N ω).atomSum (massTest n M)) (P N) := by
    intro M
    filter_upwards [h.eventually_integrable_poleMass] with N hN
    have T := h.poles 1 fun _ => massTest n M
    refine hN.1.mono' ((continuous_apply 0).measurable.comp_aemeasurable
      (T.forall_aemeasurable N)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (atomSum_massTest_nonneg _ _ _)]
    linarith [tailMass_add_atomSum_le (F N ω) n M, tailMass_nonneg (F N ω) n]
  -- the N-side mean of the window test is eventually at least `I - ε₀`
  have hlow : ∃ M : ℕ, ∀ᶠ N in atTop, I - ε₀ ≤ ∫ ω, (F N ω).atomSum (massTest n M) ∂P N := by
    by_cases hI0 : I - ε₀ ≤ 0
    · exact ⟨0, Eventually.of_forall fun N =>
        hI0.trans (integral_nonneg fun ω => atomSum_massTest_nonneg _ _ _)⟩
    push Not at hI0
    have hsup := iSup_lintegral_massTest_canon hΞ (n : ℝ)
    rw [← hI] at hsup
    have hlt : ENNReal.ofReal (I - ε₀) < ⨆ M : ℕ, ∫⁻ ω, ∫⁻ p, ENNReal.ofReal
        (massTest n M (p.1, canonicalResidue p.2)) ∂(Ξ ω).measure ∂P' := by
      rw [hsup, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
    obtain ⟨M, hM⟩ := lt_iSup_iff.1 hlt
    refine ⟨M, ?_⟩
    have T := h.poles 1 fun _ => massTest n M
    have hfat := TendstoInDistribution.lintegral_le_liminf T (f := fun y => max (y 0) 0)
      (continuous_max.comp ((continuous_apply 0).prodMk continuous_const))
      (fun y => le_max_right _ _)
    have hcan : ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (massTest n M (p.1, canonicalResidue p.2))
        ∂(Ξ ω).measure ∂P' = ∫⁻ ω, ENNReal.ofReal (max ((fun _ : Fin 1 =>
          ∫ p, massTest n M (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) 0) 0) ∂P' := by
      refine lintegral_congr fun ω => ?_
      have hi : Integrable (fun p => massTest n M p) (canonMeasure (Ξ ω)) :=
        (massTest n M).continuous.integrable_of_hasCompactSupport (massTest n M).hasCompactSupport
      have hi' : Integrable (fun p : ℝ × (Fin r → ℂ) => massTest n M (p.1, canonicalResidue p.2))
          (Ξ ω).measure :=
        (integrable_map_measure (massTest n M).continuous.aestronglyMeasurable
          continuous_canonMap.aemeasurable).1 hi
      have hnn : ∀ p : ℝ × (Fin r → ℂ), 0 ≤ massTest n M (p.1, canonicalResidue p.2) := by
        intro p
        rw [massTest_apply]
        exact mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _) (matCutoff_nonneg _ _))
          (div_nonneg (trace_re_nonneg (canonicalResidue_posSemidef _)) (by positivity))
      rw [← ofReal_integral_eq_lintegral_ofReal hi' (Eventually.of_forall hnn),
        max_eq_left (integral_nonneg hnn)]
    rw [hcan] at hM
    have hev := eventually_lt_of_lt_liminf (lt_of_lt_of_le hM hfat)
    filter_upwards [hev, hintM M] with N hN hiN
    simp only [max_eq_left (atomSum_massTest_nonneg _ _ _)] at hN
    rw [← ofReal_integral_eq_lintegral_ofReal hiN
      (Eventually.of_forall fun ω => atomSum_massTest_nonneg _ _ _)] at hN
    exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hN).1).le
  obtain ⟨M, hM⟩ := hlow
  have hup := h.tendsto_integral_poleMass.eventually (gt_mem_nhds (lt_add_of_pos_right (r : ℝ) hε₀0))
  filter_upwards [hM, hintM M, h.eventually_integrable_poleMass, hup] with N hN hiN hpN hupN
  set T' : Ω N → ℝ := fun ω => poleMass (F N ω) - (F N ω).atomSum (massTest n M) with hT'
  have hT'i : Integrable T' (P N) := hpN.1.sub hiN
  have hT'0 : 0 ≤ᵐ[P N] T' := Eventually.of_forall fun ω => by
    simp only [hT', Pi.zero_apply]
    linarith [tailMass_add_atomSum_le (F N ω) n M, tailMass_nonneg (F N ω) n]
  have hE : ∫ ω, T' ω ∂P N < η * s := by
    have hηs : 0 < η * s := by positivity
    have hε₀' : ε₀ * 4 = η * s := by rw [hε₀]; ring
    have hsub : ∫ ω, T' ω ∂P N = ∫ ω, poleMass (F N ω) ∂P N -
        ∫ ω, (F N ω).atomSum (massTest n M) ∂P N := integral_sub hpN.1 hiN
    rw [hsub]
    linarith
  have hsub : {ω | s ≤ tailMass (F N ω) n} ⊆ {ω | s ≤ T' ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, hT'] at hω ⊢
    linarith [tailMass_add_atomSum_le (F N ω) n M]
  refine (measure_mono hsub).trans ?_
  have hmk := mul_meas_ge_le_integral_of_nonneg hT'0 hT'i s
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P N) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : s * (P N).real {ω | s ≤ T' ω} < s * η := by linarith
  have h2 := lt_of_mul_lt_mul_left this hs.le
  exact h2.le

end Hyp

end BlockBand.Critical.Herglotz
