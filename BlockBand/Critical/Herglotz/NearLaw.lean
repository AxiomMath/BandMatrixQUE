module

public import BlockBand.Critical.Herglotz.NearConv
public import BlockBand.Critical.Herglotz.Together

/-!
# Convergence in law of the near part

Main result `HerglotzTailHypotheses.tendstoInDistribution_nearPart`: for a fixed smooth cutoff
`χ_L` (`L ≥ 0`), real points `x : Fin k → ℝ` and a compact `K ⊆ {Im z > 0}`, the joint values
`((near_{N,L}(x_a))_a, near_{N,L}|_K)` of `near_{N,L}(z) = Σ_x χ_L(x) (x - z)⁻¹ μ_N({x})`
converge in law, in `(Fin k → Matrix) × C(K, Matrix)`, to those of the canonical smooth cutoff
`smoothCauchy r Ξ L` (`nearPart_canonMeasure`).

Proof: convergence together (`tendstoInDistribution_of_forall_approx`) with the approximants
`approxJoint` at scale `u_n = 1/(n+2)` (regularization `δ = u_n`, residue cutoff `M = 1/u_n`,
interpolation scale `u_n`). The approximants are continuous images of finitely many truncated
coordinates (hypothesis 1, `tendstoInDistribution_coordMat`). The deterministic estimate
`nearPart_approx` reduces the errors to bad events, bounded by `O(u_n)`: at finite `N` by the bump bound
(`eventually_measure_bumpTest_le`) and residue tightness (`eventually_measure_poleMass_ge_le`),
canonically by the decorated sine intensity (`measure_canon_bad_real_le`,
`measure_canon_bad_mark_le`, `lintegral_window_mass`). Measurability of the finite-`N` near part
follows from pointwise convergence of the approximants.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexOrder

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire

variable {r : ℕ}

/-!
## The approximant as a continuous image of coordinates
-/

/-- Joint values built from a family of matrices indexed by real points and nodes. -/
def jointOfFamily {k : ℕ} {K : Set ℂ} {h : ℝ} (I : CompactInterp K h)
    (A : Fin k ⊕ I.pts → Matrix (Fin r) (Fin r) ℂ) : JointValues r k K :=
  ((fun a => A (Sum.inl a)), I.interp fun p => A (Sum.inr p))

theorem continuous_jointOfFamily {k : ℕ} {K : Set ℂ} {h : ℝ} (I : CompactInterp K h) :
    Continuous (jointOfFamily (r := r) (k := k) I) :=
  (continuous_pi fun a => continuous_apply (Sum.inl a)).prodMk
    (I.continuous_interp.comp (continuous_pi fun p => continuous_apply (Sum.inr p)))

/-- The weights of `approxJoint`. -/
def approxWeight {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ} {h : ℝ} (I : CompactInterp K h)
    (L δ : ℝ) : Fin k ⊕ I.pts → ℝ → ℂ :=
  Sum.elim (fun a => realWeight L δ (x a)) fun p => nodeWeight L p

theorem approxJoint_eq (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) {k : ℕ} (x : Fin k → ℝ)
    {K : Set ℂ} {h : ℝ} (I : CompactInterp K h) (L δ M : ℝ) :
    approxJoint ν x I L δ M = jointOfFamily I fun q => coordMat ν (approxWeight x I L δ q) M :=
  rfl

theorem continuous_approxWeight {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ}
    (hKs : K ⊆ {z : ℂ | 0 < z.im}) {h : ℝ} (I : CompactInterp K h) (L : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (q : Fin k ⊕ I.pts) : Continuous (approxWeight x I L δ q) := by
  rcases q with a | p
  · exact continuous_realWeight L hδ (x a)
  · exact continuous_nodeWeight L (hKs (I.pts_mem p p.2)).ne'

theorem hasCompactSupport_approxWeight {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ} {h : ℝ}
    (I : CompactInterp K h) (L δ : ℝ) (q : Fin k ⊕ I.pts) :
    HasCompactSupport (approxWeight x I L δ q) := by
  rcases q with a | p
  · exact hasCompactSupport_realWeight L δ (x a)
  · exact hasCompactSupport_nodeWeight L p

/-!
## Deterministic good events
-/

/-- Good event at finite `N`, scale `u ∈ (0, 1]`, residue cutoff `1/u`. -/
theorem dist_le_of_good_atom (F : AtomicHerglotz r) {L : ℝ} (hL : 0 ≤ L) {u c ε : ℝ}
    (hu : 0 < u) (hu1 : u ≤ 1) (hc : 0 < c) (hε : 0 ≤ ε) {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ}
    [CompactSpace K] (hKc : ∀ z ∈ K, c ≤ z.im) (I : CompactInterp K u)
    (h1 : ∀ a, F.atomSum (bumpTest hu (x a) (1 / u)) < 1)
    (h2 : ∀ a, poleMass F < (1 / u) / ((r + 1) * (1 + (|x a| + 1) ^ 2)))
    (h3 : poleMass F < (1 / u) / ((r + 1) * (1 + (L + 1) ^ 2)))
    (h4 : u / c ^ 2 * ((r + 1) * (1 + (L + 1) ^ 2) * poleMass F) ≤ ε) :
    dist (jointValues (nearPart (atomMeasure F) L) x K)
      (approxJoint (atomMeasure F) x I L u (1 / u)) ≤ ε := by
  refine (nearPart_approx (atomMeasure F) hu hc x hKc I (fun a => ?_) ?_ hε ?_).2
  · by_contra hne
    rcases atomMeasure_bad_real F hu hu1 (x a) (1 / u) hne with h | h
    · exact absurd h (not_le.2 (h1 a))
    · exact absurd h (not_le.2 (h2 a))
  · by_contra hne
    exact absurd (atomMeasure_bad_mark F hL (1 / u) hne) (not_le.2 h3)
  · refine le_trans ?_ h4
    exact mul_le_mul_of_nonneg_left (integral_atomMeasure_cutoffs_le F L (1 / u))
      (by positivity)

/-- Good event for the canonical measure. -/
theorem dist_le_of_good_canon (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) {L u c ε : ℝ}
    (hu : 0 < u) (hc : 0 < c) (hε : 0 ≤ ε) {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ}
    [CompactSpace K] (hKc : ∀ z ∈ K, c ≤ z.im) (I : CompactInterp K u)
    (h1 : ∀ a, canonMeasure ξ {p | 0 < |p.1 - x a| ∧ |p.1 - x a| < u} = 0)
    (h2 : canonMeasure ξ {p | |p.1| < L + 1 ∧ 1 / u < matNorm p.2} = 0)
    (h3 : ENNReal.ofReal (u / c ^ 2 * ((r + 1) / Real.pi)) *
      ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * euclidMark p.2) ∂ξ.measure <
        ENNReal.ofReal ε) :
    dist (jointValues (nearPart (canonMeasure ξ) L) x K)
      (approxJoint (canonMeasure ξ) x I L u (1 / u)) ≤ ε := by
  refine (nearPart_approx (canonMeasure ξ) hu hc x hKc I h1 h2 hε ?_).2
  have hb := ofReal_integral_canonMeasure_cutoffs_le ξ L (1 / u)
  set J := ∫ p, smoothCutoff L p.1 * matCutoff (1 / u) p.2 * matNorm p.2 ∂canonMeasure ξ
  have hJ0 : 0 ≤ J := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _) (matCutoff_nonneg _ _)) (matNorm_nonneg _)
  have hlt : ENNReal.ofReal (u / c ^ 2 * J) < ENNReal.ofReal ε := by
    rw [ENNReal.ofReal_mul (by positivity)]
    refine lt_of_le_of_lt ?_ h3
    rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
    exact mul_le_mul_right hb _
  exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1).le

/-!
## The scale `u_n = 1/(n+2)`
-/

/-- The approximation scale `u_n = 1/(n+2)`. -/
def scaleSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem scaleSeq_pos (n : ℕ) : 0 < scaleSeq n := by unfold scaleSeq; positivity

theorem scaleSeq_le_one (n : ℕ) : scaleSeq n ≤ 1 := by
  unfold scaleSeq
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_scaleSeq : Tendsto scaleSeq atTop (𝓝 0) := by
  unfold scaleSeq
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

theorem eventually_const_mul_scaleSeq_lt (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, B * scaleSeq n < η := by
  have := tendsto_scaleSeq.const_mul B
  rw [mul_zero] at this
  exact this.eventually (gt_mem_nhds hη)

theorem eventually_scaleSeq_le {t : ℝ} (ht : 0 < t) : ∀ᶠ n in atTop, scaleSeq n ≤ t :=
  (tendsto_scaleSeq.eventually (ge_mem_nhds ht))

/-- Markov in the form used below: for `a ≥ 0`, `t > 0`, `E W = ofReal C`,
`P(ofReal t ≤ ofReal a · W) ≤ ofReal (a C / t)`. -/
theorem measure_ofReal_le_mul_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → ℝ≥0∞} (hW : AEMeasurable W P) {a t C : ℝ} (ha : 0 ≤ a) (ht : 0 < t)
    (hC : ∫⁻ ω, W ω ∂P = ENNReal.ofReal C) :
    P {ω | ENNReal.ofReal t ≤ ENNReal.ofReal a * W ω} ≤ ENNReal.ofReal (a * C / t) := by
  have hmk := mul_meas_ge_le_lintegral₀ (hW.const_mul (ENNReal.ofReal a)) (ENNReal.ofReal t)
  rw [lintegral_const_mul'' _ hW, hC, ← ENNReal.ofReal_mul ha] at hmk
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hmk

section Main

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

theorem exists_im_lower_bound {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ c > 0, ∀ z ∈ K, c ≤ z.im := by
  by_cases hne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    exact ⟨z₀.im, hKs hz₀, fun z hz => hmin hz⟩
  · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hne⟩

/-- **Convergence in law of the near part.** Law: `F N` on `(Ω N, P N)` with the hypotheses
of the Herglotz tail lemma; `Ξ` a decorated sine process on `(Ω', P')`. For `L ≥ 0`, real
points `x : Fin k → ℝ` and a compact `K ⊆ {Im z > 0}`, as `N → ∞`,
`jointValues (nearPart (atomMeasure F_N) L) x K ⇒ jointValues (nearPart (canonMeasure Ξ) L) x K`
in `(Fin k → Matrix) × C(K, Matrix)` (product of the entrywise and compact-open topologies,
Borel σ-algebra). Here `nearPart (atomMeasure F) L z = Σ_x χ_L(x) (x - z)⁻¹ μ_F({x})` and
`nearPart (canonMeasure Ξ) L = smoothCauchy r Ξ L`. -/
theorem HerglotzTailHypotheses.tendstoInDistribution_nearPart
    (h : HerglotzTailHypotheses r P F P' Ξ) (hΞ : IsDecoratedSineProcess r P' Ξ)
    {L : ℝ} (hL : 0 ≤ L) {k : ℕ} (x : Fin k → ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ {z : ℂ | 0 < z.im}) :
    TendstoInDistribution (fun N ω => jointValues (nearPart (atomMeasure (F N ω)) L) x K) atTop
      (fun ω => jointValues (nearPart (canonMeasure (Ξ ω)) L) x K) P P' := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨c, hc, hKc⟩ := exists_im_lower_bound hK hKs
  set u := scaleSeq with hu
  let I : ∀ n : ℕ, CompactInterp K (u n) := fun n =>
    (exists_compactInterp hK (scaleSeq_pos n)).some
  set X : ℕ → ∀ N, Ω N → JointValues r k K := fun n N ω =>
    approxJoint (atomMeasure (F N ω)) x (I n) L (u n) (1 / u n) with hXdef
  set X' : ℕ → Ω' → JointValues r k K := fun n ω =>
    approxJoint (canonMeasure (Ξ ω)) x (I n) L (u n) (1 / u n) with hX'def
  -- (B) approximants converge for each `n`
  have hX : ∀ n, TendstoInDistribution (X n) atTop (X' n) P P' := by
    intro n
    have T := (h.tendstoInDistribution_coordMat
      (continuous_approxWeight x hKs (I n) L (scaleSeq_pos n))
      (hasCompactSupport_approxWeight x (I n) L (u n)) (1 / u n)).continuous_comp
      (continuous_jointOfFamily (r := r) (I n))
    exact T
  -- constants
  set CL : ℝ := (r + 1) * (1 + (L + 1) ^ 2) with hCL
  have hCL0 : 0 < CL := by positivity
  set Ca : Fin k → ℝ := fun a => (r + 1) * (1 + (|x a| + 1) ^ 2) with hCa
  have hCa0 : ∀ a, 0 < Ca a := fun a => by positivity
  -- (A) measurability of the near part at finite `N`
  have hY : ∀ N, AEMeasurable (fun ω => jointValues (nearPart (atomMeasure (F N ω)) L) x K)
      (P N) := by
    intro N
    refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hX n).forall_aemeasurable N)
      (ae_of_all _ fun ω => ?_)
    set G := F N ω
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- distances from the real points to the other poles
    have hpole : ∀ᶠ n in atTop, ∀ a, ∀ y ∈ G.residue.support, y ≠ x a → u n ≤ |y - x a| := by
      refine Filter.eventually_all.2 fun a => (Filter.eventually_all_finset _).2 fun y _ => ?_
      by_cases hy : y = x a
      · exact Eventually.of_forall fun n hn => absurd hy hn
      · filter_upwards [eventually_scaleSeq_le (abs_pos.2 (sub_ne_zero.2 hy))] with n hn _
        exact hn
    have hmark : ∀ᶠ n in atTop, ∀ y ∈ G.residue.support, matNorm (G.residue y) ≤ 1 / u n := by
      refine (Filter.eventually_all_finset _).2 fun y _ => ?_
      have ht : Tendsto (fun n => 1 / u n) atTop atTop := by
        simp only [hu, scaleSeq, one_div_one_div]
        exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact ht.eventually_ge_atTop _
    have hsmall : ∀ᶠ n in atTop,
        u n / c ^ 2 * ((r + 1) * (1 + (L + 1) ^ 2) * poleMass G) < ε / 2 := by
      have := eventually_const_mul_scaleSeq_lt ((r + 1) * (1 + (L + 1) ^ 2) * poleMass G / c ^ 2)
        (half_pos hε)
      filter_upwards [this] with n hn
      calc u n / c ^ 2 * ((r + 1) * (1 + (L + 1) ^ 2) * poleMass G) =
          (r + 1) * (1 + (L + 1) ^ 2) * poleMass G / c ^ 2 * scaleSeq n := by
            simp only [hu]; ring
        _ < ε / 2 := hn
    obtain ⟨n₀, hn₀⟩ := (hpole.and (hmark.and hsmall)).exists_forall_of_atTop
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨hp, hm, hs⟩ := hn₀ n hn
    have hdist := (nearPart_approx (atomMeasure G) (L := L) (M := 1 / u n) (ε := ε / 2)
      (scaleSeq_pos n) hc x hKc (I n) (fun a => ?_) ?_ (half_pos hε).le ?_).2
    · rw [dist_comm]
      exact lt_of_le_of_lt hdist (half_lt_self hε)
    · refine atomMeasure_eq_zero G fun y hy hmem => ?_
      simp only [mem_ofPred_eq] at hmem
      have hne : y ≠ x a := fun he => by
        rw [he, sub_self, abs_zero] at hmem; exact lt_irrefl _ hmem.1
      exact absurd (hp a y hy hne) (not_le.2 hmem.2)
    · refine atomMeasure_eq_zero G fun y hy hmem => ?_
      simp only [mem_ofPred_eq] at hmem
      exact absurd (hm y hy) (not_le.2 hmem.2)
    · exact le_trans (mul_le_mul_of_nonneg_left (integral_atomMeasure_cutoffs_le G L _)
        (by have := scaleSeq_pos n; positivity)) hs.le
  -- (C) canonical approximants converge in probability
  set Z : Ω' → JointValues r k K := fun ω => jointValues (nearPart (canonMeasure (Ξ ω)) L) x K
    with hZdef
  set I1 : ℝ := ∫ y, smoothCutoff (L + 1) y with hI1
  set I0 : ℝ := ∫ y, smoothCutoff L y with hI0
  have hI10 : 0 ≤ I1 := integral_nonneg (smoothCutoff_nonneg _)
  have hI00 : 0 ≤ I0 := integral_nonneg (smoothCutoff_nonneg _)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hpi := Real.pi_pos
  have hcan : ∀ ε : ℝ, 0 < ε → ∀ n, P' {ω | ε ≤ dist (X' n ω) (Z ω)} ≤
      ENNReal.ofReal ((k * 4 + (r + 1) / Real.pi * (I1 * r) +
        (r + 1) / Real.pi * (I0 * r) * 2 / (c ^ 2 * ε)) * u n) := by
    intro ε hε n
    have hun : 0 < u n := scaleSeq_pos n
    obtain ⟨hWm, hWE⟩ := lintegral_window_mass hΞ L
    set a : ℝ := u n / c ^ 2 * ((r + 1) / Real.pi) with ha
    have ha0 : 0 ≤ a := by positivity
    have hsub : {ω | ε ≤ dist (X' n ω) (Z ω)} ⊆
        ((⋃ i : Fin k, {ω | canonMeasure (Ξ ω)
            {p | 0 < |p.1 - x i| ∧ |p.1 - x i| < u n} ≠ 0}) ∪
          {ω | canonMeasure (Ξ ω) {p | |p.1| < L + 1 ∧ 1 / u n < matNorm p.2} ≠ 0}) ∪
        {ω | ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal a *
          ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * euclidMark p.2) ∂(Ξ ω).measure} := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_not,
        not_le] at hcon
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
      have hd := dist_le_of_good_canon (Ξ ω) (L := L) hun hc (half_pos hε).le x hKc (I n)
        h1 h2 h3
      simp only [mem_ofPred_eq] at hω
      rw [dist_comm] at hd
      linarith [half_lt_self hε]
    have hu0 : u n ≠ 0 := hun.ne'
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add le_rfl (measure_ofReal_le_mul_le hWm.aemeasurable ha0 (half_pos hε)
      hWE)).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add le_rfl (measure_canon_bad_mark_le hΞ L
      (by positivity : (0 : ℝ) < 1 / u n))) le_rfl).trans ?_
    refine (add_le_add (add_le_add ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun i _ => measure_canon_bad_real_le hΞ hun (x i))) le_rfl)
      le_rfl).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (r + 1) / (Real.pi * (1 / u n))),
      ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (k : ℝ) * (4 * u n))
        (by positivity : (0 : ℝ) ≤ (r + 1) / (Real.pi * (1 / u n)) * (I1 * r)),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [ha]
    field_simp
    ring
  have hTIM : TendstoInMeasure P' X' atTop Z := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hlim : Tendsto (fun n => ENNReal.ofReal ((k * 4 + (r + 1) / Real.pi * (I1 * r) +
        (r + 1) / Real.pi * (I0 * r) * 2 / (c ^ 2 * ε)) * u n)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_scaleSeq.const_mul ((k * 4 +
        (r + 1) / Real.pi * (I1 * r) + (r + 1) / Real.pi * (I0 * r) * 2 / (c ^ 2 * ε))))
      simp only [mul_zero, ENNReal.ofReal_zero] at this
      refine this.congr fun n => ?_
      rw [hu, mul_comm]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (hcan ε hε)
  have hX' : TendstoInDistribution X' atTop Z (fun _ => P') P' :=
    hTIM.tendstoInDistribution fun n => (hX n).aemeasurable_limit
  -- (D) finite-`N` closeness
  have hclose : ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ᶠ N in atTop,
      P N {ω | ε ≤ dist (jointValues (nearPart (atomMeasure (F N ω)) L) x K) (X n N ω)} ≤
        ENNReal.ofReal η := by
    intro ε hε η hη
    set B : ℝ := ∑ i : Fin k, (5 + (r + 1) * Ca i) + (r + 1) * CL +
      (r + 1) * CL * 2 / (c ^ 2 * ε) with hB
    filter_upwards [eventually_const_mul_scaleSeq_lt B hη] with n hn
    have hun : 0 < u n := scaleSeq_pos n
    have hun1 : u n ≤ 1 := scaleSeq_le_one n
    set t : ℝ := ε / 2 * c ^ 2 / (u n * CL) with ht
    have ht0 : 0 < t := by positivity
    have hev1 := Filter.eventually_all.2 fun i : Fin k =>
      h.eventually_measure_bumpTest_le hΞ hun (x i) (1 / u n) hun
    have hev2 := Filter.eventually_all.2 fun i : Fin k =>
      h.eventually_measure_poleMass_ge_le (t := (1 / u n) / Ca i) (by
        have := hCa0 i; positivity)
    have hev3 := h.eventually_measure_poleMass_ge_le (t := (1 / u n) / CL) (by positivity)
    have hev4 := h.eventually_measure_poleMass_ge_le ht0
    filter_upwards [hev1, hev2, hev3, hev4] with N h1 h2 h3 h4
    have hsub : {ω | ε ≤ dist (jointValues (nearPart (atomMeasure (F N ω)) L) x K)
        (X n N ω)} ⊆
        (((⋃ i : Fin k, ({ω | 1 ≤ (F N ω).atomSum (bumpTest hun (x i) (1 / u n))} ∪
          {ω | (1 / u n) / Ca i ≤ poleMass (F N ω)})) ∪
          {ω | (1 / u n) / CL ≤ poleMass (F N ω)}) ∪ {ω | t ≤ poleMass (F N ω)}) := by
      intro ω hω
      by_contra hcon
      simp only [mem_union, mem_iUnion, mem_ofPred_eq, not_or, not_exists, not_le] at hcon
      obtain ⟨⟨hA, hC⟩, hD⟩ := hcon
      have hS := poleMass_nonneg (F N ω)
      have h4' : u n / c ^ 2 * ((r + 1) * (1 + (L + 1) ^ 2) * poleMass (F N ω)) ≤ ε / 2 := by
        have : u n / c ^ 2 * (CL * poleMass (F N ω)) ≤ u n / c ^ 2 * (CL * t) := by
          gcongr
        have heq : u n / c ^ 2 * (CL * t) = ε / 2 := by
          have := hun.ne'
          have := hCL0.ne'
          rw [ht]; field_simp
        rw [hCL] at this heq
        linarith
      have hd := dist_le_of_good_atom (F N ω) hL hun hun1 hc (half_pos hε).le x hKc (I n)
        (fun i => (hA i).1) (fun i => (hA i).2) hC h4'
      simp only [mem_ofPred_eq] at hω
      linarith [half_lt_self hε]
    refine (measure_mono hsub).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add le_rfl h4).trans ?_
    refine (add_le_add (measure_union_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add le_rfl h3) le_rfl).trans ?_
    refine (add_le_add (add_le_add ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun i _ => (measure_union_le _ _).trans (add_le_add (h1 i) (h2 i))))
      le_rfl) le_rfl).trans ?_
    have hnn : ∀ i : Fin k, 0 ≤ (r + 1) / ((1 / u n) / Ca i) := fun i => by
      have := hCa0 i; positivity
    simp_rw [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 4 * u n + u n) (hnn _)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by have := hnn i; positivity,
      ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by have := hnn i; positivity)
        (by positivity), ← ENNReal.ofReal_add (by
          have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (by
            have := hnn i; positivity : (0 : ℝ) ≤ 4 * u n + u n + (r + 1) / ((1 / u n) / Ca i))
          positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_eq_of_lt ?_ hn))
    rw [show scaleSeq n = u n from rfl]
    have hc2 : c ^ 2 ≠ 0 := by positivity
    have hu0 : u n ≠ 0 := hun.ne'
    have hCL1 : CL ≠ 0 := hCL0.ne'
    have hε0 : ε ≠ 0 := hε.ne'
    have hsum : ∑ i : Fin k, (4 * u n + u n + (r + 1) / ((1 / u n) / Ca i)) =
        ∑ i : Fin k, (5 + (r + 1) * Ca i) * u n := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have := (hCa0 i).ne'
      field_simp
      ring
    rw [hsum, ← Finset.sum_mul, hB, ht]
    field_simp
  exact tendstoInDistribution_of_forall_approx hY hX hX' hclose

end Main

end BlockBand.Critical.Herglotz
