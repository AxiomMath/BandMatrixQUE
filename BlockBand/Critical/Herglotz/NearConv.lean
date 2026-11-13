module

public import BlockBand.Critical.Herglotz.Mass
public import BlockBand.Critical.Herglotz.MarkTruncation
public import BlockBand.Critical.Herglotz.ProductMoments

/-!
# Near parts: finite-dimensional laws and bad events

* `HerglotzTailHypotheses.poles_fintype`: hypothesis 1 for finitely many tests indexed by any
  finite type.
* `HerglotzTailHypotheses.tendstoInDistribution_coordMat`: joint convergence in law of the
  truncated matrix coordinates `coordMat (atomMeasure F_N) w_q M` to their canonical values
  (`coordMat (canonMeasure Ξ) w_q M`), for continuous compactly supported complex weights.
* `pointBump`, `bumpTest`: a bump at a real point and the residue-truncated counting test.
* Finite-`N` bad events (`atomMeasure_bad_real`, `atomMeasure_bad_mark`,
  `integral_atomMeasure_cutoffs_le`): a pole at distance in `(0, δ)` from `x₀` forces either a
  bump coordinate `≥ 1` or a large pole mass; a large residue near the window or a large
  weighted residue mass forces a large pole mass.
* Canonical bad events (`measure_canon_bad_real_le`: no point of `𝖢_r` at distance in `(0, δ)`
  from `x₀` except with probability `≤ 4δ`; `measure_canon_bad_mark_le`,
  `ofReal_integral_canonMeasure_cutoffs_le`), by the decorated sine intensity and Markov.
* `HerglotzTailHypotheses.eventually_measure_bumpTest_le` (the same for `F_N`): eventually in
  `N`, `P(atomSum(bumpTest) ≥ 1) ≤ 4δ + η`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexConjugate ComplexOrder

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

section Hyp

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

/-- **Hypothesis 1 for a finite family of tests indexed by any finite type** (reindexing of
`HerglotzTailHypotheses.poles` through `Fintype.equivFin`). -/
theorem HerglotzTailHypotheses.poles_fintype (h : HerglotzTailHypotheses r P F P' Ξ)
    {ι : Type*} [Fintype ι]
    (f : ι → CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    TendstoInDistribution (fun N ω t => (F N ω).atomSum (f t)) atTop
      (fun ω t => ∫ p, f t (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) P P' := by
  set e := Fintype.equivFin ι
  have T := h.poles (Fintype.card ι) fun s => f (e.symm s)
  have hG : Continuous fun (y : Fin (Fintype.card ι) → ℝ) (t : ι) => y (e t) :=
    continuous_pi fun t => continuous_apply _
  have T2 := T.continuous_comp hG
  have k1 : (fun N ω t => (F N ω).atomSum (f t)) = fun N =>
      (fun (y : Fin (Fintype.card ι) → ℝ) (t : ι) => y (e t)) ∘
        (fun ω k => (F N ω).atomSum (f (e.symm k))) := by
    funext N ω t; simp
  have k2 : (fun ω t => ∫ p, f t (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) =
      (fun (y : Fin (Fintype.card ι) → ℝ) (t : ι) => y (e t)) ∘
        (fun ω k => ∫ p, f (e.symm k) (p.1, canonicalResidue p.2) ∂(Ξ ω).measure) := by
    funext ω t; simp
  rw [k1, k2]
  exact T2

/-- **Joint law of truncated matrix coordinates** (hypothesis 1, complex matrix form). For a
finite family of continuous compactly supported weights `w q : ℝ → ℂ` and a residue cutoff
level `M`, the vector `(∫ w_q(y) ψ_M(ρ) ρ dν_N)_q` with `ν_N = atomMeasure F_N` converges in
law to the same vector for `ν = canonMeasure Ξ`. -/
theorem HerglotzTailHypotheses.tendstoInDistribution_coordMat
    (h : HerglotzTailHypotheses r P F P' Ξ) {Q : Type*} [Fintype Q] {w : Q → ℝ → ℂ}
    (hw : ∀ q, Continuous (w q)) (hwc : ∀ q, HasCompactSupport (w q)) (M : ℝ) :
    TendstoInDistribution (fun N ω q => coordMat (atomMeasure (F N ω)) (w q) M) atTop
      (fun ω q => coordMat (canonMeasure (Ξ ω)) (w q) M) P P' := by
  let f : Q × Fin r × Fin r × Bool → CompactlySupportedContinuousMap
      (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ :=
    fun t => coordTest (hw t.1) (hwc t.1) M t.2.1 t.2.2.1 t.2.2.2
  have T := h.poles_fintype f
  let G : (Q × Fin r × Fin r × Bool → ℝ) → (Q → Matrix (Fin r) (Fin r) ℂ) :=
    fun y q i j => (y (q, i, j, true) : ℂ) + (y (q, i, j, false) : ℂ) * Complex.I
  have hG : Continuous G := by
    refine continuous_pi fun q => continuous_pi fun i => continuous_pi fun j => ?_
    exact (Complex.continuous_ofReal.comp (continuous_apply _)).add
      ((Complex.continuous_ofReal.comp (continuous_apply _)).mul continuous_const)
  have T2 := T.continuous_comp hG
  have k1 : (fun N ω q => coordMat (atomMeasure (F N ω)) (w q) M) = fun N =>
      G ∘ fun ω t => (F N ω).atomSum (f t) := by
    funext N ω q i j
    simp only [G, f, atomSum_eq_integral]
    exact coordMat_eq _ (hw _) (hwc _) M _ _
  have k2 : (fun ω q => coordMat (canonMeasure (Ξ ω)) (w q) M) =
      G ∘ fun ω t => ∫ p, f t (p.1, canonicalResidue p.2) ∂(Ξ ω).measure := by
    funext ω q i j
    rw [coordMat_eq _ (hw q) (hwc q) M i j,
      integral_canonMeasure (Ξ ω) (f := fun p => coordTest (hw q) (hwc q) M i j true p)
        (map_continuous (coordTest (hw q) (hwc q) M i j true)).aestronglyMeasurable,
      integral_canonMeasure (Ξ ω) (f := fun p => coordTest (hw q) (hwc q) M i j false p)
        (map_continuous (coordTest (hw q) (hwc q) M i j false)).aestronglyMeasurable]
    rfl
  rw [k1, k2]
  exact T2

end Hyp

/-!
## Bumps
-/

/-- `pointBump δ x₀ u = χ_1((u - x₀)/δ)`: `1` on `|u - x₀| ≤ δ`, `0` on `|u - x₀| ≥ 2δ`. -/
def pointBump (δ x₀ u : ℝ) : ℝ := smoothCutoff 1 ((u - x₀) / δ)

theorem continuous_pointBump (δ x₀ : ℝ) : Continuous (pointBump δ x₀) :=
  (continuous_smoothCutoff 1).comp ((continuous_id.sub continuous_const).div_const _)

theorem pointBump_nonneg (δ x₀ u : ℝ) : 0 ≤ pointBump δ x₀ u := smoothCutoff_nonneg _ _

theorem pointBump_le_one (δ x₀ u : ℝ) : pointBump δ x₀ u ≤ 1 := smoothCutoff_le_one _ _

theorem pointBump_eq_one {δ x₀ u : ℝ} (hδ : 0 < δ) (h : |u - x₀| ≤ δ) :
    pointBump δ x₀ u = 1 := by
  refine smoothCutoff_eq_one ?_
  rw [abs_div, abs_of_pos hδ, div_le_one hδ]
  exact h

theorem pointBump_eq_zero {δ x₀ u : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ |u - x₀|) :
    pointBump δ x₀ u = 0 := by
  refine smoothCutoff_eq_zero ?_
  rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
  linarith

theorem pointBump_le_indicator {δ x₀ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    pointBump δ x₀ u ≤ (Icc (x₀ - 2 * δ) (x₀ + 2 * δ)).indicator 1 u := by
  by_cases hu : u ∈ Icc (x₀ - 2 * δ) (x₀ + 2 * δ)
  · rw [indicator_of_mem hu, Pi.one_apply]; exact pointBump_le_one _ _ _
  · rw [indicator_of_notMem hu, pointBump_eq_zero hδ]
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith

theorem hasCompactSupport_pointBump {δ x₀ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (pointBump δ x₀) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := x₀ - 2 * δ) (b := x₀ + 2 * δ))
    fun u hu => le_antisymm ?_ (pointBump_nonneg _ _ _)
  have := pointBump_le_indicator (x₀ := x₀) hδ u
  rwa [indicator_of_notMem hu] at this

theorem integrable_pointBump {δ x₀ : ℝ} (hδ : 0 < δ) : Integrable (pointBump δ x₀) :=
  (continuous_pointBump δ x₀).integrable_of_hasCompactSupport (hasCompactSupport_pointBump hδ)

theorem integral_pointBump_le {δ x₀ : ℝ} (hδ : 0 < δ) : ∫ u, pointBump δ x₀ u ≤ 4 * δ := by
  have hS : MeasurableSet (Icc (x₀ - 2 * δ) (x₀ + 2 * δ)) := measurableSet_Icc
  have hi : Integrable ((Icc (x₀ - 2 * δ) (x₀ + 2 * δ)).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff hS).2 continuous_const.integrableOn_Icc
  calc ∫ u, pointBump δ x₀ u ≤ ∫ u, (Icc (x₀ - 2 * δ) (x₀ + 2 * δ)).indicator 1 u :=
        integral_mono (integrable_pointBump hδ) hi (pointBump_le_indicator hδ)
    _ = 4 * δ := by
        rw [integral_indicator_one hS, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-- The residue-truncated counting test `pointBump δ x₀ (y) ψ_M(ρ)` on `ℝ × Matrix`. -/
def bumpTest {δ : ℝ} (hδ : 0 < δ) (x₀ M : ℝ) :
    CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ where
  toFun p := pointBump δ x₀ p.1 * matCutoff M p.2
  continuous_toFun := ((continuous_pointBump δ x₀).comp continuous_fst).mul
    ((continuous_matCutoff M).comp continuous_snd)
  hasCompactSupport' := by
    refine HasCompactSupport.intro ((hasCompactSupport_pointBump (x₀ := x₀) hδ).isCompact.prod
      (isCompact_matNorm_le (M + 1))) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
    · rw [matCutoff_eq_zero (le_of_lt (not_le.1 h)), mul_zero]

theorem bumpTest_apply {δ : ℝ} (hδ : 0 < δ) (x₀ M : ℝ) (p : ℝ × Matrix (Fin r) (Fin r) ℂ) :
    bumpTest hδ x₀ M p = pointBump δ x₀ p.1 * matCutoff M p.2 := rfl

theorem bumpTest_nonneg {δ : ℝ} (hδ : 0 < δ) (x₀ M : ℝ) (p : ℝ × Matrix (Fin r) (Fin r) ℂ) :
    0 ≤ bumpTest hδ x₀ M p :=
  mul_nonneg (pointBump_nonneg _ _ _) (matCutoff_nonneg _ _)

/-!
## Finite-`N` bad events
-/

theorem exists_mem_of_atomMeasure_ne_zero (F : AtomicHerglotz r)
    {s : Set (ℝ × Matrix (Fin r) (Fin r) ℂ)} (h : atomMeasure F s ≠ 0) :
    ∃ x ∈ F.residue.support, (x, F.residue x) ∈ s := by
  by_contra hc
  push Not at hc
  exact h (atomMeasure_eq_zero F hc)

/-- A pole at distance in `(0, δ)` from `x₀` (`δ ≤ 1`) forces a bump coordinate `≥ 1` or pole
mass `≥ M / ((r+1)(1 + (|x₀|+1)²))`. -/
theorem atomMeasure_bad_real (F : AtomicHerglotz r) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x₀ M : ℝ) (h : atomMeasure F {p | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} ≠ 0) :
    1 ≤ F.atomSum (bumpTest hδ x₀ M) ∨
      M / ((r + 1) * (1 + (|x₀| + 1) ^ 2)) ≤ poleMass F := by
  obtain ⟨y, hy, hys⟩ := exists_mem_of_atomMeasure_ne_zero F h
  simp only [mem_ofPred_eq] at hys
  by_cases hM : matNorm (F.residue y) ≤ M
  · left
    have hterm : bumpTest hδ x₀ M (y, F.residue y) = 1 := by
      rw [bumpTest_apply, pointBump_eq_one hδ hys.2.le, matCutoff_eq_one hM, one_mul]
    unfold AtomicHerglotz.atomSum
    rw [← hterm]
    exact Finset.single_le_sum (f := fun x => bumpTest hδ x₀ M (x, F.residue x))
      (fun x _ => bumpTest_nonneg hδ x₀ M _) hy
  · right
    have h1 := matNorm_residue_le F hy
    have hyb : y ^ 2 ≤ (|x₀| + 1) ^ 2 := by
      rw [← sq_abs y]
      have : |y| ≤ |x₀| + 1 := by
        have := abs_sub_abs_le_abs_sub y x₀
        linarith [hys.2]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hS := poleMass_nonneg F
    have hpos : (0 : ℝ) < (r + 1) * (1 + (|x₀| + 1) ^ 2) := by positivity
    rw [div_le_iff₀ hpos]
    have : (r + 1) * (1 + y ^ 2) * poleMass F ≤ (r + 1) * (1 + (|x₀| + 1) ^ 2) * poleMass F := by
      gcongr
    nlinarith [not_le.1 hM]

/-- A residue with `matNorm > M` over `|y| < L + 1` forces pole mass
`≥ M / ((r+1)(1 + (L+1)²))`. -/
theorem atomMeasure_bad_mark (F : AtomicHerglotz r) {L : ℝ} (hL : 0 ≤ L) (M : ℝ)
    (h : atomMeasure F {p | |p.1| < L + 1 ∧ M < matNorm p.2} ≠ 0) :
    M / ((r + 1) * (1 + (L + 1) ^ 2)) ≤ poleMass F := by
  obtain ⟨y, hy, hys⟩ := exists_mem_of_atomMeasure_ne_zero F h
  simp only [mem_ofPred_eq] at hys
  have h1 := matNorm_residue_le F hy
  have hyb : y ^ 2 ≤ (L + 1) ^ 2 := by
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hys.1.le 2
  have hS := poleMass_nonneg F
  have hpos : (0 : ℝ) < (r + 1) * (1 + (L + 1) ^ 2) := by positivity
  rw [div_le_iff₀ hpos]
  have : (r + 1) * (1 + y ^ 2) * poleMass F ≤ (r + 1) * (1 + (L + 1) ^ 2) * poleMass F := by
    gcongr
  nlinarith [hys.2]

/-- Weighted residue mass of the window: `∫ χ_L ψ_M matNorm dν_F ≤ (r+1)(1+(L+1)²) poleMass F`. -/
theorem integral_atomMeasure_cutoffs_le (F : AtomicHerglotz r) (L M : ℝ) :
    ∫ p, smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2 ∂atomMeasure F ≤
      (r + 1) * (1 + (L + 1) ^ 2) * poleMass F := by
  rw [integral_atomMeasure]
  unfold poleMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have ht := trace_re_nonneg (F.residue_posSemidef y)
  have hm := PosSemidef.matNorm_le_trace (F.residue_posSemidef y)
  have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
  by_cases hyL : |y| < L + 1
  · have hyb : y ^ 2 ≤ (L + 1) ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hyL.le 2
    have hχ := smoothCutoff_le_one L y
    have hψ := matCutoff_le_one M (F.residue y)
    have hχ0 := smoothCutoff_nonneg L y
    have hψ0 := matCutoff_nonneg M (F.residue y)
    have hmn := matNorm_nonneg (F.residue y)
    have h1 : smoothCutoff L y * matCutoff M (F.residue y) * matNorm (F.residue y) ≤
        matNorm (F.residue y) := by
      have : smoothCutoff L y * matCutoff M (F.residue y) ≤ 1 := by nlinarith
      nlinarith
    have h2 : matNorm (F.residue y) ≤ (r + 1) * (Matrix.trace (F.residue y)).re := by nlinarith
    have h3 : (r + 1) * (Matrix.trace (F.residue y)).re =
        (r + 1) * (1 + y ^ 2) * ((Matrix.trace (F.residue y)).re / (1 + y ^ 2)) := by
      field_simp
    have h4 : (r + 1) * (1 + y ^ 2) * ((Matrix.trace (F.residue y)).re / (1 + y ^ 2)) ≤
        (r + 1) * (1 + (L + 1) ^ 2) * ((Matrix.trace (F.residue y)).re / (1 + y ^ 2)) := by
      gcongr
    linarith
  · rw [smoothCutoff_eq_zero (not_lt.1 hyL), zero_mul, zero_mul]
    positivity

/-!
## Canonical bad events
-/

theorem canonicalResidue_posSemidef (g : Fin r → ℂ) : (canonicalResidue g).PosSemidef := by
  unfold canonicalResidue
  refine (Matrix.posSemidef_vecMulVec_self_star g).smul ?_
  rw [← Complex.ofReal_inv]
  exact Complex.zero_le_real.2 (inv_nonneg.2 Real.pi_pos.le)

theorem matNorm_canonicalResidue_le (g : Fin r → ℂ) :
    matNorm (canonicalResidue g) ≤ (r + 1) / Real.pi * euclidMark g := by
  have h1 := PosSemidef.matNorm_le_trace (canonicalResidue_posSemidef g)
  have htr : (Matrix.trace (canonicalResidue g)).re = Real.pi⁻¹ * euclidMark g := by
    rw [Matrix.trace, Complex.re_sum]
    unfold euclidMark
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, canonicalResidue_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_inv]
    norm_cast
  rw [htr] at h1
  have he := euclidMark_nonneg g
  have hpi := Real.pi_pos
  calc matNorm (canonicalResidue g) ≤ r * (Real.pi⁻¹ * euclidMark g) := h1
    _ ≤ (r + 1) * (Real.pi⁻¹ * euclidMark g) := by
        gcongr; linarith
    _ = (r + 1) / Real.pi * euclidMark g := by ring

theorem measurableSet_bad_real (x₀ δ : ℝ) :
    MeasurableSet {p : ℝ × Matrix (Fin r) (Fin r) ℂ | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} := by
  have hf : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => |p.1 - x₀| :=
    ((continuous_fst.sub continuous_const).abs).measurable
  rw [Set.ofPred_and]
  exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)

theorem measurableSet_bad_mark (L M : ℝ) :
    MeasurableSet {p : ℝ × Matrix (Fin r) (Fin r) ℂ | |p.1| < L + 1 ∧ M < matNorm p.2} := by
  have hf : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => |p.1| :=
    continuous_fst.abs.measurable
  rw [Set.ofPred_and]
  exact (measurableSet_lt hf measurable_const).inter
    (measurableSet_lt measurable_const (continuous_matNorm.measurable.comp measurable_snd))

/-- A nonzero value of an integer-valued point measure is at least `1`. -/
theorem one_le_of_ne_zero (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) {A : Set (ℝ × (Fin r → ℂ))}
    (hA : MeasurableSet A) (h : ξ.measure A ≠ 0) : 1 ≤ ξ.measure A := by
  rcases ξ.integer_valued A hA with h1 | ⟨n, hn⟩
  · rw [h1]; exact le_top
  · rw [hn] at h ⊢
    have : n ≠ 0 := by rintro rfl; exact h (by simp)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this

/-- **No canonical point near a real point**: `P(Ξ has a point at distance in (0, δ) from x₀) ≤ 4δ`
(outer measure). Law: `Ξ` decorated sine. Proof: integer values, the bump `≥` indicator, Markov
and the decorated sine intensity (`lintegral_lintegral_ofReal_of_decoratedSine`). -/
theorem measure_canon_bad_real_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {δ : ℝ} (hδ : 0 < δ) (x₀ : ℝ) :
    P {ω | canonMeasure (Ξ ω) {p | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} ≠ 0} ≤
      ENNReal.ofReal (4 * δ) := by
  have := h.prob
  set A : Set (ℝ × (Fin r → ℂ)) := {p | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} with hAdef
  have hA : MeasurableSet A := by
    have hf : Measurable fun p : ℝ × (Fin r → ℂ) => |p.1 - x₀| :=
      ((continuous_fst.sub continuous_const).abs).measurable
    rw [hAdef, Set.ofPred_and]
    exact (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)
  have hpre : ∀ ω, canonMeasure (Ξ ω) {p | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} = (Ξ ω).measure A := by
    intro ω
    unfold canonMeasure
    rw [Measure.map_apply continuous_canonMap.measurable (measurableSet_bad_real x₀ δ)]
    rfl
  set f : ℝ × (Fin r → ℂ) → ℝ := fun p => pointBump δ x₀ p.1 with hf
  have hfc : Continuous f := (continuous_pointBump δ x₀).comp continuous_fst
  have hfS : ∀ x g, x ∉ Icc (x₀ - 2 * δ) (x₀ + 2 * δ) → f (x, g) = 0 := by
    intro x g hx
    have := pointBump_le_indicator (x₀ := x₀) hδ x
    rw [indicator_of_notMem hx] at this
    exact le_antisymm this (pointBump_nonneg _ _ _)
  obtain ⟨hmeas, hE⟩ := lintegral_lintegral_ofReal_of_decoratedSine h hfc
    (fun p => pointBump_nonneg _ _ _) isCompact_Icc hfS
  have hsub : {ω | canonMeasure (Ξ ω) {p | 0 < |p.1 - x₀| ∧ |p.1 - x₀| < δ} ≠ 0} ⊆
      {ω | 1 ≤ ∫⁻ p, ENNReal.ofReal (f p) ∂(Ξ ω).measure} := by
    intro ω hω
    simp only [mem_ofPred_eq, hpre] at hω ⊢
    refine (one_le_of_ne_zero (Ξ ω) hA hω).trans ?_
    rw [← lintegral_indicator_one hA]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ A
    · rw [indicator_of_mem hp, Pi.one_apply]
      show 1 ≤ ENNReal.ofReal (pointBump δ x₀ p.1)
      rw [pointBump_eq_one hδ hp.2.le, ENNReal.ofReal_one]
    · rw [indicator_of_notMem hp]; exact bot_le
  refine (measure_mono hsub).trans ?_
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hmeas.aemeasurable 1
  rw [one_mul, hE] at hmk
  refine hmk.trans ?_
  simp only [hf, lintegral_const, measure_univ, mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pointBump hδ)
    (Eventually.of_forall (pointBump_nonneg δ x₀))]
  exact ENNReal.ofReal_le_ofReal (integral_pointBump_le hδ)

/-- **Large canonical residues near the window.** For `M > 0`,
`P(Ξ has a point with |x| < L+1 and matNorm(π⁻¹gg^*) > M) ≤ (r+1)/(πM) · r ∫ χ_{L+1}`. -/
theorem measure_canon_bad_mark_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    (L : ℝ) {M : ℝ} (hM : 0 < M) :
    P {ω | canonMeasure (Ξ ω) {p | |p.1| < L + 1 ∧ M < matNorm p.2} ≠ 0} ≤
      ENNReal.ofReal ((r + 1) / (Real.pi * M)) *
        ENNReal.ofReal ((∫ x, smoothCutoff (L + 1) x) * r) := by
  have := h.prob
  set A : Set (ℝ × (Fin r → ℂ)) := {p | |p.1| < L + 1 ∧ M < matNorm (canonicalResidue p.2)}
    with hAdef
  have hA : MeasurableSet A := by
    have hf : Measurable fun p : ℝ × (Fin r → ℂ) => |p.1| := continuous_fst.abs.measurable
    rw [hAdef, Set.ofPred_and]
    exact (measurableSet_lt hf measurable_const).inter (measurableSet_lt measurable_const
      ((continuous_matNorm.comp continuous_canonicalResidue).measurable.comp measurable_snd))
  have hpre : ∀ ω, canonMeasure (Ξ ω) {p | |p.1| < L + 1 ∧ M < matNorm p.2} =
      (Ξ ω).measure A := by
    intro ω
    unfold canonMeasure
    rw [Measure.map_apply continuous_canonMap.measurable (measurableSet_bad_mark L M)]
    rfl
  obtain ⟨hmeas, hE, -⟩ := productTest_lintegral h (continuous_smoothCutoff (L + 1))
    (hasCompactSupport_smoothCutoff (L + 1)) (smoothCutoff_nonneg (L + 1))
    continuous_euclidMark euclidMark_nonneg integrable_euclidMark_sq
  rw [integral_euclidMark] at hE
  set c : ℝ := (r + 1) / (Real.pi * M) with hc
  have hc0 : 0 ≤ c := by positivity
  have hsub : {ω | canonMeasure (Ξ ω) {p | |p.1| < L + 1 ∧ M < matNorm p.2} ≠ 0} ⊆
      {ω | 1 ≤ ENNReal.ofReal c *
        ∫⁻ p, ENNReal.ofReal (smoothCutoff (L + 1) p.1 * euclidMark p.2) ∂(Ξ ω).measure} := by
    intro ω hω
    simp only [mem_ofPred_eq, hpre] at hω ⊢
    refine (one_le_of_ne_zero (Ξ ω) hA hω).trans ?_
    rw [← lintegral_indicator_one hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun p => ?_
    by_cases hp : p ∈ A
    · rw [indicator_of_mem hp, Pi.one_apply, ← ENNReal.ofReal_mul hc0]
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := matNorm_canonicalResidue_le p.2
      rw [smoothCutoff_eq_one (by linarith [hp.1] : |p.1| ≤ L + 1), one_mul, hc]
      have hpi := Real.pi_pos
      have h2 : M < (r + 1) / Real.pi * euclidMark p.2 := lt_of_lt_of_le hp.2 h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, lt_div_iff₀ hpi] at h2
      linarith
    · rw [indicator_of_notMem hp]; exact bot_le
  refine (measure_mono hsub).trans ?_
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) (hmeas.const_mul (ENNReal.ofReal c)).aemeasurable 1
  rw [one_mul, lintegral_const_mul _ hmeas, hE] at hmk
  exact hmk

/-- Canonical weighted residue mass of the window, in `ℝ≥0∞`:
`ofReal (∫ χ_L ψ_M matNorm d(canonMeasure ξ)) ≤ ofReal((r+1)/π) ∫⁻ χ_L(x) |g|² dξ`. -/
theorem ofReal_integral_canonMeasure_cutoffs_le (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ)))
    (L M : ℝ) :
    ENNReal.ofReal (∫ p, smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2 ∂canonMeasure ξ) ≤
      ENNReal.ofReal ((r + 1) / Real.pi) *
        ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * euclidMark p.2) ∂ξ.measure := by
  have hc : Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2 :=
    (continuous_cutoffs L M).mul (continuous_matNorm.comp continuous_snd)
  have hint : Integrable (fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2) (canonMeasure ξ) :=
    hc.integrable_of_hasCompactSupport (hasCompactSupport_cutoffs L M).mul_right
  have hnn : ∀ p : ℝ × Matrix (Fin r) (Fin r) ℂ,
      0 ≤ smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2 := fun p =>
    mul_nonneg (mul_nonneg (smoothCutoff_nonneg _ _) (matCutoff_nonneg _ _)) (matNorm_nonneg _)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn),
    lintegral_canonMeasure ξ (f := fun p => ENNReal.ofReal
      (smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2))
      (ENNReal.measurable_ofReal.comp hc.measurable),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun p => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := matNorm_canonicalResidue_le p.2
  have hχ := smoothCutoff_le_one L p.1
  have hχ0 := smoothCutoff_nonneg L p.1
  have hψ := matCutoff_le_one M (canonicalResidue p.2)
  have hψ0 := matCutoff_nonneg M (canonicalResidue p.2)
  have hm := matNorm_nonneg (canonicalResidue p.2)
  have he := euclidMark_nonneg p.2
  calc smoothCutoff L p.1 * matCutoff M (canonicalResidue p.2) * matNorm (canonicalResidue p.2)
      ≤ smoothCutoff L p.1 * 1 * ((r + 1) / Real.pi * euclidMark p.2) := by gcongr
    _ = (r + 1) / Real.pi * (smoothCutoff L p.1 * euclidMark p.2) := by ring

/-- `E ∫⁻ χ_L(x) |g|² dΞ = ofReal (r ∫ χ_L)`, and measurability. -/
theorem lintegral_window_mass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ) (L : ℝ) :
    Measurable (fun ω => ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * euclidMark p.2)
      ∂(Ξ ω).measure) ∧
    ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (smoothCutoff L p.1 * euclidMark p.2) ∂(Ξ ω).measure ∂P =
      ENNReal.ofReal ((∫ x, smoothCutoff L x) * r) := by
  obtain ⟨hmeas, hE, -⟩ := productTest_lintegral h (continuous_smoothCutoff L)
    (hasCompactSupport_smoothCutoff L) (smoothCutoff_nonneg L)
    continuous_euclidMark euclidMark_nonneg integrable_euclidMark_sq
  rw [integral_euclidMark] at hE
  exact ⟨hmeas, hE⟩

section Hyp2

variable {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
  [∀ N, IsProbabilityMeasure (P N)] {F : ∀ N, Ω N → AtomicHerglotz r} {Ω' : Type*}
  [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin r → ℂ))}

/-- **No pole near a real point, at finite `N`.** Under hypothesis 1 and the decorated sine law of `Ξ`: for `δ > 0`,
every `x₀, M` and `η > 0`, eventually in `N`,
`P_N(atomSum F_N (bumpTest δ x₀ M) ≥ 1) ≤ 4δ + η` (outer measure). Proof: the bounded continuous
functional `min(max(·, 0), 1)` of the coordinate converges in law (hypothesis 1); its canonical
mean is at most the intensity `∫ pointBump ≤ 4δ`. -/
theorem HerglotzTailHypotheses.eventually_measure_bumpTest_le
    (h : HerglotzTailHypotheses r P F P' Ξ) (hΞ : IsDecoratedSineProcess r P' Ξ) {δ : ℝ}
    (hδ : 0 < δ) (x₀ M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N in atTop, P N {ω | 1 ≤ (F N ω).atomSum (bumpTest hδ x₀ M)} ≤
      ENNReal.ofReal (4 * δ + η) := by
  have T := h.poles 1 fun _ => bumpTest hδ x₀ M
  let G : BoundedContinuousFunction (Fin 1 → ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun y => min (max (y 0) 0) 1, by fun_prop⟩ 1
      (fun y z => by
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        rw [abs_le]
        constructor <;>
        · have := le_max_right (y 0) 0
          have := le_max_right (z 0) 0
          have := min_le_right (max (y 0) 0) 1
          have := min_le_right (max (z 0) 0) 1
          have := le_min (le_max_right (y 0) 0) zero_le_one
          have := le_min (le_max_right (z 0) 0) zero_le_one
          linarith)
  have hG := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ T.forall_aemeasurable
    T.aemeasurable_limit).1 T G
  -- canonical mean bound
  have hcan : ∫ ω, G (fun _ => ∫ p, bumpTest hδ x₀ M (p.1, canonicalResidue p.2)
      ∂(Ξ ω).measure) ∂P' ≤ 4 * δ := by
    set f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ :=
      ⟨⟨fun p => bumpTest hδ x₀ M (p.1, canonicalResidue p.2),
        (bumpTest hδ x₀ M).continuous.comp continuous_canonMap⟩, by
        refine HasCompactSupport.intro ((hasCompactSupport_pointBump (x₀ := x₀) hδ).isCompact.prod
          (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ)
            (Real.sqrt (Real.pi * (M + 1))))) fun p hp => ?_
        simp only [bumpTest_apply]
        rw [Set.mem_prod, not_and_or] at hp
        rcases hp with hp | hp
        · rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
        · refine mul_eq_zero_of_right _ (matCutoff_eq_zero ?_)
          simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall,
            dist_zero_right, not_forall, not_le] at hp
          obtain ⟨i, hi⟩ := hp
          have h1 := norm_sq_le_matNorm_canonicalResidue p.2 i
          have hpi := Real.pi_pos
          by_contra hlt
          push Not at hlt
          have h2 : ‖p.2 i‖ ^ 2 ≤ Real.pi * (M + 1) := by nlinarith
          have h3 := Real.sqrt_le_sqrt h2
          rw [Real.sqrt_sq (norm_nonneg _)] at h3
          linarith⟩ with hfdef
    have hf0 : ∀ z, 0 ≤ f z := fun z => bumpTest_nonneg hδ x₀ M _
    obtain ⟨hfi, hfE⟩ := integral_coordinate_of_decoratedSine hΞ f hf0
    have hle : ∀ ω, G (fun _ => ∫ p, bumpTest hδ x₀ M (p.1, canonicalResidue p.2)
        ∂(Ξ ω).measure) ≤ ∫ p, f p ∂(Ξ ω).measure := by
      intro ω
      simp only [G, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
      have h0 : 0 ≤ ∫ p, f p ∂(Ξ ω).measure := integral_nonneg hf0
      exact (min_le_left _ _).trans (max_le le_rfl h0)
    have hGint : Integrable (fun ω => G (fun _ => ∫ p, bumpTest hδ x₀ M (p.1, canonicalResidue p.2)
        ∂(Ξ ω).measure)) P' :=
      (G.integrable (P'.map _)).comp_aemeasurable T.aemeasurable_limit
    calc _ ≤ ∫ ω, ∫ p, f p ∂(Ξ ω).measure ∂P' := integral_mono hGint hfi hle
      _ = ∫ x, ∫ g, f (x, g) ∂circularVectorLaw (Fin r) := hfE
      _ ≤ ∫ x, pointBump δ x₀ x := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x =>
            integral_nonneg fun g => hf0 _) (integrable_pointBump hδ)
            (Eventually.of_forall fun x => ?_)
          calc ∫ g, f (x, g) ∂circularVectorLaw (Fin r)
              ≤ ∫ g, pointBump δ x₀ x ∂circularVectorLaw (Fin r) := by
                refine integral_mono_of_nonneg (Eventually.of_forall fun g => hf0 _)
                  (integrable_const _) (Eventually.of_forall fun g => ?_)
                simp only [hfdef, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
                  bumpTest_apply]
                exact mul_le_of_le_one_right (pointBump_nonneg _ _ _) (matCutoff_le_one _ _)
            _ = pointBump δ x₀ x := by simp
      _ ≤ 4 * δ := integral_pointBump_le hδ
  filter_upwards [hG.eventually (gt_mem_nhds (lt_of_le_of_lt hcan
    (lt_add_of_pos_right _ hη)))] with N hN
  -- Markov on `[0,1]`-valued variable
  set X : Ω N → ℝ := fun ω => G (fun _ => (F N ω).atomSum (bumpTest hδ x₀ M)) with hX
  have hXm : AEMeasurable X (P N) :=
    G.continuous.measurable.comp_aemeasurable (T.forall_aemeasurable N)
  have hXi : Integrable X (P N) :=
    (G.integrable ((P N).map _)).comp_aemeasurable (T.forall_aemeasurable N)
  have hX0 : 0 ≤ᵐ[P N] X := Eventually.of_forall fun ω => by
    simp only [hX, G, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk]
    exact le_min (le_max_right _ _) zero_le_one
  have hsub : {ω | 1 ≤ (F N ω).atomSum (bumpTest hδ x₀ M)} ⊆ {ω | 1 ≤ X ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, hX, G, BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk] at hω ⊢
    rw [max_eq_left (by linarith), min_eq_right hω]
  have hmk := mul_meas_ge_le_integral_of_nonneg hX0 hXi 1
  rw [one_mul] at hmk
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top (P N) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ∫ ω, X ω ∂P N < 4 * δ + η := hN
  exact le_trans hmk this.le

end Hyp2

end BlockBand.Critical.Herglotz
