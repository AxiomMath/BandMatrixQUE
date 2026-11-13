module

public import BlockBand.Critical.Herglotz.JointMetric
public import BlockBand.Critical.Herglotz.SmoothSharp

/-!
# Near parts of marked pole measures: deterministic part

* `atomMeasure F = Σ_x δ_{(x, μ_F({x}))}`; `atomSum_eq_integral` identifies hypothesis 1's
  coordinates with integrals.
* `canonMeasure ξ`, the image of `ξ` under `(x, g) ↦ (x, π⁻¹ g g^*)`; finite on compacts.
* `nearPart ν L z = ∫ χ_L(y) (y - z)⁻¹ ρ dν(y, ρ)` (entrywise; `χ_L = smoothCutoff L`). For
  `atomMeasure F` it is the finite sum `Σ_x χ_L(x) (x - z)⁻¹ μ_F({x})` (`nearPart_atomMeasure`);
  for `canonMeasure ξ` it is `smoothCauchy r ξ L` (`nearPart_canonMeasure`).
* `matNorm ρ = Σ_ij |ρ_ij|`, the residue cutoff `matCutoff M` (`= 1` on `matNorm ≤ M`, `0` on
  `matNorm ≥ M + 1`), `PosSemidef.matNorm_le_trace` (`matNorm ρ ≤ r tr ρ` for `ρ ⪰ 0`), and the
  regularized kernel `regInv δ u` (`= u⁻¹` for `|u| ≥ δ`, `= 0` at `u = 0`).
* `coordMat ν w M = ∫ w(y) ψ_M(ρ) ρ dν` and its real `C_c` tests `coordTest` (hypothesis 1).
* `approxJoint`: real-point values `coordMat ν (χ_L · regInv δ (· - x_a)) M` and the
  interpolant on `K` of `coordMat ν (χ_L · (· - p)⁻¹) M` at the nodes `p`.
* `nearPart_approx` (**deterministic estimate**): if `ν` has no atom at distance in `(0, δ)`
  from the real points, no residue with `matNorm > M` over `|y| < L + 1`, and
  `(h/c²) ∫ χ_L ψ_M matNorm dν ≤ ε` (`h` the interpolation scale, `c ≤ Im z` on `K`), then
  `nearPart ν L` is continuous on `K` and its joint values are `ε`-close to `approxJoint`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix NNReal ENNReal ComplexConjugate ComplexOrder

namespace BlockBand.Critical.Herglotz

open scoped JV
open BlockBand.Internal.Contracts.CriticalEntire

variable {r : ℕ}

instance instMeasurableSingletonClassMatrix :
    MeasurableSingletonClass (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (MeasurableSingletonClass (Fin r → Fin r → ℂ))

/-!
## Matrix size, positivity and cutoffs
-/

/-- Entrywise `ℓ¹` size `Σ_ij |ρ_ij|` of a matrix. -/
def matNorm (ρ : Matrix (Fin r) (Fin r) ℂ) : ℝ := ∑ i, ∑ j, ‖ρ i j‖

theorem matNorm_nonneg (ρ : Matrix (Fin r) (Fin r) ℂ) : 0 ≤ matNorm ρ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem continuous_matrix_apply (i j : Fin r) :
    Continuous fun ρ : Matrix (Fin r) (Fin r) ℂ => ρ i j :=
  (continuous_apply j).comp (continuous_apply i)

theorem continuous_matNorm : Continuous (matNorm (r := r)) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_matrix_apply i j).norm

theorem norm_apply_le_matNorm (ρ : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    ‖ρ i j‖ ≤ matNorm ρ := by
  unfold matNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖ρ i j‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖ρ i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)

theorem re_diag_nonneg {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (i : Fin r) :
    0 ≤ (A i i).re := by
  have := hA.diag_nonneg (i := i)
  exact (Complex.nonneg_iff.1 this).1

theorem norm_diag_eq {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (i : Fin r) :
    ‖A i i‖ = (A i i).re := by
  have h := Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
  have : A i i = ((A i i).re : ℂ) := Complex.ext (by simp) (by simp [← h.2])
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
  simp

/-- **Off-diagonal entries of a positive semidefinite matrix**: `2|A_ij| ≤ A_ii + A_jj`. -/
theorem PosSemidef.two_mul_norm_apply_le {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef)
    (i j : Fin r) : 2 * ‖A i j‖ ≤ (A i i).re + (A j j).re := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [norm_diag_eq hA]
    linarith
  set a := A i j with ha
  by_cases ha0 : a = 0
  · rw [ha0, norm_zero, mul_zero]
    exact add_nonneg (re_diag_nonneg hA i) (re_diag_nonneg hA j)
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  set v : Fin r → ℂ := Pi.single i (‖a‖ : ℂ) + Pi.single j (-(conj a)) with hv
  have hnn := hA.dotProduct_mulVec_nonneg v
  have hji : A j i = conj a := by
    have := hA.isHermitian.apply j i
    rw [← this, ha]
    rfl
  have hcomp : star v ⬝ᵥ (A *ᵥ v) =
      ((‖a‖ ^ 2 * ((A i i).re + (A j j).re) - 2 * ‖a‖ ^ 3 : ℝ) : ℂ) := by
    have hii : A i i = ((A i i).re : ℂ) := by
      have h := Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
      exact Complex.ext (by simp) (by simp [← h.2])
    have hjj : A j j = ((A j j).re : ℂ) := by
      have h := Complex.nonneg_iff.1 (hA.diag_nonneg (i := j))
      exact Complex.ext (by simp) (by simp [← h.2])
    have hstar : star v = Pi.single i (‖a‖ : ℂ) + Pi.single j (-a) := by
      rw [hv, star_add]
      congr 1
      · ext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
    have hmv : ∀ (l : Fin r) (y : ℂ) (k : Fin r), (A *ᵥ Pi.single l y) k = A k l * y := by
      intro l y k
      simp [Matrix.mulVec, dotProduct_single]
    rw [hstar, hv]
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct,
      hmv]
    rw [← ha, hji, hii, hjj]
    have hn : (‖a‖ : ℂ) ^ 2 = a * conj a := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    push_cast
    linear_combination (2 * (‖a‖ : ℂ) - ((A j j).re : ℂ)) * hn
  rw [hcomp] at hnn
  have hre := Complex.nonneg_iff.1 hnn
  simp only [Complex.ofReal_re] at hre
  have h1 := hre.1
  have h2 : ‖a‖ ^ 2 * (2 * ‖a‖) ≤ ‖a‖ ^ 2 * ((A i i).re + (A j j).re) := by nlinarith
  exact le_of_mul_le_mul_left h2 (by positivity)

/-- `matNorm ρ ≤ r tr ρ` for `ρ ⪰ 0`. -/
theorem PosSemidef.matNorm_le_trace {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) :
    matNorm A ≤ r * (Matrix.trace A).re := by
  unfold matNorm
  have h : ∀ i j, ‖A i j‖ ≤ ((A i i).re + (A j j).re) / 2 := fun i j => by
    have := PosSemidef.two_mul_norm_apply_le hA i j; linarith
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ i : Fin r, ∑ j : Fin r, ((A i i).re + (A j j).re) / 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = r * (Matrix.trace A).re := by
        rw [Matrix.trace, Complex.re_sum]
        simp only [Matrix.diag_apply, add_div, Finset.sum_add_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div,
          ← Finset.mul_sum]
        ring

/-- Residue cutoff `ψ_M(ρ) = max 0 (min 1 (M + 1 - matNorm ρ))`. -/
def matCutoff (M : ℝ) (ρ : Matrix (Fin r) (Fin r) ℂ) : ℝ := max 0 (min 1 (M + 1 - matNorm ρ))

theorem matCutoff_nonneg (M : ℝ) (ρ : Matrix (Fin r) (Fin r) ℂ) : 0 ≤ matCutoff M ρ :=
  le_max_left _ _

theorem matCutoff_le_one (M : ℝ) (ρ : Matrix (Fin r) (Fin r) ℂ) : matCutoff M ρ ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_matCutoff (M : ℝ) : Continuous (matCutoff (r := r) M) := by
  unfold matCutoff
  exact continuous_const.max (continuous_const.min (continuous_const.sub continuous_matNorm))

theorem matCutoff_eq_one {M : ℝ} {ρ : Matrix (Fin r) (Fin r) ℂ} (h : matNorm ρ ≤ M) :
    matCutoff M ρ = 1 := by
  unfold matCutoff
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem matCutoff_eq_zero {M : ℝ} {ρ : Matrix (Fin r) (Fin r) ℂ} (h : M + 1 ≤ matNorm ρ) :
    matCutoff M ρ = 0 := by
  unfold matCutoff
  exact max_eq_left (min_le_of_right_le (by linarith))

theorem isCompact_matNorm_le (R : ℝ) :
    IsCompact {ρ : Matrix (Fin r) (Fin r) ℂ | matNorm ρ ≤ R} := by
  have hpi : IsCompact ((Set.pi univ fun _ : Fin r => Set.pi univ fun _ : Fin r =>
      Metric.closedBall (0 : ℂ) R) : Set (Matrix (Fin r) (Fin r) ℂ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hpi.of_isClosed_subset (isClosed_le continuous_matNorm continuous_const) ?_
  intro ρ hρ
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact (norm_apply_le_matNorm ρ i j).trans hρ

/-- Support of `ψ_M`: `ψ_M ρ ≠ 0 → matNorm ρ < M + 1`. -/
theorem matNorm_lt_of_matCutoff_ne {M : ℝ} {ρ : Matrix (Fin r) (Fin r) ℂ}
    (h : matCutoff M ρ ≠ 0) : matNorm ρ < M + 1 := by
  by_contra h'
  exact h (matCutoff_eq_zero (not_lt.1 h'))

/-!
## The regularized kernel
-/

/-- `regInv δ u = u / max(δ², u²)`: continuous, `= u⁻¹` for `|u| ≥ δ`, `= 0` at `u = 0`. -/
def regInv (δ u : ℝ) : ℝ := u / max (δ ^ 2) (u ^ 2)

theorem continuous_regInv {δ : ℝ} (hδ : 0 < δ) : Continuous (regInv δ) := by
  unfold regInv
  refine continuous_id.div (continuous_const.max (continuous_pow 2)) fun u => ?_
  exact (lt_of_lt_of_le (by positivity) (le_max_left _ _)).ne'

theorem regInv_eq_inv {δ u : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ |u|) : regInv δ u = u⁻¹ := by
  unfold regInv
  have h2 : δ ^ 2 ≤ u ^ 2 := by
    rw [← sq_abs u]; exact pow_le_pow_left₀ hδ h 2
  rw [max_eq_right h2]
  by_cases hu : u = 0
  · simp [hu]
  · field_simp

theorem regInv_zero (δ : ℝ) : regInv δ 0 = 0 := by simp [regInv]

/-!
## Pole measures
-/

/-- The marked pole measure `Σ_x δ_{(x, μ_F({x}))}` of an atomic Herglotz function. -/
def atomMeasure (F : AtomicHerglotz r) : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ) :=
  ∑ x ∈ F.residue.support, Measure.dirac (x, F.residue x)

instance (F : AtomicHerglotz r) : IsFiniteMeasure (atomMeasure F) := by
  unfold atomMeasure; infer_instance

theorem integral_atomMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : AtomicHerglotz r) (f : ℝ × Matrix (Fin r) (Fin r) ℂ → E) :
    ∫ p, f p ∂atomMeasure F = ∑ x ∈ F.residue.support, f (x, F.residue x) := by
  unfold atomMeasure
  rw [integral_finsetSum_measure fun x _ => integrable_dirac enorm_lt_top]
  exact Finset.sum_congr rfl fun x _ => integral_dirac f (x, F.residue x)

theorem lintegral_atomMeasure (F : AtomicHerglotz r)
    (f : ℝ × Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞) :
    ∫⁻ p, f p ∂atomMeasure F = ∑ x ∈ F.residue.support, f (x, F.residue x) := by
  unfold atomMeasure
  rw [lintegral_finsetSum_measure]
  simp_rw [lintegral_dirac]

/-- A set avoiding every marked pole is `atomMeasure`-null. -/
theorem atomMeasure_eq_zero (F : AtomicHerglotz r) {s : Set (ℝ × Matrix (Fin r) (Fin r) ℂ)}
    (h : ∀ x ∈ F.residue.support, (x, F.residue x) ∉ s) : atomMeasure F s = 0 := by
  unfold atomMeasure
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Measure.dirac_apply, Set.indicator_of_notMem (h x hx)]

/-- Hypothesis 1's coordinates are integrals against `atomMeasure`. -/
theorem atomSum_eq_integral (F : AtomicHerglotz r)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    F.atomSum f = ∫ p, f p ∂atomMeasure F := by
  rw [integral_atomMeasure]; rfl

theorem continuous_canonicalResidue : Continuous (canonicalResidue (r := r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun g : Fin r → ℂ => canonicalResidue g i j) =
      fun g => (Real.pi : ℂ)⁻¹ * (g i * conj (g j)) := by
    funext g; simp [canonicalResidue, Matrix.vecMulVec_apply]
  rw [this]
  exact continuous_const.mul ((continuous_apply i).mul (Complex.continuous_conj.comp
    (continuous_apply j)))

theorem canonicalResidue_apply (g : Fin r → ℂ) (i j : Fin r) :
    canonicalResidue g i j = (Real.pi : ℂ)⁻¹ * (g i * conj (g j)) := by
  simp [canonicalResidue, Matrix.vecMulVec_apply]

/-- `‖g_i‖² ≤ π matNorm(π⁻¹ g g^*)`. -/
theorem norm_sq_le_matNorm_canonicalResidue (g : Fin r → ℂ) (i : Fin r) :
    ‖g i‖ ^ 2 ≤ Real.pi * matNorm (canonicalResidue g) := by
  have h := norm_apply_le_matNorm (canonicalResidue g) i i
  rw [canonicalResidue_apply, norm_mul, norm_mul, Complex.norm_conj, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h
  have hpi := Real.pi_pos
  rw [inv_mul_le_iff₀ hpi] at h
  nlinarith

/-- The canonical marked pole measure: the image of `ξ` under `(x, g) ↦ (x, π⁻¹ g g^*)`. -/
def canonMeasure (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) :
    Measure (ℝ × Matrix (Fin r) (Fin r) ℂ) :=
  ξ.measure.map fun p => (p.1, canonicalResidue p.2)

theorem continuous_canonMap :
    Continuous fun p : ℝ × (Fin r → ℂ) => (p.1, canonicalResidue p.2) :=
  continuous_fst.prodMk (continuous_canonicalResidue.comp continuous_snd)

instance (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) :
    IsFiniteMeasureOnCompacts (canonMeasure ξ) := by
  refine ⟨fun S hS => ?_⟩
  unfold canonMeasure
  rw [Measure.map_apply continuous_canonMap.measurable hS.isClosed.measurableSet]
  obtain ⟨R, hR⟩ := (hS.image continuous_snd).isBounded.exists_norm_le
  have hbd : ∃ B, ∀ q ∈ S, matNorm q.2 ≤ B := by
    obtain ⟨B, hB⟩ := (hS.image (continuous_matNorm.comp continuous_snd)).bddAbove
    exact ⟨B, fun q hq => hB ⟨q, hq, rfl⟩⟩
  obtain ⟨B, hB⟩ := hbd
  set T : Set (ℝ × (Fin r → ℂ)) := (Prod.fst '' S) ×ˢ
    (Set.pi univ fun _ : Fin r => Metric.closedBall (0 : ℂ) (Real.sqrt (Real.pi * B)))
  have hT : IsCompact T :=
    (hS.image continuous_fst).prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  refine lt_of_le_of_lt (measure_mono ?_) (ξ.finite_on_compact T hT)
  intro p hp
  refine ⟨⟨_, hp, rfl⟩, ?_⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i
  have h1 := norm_sq_le_matNorm_canonicalResidue p.2 i
  have h2 := hB _ hp
  refine Real.le_sqrt_of_sq_le ?_
  have := Real.pi_pos
  nlinarith

theorem integral_canonMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) {f : ℝ × Matrix (Fin r) (Fin r) ℂ → E}
    (hf : AEStronglyMeasurable f (canonMeasure ξ)) :
    ∫ p, f p ∂canonMeasure ξ = ∫ p, f (p.1, canonicalResidue p.2) ∂ξ.measure :=
  integral_map continuous_canonMap.aemeasurable hf

theorem lintegral_canonMeasure (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ)))
    {f : ℝ × Matrix (Fin r) (Fin r) ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂canonMeasure ξ = ∫⁻ p, f (p.1, canonicalResidue p.2) ∂ξ.measure :=
  lintegral_map hf continuous_canonMap.measurable

/-!
## Near parts, coordinates and the approximant
-/

/-- `nearPart ν L z = ∫ χ_L(y) (y - z)⁻¹ ρ dν(y, ρ)`, entrywise (Lean's `0⁻¹ = 0`). -/
def nearPart (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) (L : ℝ) (z : ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ∫ p, ((smoothCutoff L p.1 : ℝ) : ℂ) * (((p.1 : ℂ) - z)⁻¹ * p.2 i j) ∂ν

theorem nearPart_atomMeasure (F : AtomicHerglotz r) (L : ℝ) (z : ℂ) (i j : Fin r) :
    nearPart (atomMeasure F) L z i j = ∑ x ∈ F.residue.support,
      ((smoothCutoff L x : ℝ) : ℂ) * (((x : ℂ) - z)⁻¹ * F.residue x i j) :=
  integral_atomMeasure F _

/-- On the canonical pole measure the near part is the smooth cutoff `smoothCauchy`. -/
theorem nearPart_canonMeasure (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (L : ℝ) (z : ℂ) :
    nearPart (canonMeasure ξ) L z = smoothCauchy r ξ L z := by
  funext i j
  unfold nearPart smoothCauchy
  rw [integral_canonMeasure]
  · congr 1
    funext p
    dsimp only
    rw [canonicalResidue_apply, mul_inv]
    ring
  · have h1 : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
        ((smoothCutoff L p.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((continuous_smoothCutoff L).measurable.comp measurable_fst)
    have h2 : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => ((p.1 : ℂ) - z)⁻¹ :=
      ((Complex.measurable_ofReal.comp measurable_fst).sub measurable_const).inv
    have h3 : Measurable fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => p.2 i j :=
      (continuous_matrix_apply i j).measurable.comp measurable_snd
    exact (h1.mul (h2.mul h3)).aestronglyMeasurable

/-- `coordMat ν w M = ∫ w(y) ψ_M(ρ) ρ dν(y, ρ)`, entrywise. -/
def coordMat (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) (w : ℝ → ℂ) (M : ℝ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j => ∫ p, w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j) ∂ν

theorem continuous_coordIntegrand {w : ℝ → ℂ} (hw : Continuous w) (M : ℝ) (i j : Fin r) :
    Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j) :=
  (hw.comp continuous_fst).mul ((Complex.continuous_ofReal.comp
    ((continuous_matCutoff M).comp continuous_snd)).mul
    ((continuous_matrix_apply i j).comp continuous_snd))

theorem hasCompactSupport_coordIntegrand {w : ℝ → ℂ} (hwc : HasCompactSupport w) (M : ℝ)
    (i j : Fin r) :
    HasCompactSupport fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j) := by
  refine HasCompactSupport.intro (hwc.isCompact.prod (isCompact_matNorm_le (M + 1)))
    fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · have : M + 1 ≤ matNorm p.2 := le_of_lt (not_le.1 h)
    rw [matCutoff_eq_zero this]
    simp

/-- Real `C_c` tests on `ℝ × Matrix` whose integrals are the real (`b = true`) and imaginary
(`b = false`) parts of `coordMat ν w M i j`. -/
def coordTest {w : ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) (M : ℝ)
    (i j : Fin r) (b : Bool) : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ
    where
  toFun p := if b then (w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j)).re
    else (w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j)).im
  continuous_toFun := by
    cases b
    · exact Complex.continuous_im.comp (continuous_coordIntegrand hw M i j)
    · exact Complex.continuous_re.comp (continuous_coordIntegrand hw M i j)
  hasCompactSupport' := by
    cases b
    · exact (hasCompactSupport_coordIntegrand hwc M i j).comp_left Complex.zero_im
    · exact (hasCompactSupport_coordIntegrand hwc M i j).comp_left Complex.zero_re

theorem coordTest_apply {w : ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) (M : ℝ)
    (i j : Fin r) (b : Bool) (p : ℝ × Matrix (Fin r) (Fin r) ℂ) :
    coordTest hw hwc M i j b p = if b then (w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j)).re
      else (w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j)).im := rfl

theorem integrable_coordIntegrand (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ))
    [IsFiniteMeasureOnCompacts ν] {w : ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (M : ℝ) (i j : Fin r) :
    Integrable (fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      w p.1 * (((matCutoff M p.2 : ℝ) : ℂ) * p.2 i j)) ν :=
  (continuous_coordIntegrand hw M i j).integrable_of_hasCompactSupport
    (hasCompactSupport_coordIntegrand hwc M i j)

/-- `coordMat` from the real coordinates of its tests. -/
theorem coordMat_eq (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) [IsFiniteMeasureOnCompacts ν]
    {w : ℝ → ℂ} (hw : Continuous w) (hwc : HasCompactSupport w) (M : ℝ) (i j : Fin r) :
    coordMat ν w M i j = ((∫ p, coordTest hw hwc M i j true p ∂ν : ℝ) : ℂ) +
      ((∫ p, coordTest hw hwc M i j false p ∂ν : ℝ) : ℂ) * Complex.I := by
  have hi := integrable_coordIntegrand ν hw hwc M i j
  simp only [coordTest_apply, ite_true, Bool.false_eq_true, ite_false]
  have h1 := integral_re hi
  have h2 := integral_im hi
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at h1 h2
  rw [h1, h2, Complex.re_add_im]
  rfl

/-- Weight at a real point: `χ_L(y) regInv δ (y - x₀)`. -/
def realWeight (L δ x₀ : ℝ) (y : ℝ) : ℂ := ((smoothCutoff L y * regInv δ (y - x₀) : ℝ) : ℂ)

theorem continuous_realWeight (L : ℝ) {δ : ℝ} (hδ : 0 < δ) (x₀ : ℝ) :
    Continuous (realWeight L δ x₀) :=
  Complex.continuous_ofReal.comp ((continuous_smoothCutoff L).mul
    ((continuous_regInv hδ).comp (continuous_id.sub continuous_const)))

theorem hasCompactSupport_realWeight (L δ x₀ : ℝ) : HasCompactSupport (realWeight L δ x₀) := by
  have : HasCompactSupport fun y => smoothCutoff L y * regInv δ (y - x₀) :=
    (hasCompactSupport_smoothCutoff L).mul_right
  exact this.comp_left Complex.ofReal_zero

/-- Weight at an interpolation node `p` (`Im p ≠ 0`): `χ_L(y) (y - p)⁻¹`. -/
def nodeWeight (L : ℝ) (p : ℂ) (y : ℝ) : ℂ := ((smoothCutoff L y : ℝ) : ℂ) * ((y : ℂ) - p)⁻¹

theorem ofReal_sub_ne_zero {y : ℝ} {p : ℂ} (hp : p.im ≠ 0) : (y : ℂ) - p ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hp (by linarith)

theorem continuous_nodeWeight (L : ℝ) {p : ℂ} (hp : p.im ≠ 0) : Continuous (nodeWeight L p) :=
  (Complex.continuous_ofReal.comp (continuous_smoothCutoff L)).mul
    ((Complex.continuous_ofReal.sub continuous_const).inv₀ fun _ => ofReal_sub_ne_zero hp)

theorem hasCompactSupport_nodeWeight (L : ℝ) (p : ℂ) : HasCompactSupport (nodeWeight L p) :=
  ((hasCompactSupport_smoothCutoff L).comp_left Complex.ofReal_zero).mul_right

/-- The approximant of the joint values of `nearPart ν L`: values `coordMat` with real-point
weights at `x a`, and the interpolant on `K` of the node coordinates. -/
def approxJoint (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ)) {k : ℕ} (x : Fin k → ℝ)
    {K : Set ℂ} {h : ℝ} (I : CompactInterp K h) (L δ M : ℝ) : JointValues r k K :=
  ((fun a => coordMat ν (realWeight L δ (x a)) M), I.interp fun p => coordMat ν (nodeWeight L p) M)

theorem norm_inv_ofReal_sub_le {y : ℝ} {z : ℂ} {c : ℝ} (hc : 0 < c) (hz : c ≤ z.im) :
    ‖((y : ℂ) - z)⁻¹‖ ≤ 1 / c := by
  have h1 : c ≤ ‖(y : ℂ) - z‖ := by
    refine le_trans ?_ (Complex.abs_im_le_norm _)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg]
    exact le_trans hz (le_abs_self _)
  rw [norm_inv, one_div]
  exact inv_anti₀ hc h1

theorem norm_inv_sub_inv_le_of_im {y : ℝ} {z p : ℂ} {c : ℝ} (hc : 0 < c) (hz : c ≤ z.im)
    (hp : c ≤ p.im) : ‖((y : ℂ) - p)⁻¹ - ((y : ℂ) - z)⁻¹‖ ≤ ‖z - p‖ / c ^ 2 := by
  have hz0 : (y : ℂ) - z ≠ 0 := ofReal_sub_ne_zero (by linarith)
  have hp0 : (y : ℂ) - p ≠ 0 := ofReal_sub_ne_zero (by linarith)
  have hid : ((y : ℂ) - p)⁻¹ - ((y : ℂ) - z)⁻¹ = ((y : ℂ) - p)⁻¹ * ((y : ℂ) - z)⁻¹ * (p - z) := by
    field_simp
    ring
  rw [hid, norm_mul, norm_mul, norm_sub_rev p z]
  have h1 := norm_inv_ofReal_sub_le (y := y) hc hp
  have h2 := norm_inv_ofReal_sub_le (y := y) hc hz
  calc ‖((y : ℂ) - p)⁻¹‖ * ‖((y : ℂ) - z)⁻¹‖ * ‖z - p‖ ≤ (1 / c) * (1 / c) * ‖z - p‖ := by
        gcongr
    _ = ‖z - p‖ / c ^ 2 := by field_simp

theorem hasCompactSupport_cutoffs (L M : ℝ) :
    HasCompactSupport fun p : ℝ × Matrix (Fin r) (Fin r) ℂ =>
      smoothCutoff L p.1 * matCutoff M p.2 := by
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ) (L + 1)).prod
    (isCompact_matNorm_le (M + 1))) fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at h
    rw [smoothCutoff_eq_zero h.le, zero_mul]
  · rw [matCutoff_eq_zero (le_of_lt (not_le.1 h)), mul_zero]

theorem continuous_cutoffs (L M : ℝ) :
    Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => smoothCutoff L p.1 * matCutoff M p.2 :=
  ((continuous_smoothCutoff L).comp continuous_fst).mul
    ((continuous_matCutoff M).comp continuous_snd)

/-- **Deterministic near-part estimate.** Measure: any `ν` on `ℝ × Matrix` finite on compacts.
Parameters: `δ > 0`, `c > 0` with `c ≤ Im z` on the compact `K`, interpolation data `I` on `K` at
scale `h`, cutoffs `χ_L` (location) and `ψ_M` (residue). Hypotheses: (i) for every `a`, no
`ν`-mass at distance in `(0, δ)` from `x a`; (ii) no `ν`-mass on `{|y| < L + 1, matNorm ρ > M}`;
(iii) `(h/c²) ∫ χ_L ψ_M matNorm dν ≤ ε`. Conclusion: `nearPart ν L` is continuous on `K` and
`dist (jointValues (nearPart ν L) x K) (approxJoint ν x I L δ M) ≤ ε` (max of the entrywise sup
over real points and over `K`). The real-point values agree exactly. -/
theorem nearPart_approx (ν : Measure (ℝ × Matrix (Fin r) (Fin r) ℂ))
    [IsFiniteMeasureOnCompacts ν] {L δ M c h ε : ℝ} (hδ : 0 < δ) (hc : 0 < c) {k : ℕ}
    (x : Fin k → ℝ) {K : Set ℂ} [CompactSpace K] (hKc : ∀ z ∈ K, c ≤ z.im)
    (I : CompactInterp K h)
    (hi : ∀ a, ν {p | 0 < |p.1 - x a| ∧ |p.1 - x a| < δ} = 0)
    (hii : ν {p | |p.1| < L + 1 ∧ M < matNorm p.2} = 0) (hε : 0 ≤ ε)
    (hiii : h / c ^ 2 * ∫ p, smoothCutoff L p.1 * matCutoff M p.2 * matNorm p.2 ∂ν ≤ ε) :
    ContinuousOn (nearPart ν L) K ∧
      dist (jointValues (nearPart ν L) x K) (approxJoint ν x I L δ M) ≤ ε := by
  set χψ : ℝ × Matrix (Fin r) (Fin r) ℂ → ℂ :=
    fun p => ((smoothCutoff L p.1 * matCutoff M p.2 : ℝ) : ℂ) with hχψ
  have hae : ∀ᵐ p ∂ν, χψ p = ((smoothCutoff L p.1 : ℝ) : ℂ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hii] with p hp
    by_cases h1 : |p.1| < L + 1
    · have : matNorm p.2 ≤ M := by
        by_contra h2
        exact hp ⟨h1, lt_of_not_ge h2⟩
      simp [hχψ, matCutoff_eq_one this]
    · simp [hχψ, smoothCutoff_eq_zero (not_lt.1 h1)]
  have hχψc : Continuous χψ := Complex.continuous_ofReal.comp (continuous_cutoffs L M)
  have hint : ∀ g : ℝ × Matrix (Fin r) (Fin r) ℂ → ℂ, Continuous g →
      Integrable (fun p => χψ p * g p) ν := by
    intro g hg
    refine (hχψc.mul hg).integrable_of_hasCompactSupport ?_
    exact ((hasCompactSupport_cutoffs L M).comp_left Complex.ofReal_zero).mul_right
  have hnear : ∀ z i j, nearPart ν L z i j = ∫ p, χψ p * (((p.1 : ℂ) - z)⁻¹ * p.2 i j) ∂ν := by
    intro z i j
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp]
  have hentry : ∀ i j : Fin r, Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => p.2 i j :=
    fun i j => (continuous_matrix_apply i j).comp continuous_snd
  have hcz : ∀ z : ℂ, z.im ≠ 0 →
      Continuous fun p : ℝ × Matrix (Fin r) (Fin r) ℂ => ((p.1 : ℂ) - z)⁻¹ := fun z hz =>
    ((Complex.continuous_ofReal.comp continuous_fst).sub continuous_const).inv₀
      fun _ => ofReal_sub_ne_zero hz
  have hKne : ∀ z ∈ K, z.im ≠ 0 := fun z hz => (lt_of_lt_of_le hc (hKc z hz)).ne'
  have hcont : ContinuousOn (nearPart ν L) K := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    have heq : (fun z => nearPart ν L z i j) =
        fun z => ∫ p, χψ p * (((p.1 : ℂ) - z)⁻¹ * p.2 i j) ∂ν := funext fun z => hnear z i j
    show ContinuousOn (fun z => nearPart ν L z i j) K
    rw [heq]
    have hbint : Integrable (fun p => ‖χψ p * (((1 / c * matNorm p.2 : ℝ)) : ℂ)‖) ν :=
      (hint _ (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_matNorm.comp continuous_snd)))).norm
    refine continuousOn_of_dominated
      (bound := fun p => ‖χψ p * (((1 / c * matNorm p.2 : ℝ)) : ℂ)‖) ?_ ?_ hbint ?_
    · intro z hz
      exact (hint _ ((hcz z (hKne z hz)).mul (hentry i j))).aestronglyMeasurable
    · intro z hz
      refine ae_of_all _ fun p => ?_
      have hm := matNorm_nonneg p.2
      have h1 := norm_inv_ofReal_sub_le (y := p.1) hc (hKc z hz)
      have h2 := norm_apply_le_matNorm p.2 i j
      have h3 : ‖(((1 / c * matNorm p.2 : ℝ)) : ℂ)‖ = 1 / c * matNorm p.2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [norm_mul, norm_mul, norm_mul (χψ p), h3]
      exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
        (norm_nonneg _)
    · refine ae_of_all _ fun p => ?_
      refine continuousOn_const.mul (ContinuousOn.mul ?_ continuousOn_const)
      exact (continuousOn_const.sub continuousOn_id).inv₀ fun z hz => ofReal_sub_ne_zero
        (hKne z hz)
  refine ⟨hcont, ?_⟩
  change max (dist (fun a => nearPart ν L (x a)) (fun a => coordMat ν (realWeight L δ (x a)) M))
    (dist (restrictTo (nearPart ν L) K)
      (I.interp fun p => coordMat ν (nodeWeight L p) M)) ≤ ε
  refine max_le ?_ ?_
  · refine (dist_pi_le_iff hε).2 fun a => (matrix_dist_le_iff hε).2 fun i j => ?_
    have heq : nearPart ν L (x a) i j = coordMat ν (realWeight L δ (x a)) M i j := by
      rw [hnear]
      unfold coordMat
      refine integral_congr_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hi a)] with p hp
      have hk : ((p.1 : ℂ) - (x a : ℂ))⁻¹ = ((regInv δ (p.1 - x a) : ℝ) : ℂ) := by
        by_cases h0 : p.1 - x a = 0
        · have : (p.1 : ℂ) - (x a : ℂ) = 0 := by
            rw [← Complex.ofReal_sub, h0, Complex.ofReal_zero]
          rw [this, h0, regInv_zero, inv_zero, Complex.ofReal_zero]
        · have hle : δ ≤ |p.1 - x a| := not_lt.1 fun hlt => hp ⟨abs_pos.2 h0, hlt⟩
          rw [regInv_eq_inv hδ.le hle, Complex.ofReal_inv, Complex.ofReal_sub]
      simp only [hχψ, realWeight, hk]
      push_cast
      ring
    rw [heq, sub_self, norm_zero]
    exact hε
  · refine (ContinuousMap.dist_le hε).2 fun z => ?_
    rw [restrictTo_apply hcont]
    refine (matrix_dist_le_iff hε).2 fun i j => ?_
    rw [← norm_neg, neg_sub]
    refine I.norm_interp_sub_le _ z _ i j fun p hp => ?_
    have hpK : c ≤ (p : ℂ).im := hKc p (I.pts_mem p p.2)
    have hzK : c ≤ (z : ℂ).im := hKc z z.2
    rw [hnear]
    unfold coordMat
    have hw : ∀ q : ℝ × Matrix (Fin r) (Fin r) ℂ,
        nodeWeight L p q.1 * (((matCutoff M q.2 : ℝ) : ℂ) * q.2 i j) =
          χψ q * (((q.1 : ℂ) - p)⁻¹ * q.2 i j) := by
      intro q
      simp only [nodeWeight, hχψ]
      push_cast
      ring
    simp_rw [hw]
    have hp0 : (p : ℂ).im ≠ 0 := (lt_of_lt_of_le hc hpK).ne'
    have hz0 : (z : ℂ).im ≠ 0 := (lt_of_lt_of_le hc hzK).ne'
    have hI1 : Integrable (fun q : ℝ × Matrix (Fin r) (Fin r) ℂ =>
        χψ q * (((q.1 : ℂ) - p)⁻¹ * q.2 i j)) ν := hint _ ((hcz p hp0).mul (hentry i j))
    have hI2 : Integrable (fun q : ℝ × Matrix (Fin r) (Fin r) ℂ =>
        χψ q * (((q.1 : ℂ) - z)⁻¹ * q.2 i j)) ν := hint _ ((hcz z hz0).mul (hentry i j))
    rw [← integral_sub hI1 hI2]
    have hbint : Integrable (fun q : ℝ × Matrix (Fin r) (Fin r) ℂ =>
        h / c ^ 2 * (smoothCutoff L q.1 * matCutoff M q.2 * matNorm q.2)) ν := by
      refine Integrable.const_mul ?_ _
      refine ((continuous_cutoffs L M).mul (continuous_matNorm.comp continuous_snd))
        |>.integrable_of_hasCompactSupport ?_
      exact (hasCompactSupport_cutoffs L M).mul_right
    refine le_trans (norm_integral_le_of_norm_le hbint (ae_of_all _ fun q => ?_)) ?_
    · have hcalc : χψ q * (((q.1 : ℂ) - p)⁻¹ * q.2 i j) - χψ q * (((q.1 : ℂ) - z)⁻¹ * q.2 i j) =
          χψ q * ((((q.1 : ℂ) - p)⁻¹ - ((q.1 : ℂ) - z)⁻¹) * q.2 i j) := by ring
      rw [hcalc, norm_mul, norm_mul, hχψ]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hnn : 0 ≤ smoothCutoff L q.1 * matCutoff M q.2 :=
        mul_nonneg (smoothCutoff_nonneg _ _) (matCutoff_nonneg _ _)
      rw [abs_of_nonneg hnn]
      have hk := norm_inv_sub_inv_le_of_im (y := q.1) hc hzK hpK
      have hzp : ‖(z : ℂ) - p‖ ≤ h := by
        have := hp; rw [dist_eq_norm] at this; exact this.le
      have hk' : ‖((q.1 : ℂ) - p)⁻¹ - ((q.1 : ℂ) - z)⁻¹‖ ≤ h / c ^ 2 :=
        hk.trans (div_le_div_of_nonneg_right hzp (by positivity))
      calc smoothCutoff L q.1 * matCutoff M q.2 *
            (‖((q.1 : ℂ) - p)⁻¹ - ((q.1 : ℂ) - z)⁻¹‖ * ‖q.2 i j‖)
          ≤ smoothCutoff L q.1 * matCutoff M q.2 * (h / c ^ 2 * matNorm q.2) := by
            gcongr
            · exact le_trans (norm_nonneg _) hk'
            · exact norm_apply_le_matNorm _ i j
        _ = h / c ^ 2 * (smoothCutoff L q.1 * matCutoff M q.2 * matNorm q.2) := by ring
    · rw [integral_const_mul]
      exact hiii

end BlockBand.Critical.Herglotz
