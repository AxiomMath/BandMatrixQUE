module

public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RF.Defs
public import BlockBand.SourceProcess.Stochastic.RotationFlow.Unique

/-!
# `L²` stability of rotation flows in their coefficients

*Setting.* `Ω = DriverSample S ((Fin N × Fin N) × Fin 2)` with `P = driverLaw μ`; matrices carry
the Frobenius norm. Two rotation flows (`IsRotationFlow`) `M`, `M'` with the same start `s` and
window `[a, c]` (`a ≤ c`), with `Admissible` coefficients `(r, κ)`, `(r', κ')` such that on `[a, c]`

* all rates and dampings are `≤ R` (`0 ≤ R`);
* `|√r − √r'| ≤ ε` and `|κ − κ'| ≤ ε`.

Only the clamped times `clampTime a c (s + t) ∈ [a, c]` enter the coefficients.

**Result** (`integral_norm_sub_sq_le_of_isRotationFlow`, and the `ℝ≥0∞` form
`lintegral_enorm_sub_sq_le_of_isRotationFlow`): for every `t ≥ 0`,
`∫ ‖M_t − M'_t‖² dP ≤ stabConst N R t · ε²`, with the explicit constant
`stabConst N R t = 8N²(t + 2N²) (stabPert N R)² N t · exp(8N²(t + 2N²) (stabLip N R)² t)`,
monotone in `t` (`stabConst_mono`). No hypothesis beyond the statement is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.SourceProcess.Stochastic.Integral
open BlockBand.SourceProcess.Stochastic.RotationFlow BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.Internal.Contracts.TransmissionFlow

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace

variable {N : ℕ}

/-- Integral Grönwall inequality in `ℝ≥0∞` form. -/
theorem toReal_le_of_lintegral_gronwall {Ψ : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 ≤ T)
    (hΨm : AEMeasurable Ψ (volume.restrict (Ioc 0 T))) {M : ℝ≥0∞} (hM : M ≠ ⊤) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hbd : ∀ t ∈ Icc 0 T, Ψ t ≤ M)
    (hle : ∀ t ∈ Icc 0 T, Ψ t ≤ ENNReal.ofReal A + ENNReal.ofReal L * ∫⁻ s in Ioc 0 t, Ψ s) :
    ∀ t ∈ Icc 0 T, (Ψ t).toReal ≤ A * Real.exp (L * t) := by
  have hfin : ∀ t ∈ Icc 0 T, Ψ t ≠ ⊤ := fun t ht => ne_top_of_le_ne_top hM (hbd t ht)
  have hint_fin : ∀ t ∈ Icc 0 T, ∫⁻ s in Ioc 0 t, Ψ s ≠ ⊤ := by
    intro t ht
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (ENNReal.ofReal_ne_top (r := t))) ?_
    calc ∫⁻ s in Ioc 0 t, Ψ s ≤ ∫⁻ _ in Ioc 0 t, M :=
          setLIntegral_mono' measurableSet_Ioc fun s hs =>
            hbd s ⟨hs.1.le, hs.2.trans ht.2⟩
      _ = M * ENNReal.ofReal t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hmeas : ∀ t ∈ Icc 0 T, AEMeasurable Ψ (volume.restrict (Ioc 0 t)) := fun t ht =>
    hΨm.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl)
  have hreal : ∀ t ∈ Icc 0 T,
      ∫ s in (0 : ℝ)..t, (Ψ s).toReal = (∫⁻ s in Ioc 0 t, Ψ s).toReal := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht.1]
    refine integral_toReal (hmeas t ht) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact lt_top_iff_ne_top.2 (hfin s ⟨hs.1.le, hs.2.trans ht.2⟩)
  have hii : IntervalIntegrable (fun s => (Ψ s).toReal) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Integrable.mono' (g := fun _ => M.toReal) (integrableOn_const (by simp))
      hΨm.ennreal_toReal.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hM (hbd s ⟨hs.1.le, hs.2⟩)
  refine BlockBand.SourceProcess.Stochastic.SDE.gronwall_integral hL
    (fun t _ => ENNReal.toReal_nonneg) hii (fun t ht => ?_)
  rw [hreal t ht]
  have hne : ENNReal.ofReal A + ENNReal.ofReal L * ∫⁻ s in Ioc 0 t, Ψ s ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hint_fin t ht)⟩
  refine (ENNReal.toReal_mono hne (hle t ht)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hint_fin t ht)), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hL]

/-- `(x + y)² ≤ 2x² + 2y²` in `ℝ≥0∞`. -/
private theorem ennreal_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  have h : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg ((x : ℝ) - y)]
  exact_mod_cast h

/-- Real-linear coordinate of a matrix: `Re A_ij` (`q = 0`) or `Im A_ij` (`q = 1`). -/
private def entryLin (p : (Fin N × Fin N) × Fin 2) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℝ :=
  (if p.2 = 0 then Complex.reLm else Complex.imLm).comp (Matrix.entryLinearMap ℝ ℂ p.1.1 p.1.2)

/-- `|ℓ_p A| ≤ ‖A‖`. -/
private theorem abs_entryLin_le (p : (Fin N × Fin N) × Fin 2) (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖entryLin p A‖ ≤ 1 * ‖A‖ := by
  rw [one_mul]
  refine le_trans ?_ (norm_entry_le A p.1.1 p.1.2)
  by_cases h : p.2 = 0
  · simp only [entryLin, h, ite_true, LinearMap.coe_comp, Function.comp_apply,
      entryLinearMap_apply, Complex.reLm_coe, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm _
  · simp only [entryLin, h, ite_false, LinearMap.coe_comp, Function.comp_apply,
      entryLinearMap_apply, Complex.imLm_coe, Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _

/-- The coordinate functional as a continuous linear map of norm `≤ 1`. -/
private def entryCLM (p : (Fin N × Fin N) × Fin 2) :=
  (entryLin p).mkContinuous 1 (abs_entryLin_le p)

/-- Evaluation of `entryCLM`. -/
private theorem entryCLM_apply (p : (Fin N × Fin N) × Fin 2) (A : Matrix (Fin N) (Fin N) ℂ) :
    entryCLM p A = entryLin p A := rfl

/-- `‖ℓ_p‖ₑ ≤ 1`. -/
private theorem enorm_entryCLM_le (p : (Fin N × Fin N) × Fin 2) : ‖entryCLM p‖ₑ ≤ 1 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (LinearMap.mkContinuous_norm_le _ zero_le_one _)

/-- `‖A‖² = ∑_p (ℓ_p A)²` for the Frobenius norm. -/
private theorem norm_sq_eq_sum_entryCLM (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A‖ ^ 2 = ∑ p, (entryCLM p A) ^ 2 := by
  rw [norm_sq_eq_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  simp only [entryCLM_apply, entryLin, ite_true, one_ne_zero, ite_false,
    LinearMap.coe_comp, Function.comp_apply, entryLinearMap_apply, Complex.reLm_coe,
    Complex.imLm_coe, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- `‖A‖ₑ² = ∑_p ‖ℓ_p A‖ₑ²`. -/
private theorem enorm_sq_eq_sum_entryCLM (A : Matrix (Fin N) (Fin N) ℂ) :
    ‖A‖ₑ ^ 2 = ∑ p, ‖entryCLM p A‖ₑ ^ 2 := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), norm_sq_eq_sum_entryCLM,
    ENNReal.ofReal_sum_of_nonneg (fun p _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-!
## Coefficient bounds
-/

/-- Lipschitz constant: bounds `‖rotationDrift‖` and `‖rotationNoise‖` for coefficients `≤ R`. -/
def stabLip (N : ℕ) (R : ℝ) : ℝ := ((N : ℝ) + 1) ^ 2 * R + 2 * Real.sqrt R

/-- Perturbation constant: bounds the coefficient differences per unit of `ε`. -/
def stabPert (N : ℕ) (R : ℝ) : ℝ := 2 * ((N : ℝ) + 1) ^ 2 * (Real.sqrt R + 1)

/-- A matrix with entries bounded by `b` has Frobenius norm `≤ N b`. -/
private theorem norm_le_of_entry_le {A : Matrix (Fin N) (Fin N) ℂ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i j, ‖A i j‖ ≤ b) : ‖A‖ ≤ N * b := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin N, ∑ _j : Fin N, b ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = ((N : ℝ) * b) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `‖1‖ ≤ √N` (Frobenius). -/
private theorem norm_one_le_sqrt : ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖ ≤ Real.sqrt N := by
  refine Real.le_sqrt_of_sq_le (le_of_eq ?_)
  rw [norm_sq_eq_sum]
  simp [Matrix.one_apply, apply_ite, Finset.sum_ite_eq]

/-- `|x - y| ≤ 2 √R |ε|` from `|√x - √y| ≤ ε` and `0 ≤ x, y ≤ R`. -/
private theorem abs_sub_le_of_abs_sqrt_sub_le {x y R ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxR : x ≤ R)
    (hyR : y ≤ R) (h : |Real.sqrt x - Real.sqrt y| ≤ ε) :
    |x - y| ≤ 2 * Real.sqrt R * |ε| := by
  have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
    calc x - y = Real.sqrt x ^ 2 - Real.sqrt y ^ 2 := by
          rw [Real.sq_sqrt hx, Real.sq_sqrt hy]
      _ = _ := by ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have h1 : Real.sqrt x + Real.sqrt y ≤ 2 * Real.sqrt R := by
    linarith [Real.sqrt_le_sqrt hxR, Real.sqrt_le_sqrt hyR]
  calc |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) ≤ |ε| * (2 * Real.sqrt R) :=
        mul_le_mul (h.trans (le_abs_self ε)) h1 (by positivity) (abs_nonneg _)
    _ = _ := by ring

/-- `∑_{m ≠ k} f m ≤ N b` for `0 ≤ f ≤ b`. -/
private theorem sum_erase_le {f : Fin N → ℝ} (hf : ∀ m, 0 ≤ f m) {b : ℝ} (hb : ∀ m, f m ≤ b) (k : Fin N) :
    ∑ m ∈ Finset.univ.erase k, f m ≤ N * b := by
  calc ∑ m ∈ Finset.univ.erase k, f m ≤ ∑ m, f m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun m _ _ => hf m
    _ ≤ ∑ _m : Fin N, b := Finset.sum_le_sum fun m _ => hb m
    _ = N * b := by simp

/-- `‖rotationDrift r κ‖ ≤ stabLip N R` for `0 ≤ r, κ ≤ R`. -/
theorem norm_rotationDrift_le {r : Fin N → Fin N → ℝ} {κ : Fin N → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hr : ∀ k l, 0 ≤ r k l) (hκ : ∀ k, 0 ≤ κ k) (hrR : ∀ k l, r k l ≤ R) (hκR : ∀ k, κ k ≤ R) :
    ‖rotationDrift r κ‖ ≤ stabLip N R := by
  have hent : ∀ i j, ‖rotationDrift r κ i j‖ ≤ ((N : ℝ) + 1) * R := by
    intro i j
    simp only [rotationDrift, Matrix.diagonal_apply]
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 := sum_erase_le (hr i) (hrR i) i
      have h2 : 0 ≤ ∑ m ∈ Finset.univ.erase i, r i m + κ i :=
        add_nonneg (Finset.sum_nonneg fun m _ => hr i m) (hκ i)
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith [hκR i]
    · simp only [norm_zero]
      positivity
  refine (norm_le_of_entry_le (by positivity) hent).trans ?_
  unfold stabLip
  nlinarith [Real.sqrt_nonneg R, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- `‖rotationDrift r κ - rotationDrift r' κ'‖ ≤ stabPert N R · |ε|`. -/
theorem norm_rotationDrift_sub_le {r r' : Fin N → Fin N → ℝ} {κ κ' : Fin N → ℝ} {R ε : ℝ}
    (hr : ∀ k l, 0 ≤ r k l) (hr' : ∀ k l, 0 ≤ r' k l) (hrR : ∀ k l, r k l ≤ R)
    (hrR' : ∀ k l, r' k l ≤ R) (hεr : ∀ k l, |Real.sqrt (r k l) - Real.sqrt (r' k l)| ≤ ε)
    (hεκ : ∀ k, |κ k - κ' k| ≤ ε) :
    ‖rotationDrift r κ - rotationDrift r' κ'‖ ≤ stabPert N R * |ε| := by
  have hent : ∀ i j, ‖(rotationDrift r κ - rotationDrift r' κ') i j‖ ≤
      ((N : ℝ) + 1) * (Real.sqrt R + 1) * |ε| := by
    intro i j
    simp only [rotationDrift, Matrix.sub_apply, Matrix.diagonal_apply]
    split_ifs with h
    · rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hs : |∑ m ∈ Finset.univ.erase i, r i m - ∑ m ∈ Finset.univ.erase i, r' i m| ≤
          N * (2 * Real.sqrt R * |ε|) := by
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact sum_erase_le (fun m => abs_nonneg _) (fun m => abs_sub_le_of_abs_sqrt_sub_le
          (hr i m) (hr' i m) (hrR i m) (hrR' i m) (hεr i m)) i
      have e : -(1 / 2 : ℝ) * (∑ m ∈ Finset.univ.erase i, r i m + κ i) -
          -(1 / 2 : ℝ) * (∑ m ∈ Finset.univ.erase i, r' i m + κ' i) =
          -(1 / 2 : ℝ) * ((∑ m ∈ Finset.univ.erase i, r i m -
            ∑ m ∈ Finset.univ.erase i, r' i m) + (κ i - κ' i)) := by ring
      rw [e, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have h3 := (abs_add_le _ _).trans (add_le_add hs ((hεκ i).trans (le_abs_self ε)))
      have hN := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      have hsR := Real.sqrt_nonneg R
      have hε := abs_nonneg ε
      nlinarith [mul_nonneg (mul_nonneg hN hsR) hε, mul_nonneg hN hε, mul_nonneg hsR hε]
    · simp only [sub_self, norm_zero]
      positivity
  refine (norm_le_of_entry_le (by positivity) hent).trans ?_
  unfold stabPert
  have hN := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hb : 0 ≤ ((N : ℝ) + 1) * (Real.sqrt R + 1) * |ε| := by positivity
  nlinarith

/-- `‖single i j 1‖ = 1` (Frobenius). -/
private theorem norm_single_one (i j : Fin N) : ‖Matrix.single i j (1 : ℂ)‖ = 1 := by
  have h : ‖Matrix.single i j (1 : ℂ)‖ ^ 2 = 1 := by
    rw [norm_sq_eq_sum]
    simp [single_apply, apply_ite, ite_and, Finset.sum_ite_eq]
  have := norm_nonneg (Matrix.single i j (1 : ℂ))
  nlinarith

/-- `‖X_ij‖, ‖Y_ij‖ ≤ 2` (Frobenius). -/
private theorem norm_rot_le (i j : Fin N) (q : Fin 2) :
    ‖(if q = 0 then rotX i j else rotY i j)‖ ≤ 2 := by
  split_ifs
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_single_one, norm_single_one]
    norm_num
  · rw [rotY, norm_smul, Complex.norm_I, one_mul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_single_one, norm_single_one]
    norm_num

/-- `‖rotationNoise r α‖ ≤ stabLip N R` for `r ≤ R`, `0 ≤ R`. -/
theorem norm_rotationNoise_le {r : Fin N → Fin N → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hrR : ∀ k l, r k l ≤ R) (α : (Fin N × Fin N) × Fin 2) :
    ‖rotationNoise r α‖ ≤ stabLip N R := by
  have hL : 2 * Real.sqrt R ≤ stabLip N R := by
    unfold stabLip
    have : 0 ≤ ((N : ℝ) + 1) ^ 2 * R := by positivity
    linarith
  unfold rotationNoise
  by_cases h : α.1.1 < α.1.2
  · simp only [h, ite_true]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt (r α.1.1 α.1.2 / 2) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt (by linarith [hrR α.1.1 α.1.2])
    have h2 := norm_rot_le α.1.1 α.1.2 α.2
    refine le_trans ?_ hL
    nlinarith [Real.sqrt_nonneg (r α.1.1 α.1.2 / 2), norm_nonneg
      (if α.2 = 0 then rotX α.1.1 α.1.2 else rotY α.1.1 α.1.2)]
  · simp only [h, ite_false]
    rw [norm_zero]
    exact (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt R).trans hL

/-- `‖rotationNoise r α - rotationNoise r' α‖ ≤ stabPert N R · |ε|`. -/
theorem norm_rotationNoise_sub_le {r r' : Fin N → Fin N → ℝ} {R ε : ℝ}
    (hr : ∀ k l, 0 ≤ r k l) (hr' : ∀ k l, 0 ≤ r' k l)
    (hεr : ∀ k l, |Real.sqrt (r k l) - Real.sqrt (r' k l)| ≤ ε) (α : (Fin N × Fin N) × Fin 2) :
    ‖rotationNoise r α - rotationNoise r' α‖ ≤ stabPert N R * |ε| := by
  have hP : 2 * |ε| ≤ stabPert N R * |ε| := by
    unfold stabPert
    have hN := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have h1 : 1 ≤ ((N : ℝ) + 1) ^ 2 * (Real.sqrt R + 1) := by
      nlinarith [Real.sqrt_nonneg R]
    nlinarith [abs_nonneg ε]
  unfold rotationNoise
  by_cases h : α.1.1 < α.1.2
  · simp only [h, ite_true]
    rw [← sub_smul, ← Complex.ofReal_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.sqrt (r α.1.1 α.1.2 / 2) - Real.sqrt (r' α.1.1 α.1.2 / 2)| ≤ |ε| := by
      rw [Real.sqrt_div (hr _ _), Real.sqrt_div (hr' _ _), ← sub_div, abs_div,
        abs_of_pos (Real.sqrt_pos.2 two_pos)]
      refine (div_le_self (abs_nonneg _) (Real.one_le_sqrt.2 one_le_two)).trans ?_
      exact (hεr _ _).trans (le_abs_self ε)
    have h2 := norm_rot_le α.1.1 α.1.2 α.2
    refine le_trans ?_ hP
    nlinarith [abs_nonneg (Real.sqrt (r α.1.1 α.1.2 / 2) - Real.sqrt (r' α.1.1 α.1.2 / 2)),
      norm_nonneg (if α.2 = 0 then rotX α.1.1 α.1.2 else rotY α.1.1 α.1.2), abs_nonneg ε]
  · simp only [h, ite_false]
    rw [sub_self, norm_zero]
    exact (by positivity : (0 : ℝ) ≤ 2 * |ε|).trans hP

/-!
## The Grönwall comparison
-/

/-- The explicit factor `8 N² (T + 2N²)`. -/
def stabFactor (N : ℕ) (T : ℝ) : ℝ := 8 * (N : ℝ) ^ 2 * (T + 2 * (N : ℝ) ^ 2)

/-- `stabFactor N T ≥ 0` for `T ≥ 0`. -/
theorem stabFactor_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ stabFactor N T := by
  unfold stabFactor
  positivity

/-- `stabFactor` in `ℝ≥0∞`. -/
private theorem ofReal_stabFactor (N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ENNReal.ofReal (stabFactor N T) = 8 * (N : ℝ≥0∞) ^ 2 * (ENNReal.ofReal T + 2 * (N : ℝ≥0∞) ^ 2) := by
  unfold stabFactor
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_add hT (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (Nat.cast_nonneg N), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]

/-- **Grönwall comparison of two identities with perturbed coefficients.** -/
theorem lintegral_sq_sub_le_of_perturb {S : Type*} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ] {T : ℝ≥0}
    {X Y β β' : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    {γ γ' : (Fin N × Fin N) × Fin 2 → ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ}
    (hXa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (X t))
    (hYa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (Y t))
    (hXc : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, Continuous fun t => X t x)
    (hYc : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, Continuous fun t => Y t x)
    (h0 : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, X 0 x = Y 0 x)
    (hX : StoppedIdentity μ T (fun _ => ⊤) X β γ) (hY : StoppedIdentity μ T (fun _ => ⊤) Y β' γ')
    {B₀ C K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hXb : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t, ‖X t x‖ ≤ B₀)
    (hYb : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ t, ‖Y t x‖ ≤ B₀)
    (hbd : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ s : ℝ≥0,
      ‖β s x‖ ≤ C ∧ ‖β' s x‖ ≤ C)
    (hdom : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ, ∀ s : ℝ≥0,
      ‖β s x - β' s x‖ ≤ K * ‖X s x - Y s x‖ + D ∧
        ∀ α, ‖γ α s x - γ' α s x‖ ≤ K * ‖X s x - Y s x‖ + D)
    (hβ : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ,
      AEStronglyMeasurable (fun s : ℝ => β s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ))))
    (hβ' : ∀ᵐ x ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ,
      AEStronglyMeasurable (fun s : ℝ => β' s.toNNReal x) (volume.restrict (Ioc 0 (T : ℝ)))) :
    ∫⁻ x, ‖X T x - Y T x‖ₑ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ ≤
      ENNReal.ofReal (stabFactor N T * D ^ 2 * T * Real.exp (stabFactor N T * K ^ 2 * T)) := by
  classical
  set P := driverLaw (κ := (Fin N × Fin N) × Fin 2) μ with hP
  set Z : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ := fun t x => X t x - Y t x with hZdef
  have hZa : ∀ t, StronglyMeasurable[driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ t] (Z t) :=
    fun t => (hXa t).sub (hYa t)
  have hZc : ∀ᵐ x ∂P, Continuous fun t => Z t x := by
    filter_upwards [hXc, hYc] with x h1 h2
    exact h1.sub h2
  set F : ℝ × FlowSample S N → ℝ≥0∞ := fun p => ‖Z p.1.toNNReal p.2‖ₑ with hFdef
  have hFm : AEMeasurable F (timeProbMeasure T P) :=
    ((aesm_processFun (T := T) hZa hZc).mono (predictableSpace_le _)).enorm
  have hFpath : ∀ᵐ x ∂P, AEMeasurable (fun s : ℝ => F (s, x)) (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hZc] with x hx
    have hn : @Continuous (Matrix (Fin N) (Fin N) ℂ) ℝ≥0∞
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ (fun A => ‖A‖ₑ) := continuous_enorm
    exact (hn.comp (hx.comp continuous_real_toNNReal)).measurable.aemeasurable
  set H : ℝ × FlowSample S N → ℝ≥0∞ := fun p => ENNReal.ofReal K * F p + ENNReal.ofReal D
    with hHdef
  have hHm : AEMeasurable H (timeProbMeasure T P) := (hFm.const_mul _).add_const _
  have hHpath : ∀ᵐ x ∂P, AEMeasurable (fun s : ℝ => H (s, x)) (volume.restrict (Ioc 0 (T : ℝ))) := by
    filter_upwards [hFpath] with x hx
    exact (hx.const_mul _).add_const _
  have hdomH : ∀ᵐ x ∂P, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ (fun _ => (⊤ : WithTop ℝ≥0)) x →
      ‖β s x - β' s x‖ₑ ≤ H ((s : ℝ), x) ∧ ∀ a, ‖γ a s x - γ' a s x‖ₑ ≤ H ((s : ℝ), x) := by
    filter_upwards [hdom] with x hx s _ _
    have hF : H ((s : ℝ), x) = ENNReal.ofReal (K * ‖X s x - Y s x‖ + D) := by
      simp only [hHdef, hFdef, hZdef, Real.toNNReal_coe]
      rw [ENNReal.ofReal_add (by positivity) hD, ENNReal.ofReal_mul hK, ofReal_norm]
    rw [hF]
    refine ⟨?_, fun a => ?_⟩
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hx s).1
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal ((hx s).2 a)
  have hbd' : ∀ᵐ x ∂P, ∀ s : ℝ≥0, 0 < s → (s : WithTop ℝ≥0) ≤ (fun _ => (⊤ : WithTop ℝ≥0)) x →
      ‖β s x‖ ≤ C ∧ ‖β' s x‖ ≤ C := by
    filter_upwards [hbd] with x hx s _ _
    exact hx s
  have hst : ∀ (W : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0),
      stoppedProcess W (fun _ => (⊤ : WithTop ℝ≥0)) t = W t :=
    fun W t => funext fun _ => stoppedProcess_eq_of_le le_top
  -- one coordinate
  have hΦ : ∀ t ≤ T, ∀ p, ∫⁻ x, ‖entryCLM p (X t x) - entryCLM p (Y t x)‖ₑ ^ 2 ∂P ≤
      2 * (ENNReal.ofReal T + (Fintype.card ((Fin N × Fin N) × Fin 2) : ℝ≥0∞)) *
        ∫⁻ q, H q ^ 2 ∂timeProbMeasure t P := by
    intro t ht p
    have h := lintegral_sq_functional_sub_le h0 hX hY hbd' hβ hβ' hHm hHpath hdomH (entryCLM p) ht
    rw [hst X, hst Y] at h
    refine h.trans ?_
    have h1 : ‖entryCLM p‖ₑ ^ 2 ≤ 1 := pow_le_one₀ zero_le (enorm_entryCLM_le p)
    have h2 : ENNReal.ofReal t ≤ ENNReal.ofReal T :=
      ENNReal.ofReal_le_ofReal (by exact_mod_cast ht)
    calc 2 * ‖entryCLM p‖ₑ ^ 2 * (ENNReal.ofReal t +
          (Fintype.card ((Fin N × Fin N) × Fin 2) : ℝ≥0∞)) * ∫⁻ q, H q ^ 2 ∂timeProbMeasure t P
        ≤ 2 * 1 * (ENNReal.ofReal T + (Fintype.card ((Fin N × Fin N) × Fin 2) : ℝ≥0∞)) *
          ∫⁻ q, H q ^ 2 ∂timeProbMeasure t P := by gcongr
      _ = _ := by ring
  -- the Volterra function
  set Ψ : ℝ → ℝ≥0∞ := fun s => ∫⁻ x, F (s, x) ^ 2 ∂P with hΨdef
  have hF2 : AEMeasurable (fun p => F p ^ 2) (timeProbMeasure T P) := hFm.pow_const 2
  have hΨm : AEMeasurable Ψ (volume.restrict (Ioc 0 (T : ℝ))) := by
    unfold timeProbMeasure at hF2
    exact hF2.lintegral_prod_right'
  have hQ : ∀ t ≤ T, ∫⁻ p, F p ^ 2 ∂timeProbMeasure t P = ∫⁻ s in Ioc 0 (t : ℝ), Ψ s := by
    intro t ht
    have h := hF2.mono_measure (timeProbMeasure_le_of_le ht)
    unfold timeProbMeasure at h ⊢
    exact lintegral_prod _ h
  have hH2 : ∀ t ≤ T, ∫⁻ q, H q ^ 2 ∂timeProbMeasure t P ≤
      2 * ENNReal.ofReal K ^ 2 * (∫⁻ s in Ioc 0 (t : ℝ), Ψ s) +
        2 * ENNReal.ofReal D ^ 2 * ENNReal.ofReal t := by
    intro t ht
    have hne : 2 * ENNReal.ofReal K ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    calc ∫⁻ q, H q ^ 2 ∂timeProbMeasure t P
        ≤ ∫⁻ q, (2 * ENNReal.ofReal K ^ 2 * F q ^ 2 + 2 * ENNReal.ofReal D ^ 2)
            ∂timeProbMeasure t P := by
          refine lintegral_mono fun q => (ennreal_add_sq_le _ _).trans (le_of_eq ?_)
          rw [mul_pow]
          ring
      _ = 2 * ENNReal.ofReal K ^ 2 * (∫⁻ q, F q ^ 2 ∂timeProbMeasure t P) +
            2 * ENNReal.ofReal D ^ 2 * ENNReal.ofReal t := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ hne,
            lintegral_const, timeProbMeasure_univ]
      _ = _ := by rw [hQ t ht]
  have hΨbd : ∀ s, Ψ s ≤ ENNReal.ofReal ((2 * B₀) ^ 2) := by
    intro s
    calc Ψ s ≤ ∫⁻ _, ENNReal.ofReal ((2 * B₀) ^ 2) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hXb, hYb] with x h1 h2
          simp only [hFdef, hZdef]
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
          linarith [norm_sub_le (X s.toNNReal x) (Y s.toNNReal x), h1 s.toNNReal, h2 s.toNNReal]
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hXm : ∀ t, AEStronglyMeasurable (X t) P := fun t =>
    ((hXa t).mono ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)).aestronglyMeasurable
  have hYm : ∀ t, AEStronglyMeasurable (Y t) P := fun t =>
    ((hYa t).mono ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)).aestronglyMeasurable
  have hcard : ((Fintype.card ((Fin N × Fin N) × Fin 2) : ℕ) : ℝ≥0∞) = 2 * (N : ℝ≥0∞) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hstep : ∀ s ∈ Icc 0 (T : ℝ), Ψ s ≤ ENNReal.ofReal (stabFactor N T * D ^ 2 * T) +
      ENNReal.ofReal (stabFactor N T * K ^ 2) * ∫⁻ r in Ioc 0 s, Ψ r := by
    intro s hs
    have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hΨeq : Ψ s = ∑ p, ∫⁻ x, ‖entryCLM p (X s.toNNReal x) - entryCLM p (Y s.toNNReal x)‖ₑ ^ 2 ∂P := by
      rw [← lintegral_finsetSum' (f := fun p x =>
        ‖entryCLM p (X s.toNNReal x) - entryCLM p (Y s.toNNReal x)‖ₑ ^ 2) _ fun p _ =>
        ((((entryCLM p).continuous.comp_aestronglyMeasurable (hXm _)).sub
          ((entryCLM p).continuous.comp_aestronglyMeasurable (hYm _))).enorm).pow_const 2]
      refine lintegral_congr fun x => ?_
      simp only [hFdef, hZdef]
      rw [enorm_sq_eq_sum_entryCLM]
      simp only [map_sub]
    have hT0 : (0 : ℝ) ≤ T := T.2
    have hle : ENNReal.ofReal s ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal hs.2
    calc Ψ s ≤ ∑ _p : (Fin N × Fin N) × Fin 2,
          2 * (ENNReal.ofReal T + (Fintype.card ((Fin N × Fin N) × Fin 2) : ℝ≥0∞)) *
            (2 * ENNReal.ofReal K ^ 2 * (∫⁻ r in Ioc 0 s, Ψ r) +
              2 * ENNReal.ofReal D ^ 2 * ENNReal.ofReal T) := by
          rw [hΨeq]
          refine Finset.sum_le_sum fun p _ => (hΦ _ hsT p).trans ?_
          have := hH2 _ hsT
          rw [hs'] at this
          gcongr
          exact this.trans (by gcongr)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            ENNReal.ofReal_mul (mul_nonneg (stabFactor_nonneg N hT0) (sq_nonneg D)),
            ENNReal.ofReal_mul (stabFactor_nonneg N hT0), ENNReal.ofReal_mul (stabFactor_nonneg N hT0),
            ofReal_stabFactor N hT0, ENNReal.ofReal_pow hD, ENNReal.ofReal_pow hK]
          ring
  have hG := toReal_le_of_lintegral_gronwall (Ψ := Ψ) (T := (T : ℝ)) T.2 hΨm
    (M := ENNReal.ofReal ((2 * B₀) ^ 2)) ENNReal.ofReal_ne_top
    (mul_nonneg (mul_nonneg (stabFactor_nonneg N T.2) (sq_nonneg D)) T.2)
    (mul_nonneg (stabFactor_nonneg N T.2) (sq_nonneg K)) (fun s _ => hΨbd s) hstep
    (T : ℝ) ⟨T.2, le_rfl⟩
  have hΨT : Ψ (T : ℝ) = ∫⁻ x, ‖X T x - Y T x‖ₑ ^ 2 ∂P := by
    simp only [hΨdef, hFdef, hZdef, Real.toNNReal_coe]
  rw [← hΨT, ENNReal.le_ofReal_iff_toReal_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΨbd _))
    (by have := stabFactor_nonneg N T.2; positivity)]
  exact hG

/-!
## Stability of rotation flows
-/

/-- The explicit stability constant
`C(N, R, t) = 8N²(t + 2N²) · (stabPert N R)² N · t · exp(8N²(t + 2N²) (stabLip N R)² t)`. -/
def stabConst (N : ℕ) (R t : ℝ) : ℝ :=
  stabFactor N t * (stabPert N R * Real.sqrt N) ^ 2 * t *
    Real.exp (stabFactor N t * stabLip N R ^ 2 * t)

/-- The stability constant is nonnegative for `t ≥ 0`. -/
theorem stabConst_nonneg (N : ℕ) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ stabConst N R t := by
  unfold stabConst
  have := stabFactor_nonneg N ht
  positivity

/-- The stability constant is monotone in `t ≥ 0`. -/
theorem stabConst_mono (N : ℕ) (R : ℝ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    stabConst N R t ≤ stabConst N R t' := by
  unfold stabConst stabFactor
  have ht' : 0 ≤ t' := ht.trans htt
  gcongr

/-- **`L²` stability of rotation flows in their coefficients, `ℝ≥0∞` form.** Two rotation flows
on the same driver space, started at the same `s` on the same window `[a, c]`, with admissible
coefficients bounded by `R` on `[a, c]` and `|√r − √r'| ≤ ε`, `|κ − κ'| ≤ ε` on `[a, c]`, satisfy
`E‖M_t − M'_t‖² ≤ C(N, R, t) ε²` (Frobenius norm, `E` over `driverLaw μ`). -/
theorem lintegral_enorm_sub_sq_le_of_isRotationFlow {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {r r' : ℝ → Fin N → Fin N → ℝ}
    {κ κ' : ℝ → Fin N → ℝ} {a c s R ε : ℝ} (hac : a ≤ c) (h : Admissible a c r κ)
    (h' : Admissible a c r' κ') (hR : 0 ≤ R)
    (hrR : ∀ x ∈ Icc a c, ∀ k l, r x k l ≤ R ∧ r' x k l ≤ R)
    (hκR : ∀ x ∈ Icc a c, ∀ k, κ x k ≤ R ∧ κ' x k ≤ R)
    (hεr : ∀ x ∈ Icc a c, ∀ k l, |Real.sqrt (r x k l) - Real.sqrt (r' x k l)| ≤ ε)
    (hεκ : ∀ x ∈ Icc a c, ∀ k, |κ x k - κ' x k| ≤ ε)
    {M M' : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) (hM' : IsRotationFlow μ r' κ' a c s M') (t : ℝ≥0) :
    ∫⁻ x, ‖M t x - M' t x‖ₑ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ ≤
      ENNReal.ofReal (stabConst N R t * ε ^ 2) := by
  obtain ⟨hrc, hκc, hs, hr, hk⟩ := h
  obtain ⟨hrc', hκc', hs', hr', hk'⟩ := h'
  set x₀ : ℝ≥0 → ℝ := fun u => clampTime a c (s + u) with hx₀
  have hmem : ∀ u, x₀ u ∈ Icc a c := fun u => clampTime_mem hac _
  have hK0 : 0 ≤ stabLip N R := by unfold stabLip; positivity
  have hD0 : 0 ≤ stabPert N R * |ε| * Real.sqrt N := by unfold stabPert; positivity
  have hb := isRotationFlow_norm_le hs hr hk hM
  have hb' := isRotationFlow_norm_le hs' hr' hk' hM'
  have hone := norm_one_le_sqrt (N := N)
  have hpath : ∀ {r₁ : ℝ → Fin N → Fin N → ℝ} {κ₁ : ℝ → Fin N → ℝ},
      ContinuousOn r₁ (Icc a c) → ContinuousOn κ₁ (Icc a c) →
      ∀ {X : ℝ≥0 → FlowSample S N → Matrix (Fin N) (Fin N) ℂ} {x : FlowSample S N},
      Continuous (fun u => X u x) → AEStronglyMeasurable (fun u : ℝ =>
        rotationDrift (r₁ (clampTime a c (s + u.toNNReal))) (κ₁ (clampTime a c (s + u.toNNReal))) *
          X u.toNNReal x) (volume.restrict (Ioc 0 (t : ℝ))) := fun {r₁ κ₁} h1 h2 {X x} hx => by
    have h := ((continuous_driftAt s hac h1 h2).comp continuous_real_toNNReal).matrix_mul
      (hx.comp continuous_real_toNNReal)
    have : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin N) (Fin N) ℂ) :=
      matrixPseudoMetrizable
    exact h.aestronglyMeasurable
  have key := lintegral_sq_sub_le_of_perturb (T := t) hM.1.adapted hM'.1.adapted hM.1.continuous
    hM'.1.continuous (Eventually.of_forall fun x => by rw [hM.2 x, hM'.2 x])
    (isRotationFlow_stoppedIdentity_top hac hrc hκc hs hr hk hM t)
    (isRotationFlow_stoppedIdentity_top hac hrc' hκc' hs' hr' hk' hM' t)
    (C := stabLip N R * ‖(1 : Matrix (Fin N) (Fin N) ℂ)‖) hK0 hD0 hb hb'
    (by
      filter_upwards [hb, hb'] with x hx hx' u
      exact ⟨(frobenius_norm_mul _ _).trans (mul_le_mul (norm_rotationDrift_le hR
          (hr _) (hk _) (fun k l => (hrR _ (hmem u) k l).1) (fun k => (hκR _ (hmem u) k).1))
          (hx u) (norm_nonneg _) hK0),
        (frobenius_norm_mul _ _).trans (mul_le_mul (norm_rotationDrift_le hR
          (hr' _) (hk' _) (fun k l => (hrR _ (hmem u) k l).2) (fun k => (hκR _ (hmem u) k).2))
          (hx' u) (norm_nonneg _) hK0)⟩)
    (by
      filter_upwards [hb'] with x hx' u
      have hsplit : ∀ (A A' : Matrix (Fin N) (Fin N) ℂ) {L E₀ : ℝ}, ‖A‖ ≤ L →
          ‖A - A'‖ ≤ E₀ → ‖A * M u x - A' * M' u x‖ ≤
            L * ‖M u x - M' u x‖ + E₀ * Real.sqrt N := by
        intro A A' L E₀ hA hAA'
        have e : A * M u x - A' * M' u x = A * (M u x - M' u x) + (A - A') * M' u x := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ((frobenius_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) ((frobenius_norm_mul _ _).trans ?_))
        exact mul_le_mul hAA' ((hx' u).trans hone) (norm_nonneg _)
          ((norm_nonneg _).trans hAA')
      refine ⟨?_, fun α => ?_⟩
      · refine hsplit _ _ (norm_rotationDrift_le hR (hr _) (hk _)
          (fun k l => (hrR _ (hmem u) k l).1) (fun k => (hκR _ (hmem u) k).1))
          (norm_rotationDrift_sub_le (hr _) (hr' _) (fun k l => (hrR _ (hmem u) k l).1)
            (fun k l => (hrR _ (hmem u) k l).2) (hεr _ (hmem u)) (hεκ _ (hmem u)))
      · exact hsplit _ _ (norm_rotationNoise_le hR (fun k l => (hrR _ (hmem u) k l).1) α)
          (norm_rotationNoise_sub_le (hr _) (hr' _) (hεr _ (hmem u)) α))
    (by filter_upwards [hM.1.continuous] with x hx; exact hpath hrc hκc hx)
    (by filter_upwards [hM'.1.continuous] with x hx; exact hpath hrc' hκc' hx)
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  unfold stabConst
  rw [mul_pow, mul_pow, sq_abs]
  ring

/-- **`L²` stability of rotation flows in their coefficients.** Bochner form of
`lintegral_enorm_sub_sq_le_of_isRotationFlow`: `∫ ‖M_t − M'_t‖² ∂driverLaw μ ≤ C(N, R, t) ε²`. -/
theorem integral_norm_sub_sq_le_of_isRotationFlow {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {r r' : ℝ → Fin N → Fin N → ℝ}
    {κ κ' : ℝ → Fin N → ℝ} {a c s R ε : ℝ} (hac : a ≤ c) (h : Admissible a c r κ)
    (h' : Admissible a c r' κ') (hR : 0 ≤ R)
    (hrR : ∀ x ∈ Icc a c, ∀ k l, r x k l ≤ R ∧ r' x k l ≤ R)
    (hκR : ∀ x ∈ Icc a c, ∀ k, κ x k ≤ R ∧ κ' x k ≤ R)
    (hεr : ∀ x ∈ Icc a c, ∀ k l, |Real.sqrt (r x k l) - Real.sqrt (r' x k l)| ≤ ε)
    (hεκ : ∀ x ∈ Icc a c, ∀ k, |κ x k - κ' x k| ≤ ε)
    {M M' : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) (hM' : IsRotationFlow μ r' κ' a c s M') (t : ℝ≥0) :
    ∫ x, ‖M t x - M' t x‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ ≤
      stabConst N R t * ε ^ 2 := by
  have hXm : AEStronglyMeasurable (M t) (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) :=
    ((hM.1.adapted t).mono
      ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (M' t) (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) :=
    ((hM'.1.adapted t).mono
      ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖M t x - M' t x‖ ^ 2)
    (Eventually.of_forall fun x => sq_nonneg _) ((hXm.sub hYm).norm.pow 2)]
  have hle := lintegral_enorm_sub_sq_le_of_isRotationFlow hac h h' hR hrR hκR hεr hεκ hM hM' t
  have he : ∀ x, ENNReal.ofReal (‖M t x - M' t x‖ ^ 2) = ‖M t x - M' t x‖ₑ ^ 2 := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp only [he]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (stabConst_nonneg N R t.2) (sq_nonneg ε)) hle

end BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFJoint
