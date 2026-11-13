module

public import BlockBand.Endpoints.Response.PassDerivativeRatio
public import BlockBand.Internal.Contracts.TransmissionPath

/-!
# The determinant ratio as a transform of the trace measure

For `0 ⪯ T ⪯ I`, `x ≥ 0` and `0 ≤ y < 1`, the determinant ratio `F_{x,y}(T) = det(I - yT)/det(I + xT)`
is `exp ∫ g dμ_T` with `g(t) = (log(1 - yt) - log(1 + xt))/t` and the trace measure `μ_T`
(`ratioDet_eq_transmissionRatio`).

* `ratioIntegrand ![x] ![y]` is continuous and nonpositive on `[0,1]` (`ratioBCF`);
* `abs_transmissionRatio_sub_le`: `|F(μ) - F(ν)| ≤ |∫ g dμ - ∫ g dν|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal unitInterval

/-!
### The integrand for one pair
-/

/-- `g(t) = log(1 - yt) - log(1 + xt)`. -/
def ratioLog (x y t : ℝ) : ℝ := Real.log (1 - y * t) - Real.log (1 + x * t)

theorem ratioIntegrand_one (x y t : ℝ) :
    ratioIntegrand ![x] ![y] t = if t = 0 then -(x + y) else ratioLog x y t / t := by
  simp [ratioIntegrand, ratioLog]

theorem ratioLog_zero (x y : ℝ) : ratioLog x y 0 = 0 := by simp [ratioLog]

theorem hasDerivAt_ratioLog {x y t : ℝ} (h1 : 0 < 1 - y * t) (h2 : 0 < 1 + x * t) :
    HasDerivAt (ratioLog x y) (-y / (1 - y * t) - x / (1 + x * t)) t := by
  have hA : HasDerivAt (fun s => 1 - y * s) (-y) t := by
    simpa using ((hasDerivAt_id t).const_mul y).const_sub 1
  have hB : HasDerivAt (fun s => 1 + x * s) x t := by
    simpa using ((hasDerivAt_id t).const_mul x).const_add 1
  have := (hA.log h1.ne').sub (hB.log h2.ne')
  exact this

theorem continuousOn_ratioIntegrand {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ContinuousOn (fun t => ratioIntegrand ![x] ![y] t) (Icc 0 1) := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 - y * t ∧ 0 < 1 + x * t := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  intro t ht
  rcases ht.1.lt_or_eq with h0 | h0
  · -- `t > 0`: locally the quotient
    have hd := (hasDerivAt_ratioLog (hpos t ht).1 (hpos t ht).2).continuousAt
    have hq : ContinuousAt (fun s => ratioLog x y s / s) t := hd.div continuousAt_id h0.ne'
    have hev : (fun s => ratioIntegrand ![x] ![y] s) =ᶠ[𝓝 t] fun s => ratioLog x y s / s := by
      filter_upwards [lt_mem_nhds h0] with s hs
      simp [ratioIntegrand_one, hs.ne']
    exact (hq.congr hev.symm).continuousWithinAt
  · subst h0
    have hd := hasDerivAt_ratioLog (x := x) (y := y) (t := 0) (by simp) (by simp)
    simp only [mul_zero, sub_zero, add_zero, div_one] at hd
    have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
      (nhdsWithin_mono _ fun u (hu : u ∈ Ioi (0 : ℝ)) => ne_of_gt hu)
    have hcw : ContinuousWithinAt (fun s => ratioIntegrand ![x] ![y] s) (Ioi 0) 0 := by
      rw [ContinuousWithinAt, ratioIntegrand_one]
      simp only [ite_true]
      refine (hs.congr' (eventually_nhdsWithin_of_forall fun u (hu : 0 < u) => ?_)).trans ?_
      · show u⁻¹ • (ratioLog x y (0 + u) - ratioLog x y 0) = ratioIntegrand ![x] ![y] u
        simp [ratioIntegrand_one, hu.ne', ratioLog_zero, inv_mul_eq_div]
      · rw [show -y - x = -(x + y) by ring]
    rw [← continuousWithinAt_insert_self] at hcw
    exact hcw.mono fun u (hu : u ∈ Icc (0 : ℝ) 1) => by
      rcases hu.1.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl h.symm

theorem ratioIntegrand_nonpos {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ratioIntegrand ![x] ![y] t ≤ 0 := by
  rw [ratioIntegrand_one]
  split_ifs with h
  · linarith
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    refine div_nonpos_of_nonpos_of_nonneg ?_ ht0.le
    unfold ratioLog
    have h1 : 0 < 1 - y * t := by nlinarith [ht.2]
    have h2 : Real.log (1 - y * t) ≤ 0 := Real.log_nonpos h1.le (by nlinarith)
    have h3 : 0 ≤ Real.log (1 + x * t) := Real.log_nonneg (by nlinarith)
    linarith

/-- The integrand as a bounded continuous function on `[0, 1]`. -/
def ratioBCF {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) : BoundedContinuousFunction unitInterval ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t => ratioIntegrand ![x] ![y] (t : ℝ),
      (continuousOn_ratioIntegrand hx hy0 hy1).comp_continuous continuous_subtype_val
        fun t => t.2⟩

theorem ratioBCF_apply {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (t : unitInterval) :
    ratioBCF hx hy0 hy1 t = ratioIntegrand ![x] ![y] (t : ℝ) := rfl

theorem integral_ratioIntegrand_nonpos {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (μ : FiniteMeasure unitInterval) : ∫ t, ratioIntegrand ![x] ![y] (t : ℝ) ∂(μ : Measure unitInterval) ≤ 0 :=
  integral_nonpos fun t => ratioIntegrand_nonpos hx hy0 hy1 t.2

theorem transmissionRatio_pos (x y : ℝ) (μ : FiniteMeasure unitInterval) :
    0 < transmissionRatio ![x] ![y] μ := Real.exp_pos _

theorem transmissionRatio_le_one {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (μ : FiniteMeasure unitInterval) : transmissionRatio ![x] ![y] μ ≤ 1 :=
  Real.exp_le_one_iff.2 (integral_ratioIntegrand_nonpos hx hy0 hy1 μ)

theorem continuous_transmissionRatio {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    Continuous fun μ : FiniteMeasure unitInterval => transmissionRatio ![x] ![y] μ :=
  Real.continuous_exp.comp
    (FiniteMeasure.continuous_integral_boundedContinuousFunction (ratioBCF hx hy0 hy1))

/-- `ν ↦ F_{x,y}(ν 0)` as a bounded continuous test on one time slot (bound `1`). -/
def ratioPhi {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    BoundedContinuousFunction (Fin 1 → FiniteMeasure unitInterval) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun ν => transmissionRatio ![x] ![y] (ν 0),
      (continuous_transmissionRatio hx hy0 hy1).comp (continuous_apply 0)⟩ 1
    (fun ν ν' => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have a1 := transmissionRatio_pos x y (ν 0)
      have a2 := transmissionRatio_le_one hx hy0 hy1 (ν 0)
      have a3 := transmissionRatio_pos x y (ν' 0)
      have a4 := transmissionRatio_le_one hx hy0 hy1 (ν' 0)
      rw [abs_le]; constructor <;> linarith)

theorem ratioPhi_apply {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (ν : Fin 1 → FiniteMeasure unitInterval) :
    ratioPhi hx hy0 hy1 ν = transmissionRatio ![x] ![y] (ν 0) := rfl

/-- `exp` is 1-Lipschitz on `(-∞, 0]`. -/
theorem abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hab)), abs_of_nonneg (sub_nonneg.2 hab)]
  have h1 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [h1]
  have h2 : 1 - Real.exp (b - a) ≤ a - b := by
    have := Real.add_one_le_exp (b - a); linarith
  have h3 : 0 ≤ 1 - Real.exp (b - a) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; linarith
  have h4 : Real.exp a ≤ 1 := Real.exp_le_one_iff.2 ha
  calc Real.exp a * (1 - Real.exp (b - a)) ≤ 1 * (1 - Real.exp (b - a)) :=
        mul_le_mul_of_nonneg_right h4 h3
    _ ≤ a - b := by linarith

/-- `|F(μ) - F(ν)| ≤ |∫ g dμ - ∫ g dν|` (both exponents are nonpositive). -/
theorem abs_transmissionRatio_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (μ ν : FiniteMeasure unitInterval) :
    |transmissionRatio ![x] ![y] μ - transmissionRatio ![x] ![y] ν| ≤
      |∫ t, ratioBCF hx hy0 hy1 t ∂(μ : Measure unitInterval) - ∫ t, ratioBCF hx hy0 hy1 t ∂(ν : Measure unitInterval)| := by
  have ha := integral_ratioIntegrand_nonpos hx hy0 hy1 μ
  have hb := integral_ratioIntegrand_nonpos hx hy0 hy1 ν
  set a := ∫ t, ratioIntegrand ![x] ![y] (t : ℝ) ∂(μ : Measure unitInterval)
  set b := ∫ t, ratioIntegrand ![x] ![y] (t : ℝ) ∂(ν : Measure unitInterval)
  show |Real.exp a - Real.exp b| ≤ |a - b|
  exact abs_exp_sub_exp_le_of_nonpos ha hb

/-!
### `det(I - yT)/det(I + xT)` through the trace measure
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_conjStarAlgAut (U : unitary (Matrix n n ℂ)) (M : Matrix n n ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U M).det = M.det := by
  rw [Unitary.conjStarAlgAut_apply, det_mul, det_mul, mul_comm (det (U : Matrix n n ℂ)),
    mul_assoc, ← det_mul, Unitary.mul_star_self_of_mem U.2, det_one, mul_one]

theorem det_one_add_smul_hermitian {T : Matrix n n ℂ} (hT : T.IsHermitian) (c : ℂ) :
    (1 + c • T).det = ∏ i, (1 + c * (hT.eigenvalues i : ℂ)) := by
  have hd : 1 + c • T = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hT.eigenvectorUnitary
      (diagonal fun i => 1 + c * (hT.eigenvalues i : ℂ)) := by
    conv_lhs => rw [hT.spectral_theorem]
    rw [← map_smul, ← map_one (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hT.eigenvectorUnitary),
      ← map_add]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  rw [hd, det_conjStarAlgAut, det_diagonal]

/-- Eigenvalues of a band matrix lie in `[0, 1]`. -/
theorem IsUnitBand.eigenvalues_mem {T : Matrix n n ℂ} (h : IsUnitBand T) (i : n) :
    h.1.eigenvalues i ∈ Icc (0 : ℝ) 1 :=
  ⟨eigenvalues_ge_of_quad h.1 (fun v => by simpa using (h.2 v).1) i,
    eigenvalues_le_of_quad h.1 (fun v => by simpa using (h.2 v).2) i⟩

theorem integral_traceMeasure {T : Matrix n n ℂ} (hT : T.IsHermitian) (f : BoundedContinuousFunction unitInterval ℝ) :
    ∫ t, f t ∂(traceMeasure T : Measure unitInterval) =
      ∑ i, (hT.eigenvalues i).toNNReal * f (toUnit (hT.eigenvalues i)) := by
  have hroots := hT.roots_charpoly_eq_eigenvalues
  have e : traceMeasure T = ∑ i, (hT.eigenvalues i).toNNReal •
      unitDirac (toUnit (hT.eigenvalues i)) := by
    rw [traceMeasure, hroots, Multiset.map_map]
    rfl
  rw [e, FiniteMeasure.toMeasure_sum, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure]
    simp [unitDirac, integral_dirac, NNReal.smul_def]
  · intro i _
    exact (f.integrable _)

/-- `F_{x,y}(T) = det(I - yT)/det(I + xT)` through the trace measure. For `0 ⪯ T ⪯ I`,
`x ≥ 0`, `0 ≤ y < 1`: `ratioDet x y T = transmissionRatio ![x] ![y] (traceMeasure T)`. -/
theorem ratioDet_eq_transmissionRatio {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {T : Matrix n n ℂ} (hT : IsUnitBand T) :
    ratioDet x y T = transmissionRatio ![x] ![y] (traceMeasure T) := by
  set lam := hT.1.eigenvalues
  have hmem := hT.eigenvalues_mem
  have h1 : ∀ i, 0 < 1 - y * lam i := fun i => by nlinarith [(hmem i).2, (hmem i).1]
  have h2 : ∀ i, 0 < 1 + x * lam i := fun i => by nlinarith [(hmem i).1]
  have hnum : (1 - (y : ℂ) • T).det = ((∏ i, (1 - y * lam i) : ℝ) : ℂ) := by
    rw [sub_eq_add_neg, ← neg_smul, det_one_add_smul_hermitian hT.1]
    push_cast; simp [lam, sub_eq_add_neg]
  have hden : (1 + (x : ℂ) • T).det = ((∏ i, (1 + x * lam i) : ℝ) : ℂ) := by
    rw [det_one_add_smul_hermitian hT.1]; push_cast; rfl
  have hR : ratioDet x y T = ∏ i, ((1 - y * lam i) / (1 + x * lam i)) := by
    rw [ratioDet, ratioDetC, hnum, hden, ← Complex.ofReal_div, Complex.ofReal_re,
      Finset.prod_div_distrib]
  rw [hR, transmissionRatio]
  have hI : ∫ t, ratioIntegrand ![x] ![y] (t : ℝ) ∂(traceMeasure T : Measure unitInterval) =
      ∑ i, ratioLog x y (lam i) := by
    have := integral_traceMeasure hT.1 (ratioBCF hx hy0 hy1)
    simp only [ratioBCF_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hu : ((toUnit (lam i) : unitInterval) : ℝ) = lam i := by
      simp only [toUnit, Set.projIcc]
      rw [min_eq_right (hmem i).2, max_eq_right (hmem i).1]
    rw [hu, Real.coe_toNNReal _ (hmem i).1, ratioIntegrand_one]
    split_ifs with h
    · change lam i * -(x + y) = ratioLog x y (lam i)
      rw [h, ratioLog_zero, zero_mul]
    · change lam i * (ratioLog x y (lam i) / lam i) = ratioLog x y (lam i)
      field_simp
  rw [hI, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ratioLog, Real.exp_sub, Real.exp_log (h1 i), Real.exp_log (h2 i)]

end BlockBand.Endpoints
