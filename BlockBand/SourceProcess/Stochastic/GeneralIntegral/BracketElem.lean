module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Fubini
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The bracket of elementary integrals

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2Integrator Q 𝓖 N α`,
horizon `T`, simple integrands `x : Rect 𝓖 T →₀ ℝ` with pointwise representative `elemFun x`.

* `brk2 α x y t ω = ∫_{(0,t]} (elemFun x)(elemFun y) α dr`; `aesm_brk2`: it is
  `𝓖_t`-a.e.-strongly measurable (bilinear induction; on rectangles it is
  `1_{A ∩ A'} ∫_{(s ∨ s', t ∧ t_r ∧ t_{r'}]} α`, a.e.-adapted by the bracket hypothesis).
* `setIntegral_elemProc_sq`: for `u ≤ v ≤ T`, `B ∈ 𝓖_u`,
  `∫_B (I_v(x)² - I_u(x)²) dQ = ∫_B (∫_{(0,v]} - ∫_{(0,u]}) (elemFun x)² α dr dQ`
  (restriction to `(u,v] × B`, isometry, Fubini).
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {N α : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

omit [IsFiniteMeasure Q] in
theorem aesm_indicator_sub {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : AEStronglyMeasurable[m] f Q) {s : Set Ω} (hs : MeasurableSet[m] s) :
    AEStronglyMeasurable[m] (s.indicator f) Q := by
  refine ⟨s.indicator (hf.mk f), hf.stronglyMeasurable_mk.indicator hs, ?_⟩
  filter_upwards [hf.ae_eq_mk] with ω hω
  by_cases hωs : ω ∈ s <;> simp [hωs, hω]

/-- Set-integral increment orthogonality for an `L²` martingale. -/
theorem setIntegral_mul_sub_eq_zero {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓖 Q) {a b : ℝ≥0}
    (hab : a ≤ b) (hb : MemLp (X b) 2 Q) {D : Set Ω} (hD : MeasurableSet[𝓖 a] D)
    {Y : Ω → ℝ} (hY : MemLp Y 2 Q) (hYm : AEStronglyMeasurable[𝓖 a] Y Q) :
    ∫ ω in D, Y ω * (X b ω - X a ω) ∂Q = 0 := by
  rw [← integral_indicator (𝓖.le a D hD)]
  rw [← integral_mul_sub_eq_zero hX hab hb (hY.indicator (𝓖.le a D hD).nullMeasurableSet)
    (aesm_indicator_sub hYm hD)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ D <;> simp [hω]

omit [IsFiniteMeasure Q] in
theorem norm_sq_eq_integral {μ : Measure (ℝ × Ω)} (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ p, (f p) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

omit [IsFiniteMeasure Q] in
theorem norm_sq_eq_integral' (f : Lp ℝ 2 Q) : ‖f‖ ^ 2 = ∫ ω, (f ω) ^ 2 ∂Q := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

/-- `∫_{(0,t]} (elemFun x)(elemFun y) α dr`. -/
def brk2 (α : ℝ≥0 → Ω → ℝ) (x y : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in Ioc (0 : ℝ) t, elemFun x (r, ω) * elemFun y (r, ω) * α r.toNNReal ω

namespace IsL2Integrator

omit [IsFiniteMeasure Q] in
theorem brk2_single_left (r : Rect 𝓖 T) (c : ℝ) (y : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    brk2 α (Finsupp.single r c) y t = fun ω => c * brk2 α (Finsupp.single r 1) y t ω := by
  funext ω
  simp only [brk2, elemFun_single, Pi.smul_apply, smul_eq_mul, one_mul, mul_assoc]
  exact integral_const_mul c _

omit [IsFiniteMeasure Q] in
theorem brk2_single_right (x : Rect 𝓖 T →₀ ℝ) (r : Rect 𝓖 T) (c : ℝ) (t : ℝ≥0) :
    brk2 α x (Finsupp.single r c) t = fun ω => c * brk2 α x (Finsupp.single r 1) t ω := by
  funext ω
  simp only [brk2, elemFun_single, Pi.smul_apply, smul_eq_mul, one_mul]
  rw [← integral_const_mul]
  congr 1; funext ρ; ring

omit [IsFiniteMeasure Q] in
theorem brk2_rect (r r' : Rect 𝓖 T) (t : ℝ≥0) (ω : Ω) :
    brk2 α (Finsupp.single r 1) (Finsupp.single r' 1) t ω =
      (r.A ∩ r'.A).indicator (bracketIntegral α (max r.s r'.s) (min t (min r.t r'.t))) ω := by
  have hI : Ioc (0 : ℝ) t ∩ (Ioc (r.s : ℝ) r.t ∩ Ioc (r'.s : ℝ) r'.t) =
      Ioc ((max r.s r'.s : ℝ≥0) : ℝ) ((min t (min r.t r'.t) : ℝ≥0) : ℝ) := by
    rw [Ioc_inter_Ioc, Ioc_inter_Ioc, NNReal.coe_max, NNReal.coe_min, NNReal.coe_min,
      max_eq_right (le_max_of_le_left r.s.coe_nonneg)]
  have hpt : ∀ ρ : ℝ, elemFun (Finsupp.single r 1) (ρ, ω) * elemFun (Finsupp.single r' 1) (ρ, ω) *
      α ρ.toNNReal ω = (r.A ∩ r'.A).indicator 1 ω *
        (Ioc (r.s : ℝ) r.t ∩ Ioc (r'.s : ℝ) r'.t).indicator (fun ρ => α ρ.toNNReal ω) ρ := by
    intro ρ
    simp only [elemFun_single, one_smul, Rect.set]
    by_cases h1 : ρ ∈ Ioc (r.s : ℝ) r.t <;> by_cases h2 : ρ ∈ Ioc (r'.s : ℝ) r'.t <;>
      by_cases h3 : ω ∈ r.A <;> by_cases h4 : ω ∈ r'.A <;> simp [h1, h2, h3, h4]
  simp only [brk2, hpt]
  rw [integral_const_mul, setIntegral_indicator (measurableSet_Ioc.inter measurableSet_Ioc), hI]
  by_cases hω : ω ∈ r.A ∩ r'.A <;> simp [hω, bracketIntegral]

omit [IsFiniteMeasure Q] in
theorem bracketTerm_elemFun (x : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    bracketTerm α (elemFun x) t = brk2 α x x t := by
  funext ω; simp only [bracketTerm, brk2, sq]

variable (h : IsL2Integrator Q 𝓖 N α)
include h

omit [IsFiniteMeasure Q] in
theorem integrableOn_elemFun_mul (x y : Rect 𝓖 T →₀ ℝ) : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun r : ℝ => elemFun x (r, ω) * elemFun y (r, ω) * α r.toNNReal ω)
      (Ioc 0 t) := by
  obtain ⟨C, hC⟩ := elemFun_bound x
  obtain ⟨D, hD⟩ := elemFun_bound y
  filter_upwards [h.alpha_integrable] with ω hω t
  refine (hω t).bdd_mul (c := C * D) ?_ (Eventually.of_forall fun r => ?_)
  · exact (((measurable_elemFun x).comp (measurable_id.prodMk measurable_const)).mul
      ((measurable_elemFun y).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hC _) (hD _) (abs_nonneg _) ((abs_nonneg _).trans (hC (r, ω)))

omit [IsFiniteMeasure Q] in
theorem brk2_add_left (x x' y : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    brk2 α (x + x') y t =ᵐ[Q] fun ω => brk2 α x y t ω + brk2 α x' y t ω := by
  filter_upwards [h.integrableOn_elemFun_mul x y, h.integrableOn_elemFun_mul x' y] with ω h1 h2
  simp only [brk2, map_add, Pi.add_apply, add_mul]
  exact integral_add (h1 t) (h2 t)

omit [IsFiniteMeasure Q] in
theorem brk2_add_right (x y y' : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    brk2 α x (y + y') t =ᵐ[Q] fun ω => brk2 α x y t ω + brk2 α x y' t ω := by
  filter_upwards [h.integrableOn_elemFun_mul x y, h.integrableOn_elemFun_mul x y'] with ω h1 h2
  simp only [brk2, map_add, Pi.add_apply, mul_add, add_mul]
  exact integral_add (h1 t) (h2 t)

omit [IsFiniteMeasure Q] in
/-- **A.e. adaptedness of elementary brackets.** -/
theorem aesm_brk2 (x y : Rect 𝓖 T →₀ ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[𝓖 t] (brk2 α x y t) Q := by
  have hzero : ∀ z : Rect 𝓖 T →₀ ℝ, brk2 α 0 z t = fun _ => 0 := fun z => by
    funext ω; simp [brk2]
  have hzero' : ∀ z : Rect 𝓖 T →₀ ℝ, brk2 α z 0 t = fun _ => 0 := fun z => by
    funext ω; simp [brk2]
  induction x using Finsupp.induction_linear with
  | zero => rw [hzero]; exact aestronglyMeasurable_const
  | add x x' hx hx' => exact (hx.add hx').congr (h.brk2_add_left x x' y t).symm
  | single r c =>
      rw [brk2_single_left]
      refine AEStronglyMeasurable.const_mul ?_ c
      induction y using Finsupp.induction_linear with
      | zero => rw [hzero']; exact aestronglyMeasurable_const
      | add y y' hy hy' => exact (hy.add hy').congr (h.brk2_add_right _ y y' t).symm
      | single r' c' =>
          rw [brk2_single_right]
          refine AEStronglyMeasurable.const_mul ?_ c'
          have he : brk2 α (Finsupp.single r 1) (Finsupp.single r' 1) t =
              (r.A ∩ r'.A).indicator (bracketIntegral α (max r.s r'.s) (min t (min r.t r'.t))) :=
            funext fun ω => brk2_rect r r' t ω
          rw [he]
          by_cases hab : max r.s r'.s ≤ min t (min r.t r'.t)
          · have hbt : min t (min r.t r'.t) ≤ t := min_le_left _ _
            refine aesm_indicator_sub ((h.aesm_bracketIntegral hab).mono (𝓖.mono hbt)) ?_
            exact (𝓖.mono ((le_max_left _ _).trans (hab.trans hbt)) _ r.hA).inter
              (𝓖.mono ((le_max_right _ _).trans (hab.trans hbt)) _ r'.hA)
          · have h0 : bracketIntegral α (max r.s r'.s) (min t (min r.t r'.t)) = fun _ => 0 := by
              funext ω
              rw [bracketIntegral, Ioc_eq_empty_of_le (by exact_mod_cast (not_le.1 hab).le),
                Measure.restrict_empty, integral_zero_measure]
            rw [h0]
            simpa using (aestronglyMeasurable_const : AEStronglyMeasurable[𝓖 t] (fun _ : Ω => (0 : ℝ)) Q)

/-- **Elementary bracket identity.** -/
theorem setIntegral_elemProc_sq (x : Rect 𝓖 T →₀ ℝ) {u v : ℝ≥0} (huv : u ≤ v) (hvT : v ≤ T)
    {B : Set Ω} (hB : MeasurableSet[𝓖 u] B) :
    ∫ ω in B, (elemProc N x v ω ^ 2 - elemProc N x u ω ^ 2) ∂Q =
      ∫ ω in B, (bracketTerm α (elemFun x) v ω - bracketTerm α (elemFun x) u ω) ∂Q := by
  have := h.isFiniteMeasure_bracketMeasure T
  have hBm : MeasurableSet B := 𝓖.le u B hB
  set P := elemProc h.mart x
  have hP : Martingale P 𝓖 Q := elemProc_martingale h.mart_martingale x
  have hPL : ∀ t, MemLp (P t) 2 Q := elemProc_memLp h.mart_memLp x
  -- left side via the martingale version
  have hL : ∫ ω in B, (elemProc N x v ω ^ 2 - elemProc N x u ω ^ 2) ∂Q =
      ∫ ω in B, (P v ω - P u ω) ^ 2 ∂Q + 2 * ∫ ω in B, P u ω * (P v ω - P u ω) ∂Q := by
    have i1 : Integrable (fun ω => (P v ω - P u ω) ^ 2) Q := ((hPL v).sub (hPL u)).integrable_sq
    have i2 : Integrable (fun ω => 2 * (P u ω * (P v ω - P u ω))) Q :=
      ((hPL u).integrable_mul ((hPL v).sub (hPL u))).const_mul 2
    rw [← integral_const_mul, ← integral_add i1.integrableOn i2.integrableOn]
    refine setIntegral_congr_ae hBm ?_
    filter_upwards [elemProc_ae h.mart_ae x v, elemProc_ae h.mart_ae x u] with ω h1 h2 _
    rw [← h1, ← h2]; ring
  rw [hL, setIntegral_mul_sub_eq_zero hP huv (hPL v) hB (hPL u)
    (hP.stronglyMeasurable u).aestronglyMeasurable, mul_zero, add_zero]
  -- the restricted integrand
  set y := restrictLin huv hvT hB x
  have h1 : ∫ ω in B, (P v ω - P u ω) ^ 2 ∂Q = ‖h.integrandLin T y‖ ^ 2 := by
    rw [← h.norm_valueLin, norm_sq_eq_integral', ← integral_indicator hBm]
    refine integral_congr_ae ?_
    filter_upwards [h.valueLin_ae T y] with ω hω
    rw [hω, elemProc_restrict]
    by_cases hω' : ω ∈ B <;> simp [hω', P]
  rw [h1, show ‖h.integrandLin T y‖ = ‖((h.integrandLin T y : PredL2 𝓖 (bracketMeasure Q α T)) :
    Lp ℝ 2 (bracketMeasure Q α T))‖ from rfl, norm_sq_eq_integral]
  have hS : MeasurableSet (Ioc (u : ℝ) v ×ˢ B) := measurableSet_Ioc.prod hBm
  have h2 : ∫ p, ((h.integrandLin T y : Lp ℝ 2 (bracketMeasure Q α T)) p) ^ 2
      ∂bracketMeasure Q α T = ∫ p, (Ioc (u : ℝ) v ×ˢ B).indicator 1 p * (elemFun x p) ^ 2
      ∂bracketMeasure Q α T := by
    refine integral_congr_ae ?_
    filter_upwards [integrandLin_ae h y] with p hp
    rw [hp, elemFun_restrict]
    by_cases hp' : p ∈ Ioc (u : ℝ) v ×ˢ B <;> simp [hp']
  obtain ⟨C, hC⟩ := elemFun_bound x
  have hint : Integrable (fun p => (Ioc (u : ℝ) v ×ˢ B).indicator 1 p * (elemFun x p) ^ 2)
      (bracketMeasure Q α T) := by
    refine Integrable.of_bound (((measurable_one.indicator hS).mul
      ((measurable_elemFun x).pow_const 2)).aestronglyMeasurable) (C ^ 2) ?_
    refine Eventually.of_forall fun p => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have : |(Ioc (u : ℝ) v ×ˢ B).indicator (1 : ℝ × Ω → ℝ) p| ≤ 1 := by
      by_cases hp' : p ∈ Ioc (u : ℝ) v ×ˢ B <;> simp [hp']
    calc _ ≤ 1 * C ^ 2 := mul_le_mul this (pow_le_pow_left₀ (abs_nonneg _) (hC p) 2)
          (by positivity) zero_le_one
      _ = C ^ 2 := one_mul _
  rw [h2, integral_bracketMeasure h.alpha_measurable h.alpha_nonneg hint,
    ← integral_indicator hBm]
  refine integral_congr_ae ?_
  filter_upwards [h.integrableOn_elemFun_mul x x] with ω hω
  have hsub : Ioc (u : ℝ) v ⊆ Ioc (0 : ℝ) T :=
    Ioc_subset_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 hvT)
  have hsplit : bracketTerm α (elemFun x) v ω - bracketTerm α (elemFun x) u ω =
      ∫ r in Ioc (u : ℝ) v, elemFun x (r, ω) * elemFun x (r, ω) * α r.toNNReal ω := by
    have hu : Ioc (0 : ℝ) u ∪ Ioc (u : ℝ) v = Ioc (0 : ℝ) v :=
      Ioc_union_Ioc_eq_Ioc u.coe_nonneg (NNReal.coe_le_coe.2 huv)
    simp only [bracketTerm, sq]
    rw [← hu, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hω u)
      ((hω v).mono_set (hu ▸ subset_union_right))]
    ring
  by_cases hωB : ω ∈ B
  · rw [indicator_of_mem hωB, hsplit]
    conv_rhs => rw [show Ioc (u : ℝ) v = Ioc (0 : ℝ) T ∩ Ioc (u : ℝ) v from
      (inter_eq_right.2 hsub).symm, ← setIntegral_indicator measurableSet_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    by_cases hr' : r ∈ Ioc (u : ℝ) v <;> simp [hr', hωB, indicator_of_mem, indicator_of_notMem]
    ring
  · rw [indicator_of_notMem hωB]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
    simp [hωB]

end IsL2Integrator

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
