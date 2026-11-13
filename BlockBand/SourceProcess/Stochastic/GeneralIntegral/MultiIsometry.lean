module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.MultiBracket
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Fubini
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Cross isometry for simple integrands

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖`, `h : IsL2IntegratorVec Q 𝓖 N a`
(`MultiBracket`), horizon `T`, simple predictable integrands `x, y : Rect 𝓖 T →₀ ℝ` with
pointwise representatives `elemFun x`, `elemFun y` and elementary integrals
`elemProc (N i) x T = ∑ x_r 1_{A_r} (N^i_{t_r} - N^i_{s_r})`.

`crossForm a i j T x y ω = ∫_{(0,T]} x(u,ω) y(u,ω) a^{ij}_u(ω) du` (signed density).

**`integral_elemProc_mul`** (cross isometry on simple integrands, possibly different for the
two coordinates): `E[∫_0^T x dN^i · ∫_0^T y dN^j] = E ∫_0^T x y a^{ij} ds`, together with
integrability of `crossForm`. Rectangle case: `setIntegral_coord_cross`; general case:
bilinearity (`crossForm` is a.s. bilinear, the left side is bilinear in `L²`).
For `x = y`, `i = j` this is the scalar isometry on simple integrands.
`integral_sq_sum_elemProc`: the vector isometry `E(∑_i ∫ x_i dN^i)² = E ∑_{ij} ∫ x_i x_j a^{ij}`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] {N : ι → ℝ≥0 → Ω → ℝ} {a : ι → ι → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

omit [Fintype ι] in
/-- The cross form `∫_{(0,T]} x y a^{ij}`. -/
def crossForm (a : ι → ι → ℝ≥0 → Ω → ℝ) (i j : ι) (T : ℝ≥0) (x y : Rect 𝓖 T →₀ ℝ)
    (ω : Ω) : ℝ :=
  ∫ u in Ioc (0 : ℝ) T, elemFun x (u, ω) * elemFun y (u, ω) * a i j u.toNNReal ω

omit [Fintype ι] in
theorem integrableOn_elemFun_mul {i j : ι} {ω : Ω}
    (hω : IntegrableOn (fun r : ℝ => a i j r.toNNReal ω) (Ioc 0 T)) (x y : Rect 𝓖 T →₀ ℝ) :
    IntegrableOn (fun u => elemFun x (u, ω) * elemFun y (u, ω) * a i j u.toNNReal ω)
      (Ioc 0 T) := by
  obtain ⟨C₁, hC₁⟩ := elemFun_bound x
  obtain ⟨C₂, hC₂⟩ := elemFun_bound y
  have hm : Measurable fun u : ℝ => elemFun x (u, ω) * elemFun y (u, ω) :=
    ((measurable_elemFun x).comp (measurable_id.prodMk measurable_const)).mul
      ((measurable_elemFun y).comp (measurable_id.prodMk measurable_const))
  refine hω.bdd_mul (c := C₁ * C₂) hm.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hC₁ _) (hC₂ _) (abs_nonneg _) ((abs_nonneg _).trans (hC₁ (u, ω)))

namespace IsL2IntegratorVec

omit [Fintype ι] in
theorem crossForm_add_left {i j : ι} (hint : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun r : ℝ => a i j r.toNNReal ω) (Ioc 0 t)) (x x' y : Rect 𝓖 T →₀ ℝ) :
    crossForm a i j T (x + x') y =ᵐ[Q] crossForm a i j T x y + crossForm a i j T x' y := by
  filter_upwards [hint] with ω hω
  simp only [crossForm, Pi.add_apply, map_add, add_mul]
  exact integral_add (integrableOn_elemFun_mul (hω T) x y) (integrableOn_elemFun_mul (hω T) x' y)

omit [Fintype ι] in
theorem crossForm_add_right {i j : ι} (hint : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntegrableOn (fun r : ℝ => a i j r.toNNReal ω) (Ioc 0 t)) (x y y' : Rect 𝓖 T →₀ ℝ) :
    crossForm a i j T x (y + y') =ᵐ[Q] crossForm a i j T x y + crossForm a i j T x y' := by
  filter_upwards [hint] with ω hω
  simp only [crossForm, Pi.add_apply, map_add, mul_add, add_mul]
  exact integral_add (integrableOn_elemFun_mul (hω T) x y) (integrableOn_elemFun_mul (hω T) x y')

set_option linter.unusedSimpArgs false in
omit [Fintype ι] in
theorem crossForm_single {i j : ι} (r r' : Rect 𝓖 T) (c c' : ℝ) (ω : Ω) :
    crossForm a i j T (Finsupp.single r c) (Finsupp.single r' c') ω =
      c * c' * (r.A ∩ r'.A).indicator (fun ω => ∫ u in Ioc ((max r.s r'.s : ℝ≥0) : ℝ)
        (max (max r.s r'.s) (min r.t r'.t) : ℝ≥0), a i j u.toNNReal ω) ω := by
  have hI : Ioc (r.s : ℝ) r.t ∩ Ioc (r'.s : ℝ) r'.t =
      Ioc ((max r.s r'.s : ℝ≥0) : ℝ) (max (max r.s r'.s) (min r.t r'.t) : ℝ≥0) := by
    rw [Ioc_inter_Ioc, ← NNReal.coe_max, ← NNReal.coe_min]
    ext u
    simp only [mem_Ioc, NNReal.coe_max]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_max_of_le_right h2⟩
    · rintro ⟨h1, h2⟩
      rcases le_max_iff.1 h2 with h | h
      · exact absurd h (not_le.2 h1)
      · exact ⟨h1, h⟩
  have hsub : Ioc (r.s : ℝ) r.t ∩ Ioc (r'.s : ℝ) r'.t ⊆ Ioc (0 : ℝ) T :=
    fun u hu => ⟨(NNReal.coe_nonneg _).trans_lt hu.1.1, hu.1.2.trans (by exact_mod_cast r.htT)⟩
  have hpt : ∀ u, elemFun (Finsupp.single r c) (u, ω) * elemFun (Finsupp.single r' c') (u, ω) *
      a i j u.toNNReal ω = c * c' * ((r.A ∩ r'.A).indicator (fun _ => (1 : ℝ)) ω *
        (Ioc (r.s : ℝ) r.t ∩ Ioc (r'.s : ℝ) r'.t).indicator (fun u => a i j u.toNNReal ω) u) := by
    intro u
    classical
    by_cases hu1 : u ∈ Ioc (r.s : ℝ) r.t <;> by_cases hu2 : u ∈ Ioc (r'.s : ℝ) r'.t <;>
      by_cases hω1 : ω ∈ r.A <;> by_cases hω2 : ω ∈ r'.A <;>
      simp [elemFun_single, Rect.set, indicator_apply, hu1, hu2, hω1, hω2]
  rw [crossForm, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_const_mul, setIntegral_indicator (measurableSet_Ioc.inter measurableSet_Ioc),
    inter_eq_right.2 hsub, hI]
  by_cases hω : ω ∈ r.A ∩ r'.A
  · simp [indicator_of_mem hω]
  · simp [indicator_of_notMem hω]

variable [IsFiniteMeasure Q] (h : IsL2IntegratorVec Q 𝓖 N a)
include h

theorem integral_rect_mul (i j : ι) (r r' : Rect 𝓖 T) (c c' : ℝ) :
    Integrable (crossForm a i j T (Finsupp.single r c) (Finsupp.single r' c')) Q ∧
    ∫ ω, elemProc (N i) (Finsupp.single r c) T ω * elemProc (N j) (Finsupp.single r' c') T ω ∂Q =
      ∫ ω, crossForm a i j T (Finsupp.single r c) (Finsupp.single r' c') ω ∂Q := by
  have hD : MeasurableSet[𝓖 (max r.s r'.s)] (r.A ∩ r'.A) :=
    (𝓖.mono (le_max_left _ _) _ r.hA).inter (𝓖.mono (le_max_right _ _) _ r'.hA)
  have hDm : MeasurableSet (r.A ∩ r'.A) := 𝓖.le _ _ hD
  have hfun : crossForm a i j T (Finsupp.single r c) (Finsupp.single r' c') = fun ω =>
      c * c' * (r.A ∩ r'.A).indicator (fun ω => ∫ u in Ioc ((max r.s r'.s : ℝ≥0) : ℝ)
        (max (max r.s r'.s) (min r.t r'.t) : ℝ≥0), a i j u.toNNReal ω) ω :=
    funext (crossForm_single r r' c c')
  rw [hfun]
  have hB := (h.crossB_sub i j (le_max_left (max r.s r'.s) (min r.t r'.t)))
  have hint : Integrable (fun ω => ∫ u in Ioc ((max r.s r'.s : ℝ≥0) : ℝ)
      (max (max r.s r'.s) (min r.t r'.t) : ℝ≥0), a i j u.toNNReal ω) Q :=
    (((h.crossPair i j).intB _).sub ((h.crossPair i j).intB _)).congr hB
  refine ⟨(hint.indicator hDm).const_mul _, ?_⟩
  rw [integral_const_mul, integral_indicator hDm, ← h.setIntegral_coord_cross i j r.hst r'.hst hD,
    ← integral_const_mul, ← integral_indicator hDm]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [elemProc_single, Pi.smul_apply, smul_eq_mul, rectProc_T]
  by_cases h1 : ω ∈ r.A <;> by_cases h2 : ω ∈ r'.A <;>
    simp [h1, h2, indicator_of_mem, indicator_of_notMem, mul_comm, mul_left_comm, mul_assoc]

/-- **Cross isometry on simple integrands.** -/
theorem integral_elemProc_mul (i j : ι) (x y : Rect 𝓖 T →₀ ℝ) :
    Integrable (crossForm a i j T x y) Q ∧
    ∫ ω, elemProc (N i) x T ω * elemProc (N j) y T ω ∂Q =
      ∫ ω, crossForm a i j T x y ω ∂Q := by
  have hL (x y : Rect 𝓖 T →₀ ℝ) : Integrable (fun ω => elemProc (N i) x T ω *
      elemProc (N j) y T ω) Q :=
    (elemProc_memLp (h.coord i).memLp x T).integrable_mul (elemProc_memLp (h.coord j).memLp y T)
  induction x using Finsupp.induction_linear with
  | zero =>
      have h0 : crossForm a i j T 0 y = 0 := by funext ω; simp [crossForm]
      simp [h0]
  | add x x' hx hx' =>
      have he := crossForm_add_left (h.integrable i j) x x' y
      refine ⟨(hx.1.add hx'.1).congr he.symm, ?_⟩
      rw [integral_congr_ae he, integral_add' hx.1 hx'.1, ← hx.2, ← hx'.2,
        ← integral_add (hL x y) (hL x' y)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [map_add, Pi.add_apply, add_mul]
  | single r c =>
      induction y using Finsupp.induction_linear with
      | zero =>
          have h0 : crossForm a i j T (Finsupp.single r c) 0 = 0 := by funext ω; simp [crossForm]
          simp [h0]
      | add y y' hy hy' =>
          have he := crossForm_add_right (h.integrable i j) (Finsupp.single r c) y y'
          refine ⟨(hy.1.add hy'.1).congr he.symm, ?_⟩
          rw [integral_congr_ae he, integral_add' hy.1 hy'.1, ← hy.2, ← hy'.2,
            ← integral_add (hL _ y) (hL _ y')]
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [map_add, Pi.add_apply, mul_add]
      | single r' c' => exact h.integral_rect_mul i j r r' c c'

/-- **Vector isometry on simple integrands**:
`E(∑_i ∫_0^T x_i dN^i)² = E ∑_{ij} ∫_0^T x_i x_j a^{ij} ds`. -/
theorem integral_sq_sum_elemProc (x : ι → Rect 𝓖 T →₀ ℝ) :
    ∫ ω, (∑ i, elemProc (N i) (x i) T ω) ^ 2 ∂Q =
      ∫ ω, ∑ i, ∑ j, crossForm a i j T (x i) (x j) ω ∂Q := by
  have hL (i j : ι) : Integrable (fun ω => elemProc (N i) (x i) T ω *
      elemProc (N j) (x j) T ω) Q :=
    (elemProc_memLp (h.coord i).memLp (x i) T).integrable_mul
      (elemProc_memLp (h.coord j).memLp (x j) T)
  have hsq : (fun ω => (∑ i, elemProc (N i) (x i) T ω) ^ 2) =
      fun ω => ∑ i, ∑ j, elemProc (N i) (x i) T ω * elemProc (N j) (x j) T ω := by
    funext ω; rw [sq, Finset.sum_mul_sum]
  rw [hsq, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hL i j,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (h.integral_elemProc_mul i j (x i) (x j)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hL i j,
    integral_finsetSum _ fun j _ => (h.integral_elemProc_mul i j (x i) (x j)).1]
  exact Finset.sum_congr rfl fun j _ => (h.integral_elemProc_mul i j (x i) (x j)).2

end IsL2IntegratorVec

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
