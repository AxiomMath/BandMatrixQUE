module
public import BlockBand.SourceProcess.Stochastic.Representation.Mul
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Associativity of the general vector stochastic integral

Setting: `(Ω, m₀, Q)` with `Q` finite, raw filtration `𝓖` (no usual conditions), a vector
integrator `h : IsL2IntegratorVec Q 𝓖 Z a` (finite index `ι`), a horizon `T`, and a bounded
raw-predictable matrix integrand `H : κ → ι → ℝ × Ω → ℝ` (`IsBddPred`). Let
`X^k = ∑_i ∫_0^· H_{ki} dZ^i` (`h.vecCont T`). Let `hX : IsL2IntegratorVec Q 𝓖 X' c` be **any**
vector integrator structure on a process `X'` with `X'^k_t = X^k_t` a.s. for every `t ≤ T`
(e.g. a Brownian motion constructed from `X`; the density `c` is arbitrary).

* `vecIntegral_predInd_rect`: `∫_0^T 1_{(s,t] × A} G dZ = 1_A (∫_0^t G dZ - ∫_0^s G dZ)` a.s.
* `vecIntegral_Iic`: `∫_0^T 1_{[0,t]} G dZ = ∫_0^t G dZ` a.s.
* **`vecIntegral_assoc`** (terminal form, equality in `L²(Q)`): for every bounded predictable
  `K : κ → ℝ × Ω → ℝ`, `∑_k ∫_0^T K_k dX'^k = ∑_i ∫_0^T (∑_k H_{ki} K_k) dZ^i`.
* **`vecCont_assoc`**: the same a.s. simultaneously for all times `t`.

Proof: both sides are continuous linear in `K` (for `L²(ν̄_c + ν̄_a)` approximation); they agree
on simple integrands by the rectangle identity, and simple integrands are dense
(`denseRange_simpleLin`). The density `c` of `X'` never has to be identified with `H a Hᵀ`.
-/

namespace BlockBand.SourceProcess.Stochastic.Representation
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsFiniteMeasure Q]
  {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] {Z : ι → ℝ≥0 → Ω → ℝ}
  {a : ι → ι → ℝ≥0 → Ω → ℝ}

/-- The vector integral as a continuous linear map. -/
def vecIntegralL (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0) :
    (ι → PredL2 𝓖 (barMeasure Q a T)) →L[ℝ] Lp ℝ 2 Q :=
  ∑ i, (h.coordInt T i).comp (ContinuousLinearMap.proj i)

theorem vecIntegralL_apply (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0)
    (G : ι → PredL2 𝓖 (barMeasure Q a T)) : vecIntegralL h T G = h.vecIntegral T G := by
  simp [vecIntegralL, IsL2IntegratorVec.vecIntegral]

theorem vecIntegral_coeFn (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0)
    (G : ι → PredL2 𝓖 (barMeasure Q a T)) :
    (h.vecIntegral T G : Ω → ℝ) =ᵐ[Q] fun ω => ∑ i, (h.coordInt T i (G i) : Ω → ℝ) ω :=
  Lp.coeFn_fun_finsetSum Finset.univ fun i => h.coordInt T i (G i)

omit [IsFiniteMeasure Q] in
theorem restr_predInd (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0) (i : ι) {R : Set (ℝ × Ω)}
    (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R) (G : PredL2 𝓖 (barMeasure Q a T)) :
    h.restr T i (predInd 𝓖 R hR G) = predInd 𝓖 R hR (h.restr T i G) :=
  predRestrict_predInd 𝓖 _ hR G

/-- **Rectangle identity for the vector integral.** -/
theorem vecIntegral_predInd_rect (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0)
    (G : ι → PredL2 𝓖 (barMeasure Q a T)) (r : Rect 𝓖 T) :
    (h.vecIntegral T (fun i => predInd 𝓖 r.set r.measurableSet_pred (G i)) : Ω → ℝ) =ᵐ[Q]
      r.A.indicator fun ω => h.vecCont T G r.t ω - h.vecCont T G r.s ω := by
  have hi (i : ι) := (h.coord i).stochIntegral_predInd_rect T (h.restr T i (G i)) r.hst r.hA
  filter_upwards [vecIntegral_coeFn h T (fun i => predInd 𝓖 r.set r.measurableSet_pred (G i)),
    ae_all_iff.2 hi] with ω h1 h2
  rw [h1]
  have e (i : ι) : (h.coordInt T i (predInd 𝓖 r.set r.measurableSet_pred (G i)) : Ω → ℝ) ω =
      r.A.indicator (fun ω => (h.coord i).contIntegral T (h.restr T i (G i)) r.t ω -
        (h.coord i).contIntegral T (h.restr T i (G i)) r.s ω) ω := by
    rw [← h2 i]
    change ((h.coord i).stochIntegral T (h.restr T i (predInd 𝓖 r.set _ (G i))) : Ω → ℝ) ω = _
    rw [restr_predInd]
    rfl
  simp only [e]
  by_cases hω : ω ∈ r.A
  · simp only [indicator_of_mem hω, IsL2IntegratorVec.vecCont, Finset.sum_sub_distrib]
  · simp only [indicator_of_notMem hω, Finset.sum_const_zero]

/-- **Deterministic times**: `∫_0^T 1_{[0,t]} G dZ = ∫_0^t G dZ` a.s. -/
theorem vecIntegral_Iic (h : IsL2IntegratorVec Q 𝓖 Z a) (T : ℝ≥0)
    (G : ι → PredL2 𝓖 (barMeasure Q a T)) (t : ℝ≥0) :
    (h.vecIntegral T (fun i => predInd 𝓖 _ (measurableSet_Iic_prod_univ 𝓖 t) (G i)) : Ω → ℝ)
      =ᵐ[Q] h.vecCont T G t := by
  have hi (i : ι) := (h.coord i).stochIntegral_predInd_Iic T (h.restr T i (G i)) t
  filter_upwards [vecIntegral_coeFn h T _, ae_all_iff.2 hi] with ω h1 h2
  rw [h1, IsL2IntegratorVec.vecCont]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h2 i]
  change ((h.coord i).stochIntegral T (h.restr T i (predInd 𝓖 _ _ (G i))) : Ω → ℝ) ω = _
  rw [restr_predInd]

theorem bpL2_indicator {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f : ℝ × Ω → ℝ}
    (hf : IsBddPred 𝓖 f) {R : Set (ℝ × Ω)} (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R) :
    bpL2 μ (hf.indicator hR) = predInd 𝓖 R hR (bpL2 μ hf) := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [bpL2_coeFn (μ := μ) (hf.indicator hR), predInd_coeFn 𝓖 R hR (bpL2 μ hf),
    bpL2_coeFn (μ := μ) hf] with p h1 h2 h3
  rw [h1, h2]
  by_cases hp : p ∈ R
  · rw [indicator_of_mem hp, indicator_of_mem hp, h3]
  · rw [indicator_of_notMem hp, indicator_of_notMem hp]

theorem bpL2_sum {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {κ : Type*} [Fintype κ]
    {f : κ → ℝ × Ω → ℝ} (hf : ∀ k, IsBddPred 𝓖 (f k)) :
    bpL2 μ (IsBddPred.sum Finset.univ hf) = ∑ k, bpL2 μ (hf k) := by
  refine predL2_ext 𝓖 ?_
  have hs : ((∑ k, bpL2 μ (hf k) : PredL2 𝓖 μ) : Lp ℝ 2 μ) =
      ∑ k, ((bpL2 μ (hf k) : PredL2 𝓖 μ) : Lp ℝ 2 μ) :=
    Submodule.coe_sum _ _ _
  rw [hs]
  filter_upwards [bpL2_coeFn (μ := μ) (IsBddPred.sum Finset.univ hf),
    Lp.coeFn_fun_finsetSum Finset.univ fun k => ((bpL2 μ (hf k) : PredL2 𝓖 μ) : Lp ℝ 2 μ),
    ae_all_iff.2 fun k => bpL2_coeFn (μ := μ) (hf k)] with p h1 h2 h3
  rw [h1, h2]
  exact Finset.sum_congr rfl fun k _ => (h3 k).symm

theorem predRestrict_bpL2 {μ μ' : Measure (ℝ × Ω)} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hle : μ ≤ μ') {f : ℝ × Ω → ℝ} (hf : IsBddPred 𝓖 f) :
    predRestrict 𝓖 hle (bpL2 μ' hf) = bpL2 μ hf := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predRestrict_coeFn 𝓖 hle (bpL2 μ' hf),
    (bpL2_coeFn (μ := μ') hf).filter_mono (ae_mono hle), bpL2_coeFn (μ := μ) hf] with p h1 h2 h3
  rw [h1, h2, h3]

theorem predRestrict_simpleLin {μ μ' : Measure (ℝ × Ω)} [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (hle : μ ≤ μ') (T : ℝ≥0) (x : Rect 𝓖 T →₀ ℝ) :
    predRestrict 𝓖 hle (simpleLin 𝓖 T μ' x) = simpleLin 𝓖 T μ x := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predRestrict_coeFn 𝓖 hle (simpleLin 𝓖 T μ' x),
    (simpleLin_ae (μ := μ') x).filter_mono (ae_mono hle), simpleLin_ae (μ := μ) x]
    with p h1 h2 h3
  rw [h1, h2, h3]

theorem predMul_simpleLin_single {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {g : ℝ × Ω → ℝ}
    (hg : IsBddPred 𝓖 g) {T : ℝ≥0} (r : Rect 𝓖 T) (c : ℝ) :
    predMul 𝓖 hg (simpleLin 𝓖 T μ (Finsupp.single r c)) =
      c • predInd 𝓖 r.set r.measurableSet_pred (bpL2 μ hg) := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predMul_coeFn hg (simpleLin 𝓖 T μ (Finsupp.single r c)),
    simpleLin_ae (μ := μ) (Finsupp.single r c),
    Lp.coeFn_smul c ((predInd 𝓖 r.set r.measurableSet_pred (bpL2 μ hg) : PredL2 𝓖 μ) :
      Lp ℝ 2 μ),
    predInd_coeFn 𝓖 r.set r.measurableSet_pred (bpL2 μ hg), bpL2_coeFn (μ := μ) hg]
    with p h1 h2 h3 h4 h5
  have e : (((c • predInd 𝓖 r.set r.measurableSet_pred (bpL2 μ hg) : PredL2 𝓖 μ) :
      Lp ℝ 2 μ) : ℝ × Ω → ℝ) = ⇑(c • ((predInd 𝓖 r.set r.measurableSet_pred (bpL2 μ hg) :
        PredL2 𝓖 μ) : Lp ℝ 2 μ)) := rfl
  rw [e, h3, h1, h2, Pi.smul_apply, h4, elemFun_single]
  by_cases hp : p ∈ r.set
  · simp [indicator_of_mem hp, h5]; ring
  · simp [indicator_of_notMem hp]

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {X : κ → ℝ≥0 → Ω → ℝ}
  {c : κ → κ → ℝ≥0 → Ω → ℝ}

/-- **Associativity of the vector integral** (terminal values, equality in `L²(Q)`):
`∑_k ∫_0^T K_k dX'^k = ∑_i ∫_0^T (∑_k H_{ki} K_k) dZ^i` for bounded predictable `H`, `K`, when
`X'^k_t = ∑_i ∫_0^t H_{ki} dZ^i` a.s. for every `t ≤ T`. -/
theorem vecIntegral_assoc (h : IsL2IntegratorVec Q 𝓖 Z a) (hX : IsL2IntegratorVec Q 𝓖 X c)
    (T : ℝ≥0) [IsFiniteMeasure (barMeasure Q a T)] [IsFiniteMeasure (barMeasure Q c T)]
    {H : κ → ι → ℝ × Ω → ℝ} (hH : ∀ k i, IsBddPred 𝓖 (H k i))
    (hXH : ∀ k, ∀ t ≤ T, X k t =ᵐ[Q] h.vecCont T (fun i => bpL2 _ (hH k i)) t)
    {K : κ → ℝ × Ω → ℝ} (hK : ∀ k, IsBddPred 𝓖 (K k)) :
    hX.vecIntegral T (fun k => bpL2 _ (hK k)) =
      h.vecIntegral T (fun i => bpL2 _ (IsBddPred.sum Finset.univ fun k => (hH k i).mul (hK k))) := by
  set μc := barMeasure Q c T
  set μa := barMeasure Q a T
  set μ := μc + μa
  have hca : μc ≤ μ := Measure.le_add_right le_rfl
  have haa : μa ≤ μ := Measure.le_add_left le_rfl
  -- the two sides as continuous linear maps of `K ∈ PredL2(μ)^κ`
  let Mmat : (κ → PredL2 𝓖 μa) →L[ℝ] (ι → PredL2 𝓖 μa) :=
    ContinuousLinearMap.pi fun i => ∑ k, (predMul 𝓖 (hH k i)).comp (ContinuousLinearMap.proj k)
  let Φ : (κ → PredL2 𝓖 μ) →L[ℝ] Lp ℝ 2 Q := (vecIntegralL hX T).comp
    (ContinuousLinearMap.pi fun k => (predRestrict 𝓖 hca).comp (ContinuousLinearMap.proj k))
  let Ψ : (κ → PredL2 𝓖 μ) →L[ℝ] Lp ℝ 2 Q := ((vecIntegralL h T).comp Mmat).comp
    (ContinuousLinearMap.pi fun k => (predRestrict 𝓖 haa).comp (ContinuousLinearMap.proj k))
  have hΦ (F : κ → PredL2 𝓖 μ) : Φ F = hX.vecIntegral T fun k => predRestrict 𝓖 hca (F k) := by
    simp [Φ, vecIntegralL_apply]
  have hΨ (F : κ → PredL2 𝓖 μ) : Ψ F = h.vecIntegral T fun i =>
      ∑ k, predMul 𝓖 (hH k i) (predRestrict 𝓖 haa (F k)) := by
    simp [Ψ, Mmat, vecIntegralL_apply]
  -- agreement on simple integrands
  let S : (κ → Rect 𝓖 T →₀ ℝ) → (κ → PredL2 𝓖 μ) := Pi.map fun _ => simpleLin 𝓖 T μ
  have hsingle (k : κ) (r : Rect 𝓖 T) (v : ℝ) :
      Φ (Pi.single k (simpleLin 𝓖 T μ (Finsupp.single r v))) =
        Ψ (Pi.single k (simpleLin 𝓖 T μ (Finsupp.single r v))) := by
    rw [hΦ, hΨ]
    have e1 : (fun k' => predRestrict 𝓖 hca ((Pi.single k (simpleLin 𝓖 T μ
        (Finsupp.single r v)) : κ → PredL2 𝓖 μ) k')) =
        Pi.single k (simpleLin 𝓖 T μc (Finsupp.single r v)) := by
      funext k'
      by_cases hk : k' = k
      · subst hk; simp [predRestrict_simpleLin]
      · simp [hk]
    have e2 : (fun i => ∑ k', predMul 𝓖 (hH k' i) (predRestrict 𝓖 haa
        ((Pi.single k (simpleLin 𝓖 T μ (Finsupp.single r v)) : κ → PredL2 𝓖 μ) k'))) =
        v • fun i => predInd 𝓖 r.set r.measurableSet_pred (bpL2 μa (hH k i)) := by
      funext i
      rw [Finset.sum_eq_single k (fun k' _ hk => by simp [hk]) (by simp)]
      simp only [Pi.single_eq_same, predRestrict_simpleLin, Pi.smul_apply]
      exact predMul_simpleLin_single (hH k i) r v
    have hsm : ∀ G : ι → PredL2 𝓖 μa, h.vecIntegral T (v • G) = v • h.vecIntegral T G :=
      fun G => by rw [← vecIntegralL_apply, map_smul, vecIntegralL_apply]
    rw [e1, e2, hsm]
    refine Lp.ext ?_
    have hL : (hX.vecIntegral T (Pi.single k (simpleLin 𝓖 T μc (Finsupp.single r v))) :
        Ω → ℝ) =ᵐ[Q] elemProc (X k) (Finsupp.single r v) T := by
      have e : hX.vecIntegral T (Pi.single k (simpleLin 𝓖 T μc (Finsupp.single r v))) =
          hX.coordInt T k (simpleLin 𝓖 T μc (Finsupp.single r v)) := by
        rw [IsL2IntegratorVec.vecIntegral,
          Finset.sum_eq_single k (fun k' _ hk => by simp [hk]) (by simp), Pi.single_eq_same]
      rw [e]
      exact hX.coordInt_simple_ae T k (Finsupp.single r v)
    filter_upwards [hL, Lp.coeFn_smul v (h.vecIntegral T fun i =>
        predInd 𝓖 r.set r.measurableSet_pred (bpL2 μa (hH k i))),
      vecIntegral_predInd_rect h T (fun i => bpL2 μa (hH k i)) r,
      hXH k r.t r.htT, hXH k r.s (r.hst.trans r.htT)] with ω h1 h2 h3 h4 h5
    rw [h1, h2, Pi.smul_apply, h3, elemProc_apply, Finsupp.sum_single_index (by simp),
      rectProc, Rect.clamp_T, smul_eq_mul]
    by_cases hω : ω ∈ r.A
    · simp only [indicator_of_mem hω, h4, h5]; rfl
    · simp only [indicator_of_notMem hω]
  have hS : Φ ∘ S = Ψ ∘ S := by
    funext x
    have hlin : ∀ x : κ → Rect 𝓖 T →₀ ℝ, S x = ∑ k, Pi.single k (simpleLin 𝓖 T μ (x k)) := by
      intro x; funext k'; simp [S, Finset.sum_apply, Pi.single_apply]
    simp only [Function.comp_apply, hlin, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    induction x k using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz => simp only [map_add, Pi.single_add, hy, hz]
    | single r v => exact hsingle k r v
  have hdense : DenseRange S := DenseRange.piMap fun _ =>
    denseRange_simpleLin (ae_add_measure_iff.2 ⟨IsL2Integrator.bracketMeasure_ae_mem Q _ T,
      IsL2Integrator.bracketMeasure_ae_mem Q _ T⟩)
  have hΦΨ : Φ = Ψ := DFunLike.coe_injective
    (hdense.equalizer Φ.continuous Ψ.continuous hS)
  have key := congrArg (fun L : (κ → PredL2 𝓖 μ) →L[ℝ] Lp ℝ 2 Q => L fun k => bpL2 μ (hK k))
    hΦΨ
  simp only [hΦ, hΨ, predRestrict_bpL2] at key
  rw [key]
  congr 1
  funext i
  rw [bpL2_sum (fun k => (hH k i).mul (hK k))]
  exact Finset.sum_congr rfl fun k _ => predMul_bpL2 (hH k i) (hK k)

/-- **Associativity of the vector integral, process form**: a.s. for all `t`,
`∑_k ∫_0^t K_k dX'^k = ∑_i ∫_0^t (∑_k H_{ki} K_k) dZ^i`. -/
theorem vecCont_assoc (h : IsL2IntegratorVec Q 𝓖 Z a) (hX : IsL2IntegratorVec Q 𝓖 X c)
    (T : ℝ≥0) [IsFiniteMeasure (barMeasure Q a T)] [IsFiniteMeasure (barMeasure Q c T)]
    {H : κ → ι → ℝ × Ω → ℝ} (hH : ∀ k i, IsBddPred 𝓖 (H k i))
    (hXH : ∀ k, ∀ t ≤ T, X k t =ᵐ[Q] h.vecCont T (fun i => bpL2 _ (hH k i)) t)
    {K : κ → ℝ × Ω → ℝ} (hK : ∀ k, IsBddPred 𝓖 (K k)) :
    ∀ᵐ ω ∂Q, ∀ t, hX.vecCont T (fun k => bpL2 _ (hK k)) t ω =
      h.vecCont T (fun i => bpL2 _ (IsBddPred.sum Finset.univ fun k => (hH k i).mul (hK k))) t ω := by
  refine ae_forall_eq_of_continuous (hX.vecCont_spec T _).1 (h.vecCont_spec T _).1 fun t => ?_
  have hR := measurableSet_Iic_prod_univ 𝓖 t
  have hK' (k : κ) := (hK k).indicator hR
  have e := vecIntegral_assoc h hX T hH hXH hK'
  have e2 : (fun i => bpL2 (barMeasure Q a T)
      (IsBddPred.sum Finset.univ fun k => (hH k i).mul (hK' k))) =
      fun i => predInd 𝓖 _ hR (bpL2 (barMeasure Q a T)
        (IsBddPred.sum Finset.univ fun k => (hH k i).mul (hK k))) := by
    funext i
    rw [← bpL2_indicator]
    refine bpL2_congr _ _ (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Iic (t : ℝ) ×ˢ (univ : Set Ω)
    · simp [indicator_of_mem hp]
    · simp [indicator_of_notMem hp]
  have e1 : (fun k => bpL2 (barMeasure Q c T) (hK' k)) =
      fun k => predInd 𝓖 _ hR (bpL2 (barMeasure Q c T) (hK k)) := by
    funext k; exact bpL2_indicator (hK k) hR
  rw [e1, e2] at e
  have h1 := vecIntegral_Iic hX T (fun k => bpL2 (barMeasure Q c T) (hK k)) t
  have h2 := vecIntegral_Iic h T (fun i => bpL2 (barMeasure Q a T)
    (IsBddPred.sum Finset.univ fun k => (hH k i).mul (hK k))) t
  rw [e] at h1
  exact h1.symm.trans h2

end BlockBand.SourceProcess.Stochastic.Representation
