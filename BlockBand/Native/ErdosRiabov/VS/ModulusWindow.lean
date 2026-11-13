module

public import BlockBand.Native.ErdosRiabov.VS.TailSum
public import BlockBand.Native.ErdosRiabov.Stochastic.ExpTailCoord

set_option autoImplicit false

/-!
# Window tails of the VS coordinates

Exponential tail bounds for increments of the VS coordinates over a time window.

The exponential tail `measure_exists_abs_compensated_ge_le` controls `sup_{t ≤ T} |N_t|` for
martingale parts
started at time `0`. For increments over a window `[r, r + L]` the coordinate `Y^i` is multiplied
by a smooth time cutoff `winCut r L` (`0` on `(-∞, r - L]`, `1` on `[r, ∞)`):
`X_u = winCut(u) Y^i_u` is a continuous semimartingale (`vsNoise_linComb_ito`) whose martingale
part `M` satisfies `M_u - M_r = Y^i_u - Y^i_r` for `u ≥ r` a.s. (its drift vanishes after `r`,
`itoDrift_winFn_eq_zero`) and has bracket `v_i winCut² ≤ 𝟙_{(r-L, ∞)}`, so
`∫_0^t ≤ 2L` for `t ≤ r + L` (`integral_winCut_sq_le`).

* `ringVariance_le_one`: `v_i ≤ 1`.
* **`measure_window_le`**: for `r, L ∈ ℝ≥0`, `L > 0`, every coordinate `i` and `λ ≥ 0`,
  `P(∃ u ∈ [r, r + L], λ ≤ |Y^i_u - Y^i_r|) ≤ 2 exp(-λ²/(16 L))`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal ENNReal

/-!
### Variances are at most one
-/

theorem entryVariance_le_one (p : BlockBand.Parameters) (x y : p.Site) :
    p.entryVariance x y ≤ 1 := by
  have hW : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hb := p.b_lt_half
  have hb0 := p.b_pos
  unfold BlockBand.Parameters.entryVariance BlockBand.Parameters.c
  split_ifs
  · exact div_le_one_of_le₀ (by linarith) (by linarith)
  · exact div_le_one_of_le₀ (by linarith) (by linarith)
  · norm_num

theorem ringVariance_le_one (p : BlockBand.Parameters) (i : Fin (ringDim p)) :
    ringVariance p i ≤ 1 := by
  obtain ⟨c, rfl⟩ := (ringEquiv p).surjective i
  rcases c with x | ⟨x, y, b⟩
  · rw [ringVariance_diag]
    exact entryVariance_le_one p x x
  · by_cases h : p.siteIndex x < p.siteIndex y
    · rw [ringVariance_offDiag_of_lt p h b]
      linarith [entryVariance_le_one p x y, p.entryVariance_nonneg x y]
    · rw [ringVariance_offDiag_of_not_lt p h b]
      norm_num

/-!
### The smooth window cutoff
-/

/-- `winCut r L u = ψ((u - (r - L))/L)`: `0` for `u ≤ r - L`, `1` for `u ≥ r`. -/
def winCut (r L u : ℝ) : ℝ := Real.smoothTransition ((u - (r - L)) / L)

theorem winCut_of_le {r L u : ℝ} (hL : 0 < L) (hu : u ≤ r - L) : winCut r L u = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)

theorem winCut_of_ge {r L u : ℝ} (hL : 0 < L) (hu : r ≤ u) : winCut r L u = 1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ hL).2 (by linarith))

theorem winCut_nonneg (r L u : ℝ) : 0 ≤ winCut r L u := Real.smoothTransition.nonneg _

theorem winCut_le_one (r L u : ℝ) : winCut r L u ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_winCut (r L : ℝ) {n : ℕ} : ContDiff ℝ n (winCut r L) := by
  have hψ : ContDiff ℝ n Real.smoothTransition := Real.smoothTransition.contDiff
  exact hψ.comp ((contDiff_id.sub contDiff_const).div_const L)

/-!
### The coordinate test function
-/

section Coord

variable {d : ℕ}

/-- The coordinate `q ↦ q.2 i` as a continuous linear map on `ℝ × ℝ^d`. -/
def coordCLM (i : Fin d) : ℝ × (Fin d → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))

/-- The coordinate test function `q ↦ q.2 i`. -/
def coordFn (i : Fin d) (q : ℝ × (Fin d → ℝ)) : ℝ := q.2 i

theorem coordFn_eq (i : Fin d) : coordFn i = ⇑(coordCLM i) := rfl

theorem fderiv_coordFn (i : Fin d) : fderiv ℝ (coordFn i) = fun _ => coordCLM i := by
  funext q
  rw [coordFn_eq, ContinuousLinearMap.fderiv]

theorem partialSpace_coordFn (i : Fin d) (q : ℝ × (Fin d → ℝ)) (j : Fin d) :
    partialSpace (coordFn i) q j = (Pi.single j (1 : ℝ) : Fin d → ℝ) i := by
  rw [partialSpace, fderiv_coordFn]
  rfl

theorem itoDrift_coordFn (i : Fin d) (y : Fin d → ℝ) (t : ℝ≥0) (A : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (coordFn i) y t 0 A = 0 := by
  simp [itoDrift, partialTime, partialSpace2, fderiv_coordFn, coordCLM]

theorem contDiff_coordFn (i : Fin d) : ContDiff ℝ 2 (coordFn i) := by
  rw [coordFn_eq]
  exact (coordCLM i).contDiff

theorem measurable_coordFn (i : Fin d) : Measurable (coordFn i) := by
  rw [coordFn_eq]
  exact (coordCLM i).continuous.measurable

/-- The window test function `winCut(u) y_i`. -/
abbrev winFn (r L : ℝ) (i : Fin d) : ℝ × (Fin d → ℝ) → ℝ :=
  linComb (fun _ : Unit => winCut r L) (fun _ => coordFn i)

theorem winFn_apply (r L : ℝ) (i : Fin d) (q : ℝ × (Fin d → ℝ)) :
    winFn r L i q = winCut r L q.1 * q.2 i := by
  simp [linComb, coordFn]

theorem winFn_eventuallyEq {r L s : ℝ} (hL : 0 < L) (hs : r < s) (i : Fin d) (y : Fin d → ℝ) :
    winFn r L i =ᶠ[𝓝 (s, y)] coordFn i := by
  have h : ∀ᶠ q in 𝓝 (s, y), r < q.1 :=
    (continuous_fst.tendsto (s, y)).eventually (lt_mem_nhds hs)
  filter_upwards [h] with q hq
  rw [winFn_apply, winCut_of_ge hL hq.le, one_mul]
  rfl

/-- After the window start, the window test function has zero Itô drift. -/
theorem itoDrift_winFn_eq_zero {r L : ℝ} (hL : 0 < L) (i : Fin d) {s : ℝ≥0} (hs : r < s)
    (y : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (winFn r L i) y s 0 A = 0 := by
  have h := winFn_eventuallyEq hL hs i y
  have h1 := h.fderiv_eq (𝕜 := ℝ)
  have h2 := (h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  rw [← itoDrift_coordFn i y s A]
  simp only [itoDrift, partialTime, partialSpace, partialSpace2, h1, h2]

theorem winBracket_eq (r L : ℝ) (v : Fin d → ℝ) (i : Fin d) (t : ℝ) (y : Fin d → ℝ) :
    ∑ j, v j * (∑ _a : Unit, winCut r L t * partialSpace (coordFn i) (t, y) j) ^ 2 =
      v i * winCut r L t ^ 2 := by
  simp [partialSpace_coordFn, Pi.single_apply, mul_ite, ite_pow]

end Coord

/-- The integrated window bracket: `∫_0^t v winCut(s)² ds ≤ 2L` for `0 ≤ t ≤ r + L`,
`v ≤ 1`. -/
theorem integral_winCut_sq_le {r L t v : ℝ} (hL : 0 < L) (ht0 : 0 ≤ t) (htT : t ≤ r + L)
    (hv1 : v ≤ 1) :
    ∫ s in Ioc (0 : ℝ) t, v * winCut r L (s.toNNReal : ℝ) ^ 2 ≤ 2 * L := by
  have hc : Continuous (winCut r L) := (contDiff_winCut r L (n := 0)).continuous
  have hf : Continuous fun s : ℝ => v * winCut r L (s.toNNReal : ℝ) ^ 2 :=
    continuous_const.mul ((hc.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).pow 2)
  have hf1 : ∀ s : ℝ, v * winCut r L (s.toNNReal : ℝ) ^ 2 ≤ 1 := fun s => by
    have h0 := winCut_nonneg r L (s.toNNReal : ℝ)
    have h1 := winCut_le_one r L (s.toNNReal : ℝ)
    have : winCut r L (s.toNNReal : ℝ) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hle : ∀ a b : ℝ, a ≤ b → ∫ s in a..b, v * winCut r L (s.toNNReal : ℝ) ^ 2 ≤ b - a :=
    fun a b hab => by
      have := intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b)
        (intervalIntegrable_const :
          IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b) fun s _ => hf1 s
      simpa using this
  rw [← intervalIntegral.integral_of_le ht0]
  by_cases hrL : r - L ≤ 0
  · linarith [hle 0 t ht0]
  · rw [not_le] at hrL
    set m := min t (r - L) with hm
    have hm0 : 0 ≤ m := le_min ht0 hrL.le
    have hmt : m ≤ t := min_le_left _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 m)
      (hf.intervalIntegrable m t)]
    have h0 : ∫ s in (0 : ℝ)..m, v * winCut r L (s.toNNReal : ℝ) ^ 2 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
      · simp
      · rw [uIcc_of_le hm0] at hs
        have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs.1
        simp only [hs']
        rw [winCut_of_le hL (hs.2.trans (min_le_right _ _))]
        ring
    rw [h0, zero_add]
    refine (hle m t hmt).trans ?_
    rcases le_total t (r - L) with h | h
    · rw [hm, min_eq_left h]
      linarith
    · rw [hm, min_eq_right h]
      linarith

variable {p : BlockBand.Parameters}

/-- **Window tail.** For `r, L ∈ ℝ≥0` with `L > 0`, every coordinate `i` and `λ ≥ 0`:
`P(∃ u ∈ [r, r + L], λ ≤ |Y^i_u - Y^i_r|) ≤ 2 exp(-λ²/(16 L))`, `Y_u - Y_0 = vsNoise p u`. -/
theorem measure_window_le (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    (i : Fin (ringDim p)) (r L : ℝ≥0) (hL : 0 < L) {lam : ℝ} (hlam : 0 ≤ lam) :
    driverLaw (κ := Fin (ringDim p)) μ {x | ∃ u : ℝ≥0, r ≤ u ∧ u ≤ r + L ∧
        lam ≤ |vsNoise p u x i - vsNoise p r x i|} ≤
      2 * ENNReal.ofReal (Real.exp (-(lam ^ 2 / (16 * L)))) := by
  have hL' : (0 : ℝ) < L := hL
  have H := vsNoise_linComb_ito μ (fun _ : Unit => winCut r L) (fun _ => coordFn i)
    (fun _ => contDiff_winCut r L (n := 2)) (fun _ => measurable_coordFn i)
    (fun _ => contDiff_coordFn i)
  set X : ℝ≥0 → RingSample p → Fin 1 → ℝ :=
    fun t x _ => winFn (r : ℝ) L i ((t : ℝ), vsNoise p t x) with hX
  set β : ℝ≥0 → RingSample p → Fin 1 → ℝ := fun t x _ =>
    itoDrift (winFn (r : ℝ) L i) (vsNoise p t x) t 0 (diagonal (ringVariance p)) with hβ
  have key : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ u : ℝ≥0, r ≤ u →
      smCompensated X β 0 u x - smCompensated X β 0 r x =
        vsNoise p u x i - vsNoise p r x i := by
    filter_upwards [H.integrable] with x hx u hru
    have iu := (hx u).1 0
    have hru' : (r : ℝ) ≤ u := hru
    have hsplit : ∫ s in Ioc (0 : ℝ) u, β s.toNNReal x 0 =
        (∫ s in Ioc (0 : ℝ) r, β s.toNNReal x 0) + ∫ s in Ioc (r : ℝ) u, β s.toNNReal x 0 := by
      have hu := setIntegral_union (Ioc_disjoint_Ioc_of_le (le_refl (r : ℝ)))
        (measurableSet_Ioc (a := (r : ℝ)) (b := (u : ℝ)))
        (iu.mono_set (Ioc_subset_Ioc_right hru')) (iu.mono_set (Ioc_subset_Ioc_left r.2))
      have e : Ioc (0 : ℝ) r ∪ Ioc (r : ℝ) u = Ioc 0 (u : ℝ) := Ioc_union_Ioc_eq_Ioc r.2 hru'
      rw [e] at hu
      exact hu
    have hzero : ∫ s in Ioc (r : ℝ) u, β s.toNNReal x 0 = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
      have hs' : (r : ℝ) < (s.toNNReal : ℝ) := by
        rw [Real.coe_toNNReal _ ((r.2).trans hs.1.le)]
        exact hs.1
      exact itoDrift_winFn_eq_zero hL' i hs' _ _
    have hXu : X u x 0 = vsNoise p u x i := by
      rw [hX]
      simp only
      rw [winFn_apply, winCut_of_ge hL' hru', one_mul]
    have hXr : X r x 0 = vsNoise p r x i := by
      rw [hX]
      simp only
      rw [winFn_apply, winCut_of_ge hL' le_rfl, one_mul]
    simp only [smCompensated, hsplit, hzero, hXu, hXr]
    ring
  have hA : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0, t ≤ r + L →
      (t : WithTop ℝ≥0) ≤ ((r + L : ℝ≥0) : WithTop ℝ≥0) →
      ∫ s in Ioc (0 : ℝ) t, (Matrix.of fun (_ _ : Fin 1) => ∑ j, ringVariance p j *
        (∑ _a : Unit, winCut r L (s.toNNReal : ℝ) *
          partialSpace (coordFn i) ((s.toNNReal : ℝ), vsNoise p s.toNNReal x) j) ^ 2) 0 0 ≤
        2 * L := by
    refine ae_of_all _ fun x t htT _ => ?_
    simp only [Matrix.of_apply, winBracket_eq]
    exact integral_winCut_sq_le hL' t.2 (by exact_mod_cast htT) (ringVariance_le_one p i)
  have htail := measure_exists_abs_compensated_ge_le H
    (isStoppingTime_const (driverAugmented (κ := Fin (ringDim p)) μ) (r + L)) (r + L)
    (by positivity : (0 : ℝ) < 2 * L) hA (div_nonneg hlam (by norm_num : (0 : ℝ) ≤ 2))
  have hexp : (lam / 2) ^ 2 / (2 * (2 * (L : ℝ))) = lam ^ 2 / (16 * L) := by
    field_simp
    ring
  rw [hexp] at htail
  refine le_trans (measure_mono_ae ?_) htail
  filter_upwards [key] with x hx
  rintro ⟨u, hru, huT, hlt⟩
  rw [← hx u hru] at hlt
  have htri : |smCompensated X β 0 u x - smCompensated X β 0 r x| ≤
      |smCompensated X β 0 u x| + |smCompensated X β 0 r x| := abs_sub _ _
  by_cases h : lam / 2 ≤ |smCompensated X β 0 u x|
  · exact ⟨u, huT, by exact_mod_cast huT, h⟩
  · refine ⟨r, le_self_add, by exact_mod_cast le_self_add, ?_⟩
    linarith

end BlockBand.Native.ErdosRiabov.VS
