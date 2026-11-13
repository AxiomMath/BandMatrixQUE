module

public import BlockBand.Transmission.Dual.Statement
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The dual generator: locality, continuity, and `𝒟_q R = 0`

* `isOpen_dualChamber`;
* `dualGenerator_congr` (it depends only on the germ of the test) and
  `dualGenerator_eq_zero_of_notMem_tsupport`;
* `continuous_dualGenerator`: for a `C²` test with `tsupport ⊆ 𝒞_q` the function `𝒟_q f` is
  continuous (smooth coefficients on the open chamber, zero off the support);
* `drift_sum_eq_zero`: `Σ_i β_i^x + Σ_j β_j^y = 0` on `𝒞_q` (, re-derived:
  same-species `q(q-1) ± 2(q-1)Σ`, mixed `-2q² - 2q(Σx - Σy)`, base `2q + 2(Σx - Σy)`);
* `dualGenerator_eq_zero_of_eqOn_total`: if `f = R = Σ(x_i + y_i)` on an open set `O`, then
  `𝒟_q f = 0` on `O ∩ 𝒞_q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {q : ℕ}

theorem isOpen_strictMono_comp (g : DualCoord q → Fin q → ℝ) (hg : Continuous g) :
    IsOpen {z | StrictMono (g z)} := by
  have : {z | StrictMono (g z)} = ⋂ i : Fin q, ⋂ j : Fin q, {z | i < j → g z i < g z j} := by
    ext z; simp [StrictMono]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases hij : i < j
  · simpa [hij] using isOpen_lt ((continuous_apply i).comp hg) ((continuous_apply j).comp hg)
  · simp [hij]

theorem isOpen_dualChamber (q : ℕ) : IsOpen (dualChamber q) := by
  have e : dualChamber q = {z : DualCoord q | StrictMono z.1} ∩ ({z | StrictMono z.2} ∩
      ((⋂ i, {z : DualCoord q | 0 < z.1 i}) ∩ ⋂ i, {z : DualCoord q | 0 < z.2 i ∧ z.2 i < 1})) := by
    ext z; simp [dualChamber, IsRatioParameter]
  rw [e]
  refine (isOpen_strictMono_comp _ continuous_fst).inter ((isOpen_strictMono_comp _
    continuous_snd).inter ((isOpen_iInter_of_finite fun i => ?_).inter
      (isOpen_iInter_of_finite fun i => ?_)))
  · exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
  · exact (isOpen_lt continuous_const ((continuous_apply i).comp continuous_snd)).inter
      (isOpen_lt ((continuous_apply i).comp continuous_snd) continuous_const)

/-- `𝒟_q f (z)` depends only on the germ of `f` at `z`. -/
theorem dualGenerator_congr {D0 : ℝ} {f g : DualCoord q → ℝ} {z : DualCoord q}
    (h : f =ᶠ[𝓝 z] g) : dualGenerator D0 f z = dualGenerator D0 g z := by
  have h1 := h.fderiv (𝕜 := ℝ)
  have h2 : ∀ v, (fun w => fderiv ℝ f w v) =ᶠ[𝓝 z] fun w => fderiv ℝ g w v :=
    fun v => h1.mono fun w hw => by simp only [hw]
  have h3 : ∀ v, fderiv ℝ (fun w => fderiv ℝ f w v) z = fderiv ℝ (fun w => fderiv ℝ g w v) z :=
    fun v => (h2 v).fderiv_eq
  simp only [dualGenerator, h3, h1.eq_of_nhds]

theorem dualGenerator_zero (D0 : ℝ) (z : DualCoord q) :
    dualGenerator D0 (fun _ : DualCoord q => (0 : ℝ)) z = 0 := by
  simp [dualGenerator]

theorem dualGenerator_eq_zero_of_notMem_tsupport {D0 : ℝ} {f : DualCoord q → ℝ}
    {z : DualCoord q} (hz : z ∉ tsupport f) : dualGenerator D0 f z = 0 := by
  rw [dualGenerator_congr (notMem_tsupport_iff_eventuallyEq.1 hz)]
  exact dualGenerator_zero D0 z

theorem continuousAt_finsetSum' {ι : Type*} (s : Finset ι) {f : ι → DualCoord q → ℝ}
    {z : DualCoord q} (h : ∀ i ∈ s, ContinuousAt (f i) z) :
    ContinuousAt (fun w => ∑ i ∈ s, f i w) z :=
  tendsto_finsetSum s h

theorem continuousOn_dualDriftX (i : Fin q) :
    ContinuousOn (fun z : DualCoord q => dualDriftX z i) (dualChamber q) := by
  intro z hz
  have hinj : Function.Injective z.1 := hz.1.injective
  have hpos : ∀ j, 0 < z.1 i + z.2 j := fun j => add_pos (hz.2.2.1 i) (hz.2.2.2 j).1
  refine ContinuousAt.continuousWithinAt ?_
  unfold dualDriftX
  refine (continuousAt_const.add ((continuous_const.mul ((continuous_apply i).comp
    continuous_fst)).continuousAt)).add (ContinuousAt.mul ?_ ?_)
  · exact ((continuous_const.mul ((continuous_apply i).comp continuous_fst)).mul
      (continuous_const.add ((continuous_apply i).comp continuous_fst))).continuousAt
  · refine ContinuousAt.sub ?_ ?_
    · refine continuousAt_finsetSum' _ fun k hk => ?_
      have hne : z.1 i - z.1 k ≠ 0 :=
        sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hk) (hinj h).symm
      exact continuousAt_const.div (((continuous_apply i).comp continuous_fst).sub
        ((continuous_apply k).comp continuous_fst)).continuousAt hne
    · refine continuousAt_finsetSum' _ fun j _ => ?_
      exact continuousAt_const.div (((continuous_apply i).comp continuous_fst).add
        ((continuous_apply j).comp continuous_snd)).continuousAt (hpos j).ne'

theorem continuousOn_dualDriftY (j : Fin q) :
    ContinuousOn (fun z : DualCoord q => dualDriftY z j) (dualChamber q) := by
  intro z hz
  have hinj : Function.Injective z.2 := hz.2.1.injective
  have hpos : ∀ i, 0 < z.1 i + z.2 j := fun i => add_pos (hz.2.2.1 i) (hz.2.2.2 j).1
  refine ContinuousAt.continuousWithinAt ?_
  unfold dualDriftY
  refine (continuousAt_const.sub ((continuous_const.mul ((continuous_apply j).comp
    continuous_snd)).continuousAt)).add (ContinuousAt.mul ?_ ?_)
  · exact ((continuous_const.mul ((continuous_apply j).comp continuous_snd)).mul
      (continuous_const.sub ((continuous_apply j).comp continuous_snd))).continuousAt
  · refine ContinuousAt.sub ?_ ?_
    · refine continuousAt_finsetSum' _ fun l hl => ?_
      have hne : z.2 j - z.2 l ≠ 0 :=
        sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hl) (hinj h).symm
      exact continuousAt_const.div (((continuous_apply j).comp continuous_snd).sub
        ((continuous_apply l).comp continuous_snd)).continuousAt hne
    · refine continuousAt_finsetSum' _ fun i _ => ?_
      exact continuousAt_const.div (((continuous_apply i).comp continuous_fst).add
        ((continuous_apply j).comp continuous_snd)).continuousAt (hpos i).ne'

/-- **`𝒟_q f` is continuous** for a `C²` test supported in the open chamber. -/
theorem continuous_dualGenerator (D0 : ℝ) {f : DualCoord q → ℝ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ dualChamber q) : Continuous (dualGenerator D0 f) := by
  have hf1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv two_ne_zero
  have hf2 : ∀ v, Continuous fun w => fderiv ℝ (fun w => fderiv ℝ f w v) w v := by
    intro v
    have hg : ContDiff ℝ 1 fun w => fderiv ℝ f w v :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ dualChamber q
  · have hopen := isOpen_dualChamber q
    refine ContinuousOn.continuousAt ?_ (hopen.mem_nhds hz)
    unfold dualGenerator
    refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · refine continuousOn_finsetSum _ fun i _ => ContinuousOn.add ?_ ?_
      · exact (((continuous_apply i).comp continuous_fst).mul (continuous_const.add
          ((continuous_apply i).comp continuous_fst))).continuousOn.mul (hf2 _).continuousOn
      · exact (continuousOn_dualDriftX i).mul (hf1.clm_apply continuous_const).continuousOn
    · refine continuousOn_finsetSum _ fun j _ => ContinuousOn.add ?_ ?_
      · exact (((continuous_apply j).comp continuous_snd).mul (continuous_const.sub
          ((continuous_apply j).comp continuous_snd))).continuousOn.mul (hf2 _).continuousOn
      · exact (continuousOn_dualDriftY j).mul (hf1.clm_apply continuous_const).continuousOn
  · have hnot : z ∉ tsupport f := fun h => hz (hfs h)
    have hev : ∀ᶠ w in 𝓝 z, w ∉ tsupport f :=
      (isClosed_tsupport f).isOpen_compl.mem_nhds hnot
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with w hw
    exact (dualGenerator_eq_zero_of_notMem_tsupport hw).symm

/-- `𝒟_q f` has compact support when `f` does. -/
theorem hasCompactSupport_dualGenerator (D0 : ℝ) {f : DualCoord q → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (dualGenerator D0 f) := by
  refine hfc.mono' fun z hz => ?_
  by_contra h
  exact hz (dualGenerator_eq_zero_of_notMem_tsupport h)

/-!
## `𝒟_q R = 0`
-/

/-- The total coordinate `R(z) = Σ_i (x_i + y_i)` on `DualCoord q`. -/
def totalFun (q : ℕ) (z : DualCoord q) : ℝ := ∑ i, (z.1 i + z.2 i)

/-- `R` as a continuous linear map. -/
def totalCLM (q : ℕ) : DualCoord q →L[ℝ] ℝ :=
  ∑ i : Fin q, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _) +
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))

theorem totalCLM_apply (z : DualCoord q) : totalCLM q z = totalFun q z := by
  simp [totalCLM, totalFun]

theorem sum_pair_div (a w : Fin q → ℝ) (hw : Function.Injective w) (s : Fin q → Fin q → ℝ)
    (hs : ∀ i k, a i - a k = (w i - w k) * s i k) :
    2 * ∑ i, ∑ k, a i / (w i - w k) = ∑ i, ∑ k, s i k - ∑ i, s i i := by
  have hsw : ∑ i, ∑ k, a i / (w i - w k) = ∑ i, ∑ k, a k / (w k - w i) := Finset.sum_comm
  have hpt : ∀ i k, a i / (w i - w k) + a k / (w k - w i) = s i k - if i = k then s i i else 0 := by
    intro i k
    by_cases hik : i = k
    · subst hik; simp
    · have hne : w i - w k ≠ 0 := sub_ne_zero.2 fun h => hik (hw h)
      have hne' : w k - w i ≠ 0 := sub_ne_zero.2 fun h => hik (hw h).symm
      simp only [hik, ↓reduceIte, sub_zero]
      rw [div_add_div _ _ hne hne', div_eq_iff (mul_ne_zero hne hne')]
      linear_combination (w k - w i) * hs i k
  calc 2 * ∑ i, ∑ k, a i / (w i - w k)
      = ∑ i, ∑ k, (a i / (w i - w k) + a k / (w k - w i)) := by
        rw [two_mul]; nth_rewrite 2 [hsw]
        simp only [← Finset.sum_add_distrib]
    _ = ∑ i, ∑ k, (s i k - if i = k then s i i else 0) := by simp only [hpt]
    _ = ∑ i, ∑ k, s i k - ∑ i, s i i := by
        simp [Finset.sum_sub_distrib]

/-- **`Σ_i β_i^x + Σ_j β_j^y = 0`** on the open chamber. -/
theorem drift_sum_eq_zero {z : DualCoord q} (hz : z ∈ dualChamber q) :
    ∑ i, dualDriftX z i + ∑ j, dualDriftY z j = 0 := by
  have hx : Function.Injective z.1 := hz.1.injective
  have hy : Function.Injective z.2 := hz.2.1.injective
  have hpos : ∀ i j, z.1 i + z.2 j ≠ 0 := fun i j =>
    (add_pos (hz.2.2.1 i) (hz.2.2.2 j).1).ne'
  set X := ∑ i, z.1 i
  set Y := ∑ j, z.2 j
  have erase_x : ∀ i, ∑ k ∈ Finset.univ.erase i, 1 / (z.1 i - z.1 k) =
      ∑ k, 1 / (z.1 i - z.1 k) := fun i => Finset.sum_erase _ (by simp)
  have erase_y : ∀ j, ∑ l ∈ Finset.univ.erase j, 1 / (z.2 j - z.2 l) =
      ∑ l, 1 / (z.2 j - z.2 l) := fun j => Finset.sum_erase _ (by simp)
  have px := sum_pair_div (fun i => z.1 i * (1 + z.1 i)) z.1 hx (fun i k => 1 + z.1 i + z.1 k)
    (fun i k => by ring)
  have py := sum_pair_div (fun j => z.2 j * (1 - z.2 j)) z.2 hy (fun j l => 1 - z.2 j - z.2 l)
    (fun j l => by ring)
  have hmix : ∑ i, ∑ j, z.1 i * (1 + z.1 i) / (z.1 i + z.2 j) +
      ∑ j, ∑ i, z.2 j * (1 - z.2 j) / (z.1 i + z.2 j) = ∑ i, ∑ j, (1 + z.1 i - z.2 j) := by
    rw [Finset.sum_comm (f := fun j i => z.2 j * (1 - z.2 j) / (z.1 i + z.2 j)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← add_div, div_eq_iff (hpos i j)]
    ring
  have hxpart : ∑ i, dualDriftX z i = ∑ i, (1 + 2 * z.1 i) +
      2 * ∑ i, ∑ k, z.1 i * (1 + z.1 i) / (z.1 i - z.1 k) -
      2 * ∑ i, ∑ j, z.1 i * (1 + z.1 i) / (z.1 i + z.2 j) := by
    have hpt : ∀ i, dualDriftX z i = (1 + 2 * z.1 i) +
        2 * ∑ k, z.1 i * (1 + z.1 i) / (z.1 i - z.1 k) -
        2 * ∑ j, z.1 i * (1 + z.1 i) / (z.1 i + z.2 j) := fun i => by
      rw [dualDriftX, erase_x]
      simp only [div_eq_mul_inv, one_mul, ← Finset.mul_sum]
      ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hypart : ∑ j, dualDriftY z j = ∑ j, (1 - 2 * z.2 j) +
      2 * ∑ j, ∑ l, z.2 j * (1 - z.2 j) / (z.2 j - z.2 l) -
      2 * ∑ j, ∑ i, z.2 j * (1 - z.2 j) / (z.1 i + z.2 j) := by
    have hpt : ∀ j, dualDriftY z j = (1 - 2 * z.2 j) +
        2 * ∑ l, z.2 j * (1 - z.2 j) / (z.2 j - z.2 l) -
        2 * ∑ i, z.2 j * (1 - z.2 j) / (z.1 i + z.2 j) := fun j => by
      rw [dualDriftY, erase_y]
      simp only [div_eq_mul_inv, one_mul, ← Finset.mul_sum]
      ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at px py hmix
  rw [hxpart, hypart]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  linear_combination px + py - 2 * hmix

/-- If `f = R` on an open set `O`, then `𝒟_q f = 0` on `O ∩ 𝒞_q`. -/
theorem dualGenerator_eq_zero_of_eqOn_total (D0 : ℝ) {f : DualCoord q → ℝ}
    {O : Set (DualCoord q)} (hO : IsOpen O) (hfO : EqOn f (totalFun q) O) {z : DualCoord q}
    (hzO : z ∈ O) (hz : z ∈ dualChamber q) : dualGenerator D0 f z = 0 := by
  have hev : f =ᶠ[𝓝 z] totalCLM q := by
    filter_upwards [hO.mem_nhds hzO] with w hw
    rw [hfO hw, totalCLM_apply]
  rw [dualGenerator_congr hev]
  have hd : ∀ w, fderiv ℝ (⇑(totalCLM q)) w = totalCLM q := fun w => (totalCLM q).fderiv
  have hdd : ∀ v, fderiv ℝ (fun w => fderiv ℝ (⇑(totalCLM q)) w v) z = 0 := by
    intro v; simp only [hd]; exact fderiv_const_apply _
  have hX : ∀ i, totalCLM q (dirX i) = 1 := fun i => by
    rw [totalCLM_apply]; simp [totalFun, dirX, Pi.single_apply]
  have hY : ∀ j, totalCLM q (dirY j) = 1 := fun j => by
    rw [totalCLM_apply]; simp [totalFun, dirY, Pi.single_apply]
  simp only [dualGenerator, hdd, zero_apply, mul_zero, zero_add]
  simp only [hd, hX, hY, mul_one]
  rw [drift_sum_eq_zero hz, mul_zero]

end BlockBand.Transmission.Dual
