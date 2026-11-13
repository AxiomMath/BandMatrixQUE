module

public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyClocks
public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyNormalizer
public import BlockBand.Endpoints.Sine.MicroscopicTagStepsRotation

/-!
# The physical side as a window integral of Palm tag tests

* `mts_tagTest`: the averaged tag test `q⁻¹ Σ_j Φ(q v*D_jv / v*Dv)` (default `0`), a function of
  the projector `vv*`; joint measurability of the one-block data in `(e, ω)` (`blockF`, the lift,
  the clock matrices `D_j = 𝒯*P_j𝒯`, `blockFieldFactor`, `palmMass`).
* `mts_blockClockSpeed_eq_sum`: `v*Dv = Σ_j ‖P_jLv‖²`; the ring tags `mts_mainTags`
  (`Fin n ≃ ZMod n`) give `n⁻¹ Σ_j Φ(n p_j(v,e))`; the three tags `mts_atomTags`
  `(D_0/2, D_0/2, D - D_0)` with the tent test isolate the block-`0` mass:
  `ρ₀ ≤ test ≤ 2ρ₀` (`mts_atomClockTest_bounds`).
* `mts_physical_atom`: `∫ Â[three-tag test] d𝔪⁰_W ≤ 2 E Σ_α w(u_α) Σ_j p_{αj}²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.RingSymmetry
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

/-!
## The averaged tag test and measurability
-/

/-- The averaged tag test `q⁻¹ Σ_j Φ(q v*D_jv / v*Dv)` (default `0` on a null denominator). -/
def mts_tagTest {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : ι → ℂ) : ℝ :=
  (q : ℝ)⁻¹ * ∑ j, Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) v)

theorem mts_measurable_matrix_sum {α ι κ τ : Type*} [MeasurableSpace α] [Fintype τ]
    {A : α → τ → Matrix ι κ ℂ} (hA : ∀ j, Measurable fun a => A a j) :
    Measurable fun a => ∑ j, A a j :=
  Measurable.of_eval_matrix _ fun i i' => by
    simp only [Matrix.sum_apply]
    exact Finset.measurable_sum _ fun j _ => (hA j).eval_matrix

theorem mts_measurable_matrix_smul {α ι κ : Type*} [MeasurableSpace α] {c : α → ℂ}
    {A : α → Matrix ι κ ℂ} (hc : Measurable c) (hA : Measurable A) :
    Measurable fun a => c a • A a :=
  Measurable.of_eval_matrix _ fun i i' => by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc.mul hA.eval_matrix

theorem mts_measurable_quadForm_of {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {A : α → Matrix ι ι ℂ} {v : α → ι → ℂ} (hA : Measurable A) (hv : Measurable v) :
    Measurable (fun a => quadForm (A a) (v a)) := by
  have hc : Continuous (fun x : Matrix ι ι ℂ × (ι → ℂ) => quadForm x.1 x.2) := by
    unfold quadForm; fun_prop
  exact hc.measurable.comp (hA.prodMk hv)

theorem mts_measurable_tagTest_of {α ι : Type*} [MeasurableSpace α] [Fintype ι] (q : ℕ)
    {Dt : α → Fin q → Matrix ι ι ℂ} (hDt : ∀ j, Measurable fun a => Dt a j)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {v : α → ι → ℂ} (hv : Measurable v) :
    Measurable (fun a => mts_tagTest q (Dt a) Φ (v a)) := by
  have hS : Measurable fun a => ∑ j, Dt a j := mts_measurable_matrix_sum hDt
  unfold mts_tagTest
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  refine Φ.continuous.measurable.comp ?_
  unfold ratioHalfLine
  refine continuous_projIci_zero.measurable.comp ?_
  have h1 := mts_measurable_quadForm_of hS hv
  have h2 := mts_measurable_quadForm_of
    (mts_measurable_matrix_smul (c := fun _ => (q : ℂ)) measurable_const (hDt j)) hv
  exact Measurable.ite (measurableSet_eq_fun h1 measurable_const) measurable_const (h2.div h1)

theorem mts_tagTest_nonneg {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x) (v : ι → ℂ) : 0 ≤ mts_tagTest q Dt Φ v :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => hΦ _)

theorem mts_abs_tagTest_le {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : ι → ℂ) : |mts_tagTest q Dt Φ v| ≤ ‖Φ‖ := by
  unfold mts_tagTest
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_mul, abs_of_pos (inv_pos.2 hq')]
  have h := Finset.abs_sum_le_sum_abs (fun j => Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j)
    (fun _ => 0) v)) Finset.univ
  have h2 : ∑ j : Fin q, |Φ (ratioHalfLine ((q : ℂ) • Dt j) (∑ j, Dt j) (fun _ => 0) v)| ≤
      ∑ _j : Fin q, ‖Φ‖ := Finset.sum_le_sum fun _ _ => by
    rw [← Real.norm_eq_abs]; exact Φ.norm_coe_le_norm _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  calc (q : ℝ)⁻¹ * |_| ≤ (q : ℝ)⁻¹ * (q * ‖Φ‖) :=
        mul_le_mul_of_nonneg_left (h.trans h2) (inv_nonneg.2 hq'.le)
    _ = ‖Φ‖ := by field_simp

theorem mts_tagTest_le {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : ι → ℂ) : mts_tagTest q Dt Φ v ≤ ‖Φ‖ :=
  (le_abs_self _).trans (mts_abs_tagTest_le q Dt Φ v)

/-- The tag test is a function of the projector `vv*`. -/
theorem mts_tagTest_eq_proj {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : ι → ℂ) :
    mts_tagTest q Dt Φ v = (q : ℝ)⁻¹ * ∑ j, Φ (Set.projIci 0
      (if ((∑ j, Dt j) * vecMulVec v (star v)).trace.re = 0 then 0 else
        (((q : ℂ) • Dt j) * vecMulVec v (star v)).trace.re /
          ((∑ j, Dt j) * vecMulVec v (star v)).trace.re)) := by
  unfold mts_tagTest ratioHalfLine
  simp only [mts_quadForm_eq_trace]

theorem mts_measurable_tagTest_proj {ι : Type*} [Fintype ι] (q : ℕ) (Dt : Fin q → Matrix ι ι ℂ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    Measurable (fun P : Matrix ι ι ℂ => (q : ℝ)⁻¹ * ∑ j, Φ (Set.projIci 0
      (if ((∑ j, Dt j) * P).trace.re = 0 then 0 else
        (((q : ℂ) • Dt j) * P).trace.re / ((∑ j, Dt j) * P).trace.re))) := by
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  refine Φ.continuous.measurable.comp (continuous_projIci_zero.measurable.comp ?_)
  have h1 := mts_measurable_trace_re (∑ j, Dt j)
  exact Measurable.ite (measurableSet_eq_fun h1 measurable_const) measurable_const
    ((mts_measurable_trace_re _).div h1)

/-!
## Measurability of the one-block data in `(e, ω)`
-/

section Block

variable (p : Parameters) (k : ZMod p.n)

theorem mts_measurable_shift_of {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
    {H : α → Matrix ι ι ℂ} {e : α → ℝ} (hH : Measurable H) (he : Measurable e) :
    Measurable (fun a => H a - ((e a : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) :=
  measurable_mat_sub hH ((Complex.measurable_ofReal.comp he).smul_const _)

theorem mts_measurable_blockT_of {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {e : α → ℝ} (hω : Measurable ω) (he : Measurable e) :
    Measurable (fun a => physicalCoareaT (ω a).1 (ω a).2 (e a)) := by
  unfold physicalCoareaT physicalCoareaResolvent
  exact measurable_mat_mul (measurable_matrix_inv.comp
    (mts_measurable_shift_of (measurable_fst.comp hω) he)) (measurable_snd.comp hω)

theorem mts_measurable_blockF_of {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {e : α → ℝ} (hω : Measurable ω) (he : Measurable e) :
    Measurable (fun a => blockF p k (ω a) (e a)) := by
  unfold blockF physicalCoareaF physicalCoareaResolvent
  exact measurable_mat_sub measurable_const (measurable_mat_mul (measurable_mat_mul
    (measurable_conjTranspose''.comp (measurable_snd.comp hω)) (measurable_matrix_inv.comp
    (mts_measurable_shift_of (measurable_fst.comp hω) he))) (measurable_snd.comp hω))

theorem mts_measurable_reindex {ι κ : Type*} (σ : ι ≃ κ) :
    Measurable (fun A : Matrix ι ι ℂ => Matrix.reindex σ σ A) :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)

theorem mts_measurable_liftMatrix_of {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {e : α → ℝ} (hω : Measurable ω) (he : Measurable e) :
    Measurable (fun a => mts_liftMatrix p k (ω a) (e a)) := by
  have hT := mts_measurable_blockT_of p k hω he
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  unfold mts_liftMatrix
  by_cases hx : x.1 = k
  · simp only [hx, dite_true]; exact measurable_const
  · simp only [hx, dite_false]
    exact ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hT)).neg

theorem mts_measurable_blockClockMatrix_of {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {e : α → ℝ} (hω : Measurable ω) (he : Measurable e) (j : ZMod p.n) :
    Measurable (fun a => mts_blockClockMatrix p k (ω a) (e a) j) := by
  have hL := mts_measurable_liftMatrix_of p k hω he
  unfold mts_blockClockMatrix
  exact measurable_mat_mul (measurable_mat_mul (measurable_conjTranspose''.comp hL)
    measurable_const) hL

theorem mts_continuous_matchedA : Continuous matchedA := by
  have : matchedA = fun E => ((-E / 2 : ℝ) : ℂ) +
      ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
    funext E; apply Complex.ext <;> simp [matchedA]
  rw [this]; fun_prop

theorem mts_measurable_commonZ (b : ℝ) : Measurable (fun e : ℝ => commonZ b e) := by
  unfold commonZ
  have h := mts_continuous_matchedA.measurable
  exact h.inv.add (measurable_const.mul h)

theorem mts_measurable_blockFieldFactor_of {α : Type*} [MeasurableSpace α]
    {ω : α → BlockState p k} {e : α → ℝ} (hω : Measurable ω) (he : Measurable e) :
    Measurable (fun a => blockFieldFactor p k (ω a) (e a)) := by
  unfold blockFieldFactor blockShifted
  exact mts_measurable_matrix_smul measurable_const (measurable_matrix_inv.comp
    (measurable_mat_add (mts_measurable_matrix_smul ((mts_measurable_commonZ p.b).comp he)
    measurable_const) (mts_measurable_blockF_of p k hω he)))

theorem mts_measurable_palmMass {α : Type*} [MeasurableSpace α] {N : ℕ}
    {F : α → Matrix (Fin N) (Fin N) ℂ} (hF : Measurable F) {E : α → ℝ} (hE : Measurable E)
    (c₀ : ℝ) : Measurable (fun a => palmMass (F a) c₀ (E a)) := by
  have := mts_isProbabilityMeasure_freshTracelessLaw N c₀
  have hadd : Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ => F q.1 + q.2) :=
    Measurable.of_eval fun i => Measurable.of_eval fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hF.comp measurable_fst))).add
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))
  have hw : ∀ ℓ : Fin N, Measurable (fun q : α × Matrix (Fin N) (Fin N) ℂ =>
      palmWeight (F q.1) c₀ (E q.1) ℓ q.2) := by
    intro ℓ
    unfold palmWeight BlockBand.Palm.scalarWeight freshEigenvalue
    exact (measurable_gaussianPDFReal _ _).comp
      ((hE.comp measurable_fst).sub ((measurable_rawIncreasingEigenvalue _).comp hadd))
  unfold palmMass
  exact Finset.measurable_sum _ fun ℓ _ =>
    (hw ℓ).stronglyMeasurable.integral_prod_right'.measurable

theorem mts_palmMass_nonneg {N : ℕ} (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) :
    0 ≤ palmMass F c₀ E :=
  Finset.sum_nonneg fun ℓ _ => integral_nonneg fun A0 => mts_palmWeight_nonneg F c₀ E ℓ A0

end Block

/-!
## The one-block sector measures of the tag test and the window measure
-/

section Window

variable (p : Parameters) (k : ZMod p.n)

theorem mts_measurable_microCoord (E : ℝ) : Measurable (microCoord p E) :=
  (by unfold microCoord; fun_prop : Continuous (microCoord p E)).measurable

theorem mts_microEnergy_microCoord {E : ℝ} (hρ : 0 < Parameters.semicircleDensity E) (e : ℝ) :
    microEnergy p E (microCoord p E e) = e := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  unfold microEnergy microCoord
  field_simp
  ring

theorem mts_blockSectorFiber_const_mul
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (ω : BlockState p k) (e : ℝ) (ℓ : ℕ) {a : ℝ≥0∞} (ha : a ≠ ∞)
    (g : (BlockSite p k → ℂ) → ℝ≥0∞) :
    blockSectorFiber p k U ω e ℓ (fun v => a * g v) = a * blockSectorFiber p k U ω e ℓ g := by
  classical
  unfold blockSectorFiber
  simp_rw [mul_left_comm _ a]
  simp_rw [lintegral_const_mul' _ _ ha]

/-- **The sector fibers of the tag test as a Palm expectation**: the sum over `ℓ < W` of the
block sector fibers equals `palmMass · palmExpect` of the tag test. -/
theorem mts_sum_sectorFiber_tagTest (hFED : FreshEigenpairDensityContract)
    (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (ω : BlockState p k) (hω : ω.1.IsHermitian) (e : ℝ) (q : ℕ)
    (Dt : Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ)
    {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x) :
    (∑ ℓ ∈ Finset.range p.W, blockSectorFiber p k U ω e ℓ
        (fun v => ENNReal.ofReal (mts_tagTest q Dt Φ (v ∘ σ.symm)))) =
      ENNReal.ofReal (palmMass (blockDeformation p k σ ω e) p.c e *
        palmExpect (blockDeformation p k σ ω e) p.c e (mts_tagTest q Dt Φ)) := by
  have h := mts_sum_blockSectorFiber_eq_palmExpect p k hFED (mts_card_blockSite p k) σ U hU ω hω
    e (mts_tagTest q Dt Φ) (mts_tagTest_nonneg q Dt hΦ) (C := ‖Φ‖) (mts_tagTest_le q Dt Φ)
    (fun P => (q : ℝ)⁻¹ * ∑ j, Φ (Set.projIci 0
      (if ((∑ j, Dt j) * P).trace.re = 0 then 0 else
        (((q : ℂ) • Dt j) * P).trace.re / ((∑ j, Dt j) * P).trace.re)))
    (mts_measurable_tagTest_proj q Dt Φ) (mts_tagTest_eq_proj q Dt Φ)
  have hr : Finset.range p.W = Finset.range (Fintype.card (BlockSite p k)) := by
    rw [mts_card_blockSite]
  rw [hr, Finset.sum_range]
  exact h

/-- **The window measure of a Palm tag test.** For a measurable tag family `D_j(e, ω)` and a
nonnegative `Φ`: `∫ Â[test] d𝔪⁰_W = E_ω ∫ n w(u(e)) Σ_{ℓ<W} 𝒜⁰_{ℓ,e}[test] de`. -/
theorem mts_window_lintegral (hFED : FreshEigenpairDensityContract)
    {model : p.GaussianRingModel} {Pω : Measure (BlockState p k)}
    (hs : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (E : ℝ) {w : ℝ → ℝ} (hwm : Measurable w) (q : ℕ)
    (Dt : ℝ × BlockState p k → Fin q → Matrix (Fin (Fintype.card (BlockSite p k)))
      (Fin (Fintype.card (BlockSite p k))) ℂ)
    (hDt : ∀ j, Measurable fun x => Dt x j) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x) :
    ∫⁻ x, ENNReal.ofReal (palmExpect (blockDeformation p k σ x.2 x.1) p.c x.1
        (mts_tagTest q (Dt x) Φ)) ∂blockWindowMeasure p k U Pω E w =
      ∫⁻ ω, ∫⁻ e, ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E e)) *
        ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p k U ω e ℓ
          (fun v => ENNReal.ofReal (mts_tagTest q (Dt (e, ω)) Φ (v ∘ σ.symm))) ∂volume ∂Pω := by
  have hP := mts_isProbabilityMeasure_of_blockSplitting hs
  have hH := mts_ae_blockState_isHermitian hs
  have hFm : Measurable fun x : ℝ × BlockState p k => blockDeformation p k σ x.2 x.1 :=
    (mts_measurable_reindex σ).comp (mts_measurable_blockF_of p k measurable_snd measurable_fst)
  set d' : ℝ × BlockState p k → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) *
      ENNReal.ofReal (palmMass (blockDeformation p k σ x.2 x.1) p.c x.1) with hd'def
  have hd' : Measurable d' :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (hwm.comp ((mts_measurable_microCoord p E).comp measurable_fst)))).mul
      (ENNReal.measurable_ofReal.comp (mts_measurable_palmMass hFm measurable_fst _))
  have hg : Measurable fun x : ℝ × BlockState p k => ENNReal.ofReal
      (palmExpect (blockDeformation p k σ x.2 x.1) p.c x.1 (mts_tagTest q (Dt x) Φ)) := by
    refine ENNReal.measurable_ofReal.comp (mts_measurable_palmExpect hFm measurable_fst _ ?_)
    exact mts_measurable_tagTest_of q (Dt := fun y : (ℝ × BlockState p k) × _ => Dt y.1)
      (fun j => (hDt j).comp measurable_fst) Φ measurable_snd
  have hae : (fun x : ℝ × BlockState p k =>
      ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E x.1)) * blockNormalizer p k U x.2 x.1)
      =ᵐ[volume.prod Pω] d' := by
    have h2 : ∀ᵐ x ∂(volume.prod Pω), (x : ℝ × BlockState p k).2.1.IsHermitian :=
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := Pω)).ae hH
    filter_upwards [h2] with x hx
    rw [hd'def, mts_blockNormalizer_eq_palmMass p k hFED (mts_card_blockSite p k) σ U hU x.2 hx x.1]
    rfl
  unfold blockWindowMeasure
  rw [withDensity_congr_ae hae, lintegral_withDensity_eq_lintegral_mul _ hd' hg,
    lintegral_prod_symm' _ (hd'.mul hg)]
  refine lintegral_congr_ae ?_
  filter_upwards [hH] with ω hω
  refine lintegral_congr fun e => ?_
  simp only [Pi.mul_apply, hd'def]
  rw [mts_sum_sectorFiber_tagTest p k hFED σ U hU ω hω e q (Dt (e, ω)) hΦ, mul_assoc,
    ← ENNReal.ofReal_mul (mts_palmMass_nonneg _ _ _)]

end Window

/-!
## The physical tag families
-/

section Tags

variable (p : Parameters) (k : ZMod p.n)

theorem mts_re_star_dot_self {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `v*Dv = ‖v‖² + ‖Tv‖² = Σ_j ‖P_jLv‖²`. -/
theorem mts_blockClockSpeed_eq_sum (ω : BlockState p k) (e : ℝ) (v : BlockSite p k → ℂ) :
    blockClockSpeed p k ω e v = ∑ j, mts_fieldClock p k e ω v j := by
  have h1 : ∑ j, mts_fieldClock p k e ω v j = ∑ x : p.Site, ‖blockLift p k ω e v x‖ ^ 2 := by
    unfold mts_fieldClock
    exact (Fintype.sum_prod_type (fun x : p.Site => ‖blockLift p k ω e v x‖ ^ 2)).symm
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun x : p.Site => x.1 = k)]
  unfold blockClockSpeed physicalCoareaD schurClock
  rw [add_mulVec, one_mulVec, dotProduct_add, Complex.add_re, ← mulVec_mulVec, dotProduct_mulVec,
    ← star_mulVec, mts_re_star_dot_self, mts_re_star_dot_self]
  congr 1
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [blockLift, x.2]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp [blockLift, x.2]

theorem mts_fieldClock_nonneg (e : ℝ) (ω : BlockState p k) (v : BlockSite p k → ℂ)
    (j : ZMod p.n) : 0 ≤ mts_fieldClock p k e ω v j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mts_ratioHalfLine_zero {ι : Type*} [Fintype ι] (C D : Matrix ι ι ℂ) (v : ι → ℂ) :
    ratioHalfLine C D (fun _ => 0) v = Set.projIci 0 (quadForm C v / quadForm D v) := by
  unfold ratioHalfLine
  split_ifs with h
  · rw [h, div_zero]
  · rfl

theorem mts_quadForm_reindex_symm {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ)
    (A : Matrix ι ι ℂ) (v : ι → ℂ) : quadForm (Matrix.reindex σ σ A) (v ∘ σ.symm) = quadForm A v := by
  rw [mts_quadForm_reindex, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

theorem mts_quadForm_natSmul {ι : Type*} [Fintype ι] (n : ℕ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm ((n : ℂ) • A) v = n * quadForm A v := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, mts_quadForm_smul_real]

/-- `Fin n ≃ ZMod n`, indexing the ring tags. -/
def mts_ringEquiv (p : Parameters) : Fin p.n ≃ ZMod p.n := (ZMod.finEquiv p.n).toEquiv

/-- The `n` ring tags `D_j = 𝒯*P_j𝒯` of the one-block reconstruction, reindexed to `Fin N`. -/
def mts_mainTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) :
    Fin p.n → Matrix (Fin (Fintype.card (BlockSite p k))) (Fin (Fintype.card (BlockSite p k))) ℂ :=
  fun j => Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 (mts_ringEquiv p j))

/-- The averaged ring test of the block clocks `n⁻¹ Σ_j Φ(n x_j / Σ_i x_i)`. -/
def mts_mainClockTest (p : Parameters) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (x : ZMod p.n → ℝ) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ j, Φ (Set.projIci 0 ((p.n : ℝ) * x j / ∑ i, x i))

theorem mts_measurable_mainClockTest (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    Measurable (mts_mainClockTest p Φ) := by
  unfold mts_mainClockTest
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  exact Φ.continuous.measurable.comp (continuous_projIci_zero.measurable.comp
    ((measurable_const.mul (measurable_pi_apply j)).div
      (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)))

theorem mts_tagTest_mainTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (e : ℝ)
    (ω : BlockState p k) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : BlockSite p k → ℂ) :
    mts_tagTest p.n (mts_mainTags p k σ (e, ω)) Φ (v ∘ σ.symm) =
      mts_mainClockTest p Φ (mts_fieldClock p k e ω v) := by
  unfold mts_tagTest mts_mainClockTest
  congr 1
  have hS : quadForm (∑ j, mts_mainTags p k σ (e, ω) j) (v ∘ σ.symm) =
      ∑ i, mts_fieldClock p k e ω v i := by
    rw [mts_quadForm_sum]
    simp only [mts_mainTags, mts_quadForm_reindex_symm, mts_quadForm_blockClockMatrix]
    exact (mts_ringEquiv p).sum_comp (mts_fieldClock p k e ω v)
  refine Fintype.sum_equiv (mts_ringEquiv p) _ _ fun j => ?_
  rw [mts_ratioHalfLine_zero, hS, mts_quadForm_natSmul]
  simp only [mts_mainTags, mts_quadForm_reindex_symm, mts_quadForm_blockClockMatrix]

theorem mts_mainClockTest_smul (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {c : ℝ} (hc : c ≠ 0)
    (x : ZMod p.n → ℝ) : mts_mainClockTest p Φ (fun j => c * x j) = mts_mainClockTest p Φ x := by
  unfold mts_mainClockTest
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, mul_left_comm, mul_div_mul_left _ _ hc]

theorem mts_mainTags_posSemidef (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) (j : Fin p.n) : (mts_mainTags p k σ x j).PosSemidef :=
  mts_reindex_blockClockMatrix_posSemidef p k σ x.2 x.1 _

theorem mts_mainTags_sum_sub_one (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) : ((∑ j, mts_mainTags p k σ x j) - 1).PosSemidef := by
  have h : ∑ j, mts_mainTags p k σ x j =
      ∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 j) :=
    (mts_ringEquiv p).sum_comp (fun j => Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 j))
  rw [h]
  exact mts_reindex_tags_sub_one p k σ x.2 x.1

theorem mts_measurable_mainTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (j : Fin p.n) : Measurable fun x : ℝ × BlockState p k => mts_mainTags p k σ x j :=
  (mts_measurable_reindex σ).comp
    (mts_measurable_blockClockMatrix_of p k measurable_snd measurable_fst _)

/-!
### The three-tag family isolating block `0`
-/

/-- The tent `y ↦ max(0, min(y, 3 - y))`. -/
def mts_tent : Set.Ici (0 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => max 0 (min (y : ℝ) (3 - y)))
    (by fun_prop) 3 (fun y => by
      have h0 := y.2
      simp only [Set.mem_Ici] at h0
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (by norm_num) ((min_le_right _ _).trans (by linarith)))

theorem mts_tent_apply (y : Set.Ici (0 : ℝ)) : mts_tent y = max 0 (min (y : ℝ) (3 - y)) := rfl

theorem mts_tent_nonneg (y : Set.Ici (0 : ℝ)) : 0 ≤ mts_tent y := le_max_left _ _

/-- The three tags `(D_0/2, D_0/2, D - D_0)` (`D_0` the clock of block `k = 0` of the ring
reconstruction). -/
def mts_atomTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) :
    Fin 3 → Matrix (Fin (Fintype.card (BlockSite p k))) (Fin (Fintype.card (BlockSite p k))) ℂ :=
  ![((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k),
    ((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k),
    (∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 j)) -
      Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k)]

/-- The three-tag test as a function of the block clocks. -/
def mts_atomClockTest (p : Parameters) (k : ZMod p.n) (x : ZMod p.n → ℝ) : ℝ :=
  (3 : ℝ)⁻¹ * (mts_tent (Set.projIci 0 (3 * (1 / 2 * x k) / ∑ i, x i)) +
    mts_tent (Set.projIci 0 (3 * (1 / 2 * x k) / ∑ i, x i)) +
    mts_tent (Set.projIci 0 (3 * (∑ i, x i - x k) / ∑ i, x i)))

theorem mts_measurable_atomClockTest : Measurable (mts_atomClockTest p k) := by
  have hS : Measurable fun x : ZMod p.n → ℝ => ∑ i, x i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hT := mts_tent.continuous.measurable
  have hP := continuous_projIci_zero.measurable
  unfold mts_atomClockTest
  refine measurable_const.mul ?_
  refine ((hT.comp (hP.comp ?_)).add (hT.comp (hP.comp ?_))).add (hT.comp (hP.comp ?_))
  · exact (measurable_const.mul (measurable_const.mul (measurable_pi_apply k))).div hS
  · exact (measurable_const.mul (measurable_const.mul (measurable_pi_apply k))).div hS
  · exact (measurable_const.mul (hS.sub (measurable_pi_apply k))).div hS

theorem mts_tagTest_atomTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k))) (e : ℝ)
    (ω : BlockState p k) (v : BlockSite p k → ℂ) :
    mts_tagTest 3 (mts_atomTags p k σ (e, ω)) mts_tent (v ∘ σ.symm) =
      mts_atomClockTest p k (mts_fieldClock p k e ω v) := by
  have hR : ∀ j, quadForm (Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)) (v ∘ σ.symm) =
      mts_fieldClock p k e ω v j := fun j => by
    rw [mts_quadForm_reindex_symm, mts_quadForm_blockClockMatrix]
  have hS : quadForm (∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)) (v ∘ σ.symm) =
      ∑ i, mts_fieldClock p k e ω v i := by
    rw [mts_quadForm_sum]; simp only [hR]
  have h0 : quadForm (mts_atomTags p k σ (e, ω) 0) (v ∘ σ.symm) =
      1 / 2 * mts_fieldClock p k e ω v k := by
    show quadForm (((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k ω e k))
      (v ∘ σ.symm) = _
    rw [mts_quadForm_smul_real, hR]
  have h1 : quadForm (mts_atomTags p k σ (e, ω) 1) (v ∘ σ.symm) =
      1 / 2 * mts_fieldClock p k e ω v k := by
    show quadForm (((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k ω e k))
      (v ∘ σ.symm) = _
    rw [mts_quadForm_smul_real, hR]
  have h2 : quadForm (mts_atomTags p k σ (e, ω) 2) (v ∘ σ.symm) =
      ∑ i, mts_fieldClock p k e ω v i - mts_fieldClock p k e ω v k := by
    show quadForm ((∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k ω e j)) -
      Matrix.reindex σ σ (mts_blockClockMatrix p k ω e k)) (v ∘ σ.symm) = _
    rw [mts_quadForm_sub, hS, hR]
  have hD : quadForm (∑ j, mts_atomTags p k σ (e, ω) j) (v ∘ σ.symm) =
      ∑ i, mts_fieldClock p k e ω v i := by
    rw [mts_quadForm_sum, Fin.sum_univ_three, h0, h1, h2]; ring
  unfold mts_tagTest mts_atomClockTest
  rw [Fin.sum_univ_three]
  simp only [mts_ratioHalfLine_zero, mts_quadForm_natSmul, hD, h0, h1, h2]
  norm_num

/-- `x_k/Σx ≤ atomClockTest x ≤ 2 x_k/Σx` for nonnegative clocks. -/
theorem mts_atomClockTest_bounds {x : ZMod p.n → ℝ} (hx : ∀ j, 0 ≤ x j) :
    x k / (∑ i, x i) ≤ mts_atomClockTest p k x ∧
      mts_atomClockTest p k x ≤ 2 * (x k / ∑ i, x i) := by
  set S := ∑ i, x i
  have haS : x k ≤ S := Finset.single_le_sum (f := x) (fun j _ => hx j) (Finset.mem_univ k)
  have hS0 : 0 ≤ S := (hx k).trans haS
  unfold mts_atomClockTest
  rw [← (show S = ∑ i, x i from rfl)]
  rcases hS0.lt_or_eq with hS | hS
  · set ρ := x k / S
    have hρ0 : 0 ≤ ρ := div_nonneg (hx k) hS.le
    have hρ1 : ρ ≤ 1 := (div_le_one hS).2 haS
    have e1 : 3 * (1 / 2 * x k) / S = 3 / 2 * ρ := by simp only [ρ]; field_simp
    have e2 : 3 * (S - x k) / S = 3 - 3 * ρ := by simp only [ρ]; field_simp
    rw [e1, e2, mts_tent_apply, mts_tent_apply, Set.coe_projIci, Set.coe_projIci]
    have t1 : max 0 (min (max 0 (3 / 2 * ρ)) (3 - max 0 (3 / 2 * ρ))) = 3 / 2 * ρ := by
      have hm : max 0 (3 / 2 * ρ) = 3 / 2 * ρ := max_eq_right (by linarith)
      rw [hm, min_eq_left (by linarith), max_eq_right (by linarith)]
    have t2 : max 0 (min (max 0 (3 - 3 * ρ)) (3 - max 0 (3 - 3 * ρ))) =
        min (3 - 3 * ρ) (3 * ρ) := by
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ 3 - 3 * ρ)]
      rw [max_eq_right (le_min (by linarith) (by linarith))]
      congr 1; ring
    rw [t1, t2]
    have m1 : min (3 - 3 * ρ) (3 * ρ) ≤ 3 * ρ := min_le_right _ _
    have m2 : 0 ≤ min (3 - 3 * ρ) (3 * ρ) := le_min (by linarith) (by linarith)
    constructor <;> nlinarith
  · have ha : x k = 0 := le_antisymm (hS ▸ haS) (hx k)
    rw [← hS, ha]
    simp [mts_tent_apply]

theorem mts_atomClockTest_smul {c : ℝ} (hc : c ≠ 0) (x : ZMod p.n → ℝ) :
    mts_atomClockTest p k (fun j => c * x j) = mts_atomClockTest p k x := by
  unfold mts_atomClockTest
  have hS : ∑ i, c * x i = c * ∑ i, x i := (Finset.mul_sum _ _ _).symm
  rw [hS]
  have e1 : 3 * (1 / 2 * (c * x k)) / (c * ∑ i, x i) = 3 * (1 / 2 * x k) / ∑ i, x i := by
    rw [show 3 * (1 / 2 * (c * x k)) = c * (3 * (1 / 2 * x k)) by ring, mul_div_mul_left _ _ hc]
  have e2 : 3 * (c * ∑ i, x i - c * x k) / (c * ∑ i, x i) = 3 * (∑ i, x i - x k) / ∑ i, x i := by
    rw [show 3 * (c * ∑ i, x i - c * x k) = c * (3 * (∑ i, x i - x k)) by ring,
      mul_div_mul_left _ _ hc]
  rw [e1, e2]

theorem mts_atomTags_posSemidef (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) (j : Fin 3) : (mts_atomTags p k σ x j).PosSemidef := by
  have hR := mts_reindex_blockClockMatrix_posSemidef p k σ x.2 x.1
  have hhalf : (((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k)).PosSemidef :=
    (hR k).smul (Complex.zero_le_real.2 (by norm_num))
  fin_cases j
  · exact hhalf
  · exact hhalf
  · show ((∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 j)) -
      Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k)).PosSemidef
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]
    exact posSemidef_sum _ fun j _ => hR j

theorem mts_atomTags_sum (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) :
    ∑ j, mts_atomTags p k σ x j = ∑ j, Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 j) := by
  rw [Fin.sum_univ_three]
  simp only [mts_atomTags, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [← add_smul]
  norm_num

theorem mts_atomTags_sum_sub_one (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (x : ℝ × BlockState p k) : ((∑ j, mts_atomTags p k σ x j) - 1).PosSemidef := by
  rw [mts_atomTags_sum]
  exact mts_reindex_tags_sub_one p k σ x.2 x.1

theorem mts_measurable_atomTags (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (j : Fin 3) : Measurable fun x : ℝ × BlockState p k => mts_atomTags p k σ x j := by
  have hR : ∀ i, Measurable fun x : ℝ × BlockState p k =>
      Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 i) := fun i =>
    (mts_measurable_reindex σ).comp
      (mts_measurable_blockClockMatrix_of p k measurable_snd measurable_fst _)
  have hh : Measurable fun x : ℝ × BlockState p k =>
      ((1 / 2 : ℝ) : ℂ) • Matrix.reindex σ σ (mts_blockClockMatrix p k x.2 x.1 k) :=
    mts_measurable_matrix_smul (c := fun _ => ((1 / 2 : ℝ) : ℂ)) measurable_const (hR k)
  fin_cases j
  · exact hh
  · exact hh
  · exact measurable_mat_sub (mts_measurable_matrix_sum hR) (hR k)

end Tags

/-!
## The physical side as a window integral of Palm tag tests
-/

section Physical

variable (p : Parameters) (k : ZMod p.n)

/-- **One-block Palm formula for a test of the reconstructed masses**, with the window weight. -/
theorem mts_physical_lintegral (hPalm : OneBlockPalmContract) {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p k)} (hs : IsBlockSplitting p k model Pω)
    (U : (BlockSite p k → ℂ) → Matrix (BlockSite p k) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p k U) (E : ℝ) {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ u, 0 ≤ w u)
    {Θ : (ZMod p.n → ℝ) → ℝ} (hΘ : Measurable Θ) :
    (p.n : ℝ≥0∞) * ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α k) *
        ENNReal.ofReal (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          Θ (blockMassVector p H α)) ∂(model.law : Measure p.SiteMatrix) =
      ∫⁻ ω, ∫⁻ e, ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E e)) *
        ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p k U ω e ℓ
          (fun v => ENNReal.ofReal (Θ (blockReconMass p k ω e v))) ∂volume ∂Pω := by
  have hf : Measurable (Function.uncurry fun (e : ℝ) (m : ZMod p.n → ℝ) =>
      ENNReal.ofReal (w (microCoord p E e) * Θ m)) :=
    ENNReal.measurable_ofReal.comp ((hwm.comp ((mts_measurable_microCoord p E).comp
      measurable_fst)).mul (hΘ.comp measurable_snd))
  rw [hPalm.mass p model k Pω hs U hU _ hf]
  rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_congr fun e => ?_
  have h1 : ∀ v, ENNReal.ofReal (w (microCoord p E e) * Θ (blockReconMass p k ω e v)) =
      ENNReal.ofReal (w (microCoord p E e)) * ENNReal.ofReal (Θ (blockReconMass p k ω e v)) :=
    fun v => ENNReal.ofReal_mul (hw0 _)
  simp only [h1, mts_blockSectorFiber_const_mul p k U ω e _ ENNReal.ofReal_ne_top]
  rw [← Finset.mul_sum, ← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- Rotation: every block gives the block-`0` value. -/
theorem mts_lintegral_sum_blocks (hRot : RingRotationInvariance) (model : p.GaussianRingModel)
    (G : ℝ → ℝ → ℝ≥0∞) (hG : Measurable (Function.uncurry G)) :
    (∫⁻ H, ∑ α : Fin p.N, ∑ s : ZMod p.n,
        G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α s)
        ∂(model.law : Measure p.SiteMatrix)) =
      (p.n : ℝ≥0∞) * ∫⁻ H, ∑ α : Fin p.N,
        G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α 0)
        ∂(model.law : Measure p.SiteMatrix) := by
  have hs : ∀ s : ZMod p.n, (∫⁻ H, ∑ α : Fin p.N,
      G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α s)
        ∂(model.law : Measure p.SiteMatrix)) = ∫⁻ H, ∑ α : Fin p.N,
      G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α 0)
        ∂(model.law : Measure p.SiteMatrix) := by
    intro s
    have h := (hRot p model s).2.2.2 (fun l P => ∑ α : Fin p.N, G (l α) (P α 0))
    simp only [eigenvalueVector, blockMassMatrix, zero_add] at h
    exact h
  have hm : ∀ s ∈ (Finset.univ : Finset (ZMod p.n)), Measurable (fun H : p.SiteMatrix =>
      ∑ α : Fin p.N, G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α s)) :=
    fun s _ => Finset.measurable_sum _ fun α _ => hG.comp
      ((mts_measurable_physicalOrderedEigenvalue p α).prodMk
        (measurable_physicalOrderedBlockMass p α s))
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin p.N)))]
  rw [lintegral_finsetSum _ hm, Finset.sum_congr rfl fun s _ => hs s, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- The ring test of a mass vector `n⁻¹ Σ_j Φ(n m_j)`. -/
def mts_massTest (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (m : ZMod p.n → ℝ) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ j, Φ (Set.projIci 0 ((p.n : ℝ) * m j))

theorem mts_measurable_massTest (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : Measurable (mts_massTest p Φ) := by
  unfold mts_massTest
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ => Φ.continuous.measurable.comp
    (continuous_projIci_zero.measurable.comp (measurable_const.mul (measurable_pi_apply j))))

theorem mts_massTest_blockReconMass (σ : BlockSite p k ≃ Fin (Fintype.card (BlockSite p k)))
    (e : ℝ) (ω : BlockState p k) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (v : BlockSite p k → ℂ) :
    mts_massTest p Φ (blockReconMass p k ω e v) =
      mts_tagTest p.n (mts_mainTags p k σ (e, ω)) Φ (v ∘ σ.symm) := by
  rw [mts_tagTest_mainTags]
  unfold mts_massTest mts_mainClockTest blockReconMass
  simp only [mts_blockClockSpeed_eq_sum, mul_div_assoc]
  rfl

/-- **The physical side as a window integral.** For `Φ ≥ 0` and a window weight `w ≥ 0`,
for every block `k`: `E Σ_α w(u_α)Φ(n p_{αk}) = ∫ Â[n⁻¹Σ_j Φ(n v*D_jv/v*Dv)] d𝔪⁰_W` at
block `0`. Inputs: `RingRotationInvariance`, `OneBlockPalmContract.mass`,
`FreshEigenpairDensityContract`. -/
theorem mts_physical_main (hRot : RingRotationInvariance) (hPalm : OneBlockPalmContract)
    (hFED : FreshEigenpairDensityContract) {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p 0)} (hs : IsBlockSplitting p 0 model Pω)
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p 0 U) (σ : BlockSite p 0 ≃ Fin (Fintype.card (BlockSite p 0)))
    (E : ℝ) {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ u, 0 ≤ w u)
    {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ x, 0 ≤ Φ x) (k : ZMod p.n) :
    physicalTagSide p model E w Φ k =
      (∫⁻ x, ENNReal.ofReal (palmExpect (blockDeformation p 0 σ x.2 x.1) p.c x.1
        (mts_tagTest p.n (mts_mainTags p 0 σ x) Φ)) ∂blockWindowMeasure p 0 U Pω E w).toReal := by
  rw [mts_physicalTagSide_eq_zero hRot]
  have hn0 : (p.n : ℝ≥0∞) ≠ 0 := by exact_mod_cast p.n_pos.ne'
  have hnt : (p.n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  set G : ℝ → ℝ → ℝ≥0∞ := fun l x =>
    ENNReal.ofReal (w (microCoord p E l) * Φ (Set.projIci 0 ((p.n : ℝ) * x))) with hGdef
  have hG : Measurable (Function.uncurry G) :=
    ENNReal.measurable_ofReal.comp ((hwm.comp ((mts_measurable_microCoord p E).comp
      measurable_fst)).mul (Φ.continuous.measurable.comp (continuous_projIci_zero.measurable.comp
        (measurable_const.mul measurable_snd))))
  have hf : Measurable (Function.uncurry fun (l : ℝ) (m : ZMod p.n → ℝ) =>
      ENNReal.ofReal (w (microCoord p E l) * mts_massTest p Φ m)) :=
    ENNReal.measurable_ofReal.comp ((hwm.comp ((mts_measurable_microCoord p E).comp
      measurable_fst)).mul ((mts_measurable_massTest p Φ).comp measurable_snd))
  -- the physical side at block `0` as a lintegral
  have h0 : physicalTagSide p model E w Φ 0 = (∫⁻ H, ∑ α : Fin p.N,
      G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α 0)
      ∂(model.law : Measure p.SiteMatrix)).toReal := by
    unfold physicalTagSide
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun H => Finset.sum_nonneg fun α _ =>
      mul_nonneg (hw0 _) (hΦ _))]
    · congr 1
      refine lintegral_congr fun H => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun α _ => mul_nonneg (hw0 _) (hΦ _)]
    · exact (Finset.measurable_sum _ fun α _ => (hwm.comp ((mts_measurable_microCoord p E).comp
        (mts_measurable_physicalOrderedEigenvalue p α))).mul (Φ.continuous.measurable.comp
        (continuous_projIci_zero.measurable.comp (measurable_const.mul
          (measurable_physicalOrderedBlockMass p α 0))))).aestronglyMeasurable
  -- averaging over the blocks
  have hsum := mts_lintegral_sum_blocks p hRot model G hG
  have havg : ∀ H : p.SiteMatrix, ∑ α : Fin p.N, ∑ s : ZMod p.n,
      G (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α s) =
      (p.n : ℝ≥0∞) * ∑ α : Fin p.N, ENNReal.ofReal (w (microCoord p E
        (physicalOrderedEigenvalue p H α)) * mts_massTest p Φ (blockMassVector p H α)) := by
    intro H
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hGdef]
    simp only
    rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (hw0 _) (hΦ _), ← Finset.mul_sum,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    unfold mts_massTest blockMassVector
    have : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n_pos.ne'
    field_simp
  simp only [havg] at hsum
  rw [lintegral_const_mul' _ _ hnt] at hsum
  have hJ := (ENNReal.mul_right_inj hn0 hnt).1 hsum
  -- the block-`0` Palm form, the coarea formula and the window measure
  have hinv : ∀ (l : ℝ) (q : ZMod p.n → ℝ) (j : ZMod p.n),
      (fun (l : ℝ) (m : ZMod p.n → ℝ) => ENNReal.ofReal (w (microCoord p E l) *
        mts_massTest p Φ m)) l (fun i => q (i + j)) =
      (fun (l : ℝ) (m : ZMod p.n → ℝ) => ENNReal.ofReal (w (microCoord p E l) *
        mts_massTest p Φ m)) l q := by
    intro l q j
    simp only [mts_massTest]
    congr 3
    exact Fintype.sum_equiv (Equiv.addRight j) _ _ fun i => rfl
  have hB := mts_lintegral_palm_block0 hRot p model _ hf hinv
  rw [h0, ← hJ, hB, mts_physical_lintegral p 0 hPalm hs U hU E hwm hw0
    (mts_measurable_massTest p Φ), mts_window_lintegral p 0 hFED hs U hU σ E hwm p.n
      (mts_mainTags p 0 σ) (mts_measurable_mainTags p 0 σ) hΦ]
  simp only [mts_massTest_blockReconMass p 0 σ]

/-- **The block-`0` atom on the physical side.** The window integral of the Palm three-tag
test is at most `2 E Σ_α w(u_α) Σ_j p_{αj}²`. -/
theorem mts_physical_atom (hRot : RingRotationInvariance) (hPalm : OneBlockPalmContract)
    (hFED : FreshEigenpairDensityContract) {model : p.GaussianRingModel}
    {Pω : Measure (BlockState p 0)} (hs : IsBlockSplitting p 0 model Pω)
    (U : (BlockSite p 0 → ℂ) → Matrix (BlockSite p 0) (BlockFrameIndex p) ℂ)
    (hU : IsBlockFrame p 0 U) (σ : BlockSite p 0 ≃ Fin (Fintype.card (BlockSite p 0)))
    (E : ℝ) {w : ℝ → ℝ} (hwm : Measurable w) (hw0 : ∀ u, 0 ≤ w u) :
    (∫⁻ x, ENNReal.ofReal (palmExpect (blockDeformation p 0 σ x.2 x.1) p.c x.1
        (mts_tagTest 3 (mts_atomTags p 0 σ x) mts_tent)) ∂blockWindowMeasure p 0 U Pω E w) ≤
      2 * ∫⁻ H, ENNReal.ofReal (blockAtomFunctional p E w H)
        ∂(model.law : Measure p.SiteMatrix) := by
  rw [mts_window_lintegral p 0 hFED hs U hU σ E hwm 3 (mts_atomTags p 0 σ)
    (mts_measurable_atomTags p 0 σ) mts_tent_nonneg]
  have hΘ : Measurable (fun m : ZMod p.n → ℝ => 2 * m 0) :=
    measurable_const.mul (measurable_pi_apply 0)
  have hle : ∀ ω e, ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p 0 U ω e ℓ
      (fun v => ENNReal.ofReal (mts_tagTest 3 (mts_atomTags p 0 σ (e, ω)) mts_tent (v ∘ σ.symm)))
      ≤ ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p 0 U ω e ℓ
      (fun v => ENNReal.ofReal (2 * blockReconMass p 0 ω e v 0)) := by
    intro ω e
    refine Finset.sum_le_sum fun ℓ _ => ?_
    unfold blockSectorFiber
    refine lintegral_mono fun v => lintegral_mono fun G' => ?_
    refine mul_le_mul_right ?_ _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mts_tagTest_atomTags]
    have hb := (mts_atomClockTest_bounds p 0 (mts_fieldClock_nonneg p 0 e ω v)).2
    unfold blockReconMass
    rw [mts_blockClockSpeed_eq_sum]
    exact hb
  calc _ ≤ ∫⁻ ω, ∫⁻ e, ENNReal.ofReal ((p.n : ℝ) * w (microCoord p E e)) *
        ∑ ℓ ∈ Finset.range p.W, blockSectorFiber p 0 U ω e ℓ
          (fun v => ENNReal.ofReal (2 * blockReconMass p 0 ω e v 0)) ∂volume ∂Pω :=
        lintegral_mono fun ω => lintegral_mono fun e => mul_le_mul_right (hle ω e) _
    _ = (p.n : ℝ≥0∞) * ∫⁻ H, ∑ α : Fin p.N, ENNReal.ofReal (physicalOrderedBlockMass p H α 0) *
        ENNReal.ofReal (w (microCoord p E (physicalOrderedEigenvalue p H α)) *
          (2 * blockMassVector p H α 0)) ∂(model.law : Measure p.SiteMatrix) :=
        (mts_physical_lintegral p 0 hPalm hs U hU E hwm hw0 hΘ).symm
    _ = 2 * ((p.n : ℝ≥0∞) * ∫⁻ H, ∑ α : Fin p.N,
        (fun l x => ENNReal.ofReal (w (microCoord p E l) * x ^ 2))
          (physicalOrderedEigenvalue p H α) (physicalOrderedBlockMass p H α 0)
        ∂(model.law : Measure p.SiteMatrix)) := by
        rw [mul_left_comm, ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
        congr 1
        refine lintegral_congr fun H => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        simp only [blockMassVector]
        rw [← ENNReal.ofReal_mul (physicalOrderedBlockMass_nonneg _ _ _ _),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    _ = 2 * ∫⁻ H, ENNReal.ofReal (blockAtomFunctional p E w H)
        ∂(model.law : Measure p.SiteMatrix) := by
        have hG : Measurable (Function.uncurry fun (l x : ℝ) =>
            ENNReal.ofReal (w (microCoord p E l) * x ^ 2)) :=
          ENNReal.measurable_ofReal.comp ((hwm.comp ((mts_measurable_microCoord p E).comp
            measurable_fst)).mul (measurable_snd.pow_const 2))
        rw [← mts_lintegral_sum_blocks p hRot model _ hG]
        congr 1
        refine lintegral_congr fun H => ?_
        unfold blockAtomFunctional
        rw [ENNReal.ofReal_sum_of_nonneg fun α _ => mul_nonneg (abs_nonneg _)
          (Finset.sum_nonneg fun s _ => sq_nonneg _)]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (hw0 _) (sq_nonneg _),
          ← Finset.mul_sum, abs_of_nonneg (hw0 _)]

end Physical

end BlockBand.Endpoints
