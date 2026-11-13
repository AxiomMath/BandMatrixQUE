module

public import BlockBand.Transmission.Bridge.Marginal

/-!
# Ginibre bonds are almost surely invertible

No Lebesgue measure on matrices is needed: the determinant is affine in the real part
`r₀₀₀` of the `(0,0)` entry, with slope the `(0,0)` cofactor, which does not involve the first
row (`det_ginibreSample_affine`). Conditioning on all other real coordinates
(`pi_map_update`), the zero set in `r₀₀₀` is a single point when the cofactor is nonzero, and a
real Gaussian of positive variance has no atoms (`null_affine_coord`). Induction on the size
(the cofactor is again a Ginibre determinant, `infinitePi_map_reindex`) gives
`pi_det_ginibreSample_null` for every atomless real law of the coordinates.

Main results, for `t ≠ 0` (equivalently `b > 0`, `W ≥ 1` for `t = (b/W)₊`):
`ae_isUnit_ginibreMeasure`, `ae_isUnit_layerLaw_bond`, `ae_isUnit_pathLaw_bond`,
`ae_isUnit_growth_bond`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal Matrix

/-!
## Conditioning on one coordinate
-/

theorem measurable_update_coord {ι : Type*} [DecidableEq ι] (i0 : ι) :
    Measurable fun p : (ι → ℝ) × ℝ => Function.update p.1 i0 p.2 := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = i0
  · subst h; simpa using measurable_snd
  · simp only [Function.update_of_ne h]; exact (measurable_pi_apply i).comp measurable_fst

/-- Overwriting coordinate `i0` of an iid sample by an independent copy keeps the law. -/
theorem pi_map_update {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (i0 : ι) :
    ((Measure.pi fun _ : ι => μ).prod μ).map (fun p => Function.update p.1 i0 p.2) =
      Measure.pi fun _ : ι => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_update_coord i0) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i0 p.2) ⁻¹' Set.univ.pi s =
      (Set.univ.pi (Function.update s i0 Set.univ)) ×ˢ s i0 := by
    ext ⟨r, t⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h i0⟩
      by_cases hi : i = i0
      · subst hi; simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = i0
      · subst hi; simpa using h2
      · simpa [Function.update_of_ne hi] using h1 i
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i0,
    Fintype.prod_eq_mul_prod_compl i0 (fun i => μ (s i))]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (by simpa using hi)]

/-- If `c, g` do not depend on coordinate `i0` and the law has no atoms, then
`{c ≠ 0, r_{i0} c + g = 0}` is null. -/
theorem null_affine_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) (i0 : ι) (c g : (ι → ℝ) → ℂ)
    (hc : Measurable c) (hg : Measurable g)
    (hci : ∀ r t, c (Function.update r i0 t) = c r)
    (hgi : ∀ r t, g (Function.update r i0 t) = g r) :
    (Measure.pi fun _ : ι => μ) {r | c r ≠ 0 ∧ (r i0 : ℂ) * c r + g r = 0} = 0 := by
  have hF : Measurable fun r : ι → ℝ => (r i0 : ℂ) * c r + g r :=
    (Complex.measurable_ofReal.comp (measurable_pi_apply i0)).mul hc |>.add hg
  have hS : MeasurableSet {r : ι → ℝ | c r ≠ 0 ∧ (r i0 : ℂ) * c r + g r = 0} :=
    ((measurableSet_singleton (0 : ℂ)).compl.preimage hc).inter
      ((measurableSet_singleton (0 : ℂ)).preimage hF)
  rw [← pi_map_update μ i0, Measure.map_apply (measurable_update_coord i0) hS]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i0 p.2) ⁻¹'
      {r | c r ≠ 0 ∧ (r i0 : ℂ) * c r + g r = 0} =
        {p | c p.1 ≠ 0 ∧ (p.2 : ℂ) * c p.1 + g p.1 = 0} := by
    ext ⟨r, t⟩; simp [hci, hgi]
  rw [hpre]
  have hS' : MeasurableSet {p : (ι → ℝ) × ℝ | c p.1 ≠ 0 ∧ (p.2 : ℂ) * c p.1 + g p.1 = 0} :=
    ((measurableSet_singleton (0 : ℂ)).compl.preimage (hc.comp measurable_fst)).inter
      ((measurableSet_singleton (0 : ℂ)).preimage
        (((Complex.measurable_ofReal.comp measurable_snd).mul (hc.comp measurable_fst)).add
          (hg.comp measurable_fst)))
  rw [Measure.measure_prod_null hS']
  refine Filter.Eventually.of_forall fun r => ?_
  have hsub : (Prod.mk r ⁻¹' {p : (ι → ℝ) × ℝ | c p.1 ≠ 0 ∧ (p.2 : ℂ) * c p.1 + g p.1 = 0}).Subsingleton := by
    rintro t ⟨hc0, ht⟩ t' ⟨-, ht'⟩
    have : ((t : ℂ) - t') * c r = 0 := by linear_combination ht - ht'
    exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
  rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
  · simp [h]
  · simp [h, hμ]

/-!
## The Ginibre determinant
-/

/-- The cofactor coordinates `(i, j, k) ↦ (i+1, j+1, k)`. -/
def minorIndex (n : ℕ) (q : Fin n × Fin n × Fin 2) : Fin (n + 1) × Fin (n + 1) × Fin 2 :=
  (q.1.succ, q.2.1.succ, q.2.2)

theorem minorIndex_injective (n : ℕ) : Function.Injective (minorIndex n) := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  simp only [minorIndex, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; rfl

/-- `det G(r) = r₀₀₀ · cof₀₀ + det G(r with r₀₀₀ = 0)`. -/
theorem det_ginibreSample_affine (n : ℕ) (r : Fin (n + 1) × Fin (n + 1) × Fin 2 → ℝ) :
    (ginibreSample (Fin (n + 1)) (Fin (n + 1)) r).det =
      (r (0, 0, 0) : ℂ) * (ginibreSample (Fin n) (Fin n) fun q => r (minorIndex n q)).det +
        (ginibreSample (Fin (n + 1)) (Fin (n + 1)) (Function.update r (0, 0, 0) 0)).det := by
  have hminor : ∀ j : Fin (n + 1),
      (ginibreSample (Fin (n + 1)) (Fin (n + 1)) r).submatrix Fin.succ j.succAbove =
      (ginibreSample (Fin (n + 1)) (Fin (n + 1))
        (Function.update r (0, 0, 0) 0)).submatrix Fin.succ j.succAbove := by
    intro j; ext i l; simp [ginibreSample]
  have h0' : (ginibreSample (Fin (n + 1)) (Fin (n + 1))
        (Function.update r (0, 0, 0) 0)).submatrix Fin.succ Fin.succ =
      ginibreSample (Fin n) (Fin n) fun q => r (minorIndex n q) := by
    ext i l; simp [ginibreSample, minorIndex]
  have hcof : (ginibreSample (Fin (n + 1)) (Fin (n + 1)) r).submatrix Fin.succ Fin.succ =
      ginibreSample (Fin n) (Fin n) fun q => r (minorIndex n q) := by
    ext i l; rfl
  have hrow : ∀ j : Fin n, ginibreSample (Fin (n + 1)) (Fin (n + 1)) r 0 j.succ =
      ginibreSample (Fin (n + 1)) (Fin (n + 1)) (Function.update r (0, 0, 0) 0) 0 j.succ := by
    intro j; simp [ginibreSample]
  have h00 : ginibreSample (Fin (n + 1)) (Fin (n + 1)) r 0 0 = (r (0, 0, 0) : ℂ) +
      ginibreSample (Fin (n + 1)) (Fin (n + 1)) (Function.update r (0, 0, 0) 0) 0 0 := by
    simp [ginibreSample]
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero (ginibreSample (Fin (n + 1)) (Fin (n + 1))
    (Function.update r (0, 0, 0) 0)), Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero]
  rw [h0', hcof, h00]
  simp_rw [hrow, hminor]
  simp only [Fin.val_zero, pow_zero]
  ring

theorem measurable_det {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable fun M : Matrix n n ℂ => M.det :=
  (continuous_id.matrix_det).measurable

/-- **The Ginibre determinant vanishes on a null set**, for iid atomless real coordinates. -/
theorem pi_det_ginibreSample_null (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∀ n : ℕ, (Measure.pi fun _ : Fin n × Fin n × Fin 2 => μ)
      {r | (ginibreSample (Fin n) (Fin n) r).det = 0} = 0
  | 0 => by simp [Matrix.det_fin_zero]
  | n + 1 => by
    set c : (Fin (n + 1) × Fin (n + 1) × Fin 2 → ℝ) → ℂ :=
      fun r => (ginibreSample (Fin n) (Fin n) fun q => r (minorIndex n q)).det
    set g : (Fin (n + 1) × Fin (n + 1) × Fin 2 → ℝ) → ℂ :=
      fun r => (ginibreSample (Fin (n + 1)) (Fin (n + 1)) (Function.update r (0, 0, 0) 0)).det
    have hR : Measurable fun (r : Fin (n + 1) × Fin (n + 1) × Fin 2 → ℝ) q => r (minorIndex n q) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    have hc : Measurable c := measurable_det.comp ((measurable_ginibreSample _ _).comp hR)
    have hU : Measurable fun r : Fin (n + 1) × Fin (n + 1) × Fin 2 → ℝ =>
        Function.update r (0, 0, 0) 0 :=
      (measurable_update_coord (0, 0, 0)).comp (measurable_id.prodMk measurable_const)
    have hg : Measurable g := measurable_det.comp ((measurable_ginibreSample _ _).comp hU)
    have hsub : {r | (ginibreSample (Fin (n + 1)) (Fin (n + 1)) r).det = 0} ⊆
        {r | c r = 0} ∪ {r | c r ≠ 0 ∧ (r (0, 0, 0) : ℂ) * c r + g r = 0} := by
      intro r hr
      by_cases h : c r = 0
      · exact Or.inl h
      · exact Or.inr ⟨h, by rw [← det_ginibreSample_affine]; exact hr⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · have hmap := infinitePi_map_reindex μ (minorIndex n) (minorIndex_injective n)
      rw [Measure.infinitePi_eq_pi] at hmap
      have hmeas : MeasurableSet {r : Fin n × Fin n × Fin 2 → ℝ |
          (ginibreSample (Fin n) (Fin n) r).det = 0} :=
        (measurableSet_singleton 0).preimage (measurable_det.comp (measurable_ginibreSample _ _))
      have := pi_det_ginibreSample_null μ hμ n
      rw [← hmap, Measure.map_apply hR hmeas] at this
      exact this
    · refine null_affine_coord μ hμ (0, 0, 0) c g hc hg (fun r t => ?_) (fun r t => ?_)
      · simp only [c]
        congr 3
      · simp only [g, Function.update_idem]

theorem gaussianReal_singleton {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : gaussianReal 0 v {x} = 0 :=
  gaussianReal_absolutelyContinuous 0 hv (Real.volume_singleton)

/-- **Ginibre matrices are almost surely invertible** (`t ≠ 0`). -/
theorem ae_isUnit_ginibreMeasure (W : ℕ) {t : ℝ≥0} (ht : t ≠ 0) :
    ∀ᵐ B ∂ginibreMeasure (Fin W) (Fin W) t, IsUnit B := by
  have hset : MeasurableSet {B : Matrix (Fin W) (Fin W) ℂ | IsUnit B} := by
    have : {B : Matrix (Fin W) (Fin W) ℂ | IsUnit B} = (fun B => B.det) ⁻¹' {0}ᶜ := by
      ext B; simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    rw [this]; exact (measurableSet_singleton 0).compl.preimage measurable_det
  rw [ginibreMeasure_eq, ae_map_iff (measurable_ginibreSample _ _).aemeasurable hset, ae_iff]
  have hv : t / 2 ≠ 0 := by simpa using ht
  simpa [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] using
    pi_det_ginibreSample_null (gaussianReal 0 (t / 2)) (gaussianReal_singleton hv) W

theorem bondVariance_ne_zero {W : ℕ} {b : ℝ} (hb : 0 < b) (hW : 1 ≤ W) :
    Real.toNNReal (b / W) ≠ 0 := by
  rw [Ne, Real.toNNReal_eq_zero, not_le]
  exact div_pos hb (by exact_mod_cast hW)

/-!
## The bonds of the layer and path laws
-/

/-- Every bond of a fresh layer is a.s. invertible (`b > 0`, `W ≥ 1`); covers `freshLaw`. -/
theorem ae_isUnit_layerLaw_bond {W : ℕ} {b : ℝ} (hb : 0 < b) (hW : 1 ≤ W) (σ : LayerShape) :
    ∀ᵐ ω ∂layerLaw W b σ, ∀ a j, IsUnit (ω.2 a j) := by
  simp only [ae_all_iff]
  intro a j
  have hmap : (layerLaw W b σ).map (fun ω => ω.2 a j) =
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
    have : (fun ω : LayerSample W σ => ω.2 a j) =
        (fun v : Fin σ.ports → Matrix (Fin W) (Fin W) ℂ => v j) ∘ (fun u => u a) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j)
      ((measurable_pi_apply a).comp measurable_snd), ← Measure.map_map (measurable_pi_apply a)
      measurable_snd, layerLaw, Measure.map_snd_prod, measure_univ, one_smul,
      (measurePreserving_eval _ a).map_eq, (measurePreserving_eval _ j).map_eq]
  have h := ae_isUnit_ginibreMeasure W (bondVariance_ne_zero hb hW)
  rw [← hmap] at h
  have hm : Measurable fun ω : LayerSample W σ => ω.2 a j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply a).comp measurable_snd)
  exact ae_of_ae_map hm.aemeasurable h

/-- Every internal and port bond of a path under `pathLaw W r b` is a.s. invertible (`b > 0`,
`W ≥ 1`). -/
theorem ae_isUnit_pathLaw_bond {W r : ℕ} {b : ℝ} (hb : 0 < b) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂pathLaw W r b, (∀ i, IsUnit (ω.2.1 i)) ∧ ∀ j, IsUnit (ω.2.2 j) := by
  have h := ae_isUnit_ginibreMeasure W (bondVariance_ne_zero hb hW)
  have hB : ∀ (n : ℕ) (i : Fin n), (Measure.pi fun _ : Fin n =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).map (fun v => v i) =
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) :=
    fun n i => (measurePreserving_eval _ i).map_eq
  have hsnd : (pathLaw W r b).map Prod.snd =
      (Measure.pi fun _ : Fin (r - 1) => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))).prod
        (Measure.pi fun _ : Fin 2 => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) := by
    rw [pathLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have h2 : ∀ᵐ ω ∂pathLaw W r b, ∀ i, IsUnit (ω.2.1 i) := by
    rw [ae_all_iff]; intro i
    have hm : (pathLaw W r b).map (fun ω => ω.2.1 i) =
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
      rw [show (fun ω : PathSample W r => ω.2.1 i) = (fun v => v i) ∘ Prod.fst ∘ Prod.snd from rfl,
        ← Measure.map_map (measurable_pi_apply i) (measurable_fst.comp measurable_snd),
        ← Measure.map_map measurable_fst measurable_snd, hsnd, Measure.map_fst_prod,
        measure_univ, one_smul, hB]
    have h' := h; rw [← hm] at h'
    exact ae_of_ae_map ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).aemeasurable h'
  have h3 : ∀ᵐ ω ∂pathLaw W r b, ∀ j, IsUnit (ω.2.2 j) := by
    rw [ae_all_iff]; intro j
    have hm : (pathLaw W r b).map (fun ω => ω.2.2 j) =
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
      rw [show (fun ω : PathSample W r => ω.2.2 j) = (fun v => v j) ∘ Prod.snd ∘ Prod.snd from rfl,
        ← Measure.map_map (measurable_pi_apply j) (measurable_snd.comp measurable_snd),
        ← Measure.map_map measurable_snd measurable_snd, hsnd, Measure.map_snd_prod,
        measure_univ, one_smul, hB]
    have h' := h; rw [← hm] at h'
    exact ae_of_ae_map ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)).aemeasurable h'
  filter_upwards [h2, h3] with ω h2 h3 using ⟨h2, h3⟩

/-- **Every bond `B_k` of the near-end growth sample is a.s. invertible** (`b > 0`, `W ≥ 1`). -/
theorem ae_isUnit_growth_bond {W : ℕ} {b : ℝ} (hb : 0 < b) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ k, IsUnit (ω.2 k) := by
  rw [ae_all_iff]; intro k
  have hm : (growthPathLaw W b).map (fun ω => ω.2 k) =
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) := by
    rw [show (fun ω : GrowthPath W => ω.2 k) = (fun a => a k) ∘ Prod.snd from rfl,
      ← Measure.map_map (measurable_pi_apply k) measurable_snd, growthPathLaw,
      Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]
  have h := ae_isUnit_ginibreMeasure W (bondVariance_ne_zero hb hW)
  rw [← hm] at h
  exact ae_of_ae_map ((measurable_pi_apply k).comp measurable_snd).aemeasurable h

end BlockBand.Transmission.Bridge
