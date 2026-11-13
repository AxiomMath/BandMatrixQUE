module

public import BlockBand.Endpoints.Normalization.LeadProfileAssemblyFinal
public import BlockBand.Endpoints.Normalization.LeadProfileDeletion

/-!
# The physical lead-profile theorem: deterministic algebra of the reconstruction

We express the reconstructed block masses and profile cylinders as ratios of quadratic forms in
the probe vector.

**Objects.** For a one-block exterior `ω = (H_R, C)` of block `k` and an energy `e`:
* `liftMatrix`: the reconstruction matrix `L` (`p.Site × BlockSite`) with `L v = blockLift ω e v`
  (`liftMatrix_mulVec`): identity rows at block `k`, rows `-T(e)` off the block;
* `liftForm f = Lᴴ diag(f) L` for a real site weight `f`, with
  `Re v*(liftForm f)v = Σ_y f(y) |(Lv)_y|²` (`quadForm_liftForm`);
* `clockForm = liftForm 1`: `blockClockSpeed ω e v = Re v*(clockForm)v` (`blockClockSpeed_eq`);
* `blockForm j = liftForm 1_{block j}`: `blockReconMass ω e v j = Re v*Q_jv / Re v*Dv`
  (`blockReconMass_eq`), and `blockForm k = 1` (`blockForm_self`).

**Main results.**
* `reconMatrixObs_vecMulVec`: every mass-vector observable `g(p(v,e))` is a measurable function of
  the projector `vv*` (`measurable_reconMatrixObs`): the form used by
  `blockSector_ratio_eq_palmExpect`;
* `liftForm_posSemidef`, `liftForm_isSandwiched`: `liftForm f ⪰ 0` for `f ≥ 0`, and
  `-D ⪯ liftForm f ⪯ D` for `|f| ≤ 1`, `D = clockForm`;
* `cylinderVec_rotation_eq_ratioCube` (the cylinder identity, exact for every `v`):
  `(∫ φ_i d ℛ_{s/n} ν(p(v,e)))_i = ratioCube (B^s) D d^s v` with
  `B^s_i = liftForm (y ↦ φ_i(s/n + y_1/n))` and the constant default `d^s_i = φ_i(s/n)`;
* `blockReconMass_self_eq_ratioCube`: `p_k(v,e)` is the single ratio `Re v*v / Re v*Dv`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

namespace LeadGaussian

open MeasureTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open scoped BoundedContinuousFunction ComplexConjugate ComplexOrder

section Lift

variable (p : Parameters) (k : ZMod p.n) (ω : BlockState p k) (e : ℝ)

/-- The reconstruction matrix `L`: `L v = blockLift ω e v`. -/
def liftMatrix : Matrix p.Site (BlockSite p k) ℂ := fun y x =>
  if hy : y.1 = k then (if (⟨y, hy⟩ : BlockSite p k) = x then 1 else 0)
  else -(physicalCoareaT ω.1 ω.2 e ⟨y, hy⟩ x)

theorem liftMatrix_mulVec (v : BlockSite p k → ℂ) :
    liftMatrix p k ω e *ᵥ v = blockLift p k ω e v := by
  funext y
  unfold liftMatrix blockLift
  by_cases hy : y.1 = k
  · simp [hy, mulVec, dotProduct]
  · simp [hy, mulVec, dotProduct, Finset.sum_neg_distrib]

/-- `liftForm f = Lᴴ diag(f) L`. -/
def liftForm (f : p.Site → ℝ) : Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  (liftMatrix p k ω e)ᴴ * Matrix.diagonal (fun y => (f y : ℂ)) * liftMatrix p k ω e

theorem re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem re_star_dotProduct_self {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (star u ⬝ᵥ u).re = ∑ i, ‖u i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, re_star_mul_self]

theorem quadForm_liftForm (f : p.Site → ℝ) (v : BlockSite p k → ℂ) :
    quadForm (liftForm p k ω e f) v = ∑ y, f y * ‖blockLift p k ω e v y‖ ^ 2 := by
  unfold quadForm liftForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, liftMatrix_mulVec]
  simp only [mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm, Complex.re_ofReal_mul, re_star_mul_self]

theorem liftForm_isHermitian (f : p.Site → ℝ) : (liftForm p k ω e f).IsHermitian := by
  unfold liftForm
  refine isHermitian_conjTranspose_mul_mul _ ?_
  rw [IsHermitian, diagonal_conjTranspose]
  congr 1
  funext y
  simp [Complex.conj_ofReal]

theorem liftForm_posSemidef (f : p.Site → ℝ) (hf : ∀ y, 0 ≤ f y) :
    (liftForm p k ω e f).PosSemidef := by
  unfold liftForm
  refine PosSemidef.conjTranspose_mul_mul_same (posSemidef_diagonal_iff.mpr fun y => ?_) _
  exact_mod_cast hf y

theorem liftForm_sub (f g : p.Site → ℝ) :
    liftForm p k ω e f - liftForm p k ω e g = liftForm p k ω e (fun y => f y - g y) := by
  unfold liftForm
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  push_cast
  rfl

theorem liftForm_add (f g : p.Site → ℝ) :
    liftForm p k ω e f + liftForm p k ω e g = liftForm p k ω e (fun y => f y + g y) := by
  unfold liftForm
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  push_cast
  rfl

/-- The clock form `D = Lᴴ L`. -/
def clockForm : Matrix (BlockSite p k) (BlockSite p k) ℂ := liftForm p k ω e (fun _ => 1)

/-- The block-`j` mass form `Q_j = Lᴴ 1_{block j} L`. -/
def blockForm (j : ZMod p.n) : Matrix (BlockSite p k) (BlockSite p k) ℂ :=
  liftForm p k ω e (fun y => if y.1 = j then 1 else 0)

/-- `-D ⪯ liftForm f ⪯ D` for `|f| ≤ 1`. -/
theorem liftForm_isSandwiched (f : p.Site → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    IsSandwichedOn (liftForm p k ω e f) (clockForm p k ω e) := by
  refine ⟨liftForm_isHermitian p k ω e f, ?_, ?_⟩
  · rw [clockForm, liftForm_sub]
    exact liftForm_posSemidef p k ω e _ fun y => by linarith [(abs_le.mp (hf y)).2]
  · rw [clockForm, liftForm_add]
    exact liftForm_posSemidef p k ω e _ fun y => by linarith [(abs_le.mp (hf y)).1]

theorem quadForm_blockForm (j : ZMod p.n) (v : BlockSite p k → ℂ) :
    quadForm (blockForm p k ω e j) v = ∑ a : Fin p.W, ‖blockLift p k ω e v (j, a)‖ ^ 2 := by
  rw [blockForm, quadForm_liftForm, Fintype.sum_prod_type,
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem quadForm_clockForm (v : BlockSite p k → ℂ) :
    quadForm (clockForm p k ω e) v = ∑ y, ‖blockLift p k ω e v y‖ ^ 2 := by
  rw [clockForm, quadForm_liftForm]
  simp only [one_mul]

theorem quadForm_blockForm_nonneg (j : ZMod p.n) (v : BlockSite p k → ℂ) :
    0 ≤ quadForm (blockForm p k ω e j) v := by
  rw [quadForm_blockForm]; positivity

theorem sum_quadForm_blockForm (v : BlockSite p k → ℂ) :
    ∑ j, quadForm (blockForm p k ω e j) v = quadForm (clockForm p k ω e) v := by
  simp only [quadForm_blockForm, quadForm_clockForm]
  rw [Fintype.sum_prod_type]

/-- `blockClockSpeed ω e v = Σ_y |(Lv)_y|²` (`D(e) = I + T*T = LᴴL`). -/
theorem blockClockSpeed_eq (v : BlockSite p k → ℂ) :
    blockClockSpeed p k ω e v = quadForm (clockForm p k ω e) v := by
  rw [quadForm_clockForm]
  have h1 : blockClockSpeed p k ω e v =
      (∑ x, ‖v x‖ ^ 2) + ∑ z, ‖(physicalCoareaT ω.1 ω.2 e *ᵥ v) z‖ ^ 2 := by
    unfold blockClockSpeed physicalCoareaD schurClock
    rw [add_mulVec, one_mulVec, dotProduct_add, ← mulVec_mulVec, dotProduct_mulVec,
      ← star_mulVec, Complex.add_re, re_star_dotProduct_self, re_star_dotProduct_self]
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = k)]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp [blockLift, y.2]
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp [blockLift, y.2]

theorem quadForm_clockForm_nonneg (v : BlockSite p k → ℂ) :
    0 ≤ quadForm (clockForm p k ω e) v := by
  rw [quadForm_clockForm]; positivity

/-- `p_j(v,e) = Re v*Q_jv / Re v*Dv`. -/
theorem blockReconMass_eq (v : BlockSite p k → ℂ) (j : ZMod p.n) :
    blockReconMass p k ω e v j =
      quadForm (blockForm p k ω e j) v / quadForm (clockForm p k ω e) v := by
  rw [blockReconMass, blockClockSpeed_eq, quadForm_blockForm]

/-- `Q_k = 1`: the block rows of `L` are the identity. -/
theorem blockForm_self : blockForm p k ω e k = 1 := by
  ext x x'
  rw [blockForm, liftForm, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = k)]
  have hoff : ∑ y : {y : p.Site // ¬ y.1 = k}, star (liftMatrix p k ω e y x) *
      (((if (y : p.Site).1 = k then (1 : ℝ) else 0 : ℝ)) : ℂ) * liftMatrix p k ω e y x' = 0 :=
    Finset.sum_eq_zero fun y _ => by simp [y.2]
  rw [hoff, add_zero]
  have hblk : ∀ y : BlockSite p k, star (liftMatrix p k ω e y x) *
      (((if (y : p.Site).1 = k then (1 : ℝ) else 0 : ℝ)) : ℂ) * liftMatrix p k ω e y x' =
      if y = x then (1 : Matrix (BlockSite p k) (BlockSite p k) ℂ) x x' else 0 := by
    intro y
    simp only [liftMatrix, y.2, ↓reduceIte, ↓reduceDIte, Subtype.coe_eta]
    by_cases h : y = x
    · subst h; simp [one_apply]
    · simp [h]
  change ∑ y : BlockSite p k, _ = _
  simp_rw [hblk]
  simp

/-- `p_k(v,e) = Re v*v / Re v*Dv ∈ [0,1]`. -/
theorem blockReconMass_self_le_one (v : BlockSite p k → ℂ) :
    0 ≤ blockReconMass p k ω e v k ∧ blockReconMass p k ω e v k ≤ 1 := by
  rw [blockReconMass_eq]
  have h0 := quadForm_blockForm_nonneg p k ω e k v
  have hS := sum_quadForm_blockForm p k ω e v
  have hle : quadForm (blockForm p k ω e k) v ≤ quadForm (clockForm p k ω e) v := by
    rw [← hS]
    exact Finset.single_le_sum (fun j _ => quadForm_blockForm_nonneg p k ω e j v)
      (Finset.mem_univ k)
  exact ⟨div_nonneg h0 (h0.trans hle), div_le_one_of_le₀ hle (h0.trans hle)⟩

/-!
### Mass-vector observables as functions of the projector
-/

theorem trace_mul_vecMulVec_star {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) (v : ι → ℂ) :
    (Q * vecMulVec v (star v)).trace = star v ⬝ᵥ (Q *ᵥ v) := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A mass-vector observable `g` read on a matrix `X` (in place of `vv*`). -/
def reconMatrixObs (g : (ZMod p.n → ℝ) → ℝ)
    (X : Matrix (BlockSite p k) (BlockSite p k) ℂ) : ℝ :=
  g (fun j => (blockForm p k ω e j * X).trace.re / (clockForm p k ω e * X).trace.re)

theorem reconMatrixObs_vecMulVec (g : (ZMod p.n → ℝ) → ℝ) (v : BlockSite p k → ℂ) :
    reconMatrixObs p k ω e g (vecMulVec v (star v)) = g (blockReconMass p k ω e v) := by
  unfold reconMatrixObs
  congr 1
  funext j
  rw [blockReconMass_eq, trace_mul_vecMulVec_star, trace_mul_vecMulVec_star]
  rfl

theorem continuous_trace_mul_re {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℂ) :
    Continuous fun X : Matrix ι ι ℂ => (Q * X).trace.re :=
  Complex.continuous_re.comp (continuous_const.matrix_mul continuous_id).matrix_trace

theorem measurable_reconMatrixObs (g : (ZMod p.n → ℝ) → ℝ) (hg : Measurable g) :
    Measurable (reconMatrixObs p k ω e g) := by
  unfold reconMatrixObs
  exact hg.comp (measurable_pi_iff.mpr fun j =>
    (continuous_trace_mul_re _).measurable.div (continuous_trace_mul_re _).measurable)

/-!
### The cylinder identity
-/

theorem integral_massVectorMeasure (q : ZMod p.n → ℝ) (hq : ∀ j, 0 ≤ q j) (h : Torus → ℝ)
    (hh : Continuous h) :
    ∫ r, h r ∂massVectorMeasure p q = ∑ j, q j * h (physicalProfileGrid p j) := by
  unfold massVectorMeasure
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hh.measurable.stronglyMeasurable,
    ENNReal.toReal_ofReal (hq j), smul_eq_mul]

theorem integral_massProfileRotation (a : Torus) (ν : MassProfile) (h : Torus → ℝ)
    (hh : Continuous h) :
    ∫ r, h r ∂(massProfileRotation a ν : Measure Torus) = ∫ r, h (a + r) ∂(ν : Measure Torus) := by
  change ∫ r, h r ∂(Measure.map (Homeomorph.addLeft a) (ν : Measure Torus)) = _
  rw [integral_map (Homeomorph.addLeft a).continuous.measurable.aemeasurable
    hh.aestronglyMeasurable]
  rfl

theorem quadForm_liftForm_block (f : ZMod p.n → ℝ) (v : BlockSite p k → ℂ) :
    quadForm (liftForm p k ω e (fun y => f y.1)) v =
      ∑ j, f j * quadForm (blockForm p k ω e j) v := by
  rw [quadForm_liftForm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [quadForm_blockForm, Finset.mul_sum]

/-- **Cylinder identity** (exact, every `v`): the clamped spatial tests of the rotated
reconstructed profile are the clamped ratios `v*B^s_iv / v*Dv`, default `φ_i(s/n)`. -/
theorem cylinderVec_rotation_eq_ratioCube {m : ℕ} (φ : Fin m → C(Torus, ℝ)) (s : ZMod p.n)
    (v : BlockSite p k → ℂ) :
    cylinderVec φ (massProfileRotation (physicalProfileGrid p s)
        (massVectorProfile p (blockReconMass p k ω e v))) =
      ratioCube (fun i => liftForm p k ω e
          (fun y => φ i (physicalProfileGrid p s + physicalProfileGrid p y.1)))
        (clockForm p k ω e) (fun _ i => φ i (physicalProfileGrid p s)) v := by
  funext i
  unfold cylinderVec ratioCube
  congr 1
  set a := physicalProfileGrid p s
  rw [integral_massProfileRotation a _ _ (φ i).continuous]
  by_cases hS : quadForm (clockForm p k ω e) v = 0
  · simp only [hS, ↓reduceIte]
    have hq : blockReconMass p k ω e v = fun _ => 0 := by
      funext j; rw [blockReconMass_eq, hS, div_zero]
    have hnot : ¬ IsProbabilityMeasure (massVectorMeasure p (fun _ => (0 : ℝ))) := by
      intro h
      have := h.measure_univ
      simp [massVectorMeasure] at this
    have hν : (massVectorProfile p (blockReconMass p k ω e v) : Measure Torus) =
        Measure.dirac 0 := by
      rw [hq]; simp [massVectorProfile, hnot]
    rw [hν, integral_dirac, add_zero]
  · simp only [hS, ↓reduceIte]
    have hS0 := quadForm_clockForm_nonneg p k ω e v
    have hSpos : 0 < quadForm (clockForm p k ω e) v := lt_of_le_of_ne hS0 (Ne.symm hS)
    have hq0 : ∀ j, 0 ≤ blockReconMass p k ω e v j := fun j => by
      rw [blockReconMass_eq]; exact div_nonneg (quadForm_blockForm_nonneg p k ω e j v) hS0
    have hprob : IsProbabilityMeasure (massVectorMeasure p (blockReconMass p k ω e v)) := by
      constructor
      unfold massVectorMeasure
      simp only [Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply, measure_univ,
        smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq0 j)]
      simp only [blockReconMass_eq]
      rw [← Finset.sum_div, sum_quadForm_blockForm, div_self hS, ENNReal.ofReal_one]
    rw [coe_massVectorProfile_of p _ hprob,
      integral_massVectorMeasure p _ hq0 (fun r => φ i (a + r)) (by fun_prop)]
    rw [quadForm_liftForm_block p k ω e (fun j => φ i (a + physicalProfileGrid p j)),
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blockReconMass_eq]
    ring

/-- `p_k(v,e)` is the single clamped ratio `Re v*v / Re v*Dv` (default `0`). -/
theorem blockReconMass_self_eq_ratioCube (v : BlockSite p k → ℂ) :
    blockReconMass p k ω e v k =
      ((ratioCube (fun _ : Fin 1 => blockForm p k ω e k) (clockForm p k ω e)
        (fun _ _ => 0) v 0 : Set.Icc (-1 : ℝ) 1) : ℝ) := by
  unfold ratioCube
  by_cases hS : quadForm (clockForm p k ω e) v = 0
  · simp only [hS, ↓reduceIte]
    rw [blockReconMass_eq, hS, div_zero,
      Set.projIcc_of_mem _ ⟨by norm_num, by norm_num⟩]
  · simp only [hS, ↓reduceIte]
    rw [← blockReconMass_eq]
    obtain ⟨h0, h1⟩ := blockReconMass_self_le_one p k ω e v
    rw [Set.projIcc_of_mem _ ⟨by linarith, h1⟩]

end Lift

/-!
### Reindexing to `Fin N`
-/

section Reindex

variable {ι : Type*} [Fintype ι] {N : ℕ}

theorem quadForm_reindex (σ : ι ≃ Fin N) (Q : Matrix ι ι ℂ) (u : Fin N → ℂ) :
    quadForm (Matrix.reindex σ σ Q) u = quadForm Q (fun x => u (σ x)) := by
  unfold quadForm
  congr 1
  simp only [dotProduct, mulVec, reindex_apply, submatrix_apply, Pi.star_apply]
  rw [← σ.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← σ.sum_comp]
  simp

theorem ratioCube_reindex {m : ℕ} (σ : ι ≃ Fin N) (B : Fin m → Matrix ι ι ℂ) (D : Matrix ι ι ℂ)
    (d : (ι → ℂ) → Fin m → ℝ) (u : Fin N → ℂ) :
    ratioCube (fun i => Matrix.reindex σ σ (B i)) (Matrix.reindex σ σ D)
        (fun u' => d (fun x => u' (σ x))) u = ratioCube B D d (fun x => u (σ x)) := by
  unfold ratioCube
  simp only [quadForm_reindex]

theorem reindex_mulVec_apply (σ : ι ≃ Fin N) (M : Matrix ι ι ℂ) (g : Fin N → ℂ) (x : ι) :
    (Matrix.reindex σ σ M *ᵥ g) (σ x) = (M *ᵥ (fun y => g (σ y))) x := by
  simp only [mulVec, dotProduct, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  rw [← σ.sum_comp]
  simp

theorem isSandwiched_reindex (σ : ι ≃ Fin N) {B D : Matrix ι ι ℂ} (h : IsSandwichedOn B D) :
    IsSandwiched (Matrix.reindex σ σ B) (Matrix.reindex σ σ D) := by
  obtain ⟨hB, h1, h2⟩ := h
  refine ⟨hB.submatrix _, ?_, ?_⟩
  · have := h1.submatrix σ.symm
    convert this using 1
    ext i j; simp [reindex_apply]
  · have := h2.submatrix σ.symm
    convert this using 1
    ext i j; simp [reindex_apply]

end Reindex

end LeadGaussian

end BlockBand.Endpoints.Normalization
