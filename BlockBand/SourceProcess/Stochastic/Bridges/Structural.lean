module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.StoppedContract
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Structural lemmas for continuous semimartingales: reindexing and affine images

* Algebra of `HasMartingaleModification`: a.e. congruence, `0`, sums, scalar multiples,
  finite sums, and transfer to stopped processes of pathwise a.e. equal processes.
* `IsContinuousSemimartingale.comp_index`: for any map `e : Fin d' → Fin d` (e.g. the
  `λ`-block `i ↦ finSumFinEquiv (Sum.inl i)` of contract (b2)), the sub-vector `Y ∘ e` is a
  continuous semimartingale with characteristics `(β ∘ e, α.submatrix e e)`.
* `IsContinuousSemimartingale.affine` (polarization): for `A : Matrix (Fin d') (Fin d) ℝ`
  and `c : Fin d' → ℝ`, `A Y + c` is a continuous semimartingale with characteristics
  `(A β, A α Aᵀ)`. The bracket clause of the image is the bilinear combination
  `∑_{i,j} A_{ki} A_{lj} (N^i N^j - ∫ α^{ij})` of the original bracket clauses.
-/

namespace BlockBand.SourceProcess.Stochastic.Bridges
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-!
### Martingale modifications
-/

/-- A martingale modification transfers along timewise a.e. equality. -/
theorem hasMartingaleModification_congr {X X' : ℝ≥0 → Ω → ℝ}
    (h : HasMartingaleModification Q 𝓖 X) (he : ∀ t, X t =ᵐ[Q] X' t) :
    HasMartingaleModification Q 𝓖 X' := by
  obtain ⟨M, hM, hMX⟩ := h
  exact ⟨M, hM, fun t => (hMX t).trans (he t)⟩

theorem hasMartingaleModification_zero :
    HasMartingaleModification Q 𝓖 (fun _ _ => (0 : ℝ)) :=
  ⟨0, martingale_zero _ _ _, fun _ => ae_of_all _ fun _ => rfl⟩

theorem hasMartingaleModification_add {X X' : ℝ≥0 → Ω → ℝ}
    (h : HasMartingaleModification Q 𝓖 X) (h' : HasMartingaleModification Q 𝓖 X') :
    HasMartingaleModification Q 𝓖 (fun t ω => X t ω + X' t ω) := by
  obtain ⟨M, hM, hMX⟩ := h
  obtain ⟨M', hM', hMX'⟩ := h'
  exact ⟨M + M', hM.add hM', fun t => (hMX t).add (hMX' t)⟩

theorem hasMartingaleModification_const_mul {X : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (h : HasMartingaleModification Q 𝓖 X) :
    HasMartingaleModification Q 𝓖 (fun t ω => c * X t ω) := by
  obtain ⟨M, hM, hMX⟩ := h
  exact ⟨c • M, hM.smul c, fun t => (hMX t).mono fun ω hω => by
    simp only [Pi.smul_apply, smul_eq_mul, hω]⟩

theorem hasMartingaleModification_finsetSum {ι : Type*} (s : Finset ι)
    {X : ι → ℝ≥0 → Ω → ℝ} (h : ∀ i ∈ s, HasMartingaleModification Q 𝓖 (X i)) :
    HasMartingaleModification Q 𝓖 (fun t ω => ∑ i ∈ s, X i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasMartingaleModification_zero (Q := Q) (𝓖 := 𝓖))
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact hasMartingaleModification_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Processes that agree for all times on a.e. path have a.e. equal stopped values. -/
theorem stoppedProcess_ae_eq_of_ae_forall {E : Type*} {X X' : ℝ≥0 → Ω → E}
    (h : ∀ᵐ ω ∂Q, ∀ t, X t ω = X' t ω) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    stoppedProcess X τ t =ᵐ[Q] stoppedProcess X' τ t := by
  filter_upwards [h] with ω hω
  simp only [stoppedProcess_eq_stopTime, hω]

/-- A stopped process with a martingale modification, transferred to a process that agrees
with it for all times on a.e. path. -/
theorem hasMartingaleModification_stopped_congr {X X' : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} (h : HasMartingaleModification Q 𝓖 (stoppedProcess X τ))
    (he : ∀ᵐ ω ∂Q, ∀ t, X t ω = X' t ω) :
    HasMartingaleModification Q 𝓖 (stoppedProcess X' τ) :=
  hasMartingaleModification_congr h (stoppedProcess_ae_eq_of_ae_forall he τ)

/-!
### Reindexing (sub-vectors)
-/

variable {d d' : ℕ}

/-- **Sub-vector / reindexing.** For any `e : Fin d' → Fin d`, the coordinates `Y ∘ e` of a
continuous semimartingale form a continuous semimartingale with drift `β ∘ e` and covariance
`α.submatrix e e`, with the same localizing sequence. -/
theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.comp_index
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y β α) (e : Fin d' → Fin d) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω k => Y t ω (e k)) (fun t ω k => β t ω (e k))
      (fun t ω => (α t ω).submatrix e e) := by
  have hv : Continuous fun v : Fin d → ℝ => fun k => v (e k) :=
    continuous_pi fun k => continuous_apply (e k)
  have hm : Continuous fun a : Matrix (Fin d) (Fin d) ℝ => a.submatrix e e :=
    continuous_id.matrix_submatrix e e
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  refine ⟨fun t => hv.comp_stronglyMeasurable (H.adapted t),
    fun t => hv.comp_stronglyMeasurable (H.progressive t), ?_,
    fun t => hv.comp_stronglyMeasurable (H.drift_progressive t),
    fun t => hm.comp_stronglyMeasurable (H.cov_progressive t), ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun k => (hmart n).1 (e k), fun k l => (hmart n).2 (e k) (e l)⟩⟩⟩
  · filter_upwards [H.continuous] with ω hω
    exact hv.comp hω
  · filter_upwards [H.integrable] with ω hω t
    exact ⟨fun k => (hω t).1 (e k), fun k l => (hω t).2 (e k) (e l)⟩

/-!
### Affine images (polarization)
-/

omit [MeasurableSpace Ω] in
/-- Pathwise identity for the compensated coordinates of `A Y + c`. -/
theorem smCompensated_affine (A : Matrix (Fin d') (Fin d) ℝ) (c : Fin d' → ℝ)
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω} {t : ℝ≥0}
    (hβ : ∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t)) (k : Fin d') :
    smCompensated (fun t ω => A *ᵥ Y t ω + c) (fun t ω => A *ᵥ β t ω) k t ω =
      ∑ i, A k i * smCompensated Y β i t ω := by
  simp only [smCompensated, Pi.add_apply, Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ (fun i _ => (hβ i).const_mul (A k i))]
  simp only [integral_const_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The `(k,l)` entry of `A α Aᵀ` as a double sum. -/
theorem mul_mul_transpose_apply (A : Matrix (Fin d') (Fin d) ℝ)
    (a : Matrix (Fin d) (Fin d) ℝ) (k l : Fin d') :
    (A * a * Aᵀ) k l = ∑ i, ∑ j, A k i * A l j * a i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [MeasurableSpace Ω] in
/-- Pathwise identity for the compensated products of `A Y + c` (polarization). -/
theorem bracket_affine (A : Matrix (Fin d') (Fin d) ℝ) (c : Fin d' → ℝ)
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ} {ω : Ω} {t : ℝ≥0}
    (hβ : ∀ i, IntegrableOn (fun s : ℝ => β s.toNNReal ω i) (Ioc 0 t))
    (hα : ∀ i j, IntegrableOn (fun s : ℝ => α s.toNNReal ω i j) (Ioc 0 t)) (k l : Fin d') :
    smCompensated (fun t ω => A *ᵥ Y t ω + c) (fun t ω => A *ᵥ β t ω) k t ω *
        smCompensated (fun t ω => A *ᵥ Y t ω + c) (fun t ω => A *ᵥ β t ω) l t ω -
        ∫ s in Ioc (0 : ℝ) t, (A * α s.toNNReal ω * Aᵀ) k l =
      ∑ i, ∑ j, A k i * A l j * (smCompensated Y β i t ω * smCompensated Y β j t ω -
        ∫ s in Ioc (0 : ℝ) t, α s.toNNReal ω i j) := by
  rw [smCompensated_affine A c hβ k, smCompensated_affine A c hβ l]
  simp_rw [mul_mul_transpose_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hα i j).const_mul (A k i * A l j)))]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _
    (fun j _ => (hα i j).const_mul (A k i * A l j))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Affine images / polarization.** If `Y` is a continuous semimartingale with
characteristics `(β, α)`, then `A Y + c` is one with characteristics `(A β, A α Aᵀ)`, with the
same localizing sequence. -/
theorem _root_.BlockBand.Internal.Contracts.Transmission.IsContinuousSemimartingale.affine
    {Y β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ}
    (H : IsContinuousSemimartingale Q 𝓖 Y β α) (A : Matrix (Fin d') (Fin d) ℝ)
    (c : Fin d' → ℝ) :
    IsContinuousSemimartingale Q 𝓖 (fun t ω => A *ᵥ Y t ω + c) (fun t ω => A *ᵥ β t ω)
      (fun t ω => A * α t ω * Aᵀ) := by
  have hv : Continuous fun v : Fin d → ℝ => A *ᵥ v + c :=
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  have hb : Continuous fun v : Fin d → ℝ => A *ᵥ v := continuous_const.matrix_mulVec continuous_id
  have hm : Continuous fun a : Matrix (Fin d) (Fin d) ℝ => A * a * Aᵀ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨τ, hτ, hτlim, hmart⟩ := H.localizing
  refine ⟨fun t => hv.comp_stronglyMeasurable (H.adapted t),
    fun t => hv.comp_stronglyMeasurable (H.progressive t), ?_,
    fun t => hb.comp_stronglyMeasurable (H.drift_progressive t),
    fun t => hm.comp_stronglyMeasurable (H.cov_progressive t), ?_,
    ⟨τ, hτ, hτlim, fun n => ⟨fun k => ?_, fun k l => ?_⟩⟩⟩
  · filter_upwards [H.continuous] with ω hω
    exact hv.comp hω
  · filter_upwards [H.integrable] with ω hω t
    refine ⟨fun k => ?_, fun k l => ?_⟩
    · have e : (fun s : ℝ => (A *ᵥ β s.toNNReal ω) k) =
          fun s => ∑ i, A k i * β s.toNNReal ω i := by
        funext s; simp only [Matrix.mulVec, dotProduct]
      rw [e]
      exact integrable_finsetSum _ fun i _ => ((hω t).1 i).const_mul (A k i)
    · simp_rw [mul_mul_transpose_apply]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        ((hω t).2 i j).const_mul (A k i * A l j)
  · have h := hasMartingaleModification_finsetSum Finset.univ fun i _ =>
      hasMartingaleModification_const_mul (A k i) ((hmart n).1 i)
    refine hasMartingaleModification_congr h fun t => ?_
    filter_upwards [H.integrable] with ω hω
    simp only [stoppedProcess_eq_stopTime]
    exact (smCompensated_affine A c (fun i => (hω _).1 i) k).symm
  · have h := hasMartingaleModification_finsetSum Finset.univ fun i _ =>
      hasMartingaleModification_finsetSum Finset.univ fun j _ =>
        hasMartingaleModification_const_mul (A k i * A l j) ((hmart n).2 i j)
    refine hasMartingaleModification_congr h fun t => ?_
    filter_upwards [H.integrable] with ω hω
    simp only [stoppedProcess_eq_stopTime]
    exact (bracket_affine A c (fun i => (hω _).1 i) (fun i j => (hω _).2 i j) k l).symm

end BlockBand.SourceProcess.Stochastic.Bridges
