module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessStop

/-!
# Measurability and adaptedness of the survival events

* `tcx_isHermitian_pathCurrent`: `J = 𝕊*P𝕊 - P` is Hermitian at every path.
* `tcx_measurable_nuclearNorm_pathCurrent`: `ω ↦ Tr|J_i(ω)|` is Borel measurable. This is the only
  use the stop removal makes of `TcwNuclearNormMeasurable`, which is therefore not needed.
* `tcx_measurable_traceLoad`, `tcx_measurableSet_alive`: hypothesis-free versions of
  `tcw_measurable_traceLoad`, `tcw_measurableSet_alive`.
* Adaptedness. `tcx_growthSigma_le`: `growthSigma W l` is a sub-σ-algebra.
  `tcx_measurableSet_alive_growthSigma`: `{l < σ_K} ∈ growthSigma W l`. The path of length
  `i ≤ l` reads only `A_0, …, A_{i-1}` and `B_0, …, B_i` (`tcx_pathAt_ext`), so the trace loads
  `Tr Q_{i;k} + Tr|J_i|`, `i ≤ l`, factor through the coordinates `(A_{<l}, B_{≤l})`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

/-!
## The nuclear norm of the current
-/

/-- For Hermitian `A`, the `nuclearNorm A = Σ_{roots}|λ|` is `Re Tr|A|`, `|A| = CFC.abs A`. -/
theorem tcx_nuclearNorm_eq_trace_abs {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : nuclearNorm A = (CFC.abs A).trace.re := by
  have hsa : IsSelfAdjoint A := hA
  rw [CFC.abs_eq_cfc_norm A hsa]
  have h1 : cfc (‖·‖ : ℝ → ℝ) A = cfc (fun x : ℝ => |x|) A := rfl
  rw [h1, trace_eq_sum_roots_charpoly, hA.charpoly_cfc_eq, Polynomial.roots_prod]
  · unfold nuclearNorm
    rw [hA.roots_charpoly_eq_eigenvalues]
    simp [Multiset.map_map, Complex.norm_real, Complex.re_sum]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The current `J = 𝕊*P𝕊 - P` is Hermitian at every path. -/
theorem tcx_isHermitian_pathCurrent (b e : ℝ) (W i : ℕ) (ω : GrowthPath W) :
    (pathCurrent b e W i ω).IsHermitian := by
  unfold pathCurrent
  have hP : (nearProjection W)ᴴ = nearProjection W := tcs_nearProjection_hermitian W
  refine IsHermitian.sub ?_ hP
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

/-- `ω ↦ Tr|J_i(ω)|` is Borel measurable. -/
theorem tcx_measurable_nuclearNorm_pathCurrent (b e : ℝ) (W i : ℕ) :
    Measurable (fun ω : GrowthPath W => nuclearNorm (pathCurrent b e W i ω)) := by
  have he : (fun ω : GrowthPath W => nuclearNorm (pathCurrent b e W i ω)) =
      fun ω => (CFC.abs (pathCurrent b e W i ω)).trace.re :=
    funext fun ω => tcx_nuclearNorm_eq_trace_abs (tcx_isHermitian_pathCurrent b e W i ω)
  rw [he]
  have hm : Measurable (fun M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ => CFC.abs M) := by
    unfold CFC.abs
    exact CFC.measurable_sqrt.comp (continuous_star.mul continuous_id).measurable
  exact Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (hm.comp (tcw_measurable_pathCurrent b e W i)))

/-- `tcw_measurable_traceLoad` without `TcwNuclearNormMeasurable`. -/
theorem tcx_measurable_traceLoad (b e : ℝ) (W k i : ℕ) :
    Measurable (fun ω : GrowthPath W =>
      traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω) := by
  unfold traceLoad
  refine Measurable.add (Finset.measurable_sum _ fun a _ => ?_)
    (tcx_measurable_nuclearNorm_pathCurrent b e W i)
  rcases a with a | a
  · unfold sourceTrace
    have hm : Measurable (fun ω : GrowthPath W => (W : ℂ)⁻¹ • tagResponse b e W i k ω) :=
      (continuous_const_smul _).measurable.comp (tco_measurable_tagResponse b e W i k)
    exact Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp hm)
  · exact a.elim0

theorem tcx_alive_eq_iInter (b e : ℝ) (W k : ℕ) (K ε : ℝ) (l : ℕ) :
    tcw_alive b e W k K ε l = ⋂ i ∈ Finset.range (l + 1),
      {ω | ¬ (ε * W ≤ i ∧ K < traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω)} := by
  ext ω
  simp only [tcw_alive, tcw_mem_alive_iff, Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩

/-- `tcw_measurableSet_alive` without `TcwNuclearNormMeasurable`. -/
theorem tcx_measurableSet_alive (b e : ℝ) (W k : ℕ) (K ε : ℝ) (l : ℕ) :
    MeasurableSet (tcw_alive b e W k K ε l) := by
  rw [tcx_alive_eq_iInter]
  refine Finset.measurableSet_biInter _ fun i _ => ?_
  by_cases hi : ε * W ≤ i
  · simp only [hi, true_and]
    exact (measurableSet_lt measurable_const (tcx_measurable_traceLoad b e W k i)).compl
  · simp [hi]

/-!
## Adaptedness
-/

/-- The coordinates `(A_{<l}, B_{≤l})` generating `growthSigma W l`. -/
def tcx_proj (W l : ℕ) (ω : GrowthPath W) :
    (Fin l → Matrix (Fin W) (Fin W) ℂ) × (Fin (l + 1) → Matrix (Fin W) (Fin W) ℂ) :=
  ((fun k : Fin l => ω.1 k), (fun k : Fin (l + 1) => ω.2 k))

/-- Extension by zero of the coordinates `(A_{<l}, B_{≤l})` to a full path. -/
def tcx_ext (W l : ℕ)
    (x : (Fin l → Matrix (Fin W) (Fin W) ℂ) × (Fin (l + 1) → Matrix (Fin W) (Fin W) ℂ)) :
    GrowthPath W :=
  (fun n => if h : n < l then x.1 ⟨n, h⟩ else 0, fun n => if h : n < l + 1 then x.2 ⟨n, h⟩ else 0)

theorem tcx_measurable_proj (W l : ℕ) : Measurable (tcx_proj W l) := by
  unfold tcx_proj
  fun_prop

theorem tcx_measurable_ext (W l : ℕ) : Measurable (tcx_ext W l) := by
  unfold tcx_ext
  refine (measurable_pi_iff.2 fun n => ?_).prodMk (measurable_pi_iff.2 fun n => ?_)
  · by_cases h : n < l
    · simp only [h, dite_true]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, dite_false]; exact measurable_const
  · by_cases h : n < l + 1
    · simp only [h, dite_true]; exact (measurable_pi_apply _).comp measurable_snd
    · simp only [h, dite_false]; exact measurable_const

/-- `growthSigma W l` is a sub-σ-algebra of the path σ-algebra. -/
theorem tcx_growthSigma_le (W l : ℕ) :
    growthSigma W l ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
  (tcx_measurable_proj W l).comap_le

/-- The path of length `i ≤ l` reads only `A_{<i}` and `B_{≤i}`. -/
theorem tcx_pathAt_ext {W i l : ℕ} (hi : i ≤ l) (ω : GrowthPath W) :
    pathAt W i (tcx_ext W l (tcx_proj W l ω)) = pathAt W i ω := by
  unfold pathAt tcx_ext tcx_proj
  refine Prod.ext (funext fun j => ?_) (Prod.ext (funext fun j => ?_) (funext fun p => ?_))
  · have : i - 1 - j.val < l := by have := j.isLt; omega
    simp [this]
  · have : i - 1 - j.val < l + 1 := by have := j.isLt; omega
    simp [this]
  · fin_cases p
    · have : i < l + 1 := by omega
      simp [this]
    · simp

theorem tcx_fullInverse_ext {b e : ℝ} {W i l : ℕ} (hi : i ≤ l) (ω : GrowthPath W) :
    fullInverse b e W i (tcx_ext W l (tcx_proj W l ω)) = fullInverse b e W i ω := by
  unfold fullInverse fullPathMatrix
  rw [tcx_pathAt_ext hi]

theorem tcx_pathCurrent_ext {b e : ℝ} {W i l : ℕ} (hi : i ≤ l) (ω : GrowthPath W) :
    pathCurrent b e W i (tcx_ext W l (tcx_proj W l ω)) = pathCurrent b e W i ω := by
  unfold pathCurrent scatteringMatrix boundaryResolvent
  rw [tcx_fullInverse_ext hi]

theorem tcx_tagResponse_ext {b e : ℝ} {W i l k : ℕ} (hi : i ≤ l) (ω : GrowthPath W) :
    tagResponse b e W i k (tcx_ext W l (tcx_proj W l ω)) = tagResponse b e W i k ω := by
  unfold tagResponse boundaryToInterior
  rw [tcx_fullInverse_ext hi]

theorem tcx_traceLoad_ext {b e : ℝ} {W k i l : ℕ} (hi : i ≤ l) (ω : GrowthPath W) :
    traceLoad b e (tcw_tagFamily k) tcw_noInterval W i (tcx_ext W l (tcx_proj W l ω)) =
      traceLoad b e (tcw_tagFamily k) tcw_noInterval W i ω := by
  unfold traceLoad
  rw [tcx_pathCurrent_ext hi]
  refine congrArg (· + nuclearNorm (pathCurrent b e W i ω)) (Finset.sum_congr rfl fun a _ => ?_)
  rcases a with a | a
  · unfold sourceTrace
    simp only [sourceLetter, Sum.elim_inl, letterMatrix]
    rw [tcx_tagResponse_ext hi]
  · exact a.elim0

/-- A measurable set whose membership only depends on the coordinates `(A_{<l}, B_{≤l})` is in
`growthSigma W l`. -/
theorem tcx_measurableSet_growthSigma_of_invariant {W l : ℕ} {S : Set (GrowthPath W)}
    (hS : MeasurableSet S) (hinv : ∀ ω, tcx_ext W l (tcx_proj W l ω) ∈ S ↔ ω ∈ S) :
    MeasurableSet[growthSigma W l] S := by
  refine ⟨tcx_ext W l ⁻¹' S, (tcx_measurable_ext W l) hS, ?_⟩
  ext ω
  exact hinv ω

/-- Adaptedness: the survival event `{l < σ_K}` is in `growthSigma W l`. -/
theorem tcx_measurableSet_alive_growthSigma (b e : ℝ) (W k : ℕ) (K ε : ℝ) (l : ℕ) :
    MeasurableSet[growthSigma W l] (tcw_alive b e W k K ε l) := by
  refine tcx_measurableSet_growthSigma_of_invariant (tcx_measurableSet_alive b e W k K ε l)
    fun ω => ?_
  simp only [tcw_alive, tcw_mem_alive_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [tcx_traceLoad_ext hi]

end BlockBand.Endpoints
