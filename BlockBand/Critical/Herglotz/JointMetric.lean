module

public import BlockBand.Critical.Herglotz.Statement
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Metric, interpolation and measurability on `JointValues`

* Scoped instances (`open scoped BlockBand.Critical.Herglotz.JV`): the entrywise sup metric on
  `Matrix (Fin r) (Fin r) ℂ` (`Matrix.normedAddCommGroup`, with the topology replaced by the
  matrix topology so instance search sees one topology), second countability, and, for a
  compact space `K`, the max metric of `(Fin k → Matrix) × C(K, Matrix)` (sup over `K` in the
  second factor) on `JointValues r k K`. Its topology is the product of the product and
  compact-open topologies, i.e. the topology of `JointValues`.
* `dist_jointValues_le`: entrywise control of the distance of two `jointValues`.
* `CompactInterp K δ`: a finite set of nodes in `K` with a continuous partition of unity on `K`
  subordinate to the `δ`-balls around them (`exists_compactInterp`); `CompactInterp.interp`,
  `CompactInterp.continuous_interp`, `CompactInterp.norm_interp_sub_le`.
* `measurable_jointValues`: if every value `ω ↦ G ω z` is measurable and every path is
  continuous on the compact `K`, then `ω ↦ jointValues (G ω) x K` is Borel measurable.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped Matrix NNReal

namespace BlockBand.Critical.Herglotz

namespace JV

/-- Entrywise sup metric on `r × r` complex matrices, with the matrix topology. -/
scoped instance matrixPseudoMetricSpace (r : ℕ) :
    PseudoMetricSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.normedAddCommGroup (m := Fin r) (n := Fin r) (α := ℂ)).toPseudoMetricSpace.replaceUniformity
    rfl

scoped instance matrixSecondCountable (r : ℕ) :
    SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))

/-- Max metric on `JointValues r k K` for a compact space `K`. -/
scoped instance jointValuesPseudoMetricSpace (r k : ℕ) (K : Set ℂ) [CompactSpace K] :
    PseudoMetricSpace (JointValues r k K) :=
  inferInstanceAs (PseudoMetricSpace ((Fin k → Matrix (Fin r) (Fin r) ℂ) ×
    C(K, Matrix (Fin r) (Fin r) ℂ)))

scoped instance jointValuesSecondCountable (r k : ℕ) (K : Set ℂ) [CompactSpace K] :
    SecondCountableTopology (JointValues r k K) :=
  inferInstanceAs (SecondCountableTopology ((Fin k → Matrix (Fin r) (Fin r) ℂ) ×
    C(K, Matrix (Fin r) (Fin r) ℂ)))

end JV

open scoped JV

variable {r : ℕ}

/-- The matrix distance is the largest entrywise distance. -/
theorem matrix_dist_le_iff {M M' : Matrix (Fin r) (Fin r) ℂ} {ε : ℝ} (hε : 0 ≤ ε) :
    dist M M' ≤ ε ↔ ∀ i j, ‖M i j - M' i j‖ ≤ ε := by
  have hd : dist M M' = @dist (Fin r → Fin r → ℂ) _ M M' := rfl
  have h1 := dist_pi_le_iff (X := fun _ : Fin r => Fin r → ℂ) (f := M) (g := M') hε
  rw [hd, h1]
  simp_rw [dist_pi_le_iff hε, dist_eq_norm]

theorem norm_apply_sub_le_dist (M M' : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) :
    ‖M i j - M' i j‖ ≤ dist M M' :=
  (matrix_dist_le_iff dist_nonneg).1 le_rfl i j

theorem restrictTo_apply {G : ℂ → Matrix (Fin r) (Fin r) ℂ} {K : Set ℂ} (hG : ContinuousOn G K)
    (z : K) : restrictTo G K z = G z := by
  simp [restrictTo, hG]

/-- **Entrywise control of the joint distance.** For `G, G'` continuous on the compact `K`,
`ε ≥ 0`, if all entries differ by at most `ε` at the real points `x a` and at every `z ∈ K`,
then `dist (jointValues G x K) (jointValues G' x K) ≤ ε` (max metric, sup over `K`). -/
theorem dist_jointValues_le {k : ℕ} {K : Set ℂ} [CompactSpace K]
    {G G' : ℂ → Matrix (Fin r) (Fin r) ℂ} (hG : ContinuousOn G K) (hG' : ContinuousOn G' K)
    (x : Fin k → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hx : ∀ a i j, ‖G (x a) i j - G' (x a) i j‖ ≤ ε)
    (hK : ∀ z ∈ K, ∀ i j, ‖G z i j - G' z i j‖ ≤ ε) :
    dist (jointValues G x K) (jointValues G' x K) ≤ ε := by
  change max (dist (fun a => G (x a)) (fun a => G' (x a)))
    (dist (restrictTo G K) (restrictTo G' K)) ≤ ε
  refine max_le ((dist_pi_le_iff hε).2 fun a => (matrix_dist_le_iff hε).2 (hx a)) ?_
  refine (ContinuousMap.dist_le hε).2 fun z => ?_
  rw [restrictTo_apply hG, restrictTo_apply hG']
  exact (matrix_dist_le_iff hε).2 (hK z z.2)

/-!
## Interpolation on a compact set
-/

/-- Interpolation data on `K` at scale `δ`: finitely many nodes in `K` and a continuous partition
of unity on `K` whose `k`-th function vanishes outside the `δ`-ball around the `k`-th node. -/
structure CompactInterp (K : Set ℂ) (δ : ℝ) where
  /-- The nodes. -/
  pts : Finset ℂ
  pts_mem : ∀ p ∈ pts, p ∈ K
  /-- The partition of unity. -/
  wt : pts → C(K, ℝ)
  wt_nonneg : ∀ p z, 0 ≤ wt p z
  wt_sum : ∀ z, ∑ p, wt p z = 1
  wt_supp : ∀ p z, wt p z ≠ 0 → dist (z : ℂ) p < δ

/-- Interpolation data exist on every compact `K` at every scale `δ > 0`. -/
theorem exists_compactInterp {K : Set ℂ} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (CompactInterp K δ) := by
  classical
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun z => ball z (δ / 2))
    (fun z _ => ball_mem_nhds z (half_pos hδ))
  let ψ : t → C(K, ℝ) := fun p =>
    ⟨fun z => max 0 (δ - dist (z : ℂ) p), by fun_prop⟩
  have hψ0 : ∀ p z, 0 ≤ ψ p z := fun p z => le_max_left _ _
  have hpos : ∀ z : K, 0 < ∑ p, ψ p z := by
    intro z
    obtain ⟨p, hpt, hzp⟩ := Set.mem_iUnion₂.1 (hcov z.2)
    have hp : δ / 2 < ψ ⟨p, hpt⟩ z := by
      have : dist (z : ℂ) p < δ / 2 := hzp
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    exact lt_of_lt_of_le (by linarith) (Finset.single_le_sum (fun q _ => hψ0 q z)
      (Finset.mem_univ (⟨p, hpt⟩ : t)))
  have hcontS : Continuous fun z : K => ∑ p, ψ p z := by fun_prop
  refine ⟨⟨t, htK, fun p => ⟨fun z => ψ p z / ∑ q, ψ q z, ?_⟩, ?_, ?_, ?_⟩⟩
  · exact (ψ p).continuous.div hcontS fun z => (hpos z).ne'
  · intro p z
    exact div_nonneg (hψ0 p z) (hpos z).le
  · intro z
    simp only [ContinuousMap.coe_mk]
    rw [← Finset.sum_div, div_self (hpos z).ne']
  · intro p z hne
    simp only [ContinuousMap.coe_mk, ne_eq, div_eq_zero_iff, not_or] at hne
    have h1 : ψ p z ≠ 0 := hne.1
    by_contra hd
    push Not at hd
    apply h1
    show max 0 (δ - dist (z : ℂ) p) = 0
    exact max_eq_left (by linarith)

namespace CompactInterp

variable {K : Set ℂ} {δ : ℝ}

/-- The interpolant `z ↦ Σ_p wt_p(z) b_p` of node values `b`. -/
def interp (I : CompactInterp K δ) (b : I.pts → Matrix (Fin r) (Fin r) ℂ) :
    C(K, Matrix (Fin r) (Fin r) ℂ) :=
  ⟨fun z => ∑ p, ((I.wt p z : ℝ) : ℂ) • b p, by fun_prop⟩

theorem interp_apply (I : CompactInterp K δ) (b : I.pts → Matrix (Fin r) (Fin r) ℂ) (z : K)
    (i j : Fin r) : I.interp b z i j = ∑ p, ((I.wt p z : ℝ) : ℂ) * b p i j := by
  simp [interp, Matrix.sum_apply]

/-- The interpolation map is continuous (compact-open topology on `C(K, Matrix)`). -/
theorem continuous_interp (I : CompactInterp K δ) :
    Continuous (I.interp (r := r)) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun q : (I.pts → Matrix (Fin r) (Fin r) ℂ) × K =>
    ∑ p, ((I.wt p q.2 : ℝ) : ℂ) • q.1 p
  fun_prop

/-- **Interpolation error.** If at `z ∈ K` every node `p` with `dist z p < δ` satisfies
`|b_p,ij - c_ij| ≤ ε`, then `|interp b (z)_ij - c_ij| ≤ ε`. -/
theorem norm_interp_sub_le (I : CompactInterp K δ) (b : I.pts → Matrix (Fin r) (Fin r) ℂ)
    (z : K) (c : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) {ε : ℝ}
    (h : ∀ p : I.pts, dist (z : ℂ) p < δ → ‖b p i j - c i j‖ ≤ ε) :
    ‖I.interp b z i j - c i j‖ ≤ ε := by
  have hsum : I.interp b z i j - c i j = ∑ p, ((I.wt p z : ℝ) : ℂ) * (b p i j - c i j) := by
    rw [interp_apply]
    have h1 : c i j = ∑ p, ((I.wt p z : ℝ) : ℂ) * c i j := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, I.wt_sum z, Complex.ofReal_one, one_mul]
    conv_lhs => rw [h1]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hsum]
  calc ‖∑ p, ((I.wt p z : ℝ) : ℂ) * (b p i j - c i j)‖
      ≤ ∑ p, ‖((I.wt p z : ℝ) : ℂ) * (b p i j - c i j)‖ := norm_sum_le _ _
    _ ≤ ∑ p, I.wt p z * ε := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (I.wt_nonneg p z)]
        by_cases hw : I.wt p z = 0
        · rw [hw, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h p (I.wt_supp p z hw)) (I.wt_nonneg p z)
    _ = ε := by rw [← Finset.sum_mul, I.wt_sum z, one_mul]

end CompactInterp

/-- Uniform continuity of a function continuous on a compact set, entrywise, in the form used
for interpolation: for `ε > 0` there is `δ > 0` with `|G z_ij - G z'_ij| ≤ ε` whenever
`z, z' ∈ K`, `dist z z' < δ`. -/
theorem exists_delta_entry {K : Set ℂ} (hK : IsCompact K) {G : ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hG : ContinuousOn G K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ K, ∀ z' ∈ K, dist z z' < δ → ∀ i j, ‖G z i j - G z' i j‖ ≤ ε := by
  have hu := hK.uniformContinuousOn_of_continuous hG
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun z hz z' hz' hd i j => ?_⟩
  exact (norm_apply_sub_le_dist _ _ i j).trans (h z hz z' hz' hd).le

/-- Measurability of a random matrix from its entries. -/
theorem measurable_matrix_of_entries {Ω : Type*} [MeasurableSpace Ω]
    {A : Ω → Matrix (Fin r) (Fin r) ℂ} (hA : ∀ i j, Measurable fun ω => A ω i j) :
    Measurable A :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hA i j

/-- **Measurability of joint values.** Law: none (a measurable space `Ω`). For a compact
`K ⊆ ℂ`, real points `x : Fin k → ℝ`, and a random function `G : Ω → ℂ → Matrix` such that every
entry `ω ↦ G ω z i j` is measurable (`z : ℂ` fixed) and every path `G ω` is continuous on `K`, the
map `ω ↦ jointValues (G ω) x K ∈ (Fin k → Matrix) × C(K, Matrix)` is Borel measurable
(compact-open topology). Proof: interpolation at scale `1/(n+1)` gives measurable maps (continuous
images of finitely many values) converging pointwise, by uniform continuity on `K`. -/
theorem measurable_jointValues {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {K : Set ℂ}
    (hK : IsCompact K) (x : Fin k → ℝ) {G : Ω → ℂ → Matrix (Fin r) (Fin r) ℂ}
    (hmeas : ∀ z i j, Measurable fun ω => G ω z i j) (hcont : ∀ ω, ContinuousOn (G ω) K) :
    Measurable fun ω => jointValues (G ω) x K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  let I : ∀ n : ℕ, CompactInterp K (1 / ((n : ℝ) + 1)) :=
    fun n => (exists_compactInterp hK (hδ n)).some
  let J : ℕ → Ω → JointValues r k K := fun n ω =>
    ((fun a => G ω (x a)), (I n).interp fun p => G ω p)
  have hval : ∀ z, Measurable fun ω => G ω z := fun z =>
    measurable_matrix_of_entries (hmeas z)
  have hJ : ∀ n, Measurable (J n) := by
    intro n
    have h1 : Measurable fun ω => (fun a => G ω (x a)) := measurable_pi_iff.2 fun a => hval _
    have h2 : Measurable fun ω => (fun p : (I n).pts => G ω p) :=
      measurable_pi_iff.2 fun p => hval _
    have h3 : Measurable fun ω => (I n).interp (r := r) fun p => G ω p :=
      (I n).continuous_interp.measurable.comp h2
    let : MeasurableSpace C(K, Matrix (Fin r) (Fin r) ℂ) := borel _
    have : BorelSpace C(K, Matrix (Fin r) (Fin r) ℂ) := ⟨rfl⟩
    have heq : (inferInstance : MeasurableSpace (JointValues r k K)) =
        (Prod.instMeasurableSpace : MeasurableSpace ((Fin k → Matrix (Fin r) (Fin r) ℂ) ×
          C(K, Matrix (Fin r) (Fin r) ℂ))) := by
      change borel _ = _
      exact (BorelSpace.measurable_eq (α := (Fin k → Matrix (Fin r) (Fin r) ℂ) ×
        C(K, Matrix (Fin r) (Fin r) ℂ))).symm
    show @Measurable _ _ _ (inferInstance : MeasurableSpace (JointValues r k K)) _
    rw [heq]
    exact h1.prodMk h3
  refine measurable_of_tendsto_metrizable hJ ?_
  rw [tendsto_pi_nhds]
  intro ω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδpos, hδ'⟩ := exists_delta_entry hK (hcont ω) (half_pos hε)
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδpos
  refine ⟨n₀, fun n hn => ?_⟩
  have hsmall : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := by
    gcongr
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  change max (dist (fun a => G ω (x a)) (fun a => G ω (x a)))
    (dist ((I n).interp fun p => G ω p) (restrictTo (G ω) K)) ≤ ε / 2
  rw [dist_self]
  refine max_le (by positivity) ((ContinuousMap.dist_le (by positivity)).2 fun z => ?_)
  rw [restrictTo_apply (hcont ω)]
  refine (matrix_dist_le_iff (by positivity)).2 fun i j => ?_
  refine (I n).norm_interp_sub_le _ z _ i j fun p hp => ?_
  rw [← norm_neg, neg_sub]
  refine hδ' z z.2 p ((I n).pts_mem p p.2) ?_ i j
  linarith

end BlockBand.Critical.Herglotz
