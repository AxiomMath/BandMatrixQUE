module

public import Mathlib

/-!
# ε-nets of unit spheres, net-to-sup bounds, and union bounds

The ε-net step of the Gaussian absorption lemma ("On `K ≤ t^{-1/2}`, a net of mesh `t^{3/2}/2` on
the unit sphere of `Ran P` gives `P(d < t | D) ≤ C e^{-c_b W/t} + (C t^{-3/2})^{2k} (C_b t²)^W`")
and the net step of Gaussian operator-norm tails.

Setting. `V` is a finite-dimensional real normed space of real dimension `d = finrank ℝ V`; for
complex spaces (`EuclideanSpace ℂ ι`, complex subspaces `S` such as `Ran P`) the real dimension is
`2 * finrank ℂ` (so `2k` for `dim_ℂ Ran P = k`, matching the exponent `2k` of the paper).
Constants: the covering constant is `3`, i.e. a net of mesh `ε ∈ (0,1]` has at most `(3/ε)^d`
points (volume argument with disjoint balls of radius `ε/2` in the ball of radius `1 + ε/2`);
the net-to-sup constant is `2` for mesh `ε ≤ 1/2`.

Main declarations.
* `card_le_of_separated_sphere`: packing bound for `ε`-separated subsets of the unit sphere.
* `exists_sphere_net`, `exists_sphere_net_complex`, `exists_sphere_net_euclidean`,
  `exists_submodule_sphere_net`, `exists_submodule_sphere_net_euclidean`: covering.
* `opNorm_le_two_mul_of_net`, `sub_le_norm_apply_of_net`, `sub_le_iInf_sphere_of_net`:
  net-to-sup / net-to-inf for continuous `𝕜`-linear maps (`𝕜 = ℝ` or `ℂ`).
* `measure_exists_unit_lt_le`, `measure_iInf_sphere_lt_le`, `measure_opNorm_gt_le`: union bounds
  (any measure, no measurability assumptions); `measure_exists_unit_lt_le_net_card`,
  `measure_exists_unit_lt_le_real`, `measure_exists_unit_lt_le_complex`: the combined
  `(3/ε)^d` form.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory Metric Module

/-!
## Packing and covering
-/

section Covering

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Packing bound (volume argument). If `S` is a finite subset of the unit sphere of a real
normed space of dimension `d` whose distinct points are at distance `> ε`, `0 < ε ≤ 1`, then
`|S| ≤ (3/ε)^d`. The balls `B(x, ε/2)`, `x ∈ S`, are disjoint and lie in `B(0, 1 + ε/2)`, so
`|S| (ε/2)^d ≤ (1 + ε/2)^d ≤ (3/2)^d` (any additive Haar measure). -/
theorem card_le_of_separated_sphere {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (S : Finset V)
    (hS : ∀ u ∈ S, ‖u‖ = 1) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < ‖x - y‖) :
    (S.card : ℝ) ≤ (3 / ε) ^ finrank ℝ V := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  set μ : Measure V := Measure.addHaar
  set d := finrank ℝ V
  have hε2 : 0 < ε / 2 := by positivity
  have hdisj : (S : Set V).PairwiseDisjoint (fun x => ball x (ε / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    linarith [hsep x hx y hy hxy]
  have hsub : (⋃ x ∈ S, ball x (ε / 2)) ⊆ ball (0 : V) (1 + ε / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < 1 + ε / 2 := by rw [hS x hx]; linarith
  have hle := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)] at hle
  simp_rw [Measure.addHaar_ball_of_pos μ _ hε2] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by positivity : (0 : ℝ) < 1 + ε / 2), Finset.sum_const,
    nsmul_eq_mul, ← mul_assoc] at hle
  have h0 : μ (ball (0 : V) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have htop : μ (ball (0 : V) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left h0 htop).mp hle
  have h3 : (S.card : ℝ) * (ε / 2) ^ d ≤ (1 + ε / 2) ^ d := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
  have h4 : (1 + ε / 2) ^ d ≤ (3 / 2) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
  have h5 : (3 / ε) ^ d = (3 / 2) ^ d / (ε / 2) ^ d := by
    rw [← div_pow]; congr 1; field_simp
  rw [h5, le_div_iff₀ (by positivity)]
  linarith

/-- Covering (ε-net of the unit sphere). For `0 < ε ≤ 1` there is a finite set `N` of unit
vectors with `|N| ≤ (3/ε)^d`, `d = finrank ℝ V`, such that every unit vector is within `ε` of a
point of `N`. Proof: an `ε`-separated subset of the sphere of maximal cardinality (cardinalities
are bounded by `card_le_of_separated_sphere`). -/
theorem exists_sphere_net {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset V, (∀ u ∈ N, ‖u‖ = 1) ∧ (N.card : ℝ) ≤ (3 / ε) ^ finrank ℝ V ∧
      ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset V, (∀ u ∈ S, ‖u‖ = 1) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ε < ‖x - y‖) ∧ S.card = n
  set B : ℕ := ⌊(3 / ε) ^ finrank ℝ V⌋₊
  have hB : ∀ n, P n → n ≤ B := by
    rintro n ⟨S, h1, h2, rfl⟩
    exact Nat.le_floor (card_le_of_separated_sphere hε hε1 S h1 h2)
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  obtain ⟨S, hS1, hS2, hScard⟩ : P (Nat.findGreatest P B) :=
    Nat.findGreatest_spec (Nat.zero_le B) hP0
  refine ⟨S, hS1, card_le_of_separated_sphere hε hε1 S hS1 hS2, ?_⟩
  intro x hx
  by_contra hcon
  push Not at hcon
  have hxS : x ∉ S := fun hxS => by
    have := hcon x hxS
    rw [sub_self, norm_zero] at this
    linarith
  have hPins : P (S.card + 1) := by
    refine ⟨insert x S, ?_, ?_, Finset.card_insert_of_notMem hxS⟩
    · intro u hu
      rw [Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact hx
      · exact hS1 u hu
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact hcon b hb
      · rw [norm_sub_rev]; exact hcon a ha
      · exact hS2 a ha b hb hab
  have := Nat.le_findGreatest (hB _ hPins) hPins
  omega

end Covering

section CoveringComplex

/-- Covering for a finite-dimensional complex normed space `E`: real dimension
`2 * finrank ℂ E`, so `|N| ≤ (3/ε)^(2 * finrank ℂ E)` for `0 < ε ≤ 1`. -/
theorem exists_sphere_net_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset E, (∀ u ∈ N, ‖u‖ = 1) ∧ (N.card : ℝ) ≤ (3 / ε) ^ (2 * finrank ℂ E) ∧
      ∀ x : E, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε := by
  rw [← finrank_real_of_complex]
  exact exists_sphere_net hε hε1

/-- Covering for `EuclideanSpace ℂ ι`: `|N| ≤ (3/ε)^(2 * card ι)` for `0 < ε ≤ 1`. -/
theorem exists_sphere_net_euclidean {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ N : Finset (EuclideanSpace ℂ ι), (∀ u ∈ N, ‖u‖ = 1) ∧
      (N.card : ℝ) ≤ (3 / ε) ^ (2 * Fintype.card ι) ∧
      ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε := by
  rw [← finrank_euclideanSpace (𝕜 := ℂ)]
  exact exists_sphere_net_complex hε hε1

/-- Covering of the unit sphere of a finite-dimensional complex subspace `S` (e.g. `Ran P`) of a
complex normed space, with net points in the ambient space lying in `S`:
`|N| ≤ (3/ε)^(2 * finrank ℂ S)` for `0 < ε ≤ 1`. -/
theorem exists_submodule_sphere_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Submodule ℂ E) [FiniteDimensional ℂ S] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset E, (∀ u ∈ N, u ∈ S ∧ ‖u‖ = 1) ∧
      (N.card : ℝ) ≤ (3 / ε) ^ (2 * finrank ℂ S) ∧
      ∀ x ∈ S, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_sphere_net_complex (E := S) hε hε1
  refine ⟨N.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro u hu
    rw [Finset.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact ⟨v.2, hN1 v hv⟩
  · rwa [Finset.card_map]
  · intro x hxS hx
    obtain ⟨u, hu, hxu⟩ := hN3 ⟨x, hxS⟩ hx
    exact ⟨u, Finset.mem_map_of_mem _ hu, hxu⟩

/-- `exists_submodule_sphere_net` for `S : Submodule ℂ (EuclideanSpace ℂ ι)`. -/
theorem exists_submodule_sphere_net_euclidean {ι : Type*} [Fintype ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : Finset (EuclideanSpace ℂ ι), (∀ u ∈ N, u ∈ S ∧ ‖u‖ = 1) ∧
      (N.card : ℝ) ≤ (3 / ε) ^ (2 * finrank ℂ S) ∧
      ∀ x ∈ S, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε :=
  exists_submodule_sphere_net S hε hε1

end CoveringComplex

/-!
## Net-to-sup and net-to-inf for linear maps
-/

section NetSup

variable {𝕜 : Type*} [RCLike 𝕜] {V U : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]

/-- Basic net comparison: `‖T u‖ ≤ ‖T x‖ + ‖T‖ ‖x - u‖` and `‖T x‖ ≤ ‖T u‖ + ‖T‖ ‖x - u‖`. -/
theorem norm_apply_sub_le (T : V →L[𝕜] U) (x u : V) :
    ‖T u‖ ≤ ‖T x‖ + ‖T‖ * ‖x - u‖ ∧ ‖T x‖ ≤ ‖T u‖ + ‖T‖ * ‖x - u‖ := by
  have h1 : ‖T x - T u‖ ≤ ‖T‖ * ‖x - u‖ := by rw [← map_sub]; exact T.le_opNorm _
  constructor
  · calc ‖T u‖ = ‖T x - (T x - T u)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖T x‖ + ‖T x - T u‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  · calc ‖T x‖ = ‖T u + (T x - T u)‖ := by rw [add_sub_cancel]
      _ ≤ ‖T u‖ + ‖T x - T u‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- Net-to-sup, sharp form: if `N` is an `ε`-net of the unit sphere (`0 ≤ ε`) and `‖T u‖ ≤ M`
on `N` with `0 ≤ M`, then `(1 - ε) ‖T‖ ≤ M`. -/
theorem one_sub_mul_opNorm_le_of_net {ε M : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (T : V →L[𝕜] U) (hT : ∀ u ∈ N, ‖T u‖ ≤ M) : (1 - ε) * ‖T‖ ≤ M := by
  have h : ‖T‖ ≤ M + ε * ‖T‖ := by
    refine T.opNorm_le_of_unit_norm (by positivity) fun x hx => ?_
    obtain ⟨u, hu, hxu⟩ := hN x hx
    have := (norm_apply_sub_le T x u).2
    have : ‖T‖ * ‖x - u‖ ≤ ‖T‖ * ε := mul_le_mul_of_nonneg_left hxu (norm_nonneg _)
    linarith [hT u hu]
  linarith

/-- Net-to-sup (Gaussian norm tails): for an `ε`-net `N` of the unit sphere with
`0 ≤ ε ≤ 1/2`, `‖T u‖ ≤ M` on `N` (`0 ≤ M`) implies `‖T‖ ≤ 2 M`. -/
theorem opNorm_le_two_mul_of_net {ε M : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (hM : 0 ≤ M) (T : V →L[𝕜] U) (hT : ∀ u ∈ N, ‖T u‖ ≤ M) : ‖T‖ ≤ 2 * M := by
  have h := one_sub_mul_opNorm_le_of_net hN hε hM T hT
  have : ε * ‖T‖ ≤ 1 / 2 * ‖T‖ := mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)
  linarith

/-- Net-to-sup with the maximum over a nonempty net: `‖T‖ ≤ 2 max_{u ∈ N} ‖T u‖`
(`0 ≤ ε ≤ 1/2`). -/
theorem opNorm_le_two_mul_sup'_of_net {ε : ℝ} {N : Finset V} (hne : N.Nonempty)
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2)
    (T : V →L[𝕜] U) : ‖T‖ ≤ 2 * N.sup' hne (fun u => ‖T u‖) := by
  obtain ⟨u₀, hu₀⟩ := hne
  refine opNorm_le_two_mul_of_net hN hε hε2 ?_ T fun _ hu => Finset.le_sup' (fun u => ‖T u‖) hu
  exact (norm_nonneg _).trans (Finset.le_sup' (fun u => ‖T u‖) hu₀)

/-- Net-to-inf, pointwise: if `m ≤ ‖T u‖` on an `ε`-net `N` of the unit sphere, then
`m - ε ‖T‖ ≤ ‖T x‖` for every unit vector `x`. -/
theorem sub_le_norm_apply_of_net {ε m : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : V →L[𝕜] U)
    (hT : ∀ u ∈ N, m ≤ ‖T u‖) {x : V} (hx : ‖x‖ = 1) : m - ε * ‖T‖ ≤ ‖T x‖ := by
  obtain ⟨u, hu, hxu⟩ := hN x hx
  have := (norm_apply_sub_le T x u).1
  have : ‖T‖ * ‖x - u‖ ≤ ‖T‖ * ε := mul_le_mul_of_nonneg_left hxu (norm_nonneg _)
  linarith [hT u hu]

/-- Existence of a unit vector in a nontrivial normed `𝕜`-space. -/
theorem exists_norm_eq_one_of_nontrivial (𝕜 : Type*) {V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [Nontrivial V] : ∃ x : V, ‖x‖ = 1 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : V)
  refine ⟨((‖y‖⁻¹ : ℝ) : 𝕜) • y, ?_⟩
  rw [norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- The unit sphere of a nontrivial normed `𝕜`-space is nonempty. -/
theorem sphere_nonempty_of_nontrivial (𝕜 : Type*) {V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [Nontrivial V] : Nonempty (sphere (0 : V) 1) := by
  obtain ⟨x, hx⟩ := exists_norm_eq_one_of_nontrivial 𝕜 (V := V)
  exact ⟨⟨x, by rw [mem_sphere_zero_iff_norm]; exact hx⟩⟩

/-- The minimum of `‖T x‖` over the unit sphere is below `t` iff some unit vector has
`‖T x‖ < t` (`V` nontrivial). -/
theorem iInf_sphere_lt_iff [Nontrivial V] (T : V →L[𝕜] U) (t : ℝ) :
    (⨅ x : sphere (0 : V) 1, ‖T x‖) < t ↔ ∃ x : V, ‖x‖ = 1 ∧ ‖T x‖ < t := by
  have := sphere_nonempty_of_nontrivial 𝕜 (V := V)
  rw [ciInf_lt_iff ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, mem_sphere_zero_iff_norm.mp x.2, hx⟩
  · rintro ⟨x, hx1, hx⟩
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr hx1⟩, hx⟩

/-- Net-to-inf: `inf_{‖x‖ = 1} ‖T x‖ ≥ m - ε ‖T‖` when `m ≤ ‖T u‖` on an `ε`-net `N` (`V`
nontrivial). -/
theorem sub_le_iInf_sphere_of_net [Nontrivial V] {ε m : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : V →L[𝕜] U)
    (hT : ∀ u ∈ N, m ≤ ‖T u‖) : m - ε * ‖T‖ ≤ ⨅ x : sphere (0 : V) 1, ‖T x‖ := by
  have := sphere_nonempty_of_nontrivial 𝕜 (V := V)
  exact le_ciInf fun x => sub_le_norm_apply_of_net hN T hT (mem_sphere_zero_iff_norm.mp x.2)

/-- Net-to-inf with the minimum over a nonempty net:
`inf_{‖x‖=1} ‖T x‖ ≥ min_{u ∈ N} ‖T u‖ - ε ‖T‖`. -/
theorem inf'_sub_le_iInf_sphere_of_net [Nontrivial V] {ε : ℝ} {N : Finset V} (hne : N.Nonempty)
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : V →L[𝕜] U) :
    N.inf' hne (fun u => ‖T u‖) - ε * ‖T‖ ≤ ⨅ x : sphere (0 : V) 1, ‖T x‖ :=
  sub_le_iInf_sphere_of_net hN T fun _ hu => Finset.inf'_le (fun u => ‖T u‖) hu

end NetSup

/-!
## Union bounds
-/

section UnionBound

variable {𝕜 : Type*} [RCLike 𝕜] {V U : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U] {Ω : Type*} [MeasurableSpace Ω]

/-- Union bound for the smallest singular value (net step of the Gaussian absorption lemma): for
any measure `μ` (no measurability of `T` needed), any `ε`-net `N` of the
unit sphere and any `K, t`,
`μ{∃ ‖x‖ = 1, ‖T x‖ < t} ≤ μ{‖T‖ > K} + Σ_{u ∈ N} μ{‖T u‖ < t + ε K}`. -/
theorem measure_exists_unit_lt_le (μ : Measure Ω) {ε K t : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : Ω → V →L[𝕜] U) :
    μ {ω | ∃ x : V, ‖x‖ = 1 ∧ ‖T ω x‖ < t} ≤
      μ {ω | K < ‖T ω‖} + ∑ u ∈ N, μ {ω | ‖T ω u‖ < t + ε * K} := by
  calc μ {ω | ∃ x : V, ‖x‖ = 1 ∧ ‖T ω x‖ < t}
      ≤ μ ({ω | K < ‖T ω‖} ∪ ⋃ u ∈ N, {ω | ‖T ω u‖ < t + ε * K}) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨x, hx, hTx⟩ := hω
        by_cases hK : K < ‖T ω‖
        · exact Or.inl hK
        · push Not at hK
          obtain ⟨u, hu, hxu⟩ := hN x hx
          refine Or.inr (Set.mem_biUnion hu ?_)
          have h1 := (norm_apply_sub_le (T ω) x u).1
          have h2 : ‖T ω‖ * ‖x - u‖ ≤ K * ε :=
            mul_le_mul hK hxu (norm_nonneg _) ((norm_nonneg _).trans hK)
          show ‖T ω u‖ < t + ε * K
          linarith
    _ ≤ μ {ω | K < ‖T ω‖} + μ (⋃ u ∈ N, {ω | ‖T ω u‖ < t + ε * K}) := measure_union_le _ _
    _ ≤ μ {ω | K < ‖T ω‖} + ∑ u ∈ N, μ {ω | ‖T ω u‖ < t + ε * K} := by
        gcongr
        exact measure_biUnion_finset_le _ _

/-- `measure_exists_unit_lt_le` with the infimum over the unit sphere (`V` nontrivial):
`μ{inf_{‖x‖=1} ‖T x‖ < t} ≤ μ{‖T‖ > K} + Σ_{u ∈ N} μ{‖T u‖ < t + ε K}`. -/
theorem measure_iInf_sphere_lt_le [Nontrivial V] (μ : Measure Ω) {ε K t : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : Ω → V →L[𝕜] U) :
    μ {ω | (⨅ x : sphere (0 : V) 1, ‖T ω x‖) < t} ≤
      μ {ω | K < ‖T ω‖} + ∑ u ∈ N, μ {ω | ‖T ω u‖ < t + ε * K} := by
  have : {ω | (⨅ x : sphere (0 : V) 1, ‖T ω x‖) < t} =
      {ω | ∃ x : V, ‖x‖ = 1 ∧ ‖T ω x‖ < t} := by
    ext ω; exact iInf_sphere_lt_iff (T ω) t
  rw [this]
  exact measure_exists_unit_lt_le μ hN T

/-- Union bound for operator-norm tails: for an `ε`-net `N` with `0 ≤ ε ≤ 1/2` and `0 ≤ s`,
`μ{‖T‖ > s} ≤ Σ_{u ∈ N} μ{‖T u‖ > s/2}`. -/
theorem measure_opNorm_gt_le (μ : Measure Ω) {ε s : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (hε : 0 ≤ ε) (hε2 : ε ≤ 1 / 2) (hs : 0 ≤ s)
    (T : Ω → V →L[𝕜] U) :
    μ {ω | s < ‖T ω‖} ≤ ∑ u ∈ N, μ {ω | s / 2 < ‖T ω u‖} := by
  calc μ {ω | s < ‖T ω‖} ≤ μ (⋃ u ∈ N, {ω | s / 2 < ‖T ω u‖}) := by
        refine measure_mono fun ω hω => ?_
        by_contra hcon
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
        have := opNorm_le_two_mul_of_net hN hε hε2 (by positivity) (T ω) hcon
        have hω' : s < ‖T ω‖ := hω
        linarith
    _ ≤ _ := measure_biUnion_finset_le _ _

/-- Uniform-term form of `measure_exists_unit_lt_le`: if each net point has
`μ{‖T u‖ < t + ε K} ≤ p`, then `μ{∃ ‖x‖=1, ‖T x‖ < t} ≤ μ{‖T‖ > K} + |N| p`. -/
theorem measure_exists_unit_lt_le_net_card (μ : Measure Ω) {ε K t : ℝ} {N : Finset V}
    (hN : ∀ x : V, ‖x‖ = 1 → ∃ u ∈ N, ‖x - u‖ ≤ ε) (T : Ω → V →L[𝕜] U) {p : ENNReal}
    (hp : ∀ u ∈ N, μ {ω | ‖T ω u‖ < t + ε * K} ≤ p) :
    μ {ω | ∃ x : V, ‖x‖ = 1 ∧ ‖T ω x‖ < t} ≤ μ {ω | K < ‖T ω‖} + N.card * p := by
  refine (measure_exists_unit_lt_le μ (K := K) (t := t) hN T).trans ?_
  gcongr
  calc ∑ u ∈ N, μ {ω | ‖T ω u‖ < t + ε * K} ≤ ∑ _u ∈ N, p := Finset.sum_le_sum hp
    _ = N.card * p := by rw [Finset.sum_const, nsmul_eq_mul]

end UnionBound

section Combined

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Combined net bound, real case (the `(Ct^{-3/2})^{2k}` step of the paper with
`ε = t^{3/2}/2`): for `0 < ε ≤ 1`, if every unit vector `u` has `μ{‖T u‖ < t + ε K} ≤ p`, then
`μ{∃ ‖x‖=1, ‖T x‖ < t} ≤ μ{‖T‖ > K} + (3/ε)^d p`, `d = finrank ℝ V`. -/
theorem measure_exists_unit_lt_le_real {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup U] [NormedSpace ℝ U] (μ : Measure Ω)
    {ε K t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (T : Ω → V →L[ℝ] U) {p : ENNReal}
    (hp : ∀ u : V, ‖u‖ = 1 → μ {ω | ‖T ω u‖ < t + ε * K} ≤ p) :
    μ {ω | ∃ x : V, ‖x‖ = 1 ∧ ‖T ω x‖ < t} ≤
      μ {ω | K < ‖T ω‖} + ENNReal.ofReal ((3 / ε) ^ finrank ℝ V) * p := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_sphere_net (V := V) hε hε1
  refine (measure_exists_unit_lt_le_net_card μ hN3 T fun u hu => hp u (hN1 u hu)).trans ?_
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hN2

/-- Combined net bound, complex case: for a finite-dimensional complex normed space `E` and
`ℂ`-linear `T`, `μ{∃ ‖x‖=1, ‖T x‖ < t} ≤ μ{‖T‖ > K} + (3/ε)^(2 finrank ℂ E) p` for `0 < ε ≤ 1`
(exponent `2k` for `E = Ran P`, `k = dim_ℂ Ran P`, as in the paper). -/
theorem measure_exists_unit_lt_le_complex {E U : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup U] [NormedSpace ℂ U]
    (μ : Measure Ω) {ε K t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (T : Ω → E →L[ℂ] U) {p : ENNReal}
    (hp : ∀ u : E, ‖u‖ = 1 → μ {ω | ‖T ω u‖ < t + ε * K} ≤ p) :
    μ {ω | ∃ x : E, ‖x‖ = 1 ∧ ‖T ω x‖ < t} ≤
      μ {ω | K < ‖T ω‖} + ENNReal.ofReal ((3 / ε) ^ (2 * finrank ℂ E)) * p := by
  obtain ⟨N, hN1, hN2, hN3⟩ := exists_sphere_net_complex (E := E) hε hε1
  refine (measure_exists_unit_lt_le_net_card μ hN3 T fun u hu => hp u (hN1 u hu)).trans ?_
  gcongr
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hN2

end Combined

end BlockBand.Layers
