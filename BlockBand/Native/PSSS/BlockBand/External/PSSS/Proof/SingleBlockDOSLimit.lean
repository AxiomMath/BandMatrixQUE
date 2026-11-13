module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.SingleBlockDOSFiniteGrid

/-!
# Refining-grid limit for the single-block density of states

For a deterministically deformed GUE block of variance `1/N`, the expected number of eigenvalues
in `[a, b]` is at most `C N (b - a)`, with `C` uniform in the dimension, the deformation and the
interval. The bound is obtained by Fatou's lemma along equal-width refining grids, counting
occupied cells at an almost surely simple spectrum.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Every point in the half-open interval covered by an equal-width grid belongs
to one of its cells. -/
theorem exists_grid_cell_of_mem_Ico {m : ℕ} {a w x : ℝ} (_hw : 0 < w)
    (hx : x ∈ Set.Ico a (a + m * w)) :
    ∃ k : Fin m, x ∈ Set.Ico (a + k * w) (a + (k + 1) * w) := by
  induction m with
  | zero => simp at hx
  | succ m ih =>
      by_cases hxm : x < a + m * w
      · obtain ⟨k, hk⟩ := ih ⟨hx.1, hxm⟩
        exact ⟨k.castSucc, by simpa using hk⟩
      · refine ⟨⟨m, Nat.lt_succ_self m⟩, ?_⟩
        constructor
        · exact le_of_not_gt hxm
        · simpa [Nat.cast_add, Nat.cast_one, add_mul, add_assoc] using hx.2

/-- A cell of width `w` cannot contain two distinct spectral coordinates whose
separation is at least `w`. -/
theorem grid_cell_atMostOne_of_separated {N m : ℕ}
    (H : HermitianMatrix (Fin N)) (a w : ℝ) (_hw : 0 < w)
    (hsep : ∀ i j, i ≠ j → w ≤ |orderedEigenvalue H i - orderedEigenvalue H j|)
    (k : Fin m) :
    Set.Subsingleton {i : Fin (Fintype.card (Fin N)) |
      orderedEigenvalue H i ∈ Set.Ico (a + k * w) (a + (k + 1) * w)} := by
  intro i hi j hj
  by_contra hij
  have hd := hsep i j hij
  have hi' := hi.2
  have hj' := hj.2
  have hloi := hi.1
  have hloj := hj.1
  have habs : |orderedEigenvalue H i - orderedEigenvalue H j| < w := by
    rw [abs_lt]
    constructor <;> linarith
  exact (not_lt_of_ge hd) habs

/-- At a separated simple spectrum, the multiplicity count in the grid's
half-open union is bounded by the number of occupied cells. -/
theorem eigenCount_Ico_le_gridOccupiedCount_of_separated {N m : ℕ}
    (H : HermitianMatrix (Fin N)) (a w : ℝ) (hw : 0 < w)
    (hsep : ∀ i j, i ≠ j → w ≤ |orderedEigenvalue H i - orderedEigenvalue H j|) :
    eigenCount H (Set.Ico a (a + m * w)) ≤ gridOccupiedCount H a w m := by
  classical
  let S := Finset.univ.filter fun i : Fin (Fintype.card (Fin N)) =>
    orderedEigenvalue H i ∈ Set.Ico a (a + m * w)
  have hex : ∀ i : S, ∃ k : Fin m,
      orderedEigenvalue H i.1 ∈ Set.Ico (a + k * w) (a + (k + 1) * w) := by
    intro i
    exact exists_grid_cell_of_mem_Ico hw (Finset.mem_filter.mp i.2).2
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hs := grid_cell_atMostOne_of_separated H a w hw hsep (f i)
    exact hne (hs (hf i) (by simpa [hij] using hf j))
  have himage : Finset.image f Finset.univ ⊆
      Finset.univ.filter fun k : Fin m => gridCellOccupied H a w k := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, _hi, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i.1, hf i⟩⟩
  calc
    eigenCount H (Set.Ico a (a + m * w)) = S.card := by
      rw [eigenCount_def]
      apply congrArg Finset.card
      ext i
      simp [S]
    _ = (Finset.image f Finset.univ).card := by
      rw [Finset.card_image_of_injective _ hfinj]
      simp
    _ ≤ (Finset.univ.filter fun k : Fin m => gridCellOccupied H a w k).card :=
      Finset.card_le_card himage
    _ = gridOccupiedCount H a w m := by
      unfold gridOccupiedCount
      let p : Fin m → Prop := fun k => gridCellOccupied H a w k
      have hb := Finset.sum_boole (R := ℕ) p Finset.univ
      exact hb.symm

/-- Number of cells in the `n`th equal-width refining grid. -/
def singleBlockGridCount (N : ℕ) (L : ℝ) (n : ℕ) : ℕ :=
  N * (⌈L⌉₊ + n + 1)

/-- Width of a cell in the `n`th equal-width refining grid. -/
def singleBlockGridWidth (N : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  L / singleBlockGridCount N L n

lemma singleBlockGridCount_pos {N : ℕ} (hN : 0 < N) (L : ℝ) (n : ℕ) :
    0 < singleBlockGridCount N L n := by
  unfold singleBlockGridCount
  exact Nat.mul_pos hN (by omega)

lemma singleBlockGridWidth_pos {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < singleBlockGridWidth N L n := by
  unfold singleBlockGridWidth
  exact div_pos hL (by exact_mod_cast singleBlockGridCount_pos hN L n)

lemma singleBlockGridCount_mul_width {N : ℕ} (hN : 0 < N) (L : ℝ) (n : ℕ) :
    (singleBlockGridCount N L n : ℝ) * singleBlockGridWidth N L n = L := by
  unfold singleBlockGridWidth
  field_simp [ne_of_gt (singleBlockGridCount_pos hN L n)]

lemma singleBlockGrid_mesh_le_one {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 0 < L)
    (n : ℕ) :
    (N : ℝ) * singleBlockGridWidth N L n ≤ 1 := by
  have hceil : L ≤ (⌈L⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil L
  have hq : L ≤ (⌈L⌉₊ + n + 1 : ℕ) := by
    exact hceil.trans (by exact_mod_cast Nat.le_add_right (⌈L⌉₊) (n + 1))
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold singleBlockGridWidth singleBlockGridCount
  rw [Nat.cast_mul]
  have hqpos : (0 : ℝ) < (⌈L⌉₊ + n + 1 : ℕ) := by positivity
  calc
    (N : ℝ) * (L / ((N : ℝ) * (⌈L⌉₊ + n + 1 : ℕ))) =
        L / (⌈L⌉₊ + n + 1 : ℕ) := by field_simp
    _ ≤ 1 := (div_le_one hqpos).2 (by exact_mod_cast hq)

lemma tendsto_singleBlockGridWidth_zero {N : ℕ} (hN : 0 < N) (L : ℝ) :
    Tendsto (singleBlockGridWidth N L) atTop (𝓝 0) := by
  have hm : Tendsto (fun n : ℕ => (singleBlockGridCount N L n : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro B
    filter_upwards [eventually_ge_atTop ⌈max B 0⌉₊] with n hn
    have hB : B ≤ (n : ℝ) := by
      calc
        B ≤ max B 0 := le_max_left _ _
        _ ≤ (⌈max B 0⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil (max B 0)
        _ ≤ n := by exact_mod_cast hn
    have hncount : n ≤ singleBlockGridCount N L n := by
      unfold singleBlockGridCount
      have hN1 : 1 ≤ N := hN
      nlinarith [Nat.le_add_left n (⌈L⌉₊ + 1)]
    exact hB.trans (by exact_mod_cast hncount)
  change Tendsto (fun n => L / (singleBlockGridCount N L n : ℝ)) atTop (𝓝 0)
  exact hm.const_div_atTop L

/-- On a simple finite spectrum, every sufficiently fine grid has mesh no larger
than every nonzero spectral gap. -/
lemma eventually_singleBlockGridWidth_le_gaps {N : ℕ} (hN : 0 < N) {L : ℝ}
    (_hL : 0 < L) (H : HermitianMatrix (Fin N))
    (hinj : Function.Injective (orderedEigenvalue H)) :
    ∀ᶠ n in atTop, ∀ i j, i ≠ j →
      singleBlockGridWidth N L n ≤
        |orderedEigenvalue H i - orderedEigenvalue H j| := by
  have hw := tendsto_singleBlockGridWidth_zero hN L
  simp only [eventually_all]
  intro i j hij
  have hgap : 0 < |orderedEigenvalue H i - orderedEigenvalue H j| :=
    abs_pos.mpr (sub_ne_zero.mpr (hinj.ne hij))
  filter_upwards [hw.eventually_lt_const hgap] with n hn
  exact hn.le

/-- If the right endpoint is not an eigenvalue, closed- and half-open-interval
multiplicity counts agree. -/
lemma eigenCount_Icc_eq_Ico_of_right_not_eigenvalue {N : ℕ}
    (H : HermitianMatrix (Fin N)) (a b : ℝ)
    (hb : ∀ i, orderedEigenvalue H i ≠ b) :
    eigenCount H (Set.Icc a b) = eigenCount H (Set.Ico a b) := by
  rw [eigenCount_def, eigenCount_def]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc, Set.mem_Ico]
  constructor
  · intro hi
    exact ⟨hi.1, lt_of_le_of_ne hi.2 (hb i)⟩
  · intro hi
    exact ⟨hi.1, hi.2.le⟩

/-- Almost surely, the closed-interval eigenvalue count is eventually bounded by
its refining-grid occupied-cell count. -/
lemma ae_eventually_eigenCount_Icc_le_gridOccupiedCount {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N)) {a b : ℝ} (hab : a < b) :
    ∀ᵐ V ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N))),
      ∀ᶠ n in atTop,
        eigenCount (addHermitian A V) (Set.Icc a b) ≤
          gridOccupiedCount (addHermitian A V) a
            (singleBlockGridWidth N (b - a) n)
            (singleBlockGridCount N (b - a) n) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  filter_upwards [ae_publicGUE_addHermitian_orderedEigenvalue_injective hN A,
    ae_publicGUE_det_energyShift_add_ne_zero hN A b] with V hinj hdet
  have hzero : eigenCount (addHermitian A V) {b} = 0 :=
    eigenCount_singleton_eq_zero_of_det_energyShift_ne_zero
      (addHermitian A V) b (by simpa [addHermitian] using hdet)
  have hb : ∀ i, orderedEigenvalue (addHermitian A V) i ≠ b :=
    (eigenCount_singleton_eq_zero_iff (addHermitian A V) b).1 hzero
  filter_upwards [eventually_singleBlockGridWidth_le_gaps hN hL
    (addHermitian A V) hinj] with n hsep
  rw [eigenCount_Icc_eq_Ico_of_right_not_eigenvalue _ a b hb]
  have hend : a + (singleBlockGridCount N (b - a) n : ℝ) *
      singleBlockGridWidth N (b - a) n = b := by
    rw [singleBlockGridCount_mul_width hN]
    ring
  calc
    eigenCount (addHermitian A V) (Set.Ico a b) =
        eigenCount (addHermitian A V)
          (Set.Ico a (a + (singleBlockGridCount N (b - a) n : ℝ) *
            singleBlockGridWidth N (b - a) n)) := by rw [hend]
    _ ≤ gridOccupiedCount (addHermitian A V) a
        (singleBlockGridWidth N (b - a) n)
        (singleBlockGridCount N (b - a) n) :=
      eigenCount_Ico_le_gridOccupiedCount_of_separated _ _ _
        (singleBlockGridWidth_pos hN hL n) hsep

/-- Sharp closed-interval density-of-states bound for every nondegenerate
interval, obtained by Fatou along the equal-width occupied-cell grids. -/
lemma exists_publicGUE_lintegral_eigenCount_Icc_le_of_lt :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (N : ℕ), 0 < N → ∀ (A : HermitianMatrix (Fin N))
      (a b : ℝ), a < b →
      (∫⁻ V, (eigenCount (addHermitian A V) (Set.Icc a b) : ℝ≥0∞)
        ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
          Measure (HermitianMatrix (Fin N)))) ≤
      ENNReal.ofReal (K * N * (b - a)) := by
  obtain ⟨K, hK, hgrid⟩ := exists_publicGUE_lintegral_gridOccupiedCount_le
  refine ⟨K, hK, ?_⟩
  intro N hN A a b hab
  let μ := (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
    Measure (HermitianMatrix (Fin N)))
  let f : ℕ → HermitianMatrix (Fin N) → ℝ≥0∞ := fun n V =>
    (gridOccupiedCount (addHermitian A V) a
      (singleBlockGridWidth N (b - a) n)
      (singleBlockGridCount N (b - a) n) : ℝ≥0∞)
  have hpoint : ∀ᵐ V ∂μ,
      (eigenCount (addHermitian A V) (Set.Icc a b) : ℝ≥0∞) ≤
        liminf (fun n => f n V) atTop := by
    filter_upwards [ae_eventually_eigenCount_Icc_le_gridOccupiedCount hN A hab]
      with V hV
    apply Filter.le_liminf_of_le (show
      IsCoboundedUnder (fun x y : ENNReal => y ≤ x) atTop (fun n => f n V)
        from ⟨⊤, by simp⟩)
    filter_upwards [hV] with n hn
    dsimp [f]
    exact_mod_cast hn
  calc
    (∫⁻ V, (eigenCount (addHermitian A V) (Set.Icc a b) : ℝ≥0∞) ∂μ) ≤
        ∫⁻ V, liminf (fun n => f n V) atTop ∂μ := lintegral_mono_ae hpoint
    _ ≤ liminf (fun n => ∫⁻ V, f n V ∂μ) atTop := by
      apply lintegral_liminf_le
      intro n
      exact MeasurableEmbedding.natCast.measurable.comp
        (measurable_gridOccupiedCount_addHermitian A a
          (singleBlockGridWidth N (b - a) n)
          (singleBlockGridCount N (b - a) n))
    _ ≤ ENNReal.ofReal (K * N * (b - a)) := by
      let I : ℕ → ENNReal := fun n => ∫⁻ V, f n V ∂μ
      have hbounded : IsBoundedUnder (fun x y : ENNReal => y ≤ x) atTop I :=
        ⟨0, by simp⟩
      apply Filter.liminf_le_of_le hbounded
      intro c hc
      obtain ⟨n, hn⟩ := hc.exists
      refine hn.trans ?_
      dsimp [I, f, μ]
      simpa [singleBlockGridCount_mul_width hN] using
        hgrid N hN A a (singleBlockGridWidth N (b - a) n)
          (singleBlockGridWidth_pos hN (sub_pos.mpr hab) n)
          (singleBlockGrid_mesh_le_one hN (sub_pos.mpr hab) n)
          (singleBlockGridCount N (b - a) n)

/-- Fixed energies carry no eigenvalue mass under a deterministically deformed
public GUE block. -/
lemma publicGUE_lintegral_eigenCount_singleton_eq_zero {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N)) (a : ℝ) :
    (∫⁻ V, (eigenCount (addHermitian A V) {a} : ℝ≥0∞)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) = 0 := by
  calc
    (∫⁻ V, (eigenCount (addHermitian A V) {a} : ℝ≥0∞)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) = ∫⁻ _V, 0
        ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
          Measure (HermitianMatrix (Fin N))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_publicGUE_det_energyShift_add_ne_zero hN A a] with V hdet
      have hzero : eigenCount (addHermitian A V) {a} = 0 :=
        eigenCount_singleton_eq_zero_of_det_energyShift_ne_zero
          (addHermitian A V) a (by simpa [addHermitian] using hdet)
      simp [hzero]
    _ = 0 := lintegral_zero

/-- **PSSS single-block density of states.** There is an absolute constant `C`, uniform in the
dimension, the deterministic Hermitian deformation and the closed energy interval, bounding the
expected eigenvalue count of a deformed variance-`1/N` GUE block as in `SingleBlockDOS`. -/
theorem singleBlock_dos :
    ∃ C : ℝ, 1 ≤ C ∧ SingleBlockDOS C := by
  obtain ⟨K, hK, hbound⟩ := exists_publicGUE_lintegral_eigenCount_Icc_le_of_lt
  refine ⟨K, hK, ?_⟩
  intro N hN A a b hab
  change (∫⁻ V, (eigenCount (addHermitian A V) (Set.Icc a b) : ℝ≥0∞)
    ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N)))) ≤
    ENNReal.ofReal (K * N * (b - a))
  rcases hab.eq_or_lt with rfl | hab
  · simpa using publicGUE_lintegral_eigenCount_singleton_eq_zero hN A a
  · exact hbound N hN A a b hab

end PSSSNative.BlockBand.PSSS
