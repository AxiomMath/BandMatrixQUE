module

public import BlockBand.Transmission.Dual.UniqueLevel

/-!
# Regular exhaustion compacts of the chamber

Facts:
* `boxOpen` is open, `boxClosed` is compact, `closure (boxOpen q n) ⊆ boxClosed q n`;
* `boxClosed q n ⊆ boxOpen q (n+1)` and `boxClosed q n ⊆ 𝒞_q`;
* every point (`eventually_mem_boxOpen`) and every compact subset (`exists_boxOpen_superset`)
  of `𝒞_q` lies in some `boxOpen q n`;
* flat form: `isInteriorDomain_flatBox`, the interior-domain hypothesis on
  `W_n = ofFlat ⁻¹' boxOpen q n`;
* the pair `(x₀, y_j)` and the rest `(x ∘ succ, y ∘ j.succAbove)` of a point of
  `boxOpen (q+1) n` lie in `boxOpen 1 n` and `boxOpen q n` (`pair_mem_boxOpen`,
  `rest_mem_boxOpen`). Only the open boxes are needed, so convexity and
  `closure (int K) = K` are not used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual

variable {q : ℕ}

/-- The lower margin `1/(n+1)`. -/
def margin (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem margin_pos (n : ℕ) : 0 < margin n := by unfold margin; positivity

theorem margin_succ_lt (n : ℕ) : margin (n + 1) < margin n := by
  unfold margin; push_cast
  exact one_div_lt_one_div_of_lt (by positivity) (by linarith)

theorem margin_le_one (n : ℕ) : margin n ≤ 1 := by
  unfold margin
  rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The open polytope `int K^{(q)}_{n+1}`. -/
def boxOpen (q n : ℕ) : Set (DualCoord q) :=
  {z | (∀ i, margin n < z.1 i ∧ z.1 i < n + 1) ∧ (∀ i k, i < k → margin n < z.1 k - z.1 i) ∧
    (∀ j, margin n < z.2 j ∧ z.2 j < 1 - margin n) ∧ (∀ j l, j < l → margin n < z.2 l - z.2 j)}

/-- The closed polytope `K^{(q)}_{n+1}`. -/
def boxClosed (q n : ℕ) : Set (DualCoord q) :=
  {z | (∀ i, margin n ≤ z.1 i ∧ z.1 i ≤ n + 1) ∧ (∀ i k, i < k → margin n ≤ z.1 k - z.1 i) ∧
    (∀ j, margin n ≤ z.2 j ∧ z.2 j ≤ 1 - margin n) ∧ (∀ j l, j < l → margin n ≤ z.2 l - z.2 j)}

section Topology

private theorem cx (i : Fin q) : Continuous fun z : DualCoord q => z.1 i :=
  (continuous_apply i).comp continuous_fst

private theorem cy (j : Fin q) : Continuous fun z : DualCoord q => z.2 j :=
  (continuous_apply j).comp continuous_snd

theorem isOpen_boxOpen (q n : ℕ) : IsOpen (boxOpen q n) := by
  have h1 : IsOpen {z : DualCoord q | ∀ i, margin n < z.1 i ∧ z.1 i < n + 1} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (cx i)).inter (isOpen_lt (cx i) continuous_const)
  have h2 : IsOpen {z : DualCoord q | ∀ i k, i < k → margin n < z.1 k - z.1 i} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const ((cx k).sub (cx i))
  have h3 : IsOpen {z : DualCoord q | ∀ j, margin n < z.2 j ∧ z.2 j < 1 - margin n} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j =>
      (isOpen_lt continuous_const (cy j)).inter (isOpen_lt (cy j) continuous_const)
  have h4 : IsOpen {z : DualCoord q | ∀ j l, j < l → margin n < z.2 l - z.2 j} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun l =>
      isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const ((cy l).sub (cy j))
  exact h1.inter (h2.inter (h3.inter h4))

theorem isClosed_boxClosed (q n : ℕ) : IsClosed (boxClosed q n) := by
  have h1 : IsClosed {z : DualCoord q | ∀ i, margin n ≤ z.1 i ∧ z.1 i ≤ n + 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (cx i)).inter (isClosed_le (cx i) continuous_const)
  have h2 : IsClosed {z : DualCoord q | ∀ i k, i < k → margin n ≤ z.1 k - z.1 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun k =>
      isClosed_iInter fun _ => isClosed_le continuous_const ((cx k).sub (cx i))
  have h3 : IsClosed {z : DualCoord q | ∀ j, margin n ≤ z.2 j ∧ z.2 j ≤ 1 - margin n} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j =>
      (isClosed_le continuous_const (cy j)).inter (isClosed_le (cy j) continuous_const)
  have h4 : IsClosed {z : DualCoord q | ∀ j l, j < l → margin n ≤ z.2 l - z.2 j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun l =>
      isClosed_iInter fun _ => isClosed_le continuous_const ((cy l).sub (cy j))
  exact h1.inter (h2.inter (h3.inter h4))

theorem boxOpen_subset_boxClosed (q n : ℕ) : boxOpen q n ⊆ boxClosed q n := fun _ hz =>
  ⟨fun i => ⟨(hz.1 i).1.le, (hz.1 i).2.le⟩, fun i k h => (hz.2.1 i k h).le,
    fun j => ⟨(hz.2.2.1 j).1.le, (hz.2.2.1 j).2.le⟩, fun j l h => (hz.2.2.2 j l h).le⟩

theorem closure_boxOpen_subset (q n : ℕ) : closure (boxOpen q n) ⊆ boxClosed q n :=
  closure_minimal (boxOpen_subset_boxClosed q n) (isClosed_boxClosed q n)

theorem isCompact_boxClosed (q n : ℕ) : IsCompact (boxClosed q n) := by
  have hK : IsCompact ((univ.pi fun _ : Fin q => Icc (0 : ℝ) (n + 1)) ×ˢ
      (univ.pi fun _ : Fin q => Icc (0 : ℝ) 1)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  refine hK.of_isClosed_subset (isClosed_boxClosed q n) fun z hz => ?_
  have hm := margin_pos n
  refine ⟨fun i _ => ⟨hm.le.trans (hz.1 i).1, (hz.1 i).2⟩, fun j _ => ?_⟩
  exact ⟨hm.le.trans (hz.2.2.1 j).1, (hz.2.2.1 j).2.trans (by linarith)⟩

theorem isCompact_closure_boxOpen (q n : ℕ) : IsCompact (closure (boxOpen q n)) :=
  (isCompact_boxClosed q n).of_isClosed_subset isClosed_closure (closure_boxOpen_subset q n)

end Topology

theorem boxClosed_subset_boxOpen_succ (q n : ℕ) : boxClosed q n ⊆ boxOpen q (n + 1) := by
  intro z hz
  have hm := margin_succ_lt n
  refine ⟨fun i => ⟨hm.trans_le (hz.1 i).1, ?_⟩, fun i k h => hm.trans_le (hz.2.1 i k h),
    fun j => ⟨hm.trans_le (hz.2.2.1 j).1, (hz.2.2.1 j).2.trans_lt (by linarith)⟩,
    fun j l h => hm.trans_le (hz.2.2.2 j l h)⟩
  push_cast; linarith [(hz.1 i).2]

theorem boxOpen_subset_succ (q n : ℕ) : boxOpen q n ⊆ boxOpen q (n + 1) :=
  (boxOpen_subset_boxClosed q n).trans (boxClosed_subset_boxOpen_succ q n)

theorem monotone_boxOpen (q : ℕ) : Monotone (boxOpen q) :=
  monotone_nat_of_le_succ (boxOpen_subset_succ q)

theorem boxClosed_subset_dualChamber (q n : ℕ) : boxClosed q n ⊆ dualChamber q := by
  intro z hz
  have hm := margin_pos n
  refine ⟨fun i k h => ?_, fun j l h => ?_, fun i => hm.trans_le (hz.1 i).1, fun j =>
    ⟨hm.trans_le (hz.2.2.1 j).1, (hz.2.2.1 j).2.trans_lt (by linarith)⟩⟩
  · linarith [hz.2.1 i k h]
  · linarith [hz.2.2.2 j l h]

theorem boxOpen_subset_dualChamber (q n : ℕ) : boxOpen q n ⊆ dualChamber q :=
  (boxOpen_subset_boxClosed q n).trans (boxClosed_subset_dualChamber q n)

/-- Every point of the chamber lies in `boxOpen q n` for all large `n`. -/
theorem eventually_mem_boxOpen {z : DualCoord q} (hz : z ∈ dualChamber q) :
    ∀ᶠ n in atTop, z ∈ boxOpen q n := by
  have hm : Tendsto margin atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlt : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, margin n < a := fun a ha =>
    hm.eventually (gt_mem_nhds ha)
  have hbig : ∀ a : ℝ, ∀ᶠ n : ℕ in atTop, a < (n : ℝ) + 1 := fun a => by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop a)]
      with n hn using by linarith
  obtain ⟨hx, hy, hx0, hy0⟩ := hz
  have e1 : ∀ᶠ n in atTop, ∀ i, margin n < z.1 i ∧ z.1 i < n + 1 :=
    eventually_all.2 fun i => (hlt _ (hx0 i)).and (hbig (z.1 i))
  have e2 : ∀ᶠ n in atTop, ∀ i k : Fin q, i < k → margin n < z.1 k - z.1 i := by
    refine eventually_all.2 fun i => eventually_all.2 fun k => ?_
    by_cases h : i < k
    · exact (hlt _ (sub_pos.2 (hx h))).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n h' => absurd h' h
  have e3 : ∀ᶠ n in atTop, ∀ j, margin n < z.2 j ∧ margin n < 1 - z.2 j :=
    eventually_all.2 fun j => (hlt _ (hy0 j).1).and (hlt (1 - z.2 j) (by linarith [(hy0 j).2]))
  have e4 : ∀ᶠ n in atTop, ∀ j l : Fin q, j < l → margin n < z.2 l - z.2 j := by
    refine eventually_all.2 fun j => eventually_all.2 fun l => ?_
    by_cases h : j < l
    · exact (hlt _ (sub_pos.2 (hy h))).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n h' => absurd h' h
  filter_upwards [e1, e2, e3, e4] with n h1 h2 h3 h4
  exact ⟨h1, h2, fun j => ⟨(h3 j).1, by linarith [(h3 j).2]⟩, h4⟩

theorem iUnion_boxOpen (q : ℕ) : ⋃ n, boxOpen q n = dualChamber q :=
  Subset.antisymm (iUnion_subset (boxOpen_subset_dualChamber q)) fun _ hz =>
    mem_iUnion.2 (eventually_mem_boxOpen hz).exists

/-- Every compact subset of the chamber lies in some `boxOpen q n` (hence in all later ones). -/
theorem exists_boxOpen_superset {L : Set (DualCoord q)} (hL : IsCompact L)
    (hLC : L ⊆ dualChamber q) : ∃ n, L ⊆ boxOpen q n := by
  have hcov : L ⊆ ⋃ n, boxOpen q n := by rw [iUnion_boxOpen]; exact hLC
  exact hL.elim_directed_cover _ (fun n => isOpen_boxOpen q n) hcov
    (monotone_boxOpen q).directed_le

/-!
## Flat form: the interior domains
-/

/-- `W_n = ofFlat ⁻¹' boxOpen q n`, the flat interior domain. -/
def flatBox (q n : ℕ) : Set (Fin (q + q) → ℝ) := ofFlat q ⁻¹' boxOpen q n

theorem ofFlat_preimage_eq_image (S : Set (DualCoord q)) :
    ofFlat q ⁻¹' S = flatHomeo q '' S := by
  ext w
  constructor
  · intro hw; exact ⟨ofFlat q w, hw, (flatHomeo q).apply_symm_apply w⟩
  · rintro ⟨z, hz, rfl⟩
    show (flatHomeo q).symm (flatHomeo q z) ∈ S
    rwa [Homeomorph.symm_apply_apply]

theorem isOpen_flatBox (q n : ℕ) : IsOpen (flatBox q n) :=
  (isOpen_boxOpen q n).preimage (ofFlat q).continuous

theorem closure_flatBox_subset (q n : ℕ) :
    closure (flatBox q n) ⊆ ofFlat q ⁻¹' boxClosed q n :=
  closure_minimal (preimage_mono (boxOpen_subset_boxClosed q n))
    ((isClosed_boxClosed q n).preimage (ofFlat q).continuous)

/-- `W_n` is a relatively compact subdomain of the flat chamber. -/
theorem isInteriorDomain_flatBox (q n : ℕ) : IsInteriorDomain (flatBox q n) (flatChamber q) := by
  refine ⟨isOpen_flatBox q n, ?_, (closure_flatBox_subset q n).trans
    (preimage_mono (boxClosed_subset_dualChamber q n))⟩
  have hc : IsCompact (ofFlat q ⁻¹' boxClosed q n) := by
    rw [ofFlat_preimage_eq_image]; exact (isCompact_boxClosed q n).image (flatHomeo q).continuous
  exact hc.of_isClosed_subset isClosed_closure (closure_flatBox_subset q n)

theorem closure_flatBox_subset_succ (q n : ℕ) : closure (flatBox q n) ⊆ flatBox q (n + 1) :=
  (closure_flatBox_subset q n).trans (preimage_mono (boxClosed_subset_boxOpen_succ q n))

/-!
## The projections of the boxes
-/

/-- The pair `(x₀, y_j)` of a point with `q + 1` pairs. -/
def pairOf (j : Fin (q + 1)) (z : DualCoord (q + 1)) : DualCoord 1 :=
  (fun _ => z.1 0, fun _ => z.2 j)

/-- The rest: the `x`'s without `x₀` and the `y`'s without `y_j`, in order. -/
def restOf (j : Fin (q + 1)) (z : DualCoord (q + 1)) : DualCoord q :=
  (fun i => z.1 i.succ, fun l => z.2 (j.succAbove l))

theorem pair_mem_boxOpen {n : ℕ} (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ boxOpen (q + 1) n) : pairOf j z ∈ boxOpen 1 n :=
  ⟨fun _ => hz.1 0, fun i k h => absurd h (by simp [Subsingleton.elim i k]),
    fun _ => hz.2.2.1 j, fun i k h => absurd h (by simp [Subsingleton.elim i k])⟩

theorem rest_mem_boxOpen {n : ℕ} (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ boxOpen (q + 1) n) : restOf j z ∈ boxOpen q n :=
  ⟨fun i => hz.1 i.succ, fun _ _ h => hz.2.1 _ _ (Fin.succ_lt_succ_iff.2 h),
    fun _ => hz.2.2.1 _, fun _ _ h => hz.2.2.2 _ _ (Fin.strictMono_succAbove j h)⟩

theorem pair_mem_boxClosed {n : ℕ} (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ boxClosed (q + 1) n) : pairOf j z ∈ boxClosed 1 n :=
  ⟨fun _ => hz.1 0, fun i k h => absurd h (by simp [Subsingleton.elim i k]),
    fun _ => hz.2.2.1 j, fun i k h => absurd h (by simp [Subsingleton.elim i k])⟩

theorem rest_mem_boxClosed {n : ℕ} (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ boxClosed (q + 1) n) : restOf j z ∈ boxClosed q n :=
  ⟨fun i => hz.1 i.succ, fun _ _ h => hz.2.1 _ _ (Fin.succ_lt_succ_iff.2 h),
    fun _ => hz.2.2.1 _, fun _ _ h => hz.2.2.2 _ _ (Fin.strictMono_succAbove j h)⟩

theorem pair_mem_dualChamber (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ dualChamber (q + 1)) : pairOf j z ∈ dualChamber 1 :=
  ⟨Subsingleton.strictMono _, Subsingleton.strictMono _, fun _ => hz.2.2.1 0,
    fun _ => hz.2.2.2 j⟩

theorem rest_mem_dualChamber (j : Fin (q + 1)) {z : DualCoord (q + 1)}
    (hz : z ∈ dualChamber (q + 1)) : restOf j z ∈ dualChamber q :=
  ⟨hz.1.comp (Fin.strictMono_succ), hz.2.1.comp (Fin.strictMono_succAbove j),
    fun _ => hz.2.2.1 _, fun _ => hz.2.2.2 _⟩

end BlockBand.Transmission.Dual.G
