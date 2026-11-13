module

public import BlockBand.SourceProcess.ContractingWords.LayerPins

/-!
# The contracting products are admitted, contracting, of the right degree

* `contrDrift_facts`: every product in `contrDrift w` (`w ≠ []`) is admitted, has degree `|w|`
  and at least one contracting letter; `contrDrift_length_le`: there are at most `20|w|²` of them.
* `contrCov_facts`, `contrCov_length_le`: the same for `contrCov w v`, degree `|w| + |v|`, at most
  `16|w||v|` products.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open BlockBand.Internal.Contracts.TransmissionStatements

variable {nT nI : ℕ}

/-- The contracting-letter count of a product. -/
theorem count_product (Zs : List (TraceWord nT nI)) :
    unconjCount Zs + conjCount Zs =
      (Zs.map fun w => (w.map fun x => x.2.unconj).sum + (w.map fun x => x.2.conj).sum).sum := by
  induction Zs with
  | nil => simp [unconjCount, conjCount]
  | cons w Zs ih =>
    simp only [unconjCount, conjCount, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem length_pairS₁ (w : TraceWord nT nI) {i j : ℕ} (hij : i < j) (hj : j < w.length) :
    (pairS₁ w i j).length = w.length - (j - i) := by
  simp only [pairS₁, List.length_take, List.length_rotate]; omega

theorem length_pairS₂ (w : TraceWord nT nI) {i j : ℕ} (hij : i < j) (hj : j < w.length) :
    (pairS₂ w i j).length = j - i := by
  simp only [pairS₂, List.length_take, List.length_rotate]; omega

theorem ne_nil_of_length_pos {w : TraceWord nT nI} (h : 0 < w.length) : w ≠ [] := by
  rintro rfl; simp at h

theorem contrDrift_facts (w : TraceWord nT nI) :
    ∀ Zs ∈ contrDrift w, IsAdmittedProduct Zs ∧ productDegree Zs = w.length ∧
      1 ≤ unconjCount Zs + conjCount Zs := by
  intro Zs hZs
  rcases List.mem_append.mp hZs with h | h
  · obtain ⟨p, hp, h⟩ := List.mem_flatMap.mp h
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp h
    have hp' := List.mem_range.mp hp
    have hlen : (setSepAt w p σ).length = w.length := List.length_modify _ _ _
    refine ⟨fun v hv => ?_, ?_, ?_⟩
    · rw [List.mem_singleton.mp hv]; exact ne_nil_of_length_pos (by omega)
    · simp [productDegree, hlen]
    · rw [count_product]; simpa using count_setSepAt hp' hσ
  · obtain ⟨j, hj, h⟩ := List.mem_flatMap.mp h
    obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp h
    obtain ⟨σ, hσ, h⟩ := List.mem_flatMap.mp h
    obtain ⟨σ', hσ', rfl⟩ := List.mem_map.mp h
    have hj' := List.mem_range.mp hj
    have hi' := List.mem_range.mp hi
    have h1 := length_pairS₁ w hi' hj'
    have h2 := length_pairS₂ w hi' hj'
    have n1 : pairS₁ w i j ≠ [] := ne_nil_of_length_pos (by omega)
    have n2 : pairS₂ w i j ≠ [] := ne_nil_of_length_pos (by omega)
    refine ⟨fun v hv => ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ne_nil_of_length_pos (by rw [length_setLastSep]; omega)
      · exact ne_nil_of_length_pos (by rw [length_setLastSep]; omega)
    · simp only [productDegree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        length_setLastSep, h1, h2]
      omega
    · rw [count_product]
      have := count_setLastSep n1 hσ
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

theorem length_flatMap_le {α β : Type*} (L : List α) (f : α → List β) {M : ℕ}
    (h : ∀ a ∈ L, (f a).length ≤ M) : (L.flatMap f).length ≤ L.length * M := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    nlinarith

theorem contrSeps_length : contrSeps.length = 4 := rfl

theorem length_flatMap_range_le {β : Type*} (n : ℕ) (f : ℕ → List β) {M : ℕ}
    (h : ∀ a < n, (f a).length ≤ M) : ((List.range n).flatMap f).length ≤ n * M := by
  have := length_flatMap_le (List.range n) f fun a ha => h a (List.mem_range.mp ha)
  simpa using this

theorem length_seps_le {β : Type*} (f : Separator → Separator → β) :
    (contrSeps.flatMap fun σ => contrSeps.map fun σ' => f σ σ').length ≤ 16 := by
  simp [contrSeps]

theorem contrDrift_length_le (w : TraceWord nT nI) :
    (contrDrift w).length ≤ 20 * w.length ^ 2 := by
  have h1 : (contrOne w).length ≤ w.length * 4 := by
    unfold contrOne
    exact length_flatMap_range_le _ _ fun p _ => by simp [contrSeps_length]
  have h2 : (contrTwo w).length ≤ w.length * (w.length * 16) := by
    unfold contrTwo
    refine length_flatMap_range_le _ _ fun j hj => ?_
    exact (length_flatMap_range_le _ _ fun i _ => length_seps_le _).trans
      (Nat.mul_le_mul_right _ hj.le)
  have : (contrDrift w).length = (contrOne w).length + (contrTwo w).length :=
    List.length_append ..
  have h3 : w.length ≤ w.length ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : w.length * (w.length * 16) = 16 * w.length ^ 2 := by ring
  omega

theorem contrCov_facts (w v : TraceWord nT nI) (hw : w ≠ []) :
    ∀ Zs ∈ contrCov w v, IsAdmittedProduct Zs ∧ productDegree Zs = w.length + v.length ∧
      1 ≤ unconjCount Zs + conjCount Zs := by
  intro Zs hZs
  obtain ⟨i, -, h⟩ := List.mem_flatMap.mp hZs
  obtain ⟨j, -, h⟩ := List.mem_flatMap.mp h
  obtain ⟨σ, hσ, h⟩ := List.mem_flatMap.mp h
  obtain ⟨σ', -, rfl⟩ := List.mem_map.mp h
  have nw : w.rotate (i + 1) ≠ [] := by
    intro h; exact hw (List.rotate_eq_nil_iff.mp h)
  refine ⟨fun u hu => ?_, ?_, ?_⟩
  · rw [List.mem_singleton.mp hu]
    exact ne_nil_of_length_pos (by
      rw [List.length_append, length_setLastSep, List.length_rotate]
      exact Nat.add_pos_left (List.length_pos_iff.mpr hw) _)
  · simp [productDegree, length_setLastSep]
  · rw [count_product]
    have := count_setLastSep nw hσ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_append,
      List.sum_append]
    omega

theorem contrCov_length_le (w v : TraceWord nT nI) :
    (contrCov w v).length ≤ w.length * (v.length * 16) := by
  unfold contrCov
  exact length_flatMap_range_le _ _ fun i _ => length_flatMap_range_le _ _ fun j _ =>
    length_seps_le _

end BlockBand.SourceProcess.ContractingWords
