module

public import Mathlib

/-!
# Finite-`W` time discretisation: integral versus cell sum

`norm_integral_sub_sum_le`: if `f r = g ⌊W (s + r)⌋₊` for `r ≥ 0` except on the `np` cells
`⌊W (s + r)⌋₊ = k i`, and `‖f‖, ‖g‖ ≤ C`, then `∫_{(0,v]} f` and
`∑_{j ∈ [⌊Ws⌋₊, ⌊W(s+v)⌋₊)} g_j / W` differ by at most `C (2 + 2 np) / W`.

Proof. The cell `cell W s j = [j/W − s, (j+1)/W − s)` has length `1/W`, and
`⌊W (s + r)⌋₊ = j` on it. With `h r = g ⌊W (s + r)⌋₊`, the sum is `∫_S h` for the disjoint union
`S` of the cells `j ∈ [a, b)`. One has `A \ S ⊆ cell b` and `S \ A ⊆ cell a` for `A = (0, v]`,
which costs `2 C / W`. The mismatch `f − h` (norm `≤ 2C`) vanishes on `A` outside the `np`
cells `k i`, which costs `2 C np / W`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Set

/-- The cell `[j/W - s, (j+1)/W - s)` on which `⌊W (s + r)⌋₊ = j`. -/
def cell (W : ℕ) (s : ℝ) (j : ℕ) : Set ℝ := Ico ((j : ℝ) / W - s) (((j : ℝ) + 1) / W - s)

lemma floor_eq_of_mem_cell {W : ℕ} (hW : 0 < W) {s r : ℝ} {j : ℕ} (h : r ∈ cell W s j) :
    ⌊(W : ℝ) * (s + r)⌋₊ = j := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  obtain ⟨h1, h2⟩ := h
  have e1 : (j : ℝ) ≤ W * (s + r) := by
    have : (j : ℝ) / W ≤ s + r := by linarith
    rwa [div_le_iff₀ hW', mul_comm] at this
  have e2 : (W : ℝ) * (s + r) < j + 1 := by
    have : s + r < ((j : ℝ) + 1) / W := by linarith
    rwa [lt_div_iff₀ hW', mul_comm] at this
  rw [Nat.floor_eq_iff (by linarith [Nat.cast_nonneg (α := ℝ) j])]
  exact ⟨e1, e2⟩

lemma mem_cell_floor {W : ℕ} (hW : 0 < W) {s r : ℝ} (h0 : 0 ≤ (W : ℝ) * (s + r)) :
    r ∈ cell W s ⌊(W : ℝ) * (s + r)⌋₊ := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have e1 := Nat.floor_le h0
  have e2 := Nat.lt_floor_add_one ((W : ℝ) * (s + r))
  constructor
  · have : (⌊(W : ℝ) * (s + r)⌋₊ : ℝ) / W ≤ s + r := by
      rw [div_le_iff₀ hW']; linarith
    linarith
  · have : s + r < ((⌊(W : ℝ) * (s + r)⌋₊ : ℝ) + 1) / W := by
      rw [lt_div_iff₀ hW']; linarith
    linarith

lemma volume_real_cell {W : ℕ} (hW : 0 < W) (s : ℝ) (j : ℕ) :
    volume.real (cell W s j) = 1 / W := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  rw [cell, Real.volume_real_Ico]
  have : ((j : ℝ) + 1) / W - s - ((j : ℝ) / W - s) = 1 / W := by field_simp; ring
  rw [this, max_eq_left (by positivity)]

lemma volume_cell_ne_top (W : ℕ) (s : ℝ) (j : ℕ) : volume (cell W s j) ≠ ⊤ :=
  measure_Ico_lt_top.ne

theorem norm_integral_sub_sum_le {W : ℕ} (hW : 0 < W) {s : ℝ} (hs : 0 ≤ s) {np : ℕ}
    (k : Fin np → ℕ) {C : ℝ} {f : ℝ → ℂ} {g : ℕ → ℂ} (hfm : Measurable f)
    (hf : ∀ r, ‖f r‖ ≤ C) (hg : ∀ j, ‖g j‖ ≤ C)
    (hfg : ∀ r, 0 ≤ r → (∀ i, ⌊(W:ℝ) * (s + r)⌋₊ ≠ k i) → f r = g ⌊(W:ℝ) * (s + r)⌋₊)
    (v : ℝ) (hv : 0 ≤ v) :
    ‖(∫ r in Set.Ioc (0:ℝ) v, f r) - ∑ j ∈ Finset.Ico ⌊(W:ℝ) * s⌋₊ ⌊(W:ℝ) * (s + v)⌋₊,
        g j / (W:ℂ)‖
      ≤ C * (2 + 2 * np) / W := by
  -- `hv` is not needed (for `v < 0` both sides vanish); it is kept for the importing API.
  have _hv : 0 ≤ v := hv
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hC : 0 ≤ C := (norm_nonneg _).trans (hf 0)
  set h : ℝ → ℂ := fun r => g ⌊(W:ℝ) * (s + r)⌋₊ with h_def
  set a := ⌊(W:ℝ) * s⌋₊ with ha
  set b := ⌊(W:ℝ) * (s + v)⌋₊ with hb
  set A : Set ℝ := Ioc 0 v with hA
  set S : Set ℝ := ⋃ j ∈ Finset.Ico a b, cell W s j with hS
  set T : Set ℝ := ⋃ i, A ∩ cell W s (k i) with hT
  have hh : ∀ r, ‖h r‖ ≤ C := fun r => hg _
  have hhm : Measurable h :=
    measurable_from_nat.comp (Nat.measurable_floor.comp (by fun_prop))
  have intf : ∀ t : Set ℝ, volume t ≠ ⊤ → IntegrableOn f t := fun t ht =>
    Measure.integrableOn_of_bounded ht hfm.aestronglyMeasurable (Filter.Eventually.of_forall hf)
  have inth : ∀ t : Set ℝ, volume t ≠ ⊤ → IntegrableOn h t := fun t ht =>
    Measure.integrableOn_of_bounded ht hhm.aestronglyMeasurable (Filter.Eventually.of_forall hh)
  have hAfin : volume A ≠ ⊤ := measure_Ioc_lt_top.ne
  have hcellm : ∀ j, MeasurableSet (cell W s j) := fun j => measurableSet_Ico
  have hSm : MeasurableSet S := Finset.measurableSet_biUnion _ fun j _ => hcellm j
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun i => measurableSet_Ioc.inter (hcellm _)
  have hTfin : volume T ≠ ⊤ :=
    ((measure_mono (iUnion_subset fun i => inter_subset_left)).trans_lt
      measure_Ioc_lt_top).ne
  have hSint : IntegrableOn h S :=
    integrableOn_finset_iUnion.2 fun j _ => inth _ (volume_cell_ne_top _ _ _)
  -- nonnegativity of `W (s + r)` on `A`
  have hpos : ∀ r ∈ A, 0 ≤ (W:ℝ) * (s + r) := fun r hr => by
    have := hr.1; positivity
  -- Step 1: the sum is the integral of `h` over `S`.
  have step1 : ∫ r in S, h r = ∑ j ∈ Finset.Ico a b, g j / (W:ℂ) := by
    rw [integral_biUnion_finset _ (fun j _ => hcellm j)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [setIntegral_congr_fun (hcellm j) (g := fun _ => g j)
        (fun r hr => by simp only [h_def, floor_eq_of_mem_cell hW hr]),
        setIntegral_const, volume_real_cell hW, Complex.real_smul]
      push_cast
      field_simp
    · intro j _ j' _ hjj'
      refine Set.disjoint_left.2 fun r h1 h2 => hjj' ?_
      rw [← floor_eq_of_mem_cell hW h1, ← floor_eq_of_mem_cell hW h2]
    · exact fun j _ => inth _ (volume_cell_ne_top _ _ _)
  -- Step 2: `A \ S ⊆ cell b` and `S \ A ⊆ cell a`.
  have sub1 : A \ S ⊆ cell W s b := by
    intro r ⟨hrA, hrS⟩
    have h0 := hpos r hrA
    have hc := mem_cell_floor hW h0
    have hla : a ≤ ⌊(W:ℝ) * (s + r)⌋₊ :=
      Nat.floor_mono (by nlinarith [hrA.1])
    have hlb : ⌊(W:ℝ) * (s + r)⌋₊ ≤ b :=
      Nat.floor_mono (by nlinarith [hrA.2])
    rcases hlb.lt_or_eq with hlt | heq
    · exact absurd (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Ico.2 ⟨hla, hlt⟩)) hc) hrS
    · rwa [heq] at hc
  have sub2 : S \ A ⊆ cell W s a := by
    intro r ⟨hrS, hrA⟩
    simp only [hS, Set.mem_iUnion, Finset.mem_Ico] at hrS
    obtain ⟨j, ⟨hja, hjb⟩, hrj⟩ := hrS
    have hfl := floor_eq_of_mem_cell hW hrj
    have h0 : 0 ≤ (W:ℝ) * (s + r) := by
      have := hrj.1
      have : (0:ℝ) ≤ (j : ℝ) / W := by positivity
      nlinarith
    have hr : r ≤ 0 ∨ v < r := by
      by_contra hcon; push Not at hcon; exact hrA ⟨hcon.1, hcon.2⟩
    rcases hr with hr | hr
    · have : j ≤ a := by
        rw [← hfl]; exact Nat.floor_mono (by nlinarith)
      have hja' : j = a := le_antisymm this hja
      rw [← hja']; exact hrj
    · exfalso
      have : b ≤ j := by
        rw [← hfl]; exact Nat.floor_mono (by nlinarith)
      omega
  have bnd1 : ‖∫ r in A \ S, h r‖ ≤ C / W := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A \ S)
      ((measure_mono sub1).trans_lt (volume_cell_ne_top W s b).lt_top) (fun r _ => hh r)
    refine this.trans ?_
    rw [div_eq_mul_one_div, ← volume_real_cell hW s b]
    exact mul_le_mul_of_nonneg_left (measureReal_mono sub1
      (volume_cell_ne_top _ _ _)) hC
  have bnd2 : ‖∫ r in S \ A, h r‖ ≤ C / W := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := S \ A)
      ((measure_mono sub2).trans_lt (volume_cell_ne_top W s a).lt_top) (fun r _ => hh r)
    refine this.trans ?_
    rw [div_eq_mul_one_div, ← volume_real_cell hW s a]
    exact mul_le_mul_of_nonneg_left (measureReal_mono sub2
      (volume_cell_ne_top _ _ _)) hC
  -- Step 3: the mismatch `f - h` lives on `T`.
  have hAint : IntegrableOn (fun r => f r - h r) A :=
    (intf A hAfin).sub (inth A hAfin)
  have zero3 : ∫ r in A \ T, (f r - h r) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun r ⟨hrA, hrT⟩ => ?_
    have : f r = h r := by
      refine hfg r hrA.1.le fun i hi => hrT ?_
      refine Set.mem_iUnion.2 ⟨i, hrA, ?_⟩
      have := mem_cell_floor hW (hpos r hrA)
      rwa [hi] at this
    rw [this, sub_self]
  have bnd3 : ‖∫ r in A ∩ T, (f r - h r)‖ ≤ 2 * C * np / W := by
    have hAT : volume (A ∩ T) < ⊤ := (measure_mono inter_subset_left).trans_lt hAfin.lt_top
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A ∩ T) hAT
      (C := 2 * C) (fun r _ => (norm_sub_le (f r) (h r)).trans (by linarith [hf r, hh r]))
    refine this.trans ?_
    have hmT : volume.real (A ∩ T) ≤ np * (1 / W) := by
      calc volume.real (A ∩ T) ≤ volume.real T := measureReal_mono inter_subset_right hTfin
        _ ≤ ∑ i, volume.real (A ∩ cell W s (k i)) := measureReal_iUnion_fintype_le _
        _ ≤ ∑ _i : Fin np, (1 / (W:ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← volume_real_cell hW s (k i)]
          exact measureReal_mono inter_subset_right (volume_cell_ne_top _ _ _)
        _ = np * (1 / W) := by simp
    calc 2 * C * volume.real (A ∩ T) ≤ 2 * C * (np * (1 / W)) := by gcongr
      _ = 2 * C * np / W := by ring
  -- Assemble.
  have eA : ∫ r in A, f r = (∫ r in A, (f r - h r)) + ∫ r in A, h r := by
    rw [integral_sub (intf A hAfin) (inth A hAfin)]; ring
  have eAh := integral_inter_add_sdiff (μ := volume) (f := h) hSm (inth A hAfin)
  have eSh := integral_inter_add_sdiff (μ := volume) (f := h) (t := A) measurableSet_Ioc hSint
  have eT := integral_inter_add_sdiff (μ := volume) (f := fun r => f r - h r) hTm hAint
  rw [← step1, eA, ← eAh, ← eSh, ← eT, zero3, inter_comm S A]
  have key : (∫ r in A ∩ T, (f r - h r)) + 0 + ((∫ r in A ∩ S, h r) + ∫ r in A \ S, h r) -
      ((∫ r in A ∩ S, h r) + ∫ r in S \ A, h r) =
      (∫ r in A ∩ T, (f r - h r)) + (∫ r in A \ S, h r) - ∫ r in S \ A, h r := by ring
  rw [key]
  calc _ ≤ ‖(∫ r in A ∩ T, (f r - h r)) + (∫ r in A \ S, h r)‖ + ‖∫ r in S \ A, h r‖ :=
        norm_sub_le _ _
    _ ≤ ‖∫ r in A ∩ T, (f r - h r)‖ + ‖∫ r in A \ S, h r‖ + ‖∫ r in S \ A, h r‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ 2 * C * np / W + C / W + C / W := by gcongr
    _ = C * (2 + 2 * np) / W := by ring

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
