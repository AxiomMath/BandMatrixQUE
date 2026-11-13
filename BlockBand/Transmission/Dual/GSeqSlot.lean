module

public import BlockBand.Transmission.Dual.GSeqBad

/-!
# The corner case of the boundary classification, deterministic part

Level `p = q + 2`; the combined nested sequence `ŵ` (over an exhaustion `W` of `𝒞_p`) is built
from a pair sequence `û` (over `W₁`, exhausting `𝒞₁`) and a rest sequence `ŷ` (over `W₂`,
exhausting `𝒞_{p-1}`) by the slot relation `SlotRel`: up to `ρ_n(ŵ)` the `n`-th combined path is
`slotJoin j` of the `n`-th factor paths, and `ρ_n(ŵ) ≤ ρ_n(û) ∧ ρ_n(ŷ)`. Assume the corner limit
for `û` and the boundary classification at level `p − 1` for `ŷ`, both as membership in
`goodSeq`. If `ρ_∞(ŵ) < t₀`:
* **`SlotRel.mem_llSet`**: the combined left limit exists (no atomlessness needed);
* **`SlotRel.corner_or_coll`**: unless `ζ_pair = ζ' < t₀` (`ζ = ρ_∞` of the factor), the left
  limit is a corner or a positive-height collision.
So `ŵ ∉ badLim`, and `ŵ ∈ badCorner` forces `ζ_pair = ζ' < t₀` (`SlotRel.notMem_badLim`,
`SlotRel.eq_of_mem_badCorner`). The cases: the factors are continuous at `ρ_∞` before their own
lifetimes; a pair dying alone at `ρ_∞` is a corner (`j = 0`) or contradicts the order
(`j ≠ 0`); a rest dying alone contradicts `x₀ ≤ x₁`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {t₀ : ℝ≥0}

/-- The limit of one factor at a time `ρ ≤ ζ` of the factor. -/
theorem exists_factor_lim {W' : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}
    (hE : IsExh W' (flatChamber (q + 1))) {ŷ : ℕ → CPath ((q + 1) + (q + 1))}
    (hn : IsNested W' t₀ ŷ) (h0 : (ŷ 0).1 0 ∈ W' 0) (hG : ŷ ∈ goodSeq q W' t₀) {ρ : ℝ≥0}
    (hρ : ρ ≤ sinf W' t₀ ŷ) (hρt : ρ < t₀) :
    ∃ c, Tendsto (sglue ŷ) (𝓝[<] ρ) (𝓝 c) ∧ (ρ < sinf W' t₀ ŷ → c ∈ flatChamber (q + 1)) ∧
      (ρ = sinf W' t₀ ŷ → IsCorner q c) := by
  rcases lt_or_eq_of_le hρ with hlt | heq
  · refine ⟨sglue ŷ ρ, (hn.tendsto_sglue_of_lt hE.isOpen hlt).mono_left nhdsWithin_le_nhds,
      fun _ => ?_, fun h => absurd h hlt.ne⟩
    obtain ⟨m, hm⟩ := hn.sglue_mem hE.isOpen hlt
    exact (hE.dom m).2.2 (subset_closure hm)
  · have hst : sinf W' t₀ ŷ < t₀ := heq ▸ hρt
    obtain ⟨hl, hc⟩ := hG hst
    obtain ⟨c, hL⟩ := mem_llSet_iff.1 hl
    rw [hL.zstar_eq] at hc
    refine ⟨c, ?_, fun h => absurd heq h.ne, fun _ => hc⟩
    rw [heq]
    exact (hn.tendsto_sglue_iff hE.isOpen hE.mono (hn.srho_lt_sinf hE h0 hst) c).2 hL

theorem exists_eq_of_not_strictMono {n : ℕ} {f : Fin n → ℝ} (hm : ∀ i k, i ≤ k → f i ≤ f k)
    (hs : ¬StrictMono f) : ∃ i k, i < k ∧ f i = f k := by
  simp only [StrictMono, not_forall, not_lt] at hs
  obtain ⟨i, k, hik, h⟩ := hs
  exact ⟨i, k, hik, le_antisymm (hm i k hik.le) h⟩

variable {W : ℕ → Set (Fin (((q + 1) + 1) + ((q + 1) + 1)) → ℝ)} {W₁ : ℕ → Set (Fin (1 + 1) → ℝ)}
  {W₂ : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}

/-- The slot relation between a combined nested sequence and its pair and rest sequences. -/
structure SlotRel (W : ℕ → Set (Fin (((q + 1) + 1) + ((q + 1) + 1)) → ℝ))
    (W₁ : ℕ → Set (Fin (1 + 1) → ℝ)) (W₂ : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)) (t₀ : ℝ≥0)
    (j : Fin ((q + 1) + 1)) (ŵ : ℕ → CPath (((q + 1) + 1) + ((q + 1) + 1)))
    (û : ℕ → CPath (1 + 1)) (ŷ : ℕ → CPath ((q + 1) + (q + 1))) : Prop where
  nest : IsNested W t₀ ŵ
  nest₁ : IsNested W₁ t₀ û
  nest₂ : IsNested W₂ t₀ ŷ
  start : (ŵ 0).1 0 ∈ W 0
  start₁ : (û 0).1 0 ∈ W₁ 0
  start₂ : (ŷ 0).1 0 ∈ W₂ 0
  eq : ∀ n t, t ≤ srho W t₀ ŵ n → (ŵ n).1 t = slotJoin j ((û n).1 t) ((ŷ n).1 t)
  le₁ : ∀ n, srho W t₀ ŵ n ≤ srho W₁ t₀ û n
  le₂ : ∀ n, srho W t₀ ŵ n ≤ srho W₂ t₀ ŷ n

namespace SlotRel

variable {j : Fin ((q + 1) + 1)} {ŵ : ℕ → CPath (((q + 1) + 1) + ((q + 1) + 1))}
  {û : ℕ → CPath (1 + 1)} {ŷ : ℕ → CPath ((q + 1) + (q + 1))}
  (hR : SlotRel W W₁ W₂ t₀ j ŵ û ŷ) (hE : IsExh W (flatChamber ((q + 1) + 1)))
  (hE₁ : IsExh W₁ (flatChamber 1)) (hE₂ : IsExh W₂ (flatChamber (q + 1)))
  (hP : û ∈ goodSeq 0 W₁ t₀) (hG : ŷ ∈ goodSeq q W₂ t₀)
include hR hE hE₁ hE₂ hP hG

omit hE hE₁ hE₂ hP hG in
theorem sinf_le₁ : sinf W t₀ ŵ ≤ sinf W₁ t₀ û :=
  ciSup_le fun n => (hR.le₁ n).trans (srho_le_sinf û n)

omit hE hE₁ hE₂ hP hG in
theorem sinf_le₂ : sinf W t₀ ŵ ≤ sinf W₂ t₀ ŷ :=
  ciSup_le fun n => (hR.le₂ n).trans (srho_le_sinf ŷ n)

omit hP hG in
theorem sglue_eq_slotJoin {t : ℝ≥0} (ht : t < sinf W t₀ ŵ) :
    sglue ŵ t = slotJoin j (sglue û t) (sglue ŷ t) := by
  obtain ⟨n, hn⟩ := exists_lt_srho ht
  rw [hR.nest.sglue_eq hE.isOpen hn.le, hR.eq n t hn.le,
    hR.nest₁.sglue_eq hE₁.isOpen (hn.le.trans (hR.le₁ n)),
    hR.nest₂.sglue_eq hE₂.isOpen (hn.le.trans (hR.le₂ n))]

/-- The combined left limit, with the factor information. -/
theorem exists_LL (hlt : sinf W t₀ ŵ < t₀) :
    ∃ c₁ c₂, LL W t₀ ŵ (slotJoin j c₁ c₂) ∧
      (sinf W t₀ ŵ < sinf W₁ t₀ û → c₁ ∈ flatChamber 1) ∧
      (sinf W t₀ ŵ = sinf W₁ t₀ û → IsCorner 0 c₁) ∧
      (sinf W t₀ ŵ < sinf W₂ t₀ ŷ → c₂ ∈ flatChamber (q + 1)) ∧
      (sinf W t₀ ŵ = sinf W₂ t₀ ŷ → IsCorner q c₂) := by
  obtain ⟨c₁, hT₁, hc₁, hd₁⟩ := exists_factor_lim (q := 0) hE₁ hR.nest₁ hR.start₁ hP
    (hR.sinf_le₁) hlt
  obtain ⟨c₂, hT₂, hc₂, hd₂⟩ := exists_factor_lim hE₂ hR.nest₂ hR.start₂ hG
    (hR.sinf_le₂) hlt
  refine ⟨c₁, c₂, ?_, hc₁, hd₁, hc₂, hd₂⟩
  have hJ : Tendsto (fun t => slotJoin j (sglue û t) (sglue ŷ t)) (𝓝[<] sinf W t₀ ŵ)
      (𝓝 (slotJoin j c₁ c₂)) :=
    ((continuous_slotJoin j).tendsto (c₁, c₂)).comp (hT₁.prodMk_nhds hT₂)
  have hT : Tendsto (sglue ŵ) (𝓝[<] sinf W t₀ ŵ) (𝓝 (slotJoin j c₁ c₂)) := by
    refine hJ.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hR.sglue_eq_slotJoin hE hE₁ hE₂ ht).symm
  exact (hR.nest.tendsto_sglue_iff hE.isOpen hE.mono
    (hR.nest.srho_lt_sinf hE hR.start hlt) _).1 hT

/-- **The combined left limit exists before `t₀`** (no atomlessness needed). -/
theorem mem_llSet (hlt : sinf W t₀ ŵ < t₀) : ŵ ∈ llSet W t₀ := by
  obtain ⟨c₁, c₂, hL, -⟩ := hR.exists_LL hE hE₁ hE₂ hP hG hlt
  exact mem_llSet_iff.2 ⟨_, hL⟩

/-- **The case list**: unless both factors die together before `t₀`, the left limit
is a corner or a positive-height collision. -/
theorem corner_or_coll (hlt : sinf W t₀ ŵ < t₀)
    (hne : ¬(sinf W₁ t₀ û = sinf W₂ t₀ ŷ ∧ sinf W₁ t₀ û < t₀)) :
    IsCorner (q + 1) (zstar t₀ ŵ) ∨ PosColl (q + 1) (zstar t₀ ŵ) := by
  obtain ⟨c₁, c₂, hL, hc₁, hd₁, hc₂, hd₂⟩ := hR.exists_LL hE hE₁ hE₂ hP hG hlt
  rw [hL.zstar_eq]
  set c := slotJoin j c₁ c₂ with hcdef
  have hcl := hR.nest.LL_mem_closure hE hR.start hlt hL
  have hnot := hR.nest.LL_notMem hE hlt hL
  obtain ⟨hmx, hmy⟩ := mono_of_mem_closure hcl
  have hP' := pairOf_slotJoin j c₁ c₂
  have hR' := restOf_slotJoin j c₁ c₂
  rw [← hcdef] at hP' hR'
  -- coordinates of `c`
  have ex0 : (ofFlat ((q + 1) + 1) c).1 0 = (ofFlat 1 c₁).1 0 := congrArg (fun z => z.1 0) hP'
  have eyj : (ofFlat ((q + 1) + 1) c).2 j = (ofFlat 1 c₁).2 0 := congrArg (fun z => z.2 0) hP'
  have exs : ∀ i, (ofFlat ((q + 1) + 1) c).1 i.succ = (ofFlat (q + 1) c₂).1 i := fun i =>
    congrArg (fun z => z.1 i) hR'
  have eys : ∀ l, (ofFlat ((q + 1) + 1) c).2 (j.succAbove l) = (ofFlat (q + 1) c₂).2 l := fun l =>
    congrArg (fun z => z.2 l) hR'
  have hρ₁ := hR.sinf_le₁
  have hρ₂ := hR.sinf_le₂
  rcases lt_or_eq_of_le hρ₁ with h₁ | h₁ <;> rcases lt_or_eq_of_le hρ₂ with h₂ | h₂
  · -- both factors alive: a positive-height collision
    have p₁ := hc₁ h₁
    have p₂ := hc₂ h₂
    have hx : ∀ k, 0 < (ofFlat ((q + 1) + 1) c).1 k := fun k => by
      induction k using Fin.cases with
      | zero => rw [ex0]; exact p₁.2.2.1 0
      | succ i => rw [exs]; exact p₂.2.2.1 i
    have hy : ∀ k, 0 < (ofFlat ((q + 1) + 1) c).2 k ∧ (ofFlat ((q + 1) + 1) c).2 k < 1 := fun k => by
      rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨l, rfl⟩
      · rw [eyj]; exact p₁.2.2.2 0
      · rw [eys]; exact p₂.2.2.2 l
    refine Or.inr ⟨add_pos (hx 0) (hy 0).1, ?_⟩
    by_contra hno
    simp only [not_or, not_exists, not_and] at hno
    refine hnot ⟨?_, ?_, hx, hy⟩
    · by_contra hs
      obtain ⟨i, k, hik, he⟩ := exists_eq_of_not_strictMono hmx hs
      exact hno.1 i k hik he
    · by_contra hs
      obtain ⟨i, k, hik, he⟩ := exists_eq_of_not_strictMono hmy hs
      exact hno.2 i k hik he
  · -- the rest dies alone: contradicts `x₀ ≤ x₁`
    exfalso
    have p₁ := hc₁ h₁
    have hcor := hd₂ h₂
    have h01 := hmx 0 (Fin.succ 0) (Fin.zero_le _)
    rw [ex0, exs, hcor.1] at h01
    exact absurd h01 (not_le.2 (p₁.2.2.1 0))
  · -- the pair dies alone: a corner if `j = 0`, impossible otherwise
    have p₂ := hc₂ h₂
    have hcor := hd₁ h₁
    by_cases hj : j = 0
    · subst hj
      refine Or.inl ⟨by rw [ex0]; exact hcor.1, by rw [eyj]; exact hcor.2.1, ?_⟩
      rw [hcdef, slotJoin_comp_symm]
      have : rightPart (Fin.append c₁ c₂) = c₂ := funext fun i => Fin.append_right c₁ c₂ i
      rw [this]; exact p₂
    · exfalso
      have h0j := hmy 0 j (Fin.zero_le _)
      rw [← Fin.succAbove_ne_zero_zero hj, eys, eyj, hcor.2.1] at h0j
      exact absurd h0j (not_le.2 (p₂.2.2.2 0).1)
  · exact absurd ⟨h₁.symm.trans h₂, h₁ ▸ hlt⟩ hne

/-- `ŵ ∉ badLim` under the slot relation. -/
theorem notMem_badLim : ŵ ∉ badLim (q + 1) W t₀ := fun h =>
  h.2 (hR.mem_llSet hE hE₁ hE₂ hP hG h.1)

/-- `ŵ ∈ badCorner` forces the two factor lifetimes to coincide before `t₀`. -/
theorem eq_of_mem_badCorner (h : ŵ ∈ badCorner (q + 1) W t₀) :
    sinf W₁ t₀ û = sinf W₂ t₀ ŷ ∧ sinf W₁ t₀ û < t₀ := by
  by_contra hne
  rcases hR.corner_or_coll hE hE₁ hE₂ hP hG h.1 hne with h' | h'
  · exact h.2.2.1 h'
  · exact h.2.2.2 h'

end SlotRel

end BlockBand.Transmission.Dual.G
