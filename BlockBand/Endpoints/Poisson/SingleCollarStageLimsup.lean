module

public import BlockBand.Endpoints.Response.RemoteHigher

/-!
# From `W`-indexed limsup bounds to eventual bounds along a critical sequence

`RemoteHigherUniformStatement` is a `limsup` over the width `W ∈ ℕ` along *every* admissible
sequence of energies `e_W` (`|e_W - E| ≤ K/W²`) and lengths `n_W` (`n_W/W → τ`). The stage
estimate is indexed by a critical sequence `j ↦ W_j → ∞` (not injective in general) and needs a
bound uniform over the energies of the window at each `j`. Measure-free; `ℝ≥0∞`-valued.

* `scs_eventually_le_of_limsup`: the uniform `limsup` bound gives, for every `ε > 0`, eventually
  in `j`, the bound `B + ε` at every admissible energy of width `W_j` (contradiction: a bad
  energy for infinitely many `j` is assembled into one admissible `W`-sequence whose `limsup` is
  at least `B + ε`).
* `scs_eventually_of_subseq`: the subsequence principle (an eventual statement holds if every
  subsequence has a further subsequence along which it holds frequently), used with
  Bolzano–Weierstrass for the component lengths.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open Filter Topology
open scoped ENNReal

/-- **The subsequence principle.** If every subsequence `φ` has a further subsequence `ψ` along
which `P` holds frequently, then `P` holds eventually. -/
theorem scs_eventually_of_subseq {P : ℕ → Prop}
    (H : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ᶠ l in atTop, P (φ (ψ l))) :
    ∀ᶠ j in atTop, P j := by
  by_contra h
  rw [not_eventually] at h
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop h
  obtain ⟨ψ, -, hfr⟩ := H φ hφ
  obtain ⟨l, hl⟩ := hfr.exists
  exact hP (ψ l) hl

/-- **`W`-indexed `limsup` to `j`-indexed eventual bounds, uniformly in the window.**
Let `G W e n ∈ ℝ≥0∞` and suppose `limsup_W G(W, e_W, n_W) ≤ B < ∞` for every sequence of energies
with eventually `|e_W - E| ≤ K/W²` and every sequence of lengths with `n_W/W → τ`. Then for every
`j`-indexed `W_j → ∞`, `n_j/W_j → τ` and `ε > 0`, eventually in `j`, `G(W_j, e, n_j) ≤ B + ε`
for every `e` with `|e - E| ≤ K/W_j²`. -/
theorem scs_eventually_le_of_limsup {G : ℕ → ℝ → ℕ → ℝ≥0∞} {E K τ : ℝ} (hK : 0 ≤ K)
    (hτ : 0 ≤ τ) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (h : ∀ (e : ℕ → ℝ) (n : ℕ → ℕ), (∀ᶠ W : ℕ in atTop, |e W - E| ≤ K / (W : ℝ) ^ 2) →
      Tendsto (fun W : ℕ => (n W : ℝ) / W) atTop (𝓝 τ) →
      limsup (fun W : ℕ => G W (e W) (n W)) atTop ≤ B)
    {Wj nj : ℕ → ℕ} (hW : Tendsto Wj atTop atTop)
    (hn : Tendsto (fun j => (nj j : ℝ) / (Wj j : ℝ)) atTop (𝓝 τ)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ e' : ℝ, |e' - E| ≤ K / (Wj j : ℝ) ^ 2 → G (Wj j) e' (nj j) ≤ B + ε := by
  classical
  by_contra hcon
  rw [not_eventually] at hcon
  set J : Set ℕ := {j | ∃ e', |e' - E| ≤ K / (Wj j : ℝ) ^ 2 ∧ B + ε < G (Wj j) e' (nj j)}
  have hJ : ∃ᶠ j in atTop, j ∈ J := hcon.mono fun j hj => by
    push Not at hj
    obtain ⟨e', h1, h2⟩ := hj
    exact ⟨e', h1, h2⟩
  -- a bad index of width `W`, when there is one
  set A : ℕ → Prop := fun W => ∃ j ∈ J, Wj j = W
  have hsel : ∀ W, ∃ q : ℕ × ℝ, A W →
      Wj q.1 = W ∧ |q.2 - E| ≤ K / (W : ℝ) ^ 2 ∧ B + ε < G W q.2 (nj q.1) := by
    intro W
    by_cases hA : A W
    · obtain ⟨j, ⟨e', h1, h2⟩, rfl⟩ := hA
      exact ⟨(j, e'), fun _ => ⟨rfl, h1, h2⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hA⟩
  choose f hf using hsel
  set eW : ℕ → ℝ := fun W => if A W then (f W).2 else E
  set nW : ℕ → ℕ := fun W => if A W then nj (f W).1 else ⌊(W : ℝ) * τ⌋₊
  have he : ∀ᶠ W : ℕ in atTop, |eW W - E| ≤ K / (W : ℝ) ^ 2 := Eventually.of_forall fun W => by
    by_cases hA : A W
    · simp only [eW, hA, ite_true]; exact (hf W hA).2.1
    · simp only [eW, hA, ite_false, sub_self, abs_zero]; positivity
  have hnW : Tendsto (fun W : ℕ => (nW W : ℝ) / W) atTop (𝓝 τ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨j₀, hj₀⟩ := Metric.tendsto_atTop.mp hn δ hδ
    obtain ⟨W₂, hW₂⟩ := Metric.tendsto_atTop.mp (rh_tendsto_floor_div hτ) δ hδ
    set W₁ := (Finset.range j₀).sup Wj + 1
    refine ⟨max W₁ W₂, fun W hWge => ?_⟩
    by_cases hA : A W
    · simp only [nW, hA, ite_true]
      obtain ⟨hWf, -, -⟩ := hf W hA
      have hj : j₀ ≤ (f W).1 := by
        by_contra hlt
        push Not at hlt
        have h1 : Wj (f W).1 ≤ (Finset.range j₀).sup Wj :=
          Finset.le_sup (f := Wj) (Finset.mem_range.mpr hlt)
        have h2 : W₁ ≤ W := le_trans (le_max_left _ _) hWge
        omega
      have := hj₀ _ hj
      rwa [hWf] at this
    · simp only [nW, hA, ite_false]
      exact hW₂ W (le_trans (le_max_right _ _) hWge)
  have hfreq : ∃ᶠ W : ℕ in atTop, B + ε ≤ G W (eW W) (nW W) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨j, hjJ, hjN⟩ := (hJ.and_eventually (hW.eventually_ge_atTop N)).exists
    have hA : A (Wj j) := ⟨j, hjJ, rfl⟩
    refine ⟨Wj j, hjN, ?_⟩
    simp only [eW, nW, hA, ite_true]
    exact (hf (Wj j) hA).2.2.le
  have hle : B + ε ≤ limsup (fun W : ℕ => G W (eW W) (nW W)) atTop :=
    le_limsup_of_frequently_le hfreq
  have := hle.trans (h eW nW he hnW)
  exact absurd this (not_le.mpr (ENNReal.lt_add_right hB hε.ne'))

end BlockBand.Endpoints
