module

public import BlockBand.Palm.MomentFlow.MultiShort
public import BlockBand.Palm.RelativeLocalizationLabels

/-!
# `r`-particle finite speed: auxiliary facts for the asymptotic form

* `card_sector_le`: `#{ξ : Σ ξ_i = r} ≤ N^r` (every configuration is the occupation of a
  labelled `r`-tuple).
* `flowMatrix_isHermitian'`: the flow matrix is Hermitian when `F` and `ω.1` are.
* `labelDist_succ_le_count`: for a monotone spectrum, the upper count
  `#{λ_i ∈ [x,y]} ≤ C N((y-x)+h)` gives `|j-k| + 1 ≤ C N(|λ_j - λ_k| + h)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal ENNReal ComplexConjugate

variable {N : ℕ}

/-!
### Size of the sector
-/

/-- Occupation numbers of a labelled tuple. -/
def occOf {r : ℕ} (x : Fin r → Fin N) : Occ N := fun i => (univ.filter fun m => x m = i).card

theorem occOf_cons {r : ℕ} (i : Fin N) (x : Fin r → Fin N) (j : Fin N) :
    occOf (Fin.cons i x : Fin (r + 1) → Fin N) j = (if i = j then 1 else 0) + occOf x j := by
  classical
  simp only [occOf, Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp

theorem exists_occOf (r : ℕ) : ∀ ξ ∈ sector N r, ∃ x : Fin r → Fin N, occOf x = ξ := by
  classical
  induction r with
  | zero =>
    intro ξ hξ
    refine ⟨Fin.elim0, ?_⟩
    have h0 : ∀ i, ξ i = 0 := by
      intro i
      have := mem_sector.1 hξ
      exact (Finset.sum_eq_zero_iff.1 this) i (mem_univ i)
    funext i; simp [occOf, h0 i]
  | succ r ih =>
    intro ξ hξ
    have hsum := mem_sector.1 hξ
    obtain ⟨i, hi⟩ : ∃ i, 0 < ξ i := by
      by_contra h
      push Not at h
      have : ∑ i, ξ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
      omega
    have hrem : remove ξ i ∈ sector N r := by
      rw [mem_sector]
      have h1 : ∑ m, remove ξ i m + 1 = ∑ m, ξ m := by
        rw [← Finset.add_sum_erase _ _ (mem_univ i), ← Finset.add_sum_erase _ _ (mem_univ i)]
        rw [remove_apply_self]
        have : ∑ m ∈ univ.erase i, remove ξ i m = ∑ m ∈ univ.erase i, ξ m :=
          Finset.sum_congr rfl fun m hm => remove_apply_of_ne ξ (mem_erase.1 hm).1
        rw [this]; omega
      omega
    obtain ⟨x, hx⟩ := ih _ hrem
    refine ⟨Fin.cons i x, funext fun j => ?_⟩
    rw [occOf_cons, hx]
    by_cases hj : j = i
    · subst hj; simp [remove_apply_self]; omega
    · rw [ite_eq_right (Ne.symm hj), remove_apply_of_ne ξ hj, zero_add]

theorem card_sector_le (r : ℕ) : sectorCard N r ≤ N ^ r := by
  classical
  have hsub : sector N r ⊆ (univ : Finset (Fin r → Fin N)).image occOf := by
    intro ξ hξ
    obtain ⟨x, hx⟩ := exists_occOf r ξ hξ
    exact Finset.mem_image.2 ⟨x, mem_univ _, hx⟩
  calc sectorCard N r ≤ ((univ : Finset (Fin r → Fin N)).image occOf).card :=
        Finset.card_le_card hsub
    _ ≤ (univ : Finset (Fin r → Fin N)).card := Finset.card_image_le
    _ = N ^ r := by simp

/-!
### Hermitian flow matrices and the counting bound
-/

theorem hermitianBrownian_isHermitian' (B : FlowNoise N) (t : ℝ) :
    (hermitianBrownian B t).IsHermitian := by
  ext a b
  simp only [hermitianBrownian, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
    map_mul, map_add, Complex.conj_conj, map_inv₀, Complex.conj_ofReal]
  ring

theorem flowMatrix_isHermitian' {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian :=
  (hF.add hω).add (hermitianBrownian_isHermitian' _ _)

theorem labelDist_eq_of_le {k j : Fin N} (h : k ≤ j) : (labelDist k j : ℝ) = (j : ℝ) - k := by
  unfold labelDist
  have : ((k : ℤ) - (j : ℤ)).natAbs = (j : ℕ) - (k : ℕ) := by
    have : (k : ℕ) ≤ j := h
    omega
  rw [this, Nat.cast_sub (show (k : ℕ) ≤ j from h)]

/-- **Upper count ⇒ separation**: `|j - k| + 1 ≤ C N (|λ_j - λ_k| + h)`. -/
theorem labelDist_succ_le_count {lam : Fin N → ℝ} (hmono : Monotone lam) {C h : ℝ}
    (hcount : ∀ x y : ℝ, x ≤ y →
      ((univ.filter fun i : Fin N => lam i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h))
    (k j : Fin N) : (labelDist k j : ℝ) + 1 ≤ C * N * (|lam j - lam k| + h) := by
  classical
  wlog hkj : k ≤ j generalizing k j
  · have := this j k (le_of_not_ge hkj)
    rwa [labelDist_symm, abs_sub_comm] at this
  have hsub : Finset.Icc k j ⊆ univ.filter fun i : Fin N => lam i ∈ Set.Icc (lam k) (lam j) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hmono hi.1, hmono hi.2⟩
  have hcard : ((Finset.Icc k j).card : ℝ) = labelDist k j + 1 := by
    rw [Fin.card_Icc, labelDist_eq_of_le hkj]
    have : (k : ℕ) ≤ j + 1 := by have : (k : ℕ) ≤ j := hkj; omega
    rw [Nat.cast_sub this]; push_cast; ring
  have h1 := (Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hsub)
  have h2 := hcount (lam k) (lam j) (hmono hkj)
  rw [abs_of_nonneg (sub_nonneg.2 (hmono hkj))]
  linarith

/-!
### Small gaps on a window after a positive start
-/

/-- Some gap of `λ(s+x)`, `x ≤ T`, is `≤ g`. -/
def gapWin (F : Matrix (Fin N) (Fin N) ℂ) (sL T : ℝ≥0) (g : ℝ) : Set (FlowSample N) :=
  {ω | ∃ x : ℝ≥0, x ≤ T ∧ flowLam F (sL + x) ω ∈ gapSet N g}

/-- The pair `(i,j)` comes within `g` on the window. -/
def pairWin (F : Matrix (Fin N) (Fin N) ℂ) (sL T : ℝ≥0) (i j : Fin N) (g : ℝ) :
    Set (FlowSample N) :=
  {ω | ∃ x : ℝ≥0, x ≤ T ∧ |flowLam F (sL + x) ω i - flowLam F (sL + x) ω j| ≤ g}

theorem measurableSet_pairWin {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    (sL T : ℝ≥0) (i j : Fin N) (g : ℝ) : MeasurableSet (pairWin F sL T i j g) := by
  have hK : IsClosed {lam : Fin N → ℝ | |lam i - lam j| ≤ g} :=
    isClosed_le (((continuous_apply i).sub (continuous_apply j)).abs) continuous_const
  have hc : ∀ ω, Continuous fun x : ℝ≥0 => flowLam F (sL + x) ω := fun ω =>
    (flowLam_continuous hF ω).comp (continuous_const.add continuous_id)
  have hst := isStoppingTime_hitTime (shiftFiltration (flowFiltration N) sL)
    (fun x ω => flowLam F (sL + x) ω) (fun x => flowLam_adapted F (sL + x)) hc hK T
  have : pairWin F sL T i j g = {ω | hitTime (fun x ω => flowLam F (sL + x) ω)
      {lam : Fin N → ℝ | |lam i - lam j| ≤ g} ω ≤ T} := by
    ext ω
    rw [Set.mem_ofPred_eq, hitTime_le_iff (hc ω) hK]
    rfl
  rw [this]; exact (shiftFiltration (flowFiltration N) sL).le T _ hst

theorem gapWin_subset (F : Matrix (Fin N) (Fin N) ℂ) (sL T : ℝ≥0) (g : ℝ) :
    gapWin F sL T g ⊆ ⋃ p : {p : Fin N × Fin N // p.1 ≠ p.2}, pairWin F sL T p.1.1 p.1.2 g := by
  rintro ω ⟨x, hx, i, j, hij, hg⟩
  exact Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, x, hx, hg⟩

theorem collision_win_null (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) {sL : ℝ≥0} (hsL : 0 < sL) (T : ℝ≥0) {i j : Fin N}
    (hij : i ≠ j) :
    flowLaw N a (⋂ n : ℕ, pairWin F sL T i j (1 / ((n : ℝ) + 1))) = 0 := by
  refine measure_mono_null (fun ω hω => ?_) ((ae_fst_isHermitian (N := N) a).and
    (flow_simpleSpectrum hDBM hF a) |> fun h => (ae_iff.mp h))
  simp only [Set.mem_ofPred_eq, not_and_or, not_forall]
  by_contra hcon
  push Not at hcon
  obtain ⟨hH, hsimp⟩ := hcon
  set f : ℝ≥0 → ℝ := fun x => |flowLam F (sL + x) ω i - flowLam F (sL + x) ω j|
  have hfc : Continuous f := ((((continuous_apply i).comp (flowLam_continuous hF ω)).sub
    ((continuous_apply j).comp (flowLam_continuous hF ω))).abs).comp
      (continuous_const.add continuous_id)
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_isMinOn
    ⟨0, ⟨le_rfl, zero_le (a := T)⟩⟩ hfc.continuousOn
  have hf0 : f x = 0 := by
    refine le_antisymm ?_ (abs_nonneg _)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨y, hy, hgy⟩ := Set.mem_iInter.mp hω n
    have h1 : f x ≤ f y := hmin ⟨zero_le (a := y), hy⟩
    have h2 : f y ≤ 1 / ((n : ℝ) + 1) := hgy
    linarith
  have hσ : a < a + ((sL + x : ℝ≥0) : ℝ) := by
    have : (0 : ℝ) < sL := hsL
    have := NNReal.coe_nonneg x
    push_cast; linarith
  have hs := hsimp _ hσ
  simp only [f] at hf0
  rw [flowLam_add_eq_eig F a hH] at hf0
  simp only [flowEigenvalue] at hf0
  have hHerm := flowMatrix_isHermitian' hF a hH (a + ((sL + x : ℝ≥0) : ℝ))
  rw [freshEigenvalue_eq_dyson hHerm, freshEigenvalue_eq_dyson hHerm, abs_eq_zero,
    sub_eq_zero] at hf0
  exact hij (Fin.rev_injective (hs.injective hf0))

/-- **Vanishing small-gap probability on the window** (start `sL > 0`). -/
theorem tendsto_gapWin (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (a : ℝ) {sL : ℝ≥0} (hsL : 0 < sL) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => flowLaw N a (gapWin F sL T (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have hpair : ∀ p : {p : Fin N × Fin N // p.1 ≠ p.2},
      Tendsto (fun n : ℕ => flowLaw N a (pairWin F sL T p.1.1 p.1.2 (1 / ((n : ℝ) + 1))))
        atTop (𝓝 0) := by
    intro p
    have h := tendsto_measure_iInter_atTop (μ := flowLaw N a)
      (s := fun n : ℕ => pairWin F sL T p.1.1 p.1.2 (1 / ((n : ℝ) + 1)))
      (fun n => (measurableSet_pairWin hF sL T _ _ _).nullMeasurableSet)
      (fun m n hmn ω hω => by
        obtain ⟨y, hy, hg⟩ := hω
        exact ⟨y, hy, hg.trans (by gcongr)⟩) ⟨0, measure_ne_top _ _⟩
    rwa [collision_win_null hDBM hF a hsL T p.2] at h
  have hsum : Tendsto (fun n : ℕ => ∑ p : {p : Fin N × Fin N // p.1 ≠ p.2},
      flowLaw N a (pairWin F sL T p.1.1 p.1.2 (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ) fun p _ => hpair p
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
    fun n => ?_
  exact (measure_mono (gapWin_subset F sL T _)).trans (measure_iUnion_fintype_le _ _)

end BlockBand.Palm.MomentFlow
