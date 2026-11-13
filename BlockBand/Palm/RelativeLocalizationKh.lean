module

public import BlockBand.Palm.RelativeLocalizationGenericHit
public import BlockBand.Palm.RelativeLocalizationHit
public import BlockBand.Palm.RelativeLocalizationWeightAny

/-!
# Relative localization: the closed stopping set with a centre, and the drift conditions

* `centreSet N ℓ E r₀ c₁ C₁ g ⊆ ℝ × ℝ^N` : `(c, λ)` with `λ` in the relaxed failure set, or a
  gap `≤ g`, or `3r₀/32 ≤ |c - E|`. Closed (`isClosed_centreSet`).
* `hcond_centreSet` : outside it, for the weight `rlPhi ν 0 d R` (any sign of `ν`,
  `d + 2R ≤ r₀/32`) and any generator field dominated by the short generator when all gaps
  exceed `g`, the three hypotheses of `gen_expectation_avoid` hold (relaxed constants
  `c₁/2`, `2C₁`).
* the truncated short generator: `truncShortGen_continuous`, `truncShortGen_isSubGenField`,
  `truncShortGen_eq` (equal to `shortGen` when all gaps are `≥ g`); the same facts for
  `truncRefGen` (`truncRefGen_isSubGenField`, domination `truncRefGen_dom`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open Set BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

/-- Closed stopping set with a centre coordinate. -/
def centreSet (N ℓ : ℕ) (E r₀ c₁ C₁ g : ℝ) : Set (ℝ × (Fin N → ℝ)) :=
  {p | p.2 ∈ failSet N ℓ E r₀ c₁ C₁ ∪ gapSet N g ∨ 3 * r₀ / 32 ≤ |p.1 - E|}

theorem isClosed_centreSet (N ℓ : ℕ) (E r₀ c₁ C₁ g : ℝ) :
    IsClosed (centreSet N ℓ E r₀ c₁ C₁ g) := by
  have h1 : IsClosed {p : ℝ × (Fin N → ℝ) | p.2 ∈ failSet N ℓ E r₀ c₁ C₁ ∪ gapSet N g} :=
    ((isClosed_failSet N ℓ E r₀ c₁ C₁).union (isClosed_gapSet N g)).preimage continuous_snd
  have h2 : IsClosed {p : ℝ × (Fin N → ℝ) | 3 * r₀ / 32 ≤ |p.1 - E|} :=
    isClosed_le continuous_const ((continuous_fst.sub continuous_const).abs)
  exact h1.union h2

theorem truncShortGen_continuous (ℓ : ℕ) {g : ℝ} (hg : 0 < g) :
    Continuous fun lam : Fin N → ℝ => truncShortGen N lam ℓ g := by
  classical
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; exact continuous_pi fun k => k.elim0
  have hr := continuous_truncRate hN hg
  have hd : ∀ k m : Fin N, Continuous fun lam : Fin N → ℝ => truncRate N g (lam k - lam m) :=
    fun k m => hr.comp ((continuous_apply k).sub (continuous_apply m))
  refine continuous_pi fun k => continuous_pi fun l => ?_
  unfold truncShortGen
  split_ifs
  · exact (continuous_finsetSum _ fun m _ => hd k m).neg
  · exact hd k l
  · exact continuous_const

theorem truncShortGen_isSubGenField (ℓ : ℕ) (g : ℝ) :
    IsSubGenField fun lam : Fin N → ℝ => truncShortGen N lam ℓ g := by
  classical
  intro lam
  refine ⟨fun k l hkl => ?_, fun k => (truncShortGen_rowSum lam ℓ g k).le⟩
  simp only [truncShortGen, hkl, ite_false]
  split_ifs
  · exact truncRate_nonneg _ _
  · exact le_rfl

theorem truncRefGen_isSubGenField (ℓ : ℕ) (b₀ g : ℝ) :
    IsSubGenField fun lam : Fin N → ℝ => truncRefGen N lam ℓ b₀ g := fun lam =>
  truncRefGen_isSubGenerator (fun _ => lam) ℓ b₀ g 0 2 1 ⟨by norm_num, by norm_num⟩

theorem truncShortGen_eq {lam : Fin N → ℝ} {ℓ : ℕ} {g : ℝ} (hg : 0 ≤ g)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) :
    truncShortGen N lam ℓ g = shortGen N lam ℓ := by
  classical
  have hrate : ∀ k m : Fin N, k ≠ m → truncRate N g (lam k - lam m) = pairRate N lam k m :=
    fun k m h => truncRate_eq (hgap k m h) hg
  funext k l
  unfold truncShortGen shortGen
  split_ifs with h1 h2
  · congr 1
    exact Finset.sum_congr rfl fun m hm => by
      simp only [Finset.mem_filter] at hm
      exact hrate k m (fun e => hm.2.1 e.symm)
  · exact hrate k l h1
  · rfl

/-- **Drift conditions outside the centre set.** -/
theorem hcond_centreSet {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} {ℓ : ℕ} {g : ℝ}
    (hGdom : ∀ lam : Fin N → ℝ, (∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) →
      ∀ v : Fin N → ℝ, (∀ k, 0 ≤ v k) → ∀ k,
        ∑ l, Gen lam k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l)
    {ν d R E r₀ c₁ C₁ : ℝ} (hR : 0 < R) (hρ : d + 2 * R ≤ r₀ / 32) (c : ℝ) (lam : Fin N → ℝ)
    (h : (c, lam) ∉ centreSet N ℓ E r₀ c₁ C₁ g) :
    (∀ v : Fin N → ℝ, (∀ k, 0 ≤ v k) → ∀ k,
        ∑ l, Gen lam k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l) ∧
      (∀ k l : Fin N, l ≠ k → labelDist k l < ℓ →
        |(lam l - c) - (lam k - c)| ≤ 2 * C₁ * ℓ / N ∨
          (rlPhi1 ν 0 d R (lam k - c) = 0 ∧ rlPhi ν 0 d R (lam l - c) = rlPhi ν 0 d R (lam k - c))) ∧
      (∀ k l : Fin N, l ≠ k → ℓ ≤ labelDist k l →
        c₁ / 2 * labelDist k l / N ≤ |lam k - lam l|) := by
  simp only [centreSet, Set.mem_ofPred_eq, Set.mem_union, not_or, not_le] at h
  obtain ⟨⟨hf, hgp⟩, hc⟩ := h
  obtain ⟨h1, h2⟩ := relaxed_of_not_mem_failSet hf
  have hgaps : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m| := by
    intro k m hkm
    by_contra hlt; push Not at hlt
    exact hgp ⟨k, m, hkm, hlt.le⟩
  refine ⟨hGdom lam hgaps, ?_, fun k l _ hkl => h1 k l hkl⟩
  have hρ' : d + 2 * R ≤ (r₀ / 4) / 8 := by linarith
  have := rlPhi_short_close_or_flat (ν := ν) (E := 0) (G := 2 * C₁ * ℓ / N) hR hρ'
    (fun i => lam i - c) ℓ (fun i j hij hm => by
      have hm' : min |lam i - E| |lam j - E| ≤ r₀ / 8 := by
        rcases le_total |lam i - c - 0| |lam j - c - 0| with hle | hle
        · rw [min_eq_left hle, sub_zero] at hm
          have : |lam i - E| ≤ |lam i - c| + |c - E| := abs_sub_le _ _ _
          exact (min_le_left _ _).trans (by linarith)
        · rw [min_eq_right hle, sub_zero] at hm
          have : |lam j - E| ≤ |lam j - c| + |c - E| := abs_sub_le _ _ _
          exact (min_le_right _ _).trans (by linarith)
      have := h2 i j hij hm'
      simpa only [sub_sub_sub_cancel_right] using this)
  intro k l hlk hkl
  simpa only [sub_zero] using this k l hlk hkl

theorem truncShortGen_dom {ℓ : ℕ} {g : ℝ} (hg : 0 ≤ g) (lam : Fin N → ℝ)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) (v : Fin N → ℝ) (_hv : ∀ k, 0 ≤ v k)
    (k : Fin N) :
    ∑ l, truncShortGen N lam ℓ g k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l := by
  rw [truncShortGen_eq hg hgap]

theorem truncRefGen_dom {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {b₀ g : ℝ} (hg : 0 ≤ g) (lam : Fin N → ℝ)
    (hgap : ∀ k m : Fin N, k ≠ m → g ≤ |lam k - lam m|) (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k)
    (k : Fin N) :
    ∑ l, truncRefGen N lam ℓ b₀ g k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l := by
  rw [truncRefGen_eq hℓ hg hgap]
  exact refGen_le_short lam ℓ b₀ hv k

end BlockBand.Palm.RelativeLocalization
