module

public import BlockBand.Palm.MomentFlow.FlowRates
public import BlockBand.Palm.MomentFlow.BridgeIdentity
public import BlockBand.Palm.RelativeLocalizationExist

/-!
# Existence of one-particle short moment-flow solutions on collision-free paths

* `eq_single_of_mem_sector_one`: every one-particle configuration is some `δ_k`.
* `isMomentFlowSolution_of_forwardMassSolution`: a solution `v` of the forward mass equation of
  `shortGenerator` gives the sector-1 short moment-flow solution `Φ(x, ξ) = Σ_k ξ_k v_k(x)` with
  `Φ(x, δ_k) = v_k(x)` (converse of `forwardMassSolution_of_momentFlow`).
* `continuousOn_shortGenerator`: if the short gaps do not vanish on `[s, u]` (for instance
  simple spectrum at every time), `x ↦ shortGenerator F a ω ℓ x` is continuous on `[s, u]`
  (eigenvalue paths are continuous for every sample, `continuous_flowEigenvalue`).
* **`exists_shortMomentFlow_one`**: on such a path, for every initial datum `v₀` there is a
  sector-1 short moment-flow solution `Φ` on `[s, u]` with `Φ(s, δ_j) = v₀_j`
  (`forwardMass_exists`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem eq_single_of_mem_sector_one {ξ : Occ N} (hξ : ξ ∈ sector N 1) :
    ∃ k : Fin N, ξ = Pi.single k 1 := by
  classical
  rw [mem_sector] at hξ
  have hex : ∃ k, ξ k ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at hξ
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, funext fun i => ?_⟩
  have hle : ∀ j, ξ j ≤ 1 := fun j => hξ ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)
  by_cases hik : i = k
  · subst hik; simp only [Pi.single_eq_same]; have := hle i; omega
  · rw [Pi.single_eq_of_ne hik]
    have h2 : ξ i + ξ k ≤ ∑ j, ξ j := by
      rw [← Finset.sum_pair hik]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

/-- The linear extension of a one-particle mass profile to configurations. -/
def massExt (v : ℝ → Fin N → ℝ) (x : ℝ) (ξ : Occ N) : ℝ := ∑ k, (ξ k : ℝ) * v x k

theorem massExt_single (v : ℝ → Fin N → ℝ) (x : ℝ) (j : Fin N) :
    massExt v x (Pi.single j 1) = v x j := by
  classical
  unfold massExt
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

/-- A forward mass solution of `shortGenerator` is a sector-1
short moment-flow solution. -/
theorem isMomentFlowSolution_of_forwardMassSolution (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) {s u : ℝ} {v₀ : Fin N → ℝ} {v : ℝ → Fin N → ℝ}
    (hv : ForwardMassSolution (shortGenerator F a ω ℓ) s u v₀ v) :
    IsMomentFlowSolution (shortFlowRate F a ω ℓ) 1 s u (massExt v) ∧
      ∀ j : Fin N, massExt v s (Pi.single j 1) = v₀ j := by
  obtain ⟨h0, hc, hd⟩ := hv
  refine ⟨fun ξ hξ => ?_, fun j => by rw [massExt_single, h0]⟩
  obtain ⟨k, rfl⟩ := eq_single_of_mem_sector_one hξ
  have e : (fun x => massExt v x (Pi.single k 1)) = fun x => v x k :=
    funext fun x => massExt_single v x k
  refine ⟨?_, fun x hx => ?_⟩
  · rw [e]; exact (continuousOn_pi.1 hc) k
  · rw [e]
    have hk := (hasDerivAt_pi.1 (hd x hx)) k
    have hg := shortFlowMomentGenerator_single F a ω ℓ x (massExt v x) k
    unfold shortFlowMomentGenerator at hg
    rw [hg]
    simp only [massExt_single]
    exact hk

/-- Continuity of the short generator on a path whose short gaps do not vanish. -/
theorem continuousOn_shortGenerator {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) {s u : ℝ}
    (hgap : ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l) :
    ContinuousOn (shortGenerator F a ω ℓ) (Icc s u) := by
  classical
  have hrate : ∀ k l : Fin N, k ≠ l →
      ContinuousOn (fun x => flowRate F a ω x k l) (Icc s u) := by
    intro k l hkl
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast k.pos.ne'
    refine ContinuousOn.inv₀ (Continuous.continuousOn (continuous_const.mul
      (((continuous_flowEigenvalue hF a ω k).sub (continuous_flowEigenvalue hF a ω l)).pow 2)))
      fun x hx => ?_
    exact mul_ne_zero hN0 (pow_ne_zero 2 (sub_ne_zero.2 (hgap x hx k l hkl)))
  refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun l => ?_
  by_cases hkl : k = l
  · subst hkl
    have e : (fun x => shortGenerator F a ω ℓ x k k) = fun x =>
        -∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ), flowRate F a ω x k m := by
      funext x; simp [shortGenerator]
    rw [e]
    refine (continuousOn_finsetSum _ fun m hm => ?_).neg
    exact hrate k m (Ne.symm (Finset.mem_filter.1 hm).2.1)
  · by_cases hd : labelDist k l < ℓ
    · have e : (fun x => shortGenerator F a ω ℓ x k l) = fun x => flowRate F a ω x k l := by
        funext x; simp [shortGenerator, hkl, hd]
      rw [e]; exact hrate k l hkl
    · have e : (fun x => shortGenerator F a ω ℓ x k l) = fun _ => 0 := by
        funext x; simp [shortGenerator, hkl, hd]
      rw [e]; exact continuousOn_const

/-- **Existence.** On a path whose short gaps do not vanish on `[s, u]`, every initial datum
has a sector-1 short moment-flow solution on `[s, u]`. -/
theorem exists_shortMomentFlow_one {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (ω : FlowSample N) (ℓ : ℕ) {s u : ℝ} (hsu : s ≤ u)
    (hgap : ∀ x ∈ Icc s u, ∀ k l : Fin N, k ≠ l →
      flowEigenvalue F a ω x k ≠ flowEigenvalue F a ω x l) (v₀ : Fin N → ℝ) :
    ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) 1 s u Φ ∧
      ∀ j : Fin N, Φ s (Pi.single j 1) = v₀ j := by
  obtain ⟨v, hv⟩ := RelativeLocalization.forwardMass_exists hsu
    (continuousOn_shortGenerator hF a ω ℓ hgap) v₀
  exact ⟨massExt v, isMomentFlowSolution_of_forwardMassSolution F a ω ℓ hv⟩

end BlockBand.Palm.MomentFlow
