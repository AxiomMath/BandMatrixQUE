module

public import BlockBand.Palm.MomentFlow.IndProps

/-!
# The base case `CM(0, M)` of the induction on `r`

For `r = 0` the moment is one: every regular version
of the `0`-particle conditional moment equals `1` at all times of `[a, c₀]` along a.e. path:
at `c₀` it is a version of `E[1 | 𝓛] = 1`, and on the `0`-sector the moment flow is constant
(`IsMomentFlowSolution.eq_of_initial_eq` against the constant solution).

* `sector_zero_eq`: the `0`-sector is `{0}`.
* `regVersion_zero_eq_one`: a.e., `Φ σ ξ ω = 1` for all `σ ∈ [a, c]`, `ξ ∈ sector N 0`.
* **`cmWin_zero`**: `CMWin 0 M` for every `M` (with `κ = 1`, `C = 0`, `B = ∅`, `e = 0`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

variable {N : ℕ}

theorem sector_zero_eq {ξ : Occ N} (hξ : ξ ∈ sector N 0) : ξ = fun _ => 0 := by
  rw [mem_sector] at hξ
  funext i
  have := (Finset.sum_eq_zero_iff.1 hξ) i (mem_univ i)
  exact this

theorem regVersion_zero_eq_one {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} (hac : a ≤ c)
    {q : Fin N → ℂ} {Φ : ℝ → Occ N → FlowSample N → ℝ} (hΦ : RegVersion F a c q 0 Φ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ σ ∈ Icc a c, ∀ ξ ∈ sector N 0, Φ σ ξ ω = 1 := by
  have h0 : (fun _ => 0 : Occ N) ∈ sector N 0 := by rw [mem_sector]; simp
  have hc : c ∈ Icc a c := ⟨hac, le_rfl⟩
  have hv := hΦ.1 c hc _ h0
  have hce : condMoment F a c q c (fun _ => 0) =ᵐ[flowLaw N a] fun _ => (1 : ℝ) := by
    unfold condMoment
    simp only [momentMonomial_zero]
    rw [condExp_const (pathSigma_le F a a c)]
  filter_upwards [hv, hce, hΦ.2] with ω e1 e2 e3 σ hσ ξ hξ
  have hconst := isMomentFlowSolution_const (flowRate F a ω) 0 a c (Φ a (fun _ => 0) ω)
  have heq := e3.eq_of_initial_eq (fun u _ i j _ => flowRate_nonneg F a ω u i j) hconst
    (fun ζ hζ => by rw [sector_zero_eq hζ])
  rw [sector_zero_eq hξ, heq σ hσ _ h0, ← heq c hc _ h0, e1, e2]

/-- **Base case** `CM(0, M)`. -/
theorem cmWin_zero (M : ℝ) : CMWin 0 M := by
  intro A c₀ r₀ s₀ v₀ hK
  refine ⟨1, 0, one_pos, fun D => ⟨1, fun N hN F E hC q hq => ?_⟩⟩
  refine ⟨∅, @MeasurableSet.empty _ (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀), by simp,
    fun Φ hΦ => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hτ : 0 < cmTau N := by unfold cmTau; exact Real.rpow_pos_of_pos hNp _
  have hcm : c₀ - cmTau N ≤ c₀ := by linarith
  filter_upwards [regVersion_zero_eq_one hcm hΦ] with ω hω _
  refine ⟨fun _ => 0, ⟨continuousOn_const, fun _ _ => le_rfl, ?_, ?_⟩, ?_⟩
  · simp only [intervalIntegral.integral_zero]; positivity
  · positivity
  · intro σ hσ k₀ _ ξ hξ _
    have hσ' : σ ∈ Icc (c₀ - cmTau N) c₀ := by
      refine ⟨?_, hσ.2⟩
      have : 0 ≤ cmT 0 * cmTau N := by unfold cmT; norm_num; positivity
      linarith [hσ.1]
    rw [hω σ hσ' ξ hξ]; simp

end BlockBand.Palm.MomentFlow
