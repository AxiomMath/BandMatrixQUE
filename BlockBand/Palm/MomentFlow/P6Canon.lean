module

public import BlockBand.Palm.MomentFlow.CanonFlows

/-!
# Canonical forward short flows from deterministic data, and the window decomposition

* `fwdC F a c ℓ r n Φ₀`: `truncForward` at gap level `1/(n+1)` from a datum `Φ₀`; on `gapSet n`
  it is the exact short flow (`fwdC_isSolution`), it stays between the datum's bounds
  (`fwdC_bounds`), does not depend on `n` (`fwdC_succ`), and every short solution from the same
  datum equals it (`shortSol_eq_fwdC`).
* `isMomentFlowSolution_sum`: finite sums of solutions are solutions.
* **`window_decomp`**: the flow started from the indicator of a finite set `S` of configurations
  is the sum of the flows started from `δ_η`, `η ∈ S` (uniqueness).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem IsMomentFlowSolution.add {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    {F G : ℝ → Occ N → ℝ} (hF : IsMomentFlowSolution c r a b F)
    (hG : IsMomentFlowSolution c r a b G) :
    IsMomentFlowSolution c r a b (fun u ξ => F u ξ + G u ξ) := by
  intro ξ hξ
  refine ⟨(hF ξ hξ).1.add (hG ξ hξ).1, fun u hu => ?_⟩
  have h := ((hF ξ hξ).2 u hu).add ((hG ξ hξ).2 u hu)
  have e : momentGenerator (c u) (fun ζ => F u ζ + G u ζ) ξ =
      momentGenerator (c u) (F u) ξ + momentGenerator (c u) (G u) ξ :=
    momentGenerator_add (c u) (F u) (G u) ξ
  rw [e]; exact h

theorem isMomentFlowSolution_sum {ι : Type*} {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {a b : ℝ}
    (S : Finset ι) {Φ : ι → ℝ → Occ N → ℝ} (hΦ : ∀ i ∈ S, IsMomentFlowSolution c r a b (Φ i)) :
    IsMomentFlowSolution c r a b (fun u ξ => ∑ i ∈ S, Φ i u ξ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa using isMomentFlowSolution_const c r a b 0
  | insert i S hi ih =>
    have h := (hΦ i (Finset.mem_insert_self i S)).add
      (ih fun j hj => hΦ j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using h

/-- **Window decomposition.** -/
theorem window_decomp {c : ℝ → Fin N → Fin N → ℝ} {r : ℕ} {s u : ℝ}
    (hc : ∀ x ∈ Ioo s u, ∀ i j, i ≠ j → 0 ≤ c x i j) (S : Finset (Occ N))
    {H : ℝ → Occ N → ℝ} (hH : IsMomentFlowSolution c r s u H)
    (hH0 : ∀ ζ ∈ sector N r, H s ζ = if ζ ∈ S then 1 else 0)
    {Φ : Occ N → ℝ → Occ N → ℝ} (hΦ : ∀ η ∈ S, IsMomentFlowSolution c r s u (Φ η))
    (hΦ0 : ∀ η ∈ S, ∀ ζ ∈ sector N r, Φ η s ζ = if ζ = η then 1 else 0) :
    ∀ v ∈ Icc s u, ∀ ζ ∈ sector N r, H v ζ = ∑ η ∈ S, Φ η v ζ := by
  classical
  refine hH.eq_of_initial_eq hc (isMomentFlowSolution_sum S hΦ) fun ζ hζ => ?_
  rw [hH0 ζ hζ, Finset.sum_congr rfl fun η hη => hΦ0 η hη ζ hζ]
  exact (Finset.sum_ite_eq S ζ fun _ => (1 : ℝ)).symm

/-!
## Canonical forward short flows
-/

/-- `truncForward` at gap level `1/(n+1)` on `[a, c]`. -/
def fwdC (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ)
    (v : ℝ) (ω : FlowSample N) : Occ N → ℝ :=
  truncForward F a ℓ (gapLevel n) a c r Φ₀ v ω

theorem fwdC_isSolution {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    IsMomentFlowSolution (shortFlowRate F a ω ℓ) r a c (fun v => fwdC F a c ℓ r n Φ₀ v ω) ∧
      ∀ ζ ∈ sector N r, fwdC F a c ℓ r n Φ₀ a ω ζ = Φ₀ ω ζ :=
  truncForward_isSolution hF hN a ℓ (gapLevel_pos n) hac r Φ₀ ω hω

theorem fwdC_bounds {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {m M : ℝ} (hm : ∀ ζ ∈ sector N r, m ≤ Φ₀ ω ζ)
    (hM : ∀ ζ ∈ sector N r, Φ₀ ω ζ ≤ M) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r,
      m ≤ fwdC F a c ℓ r n Φ₀ v ω ζ ∧ fwdC F a c ℓ r n Φ₀ v ω ζ ≤ M := by
  obtain ⟨hs, h0⟩ := fwdC_isSolution hF hN hac ℓ r n Φ₀ hω
  exact shortFlowMoment_bounds F a ω ℓ r hs (fun ζ hζ => by rw [h0 ζ hζ]; exact hm ζ hζ)
    (fun ζ hζ => by rw [h0 ζ hζ]; exact hM ζ hζ)

theorem fwdC_succ {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r,
      fwdC F a c ℓ r (n + 1) Φ₀ v ω ζ = fwdC F a c ℓ r n Φ₀ v ω ζ := by
  obtain ⟨hs, h0⟩ := fwdC_isSolution hF hN hac ℓ r n Φ₀ hω
  obtain ⟨hs', h0'⟩ := fwdC_isSolution hF hN hac ℓ r (n + 1) Φ₀ (gapSet_mono F a c n hω)
  exact hs'.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hs
    fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

theorem shortSol_eq_fwdC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {h : ℝ → Occ N → ℝ} (hh : ShortSol F a c ω ℓ r h)
    (h0 : ∀ ζ ∈ sector N r, h a ζ = Φ₀ ω ζ) :
    ∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r, h σ ζ = fwdC F a c ℓ r n Φ₀ σ ω ζ := by
  obtain ⟨hs', h0'⟩ := fwdC_isSolution hF hN hac ℓ r n Φ₀ hω
  exact hh.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hs'
    fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

theorem measurable_fwdC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (ℓ r n : ℕ) {Φ₀ : FlowSample N → Occ N → ℝ}
    (hΦ₀ : ∀ ζ, Measurable[pathSigma F a a c] fun ω => Φ₀ ω ζ) (v : ℝ) (ζ : Occ N) :
    Measurable[pathSigma F a a c] fun ω => fwdC F a c ℓ r n Φ₀ v ω ζ :=
  measurable_truncForward hF hN ℓ (gapLevel_pos n) le_rfl hac le_rfl r hΦ₀ v ζ

theorem continuous_fwdC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a c : ℝ) (ℓ r n : ℕ) (Φ₀ : FlowSample N → Occ N → ℝ) (ω : FlowSample N) (ζ : Occ N) :
    Continuous fun v => fwdC F a c ℓ r n Φ₀ v ω ζ :=
  continuous_truncForward hF hN a ℓ (gapLevel_pos n) a c r Φ₀ ω ζ

end BlockBand.Palm.MomentFlow
