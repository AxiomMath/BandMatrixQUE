module

public import BlockBand.SourceProcess.CoupledFrames.CoupledProbe

/-!
# Consequences of the joint specification at a good sample point

At a sample
point where both frames keep full near rank (`GoodRank`):

* `probeSpec₁`, `probeSpec₂`: `ProbeSpec` for each frame's Gram process;
* `wv_frame₂`: `Y₂(τ_k) a₂_k = w_k` (the shared birth lies in both ranges);
* `wv_near`, `wv_norm`: `P w_k = w_k`, `Σ_i ‖w_k(i)‖² = v`;
* `wv_eq_wI`: `w_k` is the new column of probe `eπ⁻¹ k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal ComplexOrder ComplexConjugate
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist

variable {K R : ℕ} {π : Type*} {n : ℕ} (eπ : π ≃ Fin n) {Ω : Type*}
  {Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ' : π → Ω → ℝ} {v : π → ℝ}

theorem probeSpec₁ (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x) :
    ProbeSpec (fun t x => gramPair (ambP K R) (Y₁ t x)) σ' v (pv1 eπ Y₁ Y₂ σ' v) x :=
  probeSpec_of_frame (wI eπ Y₁ Y₂ σ' v x) (fun _ => rfl)
    (fun i => (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.1)
    (fun i k => ((jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.2.1
      (Sum.inl k) trivial).1)
    (fun i => (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.2.2.2)
    (fun _ _ hii hle => (jointPerp eπ hv hR hx hii hle).1)

theorem probeSpec₂ (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x) :
    ProbeSpec (fun t x => gramPair (ambP K R) (Y₂ t x)) σ' v (pv2 eπ Y₁ Y₂ σ' v) x :=
  probeSpec_of_frame (wI eπ Y₁ Y₂ σ' v x)
    (fun i => (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).1)
    (fun i => (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.1)
    (fun i k => ((jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.2.1
      (Sum.inl k) trivial).2)
    (fun i => (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.2.2.2)
    (fun _ _ hii hle => (jointPerp eπ hv hR hx hii hle).2)

theorem wv_eq_wI (x : Ω) (k : Fin n) :
    wv eπ Y₁ Y₂ σ' v k x = wI eπ Y₁ Y₂ σ' v x (eπ.symm k) := by
  simp only [wv, wI, pv1, bτ, Equiv.apply_symm_apply]

theorem wv_frame₂ (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (k : Fin n) : Y₂ (bτ eπ σ' k x) x *ᵥ ba eπ (pv2 eπ Y₁ Y₂ σ' v) k x = wv eπ Y₁ Y₂ σ' v k x := by
  rw [wv_eq_wI]
  exact (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx (eπ.symm k)).1

theorem wv_near (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (k : Fin n) : ambP K R *ᵥ wv eπ Y₁ Y₂ σ' v k x = wv eπ Y₁ Y₂ σ' v k x := by
  rw [wv_eq_wI]
  exact (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx (eπ.symm k)).2.1

theorem dot_self_eq_sum {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem wv_dot (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (k : Fin n) : star (wv eπ Y₁ Y₂ σ' v k x) ⬝ᵥ wv eπ Y₁ Y₂ σ' v k x = (v (eπ.symm k) : ℂ) := by
  rw [wv_eq_wI]
  exact (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx (eπ.symm k)).2.2.2.2

theorem wv_norm (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (k : Fin n) : ∑ i, ‖wv eπ Y₁ Y₂ σ' v k x i‖ ^ 2 = v (eπ.symm k) := by
  have h := wv_dot eπ (σ' := σ') hv hR hx k
  rw [dot_self_eq_sum] at h
  exact_mod_cast h

end BlockBand.SourceProcess.CoupledFrames
