module

public import BlockBand.SourceProcess.CoupledFrames.CoupledFacts

/-!
# The shared births are perpendicular to both frames

`bornFrame_perp`: at its birth time `τ_k`, the shared vector `w_k` is perpendicular to every
other column of the born frame: the current columns (`(Yᴴ w_k)_{inl y} = 0`) and the probe columns
already born (`⟨Y pv_{i'}, w_k⟩ = 0` for `θ_{i'} ≤ τ_k`). `coupled_perp`: both frames, at good
sample points.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal ComplexOrder ComplexConjugate
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique

variable {K R : ℕ} {π : Type*} [DecidableEq π] {n : ℕ} (eπ : π ≃ Fin n)
  {S : Type*} {κ : Type*}

theorem bornFrame_perp {Y : ℝ≥0 → DriverSample S κ → Matrix (Amb K R) (ExtCol K R) ℂ}
    {σ' : π → DriverSample S κ → ℝ} {pv : π → DriverSample S κ → ExtCol K R → ℂ}
    {w : Fin n → DriverSample S κ → Amb K R → ℂ} {x : DriverSample S κ}
    (hw : ∀ k, Y (bτ eπ σ' k x) x *ᵥ ba eπ pv k x = w k x)
    (hcol : ∀ k y, ((Y (bτ eπ σ' k x) x)ᴴ *ᵥ w k x) (Sum.inl y) = 0)
    (hperp : ∀ i' k, i' ≠ eπ.symm k → (σ' i' x).toNNReal ≤ bτ eπ σ' k x →
      star (Y (bτ eπ σ' k x) x *ᵥ pv i' x) ⬝ᵥ w k x = 0)
    (k : Fin n) (j : SrcCol K π) (hj : j ≠ bcol eπ k) :
    ∑ i, conj (bornFrame eπ Y σ' pv w (bτ eπ σ' k x) x i j) * w k x i = 0 := by
  rw [bornFrame_eq eπ Y σ' pv w hw]
  set L := bornL (mθ K σ') (glam K R pv) (bτ eπ σ' k x) x
  have e : ∑ i, conj ((Y (bτ eπ σ' k x) x * L) i j) * w k x i =
      star (Y (bτ eπ σ' k x) x *ᵥ fun y => L y j) ⬝ᵥ w k x := by
    simp only [dotProduct, Pi.star_apply, Matrix.mul_apply, mulVec, RCLike.star_def]
  rw [e]
  rcases j with y | i'
  · have hL : (fun y' => L y' (Sum.inl y)) = Pi.single (Sum.inl y) 1 := by
      funext y'; simp [L, bornL, mθ, glam]
    rw [hL, ← dot_conjTranspose_mulVec, single_dot]
    exact hcol k y
  · have hne : i' ≠ eπ.symm k := fun e => hj (by rw [e]; rfl)
    by_cases hb : (σ' i' x).toNNReal ≤ bτ eπ σ' k x
    · have hL : (fun y' => L y' (Sum.inr i')) = pv i' x := by
        funext y'; simp only [L, bornL, mθ, glam]; exact ite_eq_left hb
      rw [hL]
      exact hperp i' k hne hb
    · have hL : (fun y' => L y' (Sum.inr i')) = 0 := by
        funext y'; simp only [L, bornL, mθ, glam]; exact ite_eq_right hb
      rw [hL, mulVec_zero, star_zero, zero_dotProduct]

variable {Y₁ Y₂ : ℝ≥0 → DriverSample S κ → Matrix (Amb K R) (ExtCol K R) ℂ}
  {σ' : π → DriverSample S κ → ℝ} {v : π → ℝ}

/-- **Perpendicularity in both frames.** -/
theorem coupled_perp (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : DriverSample S κ}
    (hx : GoodRank Y₁ Y₂ x) (k : Fin n) (j : SrcCol K π) (hj : j ≠ bcol eπ k) :
    (∑ i, conj (bornFrame eπ Y₁ σ' (pv1 eπ Y₁ Y₂ σ' v) (wv eπ Y₁ Y₂ σ' v) (bτ eπ σ' k x) x i j) *
        wv eπ Y₁ Y₂ σ' v k x i = 0) ∧
      ∑ i, conj (bornFrame eπ Y₂ σ' (pv2 eπ Y₁ Y₂ σ' v) (wv eπ Y₁ Y₂ σ' v) (bτ eπ σ' k x) x i j) *
        wv eπ Y₁ Y₂ σ' v k x i = 0 := by
  have hs := fun k : Fin n =>
    jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx (eπ.symm k)
  refine ⟨bornFrame_perp eπ (fun k => wv_eq eπ Y₁ Y₂ σ' v k x) (fun k y => ?_) (fun i' k hi hb => ?_) k j hj,
    bornFrame_perp eπ (wv_frame₂ eπ hv hR hx) (fun k y => ?_) (fun i' k hi hb => ?_) k j hj⟩
  · rw [wv_eq_wI]; exact ((hs k).2.2.1 (Sum.inl y) trivial).1
  · rw [wv_eq_wI]; exact (jointPerp eπ hv hR hx hi hb).1
  · rw [wv_eq_wI]; exact ((hs k).2.2.1 (Sum.inl y) trivial).2
  · rw [wv_eq_wI]; exact (jointPerp eπ hv hR hx hi hb).2

end BlockBand.SourceProcess.CoupledFrames
