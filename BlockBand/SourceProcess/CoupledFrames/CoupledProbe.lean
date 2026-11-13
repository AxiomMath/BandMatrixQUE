module

public import BlockBand.SourceProcess.CoupledFrames.CoupledSpec

/-!
# The probe specification of each frame

`probeSpec_of_frame`: a frame `Y` with probe vectors `pv_i` whose new columns `w_i = Y(θ_i) pv_i`
are near, perpendicular to the current columns, of squared norm `v_i`, and perpendicular to the
earlier probe columns, meets `ProbeSpec` for its Gram process. `jointPerp`: the perpendicularity
of the shared births to the earlier probe columns of both frames (by the sorted order;
simultaneous births by conjugate symmetry).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal ComplexOrder
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist

variable {K R : ℕ} {π : Type*} {n : ℕ} (eπ : π ≃ Fin n) {Ω : Type*}

theorem dot_comm_star {ι : Type*} [Fintype ι] (u w : ι → ℂ) :
    star u ⬝ᵥ w = star (star w ⬝ᵥ u) := by
  simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **`ProbeSpec` from frame-level facts.** -/
theorem probeSpec_of_frame {Y : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ' : π → Ω → ℝ}
    {v : π → ℝ} {pv : π → Ω → ExtCol K R → ℂ} {x : Ω} (wI : π → Amb K R → ℂ)
    (hw : ∀ i, Y (σ' i x).toNNReal x *ᵥ pv i x = wI i)
    (hP : ∀ i, ambP K R *ᵥ wI i = wI i)
    (hcur : ∀ i k, ((Y (σ' i x).toNNReal x)ᴴ *ᵥ wI i) (Sum.inl k) = 0)
    (hn : ∀ i, star (wI i) ⬝ᵥ wI i = (v i : ℂ))
    (hperp : ∀ i i', i ≠ i' → (σ' i x).toNNReal ≤ (σ' i' x).toNNReal →
      star (Y (σ' i' x).toNNReal x *ᵥ pv i x) ⬝ᵥ wI i' = 0) :
    ProbeSpec (fun t x => gramPair (ambP K R) (Y t x)) σ' v pv x := by
  have hM : ∀ (V : Matrix (Amb K R) (ExtCol K R) ℂ) (a : ExtCol K R → ℂ),
      (gramPair (ambP K R) V).1 *ᵥ a = Vᴴ *ᵥ (V *ᵥ a) := fun V a => by
    simp only [gramPair, sourceGram, mulVec_mulVec]
  refine ⟨fun i => ⟨?_, fun k => ?_, ?_⟩, fun i i' hii hle => ?_⟩
  · have hMB : (gramPair (ambP K R) (Y (σ' i x).toNNReal x)).1 -
        (gramPair (ambP K R) (Y (σ' i x).toNNReal x)).2 =
        (Y (σ' i x).toNNReal x)ᴴ * ((1 - ambP K R) * Y (σ' i x).toNNReal x) := by
      simp only [gramPair, sourceGram, nearGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_assoc]
    rw [hMB, ← mulVec_mulVec, ← mulVec_mulVec, hw, sub_mulVec, one_mulVec, hP, sub_self,
      mulVec_zero]
  · rw [hM, hw]; exact hcur i k
  · rw [hM, dot_conjTranspose_mulVec, hw]; exact hn i
  · rw [hM, dot_conjTranspose_mulVec, hw]; exact hperp i i' hii hle

variable {Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ' : π → Ω → ℝ} {v : π → ℝ}

/-- The new column of probe `i`. -/
def wI (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (σ' : π → Ω → ℝ) (v : π → ℝ)
    (x : Ω) (i : π) : Amb K R → ℂ :=
  Y₁ (σ' i x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i x

theorem stateV_probe {i i' : π} {x : Ω}
    (hlt : (srt (mθf eπ σ') x).symm (eπ i) < (srt (mθf eπ σ') x).symm (eπ i')) :
    stateV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v)
      ((srt (mθf eπ σ') x).symm (eπ i')).val x ((srt (mθf eπ σ') x).symm (eπ i)) =
      jvec eπ Y₁ Y₂ σ' v (eπ i) x :=
  stateV_apply_lt _ _ _ _ x _ _ hlt

/-- **Perpendicularity to the earlier probe columns of both frames.** -/
theorem jointPerp (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    {i i' : π} (hii : i ≠ i') (hle : (σ' i x).toNNReal ≤ (σ' i' x).toNNReal) :
    star (Y₁ (σ' i' x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i x) ⬝ᵥ wI eπ Y₁ Y₂ σ' v x i' = 0 ∧
      star (Y₂ (σ' i' x).toNNReal x *ᵥ pv2 eπ Y₁ Y₂ σ' v i x) ⬝ᵥ wI eπ Y₁ Y₂ σ' v x i' = 0 := by
  have hne : (srt (mθf eπ σ') x).symm (eπ i) ≠ (srt (mθf eπ σ') x).symm (eπ i') :=
    fun e => hii (eπ.injective ((srt (mθf eπ σ') x).symm.injective e))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hs := (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i').2.2.2.1 ((srt (mθf eπ σ') x).symm (eπ i))
    rw [stateV_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (v := v) hlt] at hs
    exact hs
  · have hT := sT_mono (mθf eπ σ') x hlt.le
    simp only [mθf_sT] at hT
    have heq : (σ' i x).toNNReal = (σ' i' x).toNNReal := le_antisymm hle hT
    have hs := (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).2.2.2.1
      ((srt (mθf eπ σ') x).symm (eπ i'))
    rw [stateV_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (v := v) hlt] at hs
    have h1 : Y₂ (σ' i x).toNNReal x *ᵥ pv2 eπ Y₁ Y₂ σ' v i x =
        Y₁ (σ' i x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i x :=
      (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i).1
    have h1' : Y₂ (σ' i' x).toNNReal x *ᵥ pv2 eπ Y₁ Y₂ σ' v i' x =
        Y₁ (σ' i' x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i' x :=
      (jointSpec_probe eπ (Y₁ := Y₁) (Y₂ := Y₂) (σ' := σ') hv hR hx i').1
    have hs1 : star (Y₁ (σ' i x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i' x) ⬝ᵥ
        (Y₁ (σ' i x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i x) = 0 := hs.1
    have hs2 : star (Y₂ (σ' i x).toNNReal x *ᵥ pv2 eπ Y₁ Y₂ σ' v i' x) ⬝ᵥ
        (Y₁ (σ' i x).toNNReal x *ᵥ pv1 eπ Y₁ Y₂ σ' v i x) = 0 := hs.2
    unfold wI
    rw [← heq] at h1' ⊢
    refine ⟨?_, ?_⟩
    · rw [dot_comm_star, hs1, star_zero]
    · rw [← h1', dot_comm_star, h1, hs2, star_zero]

end BlockBand.SourceProcess.CoupledFrames
