module

public import BlockBand.SourceProcess.CoupledFrames.CoupledMeas

/-!
# The joint specification holds at every sorted birth

`jointSpec_sorted`: where both frames keep full near rank at all times (`GoodRank`), the joint
vector of the `l`-th sorted birth meets `JointSpec` for the frames at its birth time
(`genSel_spec`, `jointExists`, `jointSpec_of`); `jointSpec_probe`: the same, indexed by the probe.
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

/-- Both frames keep full near rank at all times. -/
def GoodRank (Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ) (x : Ω) : Prop :=
  ∀ t, (ambP K R).rank ≤ (ambP K R * Y₁ t x).rank ∧ (ambP K R).rank ≤ (ambP K R * Y₂ t x).rank

theorem posSemidef_jointQ {ι c' : Type*} [Fintype ι] [Fintype c'] [DecidableEq c']
    (P : Matrix ι ι ℂ) (V : Matrix ι (c' ⊕ c') ℂ) : (jointQ (gramPair P V)).PosSemidef := by
  have e : jointQ (gramPair P V) = (V * (projF 0 : Matrix (c' ⊕ c') (c' ⊕ c') ℂ))ᴴ *
      (V * (projF 0 : Matrix (c' ⊕ c') (c' ⊕ c') ℂ)) := by
    rw [conjTranspose_mul, projF_herm]
    simp only [jointQ, gramPair, sourceGram, Matrix.mul_assoc]
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

theorem card_amb : Fintype.card (Amb K R) = 2 * K + R := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- **The joint specification at every sorted birth.** -/
theorem jointSpec_sorted {Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ' : π → Ω → ℝ}
    {v : π → ℝ} (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (l : Fin n) :
    JointSpec (isCur K R) (ambP K R) (Y₁ (sT (mθf eπ σ') l x) x) (Y₂ (sT (mθf eπ σ') l x) x)
      (stateV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v) l.val x)
      (mvf eπ v (srt (mθf eπ σ') x l))
      (bV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v) l x) := by
  have hPh := (isNearProjection_ambP K R).1
  have hPP := (isNearProjection_ambP K R).2.1
  rw [bV_eq]
  set t := sT (mθf eπ σ') l x
  set prev := stateV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v) l.val x
  have hE := jointExists (cur := isCur K R) hPP (Y₁ t x) (Y₂ t x) (hx t).1 (hx t).2 prev (by
    rw [card_isCur, card_amb, rank_ambP]; omega)
  have h := genSel_spec (fun z : (Matrix (ExtCol K R ⊕ ExtCol K R) (ExtCol K R ⊕ ExtCol K R) ℂ ×
      Matrix (ExtCol K R ⊕ ExtCol K R) (ExtCol K R ⊕ ExtCol K R) ℂ) ×
      (Fin n → ExtCol K R ⊕ ExtCol K R → ℂ) × ℝ => jointG (isCur K R) z.1 z.2.1)
    (fun z => jointQ z.1) (fun z => z.2.2) (z := (jGram Y₁ Y₂ t x, prev, mvf eπ v (srt (mθf eπ σ') x l)))
    (hv _) (posSemidef_jointQ _ _) hE
  exact jointSpec_of hPh hPP h.1 h.2

/-- The joint specification of probe `i`, at its birth time `θ_i`. -/
theorem jointSpec_probe {Y₁ Y₂ : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ' : π → Ω → ℝ}
    {v : π → ℝ} (hv : ∀ i, 0 ≤ v i) (hR : 5 * K + 2 * n < R) {x : Ω} (hx : GoodRank Y₁ Y₂ x)
    (i : π) :
    JointSpec (isCur K R) (ambP K R) (Y₁ (σ' i x).toNNReal x) (Y₂ (σ' i x).toNNReal x)
      (stateV (jointSel n (isCur K R)) (jGram Y₁ Y₂) (mθf eπ σ') (mvf eπ v)
        ((srt (mθf eπ σ') x).symm (eπ i)).val x) (v i) (jvec eπ Y₁ Y₂ σ' v (eπ i) x) := by
  have h := jointSpec_sorted eπ (σ' := σ') hv hR hx ((srt (mθf eπ σ') x).symm (eπ i))
  rwa [mθf_sT, mvf_srt] at h

end BlockBand.SourceProcess.CoupledFrames
