module

public import BlockBand.Transmission.Dual.GJCalc

/-!
# The product transforms `G_j` of Lemma 1′ are h-transforms)

* `prodH q u = H₁(left u) H_q(right u)`, `flatG j = prodH q ∘ (· ∘ e.symm)`;
  `flatG_eq`: `G_j(w) = (x₀ + y_j)⁻¹ H_q(rest_j)`, the summands of `cauchyH_le_sum`.
* `gDrift D₀ j = reindexDrift e (prodDrift (flatDrift D₀ 1) (flatDrift D₀ q))`: the pair and
  rest dual drifts, relabelled; this is the drift of the comparison process `Q^{(j)}`.
* `htDrift_flatG`: on `𝒞_{q+1}`, `b⁰ + a ∂log G_j = gDrift` pointwise (block calculus, relabelling,
  then `htDrift_cauchyH` per factor at the factor's own level).
* `mpGenerator_flatG`: `𝓛⁰ G_j = 0` on `𝒞_{q+1}` (Leibniz; the cross term vanishes).
* **`isHTransform_flatG`**: `IsHTransform D₀ (q+1) 𝒞_{q+1} G_j (gDrift D₀ j)`; the joint
  identity `𝓛⁰(G_j φ) = G_j 𝓛̃ φ` for every `C²` `φ` is `transform_of_htDrift` at each point.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open Filter Topology Set Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ}

theorem reindexDrift_symm_reindexDrift' {d d' : ℕ} (e : Fin d ≃ Fin d')
    (b : (Fin d' → ℝ) → Fin d' → ℝ) : reindexDrift e.symm (reindexDrift e b) = b := by
  funext y k
  simp only [reindexDrift, Equiv.symm_symm, Equiv.apply_symm_apply]
  congr 1
  funext i; simp

/-- The generator depends on the drift only through its value at the point. -/
theorem mpGenerator_congr_drift {d : ℕ} {b b' : (Fin d → ℝ) → Fin d → ℝ}
    {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {φ : (Fin d → ℝ) → ℝ} {w : Fin d → ℝ}
    (h : b w = b' w) : mpGenerator b a φ w = mpGenerator b' a φ w := by
  simp only [mpGenerator, h]

theorem reindexDrift_slot_diffDiag (D0 : ℝ) (j : Fin (q + 1)) :
    reindexDrift (slotEquiv j) (prodDrift (flatDiffDiag D0 1) (flatDiffDiag D0 q)) =
      flatDiffDiag D0 (q + 1) := by
  simp only [flatDiffDiag_eq_coordMap]
  exact reindexDrift_slot_coordMap _ _ j

/-!
## The pair and the rest of a chamber point
-/

theorem ofFlat_left_slot (j : Fin (q + 1)) (w : Fin ((q + 1) + (q + 1)) → ℝ) :
    ofFlat 1 (leftPart (w ∘ (slotEquiv j).symm)) = pairOf j (ofFlat (q + 1) w) := by
  rw [ofFlat_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show w (slot j (Fin.castAdd (q + q) (Fin.castAdd 1 i))) = _
    rw [slot_px]; rfl
  · show w (slot j (Fin.castAdd (q + q) (Fin.natAdd 1 i))) = _
    rw [slot_py]; rfl

theorem ofFlat_right_slot (j : Fin (q + 1)) (w : Fin ((q + 1) + (q + 1)) → ℝ) :
    ofFlat q (rightPart (w ∘ (slotEquiv j).symm)) = restOf j (ofFlat (q + 1) w) := by
  rw [ofFlat_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show w (slot j (Fin.natAdd (1 + 1) (Fin.castAdd q i))) = _
    rw [slot_rx]; rfl
  · show w (slot j (Fin.natAdd (1 + 1) (Fin.natAdd q i))) = _
    rw [slot_ry]; rfl

theorem left_slot_mem {w : Fin ((q + 1) + (q + 1)) → ℝ} (hw : w ∈ flatChamber (q + 1))
    (j : Fin (q + 1)) : leftPart (w ∘ (slotEquiv j).symm) ∈ flatChamber 1 := by
  show ofFlat 1 _ ∈ dualChamber 1
  rw [ofFlat_left_slot]; exact pair_mem_dualChamber j hw

theorem right_slot_mem {w : Fin ((q + 1) + (q + 1)) → ℝ} (hw : w ∈ flatChamber (q + 1))
    (j : Fin (q + 1)) : rightPart (w ∘ (slotEquiv j).symm) ∈ flatChamber q := by
  show ofFlat q _ ∈ dualChamber q
  rw [ofFlat_right_slot]; exact rest_mem_dualChamber j hw

/-!
## `G_j`
-/

/-- `H₁(pair) H_q(rest)` in the product layout. -/
def prodH (q : ℕ) : (Fin ((1 + 1) + (q + q)) → ℝ) → ℝ :=
  fun u => flatH 1 (leftPart u) * flatH q (rightPart u)

/-- `G_j(w) = h(x₀, y_j) H_q(rest_j)` at level `q + 1`. -/
def flatG (j : Fin (q + 1)) : (Fin ((q + 1) + (q + 1)) → ℝ) → ℝ :=
  prodH q ∘ compL (slotEquiv j).symm

/-- The target drift of `G_j`: the pair and rest dual drifts, relabelled. -/
def gDrift (D0 : ℝ) (j : Fin (q + 1)) :
    (Fin ((q + 1) + (q + 1)) → ℝ) → Fin ((q + 1) + (q + 1)) → ℝ :=
  reindexDrift (slotEquiv j) (prodDrift (flatDrift D0 1) (flatDrift D0 q))

theorem cauchyH_one (z : DualCoord 1) : cauchyH 1 z = (z.1 0 + z.2 0)⁻¹ := by
  simp [cauchyH, Matrix.det_unique, cauchyMatrix]

/-- `G_j` is the `j`-th summand of the row-1 expansion bound `cauchyH_le_sum`. -/
theorem flatG_eq (j : Fin (q + 1)) (w : Fin ((q + 1) + (q + 1)) → ℝ) :
    flatG j w = ((ofFlat (q + 1) w).1 0 + (ofFlat (q + 1) w).2 j)⁻¹ *
      cauchyH q (restOf j (ofFlat (q + 1) w)) := by
  show flatH 1 (leftPart (w ∘ (slotEquiv j).symm)) *
    flatH q (rightPart (w ∘ (slotEquiv j).symm)) = _
  rw [flatH, flatH, ofFlat_left_slot, ofFlat_right_slot, cauchyH_one]
  rfl

theorem contDiffAt_flatH {w : Fin (q + q) → ℝ} (hw : w ∈ flatChamber q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (flatH q) w :=
  (contDiffAt_cauchyH_of_mem hw).comp w (ofFlat q).contDiff.contDiffAt

theorem contDiffAt_flatG {w : Fin ((q + 1) + (q + 1)) → ℝ} (hw : w ∈ flatChamber (q + 1))
    (j : Fin (q + 1)) : ContDiffAt ℝ (⊤ : ℕ∞) (flatG j) w := by
  have hp : ContDiffAt ℝ (⊤ : ℕ∞) (prodH q) (compL (slotEquiv j).symm w) :=
    ((contDiffAt_flatH (left_slot_mem hw j)).comp _ leftL.contDiff.contDiffAt).mul
      ((contDiffAt_flatH (right_slot_mem hw j)).comp _ rightL.contDiff.contDiffAt)
  exact hp.comp w (compL _).contDiff.contDiffAt

theorem flatG_pos {w : Fin ((q + 1) + (q + 1)) → ℝ} (hw : w ∈ flatChamber (q + 1))
    (j : Fin (q + 1)) : 0 < flatG j w :=
  mul_pos (cauchyH_pos (left_slot_mem hw j)) (cauchyH_pos (right_slot_mem hw j))

/-- **`b⁰ + a ∂ log G_j` is the relabelled pair/rest dual drift** on `𝒞_{q+1}`. -/
theorem htDrift_flatG (D0 : ℝ) (j : Fin (q + 1)) {w : Fin ((q + 1) + (q + 1)) → ℝ}
    (hw : w ∈ flatChamber (q + 1)) :
    htDrift (flatBaseDrift D0 (q + 1)) (flatDiffDiag D0 (q + 1)) (flatG j) w = gDrift D0 j w := by
  have h1 := left_slot_mem hw j
  have h2 := right_slot_mem hw j
  have hd : DifferentiableAt ℝ (prodH q) (compL (slotEquiv j).symm w) :=
    (((contDiffAt_flatH h1).comp _ leftL.contDiff.contDiffAt).mul
      ((contDiffAt_flatH h2).comp _ rightL.contDiff.contDiffAt)).differentiableAt (by simp)
  rw [flatG, htDrift_comp_equiv _ _ _ hd, ← reindexDrift_slot_base D0 j,
    ← reindexDrift_slot_diffDiag D0 j, reindexDrift_symm_reindexDrift',
    reindexDrift_symm_reindexDrift', Equiv.symm_symm]
  funext k
  simp only [reindexDrift, gDrift]
  rw [show prodH q = fun u => flatH 1 (leftPart u) * flatH q (rightPart u) from rfl,
    htDrift_prod _ _ _ _ ((contDiffAt_flatH h1).differentiableAt (by simp))
      ((contDiffAt_flatH h2).differentiableAt (by simp)) (cauchyH_pos h1).ne'
      (cauchyH_pos h2).ne']
  simp only [prodDrift, htDrift_cauchyH D0 h1, htDrift_cauchyH D0 h2]

/-- **`G_j` is base-harmonic** on `𝒞_{q+1}`. -/
theorem mpGenerator_flatG (D0 : ℝ) (j : Fin (q + 1)) {w : Fin ((q + 1) + (q + 1)) → ℝ}
    (hw : w ∈ flatChamber (q + 1)) :
    mpGenerator (flatBaseDrift D0 (q + 1)) (flatDiff D0 (q + 1)) (flatG j) w = 0 := by
  have h1 := left_slot_mem hw j
  have h2 := right_slot_mem hw j
  have c1 : ContDiffAt ℝ 2 (flatH 1) (leftL (compL (slotEquiv j).symm w)) :=
    (contDiffAt_flatH h1).of_le (by simp)
  have c2 : ContDiffAt ℝ 2 (flatH q) (rightL (compL (slotEquiv j).symm w)) :=
    (contDiffAt_flatH h2).of_le (by simp)
  have hp : ContDiffAt ℝ 2 (prodH q) (compL (slotEquiv j).symm w) :=
    (c1.comp _ leftL.contDiff.contDiffAt).mul (c2.comp _ rightL.contDiff.contDiffAt)
  have g1 : mpGenerator (flatBaseDrift D0 1) (fun y => Matrix.diagonal (flatDiffDiag D0 1 y))
      (flatH 1) (leftPart (w ∘ (slotEquiv j).symm)) = 0 :=
    (isHTransform_cauchyH D0).harm _ h1
  have g2 : mpGenerator (flatBaseDrift D0 q) (fun y => Matrix.diagonal (flatDiffDiag D0 q y))
      (flatH q) (rightPart (w ∘ (slotEquiv j).symm)) = 0 :=
    (isHTransform_cauchyH D0).harm _ h2
  show mpGenerator (flatBaseDrift D0 (q + 1))
    (fun y => Matrix.diagonal (flatDiffDiag D0 (q + 1) y))
    (prodH q ∘ compL (slotEquiv j).symm) w = 0
  rw [mpGenerator_comp_equiv _ _ _ hp, ← reindexDrift_slot_base D0 j,
    ← reindexDrift_slot_diffDiag D0 j, reindexDrift_symm_reindexDrift',
    reindexDrift_symm_reindexDrift',
    show prodH q = fun u => flatH 1 (leftPart u) * flatH q (rightPart u) from rfl,
    mpGenerator_prod_mul _ _ _ _ c1 c2]
  simp only [compL_apply, g1, g2, mul_zero, add_zero]

theorem contDiffAt_gDrift (D0 : ℝ) (j : Fin (q + 1)) {w : Fin ((q + 1) + (q + 1)) → ℝ}
    (hw : w ∈ flatChamber (q + 1)) : ContDiffAt ℝ (⊤ : ℕ∞) (gDrift D0 j) w := by
  have h1 := left_slot_mem hw j
  have h2 := right_slot_mem hw j
  have hP : ContDiffAt ℝ (⊤ : ℕ∞) (prodDrift (flatDrift D0 1) (flatDrift D0 q))
      (compL (slotEquiv j).symm w) := by
    refine contDiffAt_pi.2 fun s => ?_
    induction s using Fin.addCases with
    | left i =>
      have e : (fun u => prodDrift (flatDrift D0 1) (flatDrift D0 q) u (Fin.castAdd (q + q) i)) =
          (fun v => flatDrift D0 1 v i) ∘ leftL := funext fun u => Fin.append_left _ _ _
      rw [e]
      exact (contDiffAt_pi.1 (contDiffAt_flatDrift D0 h1) i).comp _ leftL.contDiff.contDiffAt
    | right l =>
      have e : (fun u => prodDrift (flatDrift D0 1) (flatDrift D0 q) u (Fin.natAdd (1 + 1) l)) =
          (fun v => flatDrift D0 q v l) ∘ rightL := funext fun u => Fin.append_right _ _ _
      rw [e]
      exact (contDiffAt_pi.1 (contDiffAt_flatDrift D0 h2) l).comp _ rightL.contDiff.contDiffAt
  have e : gDrift D0 j = fun w => compL (slotEquiv j)
      (prodDrift (flatDrift D0 1) (flatDrift D0 q) (compL (slotEquiv j).symm w)) := rfl
  rw [e]
  exact (compL (slotEquiv j)).contDiff.contDiffAt.comp w
    (hP.comp w (compL _).contDiff.contDiffAt)

theorem locallyLipschitzOn_gDrift (D0 : ℝ) (j : Fin (q + 1)) :
    LocallyLipschitzOn (flatChamber (q + 1)) (gDrift D0 j) := by
  intro w hw
  obtain ⟨K, t, ht, hK⟩ := ((contDiffAt_gDrift D0 j hw).of_le (by norm_num)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- **`G_j` is an h-transform of the base process on `𝒞_{q+1}`**, with target the relabelled
pair/rest dual drift. -/
theorem isHTransform_flatG (D0 : ℝ) (j : Fin (q + 1)) :
    IsHTransform D0 (q + 1) (flatChamber (q + 1)) (flatG j) (gDrift D0 j) where
  isOpen := isOpen_flatChamber _
  sub := subset_rfl
  smooth := fun w hw => ((contDiffAt_flatG hw j).of_le (by simp)).contDiffWithinAt
  pos := fun w hw => flatG_pos hw j
  harm := fun w hw => mpGenerator_flatG D0 j hw
  lip := locallyLipschitzOn_gDrift D0 j
  transform := fun φ hφ w hw => by
    rw [mpGenerator_congr_drift (htDrift_flatG D0 j hw).symm]
    exact transform_of_htDrift (flatBaseDrift D0 (q + 1)) (flatDiffDiag D0 (q + 1))
      ((contDiffAt_flatG hw j).of_le (by simp)) hφ.contDiffAt (flatG_pos hw j).ne'
      (mpGenerator_flatG D0 j hw)

end BlockBand.Transmission.Dual.G
