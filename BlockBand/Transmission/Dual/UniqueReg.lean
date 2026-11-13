module

public import BlockBand.Transmission.Dual.UniqueCoord

/-!
# Uniqueness in law: regularity of the flat coefficients

On the open set `flatChamber q = ofFlat q ⁻¹' 𝒞_q`:
* `isOpen_flatChamber`;
* `locallyLipschitzOn_flatDrift`: the flat drift `(D₀/2)(β^x, β^y)` is smooth at every point of
  the chamber, hence locally Lipschitz there;
* `contDiff_flatDiff`: the flat diffusion `D₀ diag(x(1+x), y(1−y))` is a polynomial, hence
  `C^∞` on all of `ℝ^{q+q}` (Frobenius normed structure on matrices); written as
  `Σ_k d_k • single k k 1`.
These are the coefficient hypotheses of `stoppedMartingaleProblemUniquenessPosDef_holds` and of
`isMPSolutionOn_of_test`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ}

/-- The chamber in flat coordinates. -/
def flatChamber (q : ℕ) : Set (Fin (q + q) → ℝ) := ofFlat q ⁻¹' dualChamber q

theorem isOpen_flatChamber (q : ℕ) : IsOpen (flatChamber q) :=
  (isOpen_dualChamber q).preimage (ofFlat q).continuous

theorem contDiffAt_dualDriftX {z : DualCoord q} (hz : z ∈ dualChamber q) (i : Fin q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : DualCoord q => dualDriftX z i) z := by
  have hinj : Function.Injective z.1 := hz.1.injective
  have hpos : ∀ j, 0 < z.1 i + z.2 j := fun j => add_pos (hz.2.2.1 i) (hz.2.2.2 j).1
  have cx : ∀ k : Fin q, ContDiff ℝ (⊤ : ℕ∞) fun z : DualCoord q => z.1 k := fun k =>
    (contDiff_apply ℝ ℝ k).comp contDiff_fst
  have cy : ∀ k : Fin q, ContDiff ℝ (⊤ : ℕ∞) fun z : DualCoord q => z.2 k := fun k =>
    (contDiff_apply ℝ ℝ k).comp contDiff_snd
  unfold dualDriftX
  refine (contDiffAt_const.add ((contDiff_const.mul (cx i)).contDiffAt)).add
    (ContDiffAt.mul ((contDiff_const.mul (cx i)).mul (contDiff_const.add (cx i))).contDiffAt ?_)
  refine ContDiffAt.sub (ContDiffAt.sum fun k hk => ?_) (ContDiffAt.sum fun j _ => ?_)
  · have hne : z.1 i - z.1 k ≠ 0 :=
      sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hk) (hinj h).symm
    exact contDiffAt_const.div ((cx i).sub (cx k)).contDiffAt hne
  · exact contDiffAt_const.div ((cx i).add (cy j)).contDiffAt (hpos j).ne'

theorem contDiffAt_dualDriftY {z : DualCoord q} (hz : z ∈ dualChamber q) (j : Fin q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : DualCoord q => dualDriftY z j) z := by
  have hinj : Function.Injective z.2 := hz.2.1.injective
  have hpos : ∀ i, 0 < z.1 i + z.2 j := fun i => add_pos (hz.2.2.1 i) (hz.2.2.2 j).1
  have cx : ∀ k : Fin q, ContDiff ℝ (⊤ : ℕ∞) fun z : DualCoord q => z.1 k := fun k =>
    (contDiff_apply ℝ ℝ k).comp contDiff_fst
  have cy : ∀ k : Fin q, ContDiff ℝ (⊤ : ℕ∞) fun z : DualCoord q => z.2 k := fun k =>
    (contDiff_apply ℝ ℝ k).comp contDiff_snd
  unfold dualDriftY
  refine (contDiffAt_const.sub ((contDiff_const.mul (cy j)).contDiffAt)).add
    (ContDiffAt.mul ((contDiff_const.mul (cy j)).mul (contDiff_const.sub (cy j))).contDiffAt ?_)
  refine ContDiffAt.sub (ContDiffAt.sum fun l hl => ?_) (ContDiffAt.sum fun i _ => ?_)
  · have hne : z.2 j - z.2 l ≠ 0 :=
      sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hl) (hinj h).symm
    exact contDiffAt_const.div ((cy j).sub (cy l)).contDiffAt hne
  · exact contDiffAt_const.div ((cx i).add (cy j)).contDiffAt (hpos i).ne'

theorem contDiffAt_flatDrift (D0 : ℝ) {w : Fin (q + q) → ℝ} (hw : w ∈ flatChamber q) :
    ContDiffAt ℝ (⊤ : ℕ∞) (flatDrift D0 q) w := by
  refine contDiffAt_pi.2 fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · have e : (fun w => flatDrift D0 q w (Fin.castAdd q i)) =
        fun w => D0 / 2 * dualDriftX (ofFlat q w) i := by
      funext w; exact Fin.append_left _ _ _
    rw [e]
    exact contDiffAt_const.mul ((contDiffAt_dualDriftX hw i).comp w
      (ofFlat q).contDiff.contDiffAt)
  · have e : (fun w => flatDrift D0 q w (Fin.natAdd q j)) =
        fun w => D0 / 2 * dualDriftY (ofFlat q w) j := by
      funext w; exact Fin.append_right _ _ _
    rw [e]
    exact contDiffAt_const.mul ((contDiffAt_dualDriftY hw j).comp w
      (ofFlat q).contDiff.contDiffAt)

/-- **The flat drift is locally Lipschitz on the chamber.** -/
theorem locallyLipschitzOn_flatDrift (D0 : ℝ) :
    LocallyLipschitzOn (flatChamber q) (flatDrift D0 q) := by
  intro w hw
  obtain ⟨K, t, ht, hK⟩ :=
    ((contDiffAt_flatDrift D0 hw).of_le (by norm_num)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

theorem contDiff_flatDiffDiag (D0 : ℝ) (k : Fin (q + q)) :
    ContDiff ℝ (⊤ : ℕ∞) fun w => flatDiffDiag D0 q w k := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · have e : (fun w => flatDiffDiag D0 q w (Fin.castAdd q i)) =
        fun w : Fin (q + q) → ℝ => D0 * (w (Fin.castAdd q i) * (1 + w (Fin.castAdd q i))) := by
      funext w; simp only [flatDiffDiag, Fin.append_left, ofFlat_apply]
    rw [e]
    have c := contDiff_apply ℝ ℝ (n := (⊤ : ℕ∞)) (Fin.castAdd q i)
    exact contDiff_const.mul (c.mul (contDiff_const.add c))
  · have e : (fun w => flatDiffDiag D0 q w (Fin.natAdd q j)) =
        fun w : Fin (q + q) → ℝ => D0 * (w (Fin.natAdd q j) * (1 - w (Fin.natAdd q j))) := by
      funext w; simp only [flatDiffDiag, Fin.append_right, ofFlat_apply]
    rw [e]
    have c := contDiff_apply ℝ ℝ (n := (⊤ : ℕ∞)) (Fin.natAdd q j)
    exact contDiff_const.mul (c.mul (contDiff_const.sub c))

theorem diagonal_eq_sum_single {n : ℕ} (d : Fin n → ℝ) :
    Matrix.diagonal d = ∑ k, d k • Matrix.single k k (1 : ℝ) := by
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right_iff.2 fun h' => absurd h' h]
    refine (Finset.sum_eq_zero fun (x : Fin n) _ => ?_).symm
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff, and_imp]
    rintro rfl rfl
    exact absurd rfl h

/-- **The flat diffusion is `C^∞`** (for the Frobenius normed structure on matrices). -/
theorem contDiff_flatDiff (D0 : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (flatDiff D0 q) := by
  have e : flatDiff D0 q = fun w => ∑ k, flatDiffDiag D0 q w k • Matrix.single k k (1 : ℝ) := by
    funext w; exact diagonal_eq_sum_single _
  rw [e]
  exact ContDiff.sum fun k _ => (contDiff_flatDiffDiag D0 k).smul contDiff_const

theorem contDiffOn_flatDiff (D0 : ℝ) : ContDiffOn ℝ 2 (flatDiff D0 q) (flatChamber q) :=
  ((contDiff_flatDiff D0).of_le (by simp)).contDiffOn

theorem continuousOn_flatDrift (D0 : ℝ) : ContinuousOn (flatDrift D0 q) (flatChamber q) :=
  (locallyLipschitzOn_flatDrift D0).continuousOn

end BlockBand.Transmission.Dual
