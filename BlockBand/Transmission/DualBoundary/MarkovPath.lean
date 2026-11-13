module

public import BlockBand.Transmission.DualBoundary.PathOne
public import BlockBand.Transmission.Dual.UniqueShift

/-!
# Markov property, pathwise part: shifting a one-pair boundary path

Deterministic paths; no measure. For an `IsBoundaryDeletionPath n x y` with `n 0 = 1`:
* `isDeletionPath_shift_boundary`: shifted by `r > 0` and truncated, it is an `IsDeletionPath`
  (the chamber condition is only lost at time `0`); the boundary analogue of
  `Dual.isDeletionPath_shift`.
* `continuous_lift`: `u ↦ dualLift F (n u) (x u) (y u)` is continuous for a continuous level-one
  test with `F 0 = 0` (it is `F(Z̄_u)`).
* **`dualMartingale_shift_one`**: at a time `r` of level one, the level-one martingale of the
  shifted truncated path is `M_{r+s} − M_r` (the boundary analogue of
  `Dual.dualMartingale_shift`, at the top level `q = p = 1`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

/-- **A boundary path shifted by `r > 0` (and truncated) is a deletion path.** -/
theorem isDeletionPath_shift_boundary (hP : IsBoundaryDeletionPath n x y) {r : ℝ≥0}
    (hr : 0 < r) :
    IsDeletionPath (fun s => n (r + s)) (fun s => truncCoord (n (r + s)) (x (r + s)))
      (fun s => truncCoord (n (r + s)) (y (r + s))) where
  antitone _ _ h := hP.antitone ((add_le_add_iff_left r).2 h)
  chamber t := by
    show dualCoordOf _ (truncCoord _ _) (truncCoord _ _) ∈ _
    rw [dualCoordOf_trunc]; exact hP.chamber (r + t) (lt_of_lt_of_le hr le_self_add)
  rightCont t := (tendsto_add_nhdsGT r t).eventually (hP.rightCont (r + t))
  cont t₁ t₂ h12 he i hi := by
    have hconst : ∀ u ∈ Icc t₁ t₂, n (r + u) = n (r + t₁) := fun u hu =>
      le_antisymm (hP.antitone ((add_le_add_iff_left r).2 hu.1))
        (he ▸ hP.antitone ((add_le_add_iff_left r).2 hu.2))
    obtain ⟨hcx, hcy⟩ := hP.cont (r + t₁) (r + t₂) ((add_le_add_iff_left r).2 h12) he i hi
    have hmaps : MapsTo (r + ·) (Icc t₁ t₂) (Icc (r + t₁) (r + t₂)) := fun u hu =>
      ⟨(add_le_add_iff_left r).2 hu.1, (add_le_add_iff_left r).2 hu.2⟩
    have hc : ContinuousOn (r + ·) (Icc t₁ t₂) := (continuous_const.add continuous_id).continuousOn
    refine ⟨(hcx.comp hc hmaps).congr fun u hu => ?_, (hcy.comp hc hmaps).congr fun u hu => ?_⟩
    · simp only [Function.comp_apply]; rw [hconst u hu, truncCoord_of_lt _ hi]
    · simp only [Function.comp_apply]; rw [hconst u hu, truncCoord_of_lt _ hi]
  deletion τ hτ q hev hne := by
    obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ).1 hev
    have hev' : ∀ᶠ u in 𝓝[<] (r + τ), n u = q + 1 := by
      have hlt : r + a < r + τ := (add_lt_add_iff_left r).2 ha
      filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
      have hru : r ≤ u := le_trans (le_add_right le_rfl) hu.1.le
      have := hsub (show u - r ∈ Ioo a τ from ⟨lt_tsub_iff_left.2 hu.1,
        (tsub_lt_iff_left hru).2 hu.2⟩)
      simpa [add_tsub_cancel_of_le hru] using this
    obtain ⟨h1, hx0, hy0, hs⟩ := hP.deletion (r + τ) (by positivity) q hev' hne
    have hev2 : ∀ᶠ u in 𝓝[<] τ, n (r + u) = q + 1 := hev
    refine ⟨h1, ?_, ?_, fun i hi => ?_⟩
    · refine ((hx0.comp (tendsto_add_nhdsLT r τ))).congr' ?_
      filter_upwards [hev2] with u hu
      simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (Nat.succ_pos q)]
    · refine ((hy0.comp (tendsto_add_nhdsLT r τ))).congr' ?_
      filter_upwards [hev2] with u hu
      simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (Nat.succ_pos q)]
    · obtain ⟨hxs, hys⟩ := hs i hi
      have hi' : i < n (r + τ) := h1 ▸ hi
      rw [truncCoord_of_lt _ hi', truncCoord_of_lt _ hi']
      refine ⟨(hxs.comp (tendsto_add_nhdsLT r τ)).congr' ?_,
        (hys.comp (tendsto_add_nhdsLT r τ)).congr' ?_⟩ <;>
      · filter_upwards [hev2] with u hu
        simp only [Function.comp_apply]; rw [hu, truncCoord_of_lt _ (by omega)]

theorem zero_notMem_dualChamber_one : (0 : DualCoord 1) ∉ dualChamber 1 := fun h =>
  lt_irrefl _ (h.2.2.1 0)

/-- Along a one-pair boundary path, a level-one lift is the test evaluated at `Z̄`. -/
theorem dualLift_eq_trunc (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    {F : DualCoord 1 → ℝ} (hF : F 0 = 0) (u : ℝ≥0) :
    dualLift F (n u) (x u) (y u) =
      F (fun _ => truncDualCoord (n u) (x u) 0, fun _ => truncDualCoord (n u) (y u) 0) := by
  rcases level_eq_one_or_zero hP h0 u with h | h
  · have e : dualCoordOf 1 (x u) (y u) =
        (fun _ => truncDualCoord (n u) (x u) 0, fun _ => truncDualCoord (n u) (y u) 0) := by
      ext i <;> rw [Fin.fin_one_eq_zero i] <;> simp [dualCoordOf, truncDualCoord, h]
    have hl : dualLift F (n u) (x u) (y u) = F (dualCoordOf 1 (x u) (y u)) := by
      simp [dualLift, h]
    rw [hl, e]
  · have e : ((fun _ => truncDualCoord (n u) (x u) 0, fun _ => truncDualCoord (n u) (y u) 0) :
        DualCoord 1) = 0 := by
      ext i <;> simp [truncDualCoord, h]
    rw [e, hF]; simp [dualLift, h]

theorem continuous_lift (hP : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    {F : DualCoord 1 → ℝ} (hFc : Continuous F) (hF : F 0 = 0) :
    Continuous fun u => dualLift F (n u) (x u) (y u) := by
  simp_rw [dualLift_eq_trunc hP h0 hF]
  exact hFc.comp ((continuous_pi fun _ => continuous_truncX hP h0).prodMk
    (continuous_pi fun _ => continuous_truncY hP h0))

section Mart

variable {Ω Ω' : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ} {ω : Ω} {D0 : ℝ}
  {f : DualCoord 1 → ℝ}

/-- **Shift of the level-one martingale along a boundary path**, at a time `r` of level one. -/
theorem dualMartingale_shift_one
    (hP : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ dualChamber 1) {r : ℝ≥0} (hr : N r ω = 1)
    {N' : ℝ≥0 → Ω' → ℕ} {X' Y' : ℝ≥0 → Ω' → ℕ → ℝ} {ω' : Ω'}
    (hN' : ∀ s, N' s ω' = N (r + s) ω)
    (hX' : ∀ s, X' s ω' = truncCoord (N (r + s) ω) (X (r + s) ω))
    (hY' : ∀ s, Y' s ω' = truncCoord (N (r + s) ω) (Y (r + s) ω)) (s : ℝ≥0) :
    dualMartingale D0 1 f N' X' Y' s ω' =
      dualMartingale D0 1 f N X Y (r + s) ω - dualMartingale D0 1 f N X Y r ω := by
  have hlift : ∀ (F : DualCoord 1 → ℝ) (u : ℝ≥0),
      dualLift F (N' u ω') (X' u ω') (Y' u ω') = dualLift F (N (r + u) ω) (X (r + u) ω)
        (Y (r + u) ω) := fun F u => by rw [hN', hX', hY', dualLift_trunc]
  have hEV : ∀ t, dualEntranceValue f N X Y t ω = f (dualCoordOf 1 (X 0 ω) (Y 0 ω)) :=
    fun t => dualEntranceValue_of_start f t ω h0
  have hN'0 : N' 0 ω' = 1 := by rw [hN', add_zero, hr]
  have hEV' : dualEntranceValue f N' X' Y' s ω' = dualLift f (N r ω) (X r ω) (Y r ω) := by
    have h := hlift f 0
    rw [add_zero] at h
    rw [dualEntranceValue_of_start f s ω' hN'0, ← h]
    simp [dualLift, hN'0]
  have hgen := continuous_dualGenerator D0 hf hfs
  obtain ⟨C, hC⟩ := hgen.bounded_above_of_compact_support (hasCompactSupport_dualGenerator D0 hfc)
  have hGc : Continuous fun u => dualLift (dualGenerator D0 f) (N u ω) (X u ω) (Y u ω) :=
    continuous_lift hP h0 hgen (dualGenerator_eq_zero_of_notMem_tsupport
      (fun h => zero_notMem_dualChamber_one (hfs h)))
  have hsh := setIntegral_Ioc_shift
    (G := fun u => dualLift (dualGenerator D0 f) (N u ω) (X u ω) (Y u ω))
    (fun t => hGc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (fun _ => norm_dualLift_le hC _ _ _) r s
  have hI : ∫ u in Ioc (0 : ℝ) s, dualLift (dualGenerator D0 f) (N' u.toNNReal ω')
      (X' u.toNNReal ω') (Y' u.toNNReal ω') = ∫ u in Ioc (0 : ℝ) s,
      dualLift (dualGenerator D0 f) (N (r + u.toNNReal) ω) (X (r + u.toNNReal) ω)
        (Y (r + u.toNNReal) ω) := by
    simp_rw [hlift]
  rw [dualMartingale, dualMartingale, dualMartingale, hEV, hEV, hEV', hlift, hI, hsh]
  ring

end Mart

end BlockBand.Transmission.DualBoundary
