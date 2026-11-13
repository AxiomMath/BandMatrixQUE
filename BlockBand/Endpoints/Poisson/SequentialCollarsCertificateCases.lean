module

public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateNetwork

/-!
# The sequential-collars lemma, item (ii): the two network cases

The deterministic part of item (ii) splits into two cases, according to how the two selected
ports sit on the old network.

* `case1_network` (both selected ports on one path: cyclic pairing at its first stage or when the
  right path closes on the selected collar, and every stage of the box pairing): `d(X₀) = d(path)`,
  `g₀ = 0`.
* `case2_network` (each selected port on its own path ending at a previously matched port):
  `d(X₀) ≤ max(d_R, d_L)`, `g₀ = g_R + g_L`; `cyclic_left_ne` shows the left path then also ends
  at a matched port.
* `certificate_on_event`: both cases, for the concrete incident runs `compRunR`, `compRunL`, on the
  event that the samples are Hermitian and the real inverses exist.
* `boundaryZ_im_pos`: the matched value has positive imaginary part in the bulk.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers (PathSample pathMatrix pathPortCoupling pathSchur
  pathPortResolvent boundaryZ matchedA matchedDistance)
open BlockBand.Internal.Contracts.TransmissionPath (portBlock)
open BlockBand.Internal.Contracts.Critical (conductance)

/-- `Im z_∂(E) = (1-b)√(4-E²)/2 > 0` in the bulk. -/
theorem boundaryZ_im_pos {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    0 < (boundaryZ b E).im := by
  have h4 : 0 < 4 - E ^ 2 := by nlinarith
  have hs : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt h4.le
  have hspos : 0 < Real.sqrt (4 - E ^ 2) := Real.sqrt_pos.mpr h4
  have hn : Complex.normSq (matchedA E) = 1 := by
    simp only [matchedA, Complex.normSq_mk]
    nlinarith [hs]
  simp only [boundaryZ, Complex.add_im, Complex.inv_im, hn, div_one, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  simp only [matchedA]
  nlinarith

section Cases

variable {m n W : ℕ} {L : Fin m → ℕ} {s : ZMod n}

theorem outerStageSite_eq_comp (hL : IsCollarLayout n L) {π : Pairing} {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r) {j₁ j₂ : Fin m}
    (hl : p₀ - 1 = unitPos n L s j₁ 2) (hr : runRight L s π p₀ r = unitPos n L s j₂ 0)
    (i : Fin 2) (c : Fin 2) (a : Fin W)
    (hpos : outerPos L s k i = if c = 0 then p₀ - 1 else runRight L s π p₀ r) :
    outerStageSite (s := s) hL hk (i, a) = (runCompMap hL h hl hr (Sum.inr (c, a))).1 :=
  Subtype.ext (Prod.ext hpos rfl)

/-- The right incident run of each pairing (the complementary path `k` for the box pairing). -/
def compRunR (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m)) (k : Fin m) :
    ZMod n × ℕ :=
  match π with
  | .box => (unitPos n L s k 3, L k)
  | .cyclic => (unitPos n L s k 3, rightLen L s hL S k)

/-- The left incident run of each pairing. -/
def compRunL (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m)) (k : Fin m) :
    ZMod n × ℕ :=
  match π with
  | .box => (unitPos n L s k 3, L k)
  | .cyclic => (unitPos n L s k 0 - (leftLen L s hL S k : ZMod n), leftLen L s hL S k)

theorem compRunR_isOldRun (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) :
    IsOldRun L s π S k (compRunR (s := s) hL π S k).1 (compRunR (s := s) hL π S k).2 := by
  cases π
  · exact isOldRun_cyclic_right hL S k
  · exact isOldRun_box hL S k

theorem compRunL_isOldRun (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) :
    IsOldRun L s π S k (compRunL (s := s) hL π S k).1 (compRunL (s := s) hL π S k).2 := by
  cases π
  · exact isOldRun_cyclic_left hL S k
  · exact isOldRun_box hL S k

/-- The zero-source old Schur matrix `X₀` at the matched value `z_b(e)`. -/
abbrev oldX0 [NeZero n] (L : Fin m → ℕ) (s : ZMod n) (π : Pairing) (S : Finset (Fin m)) (k : Fin m)
    (b e : ℝ) (buf : ℕ) (ω : RingCoords n W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  oldSchur (oldInterior L s π S k e (boundaryZ b e) buf 0 ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω)
    (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω)ᴴ

theorem runSample_hermitian {p₀ : ZMod n} {r : ℕ} {ω : RingCoords n W}
    (hA : ∀ p, (ω.1 p).IsHermitian) : ∀ i, ((runSample (W := W) p₀ r ω).1 i).IsHermitian :=
  fun _ => hA _

/-- **Case 1** (both selected ports on one Gaussian path). -/
theorem case1_network [NeZero n] (hL : IsCollarLayout n L) {π : Pairing} {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r)
    (hl : p₀ - 1 = unitPos n L s k 2) (hr : runRight L s π p₀ r = unitPos n L s k 0)
    {b e : ℝ} (hz : 0 < (boundaryZ b e).im) (buf : ℕ) (ω : RingCoords n W)
    (hA : ∀ p, (ω.1 p).IsHermitian)
    (hM : IsUnit (oldInterior L s π S k e (boundaryZ b e) buf 0 ω).det)
    (hP : IsUnit (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1).det) :
    matchedDistance b e (oldX0 L s π S k b e buf ω) =
        matchedDistance b e (pathSchur e (runSample p₀ r ω)) ∧
      conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω)) = 0 := by
  have hIm := oldInterior_numRange (L := L) (s := s) π S k e (boundaryZ b e) buf ω hA (le_refl 0)
    hz.le
  have hX := isUnit_det_sub_oldSchur _ (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω) hM hIm hz
  obtain ⟨hRout, hN⟩ := outerResolvent_eq hL hk π e (boundaryZ b e) buf 0 ω hM hX
  obtain ⟨hres, -⟩ := runComp_resolvent hL h (Finset.mem_insert_self k S) hl
    (Finset.mem_insert_self k S) hr e hz buf ω hN hP (runSample_hermitian hA)
  refine case1_conclusions b e hz (pathSchur_isHermitian e _ (runSample_hermitian hA)) ?_
  rw [hRout]
  ext ⟨i, a⟩ ⟨i', a'⟩
  have hpos : ∀ i : Fin 2, outerPos L s k i =
      if (Equiv.swap (0 : Fin 2) 1 i) = 0 then p₀ - 1 else runRight L s π p₀ r := by
    intro c; fin_cases c
    · simp [outerPos, hr]
    · simp [outerPos, hl]
  simp only [submatrix_apply]
  rw [outerStageSite_eq_comp hL hk h hl hr i _ a (hpos i),
    outerStageSite_eq_comp hL hk h hl hr i' _ a' (hpos i')]
  exact hres _ _

/-- **Case 2** (each selected port on its own Gaussian path, ending at a previously
matched port). -/
theorem case2_network [NeZero n] (hL : IsCollarLayout n L) {π : Pairing} {S : Finset (Fin m)}
    {k : Fin m} (hk : k ∉ S) {pR pL : ZMod n} {rR rL : ℕ} {jR jL : Fin m}
    (hR : IsOldRun L s π S k pR rR) (hlR : pR - 1 = unitPos n L s k 2) (hjR : jR ∈ S)
    (hrR : runRight L s π pR rR = unitPos n L s jR 0)
    (hLr : IsOldRun L s π S k pL rL) (hlL : pL - 1 = unitPos n L s jL 2) (hjL : jL ∈ S)
    (hrL : runRight L s π pL rL = unitPos n L s k 0)
    {b e : ℝ} (hz : 0 < (boundaryZ b e).im) (buf : ℕ) (ω : RingCoords n W)
    (hA : ∀ p, (ω.1 p).IsHermitian)
    (hM : IsUnit (oldInterior L s π S k e (boundaryZ b e) buf 0 ω).det)
    (hPR : IsUnit (pathMatrix (runSample pR rR ω) - (e : ℂ) • 1).det)
    (hPL : IsUnit (pathMatrix (runSample pL rL ω) - (e : ℂ) • 1).det) :
    matchedDistance b e (oldX0 L s π S k b e buf ω) ≤
        max (matchedDistance b e (pathSchur e (runSample pR rR ω)))
          (matchedDistance b e (pathSchur e (runSample pL rL ω))) ∧
      conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω)) =
        nearConductance b e (pathSchur e (runSample pR rR ω)) +
          nearConductance b e (pathSchur e (runSample pL rL ω)) := by
  have hLk := hL.2 k
  have hIm := oldInterior_numRange (L := L) (s := s) π S k e (boundaryZ b e) buf ω hA (le_refl 0)
    hz.le
  have hX := isUnit_det_sub_oldSchur _ (oldCoupling L s π S k e (boundaryZ b e) buf 0 ω) hM hIm hz
  obtain ⟨hRout, hN⟩ := outerResolvent_eq hL hk π e (boundaryZ b e) buf 0 ω hM hX
  obtain ⟨resR, crossR⟩ := runComp_resolvent hL hR (Finset.mem_insert_self k S) hlR
    (Finset.mem_insert_of_mem hjR) hrR e hz buf ω hN hPR (runSample_hermitian hA)
  obtain ⟨resL, -⟩ := runComp_resolvent hL hLr (Finset.mem_insert_of_mem hjL) hlL
    (Finset.mem_insert_self k S) hrL e hz buf ω hN hPL (runSample_hermitian hA)
  have hjRk : jR ≠ k := fun h => hk (h ▸ hjR)
  have hin1 : ∀ a : Fin W, InRunComp L s π pR rR (outerStageSite (s := s) hL hk (1, a)).1 :=
    fun a => Or.inr (Or.inl hlR.symm)
  have hout0 : ∀ a : Fin W, ¬ InRunComp L s π pR rR (outerStageSite (s := s) hL hk (0, a)).1 := by
    intro a hK
    rcases hK with ⟨i, hi, he⟩ | he | he
    · exact hR.avoid i hi ⟨k, Finset.mem_insert_self k S, Or.inl he.symm⟩
    · change unitPos n L s k 0 = pR - 1 at he
      rw [hlR] at he
      exact unitPos_ne hL (by omega) (by omega) (by norm_num) he
    · change unitPos n L s k 0 = runRight L s π pR rR at he
      rw [hrR] at he
      have := hL.2 jR
      exact hjRk ((unitPos_inj hL s (by omega) (by omega)).mp he).1.symm
  have hRout' : (boundaryZ b e • 1 - oldX0 L s π S k b e buf ω)⁻¹ = _ := hRout
  refine case2_conclusions b e hz (pathSchur_isHermitian e _ (runSample_hermitian hA))
    (pathSchur_isHermitian e _ (runSample_hermitian hA)) ?_ ?_ ?_ ?_ <;> rw [hRout']
  · ext a a'
    simp only [portBlock, Matrix.of_apply, submatrix_apply]
    rw [outerStageSite_eq_comp hL hk hR hlR hrR 1 0 a (by simp [outerPos, hlR]),
      outerStageSite_eq_comp hL hk hR hlR hrR 1 0 a' (by simp [outerPos, hlR])]
    exact resR _ _
  · ext a a'
    simp only [portBlock, Matrix.of_apply, submatrix_apply]
    rw [outerStageSite_eq_comp hL hk hLr hlL hrL 0 1 a (by simp [outerPos, hrL]),
      outerStageSite_eq_comp hL hk hLr hlL hrL 0 1 a' (by simp [outerPos, hrL])]
    exact resL _ _
  · ext a a'
    simp only [portBlock, Matrix.of_apply, submatrix_apply, Matrix.zero_apply]
    exact (crossR _ _ (hin1 a') (hout0 a)).2
  · ext a a'
    simp only [portBlock, Matrix.of_apply, submatrix_apply, Matrix.zero_apply]
    exact (crossR _ _ (hin1 a) (hout0 a')).1

theorem runRight_cyclic_eq (p₀ : ZMod n) {r : ℕ} (hr : 1 ≤ r) :
    runRight L s .cyclic p₀ r = p₀ + (r : ZMod n) := by
  simp only [runRight, bondTarget]
  rw [Nat.cast_sub hr]; ring

/-- In the cyclic pairing, if the right path ends at a previously matched port, so does the left
path (it cannot close on the selected collar). -/
theorem cyclic_left_ne (hL : IsCollarLayout n L) {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S)
    {jR jL : Fin m} (hjR : jR ∈ S)
    (hrR : runRight L s .cyclic (unitPos n L s k 3) (rightLen L s hL S k) = unitPos n L s jR 0)
    (hlL : unitPos n L s k 0 - (leftLen L s hL S k : ZMod n) - 1 = unitPos n L s jL 2) :
    jL ≠ k := by
  intro hjk
  subst hjk
  have R := isOldRun_cyclic_right (s := s) hL S jL
  have Lr := isOldRun_cyclic_left (s := s) hL S jL
  have hpL := p₀_eq_of_left hlL
  have hrL := runRight_cyclic_left (s := s) hL S jL
  rw [runRight_cyclic_eq _ R.one_le] at hrR
  rw [runRight_cyclic_eq _ Lr.one_le, hpL] at hrL
  have hjRk : jR ≠ jL := fun h => hk (h ▸ hjR)
  rcases lt_trichotomy (rightLen L s hL S jL) (leftLen L s hL S jL) with hlt | heq | hgt
  · apply Lr.avoid _ hlt
    rw [hpL, hrR]
    exact ⟨jR, Finset.mem_insert_of_mem hjR, Or.inl rfl⟩
  · rw [heq, hrL] at hrR
    have := hL.2 jR; have := hL.2 jL
    exact hjRk ((unitPos_inj hL s (by omega) (by omega)).mp hrR).1.symm
  · apply R.avoid _ hgt
    rw [hrL]
    exact ⟨jL, Finset.mem_insert_self _ _, Or.inl rfl⟩

/-- **Item (ii), deterministic part.** On the event that all diagonal samples are Hermitian and
the real inverses `M₀⁻¹` (old interior at zero source) and `(H_path - e)⁻¹` of the two incident
runs exist, `d(X₀) ≤ max(d_R, d_L)` and `|g₀| ≤ |g_R| + |g_L|`, where `d_•` are the
matched-traces quantities of the two incident paths and `g_•` their near
conductances. -/
theorem certificate_on_event [NeZero n] (hL : IsCollarLayout n L) (π : Pairing)
    {S : Finset (Fin m)} {k : Fin m} (hk : k ∉ S) {b e : ℝ} (hz : 0 < (boundaryZ b e).im)
    (buf : ℕ) (ω : RingCoords n W) (hA : ∀ p, (ω.1 p).IsHermitian)
    (hM : IsUnit (oldInterior L s π S k e (boundaryZ b e) buf 0 ω).det)
    (hPR : IsUnit (pathMatrix (runSample (compRunR (s := s) hL π S k).1
      (compRunR (s := s) hL π S k).2 ω) - (e : ℂ) • 1).det)
    (hPL : IsUnit (pathMatrix (runSample (compRunL (s := s) hL π S k).1
      (compRunL (s := s) hL π S k).2 ω) - (e : ℂ) • 1).det) :
    matchedDistance b e (oldX0 L s π S k b e buf ω) ≤
        max (matchedDistance b e (pathSchur e (runSample (compRunR (s := s) hL π S k).1
            (compRunR (s := s) hL π S k).2 ω)))
          (matchedDistance b e (pathSchur e (runSample (compRunL (s := s) hL π S k).1
            (compRunL (s := s) hL π S k).2 ω))) ∧
      ‖conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω))‖ ≤
        ‖nearConductance b e (pathSchur e (runSample (compRunR (s := s) hL π S k).1
            (compRunR (s := s) hL π S k).2 ω))‖ +
          ‖nearConductance b e (pathSchur e (runSample (compRunL (s := s) hL π S k).1
            (compRunL (s := s) hL π S k).2 ω))‖ := by
  have h23 : unitPos n L s k 3 - 1 = unitPos n L s k 2 := by rw [← unitPos_succ]; ring
  have hcase1 : ∀ {p₀ : ZMod n} {r : ℕ} (h : IsOldRun L s π S k p₀ r),
      p₀ - 1 = unitPos n L s k 2 → runRight L s π p₀ r = unitPos n L s k 0 →
      IsUnit (pathMatrix (runSample p₀ r ω) - (e : ℂ) • 1).det →
      ∀ (dL gL : ℝ), matchedDistance b e (oldX0 L s π S k b e buf ω) ≤
          max (matchedDistance b e (pathSchur e (runSample p₀ r ω))) dL ∧
        ‖conductance (oldResponse (boundaryZ b e) (oldX0 L s π S k b e buf ω))‖ ≤
          ‖nearConductance b e (pathSchur e (runSample p₀ r ω))‖ + ‖gL‖ := by
    intro p₀ r h hl hr hP dL gL
    obtain ⟨h1, h2⟩ := case1_network hL hk h hl hr hz buf ω hA hM hP
    refine ⟨h1 ▸ le_max_left _ _, ?_⟩
    rw [h2, norm_zero]; positivity
  cases π
  · obtain ⟨jR, hjR, hrR⟩ := runRight_cyclic_right (s := s) hL S k
    by_cases hjk : jR = k
    · subst hjk
      exact hcase1 (compRunR_isOldRun hL .cyclic S jR) h23 hrR hPR _ _
    · have hjRS : jR ∈ S := (Finset.mem_insert.mp hjR).resolve_left hjk
      obtain ⟨jL, hjL, hlL⟩ := left_port_cyclic_left (s := s) hL S k
      have hjLk := cyclic_left_ne hL hk hjRS hrR hlL
      have hjLS : jL ∈ S := (Finset.mem_insert.mp hjL).resolve_left hjLk
      obtain ⟨h1, h2⟩ := case2_network hL hk (compRunR_isOldRun hL .cyclic S k) h23 hjRS hrR
        (compRunL_isOldRun hL .cyclic S k) hlL hjLS (runRight_cyclic_left hL S k) hz buf ω hA hM
        hPR hPL
      exact ⟨h1, h2 ▸ norm_add_le _ _⟩
  · exact hcase1 (compRunR_isOldRun hL .box S k) h23 (runRight_box hL k) hPR _ _

end Cases

end BlockBand.Endpoints
