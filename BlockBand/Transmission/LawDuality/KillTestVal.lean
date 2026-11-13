module

public import BlockBand.Transmission.Dual.TestProc

/-!
# The localized level-`q` martingale of a cutoff of a general test

The pathwise value of the localized level-`q` dual martingale for a cutoff `f` of an arbitrary test
`g`, up to the exit time of the region where the cutoff equals `g`
(`dualMartingale_eq_of_le_hit_test`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ}

/-- **Pathwise value of the localized martingale, for a cutoff `f` of an arbitrary test `g`**
(`f = g` on the open `O ⊇ {h ≥ 1/2}`): up to the exit `θ` of `{h > 1/2}`,
`M^f_r = (g(Z_r) − g(Z_{σ_q})) 1{σ_q ≤ r, σ_q < θ} − ∫_{(0,r]} 𝒟_q g(Z_u) 1{N_u = q} du`. -/
theorem dualMartingale_eq_of_le_hit_test {Ω : Type*} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {ω : Ω} (hP : IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (D0 : ℝ) (hq : 1 ≤ q) (hq0 : q ≤ N 0 ω) {h : DualCoord q → ℝ} (hh : Continuous h)
    (hh0 : ∀ z ∉ dualChamber q, h z = 0) {f g : DualCoord q → ℝ} {O : Set (DualCoord q)}
    (hO : IsOpen O) (hhO : ∀ z, 1 / 2 ≤ h z → z ∈ O) (hfO : EqOn f g O)
    {θ : WithTop ℝ≥0}
    (hθ : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < θ → 1 / 2 < testVal q h (N u ω) (X u ω) (Y u ω))
    {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) ≤ θ) :
    dualMartingale D0 q f N X Y r ω =
      (if entryTime (fun t => N t ω) q ≤ r ∧ entryTime (fun t => N t ω) q < θ then
        dualLift g (N r ω) (X r ω) (Y r ω) - dualLift g (N (entryTime (fun t => N t ω) q).untopA ω)
          (X (entryTime (fun t => N t ω) q).untopA ω) (Y (entryTime (fun t => N t ω) q).untopA ω)
      else 0) - ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 g) (N u.toNNReal ω)
          (X u.toNNReal ω) (Y u.toNNReal ω) := by
  set n : ℝ≥0 → ℕ := fun t => N t ω with hn
  by_cases hE : entryTime n q ≤ r
  · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hE)
    have hs' : entryTime n q = s := hs.symm
    have hsr : s ≤ r := WithTop.coe_le_coe.1 (hs' ▸ hE)
    have hns : n s = q := by
      rcases lt_or_eq_of_le hq0 with hlt | heq
      · exact level_entryTime hP hlt hs'
      · have h0 : entryTime n q ≤ (0 : ℝ≥0) := (entryTime_le_iff hP q 0).2 heq.ge
        rw [hs'] at h0
        have : s = 0 := le_antisymm (WithTop.coe_le_coe.1 h0) zero_le
        rw [this]; exact heq.symm
    have hent := dualEntranceValue_eq_of_entryTime hP f hs' r
    simp only [hsr, ↓reduceIte] at hent
    rw [hs']
    simp only [untopA_coe', WithTop.coe_le_coe, hsr, true_and]
    by_cases hsθ : (s : WithTop ℝ≥0) < θ
    · simp only [hsθ, ↓reduceIte]
      -- on `[s, r]` the level is `q` and `h ≥ 1/2`
      have key : ∀ u : ℝ≥0, s ≤ u → u ≤ r → n u = q ∧
          1 / 2 ≤ h (dualCoordOf q (X u ω) (Y u ω)) := by
        intro u hsu hur
        have hle : n u ≤ q := (entryTime_le_iff hP q u).1 (hs' ▸ WithTop.coe_le_coe.2 hsu)
        have hP12 : 1 / 2 ≤ testVal q h (n u) (X u ω) (Y u ω) := by
          rcases lt_or_eq_of_le ((WithTop.coe_le_coe.2 hur).trans hr) with hlt | heq
          · exact (hθ u hlt).le
          · have hupos : 0 < u := lt_of_le_of_lt zero_le
              (WithTop.coe_lt_coe.1 (lt_of_lt_of_le hsθ (heq ▸ le_rfl)))
            have hne : entryTime n q ≠ u := by
              rw [hs']; intro e; rw [e] at hsθ; exact (hsθ.ne heq).elim
            have : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hupos⟩
            refine ge_of_tendsto (tendsto_testVal_left_of_ne hP hh hh0 hq hupos hne) ?_
            filter_upwards [self_mem_nhdsWithin] with v hv
            exact (hθ v (lt_of_lt_of_le (WithTop.coe_lt_coe.2 hv) heq.le)).le
        have hnot : ¬ q < n u := not_lt.2 hle
        simp only [testVal, hnot, ↓reduceIte, add_zero] at hP12
        by_cases hnu : n u = q
        · refine ⟨hnu, ?_⟩
          simpa [dualLift, hnu] using hP12
        · simp [dualLift, hnu] at hP12; linarith
      have fR : ∀ u : ℝ≥0, s ≤ u → u ≤ r →
          dualLift f (N u ω) (X u ω) (Y u ω) = dualLift g (N u ω) (X u ω) (Y u ω) := by
        intro u hsu hur
        obtain ⟨h1, h2⟩ := key u hsu hur
        have h1' : N u ω = q := h1
        simp only [dualLift, h1', ↓reduceIte]
        exact hfO (hhO _ h2)
      have hint : ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 f) (N u.toNNReal ω)
          (X u.toNNReal ω) (Y u.toNNReal ω) = ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 g)
          (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
        have hur : u.toNNReal ≤ r := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
        by_cases hnu : N u.toNNReal ω = q
        · have hsu : s ≤ u.toNNReal := WithTop.coe_le_coe.1
            (hs' ▸ (entryTime_le_iff hP q _).2 hnu.le)
          obtain ⟨-, h2⟩ := key _ hsu hur
          have hch : dualCoordOf q (X u.toNNReal ω) (Y u.toNNReal ω) ∈ dualChamber q := by
            have := hP.chamber u.toNNReal
            rw [show n u.toNNReal = q from hnu] at this
            exact this
          simp only [dualLift, hnu, ↓reduceIte]
          exact dualGenerator_congr (hfO.eventuallyEq_of_mem (hO.mem_nhds (hhO _ h2)))
        · simp [dualLift, hnu]
      simp only [dualMartingale, hent, hint]
      rw [fR r hsr le_rfl, fR s le_rfl hsr]
    · simp only [hsθ, ↓reduceIte]
      have hrs : r = s := le_antisymm (WithTop.coe_le_coe.1 (hr.trans (not_lt.1 hsθ))) hsr
      subst hrs
      have hint : ∀ k : DualCoord q → ℝ, ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 k)
          (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
        intro k
        rw [integral_Ioc_eq_integral_Ioo]
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        have hur : u.toNNReal < r := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
        have : q < n u.toNNReal :=
          lt_level_of_lt_entryTime hP (by rw [hs']; exact WithTop.coe_lt_coe.2 hur)
        have this' : q < N u.toNNReal ω := this
        have hne : N u.toNNReal ω ≠ q := by omega
        simp [dualLift, hne]
      simp only [dualMartingale, hent, hint, sub_self]
  · have hgt : ∀ u ≤ r, q < n u := fun u hu => by
      by_contra hc
      exact hE (((entryTime_le_iff hP q u).2 (not_lt.1 hc)).trans (WithTop.coe_le_coe.2 hu))
    simp only [hE, false_and, ↓reduceIte]
    have h1 : N r ω ≠ q := (hgt r le_rfl).ne'
    have h2 : ¬ ∃ u ≤ r, N u ω ≤ q := fun ⟨u, hu, hle⟩ => absurd hle (not_le.2 (hgt u hu))
    have hint : ∀ k : DualCoord q → ℝ, ∫ u in Ioc (0 : ℝ) r, dualLift (dualGenerator D0 k)
        (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω) = 0 := by
      intro k
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      have hur : u.toNNReal ≤ r := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
      have hne : N u.toNNReal ω ≠ q := (hgt _ hur).ne'
      simp [dualLift, hne]
    simp only [dualMartingale, hint, sub_zero]
    simp [dualLift, h1, dualEntranceValue, h2]

end BlockBand.Transmission.LawDuality
