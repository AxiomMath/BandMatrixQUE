module

public import BlockBand.Transmission.Dual.UniqueShiftPath

/-!
# Gluing two deletion paths at a paired corner

* **`isDeletionPath_glue`**: a level-`(k+1)` chamber path on `[0, ρ)`, continuous there, whose
  left limit at `ρ` is the paired corner `(0, x̃; 0, ỹ)` with `(x̃, ỹ)` the start of a level-`k`
  deletion path `(n', x', y')`, glues with `(n', x', y')` shifted by `ρ` into a deletion path.
* `isDeletionPath_const_level`: a continuous chamber path that never leaves level `k + 1`
  (the case `ρ = ⊤`, and the constant path off the stage-1 good set).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

theorem tendsto_tsub_nhdsGT {ρ t : ℝ≥0} (h : ρ ≤ t) :
    Tendsto (· - ρ) (𝓝[>] t) (𝓝[>] (t - ρ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).tendsto t).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
  exact tsub_lt_tsub_right_of_le h hu

theorem tendsto_tsub_nhdsLT {ρ t : ℝ≥0} (h : ρ < t) :
    Tendsto (· - ρ) (𝓝[<] t) (𝓝[<] (t - ρ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.sub continuous_const).tendsto t).mono_left
    nhdsWithin_le_nhds, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT h] with u hu
  exact tsub_lt_tsub_right_of_le hu.1.le hu.2

variable {k : ℕ} {ρ : ℝ≥0} {xs ys : ℝ≥0 → ℕ → ℝ} {n' : ℝ≥0 → ℕ} {x' y' : ℝ≥0 → ℕ → ℝ}

open scoped Classical in
/-- **Gluing at the corner.** -/
theorem isDeletionPath_glue
    (hch : ∀ t < ρ, dualCoordOf (k + 1) (xs t) (ys t) ∈ dualChamber (k + 1))
    (hc : ∀ i < k + 1, ContinuousOn (fun u => xs u i) (Iio ρ) ∧
      ContinuousOn (fun u => ys u i) (Iio ρ))
    (hx0 : Tendsto (fun u => xs u 0) (𝓝[<] ρ) (𝓝 0))
    (hy0 : Tendsto (fun u => ys u 0) (𝓝[<] ρ) (𝓝 0))
    (hs : ∀ i < k, Tendsto (fun u => xs u (i + 1)) (𝓝[<] ρ) (𝓝 (x' 0 i)) ∧
      Tendsto (fun u => ys u (i + 1)) (𝓝[<] ρ) (𝓝 (y' 0 i)))
    (hP : IsDeletionPath n' x' y') (hn0 : n' 0 = k) :
    IsDeletionPath (fun t => if t < ρ then k + 1 else n' (t - ρ))
      (fun t => if t < ρ then xs t else x' (t - ρ))
      (fun t => if t < ρ then ys t else y' (t - ρ)) where
  antitone a b hab := by
    by_cases hb : b < ρ
    · simp [hb, hab.trans_lt hb]
    · by_cases ha : a < ρ
      · simp only [ha, hb, ↓reduceIte]
        have := hP.antitone (zero_le : (0 : ℝ≥0) ≤ b - ρ); rw [hn0] at this; omega
      · simp only [ha, hb, ↓reduceIte]; exact hP.antitone (tsub_le_tsub_right hab ρ)
  chamber t := by
    by_cases ht : t < ρ
    · simp only [ht, ↓reduceIte]
      generalize hm : (if t < ρ then k + 1 else n' (t - ρ)) = m
      obtain rfl : m = k + 1 := hm ▸ ite_eq_left ht
      exact hch t ht
    · simp only [ht, ↓reduceIte]
      generalize hm : (if t < ρ then k + 1 else n' (t - ρ)) = m
      obtain rfl : m = n' (t - ρ) := hm ▸ ite_eq_right ht
      exact hP.chamber (t - ρ)
  rightCont t := by
    by_cases ht : t < ρ
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds ht)] with u hu
      simp only [show u < ρ from hu, ht, ↓reduceIte]
    · filter_upwards [(tendsto_tsub_nhdsGT (not_lt.1 ht)).eventually (hP.rightCont (t - ρ)),
        self_mem_nhdsWithin] with u hu hut
      have hu' : ¬ u < ρ := fun h => ht ((show t < u from hut).trans h)
      simp only [hu', ht, ↓reduceIte]; exact hu
  cont t₁ t₂ h12 he i hi := by
    by_cases h2 : t₂ < ρ
    · have h1 : t₁ < ρ := h12.trans_lt h2
      simp only [h1, ↓reduceIte] at hi
      have hsub : Icc t₁ t₂ ⊆ Iio ρ := fun u hu => hu.2.trans_lt h2
      refine ⟨((hc i hi).1.mono hsub).congr fun u hu => ?_,
        ((hc i hi).2.mono hsub).congr fun u hu => ?_⟩ <;>
        simp only [show u < ρ from hsub hu, ↓reduceIte]
    · by_cases h1 : t₁ < ρ
      · exfalso
        simp only [h1, h2, ↓reduceIte] at he
        have := hP.antitone (zero_le : (0 : ℝ≥0) ≤ t₂ - ρ); rw [hn0] at this; omega
      · simp only [h1, h2, ↓reduceIte] at he hi
        obtain ⟨hx, hy⟩ := hP.cont (t₁ - ρ) (t₂ - ρ) (tsub_le_tsub_right h12 ρ) he i hi
        have hm : MapsTo (· - ρ) (Icc t₁ t₂) (Icc (t₁ - ρ) (t₂ - ρ)) := fun u hu =>
          ⟨tsub_le_tsub_right hu.1 ρ, tsub_le_tsub_right hu.2 ρ⟩
        have hcs : ContinuousOn (· - ρ) (Icc t₁ t₂) :=
          (continuous_id.sub continuous_const).continuousOn
        have hu : ∀ u ∈ Icc t₁ t₂, ¬ u < ρ := fun u hu h => h1 (hu.1.trans_lt h)
        refine ⟨(hx.comp hcs hm).congr fun u hu' => ?_, (hy.comp hcs hm).congr fun u hu' => ?_⟩ <;>
          simp only [hu u hu', ↓reduceIte, Function.comp_apply]
  deletion τ hτ q hev hne := by
    have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
    rcases lt_trichotomy τ ρ with hlt | heq | hgt
    · exfalso
      have hev' : ∀ᶠ u in 𝓝[<] τ, u < ρ := eventually_nhdsWithin_of_forall fun u hu =>
        (show u < τ from hu).trans hlt
      obtain ⟨u, hu1, hu2⟩ := (hev.and hev').exists
      simp only [hu2, hlt, ↓reduceIte] at hu1 hne
      exact hne hu1
    · subst heq
      have hev' : ∀ᶠ u in 𝓝[<] τ, u < τ := self_mem_nhdsWithin
      obtain ⟨u, hu1, hu2⟩ := (hev.and hev').exists
      simp only [hu2, ↓reduceIte] at hu1
      have hqk : q = k := by omega
      subst hqk
      simp only [lt_irrefl, ↓reduceIte, tsub_self]
      refine ⟨hn0, hx0.congr' ?_, hy0.congr' ?_, fun i hi => ⟨(hs i hi).1.congr' ?_,
        (hs i hi).2.congr' ?_⟩⟩ <;>
      · filter_upwards [hev'] with u hu
        simp only [hu, ↓reduceIte]
    · have hτ' : 0 < τ - ρ := tsub_pos_of_lt hgt
      have hgtev : ∀ᶠ u in 𝓝[<] τ, ρ < u := Ioo_mem_nhdsLT hgt |> fun h =>
        Filter.mem_of_superset h fun u hu => hu.1
      have hsh : ∀ᶠ v in 𝓝[<] (τ - ρ), n' v = q + 1 := by
        have ht := tendsto_add_nhdsLT ρ (τ - ρ)
        rw [add_tsub_cancel_of_le hgt.le] at ht
        filter_upwards [ht.eventually hev] with v hv
        have : ¬ ρ + v < ρ := not_lt.2 le_self_add
        simpa [this] using hv
      have hnτ : ¬ τ < ρ := not_lt.2 hgt.le
      simp only [hnτ, ↓reduceIte] at hne ⊢
      obtain ⟨h1, hx, hy, hs'⟩ := hP.deletion (τ - ρ) hτ' q hsh hne
      have hT := tendsto_tsub_nhdsLT hgt
      have hc : ∀ (g g' : ℝ≥0 → ℕ → ℝ) (j : ℕ),
          (fun u => (if u < ρ then g u else g' (u - ρ)) j) =ᶠ[𝓝[<] τ] fun u => g' (u - ρ) j :=
        fun g g' j => by
          filter_upwards [hgtev] with u hu
          simp only [not_lt.2 hu.le, ↓reduceIte]
      refine ⟨h1, (hx.comp hT).congr' (hc (fun u => xs u) x' 0).symm,
        (hy.comp hT).congr' (hc (fun u => ys u) y' 0).symm, fun i hi =>
        ⟨((hs' i hi).1.comp hT).congr' (hc (fun u => xs u) x' (i + 1)).symm,
          ((hs' i hi).2.comp hT).congr' (hc (fun u => ys u) y' (i + 1)).symm⟩⟩

/-- **A path that stays at level `k + 1`.** -/
theorem isDeletionPath_const_level
    (hch : ∀ t, dualCoordOf (k + 1) (xs t) (ys t) ∈ dualChamber (k + 1))
    (hc : ∀ i < k + 1, Continuous (fun u => xs u i) ∧ Continuous (fun u => ys u i)) :
    IsDeletionPath (fun _ => k + 1) xs ys where
  antitone _ _ _ := le_rfl
  chamber := hch
  rightCont _ := Eventually.of_forall fun _ => rfl
  cont _ _ _ _ i hi := ⟨(hc i hi).1.continuousOn, (hc i hi).2.continuousOn⟩
  deletion τ hτ q hev hne := by
    have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
    obtain ⟨u, hu⟩ := hev.exists
    exact (hne hu).elim

end BlockBand.Transmission.Dual.G
