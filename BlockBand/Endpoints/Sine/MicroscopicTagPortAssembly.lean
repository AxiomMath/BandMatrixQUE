module

public import BlockBand.Endpoints.Sine.MicroscopicTagAssemblyPrior

/-!
# The Gaussian field at a fixed energy as the ported field, and block-`0` deletion

* `mts_gauss_eq_port`: the Gaussian field `Γ₀` is the ported field, through
  `LeadFieldIdentificationContract`.
* `mts_sum_portClock`: the ported block clocks are `‖Hg‖²` at block `0` and the `n - 1` lead
  masses at the blocks `leadRingBlock y` (a bijection onto the nonzero blocks).
* `mts_deletion`, `mts_port_deletion`: `|Ψ_main(clocks) - leadAveragedTest| ≤ 2 Lip(Φ) ρ₀`,
  `ρ₀ = ‖Hg‖²/(‖Hg‖² + h*Y^{all}h)`, and `ρ₀` is at most the three-tag test of the clocks.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Clocks BlockBand.Internal.Contracts.ClocksCommonPort
open BlockBand.Internal.Contracts.ClocksLeadProfile BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

/-!
## The Gaussian field `Γ₀` is the ported field
-/

/-- The Gaussian field `Γ₀` is the ported field, at a bulk energy, for a tag test that is a
scale-invariant bounded measurable function `Ψ` of the block clocks of the lifted field (exposed
block `0`). Input: `LeadFieldIdentificationContract` (through
`microscopicTagFieldIdentity_of_contract`). -/
theorem mts_gauss_eq_port (hL : LeadFieldIdentificationContract) (p : Parameters)
    {model : p.GaussianRingModel} {Pω : Measure (BlockState p 0)}
    (hs : IsBlockSplitting p 0 model Pω) (σ : BlockSite p 0 ≃ Fin (Fintype.card (BlockSite p 0)))
    {e : ℝ} (he1 : -2 < e) (he2 : e < 2) (q : ℕ)
    (Dt : ℝ × BlockState p 0 → Fin q → Matrix (Fin (Fintype.card (BlockSite p 0)))
      (Fin (Fintype.card (BlockSite p 0))) ℂ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    {Ψ : (ZMod p.n → ℝ) → ℝ} (hΨ : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, |Ψ x| ≤ C)
    (hglue : ∀ ω v, mts_tagTest q (Dt (e, ω)) Φ (v ∘ σ.symm) = Ψ (mts_fieldClock p 0 e ω v))
    (hsc : ∀ x, Ψ (fun j => p.c * x j) = Ψ x) :
    ∫ ω, mts_gaussTag p 0 σ q Dt Φ (e, ω) ∂Pω =
      ∫ y, Ψ (fun j => mts_portBlockClock p.b e p.n p.W y j) ∂mts_portLaw p.W p.b := by
  have hFP := microscopicTagFieldIdentity_of_contract hL p model 0 Pω hs e he1 he2
    (fun ω => blockFieldFactor p 0 ω e)
    (mts_measurable_blockFieldFactor_of p 0 measurable_id measurable_const)
    (fun ω => mts_blockFieldFactor_gram p 0 ω e) Ψ hΨ hΨb
  simp only [sub_zero, hsc] at hFP
  rw [← hFP]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have h1 : ∀ g : Fin (Fintype.card (BlockSite p 0)) → ℂ,
      mts_tagTest q (Dt (e, ω)) Φ (Matrix.reindex σ σ (blockFieldFactor p 0 ω e) *ᵥ g) =
        Ψ (mts_fieldClock p 0 e ω (blockFieldFactor p 0 ω e *ᵥ (g ∘ σ))) := by
    intro g; rw [mts_reindex_mulVec, hglue]
  have hm : Measurable fun g : BlockSite p 0 → ℂ =>
      Ψ (mts_fieldClock p 0 e ω (blockFieldFactor p 0 ω e *ᵥ g)) :=
    hΨ.comp (mts_measurable_fieldClock_of p 0 e measurable_const
      (mts_measurable_mulVec measurable_const measurable_id))
  simp only [mts_gaussTag, h1]
  rw [← mts_circularVectorLaw_map_comp σ]
  show _ = ∫ g, Ψ (mts_fieldClock p 0 e ω (blockFieldFactor p 0 ω e *ᵥ g))
    ∂(Measure.map (fun v => v ∘ σ) _)
  rw [integral_map (mts_measurable_comp_equiv σ).aemeasurable hm.aestronglyMeasurable]

/-!
## The ported block clocks
-/

theorem mts_leadRingBlock_lt (r : ℕ) (x : Fin r ⊕ Fin 2) : leadRingBlock r x < r + 3 := by
  rcases x with i | j
  · simp only [leadRingBlock]; omega
  · simp only [leadRingBlock]; split_ifs <;> omega

theorem mts_leadRingBlock_injective (r : ℕ) : Function.Injective (leadRingBlock r) := by
  intro x y h
  rcases x with i | i <;> rcases y with j | j <;> simp only [leadRingBlock] at h
  · exact congrArg _ (Fin.ext (by omega))
  · have := i.isLt; split_ifs at h <;> omega
  · have := j.isLt; split_ifs at h <;> omega
  · congr 1
    fin_cases i <;> fin_cases j <;> simp at h ⊢

theorem mts_leadPositionMass_nonneg (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (x : Fin r ⊕ Fin 2) : 0 ≤ leadPositionMass b e W r ω h x := by
  rcases x with i | j <;> exact Finset.sum_nonneg fun _ _ => sq_nonneg _

section PortLaw

variable (p : Parameters) (b e : ℝ)

/-- The block-`0` clock `‖Hg‖²` of the ported field. -/
def mts_portHMass (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ))) :
    ℝ :=
  ∑ a : Fin p.W, ‖(commonPortH b e (leadSchur e p.W (p.n - 3) y.1) y.2.1 *ᵥ y.2.2) (0, a)‖ ^ 2

/-- The lead masses of the transported probe `Lg`. -/
def mts_portLead (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ)))
    (x : Fin (p.n - 3) ⊕ Fin 2) : ℝ :=
  leadPositionMass b e p.W (p.n - 3) y.1 (commonPortProbe b e (leadSchur e p.W (p.n - 3) y.1) y.2)
    x

theorem mts_portBlockClock_zero
    (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ))) :
    mts_portBlockClock b e p.n p.W y 0 = mts_portHMass p b e y := by
  unfold mts_portBlockClock mts_portHMass
  have h1 : ∀ x', leadRingBlock (p.n - 3) x' ≠ 0 := fun x' => by
    have := mts_leadRingBlock_pos (p.n - 3) x'; omega
  simp only [ZMod.val_zero, ite_true, h1, ite_false, Finset.sum_const_zero, add_zero]

theorem mts_sum_portClock (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ)))
    (G : ℝ → ℝ) :
    ∑ j : ZMod p.n, G (mts_portBlockClock b e p.n p.W y j) =
      G (mts_portHMass p b e y) + ∑ x, G (mts_portLead p b e y x) := by
  classical
  have hn := p.n_ge_four
  set f : Fin (p.n - 3) ⊕ Fin 2 → ZMod p.n := fun x => ((leadRingBlock (p.n - 3) x : ℕ) : ZMod p.n)
  have hval : ∀ x, (f x).val = leadRingBlock (p.n - 3) x := fun x =>
    ZMod.val_cast_of_lt (by have := mts_leadRingBlock_lt (p.n - 3) x; omega)
  have hinj : Function.Injective f := fun x y h =>
    mts_leadRingBlock_injective _ (by rw [← hval, ← hval, h])
  have hf0 : ∀ x, f x ≠ 0 := fun x h => by
    have h1 := hval x
    rw [h, ZMod.val_zero] at h1
    have := mts_leadRingBlock_pos (p.n - 3) x
    omega
  have hcf : ∀ x, mts_portBlockClock b e p.n p.W y (f x) = mts_portLead p b e y x := by
    intro x
    unfold mts_portBlockClock
    rw [hval]
    have h1 : leadRingBlock (p.n - 3) x ≠ 0 := by have := mts_leadRingBlock_pos (p.n - 3) x; omega
    simp only [h1, ite_false, zero_add]
    have h2 : ∀ x', (leadRingBlock (p.n - 3) x' = leadRingBlock (p.n - 3) x) ↔ x' = x :=
      fun x' => (mts_leadRingBlock_injective _).eq_iff
    simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl
  have hc0 := mts_portBlockClock_zero p b e y
  have himg : Finset.univ.image f = Finset.univ.erase 0 := by
    refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) ?_
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_erase.2 ⟨hf0 x, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Finset.card_univ, ZMod.card, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_fin]
      omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p.n)), ← himg,
    Finset.sum_image fun x _ y _ h => hinj h, hc0]
  simp only [hcf]

theorem mts_portHMass_nonneg (y) : 0 ≤ mts_portHMass p b e y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem mts_portBlockClock_nonneg (y : GrowthPath p.W × (LayerSample p.W .common ×
    (Fin 1 × Fin p.W → ℂ))) (j : ZMod p.n) : 0 ≤ mts_portBlockClock b e p.n p.W y j := by
  unfold mts_portBlockClock
  refine add_nonneg ?_ (Finset.sum_nonneg fun x _ => ?_)
  · split_ifs
    · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · exact le_rfl
  · split_ifs
    · exact mts_leadPositionMass_nonneg _ _ _ _ _ _ _
    · exact le_rfl

end PortLaw

/-!
## The tag deletion identity
-/

theorem mts_lipschitz_projIci {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : NNReal} (hL : LipschitzWith L Φ)
    (s t : ℝ) : |Φ (Set.projIci 0 s) - Φ (Set.projIci 0 t)| ≤ L * |s - t| := by
  have h := hL.dist_le_mul (Set.projIci 0 s) (Set.projIci 0 t)
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, Set.coe_projIci, Set.coe_projIci,
    max_comm, max_comm (0 : ℝ) t] at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) L.coe_nonneg)

/-- Deletion of the exposed block: deleting the block-`0` mass `a` from the ring test changes it
by at most `2 Lip(Φ) a/(a + Σ m)`. -/
theorem mts_deletion {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : NNReal} (hL : LipschitzWith L Φ) {n : ℕ}
    (hn : 0 < n) {ι : Type*} [Fintype ι] (m : ι → ℝ) (hm : ∀ x, 0 ≤ m x) {a : ℝ} (ha : 0 ≤ a) :
    |(n : ℝ)⁻¹ * (Φ (Set.projIci 0 ((n : ℝ) * a / (a + ∑ x, m x))) +
          ∑ x, Φ (Set.projIci 0 ((n : ℝ) * m x / (a + ∑ x, m x)))) -
        (n : ℝ)⁻¹ * (Φ (Set.projIci 0 0) + ∑ x, Φ (Set.projIci 0 ((n : ℝ) * m x / ∑ x, m x)))| ≤
      2 * L * (a / (a + ∑ x, m x)) := by
  set T := ∑ x, m x with hTdef
  set S := a + T with hSdef
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => hm x
  have hS0 : 0 ≤ S := by linarith
  have hsum : ∑ x, |(n : ℝ) * m x / S - n * m x / T| ≤ n * a / S := by
    rcases hT0.lt_or_eq with hT | hT
    · have hS : 0 < S := by linarith
      have hterm : ∀ x, |(n : ℝ) * m x / S - n * m x / T| = n * m x * (1 / T - 1 / S) := by
        intro x
        have hle : (n : ℝ) * m x / S ≤ n * m x / T :=
          div_le_div_of_nonneg_left (mul_nonneg hn'.le (hm x)) hT (by linarith)
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
        field_simp
      simp only [hterm]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← hTdef]
      apply le_of_eq
      field_simp
      ring
    · have hm0 : ∀ x, m x = 0 := fun x =>
        (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hm x).1 hT.symm x (Finset.mem_univ _)
      simp only [hm0, mul_zero, zero_div, sub_zero, abs_zero, Finset.sum_const_zero]
      positivity
  have hdiff : (n : ℝ)⁻¹ * (Φ (Set.projIci 0 ((n : ℝ) * a / S)) +
        ∑ x, Φ (Set.projIci 0 ((n : ℝ) * m x / S))) -
      (n : ℝ)⁻¹ * (Φ (Set.projIci 0 0) + ∑ x, Φ (Set.projIci 0 ((n : ℝ) * m x / T))) =
      (n : ℝ)⁻¹ * ((Φ (Set.projIci 0 ((n : ℝ) * a / S)) - Φ (Set.projIci 0 0)) +
        ∑ x, (Φ (Set.projIci 0 ((n : ℝ) * m x / S)) -
          Φ (Set.projIci 0 ((n : ℝ) * m x / T)))) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 hn')]
  have h1 : |Φ (Set.projIci 0 ((n : ℝ) * a / S)) - Φ (Set.projIci 0 0)| ≤ L * (n * a / S) := by
    refine (mts_lipschitz_projIci hL _ _).trans (le_of_eq ?_)
    rw [sub_zero, abs_of_nonneg (div_nonneg (mul_nonneg hn'.le ha) hS0)]
  have h2 : |∑ x, (Φ (Set.projIci 0 ((n : ℝ) * m x / S)) -
      Φ (Set.projIci 0 ((n : ℝ) * m x / T)))| ≤ L * (n * a / S) :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun x _ =>
      mts_lipschitz_projIci hL _ _).trans (by
        rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum L.coe_nonneg))
  calc (n : ℝ)⁻¹ * |_| ≤ (n : ℝ)⁻¹ * (L * (n * a / S) + L * (n * a / S)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h1 h2))
          (inv_nonneg.2 hn'.le)
    _ = 2 * L * (a / S) := by field_simp; ring

/-- Block-`0` deletion on the ported field:
`|Ψ_main(ported clocks) - leadAveragedTest(Lg)| ≤ 2 Lip(Φ) · atomClockTest(ported clocks)`. -/
theorem mts_port_deletion (p : Parameters) (b e : ℝ) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : NNReal}
    (hL : LipschitzWith L Φ)
    (y : GrowthPath p.W × (LayerSample p.W .common × (Fin 1 × Fin p.W → ℂ))) :
    |mts_mainClockTest p Φ (fun j => mts_portBlockClock b e p.n p.W y j) -
        leadAveragedTest b e p.n p.W Φ
          (y.1, commonPortProbe b e (leadSchur e p.W (p.n - 3) y.1) y.2)| ≤
      2 * L * mts_atomClockTest p 0 (fun j => mts_portBlockClock b e p.n p.W y j) := by
  have hS := mts_sum_portClock p b e y id
  simp only [id] at hS
  have hmain : mts_mainClockTest p Φ (fun j => mts_portBlockClock b e p.n p.W y j) =
      (p.n : ℝ)⁻¹ * (Φ (Set.projIci 0 ((p.n : ℝ) * mts_portHMass p b e y /
          (mts_portHMass p b e y + ∑ x, mts_portLead p b e y x))) +
        ∑ x, Φ (Set.projIci 0 ((p.n : ℝ) * mts_portLead p b e y x /
          (mts_portHMass p b e y + ∑ x, mts_portLead p b e y x)))) := by
    unfold mts_mainClockTest
    rw [hS]
    congr 1
    exact mts_sum_portClock p b e y (fun t => Φ (Set.projIci 0 ((p.n : ℝ) * t /
      (mts_portHMass p b e y + ∑ x, mts_portLead p b e y x))))
  have hlead : leadAveragedTest b e p.n p.W Φ
      (y.1, commonPortProbe b e (leadSchur e p.W (p.n - 3) y.1) y.2) =
      (p.n : ℝ)⁻¹ * (Φ (Set.projIci 0 0) + ∑ x, Φ (Set.projIci 0 ((p.n : ℝ) *
        mts_portLead p b e y x / ∑ x, mts_portLead p b e y x))) := rfl
  rw [hmain, hlead]
  refine (mts_deletion hL p.n_pos _ (fun x => mts_leadPositionMass_nonneg _ _ _ _ _ _ x)
    (mts_portHMass_nonneg p b e y)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hb := (mts_atomClockTest_bounds p 0 (mts_portBlockClock_nonneg p b e y)).1
  have h0 := mts_portBlockClock_zero p b e y
  rw [h0, hS] at hb
  exact hb

end BlockBand.Endpoints
