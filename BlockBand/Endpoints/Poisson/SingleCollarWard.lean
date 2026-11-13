module

public import BlockBand.Endpoints.Poisson.SingleCollarWardNetwork

/-!
# Ward/scattering data from the component/path identification of `Q_C`

* `scsWardScattering_of_componentPaths`: **the proposition `ScsWardScattering` (defined in the
  sibling module) holds, assuming only `ScwComponentPaths`.** Every field of `ScsWardData` except `len`/`paths` is proved:
  `S₀`, `S₁` are the complete scattering matrices `I - 2iη (F_t⁻¹)_{ports}` of the old network
  with all input ports (collar ports and matched sites), evaluated on
  the Hermitian lift `scwLift` of the old coordinates and set to `I` off the (measurable,
  full-measure) set where both networks are invertible; `Q = W⁻² (P_C𝒰)*(P_C𝒰)` (`0` off it).
  Unitarity, contraction, PSD and the two Ward bounds are deterministic lemmas; the collar blocks
  are `r₀`, `r_κ` almost surely (`scw_scat_block`).
* `ScwComponentPaths` (a hypothesis here, proved as `scwComponentPaths`): the `len`/`paths`
  clause of `ScsWardData` for the explicit `Q_C = scwSourceGram` of the true network.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath (fracTrace intervalSource growthPathLaw)
open BlockBand.Endpoints.PhaseFractional (schattenFrac)
open BlockBand.Internal.Contracts.Layers (boundaryZ)
open scoped ComplexOrder

open Classical

section Lift

variable {m n W : ℕ} [NeZero n] (L : Fin m → ℕ) (s : ZMod n) (k : Fin m)

/-- Hermitian part of the old diagonal coordinates (bonds unchanged). -/
def scwHermCoords (o : oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ) :
    oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ :=
  fun i => Sum.elim (fun _ => (2⁻¹ : ℂ) • (o i + (o i)ᴴ)) (fun _ => o i) i.1

/-- The Hermitian lift of the old coordinates to a full sample (collar coordinates `0`). -/
def scwLift (o : oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ) : RingCoords n W :=
  glueOld L s k (scwHermCoords L s k o)

variable {L s k}

theorem scw_lift_isHermitian (o : oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ) (p : ZMod n) :
    ((scwLift L s k o).1 p).IsHermitian := by
  simp only [scwLift, glueOld]
  split_ifs with h
  · simp only [scwHermCoords, Sum.elim_inl, IsHermitian, conjTranspose_smul, conjTranspose_add,
      conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp
  · exact isHermitian_zero

theorem scw_oldCoords_glueOld (t : oldCoordSet L s k → Matrix (Fin W) (Fin W) ℂ) :
    oldCoords L s k (glueOld L s k t) = t := by
  funext ⟨i, hi⟩
  cases i <;> simp [oldCoords, glueOld, ringCoord, hi]

theorem scw_oldCoords_lift {ω : RingCoords n W} (hA : ∀ p, (ω.1 p).IsHermitian) :
    oldCoords L s k (scwLift L s k (oldCoords L s k ω)) = oldCoords L s k ω := by
  rw [scwLift, scw_oldCoords_glueOld]
  funext ⟨i, hi⟩
  cases i with
  | inl p =>
    simp only [scwHermCoords, Sum.elim_inl, oldCoords, ringCoord]
    rw [(hA p).eq, ← two_smul ℂ, smul_smul]
    norm_num
  | inr p => rfl

theorem scw_measurable_lift :
    Measurable (scwLift (W := W) (n := n) L s k) := by
  refine (measurable_glueOld k).comp (measurable_pi_iff.mpr fun i => ?_)
  rcases i with ⟨i | i, hi⟩
  · simp only [scwHermCoords, Sum.elim_inl]
    have hct : Continuous fun A : Matrix (Fin W) (Fin W) ℂ => (2⁻¹ : ℂ) • (A + Aᴴ) :=
      (show Continuous fun A : Matrix (Fin W) (Fin W) ℂ => A + Aᴴ from
        continuous_id.add continuous_id.matrix_conjTranspose).const_smul (2⁻¹ : ℂ)
    exact hct.measurable.comp (measurable_pi_apply _)
  · exact measurable_pi_apply _

theorem scw_full_lift (hL : IsCollarLayout n L) (π : Pairing) (S : Finset (Fin m)) (b e : ℝ)
    (buf : ℕ) (t : ℝ) {ω : RingCoords n W} (hA : ∀ p, (ω.1 p).IsHermitian) :
    scwFull L s π S k b e buf t (scwLift L s k (oldCoords L s k ω)) =
      scwFull L s π S k b e buf t ω := by
  have h := oldNetwork_congr (s := s) hL π S k e (boundaryZ b e) buf t
    (scw_oldCoords_lift (s := s) (k := k) hA)
  simp only [scwFull, h.1, h.2]

end Lift

/-!
## The component/path identification
-/

/-- The source Gram matrix `Q_C = W⁻² (P_C𝒰)*(P_C𝒰)` of the old network (base block `0`),
`𝒰 = G_{int,ports}`, `G` the inverse of the unabsorbed old network with all its input ports. -/
def scwSourceGram (P : Parameters) {m : ℕ} (L : Fin m → ℕ) (π : Pairing) (S : Finset (Fin m))
    (k : Fin m) (e : ℝ) (buf : ℕ) (ω : RingCoords P.n P.W) :
    Matrix (ScwPorts (W := P.W) L (0 : ZMod P.n) S k) (ScwPorts (W := P.W) L (0 : ZMod P.n) S k) ℂ :=
  (((1 / (P.W : ℝ) ^ 2 : ℝ)) : ℂ) •
    scwGram (scwSrc L (0 : ZMod P.n) S k buf) (scwFull L (0 : ZMod P.n) π S k P.b e buf 0 ω)⁻¹

/-- **The component/path identification**: the `len`/`len_le`/`paths` clause of `ScsWardData`
for the explicit `Q_C`. Its proof needs (a) the decomposition of the old network into its connected components
(`F₀` block-diagonal, cut at every collar of `S ∪ {k}`, closed boxes contributing `𝒰 = 0`) with
their orientation and conjugated bonds; (b) the identification of each component's block of
`Q_C` with `W⁻² Σ_{j ∈ C} tagResponse` of the component read as a `GrowthPath`, and the
profile monotonicity (`fracTrace_mono`); (c) the law of a component (measure preservation of
the readout `ringCoordLaw → pathLaw (len i)`) and the `len`-marginal relation
`(growthPathLaw W b).map (pathAt W len) = pathLaw W len b`. These are proved separately
(`scwComponentPaths`, `scp_growthPathLaw_map_pathAt`).

It is strictly weaker than `ScsWardScattering`: the scattering matrices, unitarity, contraction, positivity, both Ward
bounds and the collar blocks are proved (`scsWardScattering_of_componentPaths`). -/
def ScwComponentPaths : Prop :=
  ∀ (P : Parameters) {m : ℕ} (L : Fin m → ℕ), IsCollarLayout P.n L → ∀ (π : Pairing)
    (S : Finset (Fin m)) (k : Fin m), k ∉ S → ∀ (buf : ℕ) (e : ℝ), -2 < e → e < 2 →
    ∃ len : Fin m → ℕ, (∀ i, len i ≤ P.n) ∧
      ∀ qs : Fin m → ℝ → ℝ, (∀ i x, 0 ≤ qs i x ∧ qs i x ≤ 1) →
      (∀ i, ∀ x ∈ Icc (((buf : ℝ) - 2) / P.W) (((len i : ℝ) - buf + 2) / P.W), qs i x = 1) →
      ∃ Qc : Fin m → RingCoords P.n P.W → Matrix (Fin 2 × Fin P.W) (Fin 2 × Fin P.W) ℂ,
        (∀ i, Measurable (Qc i)) ∧
        (∀ i, (ringCoordLaw P.n P.W P.b).map (Qc i) =
          (growthPathLaw P.W P.b).map (intervalSource P.b e P.W (len i) (qs i))) ∧
        ∀ᵐ ω ∂(ringCoordLaw P.n P.W P.b), ∀ q : ℝ, 0 < q → q < 1 →
          fracTrace q (scwSourceGram P L π S k e buf ω) ≤ ∑ i, fracTrace q (Qc i ω)

/-!
## The Ward data
-/

theorem scw_measurable_scat {α : Type*} [MeasurableSpace α] {π ν : Type} [Fintype π]
    [DecidableEq π] [Fintype ν] [DecidableEq ν] {G : α → Matrix (π ⊕ ν) (π ⊕ ν) ℂ}
    (hG : Measurable G) (η : ℝ) : Measurable fun x => scwScat η (G x) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [scwScat, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, toBlocks₁₁, of_apply]
  exact measurable_const.sub (measurable_const.mul hG.eval_matrix)

theorem scw_measurable_gram {α : Type*} [MeasurableSpace α] {π ν : Type} [Fintype π]
    [DecidableEq π] [Fintype ν] [DecidableEq ν] {G : α → Matrix (π ⊕ ν) (π ⊕ ν) ℂ}
    (hG : Measurable G) (D : Matrix ν ν ℂ) : Measurable fun x => scwGram D (G x) := by
  have hc : Continuous fun M : Matrix (π ⊕ ν) (π ⊕ ν) ℂ => scwGram D M := by
    unfold scwGram
    have h21 : Continuous fun M : Matrix (π ⊕ ν) (π ⊕ ν) ℂ => M.toBlocks₂₁ :=
      continuous_id.matrix_submatrix Sum.inr Sum.inl
    exact ((continuous_const.matrix_mul h21).matrix_conjTranspose).matrix_mul
      (continuous_const.matrix_mul h21)
  exact hc.measurable.comp hG

theorem scw_schattenFrac_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℝ} (hq : 0 < q) :
    schattenFrac q (0 : Matrix ι ι ℂ) = 0 := by
  unfold schattenFrac
  rw [Matrix.mul_zero]
  exact rh_fracTrace_zero (by positivity)

/-- **`ScsWardScattering` from the component/path identification.** -/
theorem scsWardScattering_of_componentPaths (hC : ScwComponentPaths) : ScsWardScattering := by
  intro P m L hL π S k hk buf e he1 he2 κ hκ
  obtain ⟨len, hlen, hpaths⟩ := hC P L hL π S k hk buf e he1 he2
  set η := (boundaryZ P.b e).im with hηdef
  have hη : 0 < η := boundaryZ_im_pos (by linarith [P.b_lt_half]) he1 he2
  set W2 : ℝ := (P.W : ℝ) ^ 2
  have hW2 : 0 < W2 := by have := P.W_pos; positivity
  set a : ℝ := κ / W2
  have ha : 0 ≤ a := div_nonneg hκ hW2.le
  set D := scwSrc (W := P.W) L (0 : ZMod P.n) S k buf
  have hD : Dᴴ = D := scw_src_conjTranspose buf
  have hDD : D * D = D := scw_src_mul_self buf
  set μ := ringCoordLaw P.n P.W P.b
  set F : ℝ → (oldCoordSet L (0 : ZMod P.n) k → Matrix (Fin P.W) (Fin P.W) ℂ) →
      Matrix (ScwPorts (W := P.W) L (0 : ZMod P.n) S k ⊕ ScwInner (W := P.W) L (0 : ZMod P.n) S k)
        (ScwPorts (W := P.W) L (0 : ZMod P.n) S k ⊕ ScwInner (W := P.W) L (0 : ZMod P.n) S k) ℂ :=
    fun t o => scwFull L (0 : ZMod P.n) π S k P.b e buf t (scwLift L (0 : ZMod P.n) k o)
  set Hm := fun o : oldCoordSet L (0 : ZMod P.n) k → Matrix (Fin P.W) (Fin P.W) ℂ =>
    scwHerm L (0 : ZMod P.n) π S k P.b e buf (scwLift L (0 : ZMod P.n) k o)
  have hHm : ∀ o, (Hm o).IsHermitian := fun o =>
    scw_herm_isHermitian P.b e buf (scw_lift_isHermitian o)
  have hF0 : ∀ o, F 0 o = scwNet (Hm o) η 0 D := fun o => by
    simp only [F, Hm, D, η]; rw [scw_full_eq, zero_div]
  have hFκ : ∀ o, F κ o = scwNet (Hm o) η a D := fun o => by
    simp only [F, Hm, D, η, a, W2]; rw [scw_full_eq]
  have hFm : ∀ t, Measurable (F t) := fun t =>
    (scw_measurable_full P.b e buf t).comp (scw_measurable_lift (L := L) (s := 0) (k := k))
  set good := fun o => IsUnit (F 0 o).det ∧ IsUnit (F κ o).det
  have hgoodm : MeasurableSet {o | good o} :=
    (measurableSet_isUnit_det (hFm 0)).inter (measurableSet_isUnit_det (hFm κ))
  set c : ℂ := (((1 / W2 : ℝ)) : ℂ)
  have hc0 : (0 : ℝ) ≤ 1 / W2 := by positivity
  -- the almost sure identification with the true network
  have hz : 0 < (boundaryZ P.b e).im := hη
  have hae : ∀ᵐ ω ∂μ, good (oldCoords L (0 : ZMod P.n) k ω) ∧
      F 0 (oldCoords L (0 : ZMod P.n) k ω) = scwFull L (0 : ZMod P.n) π S k P.b e buf 0 ω ∧
      (scwScat η (F 0 (oldCoords L (0 : ZMod P.n) k ω))⁻¹).toBlocks₁₁ =
        scsResponse P L (0 : ZMod P.n) π S k P.b e buf 0 ω ∧
      (scwScat η (F κ (oldCoords L (0 : ZMod P.n) k ω))⁻¹).toBlocks₁₁ =
        scsResponse P L (0 : ZMod P.n) π S k P.b e buf κ ω := by
    filter_upwards [ringCoordLaw_ae_isHermitian (n := P.n) (W := P.W) P.b,
      ae_isUnit_det_oldInterior P L (0 : ZMod P.n) π S k e hz buf 0,
      ae_isUnit_det_oldInterior P L (0 : ZMod P.n) π S k e hz buf κ] with ω hA hM0 hMκ
    have hX0 := isUnit_det_sub_oldSchur _ (oldCoupling L (0 : ZMod P.n) π S k e (boundaryZ P.b e) buf 0 ω) hM0
      (oldInterior_numRange π S k e _ buf ω hA le_rfl hz.le) hz
    have hXκ := isUnit_det_sub_oldSchur _ (oldCoupling L (0 : ZMod P.n) π S k e (boundaryZ P.b e) buf κ ω)
      hMκ (oldInterior_numRange π S k e _ buf ω hA hκ hz.le) hz
    have hl0 : F 0 (oldCoords L (0 : ZMod P.n) k ω) = scwFull L (0 : ZMod P.n) π S k P.b e buf 0 ω :=
      scw_full_lift hL π S P.b e buf 0 hA
    have hlκ : F κ (oldCoords L (0 : ZMod P.n) k ω) = scwFull L (0 : ZMod P.n) π S k P.b e buf κ ω :=
      scw_full_lift hL π S P.b e buf κ hA
    refine ⟨⟨?_, ?_⟩, hl0, ?_, ?_⟩
    · rw [hl0]; exact scw_isUnit_full P.b e buf 0 ω hM0 hX0
    · rw [hlκ]; exact scw_isUnit_full P.b e buf κ ω hMκ hXκ
    · rw [hl0]; exact scw_scat_block P.b e buf 0 ω hM0 hX0
    · rw [hlκ]; exact scw_scat_block P.b e buf κ ω hMκ hXκ
  refine ⟨{
    β := ScwMatched (W := P.W) L (0 : ZMod P.n) S k
    fβ := scw_instFintypeMatched L (0 : ZMod P.n) S k
    dβ := scw_instDecEqMatched L (0 : ZMod P.n) S k
    S₀ := fun o => if good o then scwScat η (F 0 o)⁻¹ else 1
    S₁ := fun o => if good o then scwScat η (F κ o)⁻¹ else 1
    Q := fun o => if good o then c • scwGram D (F 0 o)⁻¹ else 0
    measurable_S₀ := Measurable.ite hgoodm
      (scw_measurable_scat (scw_measurable_inv.comp (hFm 0)) η) measurable_const
    measurable_S₁ := Measurable.ite hgoodm
      (scw_measurable_scat (scw_measurable_inv.comp (hFm κ)) η) measurable_const
    measurable_Q := Measurable.ite hgoodm
      ((scw_measurable_gram (scw_measurable_inv.comp (hFm 0)) D).const_smul c) measurable_const
    unitary := fun o => by
      by_cases hg : good o
      · simp only [hg, ite_true]
        rw [hF0]
        exact scw_scat_unitary (hHm o) hD η (hF0 o ▸ hg.1)
      · simp [hg]
    contraction := fun o => by
      by_cases hg : good o
      · simp only [hg, ite_true]
        rw [hFκ]
        exact scw_scat_contraction (hHm o) hD hDD hη.le ha (hFκ o ▸ hg.2)
      · simp only [hg, ite_false, conjTranspose_one, Matrix.mul_one, sub_self]
        exact PosSemidef.zero
    posSemidef_Q := fun o => by
      by_cases hg : good o
      · simp only [hg, ite_true]
        exact (scw_posSemidef_gram _ _).smul (by simp only [c]; exact_mod_cast hc0)
      · simp only [hg, ite_false]
        exact PosSemidef.zero
    ward_diff := fun o q hq _ => by
      by_cases hg : good o
      · simp only [hg, ite_true]
        rw [hF0, hFκ]
        have h := scw_ward_diff (hHm o) hD hDD hη.le ha (hF0 o ▸ hg.1) (hFκ o ▸ hg.2) hq
        refine h.trans (le_of_eq ?_)
        rw [fracTrace_smul (scw_posSemidef_gram _ _).isHermitian hc0,
          show 2 * η * a = (2 * η * κ) * (1 / W2) by simp only [a]; ring,
          Real.mul_rpow (by positivity) hc0, mul_assoc]
      · simp only [hg, ite_false, sub_self, scw_schattenFrac_zero hq, rh_fracTrace_zero hq,
          mul_zero, le_refl]
    ward_defect := fun o => by
      by_cases hg : good o
      · simp only [hg, ite_true]
        rw [smul_smul, show (((4 * η * κ : ℝ)) : ℂ) * c = (((4 * η * a : ℝ)) : ℂ) by
          simp only [c, a]; push_cast; ring, hF0, hFκ]
        exact scw_ward_defect (hHm o) hD hDD hη.le ha (hF0 o ▸ hg.1) (hFκ o ▸ hg.2)
      · simp only [hg, ite_false, smul_zero, conjTranspose_one, Matrix.mul_one, sub_self]
        exact PosSemidef.zero
    block₀ := by
      filter_upwards [hae] with ω h
      simp only [h.1, ite_true]
      exact h.2.2.1
    block₁ := by
      filter_upwards [hae] with ω h
      simp only [h.1, ite_true]
      exact h.2.2.2
    len := len
    len_le := hlen
    paths := fun qs hqs hwin => by
      obtain ⟨Qc, hm, hlaw, hQ⟩ := hpaths qs hqs hwin
      refine ⟨Qc, hm, hlaw, ?_⟩
      filter_upwards [hQ, hae] with ω h hg q hq hq1
      simp only [hg.1, ite_true, hg.2.1]
      exact h q hq hq1 }⟩

end BlockBand.Endpoints
