module

public import BlockBand.DeterminantScore.WeylIntegrationInduction

/-!
# Weyl integration: corner Fubini

`cornerFubini` proves `CornerFubiniStatement`: Lebesgue measure on the coordinates of Hermitian
`(n+1) × (n+1)` matrices is the product of Lebesgue measures on the corner `HermCoord n`, on the
border `ℂ^n` and on the corner entry `ℝ`, through the coordinate permutation `cornerEquiv`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open scoped ENNReal

variable {n : ℕ}

/-- The index decomposition of `HermCoord (n+1)`: corner, upper border, lower border, corner
entry. -/
def cornerIndex (n : ℕ) : HermCoord n ⊕ ((Fin n ⊕ Fin n) ⊕ Unit) → HermCoord (n + 1)
  | .inl c => (c.1.castSucc, c.2.castSucc)
  | .inr (.inl (.inl i)) => (i.castSucc, Fin.last n)
  | .inr (.inl (.inr i)) => (Fin.last n, i.castSucc)
  | .inr (.inr _) => (Fin.last n, Fin.last n)

theorem cornerIndex_injective : Function.Injective (cornerIndex n) := by
  have h1 : ∀ i : Fin n, i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last
  have h2 : ∀ i : Fin n, Fin.last n ≠ i.castSucc := fun i => (Fin.castSucc_ne_last i).symm
  rintro (⟨i, j⟩ | (i | i) | u) (⟨k, l⟩ | (k | k) | w) h <;>
    simp_all [cornerIndex, Prod.ext_iff]

theorem cornerIndex_bijective : Function.Bijective (cornerIndex n) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨cornerIndex_injective, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  ring

/-- `cornerIndex` as an equivalence. -/
def cornerEquiv (n : ℕ) : HermCoord n ⊕ ((Fin n ⊕ Fin n) ⊕ Unit) ≃ HermCoord (n + 1) :=
  Equiv.ofBijective _ cornerIndex_bijective

/-- `ℂ^n → ℝ^n × ℝ^n`, `v ↦ (Re v, Im v)`. -/
def complexSplit (n : ℕ) : (Fin n → ℂ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun v => MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun i => Complex.measurableEquivRealProd (v i))

theorem measurePreserving_complexSplit :
    MeasurePreserving (complexSplit n) volume (volume.prod volume) :=
  (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => volume) (fun _ => volume)).comp
    (volume_preserving_pi fun _ => Complex.volume_preserving_equiv_real_prod)

/-- The border coordinates `(v, a) ↦ (Re v, Im v, a)` indexed by `(Fin n ⊕ Fin n) ⊕ Unit`. -/
def borderSplit (n : ℕ) : (Fin n → ℂ) × ℝ → ((Fin n ⊕ Fin n) ⊕ Unit → ℝ) :=
  fun p => (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm
    ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (complexSplit n p.1),
      (MeasurableEquiv.funUnique Unit ℝ).symm p.2)

theorem measurePreserving_borderSplit :
    MeasurePreserving (borderSplit n) (volume.prod volume) volume := by
  have h1 := (measurePreserving_sumPiEquivProdPi_symm (ι := Fin n) (ι' := Fin n)
    (fun _ => (volume : Measure ℝ))).comp (measurePreserving_complexSplit (n := n))
  have h2 := (volume_preserving_funUnique Unit ℝ).symm
  exact (measurePreserving_sumPiEquivProdPi_symm (ι := Fin n ⊕ Fin n) (ι' := Unit)
    (fun _ => (volume : Measure ℝ))).comp (h1.prod h2)

/-- The coordinate assembly `(y, v, a) ↦ x ∈ ℝ^{HermCoord (n+1)}`. -/
def cornerMap (n : ℕ) : (HermCoord n → ℝ) × ((Fin n → ℂ) × ℝ) → (HermCoord (n + 1) → ℝ) :=
  fun p => MeasurableEquiv.piCongrLeft (fun _ => ℝ) (cornerEquiv n)
    ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).symm (p.1, borderSplit n p.2))

theorem measurePreserving_cornerMap :
    MeasurePreserving (cornerMap n) (volume.prod (volume.prod volume)) volume := by
  have h1 := (measurePreserving_sumPiEquivProdPi_symm (ι := HermCoord n)
    (ι' := (Fin n ⊕ Fin n) ⊕ Unit) (fun _ => (volume : Measure ℝ))).comp
      ((MeasurePreserving.id (volume : Measure (HermCoord n → ℝ))).prod
        (measurePreserving_borderSplit (n := n)))
  exact (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (cornerEquiv n)).comp h1

theorem cornerMap_apply (p : (HermCoord n → ℝ) × ((Fin n → ℂ) × ℝ))
    (b : HermCoord n ⊕ ((Fin n ⊕ Fin n) ⊕ Unit)) :
    cornerMap n p (cornerIndex n b) =
      (match b with
        | .inl c => p.1 c
        | .inr (.inl (.inl i)) => (p.2.1 i).re
        | .inr (.inl (.inr i)) => (p.2.1 i).im
        | .inr (.inr _) => p.2.2) := by
  have hb : cornerIndex n b = cornerEquiv n b := rfl
  rw [hb]
  simp only [cornerMap, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rcases b with c | (i | i) | u <;>
    simp [borderSplit, complexSplit, MeasurableEquiv.sumPiEquivProdPi,
      MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.funUnique]

/-- `H(cornerMap(y, v, a)) = [[H(y), v], [v*, a]]`. -/
theorem hermOfCoord_cornerMap (p : (HermCoord n → ℝ) × ((Fin n → ℂ) × ℝ)) :
    hermOfCoord (cornerMap n p) = borderHerm (hermOfCoord p.1) p.2.1 p.2.2 := by
  have e1 : ∀ i j : Fin n, cornerMap n p (i.castSucc, j.castSucc) = p.1 (i, j) :=
    fun i j => cornerMap_apply p (.inl (i, j))
  have e2 : ∀ i : Fin n, cornerMap n p (i.castSucc, Fin.last n) = (p.2.1 i).re :=
    fun i => cornerMap_apply p (.inr (.inl (.inl i)))
  have e3 : ∀ i : Fin n, cornerMap n p (Fin.last n, i.castSucc) = (p.2.1 i).im :=
    fun i => cornerMap_apply p (.inr (.inl (.inr i)))
  have e4 : cornerMap n p (Fin.last n, Fin.last n) = p.2.2 :=
    cornerMap_apply p (.inr (.inr ()))
  ext r s
  induction r using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last => simp [hermOfCoord, borderHerm, e4]
    | cast j =>
      have hne : Fin.last n ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
      have hlt : ¬ Fin.last n < j.castSucc := not_lt.2 (Fin.castSucc_lt_last j).le
      simp only [hermOfCoord, borderHerm, Matrix.of_apply, Fin.lastCases_last,
        Fin.lastCases_castSucc, hne, hlt, ite_false, e2, e3]
      apply Complex.ext <;> simp
  | cast i =>
    induction s using Fin.lastCases with
    | last =>
      have hne : i.castSucc ≠ Fin.last n := Fin.castSucc_ne_last i
      simp only [hermOfCoord, borderHerm, Matrix.of_apply, Fin.lastCases_last,
        Fin.lastCases_castSucc, hne, Fin.castSucc_lt_last, ite_true, ite_false, e2, e3]
      apply Complex.ext <;> simp
    | cast j =>
      simp only [hermOfCoord, borderHerm, Matrix.of_apply, Fin.lastCases_castSucc,
        Fin.castSucc_inj, Fin.castSucc_lt_castSucc_iff, e1]

/-- **Corner Fubini**: `∫ G(H(x)) dx = ∫∫∫ G([[H(y), v], [v*, a]]) da dv dy`. -/
theorem cornerFubini : CornerFubiniStatement := by
  intro n G hG
  have hGm : Measurable fun x : HermCoord (n + 1) → ℝ => G (hermOfCoord x) :=
    hG.comp continuous_hermOfCoord.measurable
  rw [← (measurePreserving_cornerMap (n := n)).lintegral_comp hGm]
  simp only [hermOfCoord_cornerMap]
  have hBm : Measurable fun p : (HermCoord n → ℝ) × ((Fin n → ℂ) × ℝ) =>
      G (borderHerm (hermOfCoord p.1) p.2.1 p.2.2) := by
    have := hGm.comp (measurePreserving_cornerMap (n := n)).measurable
    rw [show ((fun x : HermCoord (n + 1) → ℝ => G (hermOfCoord x)) ∘ cornerMap n) =
      fun p => G (borderHerm (hermOfCoord p.1) p.2.1 p.2.2) from
        funext fun p => by simp [Function.comp_apply, hermOfCoord_cornerMap]] at this
    exact this
  rw [lintegral_prod _ hBm.aemeasurable]
  refine lintegral_congr fun y => ?_
  have hy : Measurable fun q : (Fin n → ℂ) × ℝ => G (borderHerm (hermOfCoord y) q.1 q.2) :=
    hBm.comp measurable_prodMk_left
  exact lintegral_prod _ hy.aemeasurable

end BlockBand.DeterminantScore.WeylIntegration
